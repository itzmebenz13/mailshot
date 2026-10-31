/**
 * gmail.js — Multi-account Gmail manager for KoreoMail
 *
 * Architecture (Option A):
 *   - One Pub/Sub subscription per Gmail account
 *   - Each subscription pushes to /gmail/push?account=user@gmail.com
 *   - Tokens stored in Supabase `gmail_accounts` table (survives deploys)
 *
 * Supabase table required:
 *   CREATE TABLE gmail_accounts (
 *     email          TEXT PRIMARY KEY,
 *     tokens         JSONB NOT NULL,
 *     watch_expiry   TIMESTAMPTZ,
 *     watch_resource TEXT,
 *     added_at       TIMESTAMPTZ DEFAULT now()
 *   );
 */

'use strict';

const { google } = require('googleapis');
const fs          = require('fs');
require('dotenv').config();

// ── Gmail OAuth scopes ──
const SCOPES = ['https://www.googleapis.com/auth/gmail.readonly'];

// ── Load credentials ──
let credentialsData;
if (process.env.CREDENTIALS_JSON) {
  credentialsData = JSON.parse(process.env.CREDENTIALS_JSON);
} else {
  credentialsData = JSON.parse(fs.readFileSync('credentials.json'));
}
const { client_id, client_secret, redirect_uris } = credentialsData.web;

// ── Redirect URI (Auto-detects Render, Railway, or custom domain) ──
const rawDomain = process.env.RENDER_EXTERNAL_HOSTNAME || process.env.RAILWAY_PUBLIC_DOMAIN || process.env.APP_DOMAIN;
const redirectUri = process.env.RENDER_EXTERNAL_URL
  ? `${process.env.RENDER_EXTERNAL_URL}/auth/callback`
  : rawDomain
    ? `https://${rawDomain.replace(/^https?:\/\//, '')}/auth/callback`
    : (redirect_uris && redirect_uris[0]) || 'http://localhost:3000/auth/callback';

// ── Supabase client ──
const { createClient } = require('@supabase/supabase-js');
const _sb = createClient(
  process.env.SUPABASE_URL,
  process.env.SUPABASE_SERVICE_KEY
);

// ────────────────────────────────────────────────────────────
// In-memory token cache: Map<accountEmail, oAuth2Client>
// Populated on first use or server start via loadAllAccounts()
// ────────────────────────────────────────────────────────────
const _clients = new Map();

/**
 * Create or retrieve the OAuth2 client for a specific Gmail account.
 * Reads tokens from Supabase on first access and caches in memory.
 */
async function getClient(accountEmail) {
  if (_clients.has(accountEmail)) return _clients.get(accountEmail);

  const client = new google.auth.OAuth2(client_id, client_secret, redirectUri);

  // Try loading tokens from Supabase
  const { data, error } = await _sb
    .from('gmail_accounts')
    .select('tokens')
    .eq('email', accountEmail)
    .maybeSingle();

  if (!error && data && data.tokens) {
    client.setCredentials(data.tokens);
    console.log(`[gmail] Loaded tokens for ${accountEmail} from Supabase`);
  } else {
    console.warn(`[gmail] No token found for ${accountEmail} — needs OAuth`);
  }

  // Auto-refresh: persist new access_token back to Supabase
  client.on('tokens', async (newTokens) => {
    try {
      const merged = Object.assign({}, client.credentials, newTokens);
      client.setCredentials(merged);
      await _sb.from('gmail_accounts').upsert(
        { email: accountEmail, tokens: merged },
        { onConflict: 'email' }
      );
      console.log(`[gmail] Auto-refreshed token saved for ${accountEmail}`);
    } catch (e) {
      console.error(`[gmail] Token refresh save failed for ${accountEmail}:`, e.message);
    }
  });

  _clients.set(accountEmail, client);
  return client;
}

/**
 * Pre-load all accounts from Supabase into the in-memory cache.
 * Called at server startup so the first request doesn't incur DB latency.
 */
async function loadAllAccounts() {
  try {
    const { data, error } = await _sb.from('gmail_accounts').select('email, tokens');
    if (error) throw error;
    if (!data || !data.length) {
      console.log('[gmail] No Gmail accounts found in database');
      return;
    }
    for (const row of data) {
      const client = new google.auth.OAuth2(client_id, client_secret, redirectUri);
      if (row.tokens) client.setCredentials(row.tokens);

      client.on('tokens', async (newTokens) => {
        try {
          const merged = Object.assign({}, client.credentials, newTokens);
          client.setCredentials(merged);
          await _sb.from('gmail_accounts').upsert(
            { email: row.email, tokens: merged },
            { onConflict: 'email' }
          );
          console.log(`[gmail] Token refreshed for ${row.email}`);
        } catch (e) {
          console.error(`[gmail] Token save failed for ${row.email}:`, e.message);
        }
      });

      _clients.set(row.email, client);
    }
    console.log(`[gmail] Loaded ${data.length} account(s): ${data.map(r => r.email).join(', ')}`);
  } catch (e) {
    console.error('[gmail] loadAllAccounts error:', e.message);
  }
}

// ────────────────────────────────────────────────────────────
// AUTH HELPERS
// ────────────────────────────────────────────────────────────

/**
 * Generate an OAuth URL for a specific Gmail account.
 * Uses login_hint so Google pre-selects that account.
 */
function getAuthUrl(accountEmail, userId) {
  const tempClient = new google.auth.OAuth2(client_id, client_secret, redirectUri);
  const statePayload = { a: accountEmail || '', u: userId || '' };
  const params = {
    access_type: 'offline',
    prompt: 'consent',
    scope: SCOPES,
    state: Buffer.from(JSON.stringify(statePayload)).toString('base64') // passed back in ?state= on callback
  };
  if (accountEmail) params.login_hint = accountEmail;
  return tempClient.generateAuthUrl(params);
}

/**
 * Exchange auth code for tokens and persist to Supabase.
 * accountEmail comes from the ?state= callback parameter.
 */
async function saveToken(code, stateStr) {
  const tempClient = new google.auth.OAuth2(client_id, client_secret, redirectUri);
  const { tokens } = await tempClient.getToken(code);

  let accountEmail = '';
  let userId = null;
  try {
    const parsed = JSON.parse(Buffer.from(stateStr, 'base64').toString('utf8'));
    accountEmail = parsed.a;
    userId = parsed.u || null;
  } catch (e) {
    accountEmail = stateStr; // fallback for old format
  }

  // Determine actual account email from token if not provided
  let email = accountEmail;
  if (!email) {
    // Try to get profile from Gmail API
    try {
      tempClient.setCredentials(tokens);
      const gmail = google.gmail({ version: 'v1', auth: tempClient });
      const profile = await gmail.users.getProfile({ userId: 'me' });
      email = profile.data.emailAddress;
    } catch (e) {
      console.error('[gmail] Could not determine account email from token:', e.message);
      throw new Error('Could not determine Gmail account email. Please specify it.');
    }
  }

  // Upsert into Supabase
  const upsertData = { email, tokens };
  if (userId) upsertData.user_id = userId;

  const { error } = await _sb.from('gmail_accounts').upsert(
    upsertData,
    { onConflict: 'email' }
  );
  if (error) throw error;

  // Update in-memory client
  const client = new google.auth.OAuth2(client_id, client_secret, redirectUri);
  client.setCredentials(tokens);
  client.on('tokens', async (newTokens) => {
    try {
      const merged = Object.assign({}, client.credentials, newTokens);
      client.setCredentials(merged);
      await _sb.from('gmail_accounts').upsert(
        { email, tokens: merged },
        { onConflict: 'email' }
      );
    } catch (err) {
      console.error(`[gmail] Token save failed for ${email}:`, err.message);
    }
  });
  _clients.set(email, client);

  console.log(`[gmail] Token saved for ${email}`);
  return email;
}

// ────────────────────────────────────────────────────────────
// EMAIL FETCHING
// ────────────────────────────────────────────────────────────

/** Normalize a Gmail address by removing dots from the username part. */
function normalizeGmail(address) {
  if (!address) return '';
  const match = address.match(/<([^>]+)>/);
  const rawEmail = match ? match[1] : address;
  const [user, domain] = rawEmail.toLowerCase().split('@');
  return (user || '').replace(/\./g, '') + '@' + (domain || '');
}

// Per-account last-fetch time cache (in-memory, reset on restart)
const _lastFetchTimes = new Map();

// ── OTP Email filter ──
const OTP_SUBJECT_KEYWORDS = [
  'verif', 'otp', 'one-time', 'one time', 'passcode', 'pass code',
  'security code', 'confirmation code', 'auth code', 'authentication',
  'login code', 'sign in code', 'access code', '2fa', 'two-factor',
  'your code', 'enter code', 'your pin', 'temporary', 'activate',
  'validate', 'validation'
];
const PROMO_SUBJECT_KEYWORDS = [
  'sale', 'off', 'discount', 'promo', 'deal', 'offer', 'coupon',
  'shop', 'order', 'shipped', 'delivered', 'invoice', 'receipt',
  'newsletter', 'unsubscribe', 'subscription', 'welcome', 'thank you',
  'thanks for', 'update', 'news', 'announcement', 'invitation',
  'reminder', 'notification', 'alert', 'bill', 'payment', 'refund',
  'reward', 'points', 'voucher', 'flash', 'limited time', 'exclusive',
  'member', 'account created', 'successfully', 'tracking'
];
const OTP_CODE_REGEX = /\b\d{4,8}\b/;

const NOMAD_KEYWORDS = [
  'nomad', 'getnomad', 'getnomad.app', 'esim', 'qr code', 'manual installation',
  'sm-dp+', 'rsp.esim.pub', 'lpa:1$', 'activation code', 'iccid'
];

function isOTPEmail(subject, body) {
  const subjectLower = (subject || '').toLowerCase();
  const bodyLower    = (body || '').toLowerCase().slice(0, 1000);
  const hasPromo = PROMO_SUBJECT_KEYWORDS.some(k => subjectLower.includes(k));
  const hasOTP   = OTP_SUBJECT_KEYWORDS.some(k => subjectLower.includes(k));
  const hasCode  = OTP_CODE_REGEX.test(body || '');
  if (hasOTP) return true;
  if (hasCode && !hasPromo) return true;
  if (hasPromo && !hasOTP && !hasCode) return false;
  return true;
}

function isNomadOrOTPEmail(subject, body, from) {
  const fromLower    = (from || '').toLowerCase();
  const subjectLower = (subject || '').toLowerCase();
  const bodyLower    = (body || '').toLowerCase();

  // Always accept if sender is Nomad (no-reply@getnomad.app, etc.)
  if (fromLower.includes('getnomad.app') || fromLower.includes('nomad')) return true;

  // Always accept if subject or body contains Nomad / eSIM keywords
  if (NOMAD_KEYWORDS.some(k => subjectLower.includes(k) || bodyLower.includes(k))) return true;

  // Fall back to standard OTP detection
  return isOTPEmail(subject, body);
}

/**
 * Fetch recent OTP emails from a specific Gmail account.
 * @param {number} maxResults
 * @param {string} accountEmail
 * @returns {Array}
 */
async function fetchEmails(maxResults = 20, accountEmail) {
  if (!accountEmail) throw new Error('accountEmail is required for fetchEmails');
  const auth = await getClient(accountEmail);
  const gmail = google.gmail({ version: 'v1', auth });

  const normalizedBase = normalizeGmail(accountEmail);

  let lastFetchTime = _lastFetchTimes.get(accountEmail) || null;
  let query = 'in:inbox';
  if (lastFetchTime) {
    const afterSec = Math.floor(lastFetchTime / 1000) - 60;
    query += ' after:' + afterSec;
  }
  console.log(`[gmail] Fetching for ${accountEmail}, query: ${query}`);

  let list;
  try {
    list = await gmail.users.messages.list({ userId: 'me', maxResults, q: query });
  } catch (e) {
    throw e;
  }

  _lastFetchTimes.set(accountEmail, Date.now());

  if (!list.data.messages) {
    console.log(`[gmail] No messages for ${accountEmail}`);
    return [];
  }

  const emails = [];
  for (const msg of list.data.messages) {
    const detail = await gmail.users.messages.get({
      userId: 'me', id: msg.id, format: 'full'
    });

    const headers   = detail.data.payload.headers;
    const getHeader = name =>
      (headers.find(h => h.name.toLowerCase() === name) || {}).value || '';

    const toField       = getHeader('to');
    const normalizedTo  = normalizeGmail(toField);

    // Only keep emails addressed to this Gmail account (dot-variant)
    if (normalizedTo !== normalizedBase) continue;

    const from    = getHeader('from');
    const subject = getHeader('subject');
    const date    = getHeader('date');

    // Extract body (both plain text and html)
    let body = '';
    let htmlBody = '';
    const payload = detail.data.payload;
    if (payload.body && payload.body.data) {
      body = Buffer.from(payload.body.data, 'base64').toString('utf8');
    }
    function scanParts(partsList) {
      for (const part of (partsList || [])) {
        if (part.mimeType === 'text/plain' && part.body && part.body.data && !body) {
          body = Buffer.from(part.body.data, 'base64').toString('utf8');
        } else if (part.mimeType === 'text/html' && part.body && part.body.data && !htmlBody) {
          htmlBody = Buffer.from(part.body.data, 'base64').toString('utf8');
        }
        if (part.parts) scanParts(part.parts);
      }
    }
    if (payload.parts) scanParts(payload.parts);

    // If HTML exists, use it as full body so QR images render; keep plain text in fallback
    const fullBody = htmlBody || body;

    // Nomad & OTP filter
    if (!isNomadOrOTPEmail(subject, fullBody || body, from)) {
      console.log(`[gmail] Skipped non-Nomad/non-OTP email for ${accountEmail}: ${subject}`);
      continue;
    }

    const m           = from.match(/^(.*?)<(.+?)>$/);
    const senderName  = m ? m[1].trim() : from;
    const senderEmail = m ? m[2].trim() : from;

    const aliasMatch = toField.match(/[\w.]+@[\w.]+/);
    const alias = aliasMatch ? aliasMatch[0].toLowerCase() : toField.toLowerCase();

    console.log(`[gmail] Relevant email: to=${alias}, from=${accountEmail}, subject=${subject}`);
    emails.push({
      gmail_id:      msg.id,
      alias,
      gmail_account: accountEmail,
      sender:        senderName,
      sender_email:  senderEmail,
      subject,
      body:          fullBody || body,
      received_at:   new Date(date).toISOString()
    });
  }

  console.log(`[gmail] ${emails.length} OTP email(s) for ${accountEmail}`);
  return emails;
}

// ────────────────────────────────────────────────────────────
// PUB/SUB WATCH
// ────────────────────────────────────────────────────────────

/**
 * Register a Gmail push-notification watch for one account.
 * Uses a dedicated Pub/Sub subscription per account (Option A).
 *
 * Topic naming convention:
 *   projects/{PROJECT}/topics/{PUBSUB_TOPIC}
 *
 * The subscription name is derived from the Gmail address slug.
 * The push endpoint is: /gmail/push?account=user@gmail.com
 */
async function registerWatch(accountEmail) {
  if (!accountEmail) throw new Error('accountEmail required for registerWatch');
  const auth  = await getClient(accountEmail);
  const gmail = google.gmail({ version: 'v1', auth });

  const topicName = `projects/${process.env.GOOGLE_CLOUD_PROJECT}/topics/${process.env.PUBSUB_TOPIC}`;

  const res = await gmail.users.watch({
    userId: 'me',
    requestBody: {
      topicName,
      labelIds: ['INBOX']
    }
  });

  const expiry       = res.data.expiration ? new Date(Number(res.data.expiration)) : null;
  const resourceId   = res.data.historyId || null;

  // Save watch expiry to Supabase
  await _sb.from('gmail_accounts').upsert(
    {
      email:         accountEmail,
      watch_expiry:  expiry ? expiry.toISOString() : null,
      watch_resource: String(resourceId || '')
    },
    { onConflict: 'email' }
  );

  console.log(`[gmail] Watch registered for ${accountEmail} (expires: ${expiry})`);
  return { expiry, resourceId };
}

/**
 * Register/refresh watches for ALL accounts in the database.
 * Called by the cron job every 6 hours.
 */
async function registerAllWatches() {
  const { data, error } = await _sb.from('gmail_accounts').select('email');
  if (error || !data) {
    console.error('[gmail] registerAllWatches: could not load accounts:', error?.message);
    return;
  }
  for (const row of data) {
    try {
      await registerWatch(row.email);
    } catch (e) {
      console.error(`[gmail] registerWatch failed for ${row.email}:`, e.message);
    }
  }
}

// ────────────────────────────────────────────────────────────
// DEBOUNCED FETCH (per account)
// ────────────────────────────────────────────────────────────

const _fetchTimers   = new Map();   // accountEmail → timer
const _fetchRetries  = new Map();   // accountEmail → retry count
const _isFetching    = new Map();   // accountEmail → bool
const _pendingCbs    = new Map();   // accountEmail → callback fn
const _maxRetries    = 5;
const _baseDelay     = 3000;

/**
 * Schedule a debounced email fetch for one account.
 * Exponential backoff on rate limit errors.
 */
function scheduleFetch(accountEmail, callback) {
  if (!accountEmail) return;
  if (callback) _pendingCbs.set(accountEmail, callback);

  const existingTimer = _fetchTimers.get(accountEmail);
  if (existingTimer) clearTimeout(existingTimer);

  const retries = _fetchRetries.get(accountEmail) || 0;
  const delay   = Math.min(_baseDelay * Math.pow(2, retries), 60000);
  console.log(`[gmail] Fetch for ${accountEmail} scheduled in ${delay / 1000}s`);

  const timer = setTimeout(async () => {
    _fetchTimers.delete(accountEmail);
    if (_isFetching.get(accountEmail)) {
      scheduleFetch(accountEmail, null);
      return;
    }
    _isFetching.set(accountEmail, true);
    try {
      const emails = await fetchEmails(20, accountEmail);
      _fetchRetries.set(accountEmail, 0);
      _isFetching.set(accountEmail, false);

      if (emails.length > 0) {
        const cb = _pendingCbs.get(accountEmail);
        if (cb) {
          _pendingCbs.delete(accountEmail);
          await cb(emails);
        }
      }
    } catch (e) {
      _isFetching.set(accountEmail, false);
      const isRateLimit = e.message && (
        e.message.includes('rate limit') ||
        e.message.includes('Rate Limit') ||
        e.message.includes('429') ||
        e.message.includes('User Rate Limit')
      );
      if (isRateLimit) {
        const r = Math.min((_fetchRetries.get(accountEmail) || 0) + 1, _maxRetries);
        _fetchRetries.set(accountEmail, r);
        console.log(`[gmail] Rate limited for ${accountEmail} — backoff retry #${r}`);
        scheduleFetch(accountEmail, null);
      } else {
        console.error(`[gmail] Fetch error for ${accountEmail}:`, e.message);
        _fetchRetries.set(accountEmail, 0);
      }
    }
  }, delay);

  _fetchTimers.set(accountEmail, timer);
}

// ────────────────────────────────────────────────────────────
// ACCOUNT MANAGEMENT
// ────────────────────────────────────────────────────────────

/** List all connected Gmail accounts from Supabase. */
async function listAccounts() {
  const { data, error } = await _sb
    .from('gmail_accounts')
    .select('email, watch_expiry, watch_resource, added_at')
    .order('added_at', { ascending: true });
  if (error) throw error;
  return data || [];
}

/** Remove an account: delete from Supabase + evict from in-memory cache. */
async function removeAccount(accountEmail) {
  const { error } = await _sb
    .from('gmail_accounts')
    .delete()
    .eq('email', accountEmail);
  if (error) throw error;
  _clients.delete(accountEmail);
  _fetchTimers.delete(accountEmail);
  _isFetching.delete(accountEmail);
  _fetchRetries.delete(accountEmail);
  _pendingCbs.delete(accountEmail);
  _lastFetchTimes.delete(accountEmail);
  console.log(`[gmail] Removed account: ${accountEmail}`);
}

// ────────────────────────────────────────────────────────────
// BACKWARD COMPATIBILITY — legacy last_fetch_time in system_state.
// ────────────────────────────────────────────────────────────
// The old single-account system stored a global last_fetch_time.
// We no longer need it; per-account times are kept in _lastFetchTimes.

// ────────────────────────────────────────────────────────────
// EXPORTS
// ────────────────────────────────────────────────────────────
module.exports = {
  loadAllAccounts,
  getAuthUrl,
  saveToken,
  fetchEmails,
  registerWatch,
  registerAllWatches,
  scheduleFetch,
  listAccounts,
  removeAccount,
  normalizeGmail,
  // Legacy export so existing server.js code compiles without errors
  // until the server is fully updated
  getClient
};
