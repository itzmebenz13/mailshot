FROM node:20-alpine

WORKDIR /app

# Install dependencies
COPY package*.json ./
RUN npm install --omit=dev

# Copy application source
COPY . .

# Render exposes PORT dynamically (usually 10000)
ENV NODE_ENV=production
EXPOSE 10000 3000

CMD ["node", "server.js"]

