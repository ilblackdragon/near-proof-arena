# syntax=docker/dockerfile:1
# Static web frontend served by unprivileged nginx. Build context: repo root.
FROM node:22-bookworm-slim@sha256:43ac6c60b8f89723f746e8a92ce91abd5017e627ce1ddfe4238355d3a30b772c AS build
ARG WEB_DIST=dist
RUN corepack enable
WORKDIR /src/web
COPY web/ ./
RUN pnpm install --frozen-lockfile && pnpm build && test -d "$WEB_DIST" && cp -r "$WEB_DIST" /out

FROM nginxinc/nginx-unprivileged:1.29-alpine@sha256:0c79d56aee561a1d81c63f00eee5fb5fe29279560cdc55e91425133104c7fbe6
COPY deploy/local/nginx.conf /etc/nginx/conf.d/default.conf
COPY --from=build /out /usr/share/nginx/html
EXPOSE 8080
