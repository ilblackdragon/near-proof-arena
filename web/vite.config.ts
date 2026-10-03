/// <reference types="vitest/config" />
import { defineConfig, loadEnv, type Plugin } from 'vite';
import react from '@vitejs/plugin-react';

/**
 * Content-Security-Policy injected as a <meta> tag into the PRODUCTION build
 * only (the dev server needs inline HMR scripts). The recommended *server*
 * headers (which can also set frame-ancestors etc.) are documented in README.
 */
export function cspPolicy(apiBase: string): string {
  let apiOrigin = '';
  if (/^https?:\/\//.test(apiBase)) apiOrigin = ` ${new URL(apiBase).origin}`;
  return [
    "default-src 'none'",
    "script-src 'self'",
    "style-src 'self'",
    "img-src 'self'",
    "font-src 'self'",
    `connect-src 'self'${apiOrigin}`,
    "manifest-src 'self'",
    "base-uri 'none'",
    "form-action 'none'",
    "object-src 'none'",
    "frame-src 'none'",
    "worker-src 'none'",
    "require-trusted-types-for 'script'",
    "trusted-types 'none'",
  ].join('; ');
}

function cspPlugin(apiBase: string): Plugin {
  return {
    name: 'arena-csp',
    transformIndexHtml: {
      order: 'post',
      handler(html, ctx) {
        const meta = ctx.server
          ? ''
          : `<meta http-equiv="Content-Security-Policy" content="${cspPolicy(apiBase)}" />`;
        return html.replace('<!--ARENA_CSP-->', meta);
      },
    },
  };
}

/** Dev-only fixture API (all data labelled DEMO). Never part of a build. */
function mockApiPlugin(): Plugin {
  return {
    name: 'arena-mock-api',
    apply: 'serve',
    async configureServer(server) {
      // Loaded through Vite's module graph (not the config bundle).
      const mod = (await server.ssrLoadModule('/mock/dev-server.ts')) as typeof import('./mock/dev-server');
      server.middlewares.use(mod.createMockMiddleware());
      server.config.logger.info('\n  [arena] MOCK API enabled: serving DEMO fixtures at /v1\n');
    },
  };
}

export default defineConfig(({ mode }) => {
  const env = loadEnv(mode, process.cwd(), '');
  const apiBase = env.VITE_API_BASE ?? '';
  const mock = process.env.ARENA_MOCK === '1';
  const target = process.env.ARENA_API ?? 'http://127.0.0.1:8471';
  return {
    plugins: [react(), cspPlugin(apiBase), ...(mock ? [mockApiPlugin()] : [])],
    server: {
      port: 5173,
      strictPort: false,
      proxy: mock ? undefined : { '/v1': { target, changeOrigin: false } },
    },
    preview: {
      proxy: { '/v1': { target, changeOrigin: false } },
    },
    build: {
      sourcemap: false,
      modulePreload: { polyfill: false },
      target: 'es2022',
    },
    test: {
      environment: 'jsdom',
      globals: true,
      setupFiles: ['./tests/setup.ts'],
      include: ['tests/**/*.test.{ts,tsx}'],
      restoreMocks: true,
    },
  };
});
