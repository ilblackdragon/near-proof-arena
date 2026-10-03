import { render } from '@testing-library/react';
import { MemoryRouter } from 'react-router-dom';
import { vi } from 'vitest';
import { AppRoutes } from '../src/App';
import { mockFetch } from '../mock/api';
import type { Dataset } from '../mock/fixtures';

export function renderApp(path: string, ds: Dataset) {
  const fetchSpy = vi.fn(mockFetch(ds));
  vi.stubGlobal('fetch', fetchSpy);
  const utils = render(
    <MemoryRouter initialEntries={[path]}>
      <AppRoutes />
    </MemoryRouter>,
  );
  return { ...utils, fetchSpy };
}
