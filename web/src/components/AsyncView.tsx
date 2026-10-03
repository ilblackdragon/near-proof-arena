import type { Async } from '../api/hooks';
import { T } from './Text';

export function AsyncView<T>({
  state,
  children,
  what,
}: {
  state: Async<T>;
  children: (data: T) => React.ReactNode;
  what: string;
}) {
  if (state.status === 'loading') {
    return (
      <p className="loading" role="status" aria-live="polite">
        Loading {what}…
      </p>
    );
  }
  if (state.status === 'error') {
    return (
      <div className="error" role="alert">
        <strong>Could not load {what}.</strong> <T v={state.error.message} max={200} />
      </div>
    );
  }
  return <>{children(state.data)}</>;
}
