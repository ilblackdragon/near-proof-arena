import { Link } from 'react-router-dom';
export function NotFound() {
  return (
    <section>
      <h1>Not found</h1>
      <p>
        There is no page at this address. <Link to="/">Back to challenges</Link>.
      </p>
    </section>
  );
}
