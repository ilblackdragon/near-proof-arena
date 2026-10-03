import { useEffect, useState } from 'react';
import { NavLink, Outlet } from 'react-router-dom';
import { isMockApi, onMockDetected } from '../api/client';
import { API_BASE } from '../config';

export function Layout() {
  const [mock, setMock] = useState(isMockApi());
  useEffect(() => onMockDetected(() => setMock(true)), []);
  return (
    <div className="app">
      <a href="#main" className="skip">
        Skip to content
      </a>
      {mock && (
        <div className="mock-banner" role="alert">
          MOCK API · demo fixtures only — this page is served by the development mock API. Nothing
          shown is a real arena result.
        </div>
      )}
      <header className="topbar">
        <div className="brand">
          <span className="brand-mark" aria-hidden="true">
            ⊢
          </span>
          <span>
            NEAR Proof Arena <span className="brand-sub">judge results</span>
          </span>
        </div>
        <nav aria-label="Primary">
          <NavLink to="/" end>
            Challenges
          </NavLink>
          <NavLink to="/submissions">Submissions</NavLink>
          <NavLink to="/compare">Compare</NavLink>
        </nav>
      </header>
      <main id="main" tabIndex={-1}>
        <Outlet />
      </main>
      <footer className="footer">
        <p>
          Read-only view of the arena API{API_BASE ? ` at ${API_BASE}` : ''}. Admission requires a
          judge-run build, kernel-checked Lean certificates, conformance and adversarial tests, and
          judge-measured benchmarks. Candidate-supplied text is shown verbatim as inert text.
        </p>
      </footer>
    </div>
  );
}
