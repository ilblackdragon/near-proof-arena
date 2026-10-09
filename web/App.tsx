import { Route, Routes } from 'react-router-dom';
import { Layout } from './components/Layout';
import { ChallengesPage } from './pages/ChallengesPage';
import { ChallengePage } from './pages/ChallengePage';
import { SubmissionsPage } from './pages/SubmissionsPage';
import { SubmissionPage } from './pages/SubmissionPage';
import { ComparePage } from './pages/ComparePage';
import { NotFound } from './pages/NotFound';
import { ResearchPage } from './pages/ResearchPage';

export function AppRoutes() {
  return (
    <Routes>
      <Route element={<Layout />}>
        <Route index element={<ChallengesPage />} />
        <Route path="challenges/:id" element={<ChallengePage />} />
        <Route path="submissions" element={<SubmissionsPage />} />
        <Route path="submissions/:id" element={<SubmissionPage />} />
        <Route path="compare" element={<ComparePage />} />
        <Route path="research" element={<ResearchPage />} />
        <Route path="*" element={<NotFound />} />
      </Route>
    </Routes>
  );
}
