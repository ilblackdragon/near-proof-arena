import type { SubmissionView } from '../api/types';

/** Family names describe candidates; they are not verified method classifications. */
export function researchGroups(submissions: SubmissionView[], query: string, challenge: string) {
  const groups = new Map<string, { family: string; challengeId: string; submissions: SubmissionView[] }>();
  const needle = query.trim().toLowerCase();
  for (const s of submissions) {
    if (challenge && s.challenge_id !== challenge) continue;
    if (needle && ![s.backend_family, s.candidate_name, s.agent, s.id].some((v) => v.toLowerCase().includes(needle))) continue;
    // Separate scopes even when the candidate uses the same family label.
    const key = JSON.stringify([s.challenge_id, s.backend_family]);
    let group = groups.get(key);
    if (!group) {
      group = { family: s.backend_family, challengeId: s.challenge_id, submissions: [] };
      groups.set(key, group);
    }
    group.submissions.push(s);
  }
  return [...groups.values()]
    .sort((a, b) => a.family.localeCompare(b.family) || a.challengeId.localeCompare(b.challengeId))
    .map((g) => ({
      ...g,
      submissions: g.submissions.sort((a, b) => a.created_at.localeCompare(b.created_at) || a.id.localeCompare(b.id)),
    }));
}
