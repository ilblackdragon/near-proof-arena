//! `PKG_WELLFORMED`: safe ingestion + manifest/layout validation. Runs no
//! candidate code (pure parsing in the worker), so results are not
//! tier-capped by the sandbox backend.

use crate::executor::{ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::ValidateJob;
use arena_archive::{ArchiveError, PackageError};
use arena_types::{GateStatus, ObligationId, ReasonCode};

pub fn run(r: &mut JobRun<'_>, j: &ValidateJob) -> Result<StageOut, ExecError> {
    let mut g = Gate::start(ObligationId::PkgWellformed);
    let bytes = r.fetch(&j.package, MAX_PACKAGE_BYTES)?;
    g.evidence("package", j.package.clone(), false);
    let dest = r.fresh("pkg");
    let mut out = StageOut::default();
    match arena_archive::ingest_bytes(&bytes, &dest, &arena_archive::Limits::default()) {
        Err(ArchiveError::Unsafe(m)) => g.fail(ReasonCode::ArchiveUnsafe, m),
        Err(ArchiveError::Io(e)) => return Err(ExecError::Infra(format!("extract: {e}"))),
        Ok(x) => {
            r.record("package_tree", x.digest.clone(), false, false);
            g.evidence("package_tree", x.digest.clone(), false);
            match arena_archive::validate_package(&x.root, &x.tree) {
                Err(PackageError::Io(e)) => {
                    return Err(ExecError::Infra(format!("manifest read: {e}")))
                }
                Err(e) => g.fail(ReasonCode::ManifestInvalid, e.to_string()),
                Ok(m) => {
                    if m.challenge != j.challenge_id {
                        g.fail(
                            ReasonCode::ChallengeUnknown,
                            format!(
                                "manifest names challenge {:?}, submission is for {:?}",
                                m.challenge, j.challenge_id
                            ),
                        );
                    } else {
                        let json = arena_types::canonical_json(&m)
                            .map_err(|e| ExecError::Infra(e.to_string()))?;
                        let d = r.upload("manifest", &json, false)?;
                        g.evidence("manifest", d, false);
                        g.note(format!(
                            "{} files, {} bytes; manifest ok",
                            x.tree.files.len(),
                            x.tree.total_bytes()
                        ));
                    }
                    out.manifest = Some(m);
                }
            }
        }
    }
    out.gates.push(g.finish(GateStatus::Pass, true));
    Ok(out)
}
