//! `PKG_WELLFORMED`: safe ingestion + manifest/layout validation. Runs no
//! candidate code (pure parsing in the worker), so results are not
//! tier-capped by the sandbox backend.

use crate::executor::{ExecError, JobRun, StageOut, MAX_PACKAGE_BYTES};
use crate::gate::Gate;
use crate::jobs::ValidateJob;
use arena_types::ReasonCode as RC;
use arena_archive::{ArchiveError, PackageError};
use arena_types::{GateStatus, ObligationId, ReasonCode};

pub fn run(r: &mut JobRun<'_>, j: &ValidateJob) -> Result<StageOut, ExecError> {
    let mut g = Gate::start(ObligationId::PkgWellformed);
    let package = &j.ctx.package_digest;
    let bytes = r.fetch(package, MAX_PACKAGE_BYTES)?;
    let dest = r.fresh("pkg");
    let mut out = StageOut::default();
    match arena_archive::ingest_bytes(&bytes, &dest, &arena_archive::Limits::default()) {
        Err(ArchiveError::Unsafe(m)) => g.fail(ReasonCode::ArchiveUnsafe, m),
        Err(ArchiveError::Io(e)) => return Err(ExecError::Infra(format!("extract: {e}"))),
        Ok(x) => {
            g.note(format!("package TreeDigest {}", x.digest));
            match arena_archive::validate_package(&x.root, &x.tree) {
                Err(PackageError::Io(e)) => return Err(ExecError::Infra(format!("manifest read: {e}"))),
                Err(e) => g.fail(ReasonCode::ManifestInvalid, e.to_string()),
                Ok(m) => {
                    if m.challenge != j.ctx.challenge_id {
                        g.fail(RC::ChallengeUnknown, format!("manifest names challenge {:?}, submission is for {:?}", m.challenge, j.ctx.challenge_id));
                    } else if m.security_profile_request != j.challenge.security_profile.id {
                        g.fail(RC::ProfileNotAllowed, format!("requested security profile {:?} is not the challenge's {:?}", m.security_profile_request, j.challenge.security_profile.id));
                    } else if m.hardware.gpu && j.challenge.hardware_profile.gpu.is_none() {
                        g.fail(RC::ManifestInvalid, "candidate requests a GPU; the challenge hardware profile has none");
                    } else {
                        let json = arena_types::canonical_json(&m).map_err(|e| ExecError::Infra(e.to_string()))?;
                        let d = r.upload("manifest", &json, false)?;
                        g.evidence("manifest", d, false);
                        g.note(format!("{} files, {} bytes; manifest ok", x.tree.files.len(), x.tree.total_bytes()));
                    }
                    out.manifest = Some(m);
                }
            }
        }
    }
    out.gates.push(g.finish(GateStatus::Pass, true));
    Ok(out)
}
