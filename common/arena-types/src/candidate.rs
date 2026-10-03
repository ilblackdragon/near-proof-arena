use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Parsed `candidate.toml`. Every field is a *claim* the judge validates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CandidateManifest {
    pub schema: String,
    pub name: String,
    pub agent: String,
    pub challenge: String,
    pub parent: Option<String>,
    pub backend_family: String,
    pub security_profile_request: String,
    pub hardware: HardwareRequest,
    pub build: BuildSection,
    pub entry: EntrySection,
    pub formal: Option<FormalSection>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct HardwareRequest {
    pub gpu: bool,
    pub min_ram_gb: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct BuildSection {
    pub recipe: String,
    pub outputs: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct EntrySection {
    pub prepare: String,
    pub prove: String,
    pub verify: String,
    /// How the arena executes the verifier (v1.2, optional):
    /// `"npai-v1"` = judge interpreter on `verifier_bytecode`;
    /// `"native-lean"` = judge builds the verifier executable from the Lean
    /// model `formal.verifier_model` with the governed Lean compiler.
    /// Absent = legacy candidate-built `verify` (no formal route admits it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verify_route: Option<String>,
    /// `npai-v1` route: path of the verifier bytecode image.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_bytecode: Option<String>,
}

pub const VERIFY_ROUTES: &[&str] = &["npai-v1", "native-lean"];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FormalSection {
    pub lean_project: String,
    /// Lean constant whose *type* the judge constructs; candidate supplies the value.
    pub certificate: String,
    /// `native-lean` route (v1.2, optional): the candidate-defined verifier
    /// model `ArenaCore.OracleVerifier` (e.g. `Candidate.Model.verify`) that the
    /// judge splices into the expected statement and compiles into `verify`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_model: Option<String>,
    /// Lean module declaring `verifier_model` (e.g. `Candidate.Model`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_model_module: Option<String>,
}

fn is_lean_ident_path(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 255
        && s.split('.').all(|c| {
            let mut cs = c.chars();
            matches!(cs.next(), Some(ch) if ch.is_ascii_alphabetic() || ch == '_')
                && cs.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
        })
}

pub const CANDIDATE_SCHEMA: &str = "arena-candidate-v1";

#[derive(Debug, thiserror::Error)]
pub enum ManifestError {
    #[error("toml: {0}")]
    Toml(#[from] toml::de::Error),
    #[error("invalid manifest: {0}")]
    Invalid(String),
}

fn is_safe_relpath(p: &str) -> bool {
    !p.is_empty()
        && p.len() <= 255
        && !p.starts_with('/')
        && p.split('/').all(|c| !c.is_empty() && c != "." && c != "..")
        && p.bytes().all(|b| b.is_ascii_graphic())
}

impl CandidateManifest {
    pub fn parse(s: &str) -> Result<Self, ManifestError> {
        let m: CandidateManifest = toml::from_str(s)?;
        m.validate()?;
        Ok(m)
    }

    pub fn validate(&self) -> Result<(), ManifestError> {
        let bad = |s: &str| Err(ManifestError::Invalid(s.to_string()));
        if self.schema != CANDIDATE_SCHEMA {
            return bad("unsupported schema");
        }
        let name_ok = !self.name.is_empty()
            && self.name.len() <= 48
            && self
                .name
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
        if !name_ok {
            return bad("name must match [a-z0-9-]{1,48}");
        }
        if !self.challenge.starts_with("chl_") {
            return bad("challenge must be a chl_ id");
        }
        if self.agent.len() > 64 || self.backend_family.len() > 64 {
            return bad("agent/backend_family too long");
        }
        let mut paths = vec![
            self.build.recipe.as_str(),
            self.entry.prepare.as_str(),
            self.entry.prove.as_str(),
            self.entry.verify.as_str(),
        ];
        paths.extend(self.build.outputs.iter().map(|s| s.as_str()));
        if let Some(f) = &self.formal {
            paths.push(f.lean_project.as_str());
            if !is_lean_ident_path(&f.certificate) {
                return bad("formal.certificate must be a dotted Lean identifier");
            }
            match (&f.verifier_model, &f.verifier_model_module) {
                (None, None) => {}
                (Some(d), Some(m)) if is_lean_ident_path(d) && is_lean_ident_path(m) => {}
                _ => return bad("formal.verifier_model and verifier_model_module must both be dotted Lean identifiers"),
            }
        }
        if let Some(b) = &self.entry.verifier_bytecode {
            paths.push(b.as_str());
        }
        match self.entry.verify_route.as_deref() {
            None => {}
            Some(r) if !VERIFY_ROUTES.contains(&r) => return bad("unknown entry.verify_route"),
            Some("native-lean") => {
                if self.formal.as_ref().and_then(|f| f.verifier_model.as_ref()).is_none() {
                    return bad("verify_route native-lean requires formal.verifier_model");
                }
            }
            Some("npai-v1") => {
                if self.entry.verifier_bytecode.is_none() {
                    return bad("verify_route npai-v1 requires entry.verifier_bytecode");
                }
            }
            Some(_) => {}
        }
        if !paths.iter().all(|p| is_safe_relpath(p)) {
            return bad("unsafe relative path");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const OK: &str = r#"
schema = "arena-candidate-v1"
name = "ref-reexec"
agent = "arena"
challenge = "chl_00"
backend_family = "reexec"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 4 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/prepare", "out/prove", "out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
[formal]
lean_project = "formal"
certificate = "Candidate.certificate"
"#;
    #[test]
    fn parses() {
        CandidateManifest::parse(OK).unwrap();
    }
    #[test]
    fn native_lean_route() {
        let with_route = OK.replace("verify = \"out/verify\"", "verify = \"out/verify\"\nverify_route = \"native-lean\"");
        assert!(CandidateManifest::parse(&with_route).is_err(), "model required");
        let full = format!("{with_route}verifier_model = \"Candidate.Model.verify\"\nverifier_model_module = \"Candidate.Model\"\n");
        let m = CandidateManifest::parse(&full).unwrap();
        assert_eq!(m.formal.unwrap().verifier_model.as_deref(), Some("Candidate.Model.verify"));
        let bad = full.replace("Candidate.Model.verify", "Candidate.Model.verify x");
        assert!(CandidateManifest::parse(&bad).is_err());
    }
    #[test]
    fn rejects_traversal() {
        assert!(CandidateManifest::parse(&OK.replace("out/verify\"\n", "../x\"\n")).is_err());
    }
    #[test]
    fn rejects_unknown_field() {
        assert!(CandidateManifest::parse(&format!("security_bits = 128\n{OK}")).is_err());
    }
}
