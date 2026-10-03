/* eslint-disable */
/**
 * GENERATED from common/schemas/candidate.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "VerifyRoute".
 */
export type VerifyRoute = 'native' | 'npai-v1' | 'native-lean';

/**
 * Parsed `candidate.toml`. Every field is a *claim* the judge validates.
 */
export interface CandidateManifest {
  agent: string;
  backend_family: string;
  build: BuildSection;
  challenge: string;
  entry: EntrySection;
  formal?: FormalSection | null;
  hardware: HardwareRequest;
  name: string;
  parent?: string | null;
  schema: string;
  security_profile_request: string;
}
/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "BuildSection".
 */
export interface BuildSection {
  outputs: string[];
  recipe: string;
}
/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "EntrySection".
 */
export interface EntrySection {
  prepare: string;
  prove: string;
  /**
   * Built NPAI image (relative path among `build.outputs`), required iff `verify_route = "npai-v1"`.
   */
  verifier_bytecode?: string | null;
  verify: string;
  /**
   * How the arena runs verification (v1.2, additive). `native` (default): the built `verify` executable. `npai-v1`: the arena's own NPAI interpreter runs `verifier_bytecode` (docs/INTERP_SPEC.md); `prepare` must then emit exactly `public_dir/public.bin`. `native-lean`: the judge builds `verify` itself from the Lean model `formal.verifier_model` with the governed Lean compiler (the candidate's binary is not used).
   */
  verify_route?: VerifyRoute | null;
}
/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "FormalSection".
 */
export interface FormalSection {
  /**
   * Lean constant whose *type* the judge constructs; candidate supplies the value.
   */
  certificate: string;
  lean_project: string;
  /**
   * `native-lean` route (v1.2, optional): the candidate-defined verifier model `ArenaCore.OracleVerifier` (e.g. `Candidate.Model.verify`) that the judge splices into the expected statement and compiles into `verify`.
   */
  verifier_model?: string | null;
  /**
   * Lean module declaring `verifier_model` (e.g. `Candidate.Model`).
   */
  verifier_model_module?: string | null;
}
/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "HardwareRequest".
 */
export interface HardwareRequest {
  gpu: boolean;
  min_ram_gb: number;
}
