/* eslint-disable */
/**
 * GENERATED from common/schemas/candidate.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

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
  verify: string;
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
}
/**
 * This interface was referenced by `CandidateManifest`'s JSON-Schema
 * via the `definition` "HardwareRequest".
 */
export interface HardwareRequest {
  gpu: boolean;
  min_ram_gb: number;
}
