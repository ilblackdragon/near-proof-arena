/* eslint-disable */
/**
 * GENERATED from common/schemas/assumption.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `Assumption`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;

/**
 * Governed cryptographic assumption, pinned to an exact Lean declaration in `formal-core` (`security/assumptions/<id>.json`).
 */
export interface Assumption {
  description: string;
  id: string;
  /**
   * Fully qualified Lean name of the hypothesis *definition* (a `Prop`-valued def in formal-core), e.g. `ArenaCore.Assumptions.Sha256CollisionResistant`.
   */
  lean_decl: string;
  /**
   * Structural content hash of the Lean declaration (lean4export NDJSON, `arena_formal_checker::ndjson::Export::decl_hash`, rendered `sha256:<hex>`; computed by `runners/formal-checker/scripts/pin-assumption-digests.sh`).
   */
  lean_decl_digest?: Digest | null;
  references: string[];
}
