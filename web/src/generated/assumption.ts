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
   * Fully qualified Lean name of the hypothesis *definition* (a `Prop`-valued def in formal-core), e.g. `Arena.Assumptions.Sha256CollisionResistant`.
   */
  lean_decl: string;
  /**
   * Digest of the Lean declaration's exported type+value (filled by the governance tooling; checked by the formal checker).
   */
  lean_decl_digest?: Digest | null;
  references: string[];
}
