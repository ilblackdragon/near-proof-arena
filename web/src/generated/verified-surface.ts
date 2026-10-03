/* eslint-disable */
/**
 * GENERATED from common/schemas/verified-surface.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `VerifiedSurface`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;

/**
 * The digests that define the *verified* surface. If all are equal between a child and its parent, formal results may be reused (`ProverOnly`).
 */
export interface VerifiedSurface {
  certificate_decl: string;
  challenge_id: string;
  checker_image: Digest;
  formal_tree: Digest;
  prepare_artifact: Digest;
  public_artifacts: Digest;
  verify_artifact: Digest;
}
