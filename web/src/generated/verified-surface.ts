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
 * This interface was referenced by `VerifiedSurface`'s JSON-Schema
 * via the `definition` "VerifyRoute".
 */
export type VerifyRoute = 'native' | 'npai-v1' | 'native-lean';

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
  /**
   * `npai-v1`: SHA-256 digest of the built verifier bytecode image.
   */
  verifier_bytecode?: Digest | null;
  /**
   * `native-lean`: `[formal] verifier_model`.
   */
  verifier_model?: string | null;
  /**
   * `native-lean`: `[formal] verifier_model_module`.
   */
  verifier_model_module?: string | null;
  verify_artifact: Digest;
  /**
   * Effective verify route (`native` when the manifest omits it).
   */
  verify_route?: VerifyRoute | null;
}
