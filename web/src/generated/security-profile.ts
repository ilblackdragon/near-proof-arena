/* eslint-disable */
/**
 * GENERATED from common/schemas/security-profile.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * This interface was referenced by `SecurityProfile`'s JSON-Schema
 * via the `definition` "AdversaryClass".
 */
export type AdversaryClass = 'classical';
/**
 * This interface was referenced by `SecurityProfile`'s JSON-Schema
 * via the `definition` "SecurityModel".
 */
export type SecurityModel = 'standard' | 'random_oracle';
/**
 * This interface was referenced by `SecurityProfile`'s JSON-Schema
 * via the `definition` "Privacy".
 */
export type Privacy = 'validity_only' | 'zero_knowledge';
/**
 * This interface was referenced by `SecurityProfile`'s JSON-Schema
 * via the `definition` "SetupModel".
 */
export type SetupModel = 'none' | 'transparent' | 'approved_ceremony';

/**
 * Governed security profile (`security/profiles/<id>.json`).
 */
export interface SecurityProfile {
  adversary: AdversaryClass;
  /**
   * Ids into `security/assumptions/*.json`; each pins an exact Lean declaration.
   */
  allowed_assumptions: string[];
  deployment_proofs_log2: number;
  id: string;
  max_aggregation_depth: number;
  max_hash_queries_log2: number;
  max_prover_queries_log2: number;
  model: SecurityModel;
  privacy: Privacy;
  setup_model: SetupModel;
  target_bits: number;
}
