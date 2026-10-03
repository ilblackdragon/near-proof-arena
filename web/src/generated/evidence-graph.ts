/* eslint-disable */
/**
 * GENERATED from common/schemas/evidence-graph.schema.json by web/scripts/gen-types.mjs.
 * Do not edit by hand; run `pnpm gen:types`.
 */

/**
 * `sha256:<64 lowercase hex>`
 *
 * This interface was referenced by `EvidenceGraph`'s JSON-Schema
 * via the `definition` "Digest".
 */
export type Digest = string;
/**
 * This interface was referenced by `EvidenceGraph`'s JSON-Schema
 * via the `definition` "EdgeStatus".
 */
export type EdgeStatus = 'checked' | 'trusted' | 'tested' | 'missing';
/**
 * This interface was referenced by `EvidenceGraph`'s JSON-Schema
 * via the `definition` "NodeKind".
 */
export type NodeKind =
  | 'nearcore_source'
  | 'formal_semantics'
  | 'backend_semantics'
  | 'theorem'
  | 'assumption'
  | 'artifact'
  | 'tcb_component'
  | 'test_suite'
  | 'measurement';

export interface EvidenceGraph {
  edges: EvidenceEdge[];
  nodes: EvidenceNode[];
}
/**
 * This interface was referenced by `EvidenceGraph`'s JSON-Schema
 * via the `definition` "EvidenceEdge".
 */
export interface EvidenceEdge {
  evidence: Digest[];
  from: string;
  /**
   * e.g. `refines`, `binds`, `assumes`, `built_from`, `tested_against`.
   */
  kind: string;
  note: string;
  status: EdgeStatus;
  to: string;
}
/**
 * This interface was referenced by `EvidenceGraph`'s JSON-Schema
 * via the `definition` "EvidenceNode".
 */
export interface EvidenceNode {
  digest?: Digest | null;
  id: string;
  kind: NodeKind;
  label: string;
}
