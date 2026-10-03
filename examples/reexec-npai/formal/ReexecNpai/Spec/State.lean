import ReexecNpai.Spec.Front
import ReexecNpai.Spec.RcptPos
import ReexecNpai.Trie.Lemmas
import ReexecNpai.Roundtrip

/-!
# Phase interfaces: state predicates

The verifier body is `seqs [pSetup, pClaim, pProof, pReceipts, pParse, pHash,
pRootIs (CLM + 117), pBatch, pFinal]`. This file fixes the state predicates
between phases. Each phase has a soundness lemma (`wp`: every normal exit
establishes the post-state and the Lean-level facts it checked) and a
completeness lemma (`twp`: if the Lean-level facts hold, the phase exits
normally within a cost bound). The phases are proven in `Spec/*.lean`;
`Main.lean` composes them.
-/

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Receipts -/

/-- Offset of receipt `i` in the proof. -/
def rOff (rs : List Receipt) (i : Nat) : Nat := 4 + (concatAll ((rs.take i).map Receipt.encode)).length

/-- Receipt-table entry (10 × u32) of receipt `r` encoded at address `A`. -/
def rtBytes (r : Receipt) (A : Nat) : Bytes :=
  let pred := A + 4
  let recv := pred + r.predecessorId.length + 4
  let rid := recv + r.receiverId.length
  let signer := rid + 37
  let pk := signer + r.signerId.length
  let gp := pk + 1 + r.signerPk.data.length
  u32 pred ++ u32 r.predecessorId.length ++ u32 recv ++ u32 r.receiverId.length ++ u32 rid ++
    u32 signer ++ u32 r.signerId.length ++ u32 pk ++ u32 gp ++ u32 (gp + 29)

/-- Lean-level facts established by the receipts phase. -/
structure RcptsOK (cb pb : Bytes) (rs : List Receipt) (R : Nat) : Prop where
  n4 : 4 ≤ pb.length
  count : leNat (sl pb 0 4) = rs.length
  dec : readMany decReceipt rs.length (pb.drop 4) = some (rs, pb.drop R)
  Rle : R ≤ pb.length
  cnt_claim : rs.length = (claimOf cb).receiptCount
  n_pos : 1 ≤ rs.length
  n_max : rs.length ≤ Params.maxBatch
  gas : (rs.length - 1) * Params.G < (claimOf cb).gasLimit
  slice : rs.all Receipt.inSlice = true
  nodup : (rs.map Receipt.receiptId).Nodup
  commit : receiptsCommitment (claimOf cb).shardId rs = (claimOf cb).receiptsCommitment

/-- Memory facts after the receipts phase that later phases rely on. -/
structure RcptsMem (cb pb : Bytes) (rs : List Receipt) (R : Nat) (m : M) : Prop extends ClaimIn cb m where
  ok : RcptsOK cb pb rs R
  rcpts : readMem m.mem PF R = pb.take R
  plen : pb.length ≤ PMAX
  pend : rd32 m C_PEND = PF + pb.length
  nC : rd32 m C_N = rs.length
  rend : rd32 m C_REND = PF + R
  rt : ∀ i (h : i < rs.length), readMem m.mem (RT + 64 * i) 40 = rtBytes rs[i] (PF + rOff rs i)

/-- After the receipts phase the whole proof copy is still intact. -/
structure RcptsSt (cb pb : Bytes) (rs : List Receipt) (R : Nat) (m : M) : Prop
    extends RcptsMem cb pb rs R m where
  proof : readMem m.mem PF pb.length = pb

/-! ## Trie -/

/-- Arena fields in memory. -/
def EntMem (m : M) (j : Nat) (e : Ent) : Prop :=
  rd32 m (AR + 24 * j) = e.pre ∧ rd32 m (AR + 24 * j + 4) = e.preLen ∧
  rd32 m (AR + 24 * j + 8) = e.pslot ∧ rd32 m (AR + 24 * j + 12) = e.kid ∧
  rd32 m (AR + 24 * j + 16) = e.res ∧ rd32 m (AR + 24 * j + 20) = e.val

/-- The trie section in memory, with current values `vals`: arena and child
list, value regions, preimages up to placeholders, record headers. -/
structure TrieMem (pb : Bytes) (A : List Ent) (K : List Nat) (vals : Nat → Bytes) (m : M) : Prop where
  amem : ∀ j (h : j < A.length), EntMem m j A[j]
  kmem : ∀ i (h : i < K.length), rd32 m (KL + 4 * i) = K[i]
  krange : ∀ j (h : j < A.length), A[j].kid + nKids A[j].nf ≤ K.length
  klen : K.length ≤ NCAP
  nodes : rd32 m C_NODES = A.length
  vmem : ∀ j (h : j < A.length), hasVal A[j].nf = true →
    readMem m.mem A[j].val (vlenAt pb A[j]) = vals j ∧ (vals j).length = vlenAt pb A[j]
  lmem : ∀ j (h : j < A.length), hasVal A[j].nf = true →
    readMem m.mem (A[j].val - 4) 4 = pseg pb (A[j].val - 4) 4
  pmem : ∀ j (h : j < A.length), ∃ z zs, z.length = 32 ∧ zs.length = nKids A[j].nf ∧
    (∀ x ∈ zs, x.length = 32) ∧ readMem m.mem A[j].pre A[j].preLen = preImg A[j].nf (vlenAt pb A[j]) z zs
  hmem : ∀ j (h : j < A.length), match A[j].nf with
    | .ext _ _ _ => readMem m.mem (A[j].pre - 1) 1 = pseg pb (A[j].pre - 1) 1
    | .branch _ _ _ => readMem m.mem (A[j].pre - 2) 2 = pseg pb (A[j].pre - 2) 2
    | _ => True

/-- Lean-level facts established by the parse: the trie section decodes to the
tree the arena represents (with the values from the proof). -/
structure TrieOK (pb : Bytes) (R : Nat) (A : List Ent) (K : List Nat) : Prop where
  wf : ArenaWF pb A K (PF + R + 4)
  dec : decTrie (pb.drop R) = some (treeAt A K (vals0 pb A) (A.length - 1))
  size : (treeAt A K (vals0 pb A) (A.length - 1)).revealedBytes ≤ Params.maxWitnessBytes

/-- State during and after the trie phases. -/
structure TrieSt (cb pb : Bytes) (rs : List Receipt) (R : Nat) (A : List Ent) (K : List Nat)
    (vals : Nat → Bytes) (m : M) : Prop extends RcptsMem cb pb rs R m where
  tok : TrieOK pb R A K
  tmem : TrieMem pb A K vals m

/-- Inputs as seen by `run` (tapes shorter than `2^32`). -/
def TapesOK (cb pb : Bytes) : Prop := cb.length < 4294967296 ∧ pb.length < 4294967296

/-- The root of the represented trie. -/
def rootT (A : List Ent) (K : List Nat) (vals : Nat → Bytes) : PTrie := treeAt A K vals (A.length - 1)

/-- Memory below the proof copy is unchanged except the computed root `C_ROOT`
(the frame of the hash pass). -/
def HashFrame (m m' : M) : Prop :=
  ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → m'.mem a = m.mem a

/-! ## Batch -/

/-- Accumulated batch outputs in memory. -/
structure BatchMem (acc : Acc) (m : M) : Prop where
  leaves : readMem m.mem OL (32 * acc.outcomes.length) = concatAll (acc.outcomes.map Outcome.leaf)
  refunds : rd32 m C_RBEND = RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length ∧
    readMem m.mem (RB + 4) (concatAll (acc.refunds.map Receipt.encode)).length =
      concatAll (acc.refunds.map Receipt.encode)
  nref : rd32 m C_NREF = acc.refunds.length
  tokens : readMem m.mem C_TOK 16 = u128 acc.tokensBurnt
  rbcap : RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length ≤ AR

end ReexecNpai
