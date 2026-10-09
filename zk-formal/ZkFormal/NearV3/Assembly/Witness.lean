import ZkFormal.NearV3.Link.Records3
import ZkFormal.NearV3.Rcpt.Extract.RcptView
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Defs
import ZkFormal.Near.Link.Statements
import ZkFormal.V3.EncodeWitness
import NearSpecV3.PrepD0

/-!
Executable reconstruction from extracted views. These types contain no AIR or
native checker-success premise. Consistency, lookup-last selection, byte bounds,
source proofs and transition semantics remain separate obligations.

The dictionary retains encoded order and explicit unused filler entries: the
frozen checker compares distinct dictionary keys with source occurrence count,
which can repeat a key. Semantic goodness must prove no source selects a filler.
-/
namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

structure SourceEntryV3 where
  key : Bytes
  fromShard : Nat
  toShard : Nat
  receipts : ListV3
  path : SrcpB

def SourceEntryV3.entry (s : SourceEntryV3) : ProofEntry :=
  { key := s.key
    receipts := s.receipts.rs.map (fun r => r.toRcptV.toReceipt)
    proof :=
      { fromShard := s.fromShard
        toShard := s.toShard
        path := s.path.path.map (fun it => (Link3.toB it.sib, if it.dir then 1 else 0)) } }

/-- Checked source views or explicitly retained unused entries. Neither branch
is trusted by the type; the semantic relation must validate its use. -/
abbrev DictionaryEntryV3 := Sum SourceEntryV3 ProofEntry

def DictionaryEntryV3.entry : DictionaryEntryV3 → ProofEntry
  | .inl s => s.entry
  | .inr e => e

structure ExtV3 where
  nodes : List NodeS3
  values : List ValE
  heads : List HeadE
  receipts : RcptV3Vs
  dictionary : List DictionaryEntryV3

namespace ExtV3

def valuePosition (x : ExtV3) : Nat → Nat :=
  Link3.vpos ((x.values.head?.map ValE.vid).getD 0)

def rawStore (x : ExtV3) (tau : Nat) : List Bytes :=
  storeOf (Link3.recsOf x.valuePosition x.nodes) (Link3.valsOf3 x.nodes x.values) tau

/-- Stable first-occurrence dedup collapses shared records and node/value overlap.
`WitnessStore.store_partialTrie` proves exact native behavior is preserved. -/
def store (x : ExtV3) (tau : Nat) : List Bytes := (x.rawStore tau).eraseDups

def post (x : ExtV3) (tau : Nat) : Bytes :=
  Link3.toB (((x.heads.find? (fun h => h.tau == tau)).map HeadE.post).getD [])

def applied (x : ExtV3) : List Receipt :=
  x.receipts.flatMap (fun l => l.rs.map (fun r => r.toRcptV.toReceipt))

/-- Missing heads produce an invalid empty root, never implicit acceptance. -/
def transition (x : ExtV3) (tau : Nat) : Transition :=
  ⟨List.replicate 32 0, x.store tau, x.post tau⟩

end ExtV3

/-- The implicit count comes from the actual claim walk, not a free hint. -/
def stateWitnessOfV3 (k : WalkD0) (x : ExtV3) : StateWitness :=
  { epochId := k.c.epochId
    innerBytes := k.c.chunkInner
    inner := k.H
    main := x.transition 0
    entries := x.dictionary.map DictionaryEntryV3.entry
    appliedReceiptsHash := sha256 (encodeReceipts x.applied)
    nTransactions := 0
    implicit := k.implicitBlks.zipIdx.map (fun (_, i) => x.transition (i + 1))
    nNewTransactions := 0 }

def witnessOfV3 (k : WalkD0) (x : ExtV3) : Bytes :=
  V3.encodeWitnessFile (stateWitnessOfV3 k x)

theorem stateWitnessOfV3_implicit_length (k : WalkD0) (x : ExtV3) :
    (stateWitnessOfV3 k x).implicit.length = k.implicitBlks.length := by
  simp [stateWitnessOfV3]

theorem stateWitnessOfV3_entries (k : WalkD0) (x : ExtV3) :
    (stateWitnessOfV3 k x).entries = x.dictionary.map DictionaryEntryV3.entry := rfl

end ZkFormal.NearV3.Assembly
