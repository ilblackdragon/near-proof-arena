import ZkFormal.NearV3.Assembly.RcptNativeShapeIdentity
import ZkFormal.NearV3.Assembly.RcptCandidateListChain

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

inductive DecodedEntity where
  | header (start : Nat)
  | receipt (shape : RS)

def DecodedEntity.start : DecodedEntity→Nat
  | .header s=>s
  | .receipt y=>y.s

def DecodedEntity.rows : DecodedEntity→Nat
  | .header _=>12
  | .receipt y=>y.tot

def DecodedEntity.Valid (tr : Trace Fp) : DecodedEntity→Prop
  | .header s=>Fld tr 0 s 12 sCL
  | .receipt y=>Layout tr 0 y.s y.h y.Lp y.Lv y.Ls y.kt

/-- One ordered partition of physical header/receipt entities. -/
def DecodedSequence (tr : Trace Fp) : Nat→List DecodedEntity→Nat→Prop
  | s,[],e=>s=e
  | s,x::xs,e=>x.start=s ∧ x.Valid tr ∧ DecodedSequence tr (s+x.rows) xs e

def ListBlock.entities (B : ListBlock) : List DecodedEntity :=
  .header B.start::B.receipts.map DecodedEntity.receipt

theorem decoded_receipts (tr : Trace Fp) (ys : List RS) (start : Nat)
    (hc : Consec start (segsOf ys))
    (hl : ∀y∈ys,Layout tr 0 y.s y.h y.Lp y.Lv y.Ls y.kt) :
    DecodedSequence tr start (ys.map DecodedEntity.receipt) (segEnd start (segsOf ys)) := by
  induction ys generalizing start with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨hs,hc⟩ := hc
    refine ⟨hs,hl y (by simp),?_⟩
    have ht := ih (start+y.tot) hc (fun z hz=>hl z (by simp [hz]))
    simpa only [segsOf,List.map_cons,segEnd,hs,DecodedEntity.rows] using ht

theorem decoded_append (tr : Trace Fp) (xs ys : List DecodedEntity) (s m e : Nat)
    (hx : DecodedSequence tr s xs m) (hy : DecodedSequence tr m ys e) :
    DecodedSequence tr s (xs++ys) e := by
  induction xs generalizing s with
  | nil => cases hx;exact hy
  | cons x xs ih => exact ⟨hx.1,hx.2.1,ih _ hx.2.2⟩

theorem ListBlockWf.decoded {tr : Trace Fp} {B : ListBlock} (h : ListBlockWf tr 0 B) :
    DecodedSequence tr B.start (ListBlock.entities B) B.stop := by
  exact ⟨rfl,h.header,decoded_receipts tr B.receipts (B.start+12) h.consecutive h.layouts⟩

/-- The canonical physical list extraction is an ordered partition, retaining
all list headers and every receipt occurrence. -/
theorem ListChain.decoded {tr : Trace Fp} {s e : Nat} {bs : List ListBlock}
    (h : ListChain tr 0 s bs e) :
    DecodedSequence tr s (bs.flatMap ListBlock.entities) e := by
  induction h with
  | last hw _ => simpa using ListBlockWf.decoded hw
  | cons hw hc ih => exact decoded_append tr _ _ _ _ _ (ListBlockWf.decoded hw) ih

end ZkFormal.NearV3.Assembly.RcptSkeleton
