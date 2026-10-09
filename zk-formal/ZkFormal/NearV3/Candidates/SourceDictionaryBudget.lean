import ZkFormal.NearV3.Candidates.NativeEncodedBudget
import ZkFormal.NearV3.Rcpt.Candidates.SourceSizeEncoding
namespace ZkFormal.NearV3.Candidates.SourceDictionaryBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

private theorem weighted_sublist {α : Type} (f : α→Nat) {xs ys : List α}
    (h : xs.Sublist ys) : (xs.map f).sum≤(ys.map f).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons,List.sum_cons];omega
  | cons_cons a h ih => simp only [List.map_cons,List.sum_cons];omega

theorem computed_encoding (es : List ProofEntry)
    (hk : ∀e∈es,e.key.length=32)
    (hp : ∀e∈es,∀s∈e.proof.path,s.1.length=32) :
    (es.map fun e=>(ZkFormal.V3.encodeEntry e).length).sum=
      (es.map entrySizeCharge).sum+44*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he:=encoded_entry_charge e (hp e (by simp))
    have hh:=hk e (by simp)
    have ht:=ih (fun e he=>hk e (by simp [he])) (fun e he=>hp e (by simp [he]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Actual selected entries, with multiplicity preserved, fit the native
encoded dictionary. Unused entries can only increase its size. -/
theorem selected_dictionary_le (computed entries : List ProofEntry)
    (hs : computed.Sublist entries)
    (hk : ∀e∈computed,e.key.length=32)
    (hp : ∀e∈computed,∀s∈e.proof.path,s.1.length=32) :
    (computed.map entrySizeCharge).sum+44*computed.length+4≤
      (encList ZkFormal.V3.encodeEntry entries).length := by
  have hh:=weighted_sublist (fun e : ProofEntry=>(ZkFormal.V3.encodeEntry e).length) hs
  rw [computed_encoding computed hk hp] at hh
  simp only [encList,List.length_append,u32_len,concatAll_size]
  omega

/-- Current repeated-source filler accounting adds exactly 56 bytes per
repeated occurrence; that increment is not paid by selected-entry sublist coverage. -/
theorem duplicate_increment (payload N M : Nat) (h : M≤N) :
    payload+12*(N-M)+44*N+4=(payload+44*M+4)+56*(N-M) := by omega

def emptyEntry : ProofEntry := ⟨List.replicate 32 0,[],⟨0,0,[]⟩⟩
def emptySource (dup : Bool) : SrcpB :=
  {j:=0,L:=12,dup:=dup,root:=List.replicate 32 0,qe:=0,le:=0,ql:=0,
   leaf:=List.replicate 32 0,path:=[]}

/-- Concrete accounting regression only: this does not claim a complete
accepted checkD0a witness or authenticated source roots. -/
theorem repeated_accounting_regression :
    (encList ZkFormal.V3.encodeEntry [emptyEntry]).length=60 ∧
    DedupRender.size [emptySource false,emptySource true]+44*2+4=116 := by
  decide +kernel

theorem occurrence_lowerbound_fails :
    ¬(DedupRender.size [emptySource false,emptySource true]+44*2+4≤
      (encList ZkFormal.V3.encodeEntry [emptyEntry]).length) := by
  obtain ⟨h1,h2⟩:=repeated_accounting_regression
  rw [h1,h2]
  decide
end ZkFormal.NearV3.Candidates.SourceDictionaryBudget
