import ZkFormal.NearV3.Rcpt.Candidates.NativeFillers
import ZkFormal.NearV3.Rcpt.Candidates.SourceSizeEncoding
import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceShaPressure
open NearSpec NearSpecV3

/-- Distinct legal32-byte siblings, with the native left-sibling direction. -/
def longPath (n : Nat) : List (Bytes×Nat) :=
  (List.range n).map fun i => (leN 32 i,0)

def entry (n : Nat) : ProofEntry := ⟨leN 32 0,[],⟨0,0,longPath n⟩⟩

def entryRoot (n : Nat) : Bytes :=
  rootFromPath (sha256 (sha256 (u64 0++encodeReceipts []))) (longPath n)

/-- Exact native receipt-proof verification, not whole-claim acceptance. -/
theorem verifies (n : Nat) : verifyReceiptProof (entryRoot n) (entry n)=true := by
  simp [verifyReceiptProof,entryRoot,entry]

theorem path_width (n : Nat) : ∀ s∈longPath n,s.1.length=32 ∧ s.2=0 := by
  intro s hs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨leN_len 32 i,rfl⟩

theorem path_length (n : Nat) : (longPath n).length=n := by simp [longPath]

theorem entry_encoded_length (n : Nat) : (ZkFormal.V3.encodeEntry (entry n)).length=56+33*n := by
  have hh := encoded_entry_charge (entry n) (fun s hs => (path_width n s hs).1)
  simp only [entrySizeCharge,entry,path_length,encList,concatAll,leN_len,List.length_append,u64_len,u32_len,List.map_nil,List.length_nil] at hh ⊢
  omega

/-- Actual native compression inputs of the path fold. -/
def pathInputs (acc : Bytes) : List (Bytes×Nat) → List Bytes
  | [] => []
  | (sib,dir)::rest =>
    let msg := if dir==0 then sib++acc else acc++sib
    msg::pathInputs (sha256 msg) rest

private theorem pathInputs_prefix (path : List (Bytes×Nat)) (acc : Bytes)
    (hw : ∀ s∈path,s.1.length=32 ∧ s.2=0) :
    ((pathInputs acc path).map fun m => m.take 32)=path.map Prod.fst := by
  induction path generalizing acc with
  | nil => rfl
  | cons s rest ih =>
    have hs := hw s (by simp)
    have ht := ih (sha256 (s.1++acc)) (fun t ht => hw t (by simp [ht]))
    rcases s with ⟨sib,dir⟩
    simp only at hs
    simp only [pathInputs,hs.2,beq_self_eq_true,ite_true,List.map_cons,ht]
    congr 1
    rw [←hs.1,List.take_left]

/-- Distinct sibling prefixes force distinct SHA preimages independently of
SHA collision resistance, even for a single very long native proof. -/
theorem path_inputs_nodup (n : Nat) (hn : n≤256^32) (acc : Bytes) :
    (pathInputs acc (longPath n)).Nodup := by
  have hnkeys : ((longPath n).map Prod.fst).Nodup := by
    simp only [longPath,List.map_map,Function.comp_def]
    apply List.pairwise_map.mpr
    apply List.pairwise_lt_range.imp_of_mem
    intro i j hi hj hij he
    have hi' : i<256^32 := by have := List.mem_range.mp hi; omega
    have hj' : j<256^32 := by have := List.mem_range.mp hj; omega
    have hh := congrArg leNat he
    rw [leNat_leN' 32 i hi',leNat_leN' 32 j hj'] at hh
    omega
  rw [←pathInputs_prefix (longPath n) acc (path_width n)] at hnkeys
  exact (List.pairwise_map.mp hnkeys).imp (fun h he => h (congrArg (fun m => m.take 32) he))

private theorem path_input_rows (path : List (Bytes×Nat)) (acc : Bytes)
    (ha : acc.length=32) (hw : ∀ s∈path,s.1.length=32) :
    ((pathInputs acc path).map fun m => msgRows m.length).sum=35*path.length := by
  induction path generalizing acc with
  | nil => rfl
  | cons s rest ih =>
    have hs := hw s (by simp)
    have ht := ih (sha256 (if s.2==0 then s.1++acc else acc++s.1))
      (ArenaCore.sha256_length _) (fun t ht => hw t (by simp [ht]))
    rcases s with ⟨sib,dir⟩
    simp only at hs ht
    simp only [pathInputs,List.map_cons,List.sum_cons,List.length_cons]
    rw [ht]
    have hm : (if dir==0 then sib++acc else acc++sib).length=64 := by
      split <;> simp [List.length_append,hs,ha]
    rw [hm]
    simp only [msgRows]
    omega

theorem exact_path_rows (n : Nat) :
    ((pathInputs (sha256 (sha256 (u64 0++encodeReceipts []))) (longPath n)).map
      fun m => msgRows m.length).sum=35*n := by
  rw [path_input_rows _ _ (ArenaCore.sha256_length _) (fun s hs => (path_width n s hs).1),path_length]

/-- This structurally legal, natively verified source entry alone exceeds two
SHA tables. Its dictionary entry leaves468552 bytes below the native raw cap.
This theorem deliberately does not assert complete checkD0a acceptance. -/
theorem pressure_fixture :
    verifyReceiptProof (entryRoot 240000) (entry 240000)=true ∧
    (ZkFormal.V3.encodeEntry (entry 240000)).length=7920056 ∧
    (ZkFormal.V3.encodeEntry (entry 240000)).length+468552=8388608 ∧
    (pathInputs (sha256 (sha256 (u64 0++encodeReceipts []))) (longPath 240000)).Nodup ∧
    2*2^22<msgRows 32+
      ((pathInputs (sha256 (sha256 (u64 0++encodeReceipts []))) (longPath 240000)).map
        fun m => msgRows m.length).sum := by
  refine ⟨verifies _,entry_encoded_length _,?_,path_inputs_nodup _ (by decide) _,?_⟩
  · rw [entry_encoded_length]
  · rw [exact_path_rows]; decide

/-- Even charging all fixed entry overhead against the same8MiB budget does not
make the bound small enough. This is correlated arithmetic, not native coverage. -/
theorem correlated_source_bound (lists paths : Nat)
    (hl : 1≤lists) (hb : 56*lists+33*paths+224≤8388608) :
    sourceShaFor lists paths≤8896703 := by
  have hsum : lists+paths≤254192 := by omega
  simp only [sourceShaFor,msgRows]
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SourceShaPressure
