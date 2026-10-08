import ZkFormal.NearV3.Rcpt.Candidates.AccountShaJobs
import ZkFormal.Near.Spec.SoundAccount
import ZkFormal.Near.Render.Proof.AcctFacts
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

/-- Concrete account record from original native bytes and the final native
amount. The closing receipt version stays explicit until ledger allocation. -/
def nativeAccountView (vid closing : Nat) (pre : Bytes) (amount : Nat) : AcctV :=
  ⟨vid,closing,pre.map UInt8.toNat,(u128 amount).map UInt8.toNat⟩

theorem nativeAccountView_bytes (vid closing : Nat) (pre : Bytes) (amount : Nat) :
    ∀x∈(nativeAccountView vid closing pre amount).pre++(nativeAccountView vid closing pre amount).post,x<256 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx <;>
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hx <;> exact b.toNat_lt

theorem nativeAccountView_lengths (vid closing : Nat) {pre : Bytes} {a : Account}
    (hd : Account.decode pre=some a) (amount : Nat) :
    (nativeAccountView vid closing pre amount).pre.length=72 ∧
      (nativeAccountView vid closing pre amount).post.length=16 := by
  have hl:=(Sound.decode_wf hd).2.2.2.2
  simp [nativeAccountView,u128,leN_length,hl]

/-- Updating the native amount leaves the full locked/code/storage suffix
unchanged, exactly matching the actual VPOST preimage emitted by AcctV3. -/
theorem nativeAccountView_payload (vid closing : Nat) {pre : Bytes} {a : Account}
    (hd : Account.decode pre=some a) (amount : Nat) :
    (nativeAccountView vid closing pre amount).post++
      (nativeAccountView vid closing pre amount).pre.drop 16=
      ({a with amount:=amount}.encode).map UInt8.toNat := by
  rw [←Sound.encode_decode hd]
  simp [nativeAccountView,Account.encode,List.append_assoc,List.drop_append,u128,leN_length]

/-- Native-byte construction discharges the SHA byte range independently of
AcctWf's weaker field-canonical range. -/
theorem nativeAccountView_job_bytes (vid closing : Nat) (pre : Bytes) (amount : Nat) :
    ∀m∈accountShaJobs [nativeAccountView vid closing pre amount],∀x∈m.bytes,x<256 := by
  intro m hm x hx
  simp only [accountShaJobs,List.map_cons,List.map_nil,List.mem_singleton] at hm
  subst m
  rcases List.mem_append.mp hx with hx|hx
  · exact nativeAccountView_bytes vid closing pre amount x (List.mem_append_right _ hx)
  · exact nativeAccountView_bytes vid closing pre amount x (List.mem_append_left _ (List.mem_of_mem_drop hx))

theorem nativeAccountView_notMax (vid closing : Nat) {pre : Bytes} {a : Account}
    (hd : Account.decode pre=some a) (amount : Nat) :
    ∃i,i<16 ∧ (nativeAccountView vid closing pre amount).pre.getD i 0≠255 := by
  apply Classical.byContradiction
  intro h
  have hall : ∀i,i<16 → (pre.map UInt8.toNat).getD i 0=255 := by
    intro i hi
    apply Classical.byContradiction
    intro hn
    exact h ⟨i,hi,hn⟩
  have hl:=(Sound.decode_wf hd).2.2.2.2
  have hm:=ZkFormal.Near.Render.leNat_255 (pre.take 16) (by simp [hl]) (by
    intro i hi
    have hp:i<pre.length:=by omega
    simpa only [ZkFormal.Near.Render.toNats,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_take,hi,ite_true] using hall i hi)
  simp [Account.decode,hl,hm] at hd

theorem nativeAccountView_wf (vid closing : Nat) (hk:vid<Algebra.P) (ht:closing<Algebra.P)
    {pre : Bytes} {a : Account} (hd : Account.decode pre=some a) (amount : Nat) :
    AcctWf [nativeAccountView vid closing pre amount] := by
  refine ⟨by simp,?_,?_,?_⟩
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact ⟨(nativeAccountView_lengths vid closing hd amount).1,
      (nativeAccountView_lengths vid closing hd amount).2,hk,ht⟩
  · intro v hv _
    simp only [List.mem_singleton] at hv
    subst v
    exact nativeAccountView_notMax vid closing hd amount
  · intro v hv x hx
    simp only [List.mem_singleton] at hv
    subst v
    exact Nat.lt_trans (nativeAccountView_bytes vid closing pre amount x hx) (by decide)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
