import ZkFormal.Near.Link.Bus

/-!
# ZkFormal.Near.Link.ShaCore — message reconstruction for one message id

If every `BYTES` send whose id has the image of `id` is `(id, j, enc[j])` with
`j < |enc|`, then a provided digest `(id, |enc|, d)` is `sha256` of `enc`, and
`enc` consists of bytes.  (The SHA table range-checks the bytes it receives;
the consumer's length pins the message length.)
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem getD_eq_getElem {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem sha_core {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (S : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt S m)
    {id : Nat} {enc d : List Nat} (hid : id < P) (henc : ∀ x ∈ enc, x < P) (hlen : enc.length < P)
    (hd : ∀ x ∈ d, x < P)
    (hS : ∀ m ∈ S, ∀ a, m.head? = some a → Fp.ofNat a = Fp.ofNat id →
      ∃ j, j < enc.length ∧ m = [id, j, enc.getD j 0])
    (hrecv : 0 < shaS B_DIGEST (digMsg id enc.length d).toFp) :
    Bytes8 enc ∧ d = (sha256 (toBytes enc)).map UInt8.toNat := by
  obtain ⟨id', bs, hm, hall⟩ := hsha.digest _ hrecv
  simp only [digMsg, Msg.toFp, List.map_append, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq] at hm
  obtain ⟨hid', hlen', hdd⟩ := hm
  -- every received byte comes from a send `(id, j, enc[j])`
  have key : ∀ i, i < bs.length → ∃ j, j < enc.length ∧ Fp.ofNat j = Fp.ofNat i ∧
      Fp.ofNat (enc.getD j 0) = Fp.ofNat (bs.getD i 0).toNat := by
    intro i hi
    have h1 := hall i hi
    rw [hbytes] at h1
    obtain ⟨m, hmS, hmE⟩ := cnt_pos.mp h1
    cases m with
    | nil => simp [Msg.toFp] at hmE
    | cons a rest =>
      simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hmE
      obtain ⟨j, hj, hmj⟩ := hS _ hmS a rfl (by rw [hmE.1, hid'])
      simp only [List.cons.injEq] at hmj
      obtain ⟨-, rfl⟩ := hmj
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmE
      exact ⟨j, hj, hmE.2.1, hmE.2.2.1⟩
  -- lengths agree
  have hle : bs.length ≤ enc.length := by
    apply Classical.byContradiction; intro hlt
    obtain ⟨j, hj, hji, -⟩ := key enc.length (by omega)
    have := ofNat_inj (by omega) hlen hji; omega
  have hbl : bs.length = enc.length := by
    have := (ofNat_eq_iff.mp hlen'); rw [Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt (by omega)] at this
    exact this.symm
  -- bytes agree
  have hbyte : ∀ i (hi : i < enc.length), enc[i] = (bs[i]'(by omega)).toNat := by
    intro i hi
    obtain ⟨j, hj, hji, hv⟩ := key i (by omega)
    have := ofNat_inj (by omega) (by omega) hji; subst this
    rw [getD_eq_getElem _ _ hi, getD_eq_getElem _ _ (by omega)] at hv
    exact ofNat_inj (henc _ (List.getElem_mem hi))
      (Nat.lt_trans (UInt8.toNat_lt _) (by decide)) hv
  have henc' : enc = bs.map UInt8.toNat :=
    List.ext_getElem (by simp [hbl]) (fun i h1 h2 => by rw [hbyte i h1]; simp)
  have hb : toBytes enc = bs := by
    rw [henc']; unfold toBytes; rw [List.map_map]
    have : (UInt8.ofNat ∘ UInt8.toNat) = fun x => x := by funext x; exact UInt8.ofNat_toNat
    rw [this, List.map_id']
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [henc'] at hy; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy; exact UInt8.toNat_lt _
  · rw [hb]
    apply toFp_inj hd
    · intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.lt_trans (UInt8.toNat_lt _) (by decide)
    · simp only [Msg.toFp, List.map_map]; exact hdd

end Link

end ZkFormal.Near
