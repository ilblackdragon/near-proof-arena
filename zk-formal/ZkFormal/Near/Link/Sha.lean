import ZkFormal.Near.Link.MrkFacts
import ZkFormal.Near.Link.ShaCore
import ZkFormal.Near.Link.Claim

/-!
# ZkFormal.Near.Link.Sha — `sha_ok : ShaStmt`

Every `BYTES` send is `(id, j, encOf id [j])` (`bytes_classified`); `encOf id` is
canonical and short (`encOf_ok`); digest windows are canonical
(`digest_canon`).  `sha_core` then gives the statement.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-- `m` is position `j` of the intended message of some id. -/
def Emits (E : Nat → List Nat) (m : Msg) : Prop :=
  ∃ id j, id < P ∧ j < (E id).length ∧ m = [id, j, (E id).getD j 0]

theorem mem_emitAt {id off : Nat} {bs : List Nat} {m : Msg} :
    m ∈ emitAt id off bs ↔ ∃ i, i < bs.length ∧ m = [id, off + i, bs.getD i 0] := by
  simp only [emitAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem emitAt_sub {E : Nat → List Nat} {id off : Nat} {bs : List Nat} (hid : id < P)
    (hpos : ∀ i, i < bs.length → off + i < (E id).length ∧ (E id).getD (off + i) 0 = bs.getD i 0) :
    ∀ m ∈ emitAt id off bs, Emits E m := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := mem_emitAt.mp hm
  obtain ⟨h1, h2⟩ := hpos i hi
  exact ⟨id, off + i, hid, h1, by rw [h2]⟩

theorem emitAt_sub_self {E : Nat → List Nat} {id : Nat} {bs : List Nat} (hid : id < P)
    (he : E id = bs) : ∀ m ∈ emitAt id 0 bs, Emits E m :=
  emitAt_sub hid (fun i hi => by rw [he, Nat.zero_add]; exact ⟨hi, rfl⟩)

theorem mem_rr {α : Type} {l : List α} {x : α} {r : Nat} (h : (x, r) ∈ l.zip (List.range l.length)) :
    ∃ hr : r < l.length, l[r] = x := mem_zip_range.mp h

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem rs_length_le : rs.length ≤ 256 := (h.rcpt.count (fun _ _ => pubNat_lt c _)).2.2

theorem rs_wf : ∀ x ∈ rs, ∃ r a b c, x.Wf r a b c := by
  obtain ⟨toks, -, -, hw, -⟩ := rcptWf_at h.rcpt
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨_, _, _, _, hw r hr⟩

theorem rs_canon {x : RcptV} (hx : x ∈ rs) {l : List Nat} (hl : RawOrByte x l) : ∀ y ∈ l, y < P := by
  intro y hy
  rcases hl y hy with h1 | h1
  · exact h.rcpt.canon x hx y h1
  · unfold P; omega

omit h in
theorem flatMap_length_le {α : Type} (f : α → List Nat) (B : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length ≤ B) → (l.flatMap f).length ≤ l.length * B
  | [], _ => by simp
  | a :: l, hl => by
    have := flatMap_length_le f B l (fun x hx => hl x (by simp [hx]))
    have := hl a (by simp)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]; omega

/-! ## The intended messages are canonical and short -/

theorem encOf_ok (id : Nat) :
    (∀ x ∈ encOf (publicOf c) vs rs as mv id, x < P) ∧
      (encOf (publicOf c) vs rs as mv id).length < P := by
  have hrl := rs_length_le h
  have hpub := pubNat_lt c
  have hvsl := vs_length_le h.node
  have hPv : (3000000 : Nat) < P := by unfold P; omega
  have hpb : ∀ off len, ∀ y ∈ pubBytes (publicOf c) off len, y < P := by
    intro off len y hy; simp only [pubBytes, List.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy; have := hpub (off + j); unfold P; omega
  unfold encOf
  dsimp only
  by_cases hk1 : id % 16 = K_RC
  · rw [if_pos hk1]
    split
    · -- RC
      refine ⟨?_, ?_⟩
      · intro y hy; simp only [rcMsg, List.mem_append, List.mem_flatMap] at hy
        rcases hy with (hy | hy) | ⟨x, hx, hy⟩
        · exact hpb _ _ y hy
        · exact hpb _ _ y hy
        · obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
          exact rs_canon h hx (enc_vals w) y hy
      · have := flatMap_length_le RcptV.enc 400 rs (fun x hx => by
          obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx; exact enc_length w)
        simp only [rcMsg, List.length_append, pubBytes_length]
        have : rs.length * 400 ≤ 256 * 400 := Nat.mul_le_mul_right _ hrl
        unfold P; omega
    · simp; unfold P; omega
  rw [if_neg hk1]
  by_cases hk2 : id % 16 = K_RF
  · rw [if_pos hk2]
    split
    · -- RF
      refine ⟨?_, ?_⟩
      · intro y hy; simp only [rfMsg, List.mem_append, List.mem_flatMap, List.mem_filter] at hy
        rcases hy with hy | ⟨x, ⟨hx, -⟩, hy⟩
        · exact hpb _ _ y hy
        · obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
          exact rs_canon h hx (encRefund_vals w) y hy
      · have := flatMap_length_le RcptV.encRefund 400 (rs.filter (·.hr)) (fun x hx => by
          obtain ⟨r, a, b, c', w⟩ := rs_wf h x (List.mem_filter.mp hx).1; exact encRefund_length w)
        have h2 := List.length_filter_le (fun x : RcptV => x.hr) rs
        simp only [rfMsg, List.length_append, pubBytes_length]
        have : (rs.filter (·.hr)).length * 400 ≤ 256 * 400 := Nat.mul_le_mul_right _ (by omega)
        unfold P; omega
    · simp; unfold P; omega
  rw [if_neg hk2]
  -- per-receipt messages
  have hrsx : ∀ (f : RcptV → List Nat) (i : Nat),
      (∀ x ∈ rs, (∀ y ∈ f x, y < P) ∧ (f x).length < P) →
      (∀ x ∈ (rs[i]?.map f).getD [], x < P) ∧ ((rs[i]?.map f).getD []).length < P := by
    intro f i hf
    cases hi : rs[i]? with
    | none => simp; unfold P; omega
    | some x =>
      have hx : x ∈ rs := List.mem_of_getElem? hi
      simpa using hf x hx
  split
  · exact hrsx _ _ (fun x hx => by
      obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
      exact ⟨rs_canon h hx (peo_vals w), by have := peo_length w; unfold P; omega⟩)
  split
  · exact hrsx _ _ (fun x hx => by
      obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
      exact ⟨rs_canon h hx (leaf_vals), by rw [leaf_length w]; unfold P; omega⟩)
  split
  · exact hrsx _ _ (fun x hx => by
      obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
      exact ⟨rs_canon h hx (ridMsg_vals hpub), by rw [ridMsg_length w]; unfold P; omega⟩)
  split
  · -- MRK
    cases hi : (mrkMsgs mv)[id / 16]? with
    | none => simp; unfold P; omega
    | some l =>
      have hl := List.mem_of_getElem? hi
      rw [mrkMsgs_eq] at hl
      obtain ⟨nd, hnd, he⟩ := List.mem_filterMap.mp hl
      have hw := h.mrk.windows nd hnd
      have hc := h.mrk.canon.2.2.2 nd hnd
      cases nd with
      | promoted => simp [hashedMsg] at he
      | hashed lI lL l1 rI rL r1 =>
        simp only [hashedMsg, Option.some.injEq] at he; subst he
        simp only [Option.getD_some]
        refine ⟨fun y hy => hc y ?_, ?_⟩
        · simp only [MrkNode.raw]
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ (List.mem_append_right _ hy)
          · exact List.mem_append_right _ hy
        simp only [List.length_append, hw.1, hw.2]; unfold P; omega
  -- node messages
  have hvsx : ∀ (post : Bool) (i : Nat),
      (∀ x ∈ (vs[i]?.map fun s => s.v.ser post).getD [], x < P) ∧
        ((vs[i]?.map fun s => s.v.ser post).getD []).length < P := by
    intro post i
    cases hi : vs[i]? with
    | none => simp; unfold P; omega
    | some s =>
      have hs : s ∈ vs := List.mem_of_getElem? hi
      have hw := h.node.wf s hs
      have hle : (s.v.ser false).length ≤ 3000000 :=
        Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _)
          (le_sum_of_mem (fun s : NodeS => (s.v.ser false).length + if s.v.touched then 72 else 0) hs))
          h.node.size
      simp only [Option.map_some, Option.getD_some]
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases ser_vals s.v hw post x hx with h1 | h1 | h1
        · exact h.node.canon s hs x h1
        · unfold P; omega
        · omega
      · cases post
        · omega
        · rw [ser_length_post s.v hw]; omega
  split
  · exact hvsx false _
  split
  · exact hvsx true _
  -- acct messages
  have hasx : ∀ (f : AcctV → List Nat) (i : Nat), (∀ a ∈ as, (∀ y ∈ f a, y < P) ∧ (f a).length < P) →
      (∀ x ∈ ((acctOf as i).map f).getD [], x < P) ∧ (((acctOf as i).map f).getD []).length < P := by
    intro f i hf
    cases hi : acctOf as i with
    | none => simp; unfold P; omega
    | some a =>
      have ha : a ∈ as := List.mem_of_find?_eq_some hi
      simpa using hf a ha
  split
  · exact hasx _ _ (fun a ha => by
      have hl := h.acct.len a ha
      refine ⟨fun y hy => h.acct.canon a ha y (by simp [hy]), ?_⟩
      rw [hl.1]; unfold P; omega)
  split
  · exact hasx _ _ (fun a ha => by
      have hl := h.acct.len a ha
      refine ⟨fun y hy => ?_, ?_⟩
      · rcases List.mem_append.mp hy with hy | hy
        · exact h.acct.canon a ha y (by simp [hy])
        · exact h.acct.canon a ha y (by simp [List.mem_of_mem_drop hy])
      · simp only [List.length_append, List.length_drop, hl.1, hl.2.1]; unfold P; omega)
  · simp; unfold P; omega

/-! ## Every `BYTES` send is a position of an intended message -/

theorem mrk_nodes_length : mv.nodes.length ≤ 257 * 256 := by
  have hb : ∀ x, x < 4 → pubNat (publicOf c) (PV_N + x) < 256 := fun _ _ => pubNat_lt c _
  obtain ⟨hl, h1, h2⟩ := h.rcpt.count hb
  have hn : nPubNat (publicOf c) = rs.length := by rw [nPubNat_eq _ hb, hl]; rfl
  have hv : mv.n = nPubNat (publicOf c) := h.mrk.nfix hb (by rw [hn]; unfold P; omega)
  obtain ⟨hlen, -⟩ := h.mrk.shape
  rw [hlen, hv, hn]; exact mrkShape_length _ h2

theorem bytes_classified :
    ∀ m ∈ nearSends (publicOf c) vs ws rs as mv ids B_BYTES,
      Emits (encOf (publicOf c) vs rs as mv) m := by
  have hrl := rs_length_le h
  have hvl := vs_length_lt h.node
  have hP : (16 * 256 + 16 : Nat) < P := by unfold P; omega
  obtain ⟨hnd, hslot, -⟩ := vslot h
  intro m hm
  rw [nearSends_bytes] at hm
  simp only [List.mem_append] at hm
  rcases hm with ((hm | hm) | hm) | hm
  · -- node
    unfold nodeSends at hm; dsimp only at hm; rw [if_pos rfl] at hm
    obtain ⟨⟨s, n⟩, hp, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
    dsimp only at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact emitAt_sub_self (by unfold msgId K_NPRE; omega)
        (by rw [encOf_npre, List.getElem?_eq_getElem hn]; rfl) m hm
    · exact emitAt_sub_self (by unfold msgId K_NPOST; omega)
        (by rw [encOf_npost, List.getElem?_eq_getElem hn]; rfl) m hm
  · -- rcpt
    unfold rcptSends at hm; dsimp only at hm; rw [if_pos rfl] at hm
    have hhdr : (pubBytes (publicOf c) PV_SHARD 8 ++ pubBytes (publicOf c) PV_N 4).length = 12 := by
      simp [pubBytes_length]
    have hnref : (pubBytes (publicOf c) PV_NREF 4).length = 4 := pubBytes_length _ _ _
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · refine emitAt_sub (by unfold K_RC P; omega) (fun i hi => ?_) m hm
      rw [encOf_rc, rcMsg, Nat.zero_add]
      exact ⟨by simp only [List.length_append] at hi ⊢; omega, getD_append_left' hi⟩
    · refine emitAt_sub (by unfold K_RF P; omega) (fun i hi => ?_) m hm
      rw [encOf_rf, rfMsg_eq, Nat.zero_add]
      exact ⟨by simp only [List.length_append] at hi ⊢; omega, getD_append_left' hi⟩
    · obtain ⟨⟨x, r⟩, hp, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨hr, rfl⟩ := mem_zip_range.mp hp
      dsimp only at hm
      have hid : ∀ k, k < 16 → msgId k r < P := fun k hk => by unfold msgId; omega
      simp only [List.mem_append] at hm
      rcases hm with ((((hm | hm) | hm) | hm) | hm)
      · refine emitAt_sub (by unfold K_RC P; omega) (fun i hi => ?_) m hm
        obtain ⟨h1, h2⟩ := getD_flatMap_at RcptV.enc rs r hr i hi
        rw [encOf_rc, rcMsg, rcOffs_eq rs r (by omega), ← hhdr, Nat.add_assoc,
          getD_append_right', h2]
        exact ⟨by simp only [List.length_append] at h1 ⊢; omega, rfl⟩
      · split at hm
        · next hhr =>
          refine emitAt_sub (by unfold K_RF P; omega) (fun i hi => ?_) m hm
          have hi' : i < (rfPart rs[r]).length := by simp only [rfPart, hhr]; exact hi
          obtain ⟨h1, h2⟩ := getD_flatMap_at rfPart rs r hr i hi'
          have e := getD_append_right' (pubBytes (publicOf c) PV_NREF 4) (rs.flatMap rfPart)
            (((rs.take r).flatMap rfPart).length + i)
          rw [hnref] at e
          rw [encOf_rf, rfMsg_eq, rfOffs_eq rs r (by omega), Nat.add_assoc, e, h2]
          exact ⟨by simp only [List.length_append] at h1 ⊢; omega, by simp only [rfPart, hhr]; rfl⟩
        · cases hm
      · exact emitAt_sub_self (hid _ (by decide))
          (by rw [encOf_peo, List.getElem?_eq_getElem hr]; rfl) m hm
      · exact emitAt_sub_self (hid _ (by decide))
          (by rw [encOf_leaf, List.getElem?_eq_getElem hr]; rfl) m hm
      · split at hm
        · exact emitAt_sub_self (hid _ (by decide))
            (by rw [encOf_rid, List.getElem?_eq_getElem hr]; rfl) m hm
        · cases hm
  · -- acct
    simp only [acctSends, if_pos] at hm
    obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hk, -⟩ := hslot a ha
    rcases List.mem_append.mp hm with hm | hm
    · exact emitAt_sub_self (by unfold msgId K_VPRE; omega)
        (by rw [encOf_vpre, acctOf_eq hnd ha]; rfl) m hm
    · exact emitAt_sub_self (by unfold msgId K_VPOST; omega)
        (by rw [encOf_vpost, acctOf_eq hnd ha]; rfl) m hm
  · -- mrk
    have hml := mrk_nodes_length h
    unfold mrkSends at hm; dsimp only at hm; rw [if_pos rfl] at hm
    obtain ⟨⟨nd, q⟩, hp, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp
    dsimp only at hm
    have hb := hashedBefore_le mv.nodes q
    split at hm
    · next lI lL l rI rL r he =>
      exact emitAt_sub_self (by unfold msgId K_MRK P; omega)
        (by rw [encOf_mrk, mrkMsgs_at mv q hq he]; rfl) m hm
    · cases hm

/-! ## Digest windows are canonical -/

omit h in
theorem revealed_raw {v : NodeV} {c l r : Nat} {pre po : List Nat}
    (hm : (c, l, r, pre, po) ∈ v.revealed) : ∀ x ∈ pre ++ po, x ∈ v.raw := by
  intro x hx
  cases v with
  | leaf => simp [NodeV.revealed] at hm
  | ext k kid memB =>
    cases kid with
    | node c' l' r' pre' po' =>
      simp only [NodeV.revealed, List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨-, -, -, rfl, rfl⟩ := hm
      simp only [NodeV.raw, NKid.raw, List.mem_append] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]
    | _ => simp [NodeV.revealed] at hm
  | branch sv kids memB =>
    simp only [NodeV.revealed, List.mem_filterMap] at hm
    obtain ⟨kd, hkd, he⟩ := hm
    cases kd with
    | node c' l' r' pre' po' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, -, -, rfl, rfl⟩ := he
      simp only [NodeV.raw, List.mem_append, List.mem_flatMap]
      left; right; refine ⟨_, hkd, ?_⟩
      simp only [NKid.raw, List.mem_append] at hx ⊢; rcases hx with hx | hx <;> simp [hx]
    | _ => simp at he

theorem digest_canon : ∀ m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST, ∀ x ∈ m.drop 2, x < P := by
  have hpub : ∀ j, pubNat (publicOf c) j < P := fun j => by have := pubNat_lt c j; unfold P; omega
  have hpb : ∀ off len, ∀ y ∈ pubBytes (publicOf c) off len, y < P := by
    intro off len y hy; simp only [pubBytes, List.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy; exact hpub _
  have hd : ∀ a b w, (digMsg a b w).drop 2 = w := fun _ _ _ => rfl
  intro m hm x hx
  rw [nearRecvs_digest] at hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · unfold nodeRecvs at hm; dsimp only at hm; rw [if_pos rfl] at hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> (rw [hd] at hx; exact hpb _ _ x hx)
    · obtain ⟨⟨s, n⟩, hp, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
      have hs : vs[n] ∈ vs := List.getElem_mem hn
      have hcan := h.node.canon _ hs
      dsimp only at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨⟨c', l, r, pre, po⟩, hrv, hm⟩ := List.mem_flatMap.mp hm
        have := revealed_raw hrv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> rw [hd] at hx
        · exact hcan x (this x (List.mem_append_left _ hx))
        · exact hcan x (this x (List.mem_append_right _ hx))
      · split at hm <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;>
          (rcases hm with rfl | rfl <;> rw [hd] at hx <;> apply hcan x <;>
            simp_all [NodeV.raw, NSlot.raw])
  · unfold rcptRecvs at hm; dsimp only at hm; rw [if_pos rfl] at hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> (rw [hd] at hx; exact hpb _ _ x hx)
    · obtain ⟨⟨y, r⟩, hp, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨hr, rfl⟩ := mem_zip_range.mp hp
      have hcan := h.rcpt.canon _ (List.getElem_mem hr)
      dsimp only at hm
      rcases List.mem_append.mp hm with hm | hm
      · split at hm
        · simp only [List.mem_singleton] at hm; subst hm; rw [hd] at hx
          exact hcan x (by simp [RcptV.raw, hx])
        · cases hm
      · simp only [List.mem_singleton] at hm; subst hm; rw [hd] at hx
        exact hcan x (by simp [RcptV.raw, hx])
  · unfold mrkRecvs at hm; dsimp only at hm; rw [if_pos rfl] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [hd] at hx; simp only [List.mem_map] at hx; obtain ⟨j, -, rfl⟩ := hx; exact hpub _
    · obtain ⟨⟨nd, q⟩, hp, hm⟩ := List.mem_flatMap.mp hm
      have hnd := (List.of_mem_zip hp).1
      have hcan := h.mrk.canon.2.2.2 nd hnd
      dsimp only at hm
      split at hm
      · next lI lL l rI rL r' =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> rw [hd] at hx <;> apply hcan x <;> simp [MrkNode.raw, hx]
      · cases hm

/-! ## The statement -/

end Hyp

theorem sha_ok : ShaStmt := by
  intro c vs ws rs as mv ids shaS shaR h id len d hid hlen hmem
  subst hlen
  have hS := bytes_classified h
  have hbytes : ∀ m, shaR B_BYTES m = cnt (nearSends (publicOf c) vs ws rs as mv ids B_BYTES) m := by
    intro m
    have := h.bal B_BYTES m
    rw [h.sha.sends_only_digest B_BYTES m (by decide), nearRecvs_bytes] at this
    simp only [cnt, List.map_nil, List.count_nil] at this ⊢
    omega
  have hrecv : 0 < shaS B_DIGEST (digMsg id (encOf (publicOf c) vs rs as mv id).length d).toFp := by
    have := h.bal B_DIGEST (digMsg id (encOf (publicOf c) vs rs as mv id).length d).toFp
    rw [h.sha.recvs_only_bytes B_DIGEST _ (by decide), nearSends_digest] at this
    have hp := cnt_pos_of_mem hmem
    simp only [cnt, List.map_nil, List.count_nil] at this hp
    omega
  obtain ⟨hc, hl⟩ := encOf_ok h id
  refine sha_core h.sha _ hbytes hid hc hl (digest_canon h _ hmem) ?_ hrecv
  intro m hm a ha hae
  obtain ⟨id', j, hid', hj, rfl⟩ := hS m hm
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  have := ofNat_inj hid' hid hae
  subst this
  exact ⟨j, hj, rfl⟩


end Link

end ZkFormal.Near
