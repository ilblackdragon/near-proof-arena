import WasmBase.PrepAir
import WasmBase.Bus

/-!
# WasmBase.PrepSound — what the PREP AIR proves about the code hash (A-T3)

**`prep_sha_sound`**: for any trace satisfying `Holds prepAir pub tr` (constraints on every row and
the mod-p LogUp balance; the SHA table's height a power of two in `[2, 2^22]`, as for every
committed trace of the backend), there is a byte string `m` — the message the SHA-256 table lays
out — such that the public values are `|m|` (public 32) and the 32 bytes of `ArenaCore.sha256 m`
(publics 0–31).

Proof: `PHDR`'s first row is active (its constraints) and receives `[0, 53, 1, len, h_0 … h_31]` on
bus 211; every count on bus 211 is a bit (`act`, `Dmult`), so the balance is exact and some send
carries that message; the only 36-field sender on bus 211 is a `SHA256` digest row with
`Dmult = 1`; the classical digest contract (`ZkFormal.Sha.sha_digest_contract_closed`, through
`Chips.Sha.eval_z`) says that row's message is `[Id, |m|] ++ sha256 m` for the message `m` of its
chain.

This discharges `TmplPrep.PrepCirc.sha` for the real AIR (`prep_hash_of_holds`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace WasmBase
namespace PrepSound

set_option linter.unusedSimpArgs false

open ZkFormal.Algebra Chips

/-- The classical constraints hold on any table that contains lane A's SHA constraints. -/
theorem sha_local_of_sub {A : Air} {pub : List F} {tr : Trace} {t : Nat} (ht : t < A.tables.length)
    (hC : ∀ e ∈ Sha.constraints, e ∈ (A.tables[t]'ht).constraints) (h : Holds A pub tr)
    (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t)) (hge : 1 ≤ Nat.log2 (tr.height t))
    (hle : Nat.log2 (tr.height t) ≤ 22) : ZkFormal.Sha.ShaLocal (Sha.toZTrace tr) t pub where
  log_ge := hge
  log_le := by simpa [ZkFormal.Sha.Table.maxLog, Sha.toZTrace] using hle
  constr := by
    intro r hr e he
    have hH : (Sha.toZTrace tr).height t = tr.height t := Sha.toZTrace_height tr t hpow
    have hmem : Sha.toW e ∈ Sha.constraints := by
      simp only [Sha.constraints]
      exact List.mem_append_left _ (List.mem_map_of_mem he)
    have hc := h.constr t ht r (by rwa [hH] at hr) (Sha.toW e) (hC _ hmem)
    rw [Sha.eval_z tr pub t r hpow]
    exact hc

theorem sha_sub : ∀ e ∈ Sha.constraints, e ∈ (prepAir.tables[1]'(by decide)).constraints := by
  intro e he
  show e ∈ Sha.constraints ++ [Prep.cDmult]
  exact List.mem_append_left _ he

/-- One constraint of table `t` at row `r`. -/
theorem constr_at {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {t : Nat}
    (ht : t < prepAir.tables.length) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ (prepAir.tables[t]'ht).constraints) : e.eval (tr.row pub t r) = 0 :=
  H.constr t ht r hr e he

/-- `PHDR`'s `act` is `1` on the first row and `0` elsewhere. -/
theorem act_val {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r : Nat}
    (hr : r < tr.height 0) : tr.cell 0 r Prep.act = if r = 0 then 1 else 0 := by
  have c1 := constr_at H (t := 0) (by decide) hr (e := .first * (v Prep.act - 1))
    (by simp [prepAir, Prep.phdrTable, Prep.phdrConstraints])
  have c2 := constr_at H (t := 0) (by decide) hr (e := (1 - .first) * v Prep.act)
    (by simp [prepAir, Prep.phdrTable, Prep.phdrConstraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Expr.eval, Trace.row, v]
    at c1 c2
  by_cases h0 : r = 0
  · subst h0
    simp only [beq_self_eq_true, ↓reduceIte] at c1 ⊢
    grind
  · have : (r == 0) = false := by simp [h0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, h0] at c1 c2 ⊢
    grind

/-- `Dmult` is a bit on every row of the SHA table. -/
theorem dmult_bit {pub : List F} {tr : Trace} (H : Holds prepAir pub tr) {r : Nat}
    (hr : r < tr.height 1) :
    tr.cell 1 r ZkFormal.Sha.Layout.colDmult = 0 ∨ tr.cell 1 r ZkFormal.Sha.Layout.colDmult = 1 := by
  have c := constr_at H (t := 1) (by decide) hr (e := Prep.cDmult)
    (by show Prep.cDmult ∈ Sha.constraints ++ [Prep.cDmult]; simp)
  simp only [Prep.cDmult, Chips.bool, Sha.dmultE, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_col, Trace.row, v] at c
  grind

theorem toNat_le_one {x : F} (h : x = 0 ∨ x = 1) : x.toNat ≤ 1 := by
  rcases h with rfl | rfl <;> decide

/-- A table none of whose interactions is on bus 211. -/
theorem bus_ne_of_all {T : Table} (h : (T.inters.map (·.bus)).all (· != busHashCall) = true)
    {i : Inter} (hi : i ∈ T.inters) : i.bus ≠ busHashCall := by
  have := List.all_eq_true.1 h i.bus (List.mem_map_of_mem hi)
  simpa using this

/-- **Every occurrence on bus 211**: `PHDR`'s summary send / digest receive (count `act`), or a SHA
row's digest send / summary receive (count `Dmult`). -/
theorem occ211 {pub : List F} {tr : Trace} {o : Occ} (ho : o ∈ occs prepAir tr pub)
    (hb : o.1 = busHashCall) :
    (∃ r, r < tr.height 0 ∧
      (o = (busHashCall, true, Prep.callMsg.map (·.eval (tr.row pub 0 r)), (tr.cell 0 r Prep.act).toNat) ∨
       o = (busHashCall, false, Prep.hashMsg.map (·.eval (tr.row pub 0 r)), (tr.cell 0 r Prep.act).toNat))) ∨
    (∃ r, r < tr.height 1 ∧
      (o = (busHashCall, true, Prep.digMsgP.map (·.eval (tr.row pub 1 r)),
            (tr.cell 1 r ZkFormal.Sha.Layout.colDmult).toNat) ∨
       o = (busHashCall, false, Sha.callMsg.map (·.eval (tr.row pub 1 r)),
            (tr.cell 1 r ZkFormal.Sha.Layout.colDmult).toNat))) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.1 ho
  simp only at hb
  match t, ht with
  | 0, _ =>
    simp only [prepAir, Prep.phdrTable, List.getElem_cons_zero, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl
    · exact .inl ⟨r, hr, .inl rfl⟩
    · exact .inl ⟨r, hr, .inr rfl⟩
  | 1, _ =>
    simp only [prepAir, Prep.shaTableD, List.getElem_cons_succ, List.getElem_cons_zero] at hi
    rcases List.mem_append.1 hi with hi | hi
    · simp only [Prep.shaTable, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact .inr ⟨r, hr, .inl rfl⟩
      · simp [busHashDigest, busHashCall] at hb
      · simp [busHashDigest, busHashCall] at hb
      · exact .inr ⟨r, hr, .inr rfl⟩
    · exact absurd hb (bus_ne_of_all (T := ⟨"", [], [], Prep.byteRecv⟩) (by decide) hi)
  | 2, _ => exact absurd hb (bus_ne_of_all (T := Prep.CB.table) (by decide) hi)
  | 3, _ => exact absurd hb (bus_ne_of_all (T := Prep.Hdr.table) (by decide) hi)
  | 4, _ => exact absurd hb (bus_ne_of_all (T := Prep.CodeP.table) (by decide) hi)
  | 5, _ => exact absurd hb (bus_ne_of_all (T := Prep.FuncP.table) (by decide) hi)
  | n + 6, h => exact absurd h (by simp [prepAir])

theorem sum_ne_zero_mem {l : List Nat} (h : l.sum ≠ 0) : ∃ x ∈ l, x ≠ 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a = 0
    · subst ha
      obtain ⟨x, hx, hx0⟩ := ih (by simpa using h)
      exact ⟨x, List.mem_cons_of_mem _ hx, hx0⟩
    · exact ⟨a, List.mem_cons_self, ha⟩

/-- **The PREP AIR binds the public code hash and length to a hashed message.** -/
theorem prep_sha_sound {pub : List F} {tr : Trace} (H : Holds prepAir pub tr)
    (hpow : tr.height 1 = 2 ^ Nat.log2 (tr.height 1)) (hge : 1 ≤ Nat.log2 (tr.height 1))
    (hle : Nat.log2 (tr.height 1) ≤ 22) :
    ∃ m : ArenaCore.Bytes, pub.getD Prep.pubLen 0 = Fp.ofNat m.length ∧
      (List.range 32).map (fun i => pub.getD i 0) = (ArenaCore.sha256 m).map (fun x => Fp.ofNat x.toNat) := by
  classical
  have h0 : 0 < tr.height 0 := by have := H.heightPos 0 (by decide); omega
  -- the PHDR receive at row 0
  let m0 := Prep.hashMsg.map (·.eval (tr.row pub 0 0))
  have hact0 : tr.cell 0 0 Prep.act = 1 := by simpa using act_val H h0
  have ho0 : ((busHashCall, false, m0, (tr.cell 0 0 Prep.act).toNat) : Occ) ∈ occs prepAir tr pub :=
    mem_occs.2 ⟨0, by decide, 0, h0, ⟨busHashCall, false, v Prep.act, Prep.hashMsg⟩,
      by simp [prepAir, Prep.phdrTable], rfl⟩
  -- every count on bus 211 is a bit
  have hbits : ∀ o ∈ occs prepAir tr pub, o.1 = busHashCall → o.2.2.2 ≤ 1 := by
    intro o ho hb
    rcases occ211 ho hb with ⟨r, hr, rfl | rfl⟩ | ⟨r, hr, rfl | rfl⟩
    · show (tr.cell 0 r Prep.act).toNat ≤ 1
      rw [act_val H hr]; split <;> decide
    · show (tr.cell 0 r Prep.act).toNat ≤ 1
      rw [act_val H hr]; split <;> decide
    · exact toNat_le_one (dmult_bit H hr)
    · exact toNat_le_one (dmult_bit H hr)
  have hge1 : 1 ≤ busNat prepAir tr pub busHashCall false m0 := by
    have := count_le_busNat ho0 rfl rfl rfl
    rw [hact0] at this; exact this
  have hlt := busNat_lt H busHashCall false m0 (fun o ho hb _ => hbits o ho hb)
  have hbal := H.balance busHashCall m0
  rw [Nat.mod_eq_of_lt hlt] at hbal
  have hsend : busNat prepAir tr pub busHashCall true m0 ≠ 0 := by
    intro h; rw [h, Nat.zero_mod] at hbal; omega
  -- a send carrying `m0`
  unfold busNat at hsend
  obtain ⟨c, hc, hc0⟩ := sum_ne_zero_mem hsend
  obtain ⟨o, hof, rfl⟩ := List.mem_map.1 hc
  obtain ⟨ho, hcond⟩ := List.mem_filter.1 hof
  simp only [decide_eq_true_eq] at hcond
  obtain ⟨hb, hs, hm⟩ := hcond
  rcases occ211 ho hb with ⟨r, hr, rfl | rfl⟩ | ⟨r, hr, rfl | rfl⟩
  · -- PHDR's summary: 8 fields, not 36
    exfalso
    have := congrArg List.length hm
    simp only [List.length_map, m0, phdr_msg_len.1, phdr_msg_len.2.2.1] at this
    omega
  · simp at hs
  · -- a SHA digest row
    have hd1 : tr.cell 1 r ZkFormal.Sha.Layout.colDmult = 1 := by
      rcases dmult_bit H hr with h | h
      · exact absurd (by simp only at hc0 ⊢; rw [h]; rfl) hc0
      · exact h
    have hL := sha_local_of_sub (by decide) sha_sub H hpow hge hle
    have hH : (Sha.toZTrace tr).height 1 = tr.height 1 := Sha.toZTrace_height tr 1 hpow
    obtain ⟨m, dg, -, hdg, hmsg, -⟩ :=
      ZkFormal.Sha.sha_digest_contract_closed hL 0 0 (by rw [hH]; exact hr) hd1
    refine ⟨m, ?_⟩
    simp only at hm
    -- the sent message, through `eval_z`
    have hsent : Prep.digMsgP.map (·.eval (tr.row pub 1 r)) =
        [Sha.tsE.eval (tr.row pub 1 r), Sha.hidE.eval (tr.row pub 1 r)] ++
          ((ZkFormal.Sha.Table.interactions 0 0)[16]!.msgVal (Sha.toZTrace tr) 1 r pub) := by
      simp only [Prep.digMsgP, List.map_append, List.map_map, ZkFormal.Air.Interaction.msgVal,
        Prep.classDigMsg]
      congr 1
    rw [hsent, hmsg, hdg] at hm
    simp only [m0, Prep.hashMsg, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.cons_append, List.nil_append, List.cons.injEq] at hm
    obtain ⟨-, -, -, hlen, hbytes⟩ := hm
    refine ⟨?_, ?_⟩
    · exact hlen.symm
    · exact ((List.map_congr_left (fun i _ => rfl)).trans hbytes.symm)
  · simp at hs

/-- The 32 hash bytes a leaf wrapper reads off PREP's public values. -/
def hashOf (pub : List F) : ArenaCore.Bytes :=
  (List.range 32).map fun i => ((pub.getD i 0).toNat).toUInt8

theorem toUInt8_of (x : UInt8) : ((Fp.ofNat x.toNat).toNat).toUInt8 = x := by
  have hx : x.toNat < P := by have := x.toNat_lt; unfold P; omega
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt hx]
  exact UInt8.ofNat_toNat

/-- **`TmplPrep.PrepCirc.sha` for the real AIR**: the hash the wrapper reads off PREP's public values
is `SHA-256` of the SHA table's message (and the public length is its length). -/
theorem prep_hash_of_holds {pub : List F} {tr : Trace} (H : Holds prepAir pub tr)
    (hpow : tr.height 1 = 2 ^ Nat.log2 (tr.height 1)) (hge : 1 ≤ Nat.log2 (tr.height 1))
    (hle : Nat.log2 (tr.height 1) ≤ 22) :
    ∃ m : ArenaCore.Bytes, ArenaCore.sha256 m = hashOf pub ∧ pub.getD Prep.pubLen 0 = Fp.ofNat m.length := by
  obtain ⟨m, hlen, hb⟩ := prep_sha_sound H hpow hge hle
  refine ⟨m, ?_, hlen⟩
  have := congrArg (List.map fun y : F => (y.toNat).toUInt8) hb
  simp only [List.map_map] at this
  unfold hashOf
  rw [show (fun i => ((pub.getD i 0).toNat).toUInt8) = ((fun y : F => y.toNat.toUInt8) ∘ fun i => pub.getD i 0)
    from rfl, this]
  have e : List.map ((fun y : F => (y.toNat).toUInt8) ∘ fun x : UInt8 => Fp.ofNat x.toNat)
      (ArenaCore.sha256 m) = List.map id (ArenaCore.sha256 m) :=
    List.map_congr_left (fun x _ => toUInt8_of x)
  rw [e, List.map_id]

#print axioms prep_hash_of_holds
#print axioms act_val
#print axioms dmult_bit
#print axioms occ211
#print axioms prep_sha_sound

end PrepSound
end WasmBase
