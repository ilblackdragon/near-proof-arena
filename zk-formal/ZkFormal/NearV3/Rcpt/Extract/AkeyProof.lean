import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Rcpt.Tables.Akey

/-!
# ZkFormal.NearV3.Rcpt.Extract.AkeyProof — the `akeyV3` view (`AkeyViewStmt`, `akey_view`)

One `AkeyE` per 9-row segment: the value record `vid`, the final use count `U` and the 9 value
bytes (the last one `1`, `FullAccess`).  Traffic: `VBYTES (vid, p, b_p)` for `p < 9`,
`AKC (vid, 0)` sent, `AKC (vid, U)` received.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure AkeyE where
  vid : Nat
  U : Nat
  bytes : List Nat
  deriving Repr, Inhabited

structure AkeyWf (es : List AkeyE) : Prop where
  len : ∀ e ∈ es, e.bytes.length = 9
  /-- `FullAccess`: the permission tag is `1` -/
  last : ∀ e ∈ es, e.bytes.getD 8 0 = 1
  canon : ∀ e ∈ es, e.vid < P ∧ e.U < P ∧ ∀ x ∈ e.bytes, x < P
  rows : 9 * es.length ≤ 2 ^ AkeyV3.maxLog

def akeySends (es : List AkeyE) (b : Nat) : List Msg :=
  if b = B_VBYTES then es.flatMap fun e => (List.range 9).map fun p => [e.vid, p, e.bytes.getD p 0]
  else if b = B_AKC then es.map fun e => [e.vid, 0]
  else []

def akeyRecvs (es : List AkeyE) (b : Nat) : List Msg :=
  if b = B_AKC then es.map fun e => [e.vid, e.U] else []

def akeyTraffic (es : List AkeyE) : Traffic := ⟨akeySends es, akeyRecvs es⟩

/-- **The `akeyV3` view statement.** -/
def AkeyViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal AkeyV3.table tr t pub →
    ∃ es, AkeyWf es ∧ TableTraffic AkeyV3.interactions tr t pub (akeyTraffic es)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.AkeyProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.AkeyV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem mem2 {e : Expr} (h : e ∈ ([ .mul (c af) (Dsl.not (c act)), .mul (c al) (Dsl.not (c act)),
    .mul .isFirst (sub (c act) (c af)),
    .mul .isLast (.mul (c act) (Dsl.not (c al))),
    .mul (c af) (c pos),
    .mul (c al) (sub (c pos) (k 8)),
    .mul (c al) (sub (c b) (k 1)),
    mul3 (c act) (Dsl.not (c al)) (Dsl.not (n act)),
    mul3 (c act) (Dsl.not (c al)) (n af),
    mul3 (c act) (Dsl.not (c al)) (sub (n vid) (c vid)),
    mul3 (c act) (Dsl.not (c al)) (sub (n pos) (.add (c pos) (k 1))),
    mul3 (c al) (n act) (Dsl.not (n af)),
    mul3 .isTransition (Dsl.not (c act)) (n act) ] : List Expr)) : e ∈ AkeyV3.constraints := by
  unfold AkeyV3.constraints; exact List.mem_append_right _ h

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

section
variable (hL : TableLocal AkeyV3.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ AkeyV3.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e he

theorem isBool {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ [act, af, al]) :
    tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold AkeyV3.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem zero_of_not_one {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ [act, af, al])
    (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem rowFacts {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r af = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r pos = 0) ∧
    (tr.cell tt r al = 1 → tr.cell tt r act = 1 ∧ tr.cell tt r pos = 8 ∧ tr.cell tt r b = 1) ∧
    (tr.cell tt r act = 0 → tr.cell tt r af = 0) := by
  have h1 := con hL hr (e := .mul (c af) (Dsl.not (c act))) (mem2 (by simp))
  have h2 := con hL hr (e := .mul (c al) (Dsl.not (c act))) (mem2 (by simp))
  have h3 := con hL hr (e := .mul (c af) (c pos)) (mem2 (by simp))
  have h4 := con hL hr (e := .mul (c al) (sub (c pos) (k 8))) (mem2 (by simp))
  have h5 := con hL hr (e := .mul (c al) (sub (c b) (k 1))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4 h5
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩
  · rw [h] at h2 h4 h5; exact ⟨by grind, by grind, by grind⟩
  · rw [h] at h1; grind

theorem within {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1) (hl : tr.cell tt r al = 0) :
    tr.cell tt (r + 1) act = 1 ∧ tr.cell tt (r + 1) af = 0 ∧ tr.cell tt (r + 1) vid = tr.cell tt r vid ∧
    tr.cell tt (r + 1) pos = tr.cell tt r pos + 1 := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (Dsl.not (n act))) (mem2 (by simp))
  have h2 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (n af)) (mem2 (by simp))
  have h3 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (sub (n vid) (c vid))) (mem2 (by simp))
  have h4 := con hL hr' (e := mul3 (c act) (Dsl.not (c al)) (sub (n pos) (.add (c pos) (k 1)))) (mem2 (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3 h4
  rw [ha, hl] at h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind⟩

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r al = 1)
    (ha : tr.cell tt (r + 1) act = 1) : tr.cell tt (r + 1) af = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c al) (n act) (Dsl.not (n af))) (mem2 (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1
  rw [ha, hl] at h1; grind

theorem pad {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act)) (mem2 (by simp))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height tt) : tr.cell tt 0 act = tr.cell tt 0 af := by
  have h1 := con hL h0 (e := .mul .isFirst (sub (c act) (c af))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_sub, eval_isFirst, if_pos rfl] at h1
  grind

theorem lastRow (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) al = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c al)))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem segFacts (h0act : tr.cell tt 0 act = 1) :
    SegFacts (tr.height tt) (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).1 h).1
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact ((rowFacts hL hr).2.1 h).1
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have := within hL hr ha (zero_of_not_one hL (by omega) (by simp) hl)
    simp [isOne, this.1, this.2.1]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact nextSeg hL hr hl ha
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp) ha)
    simp [isOne, this]
  start h0 := by simp only [isOne, decide_eq_true_eq]; rw [← row0 hL h0, h0act]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

theorem height_le : tr.height tt ≤ 2 ^ 16 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem segInfo {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt) :
    ℓ = 9 ∧
    (∀ j, j < 9 → tr.cell tt (s + j) act = 1 ∧ tr.cell tt (s + j) pos = ((j : Nat) : Fp) ∧
      tr.cell tt (s + j) vid = tr.cell tt s vid ∧ tr.cell tt (s + j) af = (if j = 0 then 1 else 0)) ∧
    tr.cell tt (s + 8) b = 1 := by
  have hP : tr.height tt < P := by have := height_le hL; unfold P; omega
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have haf : tr.cell tt s af = 1 := by simpa [isOne] using hfs
  have hal : tr.cell tt (s + ℓ - 1) al = 1 := by simpa [isOne] using hle
  have hA : ∀ j, j < ℓ → tr.cell tt (s + j) act = 1 := fun j hj => by
    have := hact (s + j) (by omega) (by omega); simpa [isOne] using this
  have hW : ∀ j, j + 1 < ℓ → tr.cell tt (s + j) al = 0 := fun j hj =>
    zero_of_not_one hL (by omega) (by simp) (hlast (s + j) (by omega) (by omega))
  have hw := fun j (hj : j + 1 < ℓ) => within hL (r := s + j) (by omega) (hA j (by omega)) (hW j hj)
  have hs := (rowFacts hL (by omega : s < _)).1 haf
  have he := (rowFacts hL (by omega : s + ℓ - 1 < _)).2.1 hal
  have hi := counter_of (f := fun q => tr.cell tt q pos) (s := s) (ℓ := ℓ) (v0 := 0)
    hs.2 (fun q h1 h2 => by
      have := (hw (q - s) (by omega)).2.2.2; rwa [show s + (q - s) = q by omega] at this)
  have h9 : ℓ = 9 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [he.2.1, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    have := ofNat_inj (a := 8) (b := ℓ - 1) (by unfold P; omega) (by omega) e
    omega
  subst h9
  have hk := const_of (f := fun q => tr.cell tt q vid) (s := s) (ℓ := 9) (fun q h1 h2 => by
    have := (hw (q - s) (by omega)).2.2.1; rwa [show s + (q - s) = q by omega] at this)
  refine ⟨rfl, fun j hj => ⟨hA j hj, ?_, hk (s + j) (by omega) (by omega), ?_⟩, ?_⟩
  · have := hi (s + j) (by omega) (by omega); rwa [show 0 + (s + j - s) = j by omega] at this
  · by_cases h0 : j = 0
    · subst h0; simpa using haf
    · rw [if_neg h0]
      exact zero_of_not_one hL (by omega) (by simp) (hfirst (s + j) (by omega) (by omega))
  · have := he.2.2; rwa [show s + 9 - 1 = s + 8 by omega] at this

end

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic AkeyV3.interactions tr tt q pub bb sd =
      (if bb = B_VBYTES ∧ sd = true ∧ tr.cell tt q act = 1 then
        [[tr.cell tt q vid, tr.cell tt q pos, tr.cell tt q b]] else []) ++
      (if bb = B_AKC ∧ sd = true ∧ tr.cell tt q af = 1 then [[tr.cell tt q vid, 0]] else []) ++
      (if bb = B_AKC ∧ sd = false ∧ tr.cell tt q af = 1 then [[tr.cell tt q vid, tr.cell tt q uu]] else []) := by
  simp only [rowTraffic, AkeyV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons,
    List.map_nil, eval_c, eval_k, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ ?_) <;> (split <;> split <;> simp_all [eq_comm]) <;> first | rfl | grind

def akeyOf (tr : Trace Fp) (tt s : Nat) : AkeyE :=
  ⟨(tr.cell tt s vid).toNat, (tr.cell tt s uu).toNat, (List.range 9).map fun j => (tr.cell tt (s + j) b).toNat⟩

theorem akeySends_flat (es : List AkeyE) (bb : Nat) : akeySends es bb = es.flatMap fun e => akeySends [e] bb := by
  unfold akeySends; repeat' split
  all_goals simp [map_eq_flatMap]

theorem akeyRecvs_flat (es : List AkeyE) (bb : Nat) : akeyRecvs es bb = es.flatMap fun e => akeyRecvs [e] bb := by
  unfold akeyRecvs; split <;> simp [map_eq_flatMap]

theorem segTraffic (hL : TableLocal AkeyV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt af) (isOne tr tt al) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (bb : Nat) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic AkeyV3.interactions tr tt q pub bb sd) =
      ((if sd then akeySends [akeyOf tr tt s] bb else akeyRecvs [akeyOf tr tt s] bb)).map Msg.toFp := by
  obtain ⟨h9, hrow, -⟩ := segInfo hL hseg hH
  subst h9
  have hrowT : ∀ j, j < 9 → rowTraffic AkeyV3.interactions tr tt (s + j) pub bb sd =
      (if bb = B_VBYTES ∧ sd = true then [[tr.cell tt s vid, ((j : Nat) : Fp), tr.cell tt (s + j) b]] else []) ++
      (if bb = B_AKC ∧ sd = true ∧ j = 0 then [[tr.cell tt s vid, 0]] else []) ++
      (if bb = B_AKC ∧ sd = false ∧ j = 0 then [[tr.cell tt s vid, tr.cell tt s uu]] else []) := by
    intro j hj
    obtain ⟨ha, hpos, hk, hf⟩ := hrow j hj
    rw [rowT, ha, hpos, hk, hf]
    by_cases h0 : j = 0
    · subst h0; simp
    · simp [h0]
  rw [List.range'_eq_map_range, List.flatMap_map, flatMap_congr' (fun j hj => hrowT j (List.mem_range.1 hj))]
  have ofN : ∀ x : Fp, Fp.ofNat x.toNat = x := Fp.ofNat_toNat
  by_cases hV : bb = B_VBYTES
  · subst hV
    cases sd
    · simp [akeyRecvs, B_VBYTES, B_AKC, flatMap_nil_fun]
    · simp only [akeySends, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        show B_VBYTES ≠ B_AKC by decide, false_and, if_false, true_and, and_self]
      rw [map_eq_flatMap, List.flatMap_map]
      apply flatMap_congr'; intro j hj
      have hj' := List.mem_range.1 hj
      simp [akeyOf, Msg.toFp, ofN, List.getElem?_range hj', natCast_eq]
  · by_cases hK : bb = B_AKC
    · subst hK
      rw [show List.range 9 = [0] ++ List.range' 1 8 from rfl, List.flatMap_append,
        flatMap_range'_nil _ 1 8 (fun j _ => by simp [show 1 + j ≠ 0 by omega, B_AKC, B_VBYTES])]
      cases sd <;> simp [akeySends, akeyRecvs, akeyOf, Msg.toFp, ofN, B_AKC, B_VBYTES] <;> rfl
    · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hV, hK]), flatMap_nil_fun]
      cases sd <;> simp [akeySends, akeyRecvs, hV, hK]

end ZkFormal.NearV3.AkeyProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near AkeyProof

/-- **The `akeyV3` view.** -/
theorem akey_view : AkeyViewStmt := by
  intro tr pub tt hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs, hc, hend, hall, hpad⟩ : ∃ segs : List (Nat × Nat), Consec 0 segs ∧
      segEnd 0 segs ≤ tr.height tt ∧
      (∀ p ∈ segs, IsSeg (isOne tr tt AkeyV3.act) (isOne tr tt AkeyV3.af) (isOne tr tt AkeyV3.al) p.1 p.2) ∧
      (∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt AkeyV3.act r = false) := by
    by_cases h0 : tr.cell tt 0 AkeyV3.act = 1
    · exact segments_of (segFacts hL h0) hpos
    · refine ⟨[], trivial, by simp [segEnd], by simp, fun r _ hr => ?_⟩
      have : ∀ r, r < tr.height tt → tr.cell tt r AkeyV3.act = 0 := by
        intro r
        induction r with
        | zero => intro _; exact zero_of_not_one hL hpos (by simp) (by simp [isOne, h0])
        | succ r ih => intro hr; exact pad hL hr (ih (by omega))
      simp [isOne, this r hr]
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ bb sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic AkeyV3.interactions tr tt q pub bb sd = [] := by
    intro bb sd q h1 h2
    have ha := zero_of_not_one hL h2 (by simp) (hpad q h1 h2)
    have hf := (rowFacts hL h2).2.2 ha
    rw [rowT, ha, hf]; simp
  have h9 : ∀ p ∈ segs, p.2 = 9 := fun p hp => (segInfo hL (hall p hp) (hH p hp)).1
  refine ⟨segs.map fun p => akeyOf tr tt p.1, ⟨?_, ?_, ?_, ?_⟩, fun bb m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
    simp [akeyOf]
  · intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    have := (segInfo hL (hall p hp) (hH p hp)).2.2
    simp [akeyOf, this, List.getD_eq_getElem?_getD]; rfl
  · intro e he
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, fun x hx => ?_⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact Fp.toNat_lt _
  · rw [List.length_map]
    have hsum : (segs.map fun p => p.2).sum = segEnd 0 segs := by
      have := congrArg List.length (range'_segs segs 0 hc)
      simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
      rw [this]
    have : (segs.map fun p => p.2) = segs.map fun _ => 9 := List.map_congr_left h9
    rw [this] at hsum
    have e : ∀ l : List (Nat × Nat), (l.map fun _ => 9).sum = 9 * l.length := by
      intro l; induction l with
      | nil => rfl
      | cons _ l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
    rw [e] at hsum
    have := height_le hL
    simp only [AkeyV3.maxLog]; omega
  · simp only [akeyTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb true), akeySends_flat, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => segTraffic hL (hall p hp) (hH p hp) bb true)]
    rfl
  · simp only [akeyTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb false), akeyRecvs_flat, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => segTraffic hL (hall p hp) (hH p hp) bb false)]
    rfl

end ZkFormal.NearV3
