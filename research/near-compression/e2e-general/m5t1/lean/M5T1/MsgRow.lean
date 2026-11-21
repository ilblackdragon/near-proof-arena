import M5T1.MsgRowSch

/-!
# M5T1.MsgRow — the rows of one `MSG` message are a `Walk` (rows → walk; F-2)

The first half of the `MSG` soundness argument (`Walk.lean`; the second half, walk → encoder, is
`MsgSpec.lean`). On **any** trace satisfying `Holds (fullAir tape xtape)` whose `SCHT` columns are
the preprocessed schema (`SchtFixed`) and whose public tapes send nothing on `SCH` and `RNG`:

* `sch_row` (`MsgRowSch.lean`): every row's descriptor columns are a schema entry `g`, and
  `g = segAt mt s` for the row's `mt`, `s`;
* **`msg_walk`**: a message span `r0..r1` (`IsSpan`: `first` at `r0`, `endm` at `r1` and at no row
  of `r0..r1-1`) has a walk: `∃ vs, IsMsg mt mf (bytes of rows r0..r1) vs` with `mt`, `mf` row
  `r0`'s columns.

**Method.** A forward induction over the rows of the span carries the invariant `Inv`: the visits
completed so far form a `Chain` (a walk prefix) from segment `0` of family `mf` to the current
row's segment, family `q` (`qf ≡ q`) and pending length `pl` (`pl = some n ⇒ L = n`); the bytes
of the current segment so far are `cur` (`k = |cur|`, `k0 = [cur = []]`), and in a length kind
`pw = 256^|cur|`, `acc = leV (cur ++ [b])` (mod `p`). At a row with `e = 1` the segment's visit
`cur ++ [b]` satisfies `VisitOK` (`visit_at`), and either the message ends (`EndOK`, at `r1`) or
continues (`ContOK`, next segment `nextSeg`, family `+ newRAt`, pending length `nextPl`). Counters
do not wrap: the table has at most `2^20` rows.
-/

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus

/-! ## Walk prefixes -/

/-- A chain of completed (continuing) visits from `(s, q, pl)` to `(s2, q2, pl2)`. -/
inductive Chain (mt : Nat) : Nat → Nat → Option Nat → List Visit → Nat → Nat → Option Nat → Prop
  | nil {s q : Nat} {pl : Option Nat} : Chain mt s q pl [] s q pl
  | cons {s q : Nat} {pl : Option Nat} {g : Seg} {bs : List Nat} {vs : List Visit} {s2 q2 : Nat}
      {pl2 : Option Nat} :
      segAt mt s = some g → VisitOK g pl bs → ContOK g bs →
      Chain mt (nextSeg g bs) (q + newRAt mt (nextSeg g bs)) (nextPl g bs) vs s2 q2 pl2 →
      Chain mt s q pl (⟨s, q, bs⟩ :: vs) s2 q2 pl2

theorem Chain.snoc {mt s q s2 q2 : Nat} {pl pl2 : Option Nat} {vs : List Visit} {g : Seg} {bs : List Nat}
    (hc : Chain mt s q pl vs s2 q2 pl2) (hg : segAt mt s2 = some g) (hv : VisitOK g pl2 bs)
    (hk : ContOK g bs) :
    Chain mt s q pl (vs ++ [⟨s2, q2, bs⟩]) (nextSeg g bs) (q2 + newRAt mt (nextSeg g bs)) (nextPl g bs) := by
  induction hc with
  | nil => exact .cons hg hv hk .nil
  | cons h1 h2 h3 _ ih => exact .cons h1 h2 h3 (ih hg hv)

theorem Chain.walk {mt s q s2 q2 : Nat} {pl pl2 : Option Nat} {vs : List Visit} {g : Seg} {bs : List Nat}
    (hc : Chain mt s q pl vs s2 q2 pl2) (hg : segAt mt s2 = some g) (hv : VisitOK g pl2 bs)
    (he : EndOK g bs) : Walk mt s q pl (vs ++ [⟨s2, q2, bs⟩]) := by
  induction hc with
  | nil => exact .last hg hv he
  | cons h1 h2 h3 _ ih => exact .cons h1 h2 h3 (ih hg hv)

theorem vbytes_append (a b : List Visit) : vbytes (a ++ b) = vbytes a ++ vbytes b := by
  simp [vbytes]

theorem vbytes_single (v : Visit) : vbytes [v] = v.bs := by simp [vbytes]

/-! ## Message spans -/

section
variable (tr : Trace Fp) (pub : List Fp)

/-- The `b` column of rows `r0 .. r0 + n − 1`. -/
def rowBytes (r0 n : Nat) : List Nat := (List.range n).map fun i => V tr pub (r0 + i) "b"

/-- **A message span**: rows `r0..r1` within the table, `first` at `r0`, `endm` at `r1` and at no
earlier row of the span. -/
structure IsSpan (r0 r1 : Nat) : Prop where
  le : r0 ≤ r1
  lt : r1 < tr.height 3
  first : V tr pub r0 "first" = 1
  endm : V tr pub r1 "endm" = 1
  mid : ∀ x, r0 ≤ x → x < r1 → V tr pub x "endm" = 0
end

theorem rowBytes_succ {tr : Trace Fp} {pub : List Fp} (r0 n : Nat) :
    rowBytes tr pub r0 (n + 1) = rowBytes tr pub r0 n ++ [V tr pub (r0 + n) "b"] := by
  simp [rowBytes, List.range_succ]

theorem rowBytes_length {tr : Trace Fp} {pub : List Fp} (r0 n : Nat) : (rowBytes tr pub r0 n).length = n := by
  simp [rowBytes]

/-! ## Small lemmas on `b2n` and kinds -/

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide
theorem b2n_eq_one {b : Bool} (h : b2n b = 1) : b = true := by cases b <;> simp_all [b2n]
theorem b2n_eq_zero {b : Bool} (h : b2n b = 0) : b = false := by cases b <;> simp_all [b2n]
theorem b2n_and (a b : Bool) : b2n (a && b) = b2n a * b2n b := by cases a <;> cases b <;> rfl

theorem isLen_sum (g : Seg) :
    b2n (g.kind == K_LP) + b2n (g.kind == K_LE) + b2n (g.kind == K_CNT) = b2n g.isLen := by
  show b2n (g.kind == 5) + b2n (g.kind == 6) + b2n (g.kind == 7) = b2n ((g.kind == 5 || g.kind == 6) || g.kind == 7)
  by_cases h5 : g.kind = 5 <;> by_cases h6 : g.kind = 6 <;> by_cases h7 : g.kind = 7 <;> simp_all [b2n] <;> omega

theorem isLenP_sum (g : Seg) : b2n (g.kind == K_LP) + b2n (g.kind == K_LE) = b2n g.isLenP := by
  show b2n (g.kind == 5) + b2n (g.kind == 6) = b2n (g.kind == 5 || g.kind == 6)
  by_cases h5 : g.kind = 5 <;> by_cases h6 : g.kind = 6 <;> simp_all [b2n] <;> omega

theorem isLen_of_isLenP {g : Seg} (h : g.isLenP = true) : g.isLen = true := by
  simp only [Seg.isLenP, Seg.isLen, Bool.or_eq_true] at h ⊢; exact Or.inl h

/-! ## The rows of a span -/

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}
variable (H : Holds (fullAir tape xtape) pub tr) {r0 r1 : Nat} (hsp : IsSpan tr pub r0 r1)
include H hsp

theorem act_span : ∀ d, r0 + d ≤ r1 → V tr pub (r0 + d) "act" = 1 := by
  intro d
  induction d with
  | zero => intro _; exact c6 H (by have := hsp.lt; omega) hsp.first
  | succ d ih =>
    intro hd
    exact c12 H (r := r0 + d) (by have := hsp.lt; omega) (ih (by omega)) (hsp.mid _ (by omega) (by omega))

theorem act_span' {x : Nat} (h1 : r0 ≤ x) (h2 : x ≤ r1) : V tr pub x "act" = 1 := by
  have := act_span H hsp (x - r0) (by omega); rwa [Nat.add_sub_cancel' h1] at this

theorem first_span {x : Nat} (h1 : r0 < x) (h2 : x ≤ r1) : V tr pub x "first" = 0 := by
  have hl := hsp.lt
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have h := c11 H (r := y) (by omega) (e_le H (by omega)) (endm_le H (by omega))
  rw [hsp.mid y (by omega) (by omega)] at h
  simpa using h

theorem inm_span {x : Nat} (h1 : r0 ≤ x) (h2 : x < r1) : V tr pub x "inm" = 1 :=
  c13 H (by have := hsp.lt; omega) (act_span' H hsp (by omega) (by omega)) (first_span H hsp (by omega) (by omega))

theorem mt_span : ∀ d, r0 + d ≤ r1 → V tr pub (r0 + d) "mt" = V tr pub r0 "mt" := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    rw [← ih (by omega)]
    exact c15 H (r := r0 + d) (by have := hsp.lt; omega) (inm_span H hsp (by omega) (by omega))

theorem mt_span' {x : Nat} (h1 : r0 ≤ x) (h2 : x ≤ r1) : V tr pub x "mt" = V tr pub r0 "mt" := by
  have := mt_span H hsp (x - r0) (by omega); rwa [Nat.add_sub_cancel' h1] at this
end

/-! ## The invariant -/

/-- The invariant at row `x` of a span starting at `r0`: completed visits `vs` (a `Chain` from
segment `0` of family `mf` to the row's segment `s`, family `q`, pending length `pl`) and the
bytes `cur` of the current segment before row `x`. -/
structure Inv (tr : Trace Fp) (pub : List Fp) (r0 x mt mf : Nat) (vs : List Visit) (cur : List Nat)
    (q : Nat) (pl : Option Nat) : Prop where
  chain : Chain mt 0 mf none vs (V tr pub x "s") q pl
  bytes : vbytes vs ++ cur = rowBytes tr pub r0 (x - r0)
  cur8 : ∀ b ∈ cur, b < 256
  k : V tr pub x "k" = cur.length
  k0 : V tr pub x "k0" = if cur = [] then 1 else 0
  pl : ∀ n, pl = some n → V tr pub x "L" = n
  qf : V tr pub x "qf" = q % 2013265921
  acc : V tr pub x "kLP" + V tr pub x "kLE" + V tr pub x "kCNT" = 1 →
    V tr pub x "pw" = 256 ^ cur.length % 2013265921 ∧
    V tr pub x "acc" = leV (cur ++ [V tr pub x "b"]) % 2013265921

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}

/-- **Premise bundle** for the row lemma: every row's descriptor is a schema entry (`sch_row`),
every active row's byte is a byte (`RNG`). -/
structure RowHyps (tr : Trace Fp) (pub : List Fp) : Prop where
  desc : ∀ x < tr.height 3, ∃ g ∈ schema, Desc tr pub x g
  byte : ∀ x < tr.height 3, V tr pub x "act" = 1 → V tr pub x "b" < 256

theorem rowHyps_of (H : Holds (fullAir tape xtape) pub tr) (hS : SchtFixed tr)
    (hs1 : NoSendOn B_SCH tape) (hs2 : NoSendOn B_SCH xtape) (hr1 : NoRng tape) (hr2 : NoRng xtape) :
    RowHyps tr pub where
  desc := fun x hx => by
    obtain ⟨g, hg, hd⟩ := sch_row H hS hs1 hs2 hx
    exact ⟨g, hg, desc_of hd⟩
  byte := fun x hx hA => b_lt H hr1 hr2 hx hA

theorem desc_unique {x y : Nat} {g g' : Seg} (hg : g ∈ schema) (hg' : g' ∈ schema)
    (hd : Desc tr pub x g) (hd' : Desc tr pub y g') (hm : V tr pub x "mt" = V tr pub y "mt")
    (hs : V tr pub x "s" = V tr pub y "s") : g = g' := by
  have h1 := segAt_of_mem hg
  have h2 := segAt_of_mem hg'
  rw [← hd.mt, ← hd.s, hm, hs, hd'.mt, hd'.s, h2] at h1
  exact (Option.some.inj h1).symm

theorem segAt_desc {x : Nat} {g : Seg} (hg : g ∈ schema) (hd : Desc tr pub x g) :
    segAt (V tr pub x "mt") (V tr pub x "s") = some g := by
  rw [hd.mt, hd.s]; exact segAt_of_mem hg

variable (H : Holds (fullAir tape xtape) pub tr) (RH : RowHyps tr pub) {r0 r1 : Nat}
  (hsp : IsSpan tr pub r0 r1)
include H RH hsp

theorem inv_start : Inv tr pub r0 r0 (V tr pub r0 "mt") (V tr pub r0 "mf") [] [] (V tr pub r0 "mf") none := by
  have hr : r0 < tr.height 3 := by have := hsp.lt; have := hsp.le; omega
  obtain ⟨hj, hk, hs, hq, hk0⟩ := cfirst H hr hsp.first
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact .nil
  · simp [vbytes, rowBytes]
  · simp
  · simpa using hk
  · simpa using hk0
  · intro n hn; cases hn
  · rw [hq, Nat.mod_eq_of_lt (V_lt _ _ _ _)]
  · intro hl
    obtain ⟨hp, ha⟩ := c36 H hr hl hk0
    have hb := V_lt tr pub r0 "b"
    simp only [hp, ha, List.nil_append, leV, List.length_nil, Nat.pow_zero, Nat.one_mod, true_and]
    omega

/-- **The visit ending at a row with `e = 1`**: its bytes `cur ++ [b]` satisfy `VisitOK`, the
zero flag is `zOf`, and a length kind's `acc` is the visit's value. -/
theorem visit_at {x mt mf q : Nat} {vs : List Visit} {cur : List Nat} {pl : Option Nat}
    (hx1 : r0 ≤ x) (hx2 : x ≤ r1) (I : Inv tr pub r0 x mt mf vs cur q pl) (he : V tr pub x "e" = 1)
    {g : Seg} (hg : g ∈ schema) (hd : Desc tr pub x g) :
    VisitOK g pl (cur ++ [V tr pub x "b"]) ∧ V tr pub x "z" = b2n (zOf g (cur ++ [V tr pub x "b"])) ∧
    (g.isLen = true → V tr pub x "acc" = leV (cur ++ [V tr pub x "b"])) := by
  have hl := hsp.lt
  have hxH : x < tr.height 3 := by omega
  have hHt := msg_height H
  have hA := act_span' H hsp hx1 hx2
  have hb := RH.byte x hxH hA
  have hcl : cur.length ≤ x - r0 := by
    have := congrArg List.length I.bytes
    simp only [List.length_append, rowBytes_length] at this; omega
  have hL : V tr pub x "L" = cur.length + 1 := by
    rw [c28 H hxH he, I.k, Nat.mod_eq_of_lt (by omega)]
  have hsh := shape_of_mem hg
  have hlen : (cur ++ [V tr pub x "b"]).length = cur.length + 1 := by simp
  have hfix : g.var = false → (cur ++ [V tr pub x "b"]).length = g.fixL := by
    intro hv
    have := c27 H hxH (by rw [hd.var, hv]; rfl)
    rw [hlen, ← hL, this, hd.fixL]
  -- the length kinds
  have hlenK : g.isLen = true → (cur ++ [V tr pub x "b"]).length = 4 ∧ V tr pub x "b" = 0 := by
    intro hk
    refine ⟨by rw [hfix (hsh.2 hk).1, (hsh.2 hk).2], ?_⟩
    exact c40 H hxH (by rw [hd.kLP, hd.kLE, hd.kCNT, isLen_sum, hk]; rfl) he
  have hacc : g.isLen = true → V tr pub x "acc" = leV (cur ++ [V tr pub x "b"]) := by
    intro hk
    have h1 := (I.acc (by rw [hd.kLP, hd.kLE, hd.kCNT, isLen_sum, hk]; rfl)).2
    obtain ⟨h4, h0⟩ := hlenK hk
    have hlt : leV (cur ++ [V tr pub x "b"]) < 256 ^ 3 := by
      rw [leV_append, h0, Nat.mul_zero, Nat.add_zero]
      have := leV_lt cur I.cur8
      have hc3 : cur.length = 3 := by simp at h4; omega
      rw [hc3] at this; exact this
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, hfix, ?_, ?_⟩, ?_, hacc⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact I.cur8 y hy
    · rw [List.mem_singleton.1 hy]; exact hb
  · simp
  · intro hk
    obtain ⟨hv, hf⟩ := hsh.1 hk
    have h1 := hfix hv
    rw [hf, hlen] at h1
    have hc : cur = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hc, c44 H hxH (by rw [hd.kC, hk]; rfl), hd.cv]; rfl
  · intro hk
    obtain ⟨h4, h0⟩ := hlenK hk
    exact ⟨h4, by rw [h0]; simp⟩
  · intro hv _ n hn
    rw [hlen, ← hL, I.pl n hn]
  · intro hp
    have := hd.act
    rw [hA, hp] at this
    exact absurd this (by decide)
  · -- the zero flag
    have hz := z_le H hxH
    have hp1 : V tr pub x "kLP" + V tr pub x "kLE" = b2n g.isLenP := by rw [hd.kLP, hd.kLE, isLenP_sum]
    cases hP : g.isLenP
    · rw [hP] at hp1
      rw [c41 H hxH (by rw [hp1]; decide) (by omega) (Or.inl hp1)]
      simp [zOf, hP, b2n]
    · rw [hP] at hp1
      have hk := hacc (isLen_of_isLenP hP)
      rcases (show V tr pub x "z" = 0 ∨ V tr pub x "z" = 1 by omega) with h0 | h1
      · have := c43 H hxH hp1 he h0
        rw [hk] at this
        simp [zOf, hP, h0, b2n, this]
      · have := c42 H hxH h1
        rw [hk] at this
        simp [zOf, hP, h1, b2n, this]

/-- **One row of the span**: the invariant moves from row `x < r1` to row `x + 1`. -/
theorem inv_step {x q : Nat} {vs : List Visit} {cur : List Nat} {pl : Option Nat}
    (hx1 : r0 ≤ x) (hx2 : x < r1)
    (I : Inv tr pub r0 x (V tr pub r0 "mt") (V tr pub r0 "mf") vs cur q pl) :
    ∃ vs' cur' q' pl', Inv tr pub r0 (x + 1) (V tr pub r0 "mt") (V tr pub r0 "mf") vs' cur' q' pl' := by
  have hl := hsp.lt
  have hxH : x < tr.height 3 := by omega
  have hx1H : x + 1 < tr.height 3 := by omega
  have hHt := msg_height H
  have hA := act_span' H hsp hx1 (by omega)
  have hA1 := act_span' H hsp (x := x + 1) (by omega) (by omega)
  have hb := RH.byte x hxH hA
  have hb1 := RH.byte (x + 1) hx1H hA1
  have hi := inm_span H hsp hx1 hx2
  have hcl : cur.length ≤ x - r0 := by
    have := congrArg List.length I.bytes
    simp only [List.length_append, rowBytes_length] at this; omega
  have hmt := mt_span' H hsp hx1 (by omega)
  have hmt1 := mt_span' H hsp (x := x + 1) (by omega) (by omega)
  obtain ⟨g, hg, hd⟩ := RH.desc x hxH
  obtain ⟨g', hg', hd'⟩ := RH.desc (x + 1) hx1H
  have hseg : segAt (V tr pub r0 "mt") (V tr pub x "s") = some g := by rw [← hmt]; exact segAt_desc hg hd
  have hseg' : segAt (V tr pub r0 "mt") (V tr pub (x + 1) "s") = some g' := by
    rw [← hmt1]; exact segAt_desc hg' hd'
  have hel := e_le H hxH
  have hbytes : rowBytes tr pub r0 (x + 1 - r0) = rowBytes tr pub r0 (x - r0) ++ [V tr pub x "b"] := by
    rw [show x + 1 - r0 = (x - r0) + 1 by omega, rowBytes_succ, Nat.add_sub_cancel' hx1]
  rcases (show V tr pub x "e" = 0 ∨ V tr pub x "e" = 1 by omega) with he | he
  · -- inside a segment
    have hs1 : V tr pub (x + 1) "s" = V tr pub x "s" := by rw [c23 H hx1H hi hel, he]; rfl
    have hgg : g = g' := desc_unique hg hg' hd hd' (by rw [hmt, hmt1]) hs1.symm
    subst hgg
    refine ⟨vs, cur ++ [V tr pub x "b"], q, pl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hs1]; exact I.chain
    · rw [hbytes, ← I.bytes, List.append_assoc]
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact I.cur8 y hy
      · rw [List.mem_singleton.1 hy]; exact hb
    · rw [c21 H hx1H hi hel, he, I.k]; simp; omega
    · rw [c20 H hx1H hi, he]; simp
    · intro n hn; rw [c24 H hx1H hi he]; exact I.pl n hn
    · rw [c19 H hx1H hi hel, he, I.qf]; simp
    · intro hk
      have hk' : V tr pub x "kLP" + V tr pub x "kLE" + V tr pub x "kCNT" = 1 := by
        rw [hd.kLP, hd.kLE, hd.kCNT]; rw [hd'.kLP, hd'.kLE, hd'.kCNT] at hk; exact hk
      obtain ⟨hpw, hac⟩ := I.acc hk'
      have hk01 : V tr pub (x + 1) "k0" = 0 := by rw [c20 H hx1H hi, he]
      obtain ⟨hpw1, hac1⟩ := c38 H hx1H hk01 hk
      have hpb := c35 H (r := x + 1) hx1H
      refine ⟨?_, ?_⟩
      · rw [hpw1, hpw, List.length_append, List.length_singleton, Nat.pow_succ, Nat.mul_mod, Nat.mod_mod,
          ← Nat.mul_mod, Nat.mul_comm]
      · rw [hac1, hpb, hpw1, hac, hpw, leV_append (cur ++ [V tr pub x "b"])]
        simp only [List.length_append, List.length_singleton]
        have e1 : 256 * (256 ^ cur.length % 2013265921) % 2013265921 = 256 ^ (cur.length + 1) % 2013265921 := by
          rw [Nat.pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]
        rw [e1, Nat.mul_mod (256 ^ (cur.length + 1) % 2013265921), Nat.mod_mod, ← Nat.mul_mod,
          ← Nat.add_mod]
  · -- the last byte of a segment: one more visit
    obtain ⟨hv, hz, hacc⟩ := visit_at H RH hsp hx1 (by omega) I he hg hd
    have hm0 := hsp.mid x hx1 hx2
    obtain ⟨hcont, hzs⟩ := c47 H hxH he hm0
    have hcok : ContOK g (cur ++ [V tr pub x "b"]) := by
      refine ⟨b2n_eq_one (hd.cont ▸ hcont), ?_⟩
      rw [hz, hd.skipEnd, ← b2n_and] at hzs
      exact b2n_eq_zero hzs
    have hs1 : V tr pub (x + 1) "s" = nextSeg g (cur ++ [V tr pub x "b"]) := by
      rw [c23 H hx1H hi hel, he, if_pos rfl, c22 H hxH (z_le H hxH) (V_lt _ _ _ _) (V_lt _ _ _ _), hz,
        hd.skipS, hd.nextS]
      unfold nextSeg
      cases zOf g (cur ++ [V tr pub x "b"]) <;> rfl
    have hnr : newRAt (V tr pub r0 "mt") (nextSeg g (cur ++ [V tr pub x "b"])) = b2n g'.newR := by
      unfold newRAt; rw [← hs1, hseg']
    refine ⟨vs ++ [⟨V tr pub x "s", q, cur ++ [V tr pub x "b"]⟩], [],
      q + newRAt (V tr pub r0 "mt") (nextSeg g (cur ++ [V tr pub x "b"])),
      nextPl g (cur ++ [V tr pub x "b"]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hs1]; exact I.chain.snoc hseg hv hcok
    · rw [List.append_nil, vbytes_append, vbytes_single, hbytes, ← I.bytes, List.append_assoc]
    · simp
    · rw [c21 H hx1H hi hel, he]; rfl
    · rw [c20 H hx1H hi, he]; rfl
    · intro n hn
      unfold nextPl at hn
      split at hn
      · rename_i hc
        cases hn
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hz0 : V tr pub x "z" = 0 := by rw [hz, hc.2]; rfl
        have hsl := c25 H hxH (by rw [hd.kLP, hd.kLE, isLenP_sum, hc.1]; rfl) he hz0
        rw [c26 H hx1H hi hsl, hacc (isLen_of_isLenP hc.1)]
      · cases hn
    · rw [c19 H hx1H hi hel, he, I.qf, hd'.newR, hnr, Nat.one_mul, Nat.add_mod (q % 2013265921), Nat.mod_mod,
        ← Nat.add_mod]
    · intro hk
      have hk01 : V tr pub (x + 1) "k0" = 1 := by rw [c20 H hx1H hi, he]
      obtain ⟨hpw, hac⟩ := c36 H hx1H hk hk01
      have := V_lt tr pub (x + 1) "b"
      simp only [hpw, hac, List.nil_append, leV, List.length_nil, Nat.pow_zero, Nat.one_mod, true_and]
      omega

/-- The invariant holds at every row of the span. -/
theorem inv_all : ∀ d, r0 + d ≤ r1 → ∃ vs cur q pl,
    Inv tr pub r0 (r0 + d) (V tr pub r0 "mt") (V tr pub r0 "mf") vs cur q pl := by
  intro d
  induction d with
  | zero => intro _; exact ⟨_, _, _, _, inv_start H RH hsp⟩
  | succ d ih =>
    intro hd
    obtain ⟨vs, cur, q, pl, I⟩ := ih (by omega)
    exact inv_step H RH hsp (x := r0 + d) (by omega) (by omega) I

/-- **Rows → walk** (premises bundled in `RowHyps`). -/
theorem span_walk : ∃ vs, IsMsg (V tr pub r0 "mt") (V tr pub r0 "mf") (rowBytes tr pub r0 (r1 + 1 - r0)) vs := by
  have hl := hsp.lt
  have hle := hsp.le
  obtain ⟨vs, cur, q, pl, I⟩ := inv_all H RH hsp (r1 - r0) (by omega)
  rw [Nat.add_sub_cancel' hle] at I
  have hr1 : r1 < tr.height 3 := hl
  have he := c45 H hr1 hsp.endm
  obtain ⟨g, hg, hd⟩ := RH.desc r1 hr1
  obtain ⟨hv, hz, -⟩ := visit_at H RH hsp hle (Nat.le_refl _) I he hg hd
  have hmt := mt_span' H hsp hle (Nat.le_refl _)
  have hseg : segAt (V tr pub r0 "mt") (V tr pub r1 "s") = some g := by rw [← hmt]; exact segAt_desc hg hd
  have hend : EndOK g (cur ++ [V tr pub r1 "b"]) := by
    have h := c46 H hr1 hsp.endm (by rw [hd.endOK]; exact b2n_le _) (z_le H hr1)
      (by rw [hd.skipEnd]; exact b2n_le _)
    rw [hd.endOK, hz, hd.skipEnd, ← b2n_and] at h
    exact h
  refine ⟨vs ++ [⟨V tr pub r1 "s", q, cur ++ [V tr pub r1 "b"]⟩], I.chain.walk hseg hv hend, ?_⟩
  rw [vbytes_append, vbytes_single, ← List.append_assoc, I.bytes,
    show r1 + 1 - r0 = (r1 - r0) + 1 by omega, rowBytes_succ, Nat.add_sub_cancel' hle]
end

/-! ## The row lemma -/

/-- **`msg_walk`: the rows of a message are a walk.** On any trace satisfying the runtime AIR
`fullAir tape xtape`, with the preprocessed `SCHT` columns (`SchtFixed`) and public tapes that send
nothing on `SCH` and `RNG`: for every message span `r0..r1` of `MSG` (`IsSpan`: `first` at `r0`,
the first `endm` at `r1`), there are visits `vs` with `IsMsg mt mf m vs`, where `mt`, `mf` are row
`r0`'s columns and `m` is the `b` column of rows `r0..r1`. -/
theorem msg_walk {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}
    (H : Holds (fullAir tape xtape) pub tr) (hS : SchtFixed tr)
    (hs1 : NoSendOn B_SCH tape) (hs2 : NoSendOn B_SCH xtape) (hr1 : NoRng tape) (hr2 : NoRng xtape)
    {r0 r1 : Nat} (hsp : IsSpan tr pub r0 r1) :
    ∃ vs, IsMsg (V tr pub r0 "mt") (V tr pub r0 "mf") (rowBytes tr pub r0 (r1 + 1 - r0)) vs :=
  span_walk H (rowHyps_of H hS hs1 hs2 hr1 hr2) hsp

#print axioms sch_row
#print axioms msg_walk

end M5T1.MsgRow
