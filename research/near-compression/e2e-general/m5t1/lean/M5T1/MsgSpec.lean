import M5T1.Walk
import M5T1.SpecLink
import NearSpecV3.D2.State
import NearSpecV3.D3.FunctionCall
import NearSpecV3.RuntimeD1

/-!
# M5T1.MsgSpec — every `Walk` of a message type is the spec encoder of its fields

The walk → encoder half of the `MSG` soundness argument (F-2, see `Walk.lean`): for every message
type of the byte engine's schema (`Schema.lean`), the bytes of **every** walk (universally
quantified) are the spec's encoder of the record whose fields are the visits' bytes.

**Method.** A message layout is described by a list of *items* (`It`): a run of constant bytes,
a fixed-width field, a variable field with no length prefix, a u32 length prefix with its
variable field (skipped when the prefix is `0`), and the same pair where an empty field ends the
message (`skipEnd`). A Boolean checker `chk` (evaluated by the kernel, `decide +kernel`) verifies
that the schema entries of a message type follow an item list; one generic theorem
(`tmpl_walk`) then inverts every walk over such a schema into the items' values. Each message
type's theorem instantiates it and computes the spec encoder.

Bytes of the engine are `List Nat` (`< 256` by `RNG`); the spec's are `List UInt8`; `toB` maps
one to the other.
-/

namespace M5T1.MsgSpec

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Bytes -/

/-- Engine bytes (naturals `< 256`) as spec bytes. -/
def toB (l : List Nat) : Bytes := l.map UInt8.ofNat

/-- Every element is a byte. -/
def B8 (b : List Nat) : Prop := ∀ x ∈ b, x < 256

@[simp] theorem toB_nil : toB [] = [] := rfl
@[simp] theorem toB_cons (a : Nat) (l : List Nat) : toB (a :: l) = UInt8.ofNat a :: toB l := rfl
@[simp] theorem toB_append (a b : List Nat) : toB (a ++ b) = toB a ++ toB b := List.map_append
@[simp] theorem toB_length (a : List Nat) : (toB a).length = a.length := List.length_map _

theorem leBytes_succ (v n : Nat) : leBytes v (n + 1) = v % 256 :: leBytes (v / 256) n := by
  unfold leBytes
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.pow_zero, Nat.div_one, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- The engine's little-endian bytes are the spec's `leN`. -/
theorem toB_leBytes (v n : Nat) : toB (leBytes v n) = leN n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [leBytes_succ, toB_cons, ih]; rfl

/-- A byte list is the little-endian encoding of its value. -/
theorem leBytes_leV (bs : List Nat) (h : B8 bs) : leBytes (leV bs) bs.length = bs := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
    have hb : b < 256 := h b (by simp)
    have hr : B8 r := fun x hx => h x (by simp [hx])
    have e1 : (b + 256 * leV r) % 256 = b := by omega
    have e2 : (b + 256 * leV r) / 256 = leV r := by omega
    rw [List.length_cons, leBytes_succ]
    simp only [leV, e1, e2, ih hr]

/-- **Fixed-width fields**: the spec's `leN` of the visit's value. -/
theorem toB_eq_leN (bs : List Nat) (h : B8 bs) : toB bs = leN bs.length (leV bs) := by
  rw [← toB_leBytes, leBytes_leV bs h]

theorem toB_u32 {bs : List Nat} (h : B8 bs) (hl : bs.length = 4) : toB bs = u32 (leV bs) := by
  rw [toB_eq_leN bs h, hl]; rfl
theorem toB_u64 {bs : List Nat} (h : B8 bs) (hl : bs.length = 8) : toB bs = u64 (leV bs) := by
  rw [toB_eq_leN bs h, hl]; rfl
theorem toB_u128 {bs : List Nat} (h : B8 bs) (hl : bs.length = 16) : toB bs = u128 (leV bs) := by
  rw [toB_eq_leN bs h, hl]; rfl

theorem leV_lt (bs : List Nat) (h : B8 bs) : leV bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leV]
  | cons b r ih =>
    have hb : b < 256 := h b (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [leV, List.length_cons, Nat.pow_succ]
    have : 256 * leV r + 256 ≤ 256 * 256 ^ r.length := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt this); omega
    rw [Nat.mul_comm (256 ^ r.length)]; omega

/-- **Length kinds** (`K_LP`, `K_LE`, `K_CNT`): 4 bytes, the spec's `u32` of their value, which
is `< 2^24` (zero top byte). -/
theorem len_visit {g : Seg} {pl : Option Nat} {bs : List Nat} (hv : VisitOK g pl bs)
    (hk : g.isLen = true) :
    toB bs = u32 (leV bs) ∧ leV bs < 2 ^ 24 ∧ bs = leBytes (leV bs) 4 := by
  obtain ⟨hl, hlast⟩ := hv.len hk
  have h8 : B8 bs := hv.bytes
  refine ⟨toB_u32 h8 hl, ?_, by rw [← hl, leBytes_leV bs h8]⟩
  match bs, hl, hlast, h8 with
  | [a, b, c, d], _, hlast, h8 =>
    simp at hlast
    have := h8 a (by simp); have := h8 b (by simp); have := h8 c (by simp)
    subst hlast; simp only [leV]; omega

/-- A length prefix followed by its field is borsh `Vec<u8>`. -/
def lpB (b : List Nat) : List Nat := leBytes b.length 4 ++ b

theorem toB_lpB (b : List Nat) : toB (lpB b) = borshBytes (toB b) := by
  simp only [lpB, toB_append, toB_leBytes, borshBytes, toB_length]; rfl

theorem toB_flatten (ds : List (List Nat)) : toB ds.flatten = concatAll (ds.map toB) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.flatten_cons, concatAll, ih]

/-! ## Inverting one visit -/

section Steps

variable {mt s f : Nat} {pl : Option Nat} {vs : List Visit} {g : Seg}

theorem inv (hw : Walk mt s f pl vs) :
    ∃ g bs, segAt mt s = some g ∧ VisitOK g pl bs ∧
      ((EndOK g bs ∧ vs = [⟨s, f, bs⟩]) ∨
       (ContOK g bs ∧ ∃ vs', vs = ⟨s, f, bs⟩ :: vs' ∧
          Walk mt (nextSeg g bs) (f + newRAt mt (nextSeg g bs)) (nextPl g bs) vs')) := by
  cases hw with
  | last hs hv he => exact ⟨_, _, hs, hv, .inl ⟨he, rfl⟩⟩
  | cons hs hv hc hw => exact ⟨_, _, hs, hv, .inr ⟨hc, _, rfl, hw⟩⟩

theorem walk_ne_nil (hw : Walk mt s f pl vs) : vs ≠ [] := by
  cases hw <;> simp

/-- A non-length segment that cannot end the message. -/
theorem stepMid (hw : Walk mt s f pl vs) (hs : segAt mt s = some g) (hk : g.isLenP = false)
    (he : g.endOK = false) :
    ∃ bs vs', VisitOK g pl bs ∧ vs = ⟨s, f, bs⟩ :: vs' ∧
      Walk mt g.nextS (f + newRAt mt g.nextS) none vs' := by
  obtain ⟨g', bs, hs', hv, h⟩ := inv hw
  rw [hs] at hs'; cases hs'
  have hz : zOf g bs = false := by simp [zOf, hk]
  rcases h with ⟨hE, _⟩ | ⟨_, vs', rfl, hw'⟩
  · simp [EndOK, hz, he, b2n] at hE
  · have e1 : nextSeg g bs = g.nextS := by simp [nextSeg, hz]
    have e2 : nextPl g bs = none := by simp [nextPl, hk]
    rw [e1, e2] at hw'
    exact ⟨bs, vs', hv, rfl, hw'⟩

/-- A non-length segment that may end the message. -/
theorem stepEnd (hw : Walk mt s f pl vs) (hs : segAt mt s = some g) (hk : g.isLenP = false) :
    ∃ bs rest, VisitOK g pl bs ∧ vs = ⟨s, f, bs⟩ :: rest ∧
      (rest = [] ∨ (g.cont = true ∧ Walk mt g.nextS (f + newRAt mt g.nextS) none rest)) := by
  obtain ⟨g', bs, hs', hv, h⟩ := inv hw
  rw [hs] at hs'; cases hs'
  have hz : zOf g bs = false := by simp [zOf, hk]
  rcases h with ⟨_, rfl⟩ | ⟨hc, vs', rfl, hw'⟩
  · exact ⟨bs, [], hv, rfl, .inl rfl⟩
  · have e1 : nextSeg g bs = g.nextS := by simp [nextSeg, hz]
    have e2 : nextPl g bs = none := by simp [nextPl, hk]
    rw [e1, e2] at hw'
    exact ⟨bs, vs', hv, rfl, .inr ⟨hc.1, hw'⟩⟩

/-- A length prefix (no `skipEnd`) that cannot end the message: a zero prefix skips the field. -/
theorem stepLP (hw : Walk mt s f pl vs) (hs : segAt mt s = some g) (hk : g.isLenP = true)
    (hse : g.skipEnd = false) (he : g.endOK = false) :
    ∃ bs vs', VisitOK g pl bs ∧ vs = ⟨s, f, bs⟩ :: vs' ∧
      ((leV bs = 0 ∧ Walk mt g.skipS (f + newRAt mt g.skipS) none vs') ∨
       (leV bs ≠ 0 ∧ Walk mt g.nextS (f + newRAt mt g.nextS) (some (leV bs)) vs')) := by
  obtain ⟨g', bs, hs', hv, h⟩ := inv hw
  rw [hs] at hs'; cases hs'
  rcases h with ⟨hE, _⟩ | ⟨_, vs', rfl, hw'⟩
  · simp [EndOK, he, hse, b2n] at hE
  · refine ⟨bs, vs', hv, rfl, ?_⟩
    by_cases h0 : leV bs = 0
    · have hz : zOf g bs = true := by simp [zOf, hk, h0]
      have e1 : nextSeg g bs = g.skipS := by simp [nextSeg, hz]
      have e2 : nextPl g bs = none := by simp [nextPl, hz]
      rw [e1, e2] at hw'
      exact .inl ⟨h0, hw'⟩
    · have hz : zOf g bs = false := by simp [zOf, h0]
      have e1 : nextSeg g bs = g.nextS := by simp [nextSeg, hz]
      have e2 : nextPl g bs = some (leV bs) := by simp [nextPl, hz, hk]
      rw [e1, e2] at hw'
      exact .inr ⟨h0, hw'⟩

/-- A length prefix with `skipEnd`: a zero prefix ends the message. -/
theorem stepPE (hw : Walk mt s f pl vs) (hs : segAt mt s = some g) (hk : g.isLenP = true)
    (hse : g.skipEnd = true) (he : g.endOK = false) :
    ∃ bs, VisitOK g pl bs ∧
      ((leV bs = 0 ∧ vs = [⟨s, f, bs⟩]) ∨
       (leV bs ≠ 0 ∧ ∃ vs', vs = ⟨s, f, bs⟩ :: vs' ∧
          Walk mt g.nextS (f + newRAt mt g.nextS) (some (leV bs)) vs')) := by
  obtain ⟨g', bs, hs', hv, h⟩ := inv hw
  rw [hs] at hs'; cases hs'
  refine ⟨bs, hv, ?_⟩
  by_cases h0 : leV bs = 0
  · have hz : zOf g bs = true := by simp [zOf, hk, h0]
    rcases h with ⟨_, rfl⟩ | ⟨hc, _⟩
    · exact .inl ⟨h0, rfl⟩
    · simp [ContOK, hz, hse] at hc
  · have hz : zOf g bs = false := by simp [zOf, h0]
    rcases h with ⟨hE, _⟩ | ⟨_, vs', rfl, hw'⟩
    · simp [EndOK, he, hz, b2n] at hE
    · have e1 : nextSeg g bs = g.nextS := by simp [nextSeg, hz]
      have e2 : nextPl g bs = some (leV bs) := by simp [nextPl, hz, hk]
      rw [e1, e2] at hw'
      exact .inr ⟨h0, vs', rfl, hw'⟩

end Steps

theorem isLen_of_isLenP {g : Seg} (h : g.isLenP = true) : g.isLen = true := by
  simp only [Seg.isLenP, Seg.isLen, Bool.or_eq_true] at *; tauto

/-- The bytes of a length-prefix visit with value `n` are `leBytes n 4`, `n < 2^24`. -/
theorem lp_visit {g : Seg} {pl : Option Nat} {bs : List Nat} (hv : VisitOK g pl bs)
    (hk : g.isLenP = true) : bs = leBytes (leV bs) 4 ∧ leV bs < 2 ^ 24 :=
  let h := len_visit hv (isLen_of_isLenP hk); ⟨h.2.2, h.2.1⟩

/-! ## Layout items and the checker -/

/-- One item of a message layout. -/
inductive It where
  /-- a run of constant bytes (`K_C`) -/
  | c (cs : List Nat)
  /-- a fixed-width field of `L` bytes -/
  | fx (L : Nat)
  /-- a variable field without a length prefix (`K_UV`) -/
  | uv
  /-- a u32 length prefix and its variable field (absent when the prefix is `0`) -/
  | pr
  /-- the same, where an empty field ends the message (`skipEnd`) -/
  | pe
  deriving DecidableEq, Repr

/-- Number of schema segments of an item. -/
def It.w : It → Nat
  | .c cs => cs.length
  | .fx _ => 1
  | .uv => 1
  | .pr => 2
  | .pe => 2

/-- The visits of a constant run. -/
def constVis (s f : Nat) : List Nat → List Visit
  | [] => []
  | c :: cs => ⟨s, f, [c]⟩ :: constVis (s + 1) f cs

/-- The visits of a length prefix at segment `s` and its field `b` (no field visit if empty). -/
def lpv (s f : Nat) (b : List Nat) : List Visit :=
  ⟨s, f, leBytes b.length 4⟩ :: (if b = [] then [] else [⟨s + 1, f, b⟩])

def itVis (s f : Nat) : It → List Nat → List Visit
  | .c _, b => constVis s f b
  | .fx _, b => [⟨s, f, b⟩]
  | .uv, b => [⟨s, f, b⟩]
  | .pr, b => lpv s f b
  | .pe, b => lpv s f b

/-- The visits of a layout at segment `s`, family `f`, given the items' values. -/
def tvis (s f : Nat) : List It → List (List Nat) → List Visit
  | it :: its, b :: bs => itVis s f it b ++ tvis (s + it.w) f its bs
  | _, _ => []

def itBytes : It → List Nat → List Nat
  | .pr, b => lpB b
  | .pe, b => lpB b
  | _, b => b

/-- The bytes of a layout given the items' values. -/
def tbytes : List It → List (List Nat) → List Nat
  | it :: its, b :: bs => itBytes it b ++ tbytes its bs
  | _, _ => []

/-- What a value of an item is. -/
def vOK : It → List Nat → Prop
  | .c cs, b => b = cs
  | .fx L, b => b.length = L ∧ B8 b
  | .uv, b => b ≠ [] ∧ B8 b
  | .pr, b => b.length < 2 ^ 24 ∧ B8 b
  | .pe, b => b.length < 2 ^ 24 ∧ B8 b

def vOKs : List It → List (List Nat) → Prop
  | [], [] => True
  | it :: its, b :: bs => vOK it b ∧ vOKs its bs
  | _, _ => False

theorem vOKs_cons {it : It} {its : List It} {vals : List (List Nat)} (h : vOKs (it :: its) vals) :
    ∃ b bs, vals = b :: bs ∧ vOK it b ∧ vOKs its bs := by
  match vals, h with
  | b :: bs, h => exact ⟨b, bs, rfl, h.1, h.2⟩

theorem vOKs_nil {vals : List (List Nat)} (h : vOKs [] vals) : vals = [] := by
  match vals, h with
  | [], _ => rfl

def segIs (mt s : Nat) (p : Seg → Bool) : Bool :=
  match segAt mt s with
  | some g => p g
  | none => false

theorem segIs_spec {mt s : Nat} {p : Seg → Bool} (h : segIs mt s p = true) :
    ∃ g, segAt mt s = some g ∧ p g = true := by
  cases hs : segAt mt s with
  | none => simp [segIs, hs] at h
  | some g => exact ⟨g, rfl, by simpa [segIs, hs] using h⟩

/-- A segment in the middle of a family: cannot end, goes to `s'`, which opens no receipt. -/
def midP (mt s' : Nat) (g : Seg) : Bool := !g.endOK && g.nextS == s' && newRAt mt s' == 0

/-- A segment that may end the message; in `loop` mode it may also continue at `nx`, opening the
next receipt family. -/
def endP (mt nx : Nat) (loop : Bool) (g : Seg) : Bool :=
  g.endOK && (if loop then g.cont && g.nextS == nx && newRAt mt nx == 1 else !g.cont)

def constsMid (mt : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | s, c :: cs =>
    segIs mt s (fun g => g.kind == K_C && g.cv == c && !g.isLenP && midP mt (s + 1) g) &&
      constsMid mt (s + 1) cs

def constsLast (mt nx : Nat) (loop : Bool) : Nat → List Nat → Bool
  | _, [] => false
  | s, [c] => segIs mt s (fun g => g.kind == K_C && g.cv == c && !g.isLenP && endP mt nx loop g)
  | s, c :: d :: cs =>
    segIs mt s (fun g => g.kind == K_C && g.cv == c && !g.isLenP && midP mt (s + 1) g) &&
      constsLast mt nx loop (s + 1) (d :: cs)

def lpMid (mt s : Nat) (g : Seg) : Bool :=
  g.isLenP && !g.skipEnd && !g.endOK && g.nextS == s + 1 && g.skipS == s + 2 &&
    newRAt mt (s + 1) == 0 && newRAt mt (s + 2) == 0

def chkMid (mt s : Nat) : It → Bool
  | .c cs => cs != [] && constsMid mt s cs
  | .fx L => segIs mt s (fun g => !g.isLenP && !g.var && g.fixL == L && midP mt (s + 1) g)
  | .uv => segIs mt s (fun g => !g.isLenP && g.var && midP mt (s + 1) g)
  | .pr => segIs mt s (lpMid mt s) &&
      segIs mt (s + 1) (fun g => g.var && g.kind != K_UV && !g.isLenP && midP mt (s + 2) g)
  | .pe => false

def chkLast (mt nx : Nat) (loop : Bool) (s : Nat) : It → Bool
  | .c cs => constsLast mt nx loop s cs
  | .fx L => segIs mt s (fun g => !g.isLenP && !g.var && g.fixL == L && endP mt nx loop g)
  | .uv => segIs mt s (fun g => !g.isLenP && g.var && endP mt nx loop g)
  | .pr => false
  | .pe => !loop &&
      segIs mt s (fun g => g.isLenP && g.skipEnd && !g.endOK && g.nextS == s + 1 &&
        newRAt mt (s + 1) == 0) &&
      segIs mt (s + 1) (fun g => g.var && g.kind != K_UV && !g.isLenP && endP mt nx loop g)

/-- **The checker**: the schema entries of type `mt` from segment `s` follow the item list. -/
def chk (mt nx : Nat) (loop : Bool) : Nat → List It → Bool
  | _, [] => false
  | s, [it] => chkLast mt nx loop s it
  | s, it :: it2 :: its => chkMid mt s it && chk mt nx loop (s + it.w) (it2 :: its)

/-- What may follow the last item: nothing, or (loop mode) the next family's walk from `nx`. -/
def Tail (mt nx : Nat) (loop : Bool) (f : Nat) (rest : List Visit) : Prop :=
  rest = [] ∨ (loop = true ∧ Walk mt nx (f + 1) none rest)

/-! ## The generic inversion -/

section Items

variable {mt nx s f : Nat} {loop : Bool} {pl : Option Nat} {vs : List Visit}

theorem constsMid_walk {cs : List Nat} (hc : constsMid mt s cs = true) (hne : cs ≠ [])
    (hw : Walk mt s f pl vs) :
    ∃ vs', vs = constVis s f cs ++ vs' ∧ Walk mt (s + cs.length) f none vs' := by
  induction cs generalizing s pl vs with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    simp only [constsMid, Bool.and_eq_true] at hc
    obtain ⟨g, hs, hp⟩ := segIs_spec hc.1
    simp only [midP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨⟨hk, hcv⟩, hlp⟩, ⟨he, hn⟩, hr⟩ := hp
    obtain ⟨bs, vs', hv, rfl, hw'⟩ := stepMid hw hs hlp he
    rw [hn, hr, Nat.add_zero] at hw'
    have hb : bs = [c] := by rw [hv.kc hk, hcv]
    subst hb
    rcases cs with _ | ⟨d, cs⟩
    · exact ⟨vs', rfl, hw'⟩
    · obtain ⟨vs'', rfl, hw''⟩ := ih hc.2 (by simp) hw'
      refine ⟨vs'', rfl, ?_⟩
      have e : s + 1 + (d :: cs).length = s + (c :: d :: cs).length := by simp; omega
      rwa [e] at hw''

theorem constsLast_walk {cs : List Nat} (hc : constsLast mt nx loop s cs = true)
    (hw : Walk mt s f pl vs) :
    ∃ rest, vs = constVis s f cs ++ rest ∧ Tail mt nx loop f rest := by
  induction cs generalizing s pl vs with
  | nil => simp [constsLast] at hc
  | cons c cs ih =>
    rcases cs with _ | ⟨d, cs⟩
    · simp only [constsLast] at hc
      obtain ⟨g, hs, hp⟩ := segIs_spec hc
      simp only [endP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      obtain ⟨⟨⟨hk, hcv⟩, hlp⟩, he, hl⟩ := hp
      obtain ⟨bs, rest, hv, rfl, hr⟩ := stepEnd hw hs hlp
      have hb : bs = [c] := by rw [hv.kc hk, hcv]
      subst hb
      refine ⟨rest, rfl, ?_⟩
      rcases hr with rfl | ⟨hct, hw'⟩
      · exact .inl rfl
      · cases loop with
        | false => simp [hct] at hl
        | true =>
          simp only [if_true, Bool.and_eq_true, beq_iff_eq] at hl
          obtain ⟨⟨_, hn⟩, hr1⟩ := hl
          rw [hn, hr1] at hw'
          exact .inr ⟨rfl, hw'⟩
    · simp only [constsLast, Bool.and_eq_true] at hc
      obtain ⟨g, hs, hp⟩ := segIs_spec hc.1
      simp only [midP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      obtain ⟨⟨⟨hk, hcv⟩, hlp⟩, ⟨he, hn⟩, hr⟩ := hp
      obtain ⟨bs, vs', hv, rfl, hw'⟩ := stepMid hw hs hlp he
      rw [hn, hr, Nat.add_zero] at hw'
      have hb : bs = [c] := by rw [hv.kc hk, hcv]
      subst hb
      obtain ⟨rest, rfl, ht⟩ := ih hc.2 hw'
      exact ⟨rest, rfl, ht⟩

theorem lpv_nil (s f : Nat) : lpv s f [] = [⟨s, f, leBytes 0 4⟩] := rfl

theorem lpv_ne {b : List Nat} (s f : Nat) (h : b ≠ []) :
    lpv s f b = [⟨s, f, leBytes b.length 4⟩, ⟨s + 1, f, b⟩] := by
  simp [lpv, h]

theorem item_mid {it : It} (hc : chkMid mt s it = true) (hw : Walk mt s f pl vs) :
    ∃ b vs', vOK it b ∧ vs = itVis s f it b ++ vs' ∧ Walk mt (s + it.w) f none vs' := by
  cases it with
  | c cs =>
    simp only [chkMid, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨vs', rfl, hw'⟩ := constsMid_walk hc.2 hc.1 hw
    exact ⟨cs, vs', rfl, rfl, hw'⟩
  | fx L =>
    simp only [chkMid] at hc
    obtain ⟨g, hs, hp⟩ := segIs_spec hc
    simp only [midP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨⟨hlp, hvar⟩, hL⟩, ⟨he, hn⟩, hr⟩ := hp
    obtain ⟨bs, vs', hv, rfl, hw'⟩ := stepMid hw hs hlp he
    rw [hn, hr, Nat.add_zero] at hw'
    exact ⟨bs, vs', ⟨by rw [hv.fix hvar, hL], hv.bytes⟩, rfl, hw'⟩
  | uv =>
    simp only [chkMid] at hc
    obtain ⟨g, hs, hp⟩ := segIs_spec hc
    simp only [midP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨hlp, _⟩, ⟨he, hn⟩, hr⟩ := hp
    obtain ⟨bs, vs', hv, rfl, hw'⟩ := stepMid hw hs hlp he
    rw [hn, hr, Nat.add_zero] at hw'
    exact ⟨bs, vs', ⟨List.ne_nil_of_length_pos hv.pos, hv.bytes⟩, rfl, hw'⟩
  | pr =>
    simp only [chkMid, Bool.and_eq_true] at hc
    obtain ⟨g1, hs1, hp1⟩ := segIs_spec hc.1
    obtain ⟨g2, hs2, hp2⟩ := segIs_spec hc.2
    simp only [lpMid, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp1
    obtain ⟨⟨⟨⟨⟨⟨hk1, hse1⟩, he1⟩, hn1⟩, hsk1⟩, hr1⟩, hr2⟩ := hp1
    simp only [midP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at hp2
    obtain ⟨⟨⟨hvar2, huv2⟩, hlp2⟩, ⟨he2, hn2⟩, hr2'⟩ := hp2
    obtain ⟨bs, vs', hv, rfl, h⟩ := stepLP hw hs1 hk1 hse1 he1
    obtain ⟨hbs, hlt⟩ := lp_visit hv hk1
    rcases h with ⟨h0, hw'⟩ | ⟨h0, hw'⟩
    · rw [hsk1, hr2, Nat.add_zero] at hw'
      refine ⟨[], vs', ⟨by simp, by simp [B8]⟩, ?_, hw'⟩
      rw [hbs, h0]; rfl
    · rw [hn1, hr1, Nat.add_zero] at hw'
      obtain ⟨b, vs'', hv2, rfl, hw''⟩ := stepMid hw' hs2 hlp2 he2
      rw [hn2, hr2', Nat.add_zero] at hw''
      have hlen : b.length = leV bs := hv2.var hvar2 huv2 _ rfl
      have hne : b ≠ [] := List.ne_nil_of_length_pos hv2.pos
      refine ⟨b, vs'', ⟨by omega, hv2.bytes⟩, ?_, hw''⟩
      simp only [itVis, lpv_ne s f hne, List.cons_append, List.nil_append]
      rw [hbs, hlen]
  | pe => simp [chkMid] at hc

theorem end_tail {g : Seg} {rest : List Visit}
    (hl : endP mt nx loop g = true)
    (hr : rest = [] ∨ (g.cont = true ∧ Walk mt g.nextS (f + newRAt mt g.nextS) none rest)) :
    Tail mt nx loop f rest := by
  rcases hr with rfl | ⟨hct, hw'⟩
  · exact .inl rfl
  · simp only [endP, Bool.and_eq_true] at hl
    cases loop with
    | false => simp [hct] at hl
    | true =>
      simp only [if_true, Bool.and_eq_true, beq_iff_eq] at hl
      obtain ⟨_, ⟨_, hn⟩, hr1⟩ := hl
      rw [hn, hr1] at hw'
      exact .inr ⟨rfl, hw'⟩

theorem item_last {it : It} (hc : chkLast mt nx loop s it = true) (hw : Walk mt s f pl vs) :
    ∃ b rest, vOK it b ∧ vs = itVis s f it b ++ rest ∧ Tail mt nx loop f rest := by
  cases it with
  | c cs =>
    simp only [chkLast] at hc
    obtain ⟨rest, rfl, ht⟩ := constsLast_walk hc hw
    exact ⟨cs, rest, rfl, rfl, ht⟩
  | fx L =>
    simp only [chkLast] at hc
    obtain ⟨g, hs, hp⟩ := segIs_spec hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨⟨hlp, hvar⟩, hL⟩, hl⟩ := hp
    obtain ⟨bs, rest, hv, rfl, hr⟩ := stepEnd hw hs hlp
    exact ⟨bs, rest, ⟨by rw [hv.fix hvar, hL], hv.bytes⟩, rfl, end_tail hl hr⟩
  | uv =>
    simp only [chkLast] at hc
    obtain ⟨g, hs, hp⟩ := segIs_spec hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    obtain ⟨⟨hlp, _⟩, hl⟩ := hp
    obtain ⟨bs, rest, hv, rfl, hr⟩ := stepEnd hw hs hlp
    exact ⟨bs, rest, ⟨List.ne_nil_of_length_pos hv.pos, hv.bytes⟩, rfl, end_tail hl hr⟩
  | pr => simp [chkLast] at hc
  | pe =>
    simp only [chkLast, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨hloop, h1⟩, h2⟩ := hc
    obtain ⟨g1, hs1, hp1⟩ := segIs_spec h1
    obtain ⟨g2, hs2, hp2⟩ := segIs_spec h2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp1
    obtain ⟨⟨⟨⟨hk1, hse1⟩, he1⟩, hn1⟩, hr1⟩ := hp1
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hp2
    obtain ⟨⟨⟨hvar2, huv2⟩, hlp2⟩, hl2⟩ := hp2
    obtain ⟨bs, hv, h⟩ := stepPE hw hs1 hk1 hse1 he1
    obtain ⟨hbs, hlt⟩ := lp_visit hv hk1
    rcases h with ⟨h0, rfl⟩ | ⟨h0, vs', rfl, hw'⟩
    · refine ⟨[], [], ⟨by simp, by simp [B8]⟩, ?_, .inl rfl⟩
      rw [hbs, h0]; rfl
    · rw [hn1, hr1, Nat.add_zero] at hw'
      obtain ⟨b, rest, hv2, rfl, hr⟩ := stepEnd hw' hs2 hlp2
      have hlen : b.length = leV bs := hv2.var hvar2 huv2 _ rfl
      have hne : b ≠ [] := List.ne_nil_of_length_pos hv2.pos
      refine ⟨b, rest, ⟨by omega, hv2.bytes⟩, ?_, end_tail hl2 hr⟩
      simp only [itVis, lpv_ne s f hne, List.cons_append, List.nil_append]
      rw [hbs, hlen]

/-- **Generic inversion**: a walk over a schema that follows the item list `its` is the items'
visits, for values satisfying `vOKs`, followed by nothing or (loop mode) the next family. -/
theorem tmpl_walk {its : List It} (hc : chk mt nx loop s its = true) (hw : Walk mt s f pl vs) :
    ∃ vals rest, vOKs its vals ∧ vs = tvis s f its vals ++ rest ∧ Tail mt nx loop f rest := by
  induction its generalizing s pl vs with
  | nil => simp [chk] at hc
  | cons it its ih =>
    rcases its with _ | ⟨it2, its⟩
    · obtain ⟨b, rest, hb, rfl, ht⟩ := item_last hc hw
      exact ⟨[b], rest, ⟨hb, trivial⟩, by simp [tvis], ht⟩
    · simp only [chk, Bool.and_eq_true] at hc
      obtain ⟨b, vs', hb, rfl, hw'⟩ := item_mid hc.1 hw
      obtain ⟨vals, rest, hvals, rfl, ht⟩ := ih hc.2 hw'
      exact ⟨b :: vals, rest, ⟨hb, hvals⟩, by simp [tvis, List.append_assoc], ht⟩

end Items

/-! ## Bytes of the visits -/

theorem vbytes_append (a b : List Visit) : vbytes (a ++ b) = vbytes a ++ vbytes b := by
  simp [vbytes, List.flatten_append]

theorem vbytes_constVis (s f : Nat) (cs : List Nat) : vbytes (constVis s f cs) = cs := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    show [c] ++ vbytes (constVis (s + 1) f cs) = c :: cs
    rw [ih]; rfl

theorem vbytes_lpv (s f : Nat) (b : List Nat) : vbytes (lpv s f b) = lpB b := by
  by_cases h : b = []
  · subst h; rfl
  · rw [lpv_ne s f h]; simp [vbytes, lpB]

theorem vbytes_itVis (s f : Nat) (it : It) (b : List Nat) :
    vbytes (itVis s f it b) = itBytes it b := by
  cases it <;> simp [itVis, itBytes, vbytes_constVis, vbytes_lpv, vbytes]

theorem vbytes_tvis (s f : Nat) (its : List It) (vals : List (List Nat)) :
    vbytes (tvis s f its vals) = tbytes its vals := by
  induction its generalizing s vals with
  | nil => rfl
  | cons it its ih =>
    cases vals with
    | nil => rfl
    | cons b bs => simp [tvis, tbytes, vbytes_append, vbytes_itVis, ih]

/-- **Messages of a non-looping layout** starting at segment `0`. -/
theorem tmpl_msg {mt mf : Nat} {m : List Nat} {vs : List Visit} {its : List It}
    (hc : chk mt 0 false 0 its = true) (h : IsMsg mt mf m vs) :
    ∃ vals, vOKs its vals ∧ vs = tvis 0 mf its vals ∧ m = tbytes its vals := by
  obtain ⟨vals, rest, hv, rfl, ht⟩ := tmpl_walk hc h.1
  have : rest = [] := by
    rcases ht with h | ⟨h, _⟩
    · exact h
    · cases h
  subst this
  refine ⟨vals, hv, by simp, ?_⟩
  rw [← h.2, List.append_nil, vbytes_tvis]

end M5T1.MsgSpec
