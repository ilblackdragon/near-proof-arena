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
  simp only [Seg.isLenP] at h; simp [Seg.isLen, h]

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
          simp only [ite_true, Bool.and_eq_true, beq_iff_eq] at hl
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
      rw [hbs, hlen]; rfl
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
      simp only [ite_true, Bool.and_eq_true, beq_iff_eq] at hl
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
      rw [hbs, hlen]; rfl

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
  cases it with
  | c cs => exact vbytes_constVis s f b
  | fx L => simp [itVis, itBytes, vbytes]
  | uv => simp [itVis, itBytes, vbytes]
  | pr => exact vbytes_lpv s f b
  | pe => exact vbytes_lpv s f b

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

/-! ## The layouts of the schema, checked against it -/

def itsKey : List It := [.c [0], .uv]
def itsAcct : List It := [.fx 16, .fx 16, .fx 32, .fx 8]
def itsAH : List It := [.fx 32, .fx 8, .c (leBytes (2 ^ 64 - 1) 8)]
def itsSeed : List It := [.fx 32, .fx 32]
def itsRid : List It := [.fx 32, .fx 8, .c (leBytes 0 8)]
/-- The constants of `RREF` after the signer key: `gas_price = 0`, no outputs, no inputs, one
action, `Transfer`. -/
def rrefC : List Nat := leBytes 0 16 ++ u32b 0 ++ u32b 0 ++ u32b 1 ++ [3]
def itsRRef : List It :=
  [.c (u32b 6 ++ systemId), .pr, .fx 32, .c [0], .pr, .c [0], .fx 32, .c rrefC, .fx 16]
def itsLog : List It := [.uv]
def itsPart : List It := [.c (u32b 1), .fx 32, .fx 8, .fx 16, .pr, .c [2], .pe]
def itsLeaf (n : Nat) : List It := [.fx 4, .fx 32, .fx 32] ++ List.replicate n (.fx 32)
/-- The constants of an `RL` receipt after the gas price: no outputs, no inputs, one action,
`FunctionCall`. -/
def rlC : List Nat := u32b 0 ++ u32b 0 ++ u32b 1 ++ [2]
/-- One receipt of `RL`, segments `1 … 30`. -/
def itsRL : List It :=
  [.pr, .pr, .fx 32, .c [0], .pr, .c [0], .fx 32, .fx 16, .c rlC, .pr, .pr, .fx 8, .fx 16]

theorem chk_keyr : chk MT_KEYR 0 false 0 itsKey = true := by decide +kernel
theorem chk_keyw : chk MT_KEYW 0 false 0 itsKey = true := by decide +kernel
theorem chk_apre : chk MT_APRE 0 false 0 itsAcct = true := by decide +kernel
theorem chk_apost : chk MT_APOST 0 false 0 itsAcct = true := by decide +kernel
theorem chk_ah : chk MT_AH 0 false 0 itsAH = true := by decide +kernel
theorem chk_seed : chk MT_SEED 0 false 0 itsSeed = true := by decide +kernel
theorem chk_rid : chk MT_RID 0 false 0 itsRid = true := by decide +kernel
theorem chk_rref : chk MT_RREF 0 false 0 itsRRef = true := by decide +kernel
theorem chk_part : chk MT_PART 0 false 0 itsPart = true := by decide +kernel
theorem chk_log (i : Nat) (hi : i < MAX_LOGS) : chk (MT_LOG0 + i) 0 false 0 itsLog = true := by
  match i, hi with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel
theorem chk_leaf (n : Nat) (hn : n ≤ MAX_LOGS) :
    chk (MT_LEAF0 + n) 0 false 0 (itsLeaf n) = true := by
  match n, hn with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel
  | 4, _ => decide +kernel
/-- The receipt of `RL` from segment `1`; the last segment loops back to `1`. -/
theorem chk_rl : chk MT_RL 1 true 1 itsRL = true := by decide +kernel
/-- Segment `0` of `RL`: the u32 count, then segment `1` opens receipt family `mf + 1`. -/
theorem chk_rl0 : segIs MT_RL 0 (fun g => g.kind == K_CNT && !g.isLenP && !g.endOK &&
    g.nextS == 1 && newRAt MT_RL 1 == 1) = true := by decide +kernel

/-! ## The message types -/

section Msgs

variable {mf : Nat} {m : List Nat} {vs : List Visit}

/-- **`KEYR` / `KEYW`**: `m = kAccount recv` (`TrieKey::Account`), `recv` the `K_UV` visit. -/
theorem key_spec {mt : Nat} (hmt : mt = MT_KEYR ∨ mt = MT_KEYW) (h : IsMsg mt mf m vs) :
    ∃ recv, recv ≠ [] ∧ B8 recv ∧ vs = [⟨0, mf, [0]⟩, ⟨1, mf, recv⟩] ∧ m = 0 :: recv ∧
      toB m = kAccount (toB recv) := by
  have hc : chk mt 0 false 0 itsKey = true := by
    rcases hmt with rfl | rfl
    · exact chk_keyr
    · exact chk_keyw
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg hc h
  obtain ⟨b1, vals, rfl, h1, hv⟩ := vOKs_cons hv
  obtain ⟨b2, vals, rfl, h2, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at h1 h2
  subst h1
  refine ⟨b2, h2.1, h2.2, rfl, by simp [itsKey, tbytes, itBytes],
    by simp [itsKey, tbytes, itBytes, kAccount]⟩

/-- **`APRE` / `APOST`**: `m = Acct.encode` of a V1 account with a local contract whose amount,
locked, code hash and storage usage are the four visits. (A zero code hash encodes like
`Contract.none`.) -/
theorem acct_spec {mt : Nat} (hmt : mt = MT_APRE ∨ mt = MT_APOST) (h : IsMsg mt mf m vs) :
    ∃ a l c u, vs = [⟨0, mf, a⟩, ⟨1, mf, l⟩, ⟨2, mf, c⟩, ⟨3, mf, u⟩] ∧
      a.length = 16 ∧ l.length = 16 ∧ c.length = 32 ∧ u.length = 8 ∧
      B8 a ∧ B8 l ∧ B8 c ∧ B8 u ∧ m = a ++ l ++ c ++ u ∧
      toB m = Acct.encode ⟨leV a, leV l, leV u, .local (toB c), false⟩ := by
  have hc : chk mt 0 false 0 itsAcct = true := by
    rcases hmt with rfl | rfl
    · exact chk_apre
    · exact chk_apost
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg hc h
  obtain ⟨a, vals, rfl, ha, hv⟩ := vOKs_cons hv
  obtain ⟨l, vals, rfl, hl, hv⟩ := vOKs_cons hv
  obtain ⟨c, vals, rfl, hc, hv⟩ := vOKs_cons hv
  obtain ⟨u, vals, rfl, hu, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at ha hl hc hu
  refine ⟨a, l, c, u, rfl, ha.1, hl.1, hc.1, hu.1, ha.2, hl.2, hc.2, hu.2,
    by simp [itsAcct, tbytes, itBytes], ?_⟩
  simp only [itsAcct, tbytes, itBytes, toB_append, List.append_nil, Acct.encode, Bool.false_eq_true,
    ite_false, toB_u128 ha.2 ha.1, toB_u128 hl.2 hl.1, toB_u64 hu.2 hu.1, List.append_assoc]

/-- **`AH`**: the preimage of the action hash, `actionHash rid h 0 = sha256 m`. -/
theorem ah_spec (h : IsMsg MT_AH mf m vs) :
    ∃ rid hb, vs = [⟨0, mf, rid⟩, ⟨1, mf, hb⟩] ++ constVis 2 mf (leBytes (2 ^ 64 - 1) 8) ∧
      rid.length = 32 ∧ hb.length = 8 ∧ B8 rid ∧ B8 hb ∧
      m = rid ++ hb ++ leBytes (2 ^ 64 - 1) 8 ∧
      toB m = toB rid ++ u64 (leV hb) ++ u64 (2 ^ 64 - 1) ∧
      D3.actionHash (toB rid) (leV hb) 0 = sha256 (toB m) := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg chk_ah h
  obtain ⟨a, vals, rfl, ha, hv⟩ := vOKs_cons hv
  obtain ⟨b, vals, rfl, hb, hv⟩ := vOKs_cons hv
  obtain ⟨c, vals, rfl, hc, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at ha hb hc
  subst hc
  have e : toB (tbytes itsAH [a, b, leBytes (2 ^ 64 - 1) 8]) =
      toB a ++ u64 (leV b) ++ u64 (2 ^ 64 - 1) := by
    simp only [itsAH, tbytes, itBytes, toB_append, List.append_nil, toB_u64 hb.2 hb.1,
      toB_leBytes, List.append_assoc]; rfl
  refine ⟨a, b, rfl, ha.1, hb.1, ha.2, hb.2, by simp [itsAH, tbytes, itBytes], e, ?_⟩
  rw [e]; rfl

/-- **`SEED`**: `m = ah ‖ randomValue`, the preimage of the call's `randomSeed`. -/
theorem seed_spec (h : IsMsg MT_SEED mf m vs) :
    ∃ ah rv, vs = [⟨0, mf, ah⟩, ⟨1, mf, rv⟩] ∧ ah.length = 32 ∧ rv.length = 32 ∧ B8 ah ∧ B8 rv ∧
      m = ah ++ rv ∧ toB m = toB ah ++ toB rv := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg chk_seed h
  obtain ⟨a, vals, rfl, ha, hv⟩ := vOKs_cons hv
  obtain ⟨b, vals, rfl, hb, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at ha hb
  exact ⟨a, b, rfl, ha.1, hb.1, ha.2, hb.2, by simp [itsSeed, tbytes, itBytes],
    by simp [itsSeed, tbytes, itBytes]⟩

/-- **`RID`**: the preimage of the refund's receipt id, `receiptIdFrom rid h 0 = sha256 m`. -/
theorem rid_spec (h : IsMsg MT_RID mf m vs) :
    ∃ rid hb, vs = [⟨0, mf, rid⟩, ⟨1, mf, hb⟩] ++ constVis 2 mf (leBytes 0 8) ∧
      rid.length = 32 ∧ hb.length = 8 ∧ B8 rid ∧ B8 hb ∧
      m = rid ++ hb ++ leBytes 0 8 ∧ toB m = toB rid ++ u64 (leV hb) ++ u64 0 ∧
      receiptIdFrom (toB rid) (leV hb) 0 = sha256 (toB m) := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg chk_rid h
  obtain ⟨a, vals, rfl, ha, hv⟩ := vOKs_cons hv
  obtain ⟨b, vals, rfl, hb, hv⟩ := vOKs_cons hv
  obtain ⟨c, vals, rfl, hc, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at ha hb hc
  subst hc
  have e : toB (tbytes itsRid [a, b, leBytes 0 8]) = toB a ++ u64 (leV b) ++ u64 0 := by
    simp only [itsRid, tbytes, itBytes, toB_append, List.append_nil, toB_u64 hb.2 hb.1,
      toB_leBytes, List.append_assoc]; rfl
  refine ⟨a, b, rfl, ha.1, hb.1, ha.2, hb.2, by simp [itsRid, tbytes, itBytes], e, ?_⟩
  rw [e]; rfl

/-- **`LOGi`**: the message is the log's bytes (one `K_UV` visit). -/
theorem log_spec {i : Nat} (hi : i < MAX_LOGS) (h : IsMsg (MT_LOG0 + i) mf m vs) :
    m ≠ [] ∧ B8 m ∧ vs = [⟨0, mf, m⟩] := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg (chk_log i hi) h
  obtain ⟨a, vals, rfl, ha, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at ha
  simp only [itsLog, tbytes, itBytes, List.append_nil]
  exact ⟨ha.1, ha.2, rfl⟩

end Msgs


/-! ## `RREF`, `PART`, `LEAFn` -/

section Msgs2

variable {mf : Nat} {m : List Nat} {vs : List Visit}

theorem toB_u32b (v : Nat) : toB (u32b v) = u32 v := toB_leBytes v 4
theorem toB_systemId : toB systemId = AccountId.system := rfl
theorem borsh_system : borshBytes AccountId.system = u32 6 ++ AccountId.system := rfl
theorem toB_rrefC : toB rrefC = u128 0 ++ u32 0 ++ u32 0 ++ u32 1 ++ [3] := by decide
theorem toB_zero1 : toB [0] = [0] := rfl
theorem toB_two1 : toB [2] = [2] := rfl
theorem u8_zero : u8 0 = [0] := rfl

/-- **`RREF`**: `m = Rcpt.encode` of the gas-refund receipt `D2.refunds` builds
(`SpecLink.refundRcpt signer pk amount`: `pred = system`, an action receipt signed by the signer
with one `Transfer`) with `recv` the first signer visit and the receipt id the `RID` digest visit
(the id `emitReceipts` assigns, `receiptIdFrom parent h 0`, in place of `refundRcpt`'s
placeholder `zero32`). The signer key is ED25519 (tag `0`). -/
theorem rref_spec (h : IsMsg MT_RREF mf m vs) :
    ∃ s1 rid s2 pk amt,
      vs = constVis 0 mf (u32b 6 ++ systemId) ++ lpv 10 mf s1 ++ [⟨12, mf, rid⟩] ++
        constVis 13 mf [0] ++ lpv 14 mf s2 ++ constVis 16 mf [0] ++ [⟨17, mf, pk⟩] ++
        constVis 18 mf rrefC ++ [⟨47, mf, amt⟩] ∧
      s1.length < 2 ^ 24 ∧ s2.length < 2 ^ 24 ∧ rid.length = 32 ∧ pk.length = 32 ∧
      amt.length = 16 ∧ B8 s1 ∧ B8 s2 ∧ B8 rid ∧ B8 pk ∧ B8 amt ∧
      m = (u32b 6 ++ systemId) ++ lpB s1 ++ rid ++ [0] ++ lpB s2 ++ [0] ++ pk ++ rrefC ++ amt ∧
      toB m = Rcpt.encode { SpecLink.refundRcpt (toB s2) ⟨0, toB pk⟩ (leV amt) with
        recv := toB s1, rid := toB rid } ∧
      (s1 = s2 → toB m = Rcpt.encode { SpecLink.refundRcpt (toB s2) ⟨0, toB pk⟩ (leV amt) with
        rid := toB rid }) := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg chk_rref h
  obtain ⟨c1, vals, rfl, h1, hv⟩ := vOKs_cons hv
  obtain ⟨s1, vals, rfl, hs1, hv⟩ := vOKs_cons hv
  obtain ⟨rid, vals, rfl, hrid, hv⟩ := vOKs_cons hv
  obtain ⟨z1, vals, rfl, hz1, hv⟩ := vOKs_cons hv
  obtain ⟨s2, vals, rfl, hs2, hv⟩ := vOKs_cons hv
  obtain ⟨z2, vals, rfl, hz2, hv⟩ := vOKs_cons hv
  obtain ⟨pk, vals, rfl, hpk, hv⟩ := vOKs_cons hv
  obtain ⟨c2, vals, rfl, h2, hv⟩ := vOKs_cons hv
  obtain ⟨amt, vals, rfl, hamt, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at h1 hs1 hrid hz1 hs2 hz2 hpk h2 hamt
  subst h1 hz1 hz2 h2
  have e : toB (tbytes itsRRef [u32b 6 ++ systemId, s1, rid, [0], s2, [0], pk, rrefC, amt]) =
      Rcpt.encode { SpecLink.refundRcpt (toB s2) ⟨0, toB pk⟩ (leV amt) with
        recv := toB s1, rid := toB rid } := by
    simp only [itsRRef, tbytes, itBytes, toB_append, List.append_nil, toB_lpB, toB_u32b,
      toB_systemId, borsh_system, toB_rrefC, toB_zero1, toB_u128 hamt.2 hamt.1,
      SpecLink.refundRcpt, Rcpt.encode, RBody.encode, ActionR.encode, Bool.false_eq_true,
      ite_false, PublicKey.encode, u8_zero, List.length_nil, concatAll, List.append_assoc,
      Act.raw, List.map_nil, List.map_cons, List.length_singleton]
  refine ⟨s1, rid, s2, pk, amt, ?_, hs1.1, hs2.1, hrid.1, hpk.1, hamt.1, hs1.2, hs2.2, hrid.2,
    hpk.2, hamt.2, ?_, e, fun h12 => ?_⟩
  · simp only [List.append_assoc]; rfl
  · simp only [itsRRef, tbytes, itBytes, List.append_nil, List.append_assoc]
  · rw [e, ← h12]; rfl

/-- **`PART`**: `m = OutD1.partialEncode` of an outcome with one receipt id (the `RID` digest),
gas / tokens burnt, executor `recv` and status `SuccessValue ret` (for any outcome id and logs,
which `partialEncode` does not cover). An empty return value ends the message after its zero
length prefix (`skipEnd`); `SuccessValue []` encodes like `OStatus.value`. -/
theorem part_spec (h : IsMsg MT_PART mf m vs) :
    ∃ rid gb tb recv ret,
      vs = constVis 0 mf (u32b 1) ++ [⟨4, mf, rid⟩, ⟨5, mf, gb⟩, ⟨6, mf, tb⟩] ++ lpv 7 mf recv ++
        constVis 9 mf [2] ++ lpv 10 mf ret ∧
      rid.length = 32 ∧ gb.length = 8 ∧ tb.length = 16 ∧ recv.length < 2 ^ 24 ∧
      ret.length < 2 ^ 24 ∧ B8 rid ∧ B8 gb ∧ B8 tb ∧ B8 recv ∧ B8 ret ∧
      m = u32b 1 ++ rid ++ gb ++ tb ++ lpB recv ++ [2] ++ lpB ret ∧
      ∀ (id : Bytes) (logs : List Bytes),
        toB m = OutD1.partialEncode
          { o := { id, receiptIds := [toB rid], gasBurnt := leV gb, tokensBurnt := leV tb,
                   executorId := toB recv },
            status := .valueBytes (toB ret), logs } := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg chk_part h
  obtain ⟨c1, vals, rfl, h1, hv⟩ := vOKs_cons hv
  obtain ⟨rid, vals, rfl, hrid, hv⟩ := vOKs_cons hv
  obtain ⟨gb, vals, rfl, hgb, hv⟩ := vOKs_cons hv
  obtain ⟨tb, vals, rfl, htb, hv⟩ := vOKs_cons hv
  obtain ⟨recv, vals, rfl, hrecv, hv⟩ := vOKs_cons hv
  obtain ⟨c2, vals, rfl, h2, hv⟩ := vOKs_cons hv
  obtain ⟨ret, vals, rfl, hret, hv⟩ := vOKs_cons hv
  obtain rfl := vOKs_nil hv
  simp only [vOK] at h1 hrid hgb htb hrecv h2 hret
  subst h1 h2
  refine ⟨rid, gb, tb, recv, ret, ?_, hrid.1, hgb.1, htb.1, hrecv.1, hret.1, hrid.2, hgb.2,
    htb.2, hrecv.2, hret.2, ?_, fun id logs => ?_⟩
  · rw [← List.append_nil (lpv 10 mf ret)]
    simp only [List.append_assoc]; rfl
  · simp only [itsPart, tbytes, itBytes, List.append_nil, List.append_assoc]
  · simp only [itsPart, tbytes, itBytes, toB_append, List.append_nil, toB_lpB, toB_two1, u32b,
      toB_leBytes, toB_u64 hgb.2 hgb.1, toB_u128 htb.2 htb.1, OutD1.partialEncode,
      OStatus.encode, List.length_cons, List.length_nil, concatAll, List.append_assoc,
      borshBytes, toB_length]
    rfl

theorem pe_empty : OStatus.encode (.valueBytes []) = OStatus.encode .value := rfl

/-- The visits of `n` digests from segment `s`. -/
def digVis (s f : Nat) : List (List Nat) → List Visit
  | [] => []
  | d :: ds => ⟨s, f, d⟩ :: digVis (s + 1) f ds

theorem rep_vOKs {L : Nat} : ∀ {n : Nat} {ds : List (List Nat)},
    vOKs (List.replicate n (.fx L)) ds → ds.length = n ∧ ∀ d ∈ ds, d.length = L ∧ B8 d
  | 0, ds, h => by rw [vOKs_nil h]; simp
  | n + 1, ds, h => by
    obtain ⟨d, ds, rfl, hd, h⟩ := vOKs_cons h
    obtain ⟨h1, h2⟩ := rep_vOKs h
    refine ⟨by simp [h1], ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hd
    · exact h2 x hx

theorem rep_tvis {L : Nat} : ∀ {n s f : Nat} {ds : List (List Nat)}, ds.length = n →
    tvis s f (List.replicate n (.fx L)) ds = digVis s f ds
  | 0, s, f, [], _ => rfl
  | n + 1, s, f, d :: ds, h => by
    simp only [List.replicate_succ, tvis, itVis, It.w, digVis, List.cons_append, List.nil_append]
    rw [rep_tvis (by simpa using h)]

theorem rep_tbytes {L : Nat} : ∀ {n : Nat} {ds : List (List Nat)}, ds.length = n →
    tbytes (List.replicate n (.fx L)) ds = ds.flatten
  | 0, [], _ => rfl
  | n + 1, d :: ds, h => by
    simp only [List.replicate_succ, tbytes, itBytes, List.flatten_cons]
    rw [rep_tbytes (by simpa using h)]

/-- **`LEAFn`** (`n ≤ 4` logs): `m = leafN ‖ id ‖ d_partial ‖ d_log₁ ‖ … ‖ d_logₙ`, the preimage
`OutD1.leaf` hashes (see `leaf_link`). -/
theorem leaf_spec {n : Nat} (hn : n ≤ MAX_LOGS) (h : IsMsg (MT_LEAF0 + n) mf m vs) :
    ∃ ln rid dp ds, ds.length = n ∧ (∀ d ∈ ds, d.length = 32 ∧ B8 d) ∧
      ln.length = 4 ∧ rid.length = 32 ∧ dp.length = 32 ∧ B8 ln ∧ B8 rid ∧ B8 dp ∧
      vs = [⟨0, mf, ln⟩, ⟨1, mf, rid⟩, ⟨2, mf, dp⟩] ++ digVis 3 mf ds ∧
      m = ln ++ rid ++ dp ++ ds.flatten := by
  obtain ⟨vals, hv, rfl, rfl⟩ := tmpl_msg (chk_leaf n hn) h
  obtain ⟨ln, vals, rfl, hln, hv⟩ := vOKs_cons hv
  obtain ⟨rid, vals, rfl, hrid, hv⟩ := vOKs_cons hv
  obtain ⟨dp, ds, rfl, hdp, hv⟩ := vOKs_cons hv
  simp only [vOK] at hln hrid hdp
  obtain ⟨hl, hds⟩ := rep_vOKs hv
  refine ⟨ln, rid, dp, ds, hl, hds, hln.1, hrid.1, hdp.1, hln.2, hrid.2, hdp.2, ?_, ?_⟩
  · show itVis 0 mf (.fx 4) ln ++ (itVis 1 mf (.fx 32) rid ++ (itVis 2 mf (.fx 32) dp ++
      tvis 3 mf (List.replicate n (.fx 32)) ds)) = _
    rw [rep_tvis hl]; rfl
  · show itBytes (.fx 4) ln ++ (itBytes (.fx 32) rid ++ (itBytes (.fx 32) dp ++
      tbytes (List.replicate n (.fx 32)) ds)) = _
    rw [rep_tbytes hl]; simp [itBytes, List.append_assoc]

/-- The link of `LEAFn` to `OutD1.leaf`: when the fields carry the outcome's values (the
`2 + n` count, the outcome id, the digest of its `partialEncode`, the digests of its `n` logs),
`OutD1.leaf` is the digest of the message. -/
theorem leaf_link (x : OutD1) (ln rid dp : List Nat) (ds : List (List Nat))
    (hln : toB ln = u32 (2 + ds.length)) (hid : toB rid = x.o.id)
    (hdp : toB dp = sha256 x.partialEncode) (hds : ds.map toB = x.logs.map sha256) :
    OutD1.leaf x = sha256 (toB (ln ++ rid ++ dp ++ ds.flatten)) := by
  simp only [toB_append, toB_flatten, hln, hid, hdp, hds]
  unfold OutD1.leaf
  cases hl : x.logs with
  | nil =>
    have : ds = [] := by
      have := congrArg List.length hds; rw [hl] at this; simpa using this
    subst this
    simp [concatAll]
  | cons l ls =>
    have : ds.length = (l :: ls).length := by
      have := congrArg List.length hds; rw [hl] at this; simpa using this
    simp only [this, List.append_assoc]

end Msgs2

/-! ## `RL`: the receipt list -/

/-- The fields of one receipt of `RL` (bytes as the engine holds them). -/
structure FC where
  pred : List Nat
  recv : List Nat
  rid : List Nat
  signer : List Nat
  pk : List Nat
  gp : List Nat
  meth : List Nat
  args : List Nat
  gas : List Nat
  dep : List Nat
  deriving Repr, DecidableEq

def FC.vals (x : FC) : List (List Nat) :=
  [x.pred, x.recv, x.rid, [0], x.signer, [0], x.pk, x.gp, rlC, x.meth, x.args, x.gas, x.dep]

/-- Field widths and byte ranges. -/
def FC.wf (x : FC) : Prop :=
  x.pred.length < 2 ^ 24 ∧ B8 x.pred ∧ x.recv.length < 2 ^ 24 ∧ B8 x.recv ∧
  x.rid.length = 32 ∧ B8 x.rid ∧ x.signer.length < 2 ^ 24 ∧ B8 x.signer ∧
  x.pk.length = 32 ∧ B8 x.pk ∧ x.gp.length = 16 ∧ B8 x.gp ∧
  x.meth.length < 2 ^ 24 ∧ B8 x.meth ∧ x.args.length < 2 ^ 24 ∧ B8 x.args ∧
  x.gas.length = 8 ∧ B8 x.gas ∧ x.dep.length = 16 ∧ B8 x.dep

/-- The raw bytes of a `FunctionCall` action (`Act.raw`): `2 ‖ borsh method ‖ borsh args ‖ u64 gas
‖ u128 deposit`. -/
def fcRaw (m a : Bytes) (g d : Nat) : Bytes :=
  [2] ++ borshBytes m ++ borshBytes a ++ u64 g ++ u128 d

/-- **The template shape** the constant bytes of `RL` force: a V1 action receipt, not a yield,
signer key ED25519, no output data receivers, no input data ids, one `FunctionCall` action whose
raw bytes are its borsh. -/
def FcShape (r : Rcpt) : Prop :=
  ∃ (pred recv rid signer pk : Bytes) (gp : Nat) (m a : Bytes) (g d : Nat),
    r = ⟨pred, recv, rid, .action false ⟨false, signer, none, ⟨0, pk⟩, gp, [], [],
      [.base ⟨fcRaw m a g d, .fcall m a g d⟩]⟩⟩ ∧
    rid.length = 32 ∧ pk.length = 32 ∧ gp < 2 ^ 128 ∧ g < 2 ^ 64 ∧ d < 2 ^ 128 ∧
    pred.length < 2 ^ 24 ∧ recv.length < 2 ^ 24 ∧ signer.length < 2 ^ 24 ∧
    m.length < 2 ^ 24 ∧ a.length < 2 ^ 24

/-- The spec receipt of the fields. -/
def FC.toRcpt (x : FC) : Rcpt :=
  ⟨toB x.pred, toB x.recv, toB x.rid, .action false ⟨false, toB x.signer, none, ⟨0, toB x.pk⟩,
    leV x.gp, [], [], [.base ⟨fcRaw (toB x.meth) (toB x.args) (leV x.gas) (leV x.dep),
      .fcall (toB x.meth) (toB x.args) (leV x.gas) (leV x.dep)⟩]⟩⟩

/-- The visits of one receipt of `RL` in family `f` (segments `1 … 30`; a length prefix of `0`
has no field visit). -/
def fcVisits (f : Nat) (x : FC) : List Visit :=
  lpv 1 f x.pred ++ lpv 3 f x.recv ++ [⟨5, f, x.rid⟩] ++ constVis 6 f [0] ++ lpv 7 f x.signer ++
    constVis 9 f [0] ++ [⟨10, f, x.pk⟩, ⟨11, f, x.gp⟩] ++ constVis 12 f rlC ++
    lpv 25 f x.meth ++ lpv 27 f x.args ++ [⟨29, f, x.gas⟩, ⟨30, f, x.dep⟩]

/-- The visits of receipts `xs`, receipt `i` in family `f + i`. -/
def fcVis (f : Nat) : List FC → List Visit
  | [] => []
  | x :: xs => fcVisits f x ++ fcVis (f + 1) xs

theorem fcVisits_eq (f : Nat) (x : FC) : tvis 1 f itsRL x.vals = fcVisits f x := by
  simp only [fcVisits, List.append_assoc]; rfl

theorem vals_fc {vals : List (List Nat)} (h : vOKs itsRL vals) : ∃ x : FC, vals = x.vals ∧ x.wf := by
  obtain ⟨pred, vals, rfl, h1, h⟩ := vOKs_cons h
  obtain ⟨recv, vals, rfl, h2, h⟩ := vOKs_cons h
  obtain ⟨rid, vals, rfl, h3, h⟩ := vOKs_cons h
  obtain ⟨z1, vals, rfl, h4, h⟩ := vOKs_cons h
  obtain ⟨signer, vals, rfl, h5, h⟩ := vOKs_cons h
  obtain ⟨z2, vals, rfl, h6, h⟩ := vOKs_cons h
  obtain ⟨pk, vals, rfl, h7, h⟩ := vOKs_cons h
  obtain ⟨gp, vals, rfl, h8, h⟩ := vOKs_cons h
  obtain ⟨c, vals, rfl, h9, h⟩ := vOKs_cons h
  obtain ⟨meth, vals, rfl, h10, h⟩ := vOKs_cons h
  obtain ⟨args, vals, rfl, h11, h⟩ := vOKs_cons h
  obtain ⟨gas, vals, rfl, h12, h⟩ := vOKs_cons h
  obtain ⟨dep, vals, rfl, h13, h⟩ := vOKs_cons h
  obtain rfl := vOKs_nil h
  simp only [vOK] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h4 h6 h9
  exact ⟨⟨pred, recv, rid, signer, pk, gp, meth, args, gas, dep⟩, rfl,
    h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2, h7.1, h7.2, h8.1, h8.2, h10.1, h10.2,
    h11.1, h11.2, h12.1, h12.2, h13.1, h13.2⟩

theorem toB_rlC : toB rlC = u32 0 ++ u32 0 ++ u32 1 ++ [2] := by decide

/-- The bytes of one receipt are `Rcpt.encode` of its spec receipt. -/
theorem fc_encode (x : FC) (hx : x.wf) : toB (vbytes (fcVisits 0 x)) = Rcpt.encode x.toRcpt := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hgp, hgp8, _, _, _, _, hg, hg8, hd, hd8⟩ := hx
  rw [← fcVisits_eq, vbytes_tvis]
  simp only [FC.vals, itsRL, tbytes, itBytes, toB_append, List.append_nil, toB_lpB, toB_zero1,
    toB_rlC, toB_u128 hgp8 hgp, toB_u64 hg8 hg, toB_u128 hd8 hd, FC.toRcpt, fcRaw, Rcpt.encode,
    RBody.encode, ActionR.encode, Bool.false_eq_true, ite_false, PublicKey.encode, u8_zero,
    List.length_nil, List.length_cons, concatAll, List.append_assoc, Act.raw,
    List.map_cons, List.map_nil, Nat.zero_add]

theorem vbytes_fcVisits (f g : Nat) (x : FC) : vbytes (fcVisits f x) = vbytes (fcVisits g x) := by
  rw [← fcVisits_eq, ← fcVisits_eq, vbytes_tvis, vbytes_tvis]

theorem fc_shape (x : FC) (hx : x.wf) : FcShape x.toRcpt := by
  obtain ⟨hp, _, hr, _, hid, _, hs, _, hk, _, hgp, hgp8, hm, _, ha, _, hg, hg8, hd, hd8⟩ := hx
  have e16 : (256 : Nat) ^ 16 = 2 ^ 128 := by decide
  have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have l1 := leV_lt x.gp hgp8; have l2 := leV_lt x.gas hg8; have l3 := leV_lt x.dep hd8
  rw [hgp, e16] at l1; rw [hg, e8] at l2; rw [hd, e16] at l3
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simpa using hid, by simpa using hk, l1, l2, l3,
    by simpa using hp, by simpa using hr, by simpa using hs, by simpa using hm, by simpa using ha⟩

theorem rl_blocks : ∀ (k f : Nat) (vs : List Visit), vs.length ≤ k → Walk MT_RL 1 f none vs →
    ∃ xs : List FC, xs ≠ [] ∧ (∀ x ∈ xs, x.wf) ∧ vs = fcVis f xs := by
  intro k
  induction k with
  | zero =>
    intro f vs hl hw
    have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact absurd this (walk_ne_nil hw)
  | succ k ih =>
    intro f vs hl hw
    obtain ⟨vals, rest, hv, rfl, ht⟩ := tmpl_walk chk_rl hw
    obtain ⟨x, rfl, hx⟩ := vals_fc hv
    rw [fcVisits_eq] at hl ⊢
    rcases ht with rfl | ⟨_, hw'⟩
    · exact ⟨[x], by simp, by simpa using hx, by simp [fcVis]⟩
    · have hpos : 1 ≤ (fcVisits f x).length := by simp [fcVisits, lpv]
      have hl' : rest.length ≤ k := by simp at hl; omega
      obtain ⟨xs, _, hxs, rfl⟩ := ih (f + 1) rest hl' hw'
      refine ⟨x :: xs, by simp, ?_, rfl⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hxs y hy

theorem vbytes_fcVis : ∀ (f : Nat) (xs : List FC), (∀ x ∈ xs, x.wf) →
    toB (vbytes (fcVis f xs)) = concatAll (xs.map fun x => Rcpt.encode x.toRcpt)
  | _, [], _ => rfl
  | f, x :: xs, h => by
    simp only [fcVis, vbytes_append, toB_append, List.map_cons, concatAll]
    rw [vbytes_fcVisits f 0, fc_encode x (h x (by simp)),
      vbytes_fcVis (f + 1) xs (fun y hy => h y (by simp [hy]))]

/-- **`RL`** (`encodeRcpts`): the message is a u32 count followed by one or more receipts of the
template shape; receipt `i` is family `mf + 1 + i` and its fields are its visits (`fcVisits`).
When the count is the number of receipts, the bytes are `encodeRcpts`. -/
theorem rl_spec {mf : Nat} {m : List Nat} {vs : List Visit} (h : IsMsg MT_RL mf m vs) :
    ∃ (cnt : List Nat) (xs : List FC), xs ≠ [] ∧ (∀ x ∈ xs, x.wf ∧ FcShape x.toRcpt) ∧
      cnt.length = 4 ∧ B8 cnt ∧ leV cnt < 2 ^ 24 ∧
      vs = ⟨0, mf, cnt⟩ :: fcVis (mf + 1) xs ∧
      toB m = u32 (leV cnt) ++ concatAll (xs.map fun x => Rcpt.encode x.toRcpt) ∧
      (leV cnt = xs.length → toB m = encodeRcpts (xs.map FC.toRcpt)) := by
  obtain ⟨g, hs, hp⟩ := segIs_spec chk_rl0
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨⟨hk, hlp⟩, he⟩, hn⟩, hr⟩ := hp
  obtain ⟨cnt, vs', hv, rfl, hw⟩ := stepMid h.1 hs hlp he
  rw [hn, hr] at hw
  have hlen : g.isLen = true := by simp [Seg.isLen, hk]
  obtain ⟨hcnt, hlt, _⟩ := len_visit hv hlen
  obtain ⟨xs, hne, hxs, rfl⟩ := rl_blocks _ _ _ (Nat.le_refl _) hw
  have hm : toB m = u32 (leV cnt) ++ concatAll (xs.map fun x => Rcpt.encode x.toRcpt) := by
    rw [← h.2]
    show toB (cnt ++ vbytes (fcVis (mf + 1) xs)) = _
    rw [toB_append, hcnt, vbytes_fcVis _ _ hxs]
  refine ⟨cnt, xs, hne, fun x hx => ⟨hxs x hx, fc_shape x (hxs x hx)⟩,
    (hv.len hlen).1, hv.bytes, hlt, rfl, hm, fun hc => ?_⟩
  rw [hm, hc, encodeRcpts, List.length_map, List.map_map]
  rfl

/-! ## Non-vacuity: concrete walks -/

/-- `VisitOK` as a Boolean (no pending length). -/
def visitB (g : Seg) (bs : List Nat) : Bool :=
  bs.all (· < 256) && 0 < bs.length && (g.kind != K_C || bs == [g.cv]) &&
    (!g.isLen || (bs.length == 4 && bs.getLast? == some 0)) && (g.var || bs.length == g.fixL) &&
    g.kind != K_PAD

theorem visitOK_of {g : Seg} {bs : List Nat} (h : visitB g bs = true) : VisitOK g none bs := by
  simp only [visitB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun hk => ?_, fun hk => ?_, fun hv => ?_, (fun _ _ n hn => by cases hn), h6⟩
  · rcases h3 with h3 | h3
    · exact absurd hk h3
    · exact h3
  · rcases h4 with h4 | h4
    · rw [hk] at h4; cases h4
    · exact h4
  · rcases h5 with h5 | h5
    · rw [hv] at h5; cases h5
    · exact h5

theorem walk_cons_none {mt s qf s' qf' : Nat} {g : Seg} {bs : List Nat} {vs : List Visit}
    (hs : segAt mt s = some g) (hv : visitB g bs = true)
    (hc : (g.cont && !(zOf g bs && g.skipEnd)) = true)
    (hn : nextSeg g bs = s') (hq : qf + newRAt mt s' = qf') (hp : nextPl g bs = none)
    (hw : Walk mt s' qf' none vs) : Walk mt s qf none (⟨s, qf, bs⟩ :: vs) := by
  subst hn hq
  refine Walk.cons hs (visitOK_of hv) ?_ (hp ▸ hw)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  exact hc

theorem walk_last_none {mt s qf : Nat} {g : Seg} {bs : List Nat}
    (hs : segAt mt s = some g) (hv : visitB g bs = true)
    (he : (b2n g.endOK + b2n (zOf g bs && g.skipEnd) == 1) = true) :
    Walk mt s qf none [⟨s, qf, bs⟩] :=
  Walk.last hs (visitOK_of hv) (by simpa [EndOK] using he)

/-- A placeholder segment (never used: every `segAt` below is `some`). -/
def seg0 : Seg := { mt := 0, s := 0, kind := 0 }

/-- A concrete `KEYR` message of family `1` for the account `"ab"`. -/
example : IsMsg MT_KEYR 1 [0, 97, 98] [⟨0, 1, [0]⟩, ⟨1, 1, [97, 98]⟩] := by
  refine ⟨?_, rfl⟩
  refine walk_cons_none (g := (segAt MT_KEYR 0).getD seg0) (s' := 1) (qf' := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  exact walk_last_none (g := (segAt MT_KEYR 1).getD seg0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A concrete `APRE` message of family `1`: amount 1, locked 0, code hash `7^32`, usage 100. -/
example : IsMsg MT_APRE 1 (leBytes 1 16 ++ leBytes 0 16 ++ List.replicate 32 7 ++ leBytes 100 8)
    [⟨0, 1, leBytes 1 16⟩, ⟨1, 1, leBytes 0 16⟩, ⟨2, 1, List.replicate 32 7⟩,
     ⟨3, 1, leBytes 100 8⟩] := by
  refine ⟨?_, by decide⟩
  refine walk_cons_none (g := (segAt MT_APRE 0).getD seg0) (s' := 1) (qf' := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  refine walk_cons_none (g := (segAt MT_APRE 1).getD seg0) (s' := 2) (qf' := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  refine walk_cons_none (g := (segAt MT_APRE 2).getD seg0) (s' := 3) (qf' := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_
  exact walk_last_none (g := (segAt MT_APRE 3).getD seg0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end M5T1.MsgSpec

#print axioms M5T1.MsgSpec.tmpl_walk
#print axioms M5T1.MsgSpec.rl_spec
#print axioms M5T1.MsgSpec.key_spec
#print axioms M5T1.MsgSpec.acct_spec
#print axioms M5T1.MsgSpec.ah_spec
#print axioms M5T1.MsgSpec.seed_spec
#print axioms M5T1.MsgSpec.rid_spec
#print axioms M5T1.MsgSpec.rref_spec
#print axioms M5T1.MsgSpec.log_spec
#print axioms M5T1.MsgSpec.part_spec
#print axioms M5T1.MsgSpec.leaf_spec
#print axioms M5T1.MsgSpec.leaf_link
