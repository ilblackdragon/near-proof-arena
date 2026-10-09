import ZkFormal.NearV3.Extract.UniqProof
import ZkFormal.NearV3.Spec.Rank

/-!
# ZkFormal.NearV3.Link.Uniq — `uniqV3` view ⇒ weak uniqueness ⇒ hash-functional stores

The trace-free link step for `uniqV3`.  Inputs:
* the view `UniqWf es` (`uniq_view`);
* the byte-equality the `DUP` messages carry: for every entry with `eq = 1`, the message
  bytes `B eid` of the entry equal those of its predecessor (`nodeV3` receives
  `DUP (eid, peid)` exactly on duplicate entries and copies their bytes over `ENT`);
* digest bytes are bytes (`< 256`, from the SHA contract) and instance numbers are small
  (no wrap of `τ + st` modulo `p`; `τ ≤ K` from the `ROOT` chain).

Output (`uniq_functional`): two entries with the same instance and the same digest carry
the same message bytes.  `storeOf_hashFunctional` then gives `HashFunctional` for any
store whose entries are message bytes of `uniq` entries of instance `τ` whose digest
bytes are the SHA-256 of those message bytes — exactly what `storeBuildR` consumes.
-/

namespace ZkFormal.NearV3

open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Sort key of an entry: `τ` above the little-endian digest. -/
def ukey (e : UniqE) : Nat := e.tau * 2 ^ 256 + le256 e.bytes

theorem le256_lt : ∀ (l : List Nat), (∀ y ∈ l, y < 256) → le256 l < 256 ^ l.length
  | [], _ => by simp [le256]
  | y :: l, h => by
    have hy := h y (by simp)
    have ih := le256_lt l (fun z hz => h z (by simp [hz]))
    simp only [le256, List.length_cons, Nat.pow_succ]
    have : 256 * le256 l + 256 ≤ 256 ^ l.length * 256 := by
      rw [Nat.mul_comm (256 ^ l.length)]; exact Nat.mul_le_mul_left _ ih
    omega

theorem le256_lt32 {l : List Nat} (hl : l.length = 32) (h : ∀ y ∈ l, y < 256) : le256 l < 2 ^ 256 := by
  have := le256_lt l h
  rw [hl] at this
  have e : (256 : Nat) ^ 32 = 2 ^ 256 := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  omega

theorem ukey_inj {a b : UniqE} (ha : a.bytes.length = 32) (hb : b.bytes.length = 32)
    (ha' : ∀ y ∈ a.bytes, y < 256) (hb' : ∀ y ∈ b.bytes, y < 256) :
    ukey a = ukey b ↔ a.tau = b.tau ∧ le256 a.bytes = le256 b.bytes := by
  have h1 := le256_lt32 ha ha'
  have h2 := le256_lt32 hb hb'
  unfold ukey
  constructor
  · intro h
    have e1 : (a.tau * 2 ^ 256 + le256 a.bytes) / 2 ^ 256 = a.tau := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt h1]; simp
    have e2 : (b.tau * 2 ^ 256 + le256 b.bytes) / 2 ^ 256 = b.tau := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 256), Nat.div_eq_of_lt h2]; simp
    have ht : a.tau = b.tau := by rw [← e1, ← e2, h]
    refine ⟨ht, ?_⟩
    rw [ht] at h; omega
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- **Weak uniqueness from the `uniqV3` view.** -/
theorem uniq_weak (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) (htau : ∀ e ∈ es, e.tau + 1 < P) :
    WeakUniq ukey (fun e => B e.eid) es := by
  have step : ∀ t (ht : t + 1 < es.length), WeakStep ukey (fun e => B e.eid) es[t] es[t + 1] := by
    intro t ht
    have h0 : es[t] ∈ es := List.getElem_mem (by omega)
    have h1 : es[t + 1] ∈ es := List.getElem_mem ht
    obtain ⟨hpe, hta, heq1, heq0⟩ := hwf.link t ht
    obtain ⟨-, -, hT0, -, -, -⟩ := hwf.canon _ h0
    obtain ⟨-, -, -, hst, heqb, -⟩ := hwf.canon _ h1
    have hl0 := hwf.len _ h0
    have hl1 := hwf.len _ h1
    have hb0 := hbytes _ h0
    have hb1 := hbytes _ h1
    have hlt0 := le256_lt32 hl0 hb0
    have hlt1 := le256_lt32 hl1 hb1
    have hbb : ∀ y ∈ es[t].bytes ++ es[t + 1].bytes, y < 256 := by
      intro y hy; rcases List.mem_append.1 hy with hy | hy
      · exact hb0 y hy
      · exact hb1 y hy
    have hw := htau _ h0
    unfold WeakStep ukey
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hst with hs | hs
    · -- same instance
      simp only [hs, Nat.add_zero, Nat.mod_eq_of_lt hT0] at hta
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 heqb with he | he
      · left; rw [hta]; have := heq0 he hs hbb; omega
      · right
        have hbe := (heq1 he).2 hbb
        refine ⟨by rw [hta, hbe], (hdup t ht he).symm⟩
    · -- next instance
      simp only [hs] at hta
      rw [Nat.mod_eq_of_lt (by omega)] at hta
      left; rw [hta, Nat.add_mul, Nat.one_mul]; omega
  -- assemble the chain
  have key : ∀ (l : List UniqE), (∀ t (ht : t + 1 < l.length), WeakStep ukey (fun e => B e.eid) l[t] l[t + 1]) →
      WeakUniq ukey (fun e => B e.eid) l := by
    intro l
    induction l with
    | nil => intro _; trivial
    | cons a l ih =>
      intro h
      cases l with
      | nil => trivial
      | cons b r =>
        exact ⟨h 0 (by simp), ih (fun t ht => h (t + 1) (by simp at ht ⊢; omega))⟩
  exact key es step

/-- **Equal instance and digest ⇒ equal message bytes.** -/
theorem uniq_functional (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) (htau : ∀ e ∈ es, e.tau + 1 < P) :
    ∀ e ∈ es, ∀ e' ∈ es, e.tau = e'.tau → e.bytes = e'.bytes → B e.eid = B e'.eid := by
  intro e he e' he' ht hb
  exact weakUniq_functional (uniq_weak es hwf B hdup hbytes htau) e he e' he'
    ((ukey_inj (hwf.len e he) (hwf.len e' he') (hbytes e he) (hbytes e' he')).2 ⟨ht, by rw [hb]⟩)

/-- Digest bytes of a byte string, as `uniq` stores them (`i`-th byte at position `i`). -/
def digNat (b : Bytes) : List Nat := (sha256 b).map UInt8.toNat

/-- **A store covered by `uniq` entries is hash-functional.** Every entry of the store `st`
is the message `B eid` of some `uniq` entry of instance `τ` whose digest bytes are
`sha256 (B eid)`. -/
theorem storeOf_hashFunctional (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) (htau : ∀ e ∈ es, e.tau + 1 < P)
    (τ : Nat) (st : List Bytes)
    (hcov : ∀ x ∈ st, ∃ e ∈ es, e.tau = τ ∧ B e.eid = x ∧ e.bytes = digNat x) : HashFunctional st := by
  intro x hx y hy hxy
  obtain ⟨e, he, het, hex, heb⟩ := hcov x hx
  obtain ⟨e', he', het', hey, heb'⟩ := hcov y hy
  rw [← hex, ← hey]
  apply uniq_functional es hwf B hdup hbytes htau e he e' he' (by rw [het, het'])
  rw [heb, heb', digNat, digNat, hxy]

end ZkFormal.NearV3
