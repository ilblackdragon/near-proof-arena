import NearSpecV3.Wasm.FuelDefs
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm
open Classical

/-- Cost of positions `a, a+1, …, a+len-1`. -/
def cs (pf : PFunc) (a : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (match pf.code[a]? with | some i => costOf i | none => 0) + cs pf (a + 1) len

/-- What the semantic half needs from the table: a set of group starts. -/
structure GT (cfg : NearCfg) (pf : PFunc) (enc : Nat → List Nat) (start : Nat → Prop) : Prop where
  start0 : start 0
  startN : start pf.code.size
  entry : ∀ a e, pf.gas[a]? = some (some e) → start a
  fee : ∀ s k fee len, pf.gas[s]? = some (some (k, fee)) → s + len ≤ pf.code.size →
    (∀ t, s < t → t < s + len → ¬ start t) → cfg.regularOpCost * cs pf s len ≤ fee.c
  zero : ∀ s len, start s → Live pf enc s → (∀ e, pf.gas[s]? ≠ some (some e)) →
    s + len ≤ pf.code.size → (∀ t, s < t → t < s + len → ¬ start t) → cs pf s len = 0
  jump : ∀ pc q, Live pf enc pc → Succ pf enc pc q true → start q
  ret : ∀ pc i, Live pf enc pc → pf.code[pc]? = some i → isCallI i = true → start (pc + 1)

theorem req_ge (pf : PFunc) (a : Nat) (h : pf.code.size ≤ a) : req pf a = 0 := by
  unfold req; rw [show pf.code.size - a = 0 by omega]; rfl

theorem req_lt (pf : PFunc) (a : Nat) (h : a < pf.code.size) :
    req pf a = match pf.gas[a]? with
      | some (some _) => 0
      | _ => match pf.code[a]? with
        | none => 0
        | some i => costOf i + (if fallsThrough i then req pf (a + 1) else 0) := by
  unfold req
  rw [show pf.code.size - a = (pf.code.size - (a + 1)) + 1 by omega]
  rfl

theorem req_entry (pf : PFunc) (a : Nat) (e : IK × Fee) (h : pf.gas[a]? = some (some e)) :
    req pf a = 0 := by
  by_cases ha : a < pf.code.size
  · rw [req_lt pf a ha]; simp [h]
  · exact req_ge pf a (by omega)

theorem req_cons (pf : PFunc) (a : Nat) (i : Instr) (hc : pf.code[a]? = some i)
    (hg : ∀ e, pf.gas[a]? ≠ some (some e)) :
    req pf a = costOf i + (if fallsThrough i then req pf (a + 1) else 0) := by
  have ha : a < pf.code.size := by
    rcases Nat.lt_or_ge a pf.code.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hc
  rw [req_lt pf a ha]
  split
  · rename_i e he; exact absurd he (hg _)
  · simp [hc]

theorem live_fall {pf : PFunc} {enc : Nat → List Nat} (hn : NestOK pf enc) {a : Nat} {i : Instr}
    (hl : Live pf enc a) (hc : pf.code[a]? = some i) (hf : fallsThrough i = true) :
    Live pf enc (a + 1) ∨ a + 1 = pf.code.size := by
  by_cases he : i = .end_ ∧ enc a = []
  · right; obtain ⟨rfl, h2⟩ := he; exact (hn.end_ a hc).1 h2
  · left
    exact Live.step a (a + 1) false hl (Succ.fall a i hc hf (fun h1 h2 => he ⟨h1, h2⟩))

theorem exists_next (start : Nat → Prop) (n : Nat) (hn : start n) :
    ∀ d a, a + d = n → 0 < d → ∃ len, 1 ≤ len ∧ a + len ≤ n ∧ start (a + len) ∧
      ∀ t, a < t → t < a + len → ¬ start t := by
  intro d
  induction d with
  | zero => intro a _ h; omega
  | succ d ih =>
    intro a had _
    by_cases h1 : start (a + 1)
    · exact ⟨1, by omega, by omega, h1, fun t h h' => by omega⟩
    · have hd : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h; exact absurd (by rw [show a + 1 = n by omega]; exact hn) h1
        · exact h
      obtain ⟨len, h1l, h2l, h3l, h4l⟩ := ih (a + 1) (by omega) hd
      refine ⟨len + 1, by omega, by omega, by rw [show a + (len + 1) = a + 1 + len by omega]; exact h3l, ?_⟩
      intro t ht ht'
      by_cases htt : t = a + 1
      · subst htt; exact h1
      · exact h4l t (by omega) (by omega)

theorem claim {cfg : NearCfg} {pf : PFunc} {enc : Nat → List Nat} {start : Nat → Prop}
    (hn : NestOK pf enc) (G : GT cfg pf enc start) :
    ∀ d a, a + d = pf.code.size → Live pf enc a → ∀ len, 1 ≤ len → a + len ≤ pf.code.size →
      start (a + len) → (∀ t, a < t → t < a + len → ¬ start t) →
      req pf a ≤ (if start a then 0 else cs pf a len) := by
  intro d
  induction d with
  | zero => intro a h _ len h1 h2; omega
  | succ d ih =>
    intro a had hl len h1 h2 h3 h4
    have ha : a < pf.code.size := by omega
    -- bound for the successor
    have hnext : ∀ i, pf.code[a]? = some i → fallsThrough i = true →
        req pf (a + 1) ≤ cs pf (a + 1) (len - 1) := by
      intro i hc hf
      rcases live_fall hn hl hc hf with hl' | he
      · by_cases hlen : len = 1
        · subst hlen
          have := ih (a + 1) (by omega) hl'
          by_cases hs : a + 1 < pf.code.size
          · obtain ⟨l2, a1, a2, a3, a4⟩ := exists_next start pf.code.size G.startN
              (pf.code.size - (a + 1)) (a + 1) (by omega) (by omega)
            have := this l2 a1 a2 a3 a4
            simp only [h3, if_true] at this
            simp [cs]; omega
          · rw [req_ge pf _ (by omega)]; simp
        · have := ih (a + 1) (by omega) hl' (len - 1) (by omega) (by omega)
            (by rw [show a + 1 + (len - 1) = a + len by omega]; exact h3)
            (fun t ht ht' => h4 t (by omega) (by omega))
          have hs : ¬ start (a + 1) := h4 (a + 1) (by omega) (by omega)
          simpa [hs] using this
      · rw [req_ge pf _ (by omega)]; simp
    by_cases hg : ∃ e, pf.gas[a]? = some (some e)
    · obtain ⟨e, he⟩ := hg; rw [req_entry pf a e he]; exact Nat.zero_le _
    · have hg' : ∀ e, pf.gas[a]? ≠ some (some e) := fun e he => hg ⟨e, he⟩
      obtain ⟨i, hc⟩ : ∃ i, pf.code[a]? = some i := ⟨pf.code[a], by simp [ha]⟩
      rw [req_cons pf a i hc hg']
      have hcs : cs pf a len = costOf i + cs pf (a + 1) (len - 1) := by
        obtain ⟨l', rfl⟩ : ∃ l', len = l' + 1 := ⟨len - 1, by omega⟩
        simp [cs, hc]
      have hn' : (if fallsThrough i then req pf (a + 1) else 0) ≤ cs pf (a + 1) (len - 1) := by
        by_cases hf : fallsThrough i = true
        · rw [if_pos hf]; exact hnext i hc hf
        · rw [if_neg hf]; exact Nat.zero_le _
      by_cases hsa : start a
      · have hz := G.zero a len hsa hl hg' h2 h4
        rw [if_pos hsa]; omega
      · rw [if_neg hsa]; omega

theorem wc_of_GT {cfg : NearCfg} {pf : PFunc} {enc : Nat → List Nat} {start : Nat → Prop}
    (hn : NestOK pf enc) (G : GT cfg pf enc start) : WC cfg pf enc := by
  have startZero : ∀ q, Live pf enc q → start q → req pf q = 0 := by
    intro q hq hs
    by_cases hlt : q < pf.code.size
    · obtain ⟨len, a1, a2, a3, a4⟩ := exists_next start pf.code.size G.startN
        (pf.code.size - q) q (by omega) (by omega)
      have := claim hn G (pf.code.size - q) q (by omega) hq len a1 a2 a3 a4
      simp only [hs, if_true] at this; omega
    · exact req_ge pf q (by omega)
  refine ⟨startZero 0 Live.entry G.start0, ?_, ?_, ?_⟩
  · intro pc i k fee hl hc hg
    have hlt : pc < pf.code.size := by
      rcases Nat.lt_or_ge pc pf.code.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at hc
    obtain ⟨len, a1, a2, a3, a4⟩ := exists_next start pf.code.size G.startN
      (pf.code.size - pc) pc (by omega) (by omega)
    have hf := G.fee pc k fee len hg a2 a4
    have hcs : cs pf pc len = costOf i + cs pf (pc + 1) (len - 1) := by
      obtain ⟨l', rfl⟩ : ∃ l', len = l' + 1 := ⟨len - 1, by omega⟩
      simp [cs, hc]
    have hr : (if fallsThrough i then req pf (pc + 1) else 0) ≤ cs pf (pc + 1) (len - 1) := by
      split
      · rename_i hft
        rcases live_fall hn hl hc hft with hl' | he
        · by_cases hlen : len = 1
          · subst hlen; rw [startZero _ hl' a3]; simp
          · have := claim hn G (pf.code.size - (pc + 1)) (pc + 1) (by omega) hl' (len - 1)
              (by omega) (by omega) (by rw [show pc + 1 + (len - 1) = pc + len by omega]; exact a3)
              (fun t ht ht' => a4 t (by omega) (by omega))
            have hs : ¬ start (pc + 1) := a4 (pc + 1) (by omega) (by omega)
            simpa [hs] using this
        · rw [req_ge pf _ (by omega)]; simp
      · simp
    calc cfg.regularOpCost * (costOf i + (if fallsThrough i then req pf (pc + 1) else 0))
        ≤ cfg.regularOpCost * cs pf pc len := by rw [hcs]; exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ fee.c := hf
  · intro pc q hl hs
    exact startZero q (Live.step pc q true hl hs) (G.jump pc q hl hs)
  · intro pc i hl hc hi
    have hft : fallsThrough i = true := by
      cases i <;> simp_all [isCallI, fallsThrough]
    rcases live_fall hn hl hc hft with hl' | he
    · exact startZero _ hl' (G.ret pc i hl hc hi)
    · exact req_ge pf _ (by omega)

end NearSpecV3.Wasm.FuelGas
