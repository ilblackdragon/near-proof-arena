import ZkFormal.NearV3.Rcpt.Link.ProofDecode

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- Parser tail lengths never increase; used to charge source path bytes to raw witness bytes. -/
def NonIncreasing {α : Type} (p : NearSpecV3.P α) : Prop :=
  ∀ bs a rest, p bs = .ok (a, rest) → rest.length ≤ bs.length

theorem takeN_consumption : ∀ n bs v rest, takeN n bs = some (v, rest) →
    bs.length = n + rest.length := by
  intro n
  induction n with
  | zero => intro bs v rest h; cases h; simp
  | succ n ih =>
    intro bs v rest h
    cases bs with
    | nil => simp [takeN] at h
    | cons b bs =>
      simp only [takeN, Option.map_eq_some_iff] at h
      obtain ⟨⟨v', rest'⟩, hh, he⟩ := h
      cases he
      have hl := ih bs v' rest' hh
      simp only [List.length_cons]
      omega

theorem pLE_consumption {n : Nat} {w : String} {bs rest : Bytes} {v : Nat}
    (h : NearSpecV3.lift w (readLE n) bs = .ok (v, rest)) : bs.length = n + rest.length := by
  unfold NearSpecV3.lift readLE at h
  split at h
  · rename_i out ho
    cases h
    simp only [Option.map_eq_some_iff] at ho
    obtain ⟨⟨a, tail⟩, ha, he⟩ := ho
    cases he
    exact takeN_consumption _ _ _ _ ha
  · cases h

theorem pHash_consumption {w : String} {bs v rest : Bytes}
    (h : pHash w bs = .ok (v, rest)) : bs.length = 32 + rest.length := by
  unfold pHash NearSpecV3.lift at h
  split at h
  · rename_i out ho
    cases h
    exact takeN_consumption _ _ _ _ ho
  · cases h

theorem takeAcc_consumption : ∀ n acc bs v rest, takeAcc n acc bs = some (v, rest) →
    bs.length = n + rest.length := by
  intro n
  induction n with
  | zero => intro acc bs v rest h; cases h; simp
  | succ n ih =>
    intro acc bs v rest h
    cases bs with
    | nil => simp [takeAcc] at h
    | cons b bs =>
      have hh := ih (b :: acc) bs v rest h
      simp only [List.length_cons]
      omega

theorem pTake_consumption {n : Nat} {w : String} {bs v rest : Bytes}
    (h : pTake n w bs = .ok (v, rest)) : bs.length = n + rest.length := by
  unfold pTake NearSpecV3.lift takeT at h
  split at h
  · rename_i out ho
    cases h
    exact takeAcc_consumption _ _ _ _ _ ho
  · cases h

theorem pU8_consumption {w : String} {bs rest : Bytes} {v : Nat}
    (h : pU8 w bs = .ok (v, rest)) : bs.length = 1 + rest.length := pLE_consumption h

theorem pUInt_le (n : Nat) (w : String) : NonIncreasing (NearSpecV3.lift w (readLE n)) := by
  intro bs v rest h
  have := pLE_consumption h
  omega

theorem pHash_le (w : String) : NonIncreasing (pHash w) := by
  intro bs v rest h; have := pHash_consumption h; omega

theorem pTake_le (n : Nat) (w : String) : NonIncreasing (pTake n w) := by
  intro bs v rest h; have := pTake_consumption h; omega

theorem pBytes_le (w : String) : NonIncreasing (pBytes w) := by
  intro bs v rest h
  unfold pBytes NearSpecV3.lift readBytesT at h
  split at h
  · rename_i out ho
    cases h
    split at ho
    · cases ho
    · rename_i n tail hn
      have hn' := pLE_consumption (w := w) (show NearSpecV3.lift w (readLE 4) bs = .ok (n, tail) by
        unfold NearSpecV3.lift; rw [show readLE 4 bs = some (n, tail) from hn])
      have ht := takeAcc_consumption _ _ _ _ _ ho
      omega
  · cases h

end ZkFormal.NearV3.Rcpt.Candidates
