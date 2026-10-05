import ZkFormal.Game

/-!
# ZkFormal.Assembly.Guard — the claim-canonicality guard of the deployed verifier

**Why (finding R-L7-2).** The IOP reads the claim only through
`pubOf cb = cb.map ofNat` and `Expr.pub i = pub.getD i 0`, so an AIR cannot tell
`cb` from `cb ++ [0]`: if `Holds A (pubOf cb) tr` then `Holds A (pubOf (cb ++ [0])) tr`
for every AIR whose public reads stay below `|cb|`.  The honest prover then makes
an *accepted* proof for `cb ++ [0]`, which does not decode under a strict claim
codec, so the judge's game (language `bk.InLang` = decodable claims with a backend
object) would count it as a win.  The deployed verifier therefore first checks
that the claim bytes are canonical (`claimOk`: decode, re-encode, compare) and
rejects otherwise, before any oracle query.

`romSound_guard` transfers `RomSound` from the unguarded verifier with language `L`
to the guarded one with any language `L'` that contains every canonical claim of `L`.
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security ZkFormal

/-- Reject claims failing `ok` before running `V`. -/
def guardTree (ok : Bytes → Bool) (V : TreeVerifier) : TreeVerifier :=
  ⟨fun pub cb pb => if ok cb then V.tree pub cb pb else .pure false⟩

/-- Canonical claim bytes of a challenge: they decode, and re-encode to themselves. -/
def claimOk (S : ChallengeSpec) (cb : Bytes) : Bool :=
  match S.decodeClaim cb with
  | some c => S.encodeClaim c == cb
  | none => false

theorem claimOk_encode (S : ChallengeSpec) (c : S.Claim) : claimOk S (S.encodeClaim c) = true := by
  simp [claimOk, S.decode_encode c]

theorem claimOk_iff (S : ChallengeSpec) (cb : Bytes) (h : claimOk S cb = true) :
    ∃ c, S.decodeClaim cb = some c ∧ S.encodeClaim c = cb := by
  unfold claimOk at h
  split at h
  · rename_i c hc; exact ⟨c, hc, by simpa using h⟩
  · cases h

/-- The lazy oracle never clears its overflow flag. -/
theorem runH_overflow {α : Type} (A : OracleComp hashSpec α) (s : LazyRO) (h : s.overflow = true) :
    (runH LazyRO.query A s).2.overflow = true := by
  induction A generalizing s with
  | pure a => exact h
  | query x k ih =>
    simp only [runH]
    apply ih
    simp only [LazyRO.query]
    split
    · exact h
    · split
      · rfl
      · exact h

theorem romSound_guard {S : ChallengeSpec} {L L' : Bytes → Prop} (ok : Bytes → Bool)
    (hLL : ∀ cb, ok cb = true → L cb → L' cb) (V : TreeVerifier) (P : OracleProver S)
    (pub : Bytes) {qH qP n num den : Nat}
    (h : RomSound S L V.toVerifier P pub qH qP n num den) :
    RomSound S L' (guardTree ok V).toVerifier P pub qH qP n num den := by
  intro A hH hP
  refine PrLE.mono (fun t hw => ?_) (h A hH hP)
  unfold romWins at hw ⊢
  simp only [TreeVerifier.toVerifier, guardTree] at hw ⊢
  generalize OracleComp.simulate (romImpl S P pub) A (LazyRO.init t) = r1 at hw ⊢
  by_cases hok : ok r1.1.1 = true
  · rw [if_pos hok] at hw
    rcases hw with hw | ⟨hacc, hn⟩
    · exact Or.inl hw
    · exact Or.inr ⟨hacc, fun hl => hn (hLL _ hok hl)⟩
  · rw [if_neg hok] at hw
    rcases hw with hw | ⟨hacc, _⟩
    · exact Or.inl (runH_overflow _ _ hw)
    · cases hacc

end ZkFormal.Assembly
