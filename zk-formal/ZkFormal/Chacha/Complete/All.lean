import ZkFormal.Chacha.Complete.Kind
import ZkFormal.Chacha.Complete.Bus

/-!
# ZkFormal.Chacha.Complete.All — completeness of the ChaCha20 table `chachaV3`

For any list of supported requests that fits the table, the honest trace
(ZkFormal.Chacha.Gen) has a legal height, satisfies every constraint on every row
(including padding rows and the cyclic wrap), has boolean multiplicity bits, and provides
on `busChacha` exactly the messages `expected reqs` (each `chachaMsg key ctr w (block[w])`
for a used word `w`), receiving nothing.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen

/-- Every constraint vanishes (as an integer) on a legal row pair. -/
theorem row_ok {Z : ZEnv} {X Y : Row} (h : HEnv Z X Y) (hs : Step X Y)
    (hf : Z.first = 0 ∨ (Z.first = 1 ∧ FirstOk X)) : ∀ e ∈ constraints, zev Z e = 0 := by
  intro e he
  unfold constraints at he
  simp only [List.mem_append] at he
  rcases he with ((((he | he) | he) | he) | he) | he
  · exact complete_cBool h e he
  · exact complete_cKind h hs hf e he
  · exact complete_cInit h hs e he
  · exact complete_cCopy h hs e he
  · -- quarter-round constraints: only `Q` rows have a `P` flag
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    have hq' := List.mem_range.mp hq
    cases hs with
    | qp R hR dr p hdr hp => rw [q_selP h (by omega)]; exact q_qrC h hR (by omega) hq'
    | qd R hR dr hdr => rw [q_selP h (by omega)]; exact q_qrC h hR (by omega) hq'
    | qf R hR => rw [q_selP h (by omega)]; exact q_qrC h hR (by omega) hq'
    | pd Y hY => exact selP_zero h (fun _ _ => rfl) _
    | _ => exact selP_zero h (fun _ _ => by kfl) _
  · exact complete_cFF h hs e he

theorem constraints_ok (reqs : List Req) (hok : ∀ R ∈ reqs, ReqOk R) (t : Nat) (pub : List Fp) (r : Nat)
    (hr : r < (honestTrace reqs).height t) :
    ∀ e ∈ constraints, e.eval (honestTrace reqs) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  refine row_ok (honest_env reqs t r pub) (step_at reqs hok t r hr) ?_ e he
  show (if r = 0 then 1 else 0 : Int) = 0 ∨ ((if r = 0 then 1 else 0 : Int) = 1 ∧ _)
  by_cases h0 : r = 0
  · right; subst h0; exact ⟨rfl, row0_ok reqs⟩
  · left; rw [if_neg h0]

/-- **Completeness of the ChaCha20 table.** -/
theorem chacha_complete (reqs : List Gen.Req) (hok : ∀ R ∈ reqs, Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ Table.maxLog) (busChacha : Nat) :
    (∀ t, 1 ≤ (Gen.honestTrace reqs).log t ∧ (Gen.honestTrace reqs).log t ≤ Table.maxLog) ∧
    (∀ t pub r, r < (Gen.honestTrace reqs).height t → ∀ e ∈ Table.constraints,
       e.eval (Gen.honestTrace reqs) t r pub = 0) ∧
    (∀ t pub r, r < (Gen.honestTrace reqs).height t → ∀ i ∈ Table.interactions busChacha, ∀ b ∈ i.mult,
       b.eval (Gen.honestTrace reqs) t r pub = 0 ∨ b.eval (Gen.honestTrace reqs) t r pub = 1) ∧
    (∀ t pub m, tableBusCount (Table.interactions busChacha) (Gen.honestTrace reqs) t pub busChacha true m =
       (Gen.expected reqs).count m ∧
     tableBusCount (Table.interactions busChacha) (Gen.honestTrace reqs) t pub busChacha false m = 0) :=
  ⟨log_bounds reqs hrows,
   fun t pub r hr => constraints_ok reqs hok t pub r hr,
   fun t pub r _ => multBits reqs busChacha t r pub,
   fun t pub m => ⟨count_send reqs hok busChacha t pub m, count_recv reqs busChacha t pub m⟩⟩

/-- The honest trace is a legal ChaCha table (the hypothesis of the soundness theorems). -/
theorem chLocal_honest (reqs : List Gen.Req) (hok : ∀ R ∈ reqs, Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ Table.maxLog) (t : Nat) (pub : List Fp) :
    Sound.ChLocal (Gen.honestTrace reqs) t pub :=
  ⟨(log_bounds reqs hrows t).1, (log_bounds reqs hrows t).2,
   fun r hr => constraints_ok reqs hok t pub r hr⟩

end ZkFormal.Chacha.Complete

