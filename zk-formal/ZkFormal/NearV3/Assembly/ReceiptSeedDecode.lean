import ZkFormal.NearV3.Assembly.ReceiptSeeds
import ZkFormal.NearV3.Assembly.CodecSize
import ZkFormal.NearV3.Spec.StoreBuilt

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pU128_bound {w : String} {bs rest : Bytes} {x : Nat}
    (h : pU128 w bs = .ok (x,rest)) : x < 256^16 := by
  unfold pU128 NearSpecV3.lift at h
  split at h
  · rename_i r hr
    simp only [Except.ok.injEq] at h
    subst h
    unfold readU128 readLE at hr
    cases e : takeN 16 bs with
    | none => rw [e] at hr; cases hr
    | some q =>
      obtain ⟨hd,tl⟩ := q
      rw [e] at hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      rw [←hr.1]
      have hh := ZkFormal.Near.Sound.leNat_lt hd
      rw [(ReexecV3D0.takeN_split e).2] at hh
      exact hh
  · cases h

theorem pReceipt_seed {bs rest : Bytes} {r : Receipt}
    (h : pReceipt bs = .ok (r,rest)) :
    (receiptSeed r).toRcptV.toReceipt = r := by
  unfold pReceipt at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    apply receiptSeed_toReceipt
    all_goals exact pU128_bound (by assumption)

theorem pMany_property {α : Type} (p : NearSpecV3.P α) (Q : α → Prop)
    (hp : ∀ bs a rest, p bs = .ok (a,rest) → Q a) :
    ∀ n bs xs rest, pMany p n bs = .ok (xs,rest) → ∀ x ∈ xs, Q x := by
  intro n
  induction n with
  | zero => intro bs xs rest h; cases h; simp
  | succ n ih =>
    intro bs xs rest h
    unfold pMany at h
    obtain ⟨⟨a,tail⟩,ha,h⟩ := bind_ok h
    obtain ⟨⟨ys,last⟩,hy,h⟩ := bind_ok h
    cases h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp _ _ _ ha
    · exact ih _ _ _ hy x hx

theorem pVec_property {α : Type} (p : NearSpecV3.P α) (Q : α → Prop)
    (hp : ∀ bs a rest, p bs = .ok (a,rest) → Q a)
    {w : String} {bs rest : Bytes} {xs : List α}
    (h : pVec w p bs = .ok (xs,rest)) : ∀ x ∈ xs, Q x := by
  unfold pVec at h
  obtain ⟨⟨n,tail⟩,_,h⟩ := bind_ok h
  exact pMany_property p Q hp n _ _ _ h

def ReceiptSeedExact (r : Receipt) : Prop := (receiptSeed r).toRcptV.toReceipt = r

theorem pEntry_receipt_seeds {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e,rest)) : ∀ r ∈ e.receipts, ReceiptSeedExact r := by
  unfold pEntry at h
  repeat' (obtain ⟨_, _, h⟩ := bind_ok h)
  dsimp only at h
  cases h
  exact pVec_property pReceipt ReceiptSeedExact (fun _ _ _ hp => pReceipt_seed hp) (by assumption)

theorem decodeStateWitness_receipt_seeds {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) :
    ∀ e ∈ w.entries, ∀ r ∈ e.receipts, ReceiptSeedExact r := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    exact pVec_property pEntry (fun e => ∀ r ∈ e.receipts, ReceiptSeedExact r)
      (fun _ _ _ hp => pEntry_receipt_seeds hp) (by assumption)

end ZkFormal.NearV3.Assembly
