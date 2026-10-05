import ZkFormal.Near.Render.Proof.AcctFacts

/-!
# ZkFormal.Near.Render.Proof.BusCommon — unfolding `hcount` on one bus
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- `hcount` as the sum of the seven tables' counts. -/
theorem hcount_eq (c : Claim) (e : Ext) (b : Nat) (s : Bool) (m : List Fp) :
    hcount c e b s m =
      cnt (sel s (shaTraffic (bundle c e).msgs) b) m +
      (cnt (sel s (nodeTraffic (nodeViewsOf (bundle c e).info (edgeUses (bundle c e).walks)) (pubOf c)) b) m +
      (cnt (sel s (walkTraffic (walkViewsOf (bundle c e).walks)) b) m +
      (cnt (sel s (rcptTraffic (pubOf c) (rcptViewsOf (bundle c e).info)) b) m +
      (cnt (sel s (acctTraffic (acctViewsOf (bundle c e).info)) b) m +
      (cnt (sel s (mrkTraffic (pubOf c) (mrkViewOf (bundle c e).info)) b) m +
      (cnt (sel s (sortTraffic (sortIdsOf (bundle c e).info)) b) m + 0)))))) := rfl

theorem cnt_nil (m : List Fp) : cnt [] m = 0 := rfl

theorem zip_range_map {α : Type} (f : Nat → α) :
    ∀ (l : List Nat), (l.map f).zip l = l.map fun x => (f x, x)
  | [] => rfl
  | x :: l => by simp [zip_range_map f l]

theorem map_filter_eq {α β : Type} (p : α → Bool) (g : α → β) :
    ∀ l : List α, (l.filter p).map g = l.filterMap (fun x => if p x then some (g x) else none)
  | [] => rfl
  | x :: l => by
    by_cases h : p x <;> simp [List.filter_cons, h, map_filter_eq p g l]

theorem bundle_info (c : Claim) (e : Ext) : (bundle c e).info = mkInfo c e := rfl

end ZkFormal.Near.Render
