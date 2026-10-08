import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowPatchedTraffic
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay

/-- Canonical representative of the exact six field-valued UPB columns. -/
def physicalWindowKey (tr : Trace Fp) (t r : Nat) : Msg :=
  (windowFieldKey tr t r).map Fp.toNat

def selectedWindow (tr : Trace Fp) (t : Nat) (key : Msg) (r : Nat) : Bool :=
  decide (tr.cell t r UpsV3.rd=1) && (physicalWindowKey tr t r==key)

def physicalWindowRank (tr : Trace Fp) (t r : Nat) : Nat :=
  (List.range r).countP (selectedWindow tr t (physicalWindowKey tr t r))

def physicalWindowUsers (tr : Trace Fp) (t : Nat) (key : Msg) : Nat :=
  (List.range (tr.height t)).countP (selectedWindow tr t key)

def windowRanksFor (tr : Trace Fp) (t : Nat) (key : Msg) : List Nat :=
  (List.range (tr.height t)).filterMap (fun r=>
    if selectedWindow tr t key r then some (physicalWindowRank tr t r) else none)

private theorem range_count_ranks (p : Nat→Bool) (n : Nat) :
    (List.range n).filterMap (fun r=>if p r then some ((List.range r).countP p) else none)=
      List.range' 0 ((List.range n).countP p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filterMap_append,ih,List.countP_append]
    cases h : p n <;> simp [h,List.range'_1_concat]

theorem windowRanksFor_exact (tr : Trace Fp) (t : Nat) (key : Msg) :
    windowRanksFor tr t key=List.range' 0 (physicalWindowUsers tr t key) := by
  rw [physicalWindowUsers,←range_count_ranks]
  unfold windowRanksFor
  congr 1
  funext r
  by_cases hs : selectedWindow tr t key r=true
  · have hk : physicalWindowKey tr t r=key := by
      simpa only [selectedWindow,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
        (show (tr.cell t r UpsV3.rd=1) ∧ physicalWindowKey tr t r=key from by
          simpa only [selectedWindow,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using hs).2
    simp [hs,physicalWindowRank,hk]
  · have hf : selectedWindow tr t key r=false := by
      cases he : selectedWindow tr t key r <;> simp_all
    simp [hf]

theorem physicalWindowRank_bound (tr : Trace Fp) (t r : Nat) :
    physicalWindowRank tr t r≤r := by
  have := List.countP_le_length (p:=selectedWindow tr t (physicalWindowKey tr t r))
    (l:=List.range r)
  simpa [physicalWindowRank] using this

theorem physicalWindowRank_field {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL : TableLocal compactTable tr t pub) (hr : r<tr.height t) :
    physicalWindowRank tr t r<P := by
  have hb:=physicalWindowRank_bound tr t r
  have hl : tr.log t≤22:=hL.log_le
  have hp:=Nat.pow_le_pow_right (n:=2) (by decide) hl
  change 2^tr.log t≤2^22 at hp
  change r<2^tr.log t at hr
  unfold P;omega

theorem window_counter_chain (tr : Trace Fp) (t : Nat) (key : Msg) :
    (key++[0])::((windowRanksFor tr t key).map (fun u=>key++[u+1]))=
      (windowRanksFor tr t key).map (fun u=>key++[u])++[key++[physicalWindowUsers tr t key]] := by
  rw [windowRanksFor_exact]
  have h : 0::(List.range' 0 (physicalWindowUsers tr t key)).map (·+1)=
      List.range' 0 (physicalWindowUsers tr t key)++[physicalWindowUsers tr t key] := by
    rw [←List.range'_succ_left]
    simpa only [List.range'_succ,Nat.zero_add] using
      (List.range'_1_concat (s:=0) (n:=physicalWindowUsers tr t key))
  have hm:=congrArg (List.map (fun u=>key++[u])) h
  simpa only [List.map_cons,List.map_map,List.map_append,List.map_nil,Function.comp_def] using hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
