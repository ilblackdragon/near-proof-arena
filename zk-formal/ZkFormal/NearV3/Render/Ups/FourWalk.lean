import ZkFormal.NearV3.Render.Ups.Ok

set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- Whether the first query nibble enters the next proper source record. -/
def walkEnter1 (I : UpsInst) : Prop := I.D=2 ∨ (I.D=1 ∧ (I.ts=2 ∨ I.ti=1))
instance (I : UpsInst) : Decidable (walkEnter1 I) := inferInstanceAs (Decidable (_ ∨ _))

def terminalMode (ci : Nat) : Nat := if ci≤1 then 0 else if ci≤3 then 2 else 1

def terminalSymbol (I : UpsInst) : Nat := if 4≤I.ci then (if I.ci=4 then SYM_END else I.x) else wsym I.ts

def fourWalk (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat) : List WStep3 :=
  let N0 := I.N.getD 0 0
  let N1 := I.N.getD (if walkEnter1 I then 1 else 0) 0
  let pos1 := if walkEnter1 I then 0 else 1
  let ND := I.N.getD I.D 0
  let start : WStep3 := ⟨0,SYM_START,[0,I.tau,SYM_START,N0,0,EK_DOWN],0,0,0,0⟩
  let terminal : WStep3 := ⟨terminalMode I.ci,wsym I.ts,
    [ND,I.ti,terminalSymbol I,target,targetPos,
      if I.ci≤1 then EK_VAL else if I.ci=4 then EK_LEND else EK_KEY],0,bm,hv,0⟩
  let drain (t : Nat) : WStep3 := ⟨3,wsym t,[0,0,0,0,0,0],0,0,0,0⟩
  let first : WStep3 := ⟨0,0,[N0,0,0,N1,pos1,ek1],0,0,0,0⟩
  let second : WStep3 := ⟨0,15,[N1,pos1,15,ND,I.ti,ek2],0,0,0,0⟩
  [start,if I.ts=1 then terminal else first,
    if I.ts=1 then drain 2 else if I.ts=2 then terminal else second,
    if I.ts=3 then terminal else drain 3]

def withFourWalk (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat) : UpsInst :=
  {I with walk:=fourWalk I bm hv ek1 ek2 target targetPos}

private theorem forall_one_four (p : Nat→Prop) : (∀t,1≤t→t<4→p t) ↔ p 1 ∧ p 2 ∧ p 3 := by
  constructor
  · intro h; exact ⟨h 1 (by decide) (by decide),h 2 (by decide) (by decide),h 3 (by decide) (by decide)⟩
  · intro h t h1 h4
    rcases (show t=1 ∨ t=2 ∨ t=3 by omega) with rfl|rfl|rfl
    exact h.1
    exact h.2.1
    exact h.2.2

private theorem forall_one_three (p : Nat→Prop) : (∀t,1≤t→t<3→p t) ↔ p 1 ∧ p 2 := by
  constructor
  · intro h; exact ⟨h 1 (by decide) (by decide),h 2 (by decide) (by decide)⟩
  · intro h t h1 h3
    rcases (show t=1 ∨ t=2 by omega) with rfl|rfl
    exact h.1
    exact h.2

private theorem forall_zero_3 (p : Nat→Prop) : (∀t,t<3→p t) ↔ p 0 ∧ p 1 ∧ p 2 := by
  constructor
  · intro h; exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide)⟩
  · intro h t ht
    rcases (show t=0 ∨ t=1 ∨ t=2 by omega) with rfl|rfl|rfl
    exact h.1
    exact h.2.1
    exact h.2.2

private theorem forall_zero_4 (p : Nat→Prop) : (∀t,t<4→p t) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 := by
  constructor
  · intro h; exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · intro h t ht
    rcases (show t=0 ∨ t=1 ∨ t=2 ∨ t=3 by omega) with rfl|rfl|rfl|rfl
    exact h.1
    exact h.2.1
    exact h.2.2.1
    exact h.2.2.2

private theorem geometry0_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=0) (ht : I.ts=1) (hi : I.ti=0)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry1_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=0) (ht : I.ts=2) (hi : I.ti=1)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry2_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=0) (ht : I.ts=3) (hi : I.ti=2)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry3_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=1) (ht : I.ts=2) (hi : I.ti=0)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry4_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=1) (ht : I.ts=3) (hi : I.ti=0)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry5_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=1) (ht : I.ts=3) (hi : I.ti=1)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

private theorem geometry6_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hD : I.D=2) (ht : I.ts=3) (hi : I.ti=0)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  rcases (show I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 by omega)
    with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  all_goals simp_all [hD,ht,hi,hc,wsym,SYM_END]
  all_goals try clear hci hts hti hend hnib
  all_goals constructor <;>
    (try simp only [forall_one_four,forall_one_three,forall_zero_3,forall_zero_4]) <;>
    simp_all [withFourWalk,step,fourWalk,terminalMode,terminalSymbol,walkEnter1,wsym,ent,lv,
      forall_one_four,forall_one_three,Nat.forall_lt_succ_right,EK_DOWN,EK_KEY,EK_VAL,EK_LEND,SYM_END]

theorem fourWalk_ok (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (hci : I.ci<11) (hts : 1≤I.ts ∧ I.ts≤3) (hti : I.ti<3)
    (geometry : (I.D=0 ∧ I.ts=I.ti+1) ∨ (I.D=1 ∧ I.ts=2 ∧ I.ti=0) ∨
      (I.D=1 ∧ I.ts=3 ∧ I.ti≤1) ∨ (I.D=2 ∧ I.ts=3 ∧ I.ti=0))
    (hend : I.ts=3 → I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8)
    (hnib : I.ts≠3 → I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10)
    (hbranch : I.ci=2 ∨ I.ci=3 → I.ti=0)
    (hb : bm<2^16) (hh : hv≤1) (hval : I.ci=2 → hv=0)
    (hb0 : I.ci=3 → I.ts=1 → bm%2=0)
    (hb15 : I.ci=3 → I.ts=2 → bm/2^15%2=0)
    (habs : 4≤I.ci → (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P)
    (hek1 : ek1≤1) (hek2 : ek2≤1) :
    WalkOkU (withFourWalk I bm hv ek1 ek2 target targetPos) := by
  have geom : (I.D=0 ∧ I.ts=1 ∧ I.ti=0) ∨ (I.D=0 ∧ I.ts=2 ∧ I.ti=1) ∨
      (I.D=0 ∧ I.ts=3 ∧ I.ti=2) ∨ (I.D=1 ∧ I.ts=2 ∧ I.ti=0) ∨
      (I.D=1 ∧ I.ts=3 ∧ I.ti=0) ∨ (I.D=1 ∧ I.ts=3 ∧ I.ti=1) ∨
      (I.D=2 ∧ I.ts=3 ∧ I.ti=0) := by
    clear hend hnib hbranch hval hb0 hb15 habs hci hb hh hek1 hek2
    omega
  rcases geom with ⟨hD,ht,hi⟩|⟨hD,ht,hi⟩|⟨hD,ht,hi⟩|⟨hD,ht,hi⟩|⟨hD,ht,hi⟩|⟨hD,ht,hi⟩|⟨hD,ht,hi⟩
  · exact geometry0_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry1_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry2_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry3_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry4_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry5_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
  · exact geometry6_ok I bm hv ek1 ek2 target targetPos hD ht hi hci hts hti hend hnib hbranch hb hh hval hb0 hb15 habs hek1 hek2
end ZkFormal.NearV3.Render.UpsGen
