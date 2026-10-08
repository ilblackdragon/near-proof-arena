import ZkFormal.NearV3.Candidates.HorizontalDegree
namespace ZkFormal.NearV3.Candidates.HorizontalProfile
open ZkFormal.Air ZkFormal.Stark HorizontalTables HorizontalDegree

/-- Only degrees and direction influence auxiliary shape. Column indices are erased. -/
structure IP where
  send : Bool
  mult : List Nat
  msg : List Nat
  deriving DecidableEq, Repr

def profile (i : Interaction) : IP := ⟨i.send,i.mult.map Expr.degree,i.msg.map Expr.degree⟩
def profiles (T : Air.Table) : List IP := T.interactions.map profile

def IP.phi (i : IP) : Nat := match i.mult with
  | [] => 0
  | [b] => b+i.msg.foldr max 0
  | _ => 1

def IP.multi (i : IP) : Nat := match i.mult with
  | [] | [_] => 0
  | a::b::bs => max (2*i.msg.foldr max 0)
      (max 2 (max (a+i.msg.foldr max 0+b+1) ((bs.map (·+2)).foldr max 0)))

def auxDegree (ps : List IP) (g : Nat) : Nat :=
  (ps.map IP.multi ++
    (chunksOf (max g 1) (ps.filter (fun (i : IP)=>i.send==true))).map (fun (xs : List IP)=>2+(xs.map IP.phi).sum) ++
    (chunksOf (max g 1) (ps.filter (fun (i : IP)=>i.send==false))).map (fun (xs : List IP)=>2+(xs.map IP.phi).sum)).foldr max 2

@[simp] theorem profile_shift (off : Nat) (i : Interaction) :
    profile (interaction off i)=profile i := by
  simp [profile,interaction,List.map_map,Function.comp_def]

@[simp] theorem phi_profile (i : Interaction) : (profile i).phi=i.phiDegree := by
  rcases i with ⟨bus,mult,msg,send⟩
  cases mult with
  | nil => rfl
  | cons a bs => cases bs <;> rfl

theorem auxDegree_eq (T : Air.Table) (g : Nat) : T.auxDegree g=auxDegree (profiles T) g := by
  unfold Table.auxDegree auxDegree profiles
  simp only [List.map_map,Function.comp_def,List.filter_map]
  have hs : ∀ i : Interaction, (profile i).send=i.send := fun _=>rfl
  simp only [hs,ZkFormal.V2.G.chunksOf_map,List.map_map,Function.comp_def,phi_profile]
  congr 3
  apply List.map_congr_left
  intro i hi
  cases h : i.mult with
  | nil => simp [IP.multi,profile,h]
  | cons a bs => cases bs <;> simp [IP.multi,profile,h,List.map_map,Function.comp_def]

@[simp] theorem layout_profiles (ts : List Air.Table) (off : Nat) :
    (HorizontalTables.layout off ts).flatMap profiles=ts.flatMap profiles := by
  induction ts generalizing off with
  | nil => rfl
  | cons T ts ih =>
    simp [HorizontalTables.layout,profiles,shifted,List.map_map,Function.comp_def,ih]

@[simp] theorem fuse_profiles (ts : List Air.Table) :
    profiles (fuse ts)=ts.flatMap profiles := by
  change ((HorizontalTables.layout 0 ts).flatMap (·.interactions)).map profile=ts.flatMap profiles
  rw [List.map_flatMap]
  exact layout_profiles ts 0

theorem numSide_eq (T : Air.Table) (b : Bool) :
    T.numSide b=((profiles T).filter (fun i=>i.send==b)).length := by
  simp [Table.numSide,profiles,List.filter_map,profile,Function.comp_def]

theorem auxCount_eq (T : Air.Table) (g : Nat) :
    T.auxCount g=((profiles T).map (fun i=>2*(i.mult.length-1))).sum+
      numGroups (((profiles T).filter (fun i=>i.send==true)).length) g+
      numGroups (((profiles T).filter (fun i=>i.send==false)).length) g := by
  unfold Table.auxCount
  rw [numSide_eq,numSide_eq]
  simp [profiles,List.map_map,profile,Function.comp_def]

theorem layout_constraints (ts : List Air.Table) (off : Nat) :
    (HorizontalTables.layout off ts).flatMap (fun T=>T.allConstraints.map Expr.degree)=
      ts.flatMap (fun T=>T.allConstraints.map Expr.degree) := by
  induction ts generalizing off with
  | nil => rfl
  | cons T ts ih => simp [HorizontalTables.layout,ih]

theorem fused_constraint_bound (ts : List Air.Table) (d : Nat)
    (h : ∀ T∈ts, ∀ e∈T.allConstraints, e.degree≤d) :
    ∀ e∈(fuse ts).allConstraints, e.degree≤d := by
  have hshift : ∀ T∈HorizontalTables.layout 0 ts, ∀ e∈T.allConstraints, e.degree≤d := by
    have hl := layout_constraints ts 0
    intro T hT e he
    have hm : e.degree∈(HorizontalTables.layout 0 ts).flatMap
        (fun T=>T.allConstraints.map Expr.degree) :=
      List.mem_flatMap.mpr ⟨T,hT,List.mem_map.mpr ⟨e,he,rfl⟩⟩
    rw [hl] at hm
    obtain ⟨U,hU,hv⟩ := List.mem_flatMap.mp hm
    obtain ⟨f,hf,hfdeg⟩ := List.mem_map.mp hv
    rw [← hfdeg]
    exact h U hU f hf
  intro e he
  rcases List.mem_append.mp he with hc | hb
  · obtain ⟨T,hT,he⟩ := List.mem_flatMap.mp hc
    exact hshift T hT e (List.mem_append_left _ he)
  · obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp hb
    obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp he
    obtain ⟨T,hT,hi⟩ := List.mem_flatMap.mp hi
    exact hshift T hT _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_map.mpr ⟨bit,hbit,rfl⟩⟩))

theorem mult_weights (T : Air.Table) :
    T.interactions.map (fun i=>2^i.mult.length-1)=
      (profiles T).map (fun i=>2^i.mult.length-1) := by
  simp [profiles,profile,List.map_map,Function.comp_def]

theorem msg_lengths (T : Air.Table) :
    T.interactions.map (fun i=>i.msg.length)=(profiles T).map (fun i=>i.msg.length) := by
  simp [profiles,profile,List.map_map,Function.comp_def]

theorem interaction_count (T : Air.Table) : T.interactions.length=(profiles T).length := by
  simp [profiles]
end ZkFormal.NearV3.Candidates.HorizontalProfile
