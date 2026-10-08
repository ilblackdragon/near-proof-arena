import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Candidates.InteractionTriplesProfile
open ZkFormal.Air HorizontalProfile
abbrev P := HorizontalProfile.IP

def dummy (s : Bool) : P := ⟨s,[],[]⟩
def singles (s : Bool) (xs : List P) := xs.flatMap fun x=>[x,dummy s,dummy s]
def pairs (s : Bool) : List P→List P
  | []=>[]
  | [x]=>[x,dummy s,dummy s]
  | x::y::xs=>x::y::dummy s::pairs s xs
def lows (s : Bool) : List P→List P
  | []=>[]
  | [x]=>[x,dummy s,dummy s]
  | [x,y]=>[x,y,dummy s]
  | x::y::z::xs=>x::y::z::lows s xs
def highLow (s : Bool) : List P→List P→List P
  | [],ys=>lows s ys
  | xs,[]=>singles s xs
  | x::xs,y::ys=>x::y::dummy s::highLow s xs ys
def side (s : Bool) (xs : List P) :=
  singles s (xs.filter fun i=>4<i.phi) ++ pairs s (xs.filter fun i=>i.phi=3) ++
  highLow s (xs.filter fun i=>i.phi=4) (xs.filter fun i=>i.phi≤2)
def reorder (xs : List P) := side true (xs.filter (·.send)) ++ side false (xs.filter fun i=>!i.send)

theorem singles_map (s : Bool) (xs : List Interaction) :
    (InteractionTriples.singles s xs).map profile=singles s (xs.map profile) := by
  simp [InteractionTriples.singles,singles,List.map_flatMap,List.flatMap_map,Function.comp_def,
    profile,InteractionTriples.dummy,dummy]
theorem pairs_map (s : Bool) (xs : List Interaction) :
    (InteractionTriples.pairs s xs).map profile=pairs s (xs.map profile) := by
  match xs with
  | []=>rfl
  | [x]=>rfl
  | x::y::xs=>simp [InteractionTriples.pairs,pairs,pairs_map s xs]; rfl
theorem lows_map (s : Bool) (xs : List Interaction) :
    (InteractionTriples.lows s xs).map profile=lows s (xs.map profile) := by
  match xs with
  | []=>rfl
  | [x]=>rfl
  | [x,y]=>rfl
  | x::y::z::xs=>simp [InteractionTriples.lows,lows,lows_map s xs]
theorem highLow_map (s : Bool) (xs ys : List Interaction) :
    (InteractionTriples.highLow s xs ys).map profile=highLow s (xs.map profile) (ys.map profile) := by
  match xs,ys with
  | [],ys=>simp [InteractionTriples.highLow,highLow,lows_map]
  | x::xs,[]=>simp [InteractionTriples.highLow,highLow,singles_map]
  | x::xs,y::ys=>simp [InteractionTriples.highLow,highLow,highLow_map s xs ys]; rfl

theorem side_map (s : Bool) (xs : List Interaction) :
    (InteractionTriples.side s xs).map profile=side s (xs.map profile) := by
  simp only [InteractionTriples.side,side,List.map_append,singles_map,pairs_map,highLow_map,
    List.filter_map,Function.comp_def,phi_profile]
theorem reorder_map (xs : List Interaction) :
    (InteractionTriples.reorder xs).map profile=reorder (xs.map profile) := by
  simp only [InteractionTriples.reorder,reorder,List.map_append,side_map,List.filter_map,
    Function.comp_def,profile]
theorem table_profiles (T : Air.Table) : profiles (InteractionTriples.table T)=reorder (profiles T) :=
  reorder_map T.interactions

def paired (xs : List P) := InteractionPairing.interleave
  (xs.filter fun i=>2<i.phi) (xs.filter fun i=>!(2<i.phi))
def pairReorder (xs : List P) := paired (xs.filter (·.send)) ++ paired (xs.filter fun i=>!i.send)
theorem interleave_map {α β : Type} (f : α→β) (xs ys : List α) :
    (InteractionPairing.interleave xs ys).map f=InteractionPairing.interleave (xs.map f) (ys.map f) := by
  induction xs generalizing ys with
  | nil=>simp [InteractionPairing.interleave]
  | cons x xs ih=>cases ys <;> simp [InteractionPairing.interleave,ih]
theorem paired_map (xs : List Interaction) :
    (InteractionPairing.paired xs).map profile=paired (xs.map profile) := by
  simp only [InteractionPairing.paired,paired,interleave_map,List.filter_map,Function.comp_def,phi_profile]
theorem pairReorder_map (xs : List Interaction) :
    (InteractionPairing.reorder xs).map profile=pairReorder (xs.map profile) := by
  simp only [InteractionPairing.reorder,pairReorder,List.map_append,paired_map,List.filter_map,
    Function.comp_def,profile]
end ZkFormal.NearV3.Candidates.InteractionTriplesProfile
