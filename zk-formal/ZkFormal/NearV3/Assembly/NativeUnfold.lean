import ZkFormal.NearV3.Assembly.QueryAccepted

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def unfoldedPairs (steps : List ImplicitStepV3) : List (PTrie × PTrie) :=
  steps.map (fun s => (s.pre,rebuildPost s.witness.values s.post [keyDelayedIdx,keyBwState]))

theorem ImplicitTraceValid.unfold_result {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) (acc : List (PTrie × PTrie)) :
    forIn pairs (acc,root) (unfoldStep k) = .ok (acc ++ unfoldedPairs steps,last) := by
  induction hv generalizing acc with
  | nil => simp [unfoldedPairs,pure,Except.pure]
  | cons root b t rest steps post last run checked tail ih =>
    simp only [List.forIn_cons,unfoldStep,run,bind,Except.bind,pure,Except.pure]
    rw [ih]
    simp only [unfoldedPairs,List.map_cons,List.append_assoc,List.singleton_append]

theorem triesD0_native_result {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    triesD0 cb wb = .ok ((m.pre,rebuildPost w.main.values m.result.trie
      (mainKeys (appliedReceipts k w) m.bufferedShards)) :: unfoldedPairs steps) := by
  obtain ⟨v,hfind,hparse⟩ := hm.buffered
  have run := hm.run
  rw [hm.pre] at run
  unfold MainExecutionV3.ctx at run
  have hloop := hv.unfold_result
  unfold ZkFormal.NearV3.Assembly.unfoldStep at hloop
  dsimp only at hloop
  simp only [bind,Except.bind,pure,Except.pure] at hloop
  unfold triesD0
  simp only [hk,hw,bind,Except.bind,hm.block,hm.previous,pure,Except.pure,hfind,hparse,run,hloop]
  rw [hm.pre]
  rfl

def preBytes (trees : List PTrie) : Nat := (trees.map NearSpecV3.unfoldedBytesT).sum

theorem preBytes_pairs_le (ps : List (PTrie × PTrie)) :
    preBytes (ps.map Prod.fst) ≤
      (ps.map (fun p => NearSpecV3.unfoldedBytesT p.1 + NearSpecV3.diffT p.1 p.2)).sum := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih => simp only [preBytes,List.map_cons,List.sum_cons] at *; omega

theorem checkD0a_preBytes {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    preBytes (m.pre :: steps.map ImplicitStepV3.pre) ≤ B := by
  have hr := triesD0_native_result hk hw hm hv
  have hh := (relD0a_iff B cb wb).mpr h
  have hb : unfoldBytes cb wb ≤ B := by simpa only [a7,decide_eq_true_eq] using hh.2.2.2.2.1
  simp only [unfoldBytes,hr] at hb
  have hl := preBytes_pairs_le ((m.pre,rebuildPost w.main.values m.result.trie
      (mainKeys (appliedReceipts k w) m.bufferedShards)) :: unfoldedPairs steps)
  simp only [List.map_cons,unfoldedPairs,List.map_map,Function.comp_def] at hl hb
  exact Nat.le_trans hl hb

end ZkFormal.NearV3.Assembly
