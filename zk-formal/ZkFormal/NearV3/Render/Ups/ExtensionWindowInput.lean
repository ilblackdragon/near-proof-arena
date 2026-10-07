import ZkFormal.NearV3.Render.Ups.SourceCidWindows
import ZkFormal.NearV3.Render.Ups.WindowInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- An ordinary encoded extension update reads its immediate child occurrence at
the unique CH start. This covers RDE and PT with full u32 HP headers. -/
theorem extension_window_ok (I : UpsInst) (base : UpsPartI) (n : Nat)
    (key : List Nat) (child : PTrie) (oldMem : Nat) (newKid : NKid) (newMem : List Nat)
    (hk : base.kind=1 ∨ base.kind=11) (hn : isNode child=true)
    (hc : base.cN=n+1)
    (hp : base.pcid=sourceCidBytes (viewNode n 0 (.ext key child oldMem))) :
    WindowOk I (encodePart base (.ext key (treeKid child) ((u64 oldMem).map UInt8.toNat))
      (.ext key newKid newMem)) := by
  let Q := encodePart base (.ext key (treeKid child) ((u64 oldMem).map UInt8.toNat)) (.ext key newKid newMem)
  have hshape : Q.shape=nodeFields 1 (1+key.length/2) 1 := by
    change nonemptyFields (nodeRawShape (.ext key newKid newMem))=_
    rw [nonempty_node_shape]
    rfl
  constructor
  · intro hbad
    change base.kind=10 at hbad
    omega
  · intro p _ hs hix _ _
    change (fieldAt Q.shape p).1=7 at hs
    change (fieldAt Q.shape p).2.1=0 at hix
    have hpos := ext_child_position (1+key.length/2) p (by omega) (hshape ▸ hs) (hshape ▸ hix)
    have hread : (sposV I Q 7 0 (fieldAt Q.shape p).2.2.2 p).toNat=p := by
      rcases hk with hk|hk <;> simp [sposV,Q,encodePart,hk]
    change Q.pcid.getD (sposV I Q 7 0 (fieldAt Q.shape p).2.2.2 p).toNat 0=Q.cN
    rw [hread]
    change base.pcid.getD p 0=base.cN
    rw [hp,hc,hpos]
    have h := sourceCidBytes_ext_child n 0 key child oldMem 0 hn (by decide)
    simpa only [Nat.add_zero,show 5+(1+key.length/2)=6+key.length/2 by omega] using h
end ZkFormal.NearV3.Render.UpsGen
