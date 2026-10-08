import ZkFormal.NearV3.Assembly.CompactBranchDigestInventory

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem cast_nat (n : Nat) : ((n:Int):Fp).toNat=n%P := by
  change (Fp.ofNat n).toNat=n%P
  exact Fp.toNat_ofNat n

def digestWindow (I : Render.UpsInst) (k pos job len : Nat) : Msg :=
  digMsg (Fp.ofNat (upsertJobId I.tau job)).toNat (Fp.ofNat len).toNat
    ((List.range 32).map fun i=>(Fp.ofNat ((part I k).q.getD (pos+i) 0)).toNat)

/-- The value field targets job0 exactly when the native edit inserts/replaces
its value; copied value references create no digest demand. -/
theorem value_field_target (I : Render.UpsInst) (k pos wi : Nat) :
    fieldDigestMsgs I k pos 5 wi=
      if VcpB I (part I k)=true then [] else [digestWindow I k pos 0 (L I)] := by
  have hid : upsIdV I 0=(upsertJobId I.tau 0 : Int) := (upsertJobId_renderer I 0).symm
  cases hv:VcpB I (part I k) <;>
    simp [fieldDigestMsgs,WinFrB,CpB,WfrB,hv,hid,dIV,dLV,GdB,digestWindow,←upsertJobId_renderer,cast_nat]


/-- Child windows retain the exact native plan target: the new-leaf job k
with length50, or the specified jm child and its actual encoded length. -/
theorem child_field_target (I : Render.UpsInst) (k pos wi : Nat) :
    fieldDigestMsgs I k pos 7 wi=
      if WfrB I (part I k) 7 wi=true then
        [digestWindow I k pos
          (if WnB I (part I k) 7 wi=true then k else (part I k).jm)
          (if WnB I (part I k) 7 wi=true then 50 else (part I k).clen)] else [] := by
  cases hf:WfrB I (part I k) 7 wi <;> cases hn:WnB I (part I k) 7 wi <;>
    simp [fieldDigestMsgs,WinFrB,hf,hn,dIV,dLV,GdB,digestWindow,←upsertJobId_renderer,cast_nat]
  all_goals simp only [←upsertJobId_renderer I 0,cast_nat,
    show ((50:Int):Fp).toNat=50 by decide,show 50%P=50 by decide]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
