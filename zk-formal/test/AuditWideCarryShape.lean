import ZkFormal.NearV3.BudgetUps
import ZkFormal.NearV3.Render.Ups.GMem
import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Extract.Ups.Mem
import ZkFormal.NearV3.Render.Ups.WideBits

open ZkFormal.NearV3
example : UpsV3.table.width=200 := by decide +kernel
example : UpsV3.memBitCols.length=41 := by decide +kernel
example : UpsV3.cMem.length=29 := by decide +kernel
/-- info: 'ZkFormal.NearV3.Render.UpsGen.cMem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Render.UpsGen.cMem_ok
/-- info: 'ZkFormal.NearV3.UpsRows.ups_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpsRows.ups_mem
/-- The carry 16 lost by the old 3-bit encoding is represented exactly. -/
example : ((List.range 16).map (fun j => (2:Int)^j*((16:Int)/2^j%2))).sum=16 := by decide +kernel
