import ZkFormal.NearV3.Render.Ups.GByteHpl
import ZkFormal.NearV3.Extract.Ups.PartBytes

open ZkFormal.NearV3 ZkFormal.NearV3.Render
#guard UpsV3.cBytes.length=81
#guard (UpsV3.cBytes.map ZkFormal.Air.Expr.degree).foldl max 0=4
/-- info: 'ZkFormal.NearV3.Render.UpsGen.SourceHeader.length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UpsGen.SourceHeader.length
/-- info: 'ZkFormal.NearV3.Render.UpsGen.cByteHpl_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpsGen.cByteHpl_ok
/-- info: 'ZkFormal.NearV3.UpsRows.hplField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpsRows.hplField
