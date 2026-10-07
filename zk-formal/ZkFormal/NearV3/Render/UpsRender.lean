import ZkFormal.NearV3.Render.Ups.GSeg
import ZkFormal.NearV3.Render.Ups.GDig
import ZkFormal.NearV3.Render.Ups.GWalk
import ZkFormal.NearV3.Render.Ups.GRows
import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.GPlan

/-!
# ZkFormal.NearV3.Render.UpsRender — the `upsV3` render (M7d, in progress)

* generator `UpsGen.cell` from `UpsInst` (`Render/Ups/Gen.lean`), honest input `UpsOk`
  (`Render/Ups/Ok.lean`);
* `ups_render_local_of` (`Render/Ups/Local.lean`): `TableLocal` from `GroupOk` of all constraints;
* `ups_render_traffic`, `ups_render_view` (`Render/Ups/Traffic.lean`);
* groups proved: `cSeg_ok`, `cDigest_ok`, `cWalk_ok`, `cRows_ok`, `cConst_ok`, `cBool_ok`, `cPlan_ok` (with explicit `PartOk` inputs); padding rows for every group (`groupOk_of`).
-/
