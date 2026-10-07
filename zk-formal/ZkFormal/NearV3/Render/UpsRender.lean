import ZkFormal.NearV3.Render.Ups.GSeg
import ZkFormal.NearV3.Render.Ups.GDig
import ZkFormal.NearV3.Render.Ups.GWalk
import ZkFormal.NearV3.Render.Ups.GRows
import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.GPlan
import ZkFormal.NearV3.Render.Ups.GFieldsComplete
import ZkFormal.NearV3.Render.Ups.GMem
import ZkFormal.NearV3.Render.Ups.GByteWindows
import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.GByteOffsets
import ZkFormal.NearV3.Render.Ups.GByteHeaders
import ZkFormal.NearV3.Render.Ups.GBytePositions

/-!
# ZkFormal.NearV3.Render.UpsRender — the `upsV3` render (M7d, in progress)

* generator `UpsGen.cell` from `UpsInst` (`Render/Ups/Gen.lean`), honest input `UpsOk`
  (`Render/Ups/Ok.lean`);
* `ups_render_local_of` (`Render/Ups/Local.lean`): `TableLocal` from `GroupOk` of all constraints;
* `ups_render_traffic`, `ups_render_view` (`Render/Ups/Traffic.lean`);
* groups proved: `cSeg_ok`, `cDigest_ok`, `cWalk_ok`, `cRows_ok`, `cConst_ok`, `cBool_ok`, `cPlan_ok` (with explicit `PartOk` inputs); `cFields_ok` (with semantic shape/window inputs); all 29 memory equations via `cMem_ok` (with explicit carry/serialization inputs); 58 byte-window, selector, header and source-position equations; padding rows for every group (`groupOk_of`).
-/
