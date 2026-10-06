import ZkFormal.NearV3.Render.Node.Local
import ZkFormal.NearV3.Render.Node.Traffic

/-!
# ZkFormal.NearV3.Render.NodeRender — the `nodeV3` render

Re-exports `node_render_local` (`Render/Node/Local.lean`) and `node_render_traffic`
(`Render/Node/Traffic.lean`): an honest `nodeV3` table generated from a view `vs` with
`NodeOk vs` is locally legal and has traffic `nodeTraffic3 vs`.
-/
