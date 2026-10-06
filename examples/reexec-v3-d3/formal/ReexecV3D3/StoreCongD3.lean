import NearSpecV3.D3.FunctionCall
import ReexecV3D3.StoreCong

/-!
# The D3 `FunctionCall` hook reads `Env.store` only through `Env.codeOf`

`NearSpecV3.D3.functionCall` consults the merged recorded storage only as `env.codeOf` (the code
blob of the called account, `codeAvailable`'s fallback, and the trie-backed `External`'s node
store `TTN.RealStore.store`). So two stores that answer every lookup alike (`hGet s1 = hGet s2`,
e.g. the same set of values in any order, without duplicates) give the same hook results
(`d3Hooks_cong`), and by `StoreCong` the same main transition (`applyNewChunkD2_d3_store`).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3

theorem codeOf_ext (E : Env) {s1 s2 : HStore} (hext : ∀ h, hGet s1 h = hGet s2 h) :
    Env.codeOf { E with store := s1 } = Env.codeOf { E with store := s2 } :=
  funext fun h => hext h

theorem d3Hooks_cong (cfg : Wasm.NearCfg) (E : Env) {s1 s2 : HStore} (hext : ∀ h, hGet s1 h = hGet s2 h) :
    HookCong (d3Hooks cfg) E s1 s2 := by
  intro r a i n inputs deployed attempted st ar b
  show functionCallD3 cfg _ st ar b = functionCallD3 cfg _ st ar b
  unfold functionCallD3 functionCall codeAvailable
  simp only [codeOf_ext E hext]

theorem applyNewChunkD2_d3_store (cfg : Wasm.NearCfg) (E : Env) {s1 s2 : HStore}
    (hext : ∀ h, hGet s1 h = hGet s2 h) (prims : Prims) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    applyNewChunkD2 (d3Hooks cfg) prims { E with store := s1 } t vu lastProps incoming txs ownCong =
    applyNewChunkD2 (d3Hooks cfg) prims { E with store := s2 } t vu lastProps incoming txs ownCong :=
  applyNewChunkD2_store (d3Hooks cfg) E s1 s2 (d3Hooks_cong cfg E hext) prims t vu lastProps incoming
    txs ownCong

end ReexecV3D3
