import StateM5a.StSound

/-!
# StateM5a.StSoundW — the working-set accesses are STATE writes (toward `committed ~ cs`)

On the M5b AIR every active `WSA` row (the working-set access `WsDecode2.wsaRow`, whose list
`wsa tr pub` is what `WsEntries.ws_entries`' memory chains `accOf (wsa tr pub) (seg, kd)` range
over) received its `WRITE` message from an `STW` row (`StSound.write_recv`), so:

* **`wsa_write`** / **`wsa_mem_write`**: the access's key digest is `kd = pairs (sha256 key)` and its
  written value is `new = [pr, |val|] ++ pairs (sha256 val) ++ [1]` (a write, `pr = 1`) or
  `[0, 0] ++ 0^16 ++ [1]` (a remove), for an execution-side request
  `SREQ(t, pr, seg, klen, kptr, vlen, vptr)` with the access's own time `t` and segment `seg`, `key`
  the `klen` bytes the call read at `kptr` and `val` the `vlen` bytes at `vptr` (`HB`).

* **`wsa_key`** (`Sha256CR`, named hypothesis): an access whose key digest is `pairs (sha256 K)`
  (e.g. `K = keyBytes tr kid`, the INTAKE key, `KeyDigest.wsb_kd`) read exactly the bytes `K`.

With `ws_entries` (each touched leaf's closing value is `lastVal` of its accesses in time order)
this identifies every FINAL value as the latest request's value digest for that key digest.
-/

namespace StateM5a.StSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.Tape StateM5a.M5b StateM5a.WsDecode2 StateM5a.WsBus NearSpec

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {host : List (Nat × Bool × List Nat)}
  {prev post : NearSpec.Bytes} {n : Nat}

theorem pairs_sha_len (x : Bytes) : (pairs (sha256 x)).length = 16 := by
  rw [pairs_length, show (sha256 x).length = 32 from ArenaCore.sha256_length x]

/-- **A `WSA` access is a STATE write.** -/
theorem wsa_write (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {r : Nat} (hr : r < tr.height 7) (hA : (Wsa.c "act").eval tr 7 r pub = 1) :
    ∃ pr klen kptr vlen vptr : Fp,
      [(Wsa.c "t").eval tr 7 r pub, pr, (Wsa.c "seg").eval tr 7 r pub, klen, kptr, vlen, vptr] ∈
        busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SREQ true ∧
      ∃ (key : Bytes) (dv : List Nat), key.length = klen.toNat ∧
        HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ((Wsa.c "t").eval tr 7 r pub) kptr key ∧
        ((pr = 1 ∧ ∃ val : Bytes, val.length = vlen.toNat ∧
            HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ((Wsa.c "t").eval tr 7 r pub) vptr val ∧
            dv = pairs (sha256 val)) ∨
          (pr = 0 ∧ vlen = 0 ∧ dv = List.replicate 16 0)) ∧
        (wsaRow tr pub r).kd = pairs (sha256 key) ∧
        (wsaRow tr pub r).new = [pr.toNat, vlen.toNat] ++ dv ++ [1] := by
  have hi : rcv B_WRITE (Wsa.c "act") ([Wsa.c "seg", Wsa.c "t"] ++ Wsa.vec "kd" 16 ++ [Wsa.c "ncp", Wsa.c "ncl"] ++
      Wsa.vec "ncv" 16) ∈ ((fullAir D (m5bX host prev post n) nb np).tables[7]!).interactions := by
    rw [WsDecode.full_wsa]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
  have h1 := WsDecode.mem_busList _ (by rw [WsDecode.full_len]; omega) hi hr (WsDecode.mult_one hA)
  obtain ⟨ts, pr, seg, klen, kptr, vlen, vptr, hq, key, dv, hkl, hkb, hcase, hw⟩ := write_recv hh hH h1
  have hL : ((rcv B_WRITE (Wsa.c "act") ([Wsa.c "seg", Wsa.c "t"] ++ Wsa.vec "kd" 16 ++
      [Wsa.c "ncp", Wsa.c "ncl"] ++ Wsa.vec "ncv" 16)).msgVal tr 7 r pub).map Fp.toNat =
      ([ev tr 7 r pub (Wsa.c "seg"), ev tr 7 r pub (Wsa.c "t")] ++ vecN tr pub 7 r (fun j => Wsa.c "kd" j) 16 ++
        [ev tr 7 r pub (Wsa.c "ncp"), ev tr 7 r pub (Wsa.c "ncl")]) ++ vecN tr pub 7 r (fun j => Wsa.c "ncv" j) 16 := by
    simp only [rcv, Interaction.msgVal, List.map_append, List.map_cons, List.map_nil, List.map_map, Wsa.vec, vecN]
    rfl
  rw [hL] at hw
  have hl1 : ([ev tr 7 r pub (Wsa.c "seg"), ev tr 7 r pub (Wsa.c "t")] ++ vecN tr pub 7 r (fun j => Wsa.c "kd" j) 16 ++
      [ev tr 7 r pub (Wsa.c "ncp"), ev tr 7 r pub (Wsa.c "ncl")]).length =
      ([seg.toNat, ts.toNat] ++ pairs (sha256 key) ++ [pr.toNat, vlen.toNat]).length := by
    simp [vecN, pairs_sha_len]
  obtain ⟨hw1, hdv⟩ := List.append_inj hw hl1
  obtain ⟨hw2, hpv⟩ := List.append_inj hw1 (by simp [vecN, pairs_sha_len])
  obtain ⟨hw3, hkd⟩ := List.append_inj hw2 rfl
  simp only [List.cons.injEq, and_true] at hw3 hpv
  obtain ⟨eseg, ets⟩ := hw3
  obtain ⟨epr, evl⟩ := hpv
  have ets' : ts = (Wsa.c "t").eval tr 7 r pub := Fp.ext ets.symm
  have eseg' : seg = (Wsa.c "seg").eval tr 7 r pub := Fp.ext eseg.symm
  subst ets' eseg'
  refine ⟨pr, klen, kptr, vlen, vptr, hq, key, dv, hkl, hkb, hcase, hkd, ?_⟩
  show [ev tr 7 r pub (Wsa.c "ncp"), ev tr 7 r pub (Wsa.c "ncl")] ++ vecN tr pub 7 r (fun j => Wsa.c "ncv" j) 16 ++ [1] = _
  rw [epr, evl, hdv]

/-- **Every working-set access (`wsa tr pub`) is a STATE write.** -/
theorem wsa_mem_write (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    {a : WsaRow (List Nat) (List Nat)} (ha : a ∈ wsa tr pub) :
    ∃ ts pr seg klen kptr vlen vptr : Fp, ts.toNat = a.t ∧ seg.toNat = a.seg ∧
      [ts, pr, seg, klen, kptr, vlen, vptr] ∈
        busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SREQ true ∧
      ∃ (key : Bytes) (dv : List Nat), key.length = klen.toNat ∧
        HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ts kptr key ∧
        ((pr = 1 ∧ ∃ val : Bytes, val.length = vlen.toNat ∧
            HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ts vptr val ∧ dv = pairs (sha256 val)) ∨
          (pr = 0 ∧ vlen = 0 ∧ dv = List.replicate 16 0)) ∧
        a.kd = pairs (sha256 key) ∧ a.new = [pr.toNat, vlen.toNat] ++ dv ++ [1] := by
  simp only [wsa, actRows, List.mem_filterMap, List.mem_range] at ha
  obtain ⟨r, hr, h⟩ := ha
  split at h
  · rename_i hA
    obtain rfl := Option.some.inj h
    obtain ⟨pr, klen, kptr, vlen, vptr, hq, key, dv, hkl, hkb, hcase, hkd, hnew⟩ := wsa_write hh hH hr hA
    exact ⟨_, pr, _, klen, kptr, vlen, vptr, rfl, rfl, hq, key, dv, hkl, hkb, hcase, hkd, hnew⟩
  · exact absurd h (by simp)

/-- 16-bit limbs of SHA-256 digests identify the message (`Sha256CR`). -/
theorem pairs_sha_inj (hCR : Walk.Sha256CR) {a b : Bytes} (h : pairs (sha256 a) = pairs (sha256 b)) :
    a = b := by
  apply hCR
  have ha : (sha256 a).length % 2 = 0 := by rw [ArenaCore.sha256_length]
  have hb : (sha256 b).length % 2 = 0 := by rw [ArenaCore.sha256_length]
  rw [← limbBytes_pairs _ ha, h, limbBytes_pairs _ hb]

/-- **An access to an entry whose key digest is `pairs (sha256 K)` read exactly the key bytes `K`**
(e.g. `K = keyBytes tr kid` of the INTAKE row, `KeyDigest.wsb_kd`), under `Sha256CR`. -/
theorem wsa_key (hh : HostOK host) (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    (hCR : Walk.Sha256CR) {a : WsaRow (List Nat) (List Nat)} (ha : a ∈ wsa tr pub) {K : Bytes}
    (hK : a.kd = pairs (sha256 K)) :
    ∃ ts pr seg klen kptr vlen vptr : Fp, ts.toNat = a.t ∧ seg.toNat = a.seg ∧
      [ts, pr, seg, klen, kptr, vlen, vptr] ∈
        busList (fullAir D (m5bX host prev post n) nb np) tr pub B_SREQ true ∧
      K.length = klen.toNat ∧ HBytes (fullAir D (m5bX host prev post n) nb np) tr pub ts kptr K := by
  obtain ⟨ts, pr, seg, klen, kptr, vlen, vptr, h1, h2, hq, key, -, hkl, hkb, -, hkd, -⟩ := wsa_mem_write hh hH ha
  obtain rfl := pairs_sha_inj hCR (hkd.symm.trans hK)
  exact ⟨ts, pr, seg, klen, kptr, vlen, vptr, h1, h2, hq, hkl, hkb⟩

end

end StateM5a.StSound
