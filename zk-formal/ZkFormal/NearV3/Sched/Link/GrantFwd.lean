import ZkFormal.NearV3.Sched.Link.GrantFin
import ZkFormal.NearV3.Sched.Link.SoundProc

/-!
# ZkFormal.NearV3.Sched.Link.GrantFwd — the τ = 0 forwarding check (stage E step c)

On every record end of instance 0's codec block the codec receives the public forwarding record
`SPUBB (0, 4, k_lo, k_hi, ft₀, ft₁, ft₂)` and sends `SCMP (gfin + gb, ft, 1)` (`codec_rec_msgs`).

* `fwdDemand fwd l`: the demand `render` writes for link `l` (`fwdRecs`, 0 if absent);
* **`fwd_msg`**: a public `SPUBB` record with tag 4 is `fwdRecs`' record of a link `l < n₀²`;
* **`codec_kidx`**: on a record row, `k_lo + 256·k_hi ≡ k` (constraint `kR·(kidx − k_lo − 256·k_hi)`);
* **`Dist.cell_gb_lt`**, **`codec_gb_lt`**: the distribute cell's grant, hence the codec's `gb`
  (received on `SDG`), is `< 2^23` (`gb = min(q₁, q₂)` with 23-bit quotients when allowed, `0`
  otherwise);
* **`codec_fwd`**: in instance 0, with `gfin ≤ 4,500,000` (from `codec_gfin` + `GInv`), the
  comparator operands are `< 2^29`, so `cmp_sound` with bit 1 gives
  `fwdDemand fwd k mod 2^24 ≤ gfin + gb`. The record holds the demand as three bytes, so a
  demand `≥ 2^24` is seen modulo `2^24` (flagged: the renderer must reject such demands).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- The forwarding demand `render` writes for link `l` (`fwdRecs`). -/
def fwdDemand (fwd : List (Nat × Nat)) (l : Nat) : Nat :=
  ((fwd.find? (·.1 == l)).map (·.2)).getD 0

theorem b3_mod (x : Nat) : x % 256 + 256 * (x / 256 % 256) + 65536 * (x / 65536 % 256) = x % 2 ^ 24 := by
  omega

/-- A public `SPUBB` record matching `(0, 4, k_lo, k_hi, t₀, t₁, t₂)` is the forwarding record of a
link `l < n₀²`. -/
theorem fwd_msg {Ps : List InstPub} {fwd : List (Nat × Nat)}
    {M : List Fp} (hM : M ∈ (render Ps fwd).pubb.map (·.map Fp.ofNat))
    {klo khi x0 x1 x2 : Nat} (hlo : klo < 2013265921) (hhi : khi < 2013265921) (h0 : x0 < 2013265921)
    (h1 : x1 < 2013265921) (h2 : x2 < 2013265921)
    (e : M = [0, TAG_FWD, klo, khi, x0, x1, x2].map Fp.ofNat) :
    ∃ l, l < (Ps.getD 0 instD).n * (Ps.getD 0 instD).n ∧ klo = l % 256 ∧ khi = l / 256 % 256 ∧
      x0 + 256 * x1 + 65536 * x2 = fwdDemand fwd l % 2 ^ 24 := by
  subst e
  obtain ⟨r, hr, hre⟩ := List.mem_map.1 hM
  rw [render_pubb, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨τ', -, hr⟩ | hr
  · rw [List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [keyRecs, List.mem_map] at hr
      obtain ⟨k, -, rfl⟩ := hr
      simp only [List.map_cons, List.cons.injEq] at hre
      exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_FWD, TAG_KEY])
    · simp only [ashRecs, List.mem_map] at hr
      obtain ⟨k, -, rfl⟩ := hr
      simp only [List.map_cons, List.cons.injEq] at hre
      exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_FWD, TAG_ASH])
  · simp only [fwdRecs, List.mem_map, List.mem_range] at hr
    obtain ⟨l, hl, rfl⟩ := hr
    simp only [b2, b3, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.cons.injEq] at hre
    obtain ⟨-, -, e2, e3, e4, e5, e6, -⟩ := hre
    have q2 := ofNat_inj' (by omega) hlo e2
    have q3 := ofNat_inj' (by omega) hhi e3
    have q4 := ofNat_inj' (by omega) h0 e4
    have q5 := ofNat_inj' (by omega) h1 e5
    have q6 := ofNat_inj' (by omega) h2 e6
    refine ⟨l, hl, q2.symm, q3.symm, ?_⟩
    rw [← q4, ← q5, ← q6]
    exact b3_mod _

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- On every row of record `k`, `k_lo + 256·k_hi ≡ k`. -/
theorem codec_kidx (hL : CLocal tr t pub) {f k o : Nat} (R : RRow tr t f k o) :
    ∃ q : Int, (k : Int) - ((cv tr t (f + 5 + 24 * k + o) klo : Int) +
      256 * (cv tr t (f + 5 + 24 * k + o) khi : Int)) = 2013265921 * q := by
  obtain ⟨hw, hkR, -, -, hki, -, -⟩ := R
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c kR) (sub (c kidx) (.add (c klo) (smul 256 (c khi)))))
    (by simp [constraints, cRec])
  zs c1 [hkR]
  exact ⟨q, by omega⟩

end Codec

namespace Dist
variable {tr : Trace Fp} {td : Nat} {pub : List Fp}

set_option maxRecDepth 8000 in
/-- **A cell's grant is below `2^23`.** -/
theorem cell_gb_lt (hL : DLocal tr td pub) {r : Nat} (hr : r < tr.height td) (hc : cv tr td r kC = 1) :
    cv tr td r gb < 2 ^ 23 := by
  have hal := bool_of hL hr (x := al) (by simp [boolCols])
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hal with h0 | h1
  · have h := hL.zc hr (e := .mul (c kC) (.mul (notE (c al)) (c gb))) (by simp [constraints, cGrid])
    simp only [notE, zev_mul, zev_sub, zev_k, zev_c, cur_cv, hc, h0] at h
    have := cv_lt (tr := tr) (t := td) r gb
    have := h (by omega) (by omega)
    omega
  · obtain ⟨-, -, -, -, -, -, hg⟩ := cell_div hL hr h1
    obtain ⟨hq1, hq2, -, -⟩ := ranges hL hr
    rw [hg]; split <;> omega

end Dist

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd tcd tcmp : Nat}

/-- **The codec's `gb` is below `2^23`** (received on `SDG` from a distribute cell). -/
theorem codec_gb_lt (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (OS : ScanOwn AP tsd tp)
    (IO : InitOwn AP tcd tsd) {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN) :
    cv tr tcd (f + 5 + 24 * k + 23) Codec.gb < 2 ^ 23 := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨m12, msg12, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  have hw0 : f + 5 + 24 * k < tr.height tcd := (RR k hk 0 (by omega)).1
  obtain ⟨r', hr', i', hi', hb', -, hmsg, hm'⟩ := recv_matched hH OS.lt IO.dgOnly IO.dgPub OC.lt hw0
    (by rw [OC.tab]; exact codec_mem 12 (by decide)) (by rw [Codec.i12_def]) (by rw [Codec.i12_def])
    (by rw [m12]; exact Nat.one_ne_zero)
  rw [OS.tab] at hi'
  have e9 := ScanDist.sdg_i i' hi' hb'
  subst e9
  have hSD := sd_local hH OS
  have hkC : cv tr tsd r' Dist.kC = 1 := Codec.one_of_mult (i := ScanDist.interactions[9]!) rfl hm'
  rw [ScanDist.sdg_msg, msg12] at hmsg
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨-, -, -, t3, -⟩ := hmsg
  rw [← ofNat_inj' (cv_lt _ _) (cv_lt _ _) t3]
  exact Dist.cell_gb_lt (Dist.DLocal.of_sd hSD) hr' hkC

/-- **The forwarding check of instance 0**: at record `k`, the public demand (mod `2^24`) is at most
`gfin + gb`. -/
theorem codec_fwd (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (OS : ScanOwn AP tsd tp)
    (IO : InitOwn AP tcd tsd) (CO : CmpOwn AP tcmp) (PB : PubbOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb) (hn0 : (Ps.getD 0 instD).n ≤ 64)
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1) (h0 : cv tr tcd f Codec.tau = 0)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN)
    (hgf : cv tr tcd (f + 5 + 24 * k + 23) Codec.gfin ≤ 4500000) :
    fwdDemand fwd k % 2 ^ 24 ≤
      cv tr tcd (f + 5 + 24 * k + 23) Codec.gfin + cv tr tcd (f + 5 + 24 * k + 23) Codec.gb := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfw, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  obtain ⟨m15, msg15, m9, msg9⟩ := hfw h0
  have hgb := codec_gb_lt hH OC OS IO hf hF hk
  have hw : f + 5 + 24 * k + 23 < tr.height tcd := (RR k hk 23 (by omega)).1
  -- the public record
  have hp := recv_pub hH PB.none PB.pub OC.lt hw
    (by rw [OC.tab]; exact codec_mem 9 (by decide)) (by rw [Codec.i9_def]) (by rw [Codec.i9_def])
    (by rw [m9]; exact Nat.one_ne_zero)
  rw [I.count, hrecB, msg9] at hp
  have hmem := List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
  obtain ⟨l, hl, elo, ehi, eft⟩ := fwd_msg hmem (cv_lt _ _) (cv_lt _ _) (cv_lt _ _) (cv_lt _ _) (cv_lt _ _) rfl
  have hnn := Nat.mul_le_mul hn0 hn0
  -- the record index
  have hkl : k = l := by
    obtain ⟨q, hm⟩ := Codec.codec_kidx hL (RR k hk 23 (by omega))
    have hx : cv tr tcd (f + 5 + 24 * k + 23) Codec.klo + 256 * cv tr tcd (f + 5 + 24 * k + 23) Codec.khi = l := by
      rw [elo, ehi]; omega
    have hx' : ((cv tr tcd (f + 5 + 24 * k + 23) Codec.klo : Nat) : Int) +
        256 * ((cv tr tcd (f + 5 + 24 * k + 23) Codec.khi : Nat) : Int) = (l : Int) := by omega
    rw [hx'] at hm
    have hkP : k < 2013265921 := by have := cv_lt (tr := tr) (t := tcd) f Codec.NN; omega
    have hl' : l < 4096 := by omega
    omega
  subst hkl
  -- the comparison
  have hft : (cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 0) + 256 * cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 1) +
      65536 * cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 2)) < 2 ^ 24 := by
    rw [eft]; exact Nat.mod_lt _ (by decide)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at msg15
  simp only [List.map_cons, List.map_nil] at msg15
  have ex := toNat_ofNat_lt' (show cv tr tcd (f + 5 + 24 * k + 23) Codec.gfin +
    cv tr tcd (f + 5 + 24 * k + 23) Codec.gb < 2013265921 by omega)
  have ey := toNat_ofNat_lt' (show cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 0) +
    256 * cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 1) + 65536 * cv tr tcd (f + 5 + 24 * k + 23) (Codec.fb 2) <
      2013265921 by omega)
  have hc := cmp_sound hH CO OC.lt hw (by rw [OC.tab]; exact codec_mem 15 (by decide))
    (by rw [Codec.i15_def]) (by rw [Codec.i15_def]) (by rw [m15]; exact Nat.one_ne_zero) msg15
    (by rw [ex]; omega) (by rw [ey]; omega)
  rw [ex, ey] at hc
  rcases hc with ⟨-, h⟩ | ⟨h, -⟩
  · rw [← eft]; exact h
  · have := congrArg Fp.toNat h
    rw [toNat_ofNat_lt' (by decide), Fp.toNat_zero] at this
    exact absurd this (by decide)

end

end ZkFormal.NearV3.Sched
