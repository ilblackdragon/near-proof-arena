import ZkFormal.NearV3.Render.HeadRender
import ZkFormal.NearV3.Render.ValRender
import ZkFormal.NearV3.Rcpt.Render.BndRender
import ZkFormal.NearV3.Rcpt.Render.AkeyRender
import ZkFormal.Size.PadHeader

/-!
# Concrete aligned generators

Each theorem checks local constraints and the complete bus traffic of a
constructed array-backed trace. Caps are explicit proposed v3 assembly caps;
this module does not change the existing table definitions or their soundness
views. Other tables and the assembled HoldsP proof remain to be completed.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size

/-- An array-backed trace for a single generated table. The same table can be
placed at any index; assembly selects one such row array for each table. -/
def rowsTrace (log : Nat) (rows : Array Row) : Trace Fp :=
  ⟨fun _ => log, fun _ r c => Fp.ofNat ((rows.getD r #[]).getD c 0)⟩

theorem rowsTrace_mkTab (log width : Nat) (cell : Nat → Nat → Nat)
    (t r c : Nat) (hr : r < 2 ^ log) (hc : c < width) :
    (rowsTrace log (mkTab (2 ^ log) width cell)).cell t r c = Fp.ofNat (cell r c) := by
  unfold rowsTrace
  dsimp only
  rw [mkTab_get hr hc]

/-- The padded height fits the rows and has the arity-8 residue. -/
theorem padded_log_fits (n : Nat) (h : n ≤ 2 ^ 22) :
    n ≤ 2 ^ padLog22 (logOf n) ∧ 1 ≤ padLog22 (logOf n) ∧
      padLog22 (logOf n) ≤ 22 ∧ padLog22 (logOf n) % 3 = 1 := by
  have hl : 1 ≤ logOf n ∧ logOf n ≤ 22 := ⟨one_le_logOf _, logOf_le (by decide) h⟩
  have hp := padLog22_bounds (logOf n) hl
  exact ⟨Nat.le_trans (le_pow_logOf _) (Nat.pow_le_pow_right (by decide) hp.1),
    by omega, hp.2.1, hp.2.2⟩

def headTraceAligned (hs : List HeadE) : Trace Fp :=
  let log := padLog22 (logOf (32 * hs.length))
  rowsTrace log (headRowsAt log hs)

/-- Head table completeness at the rounded height (cap 11 rounds to 13).
The exact same `headTraffic hs` is emitted, including all digest messages. -/
theorem head_aligned_complete (hs : List HeadE) (hok : HeadOk hs) (t : Nat) (pub : List Fp) :
    TableLocal { HeadV3.table with maxLog := 13 } (headTraceAligned hs) t pub ∧
    TableTraffic HeadV3.interactions (headTraceAligned hs) t pub (headTraffic hs) ∧
    (headTraceAligned hs).log t % 3 = 1 := by
  have hl : logOf (32 * hs.length) ≤ 11 := logOf_le (by decide) hok.cap
  have hh := padded_log_fits (32 * hs.length) (Nat.le_trans hok.cap (by decide))
  have hlog : 1 ≤ (headTraceAligned hs).log t ∧ (headTraceAligned hs).log t ≤ 13 := by
    change 1 ≤ padLog22 (logOf (32 * hs.length)) ∧ padLog22 (logOf (32 * hs.length)) ≤ 13
    unfold padLog22 at *
    omega
  have hcell : ∀ r x, r < (headTraceAligned hs).height t → x < HeadV3.width →
      (headTraceAligned hs).cell t r x = Fp.ofNat
        (HeadGen.cell hs ((headTraceAligned hs).height t) r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨head_render_local_at hs hok _ t pub 13 hlog hh.1 hcell,
    head_render_traffic_at hs hok _ t pub hh.1 hcell, hh.2.2.2⟩

def valRowsAt (log : Nat) (es : List ValE) : Array Row :=
  mkTab (2 ^ log) ValV3.width (ValGen.cell es (2 ^ log))

def valTraceAligned (es : List ValE) : Trace Fp :=
  let log := padLog22 (logOf (ValGen.R es + 1))
  rowsTrace log (valRowsAt log es)

/-- Value table completeness after padding, preserving byte and SUM traffic. -/
theorem val_aligned_complete (es : List ValE) (hok : ValOk es) (t : Nat) (pub : List Fp) :
    TableLocal ValV3.table (valTraceAligned es) t pub ∧
    TableTraffic ValV3.interactions (valTraceAligned es) t pub (valTraffic es) ∧
    (valTraceAligned es).log t % 3 = 1 := by
  have hh := padded_log_fits (ValGen.R es + 1) hok.wf.rows
  have hcell : ∀ r x, r < (valTraceAligned es).height t → x < ValV3.width →
      (valTraceAligned es).cell t r x = Fp.ofNat
        (ValGen.cell es ((valTraceAligned es).height t) r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨val_render_local_at es hok _ t pub 22 ⟨hh.2.1, hh.2.2.1⟩ hh.1 hcell,
    val_render_traffic_at es hok _ t pub hh.1 hcell, hh.2.2.2⟩

/-- A requested aligned cap bounds the rounded generator height. -/
theorem padded_log_le (n cap : Nat) (hcap : 1 ≤ cap ∧ cap ≤ 22)
    (hr : cap % 3 = 1) (hn : n ≤ 2 ^ cap) : padLog22 (logOf n) ≤ cap :=
  padLog22_le _ cap (logOf_le hcap.1 hn) hcap.2 hr

def bndTraceAligned (es : List BndE) : Trace Fp :=
  let log := padLog22 (logOf es.length)
  rowsTrace log (mkTab (2 ^ log) BndV3.width (BndGen.cell es))

/-- The boundary table pads within its existing cap 13 and preserves traffic. -/
theorem bnd_aligned_complete (es : List BndE) (hn : es.length ≤ 2 ^ BndV3.maxLog)
    (t : Nat) (pub : List Fp) :
    TableLocal BndV3.table (bndTraceAligned es) t pub ∧
    TableTraffic BndV3.interactions (bndTraceAligned es) t pub (bndTraffic es) ∧
    (bndTraceAligned es).log t % 3 = 1 := by
  have hh := padded_log_fits es.length (Nat.le_trans hn (by decide))
  have hl := padded_log_le es.length BndV3.maxLog (by decide) (by decide) hn
  have hc : ∀ r x, r < (bndTraceAligned es).height t → x < BndV3.width →
      (bndTraceAligned es).cell t r x = Fp.ofNat (BndGen.cell es r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨bnd_render_local_at es _ t pub BndV3.maxLog ⟨hh.2.1, hl⟩ hc,
    bnd_render_traffic_at es _ t pub hh.1 hc, hh.2.2.2⟩

def akeyTraceAligned (es : List AkeyE) : Trace Fp :=
  let log := padLog22 (logOf (9 * es.length))
  rowsTrace log (mkTab (2 ^ log) AkeyV3.width (AkeyGen.cell es))

/-- The access-key table pads within its existing cap 16 and preserves traffic. -/
theorem akey_aligned_complete (es : List AkeyE) (hok : AkeyOk es) (t : Nat) (pub : List Fp) :
    TableLocal AkeyV3.table (akeyTraceAligned es) t pub ∧
    TableTraffic AkeyV3.interactions (akeyTraceAligned es) t pub (akeyTraffic es) ∧
    (akeyTraceAligned es).log t % 3 = 1 := by
  have hh := padded_log_fits (9 * es.length) (Nat.le_trans hok.rows (by decide))
  have hl := padded_log_le (9 * es.length) AkeyV3.maxLog (by decide) (by decide) hok.rows
  have hc : ∀ r x, r < (akeyTraceAligned es).height t → x < AkeyV3.width →
      (akeyTraceAligned es).cell t r x = Fp.ofNat (AkeyGen.cell es r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨akey_render_local_at es hok _ t pub AkeyV3.maxLog ⟨hh.2.1, hl⟩ hh.1 hc,
    akey_render_traffic_at es _ t pub hh.1 hc, hh.2.2.2⟩

end ZkFormal.NearV3.Render
