import ZkFormal.NearV3.Render.Ups.CompactExtract.Plan
import ZkFormal.NearV3.Render.Ups.CompactExtract.FreshTraffic
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open NearSpec Assembly ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows UpsGen
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
    {ps : List (Nat×Nat)} {fls : List (List (Nat×Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat→Nat}
    (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

theorem partRow {i : Nat} (h1 : 4≤i) (h2 : i<s.rows.length) :
    ∃k,∃hk:k<ps.length,ps[k].1≤i ∧ i<ps[k].1+ps[k].2 :=
  consec_find ps 4 hL.consec i h1 (by rw [hL.cover]; exact h2)

theorem partPc (k : Nat) (hk : k<ps.length) (d : Nat) (hd : d<ps[k].2)
    {x : Nat} (hx : x∈partConst) : s.row (ps[k].1+d) x=s.row ps[k].1 x :=
  ((hL.part k hk).2.rows d hd).2.2.2.2 x hx
end

/-- Existing node SHA contract, now using compact physical BYTES plus Codec
slot-zero relays. Relay jobs cannot alias any positive-index node part. -/
theorem sha_seg {v : List UpsSeg} (hw : Wf v) {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (taus : List Nat) (values : Nat→NearSpec.Bytes) (others : List Msg)
    (htaus : ∀t∈taus,t<32) (hbytes : ∀ m, shaR B_BYTES m = cnt (taus.flatMap (fun t=>relayValueMsgs t (values t)) ++ (upsTraffic v).sends B_BYTES ++ others) m)
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdig : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (htau : UpsTauDistinct v) (hB : CompactIdBound v) :
    ∀ s ∈ v, ∀ ps fls ws, UpsLayout s ps fls ws → UpsShaSeg s ps := by
  intro s hs ps fls ws hL i hi hg k hk hI hLn
  obtain ⟨hτ, hps⟩ := hB s hs
  have hps' := hps ps fls ws hL
  have hlen := lenLe hw hs
  have U := (hL.part k hk).2
  have hle := U.le
  have hencL : (rowsB s ps[k].1 ps[k].2).length = ps[k].2 := by simp [rowsB]
  -- the lookup is provided
  have hrecv : 0 < shaS B_DIGEST (digMsg (upsIdN (s.row 0 tau) (k + 1)) (rowsB s ps[k].1 ps[k].2).length
      (regN (s.row i))).toFp := by
    have := hdig _ (mem_upsRecvs.2 ⟨s, hs, i, hi, digest_member (rowLt hw hs i) hg⟩)
    rwa [hI, hLn, ← hencL] at this
  -- the sends with this id are the part's bytes
  have hS : ∀ m ∈ (upsTraffic v).sends B_BYTES ++ (taus.flatMap (fun t=>relayValueMsgs t (values t)) ++ others), ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (upsIdN (s.row 0 tau) (k + 1)) →
      ∃ d, d < (rowsB s ps[k].1 ps[k].2).length ∧ m = [upsIdN (s.row 0 tau) (k + 1), d, (rowsB s ps[k].1 ps[k].2).getD d 0] := by
    intro m hm a ha he
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨s', hs', i', hi', hm'⟩ := mem_upsSends.1 hm
      obtain ⟨ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
      obtain ⟨ci', ti', di', si', kd', sdx', hP'⟩ := ups_plan hw hs' hL'
      obtain ⟨hτ', hps2⟩ := hB s' hs'
      have hps2' := hps2 ps' fls' ws' hL'
      rcases Nat.lt_or_ge i' 4 with h4 | h4
      · rw [hL'.msgsW i' h4 B_BYTES true] at hm'
        simp [B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP] at hm'
      · rw [hL'.msgsQ i' h4 hi' B_BYTES true] at hm'
        simp [B_BYTES, B_DIGEST, B_UPB, B_MEMD] at hm'
        subst hm'
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        obtain ⟨k', hk', e1, e2⟩ := partRow hw hs' hL' hP' h4 hi'
        have hj : s'.row i' j = k' + 1 := by
          rw [show i' = ps'[k'].1 + (i' - ps'[k'].1) by omega, partPc hw hs' hL' hP' k' hk' _ (by omega) (by decide)]
          exact (hL'.part k' hk').1
        have e := Link.ofNat_inj (upsIdN_lt _ _) (upsIdN_lt _ _) he
        rw [hL'.segc _ hi' tau (by decide), hj] at e
        obtain ⟨et, ek⟩ := upsIdN_inj (by omega) (by omega) (by omega) (by omega) e
        have hss : s' = s := htau s' hs' s hs et
        subst hss
        -- the row in the given layout
        have hqi : s'.row i' qb = 1 := by
          have := ((hL'.part k' hk').2.rows (i' - ps'[k'].1) (by omega)).1
          rwa [show ps'[k'].1 + (i' - ps'[k'].1) = i' by omega] at this
        obtain ⟨ci0, ti0, di0, si0, kd0, sdx0, hP0⟩ := ups_plan hw hs hL
        obtain ⟨k'', hk'', f1, f2⟩ := partRow hw hs hL hP0 h4 hi'
        have hj' : s'.row i' j = k'' + 1 := by
          rw [show i' = ps[k''].1 + (i' - ps[k''].1) by omega, partPc hw hs hL hP0 k'' hk'' _ (by omega) (by decide)]
          exact (hL.part k'' hk'').1
        have hkk : k'' = k := by omega
        subst hkk
        have hτi : s'.row i' tau = s'.row 0 tau := hL.segc _ hi' tau (by decide)
        have hd := (U.rows (i' - ps[k''].1) (by omega)).2.1
        rw [show ps[k''].1 + (i' - ps[k''].1) = i' by omega] at hd
        refine ⟨i' - ps[k''].1, by rw [hencL]; omega, ?_⟩
        rw [hτi, hj', hd]
        simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (show i' - ps[k''].1 < ps[k''].2 by omega), Option.map_some, Option.getD_some]
        rw [show ps[k''].1 + (i' - ps[k''].1) = i' by omega]
    · rcases List.mem_append.mp hm with hm|hm
      · obtain ⟨t,ht,hm⟩:=List.mem_flatMap.mp hm
        obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hm
        simp only [List.head?_cons,Option.some.injEq] at ha
        subst a
        have hid : upsertJobId t 0<P := by
          have := upsertJobId_bound (htaus t ht) (by decide : 0<512)
          have : 262144<P := by decide
          omega
        have e:=Link.ofNat_inj hid (upsIdN_lt _ _) he
        rw [upsIdN_val (by omega) (by omega)] at e
        unfold upsertJobId at e
        have ht':=htaus t ht
        omega
      · obtain ⟨h1,h2⟩:=hoth m hm a ha
        have e:=Link.ofNat_inj h1 (upsIdN_lt _ _) he
        rw [e,upsIdN_val (by omega) (by omega)] at h2
        unfold K_VUPS at h2
        omega
  have hbytes' : ∀m,shaR B_BYTES m=cnt ((upsTraffic v).sends B_BYTES ++
      (taus.flatMap (fun t=>relayValueMsgs t (values t)) ++ others)) m := by
    intro m
    rw [hbytes]
    simp only [cnt,List.map_append,List.count_append]
    omega
  have core := Link.sha_core hsha _ hbytes'  (upsIdN_lt _ _) (fun x hx => by
      simp only [rowsB, List.mem_map, List.mem_range] at hx
      obtain ⟨d, -, rfl⟩ := hx; exact rowLt hw hs _ _)
    (by rw [hencL, P_lit]; omega) (fun x hx => by
      simp only [regN, List.mem_map, List.mem_range] at hx
      obtain ⟨d, -, rfl⟩ := hx; exact rowLt hw hs _ _) hS hrecv
  refine ⟨fun d hd => core.1 _ (by simp only [rowsB, List.mem_map, List.mem_range]; exact ⟨d, hd, rfl⟩), ?_⟩
  rw [core.2]; rfl



end ZkFormal.NearV3.Render.UpsRelay.Extract
