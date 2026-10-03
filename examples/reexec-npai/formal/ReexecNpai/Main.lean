import ReexecNpai.Spec.Receipts
import ReexecNpai.Spec.Parse
import ReexecNpai.Spec.Hash
import ReexecNpai.Spec.Batch
import ReexecNpai.Spec.Final
import ReexecNpai.Model
import NpaiIR.Adequacy
import NpaiIR.Encode

/-!
# Main theorem: the bytecode computes `check`

`interpVerify code fuel pub cb pb = check cb pb` for every `fuel ≥ FUEL`
(and public tape shorter than `2^32`): soundness from the phase `wp` lemmas,
completeness (with the fuel bound) from the phase `twp` lemmas.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem body_eq : body = .seq pSetup (.seq pClaim (.seq pProof (.seq pReceipts (.seq pParse
    (.seq pHash (.seq (pRootIs (CLM + 117)) (.seq pBatch pFinal))))))) := rfl

/-- The claim region holds the fixed-offset fields. -/
theorem claim_seg {cb : Bytes} {m : M} (h : ClaimIn cb m) (o n : Nat) (hn : o + n ≤ 309) :
    readMem m.mem (CLM + o) n = seg cb o n := by
  have := h.claim
  apply List.ext_getElem (by simp [seg]; have := h.shape.1; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  rw [readMem_getElem]
  have h3 := mem_of_readMem this (o + i) (by omega)
  rw [Nat.add_assoc, h3]
  have hl := h.shape.1
  simp [seg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o + i < cb.length by omega)]

/-- Everything the phases establish implies `check`. -/
theorem check_of {cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {acc : Acc}
    (hs : claimShape cb) (hr : RcptsOK cb pb rs R) (ht : TrieOK pb R A K)
    (hroot : (rootT A K (vals0 pb A)).hashOf = (claimOf cb).preStateRoot)
    (hb : runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc)
    (ho : Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb)) : check cb pb = true := by
  unfold check
  rw [decode_of_shape hs]
  simp only
  have hdp : decodeProof pb = some ⟨rs, rootT A K (vals0 pb A)⟩ := by
    unfold decodeProof readU32
    have h4 := readLE_drop pb 0 4 (by omega)
    simp only [List.drop_zero, Nat.zero_add] at h4
    rw [h4, if_pos hr.n4]
    simp only
    rw [hr.count, hr.dec]
    simp only [Option.map_eq_some_iff]
    exact ⟨_, ht.dec, rfl⟩
  rw [hdp]
  simp only [decide_eq_true_eq]
  obtain ⟨-, hwf, -⟩ := decTrie_some ht.dec
  have hc := hr.cnt_claim
  refine ⟨⟨claimOf_wf hs, rfl, rfl, hc, by rw [← hc]; exact hr.n_pos, by rw [← hc]; exact hr.n_max,
    by rw [← hc]; exact hr.gas, hr.slice, hr.nodup, hwf, ht.size⟩, hr.commit, hroot, ?_⟩
  show Option.map Outputs.ofAcc (runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs) = _
  rw [hb]
  simp only [Option.map_some, ho]

end ReexecNpai

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem body_okB : body.okB = true := by decide +kernel
theorem body_noHaltB : body.noHaltB = true := by decide +kernel
theorem program_canon : progCanon program = true := by decide +kernel

theorem applyReceipt_lens {ctx : Ctx} {st st' : Acc} {r : Receipt} (h : applyReceipt ctx st r = some st') :
    st'.outcomes.length = st.outcomes.length + 1 ∧ st'.gasBurnt = st.gasBurnt + Params.G := by
  unfold applyReceipt at h
  revert h
  dsimp only
  repeat' (first | (intro h; cases h; done) | (intro h; simp only [Option.some.injEq] at h; subst h; simp; done) | split)

theorem applyAll_lens (ctx : Ctx) : ∀ (rs : List Receipt) (st acc : Acc), applyAll ctx st rs = some acc →
    acc.outcomes.length = st.outcomes.length + rs.length ∧ acc.gasBurnt = st.gasBurnt + rs.length * Params.G
  | [], st, acc, h => by simp [applyAll] at h; subst h; simp
  | r :: rs, st, acc, h => by
    simp only [applyAll] at h
    split at h
    · cases h
    · rename_i st' h1
      have ih := applyAll_lens ctx rs st' acc h
      have h2 := applyReceipt_lens h1
      simp only [List.length_cons]
      constructor
      · omega
      · rw [ih.2, h2.2, Nat.add_mul]; omega

theorem runBatch_lens {ctx : Ctx} {t : PTrie} {rs : List Receipt} {acc : Acc} (h : runBatch ctx t rs = some acc) :
    acc.outcomes.length = rs.length ∧ acc.gasBurnt = rs.length * Params.G := by
  have := applyAll_lens ctx rs _ acc h
  simpa using this

theorem TrieSt.congr {cb pb : Bytes} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    {vals : Nat → Bytes} {m m' : M} (h : TrieSt cb pb rs R A K vals m) (hm : m'.mem = m.mem)
    (h14 : m'.regs 14 = 8) (h15 : m'.regs 15 = 1) : TrieSt cb pb rs R A K vals m' := by
  obtain ⟨⟨⟨⟨_, _, hd⟩, hcl, hs⟩, hok, hrc, hpl, hpe, hn, hre, hrt⟩, htok, ⟨ha, hk, hno, hv, hl, hp, hh⟩⟩ := h
  have r32 : ∀ a, rd32 m' a = rd32 m a := fun a => by simp [rd32, hm]
  refine ⟨⟨⟨⟨h15, h14, (by rw [hm]; exact hd)⟩, (by rw [hm]; exact hcl), hs⟩, hok, (by rw [hm]; exact hrc), hpl,
    (by rw [r32]; exact hpe), (by rw [r32]; exact hn), (by rw [r32]; exact hre), fun i hi => (by rw [hm]; exact hrt i hi)⟩,
    htok, ⟨fun j hj => ?_, fun i hi => (by rw [r32]; exact hk i hi), (by rw [r32]; exact hno),
    fun j hj hv' => (by rw [hm]; exact hv j hj hv'), fun j hj hv' => (by rw [hm]; exact hl j hj hv'),
    fun j hj => (by rw [hm]; exact hp j hj),
    fun j hj => (by rw [hm]; exact hh j hj)⟩⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha j hj
  exact ⟨(by rw [r32]; exact a1), (by rw [r32]; exact a2), (by rw [r32]; exact a3), (by rw [r32]; exact a4),
    (by rw [r32]; exact a5), (by rw [r32]; exact a6)⟩

/-- **Soundness of the body**: a normal exit implies `check`. -/
theorem body_wp {pub cb pb : Bytes} (ht : TapesOK cb pb) :
    wp P (Inp pub cb pb) body (M.init P) (fun _ => check cb pb = true) := by
  have hdata : readMem (M.init P).mem 0 168 = dataSeg := by
    simp only [M.init]
    apply List.ext_getElem (by simp [dataSeg_length])
    intro i h1 h2
    simp [readMem, P, program, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [body_eq]
  simp only [wp_seq]
  refine wp_mono (setup_wp hdata) fun m1 h1 => ?_
  refine wp_mono (claim_wp h1 ht.1) fun m2 h2 => ?_
  refine wp_mono (proof_wp h2 ht.2) fun m3 h3 => ?_
  refine wp_mono (receipts_wp h3 ht) fun m4 ⟨rs, R, h4⟩ => ?_
  refine wp_mono (parse_wp h4) fun m5 ⟨A, K, h5⟩ => ?_
  refine wp_mono (hash_wp h5) fun m6 ⟨h6, hroot6⟩ => ?_
  refine wp_mono (rootIs_wp h6.toBase hroot6 (by decide)) fun m7 ⟨heq, hmem, h14, h15⟩ => ?_
  have h7 : TrieSt cb pb rs R A K (vals0 pb A) m7 := TrieSt.congr h6 hmem h14 h15
  refine wp_mono (batch_wp h7) fun m8 ⟨acc, vals, hb, h8, htr, hbm⟩ => ?_
  obtain ⟨hl, hg⟩ := runBatch_lens hb
  refine wp_mono (final_wp h8 hbm htr hl hg) fun m9 ⟨ho, _⟩ => ?_
  refine check_of h2.shape h4.ok h5.tok ?_ hb ho
  rw [heq, claim_seg h6.toClaimIn 117 32 (by decide)]
  rfl

end ReexecNpai

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- What `check cb pb = true` gives the completeness argument. -/
theorem check_facts {cb pb : Bytes} (h : check cb pb = true) :
    ∃ rs R t acc, claimShape cb ∧ RcptsOK cb pb rs R ∧ decTrie (pb.drop R) = some t ∧
      t.revealedBytes ≤ Params.maxWitnessBytes ∧ t.hashOf = (claimOf cb).preStateRoot ∧
      runBatch (claimOf cb).ctx t rs = some acc ∧ Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb) ∧
      pb.length ≤ PMAX := by
  unfold check at h
  split at h
  · cases h
  rename_i c hdc
  split at h
  · cases h
  rename_i w hdw
  have hrel : NearRelation c.1 w := of_decide_eq_true h
  obtain ⟨⟨hwf, hpv, hch, hlen, hn1, hnmax, hgas, hslice, hnodup, htwf, hsize⟩, hcom, hroot, hrun⟩ := hrel
  obtain ⟨hs, hcc⟩ := shape_of_decode hdc hpv hch
  rw [hcc] at hlen hn1 hnmax hgas hcom hroot hrun
  have hdw' := hdw
  unfold decodeProof at hdw'
  split at hdw'
  · cases hdw'
  rename_i n bs hu
  split at hdw'
  · cases hdw'
  rename_i rs bs' hm
  simp only [Option.map_eq_some_iff] at hdw'
  obtain ⟨t, hdt, rfl⟩ := hdw'
  obtain ⟨hpb, hn⟩ := readLE_some hu
  obtain ⟨hbs, hrl⟩ := readMany_decReceipt_some hm
  have hpbl : pb.length = 4 + (concatAll (rs.map Receipt.encode)).length + bs'.length := by
    rw [hpb, hbs]; simp [leN_length]; omega
  have hd4 : pb.drop 4 = bs := by rw [hpb]; simp [leN_length]
  have hdR : pb.drop (4 + (concatAll (rs.map Receipt.encode)).length) = bs' := by
    have : pb.drop (4 + (concatAll (rs.map Receipt.encode)).length) =
        (pb.drop 4).drop (concatAll (rs.map Receipt.encode)).length := by rw [List.drop_drop]
    rw [this, hd4, hbs]; simp
  have hcount : leNat (sl pb 0 4) = n := by
    rw [hpb]; simp [sl, List.take_append_of_le_length, leN_length, leNat_leN 4 n hn]
  simp only [Option.map_eq_some_iff] at hrun
  obtain ⟨acc, hacc, hout⟩ := hrun
  simp only at hlen hn1 hslice hnodup htwf hsize hcom hroot hacc
  have hok : RcptsOK cb pb rs (4 + (concatAll (rs.map Receipt.encode)).length) :=
    { n4 := by omega
      count := by rw [hcount, hrl]
      dec := by rw [hrl, hd4, hdR]; exact hm
      Rle := by omega
      cnt_claim := hlen
      n_pos := by omega
      n_max := by omega
      gas := by rw [hlen]; exact hgas
      slice := hslice
      nodup := hnodup
      commit := hcom }
  refine ⟨rs, 4 + (concatAll (rs.map Receipt.encode)).length, t, acc, hs, hok,
    by rw [hdR]; exact hdt, hsize, hroot, hacc, hout, ?_⟩
  have hrwf : rs.all Receipt.wf = true := by
    rw [List.all_eq_true] at hslice ⊢
    intro r hr
    have := hslice r hr
    simp only [Receipt.inSlice, Bool.and_eq_true] at this
    exact this.1.1
  have hrsl : rs.length < 4294967296 := by
    have := hok.n_max; simp only [Params.maxBatch] at this; omega
  have henc : Encodable ⟨rs, t⟩ := ⟨hrwf, hrsl, htwf, hsize, (decTrie_some hdt).2.2⟩
  have hl1 := (decodeProof_some hdw).1
  have hl2 := encodeProof_length_le _ henc
  have hl3 := cntT_le t htwf
  have hmx := hok.n_max
  simp only [PMAX, Params.maxWitnessBytes, Params.maxBatch] at hl1 hl2 hl3 hsize hmx ⊢
  omega

end ReexecNpai

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Fuel sufficient for every in-domain input (`verifyFuel = 2^30` exceeds it). -/
def FUEL : Nat := 700000000

theorem init_data : readMem (M.init P).mem 0 168 = dataSeg := by
  simp only [M.init]
  apply List.ext_getElem (by simp [dataSeg_length])
  intro i h1 h2
  simp [readMem, P, program, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **Completeness of the body** with the fuel bound. -/
theorem body_twp {pub cb pb : Bytes} (hc : check cb pb = true) :
    twp P (Inp pub cb pb) body (M.init P) (fun m c => m.regs 15 = 1 ∧ c ≤ FUEL) := by
  obtain ⟨rs, R, t, acc, hs, hok, hdt, hsz, hroot, hrun, hout, hpl⟩ := check_facts hc
  obtain ⟨hl, hg⟩ := runBatch_lens hrun
  rw [body_eq]
  simp only [twp_seq]
  refine twp_mono (setup_twp init_data) fun m1 c1 ⟨h1, hc1⟩ => ?_
  refine twp_mono (claim_twp h1 hs) fun m2 c2 ⟨h2, hc2⟩ => ?_
  refine twp_mono (proof_twp h2 hpl) fun m3 c3 ⟨h3, hc3⟩ => ?_
  refine twp_mono (receipts_twp h3 hok) fun m4 c4 ⟨h4, hc4⟩ => ?_
  refine twp_mono (parse_twp h4 hdt hsz) fun m5 c5 ⟨A, K, h5, ht5, hc5⟩ => ?_
  refine twp_mono (hash_twp h5) fun m6 c6 ⟨h6, hr6, hc6⟩ => ?_
  have he : (rootT A K (vals0 pb A)).hashOf = readMem m6.mem (CLM + 117) 32 := by
    rw [claim_seg h6.toClaimIn 117 32 (by decide), ht5, hroot]; rfl
  refine twp_mono (rootIs_twp h6.toBase hr6 (by decide) he) fun m7 c7 ⟨hm7, hr7, hc7⟩ => ?_
  have h7 : TrieSt cb pb rs R A K (vals0 pb A) m7 :=
    TrieSt.congr h6 hm7 (by rw [hr7 14 (by decide) (by decide) (by decide) (by decide)]; exact h6.k8)
      (by rw [hr7 15 (by decide) (by decide) (by decide) (by decide)]; exact h6.k1)
  rw [← ht5] at hrun
  refine twp_mono (batch_twp h7 hrun) fun m8 c8 ⟨vals, h8, htr, hbm, hc8⟩ => ?_
  refine twp_mono (final_twp h8 hbm htr hl hg hout) fun m9 c9 ⟨h15, hc9⟩ => ?_
  refine ⟨h15, ?_⟩
  simp only [PMAX] at hpl
  simp only [FUEL]
  omega

theorem prog_eq : prog = .seq body (.halt 15) := rfl

theorem prog_okB : prog.okB = true := by
  simp only [prog_eq, Stmt.okB, body_okB, Bool.true_and]

/-- Machine acceptance ⇒ `check`. -/
theorem prog_sound {pub cb pb : Bytes} (ht : TapesOK cb pb) {c : Nat}
    (h : Ev P (Inp pub cb pb) prog (M.init P) (.halt true) c) : check cb pb = true := by
  rw [prog_eq] at h
  cases h with
  | seqOk h1 h2 => exact body_wp ht _ _ h1
  | seqHalt h1 => exact absurd h1 (Ev.noHalt (Stmt.noHalt_of_noHaltB body_noHaltB))

/-- `check` ⇒ machine acceptance within `FUEL + 1`. -/
theorem prog_complete {pub cb pb : Bytes} (hc : check cb pb = true) :
    ∃ c, c ≤ FUEL + 1 ∧ Ev P (Inp pub cb pb) prog (M.init P) (.halt true) c := by
  obtain ⟨m, c, e, h15, hcf⟩ := body_twp (pub := pub) hc
  refine ⟨c + 1, by omega, ?_⟩
  rw [prog_eq]
  have := @Ev.halt P (Inp pub cb pb) 15 m
  rw [h15] at this
  exact Ev.seqOk e this

end ReexecNpai

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem decode_code : ArenaCore.Interp.decode code = some program := decode_encode program program_canon

/-- **Main theorem.** On every input (public tape shorter than `2^32`), the
NPAI image `code` run by the approved interpreter with any fuel `≥ FUEL + 1`
accepts exactly when the reference model `check` does. -/
theorem interpVerify_eq_check {pub cb pb : Bytes} (hpub : pub.length < 4294967296) {fuel : Nat}
    (hf : FUEL + 1 ≤ fuel) : interpVerify code fuel pub cb pb = check cb pb := by
  unfold interpVerify
  rw [decode_code]
  simp only
  cases hc : check cb pb with
  | true =>
    obtain ⟨rs, R, t, acc, hs, hok, -, -, -, -, -, hpl⟩ := check_facts hc
    obtain ⟨c, hcf, hev⟩ := prog_complete (pub := pub) hc
    have hacc := exec_accept_complete program prog (Stmt.ok_of_okB prog_okB) rfl fuel c hev (by omega)
    have : run program { pub := pub, claim := cb, proof := pb } fuel = some true := by
      rw [run_eq_some_true_iff]
      unfold runFull runWith
      have hpl' : pb.length < maxTapeLen := by simp only [PMAX] at hpl; unfold maxTapeLen; omega
      rw [if_pos ⟨hpub, by show cb.length < maxTapeLen; rw [hs.1]; decide, hpl'⟩]
      exact hacc
    rw [this]; rfl
  | false =>
    cases hr : run program { pub := pub, claim := cb, proof := pb } fuel with
    | none => rfl
    | some b =>
      cases b with
      | false => rfl
      | true =>
        exfalso
        rw [run_eq_some_true_iff] at hr
        unfold runFull runWith at hr
        split at hr
        · rename_i hlen
          obtain ⟨c, hev⟩ := exec_accept_sound program prog (Stmt.ok_of_okB prog_okB) rfl fuel hr
          have := prog_sound (pub := pub) ⟨hlen.2.1, hlen.2.2⟩ hev
          rw [hc] at this; cases this
        · cases hr

end ReexecNpai
