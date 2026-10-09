import ZkFormal.NearV3.Sched.Link.GridLink
import ZkFormal.NearV3.Sched.Pub.Prep

/-!
# Forwarding with `Prep.fwd`: no demand premise

With the public forwarding records rendered from `p.fwd` (link-keyed, `prepD0_fwd_links`), every
demand is `< 2^24` (`prepD0_fwd_lt`). So the τ = 0 conclusion of `schedCore_fwd'` holds for
**every** link, with no per-link premise.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3 NearSpecV3.Scheduler

theorem fwdDemand_lt {fwd : List (Nat × Nat)} (h : ∀ x ∈ fwd, x.2 < 2 ^ 24) (l : Nat) :
    fwdDemand fwd l < 2 ^ 24 := by
  unfold fwdDemand
  cases e : fwd.find? (·.1 == l) with
  | none => simp
  | some x => simpa using h x (List.mem_of_find?_eq_some e)

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **Forwarding (τ = 0), every link**: each demand of `p.fwd` is at most the run's grant. -/
theorem schedCore_fwd_prep (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn AP tsha) (DX : SdlxOwn AP tsd)
    (SK : ShaKind AP pub tr tcd)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (I : PubIdx AP pub Fp.ofNat)
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) p.fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) p.fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) p.fwd).dlSend)
    (h0 : 0 < p.sched.length) :
    ∃ out, runCore p.sched[0] (prevOf tr tcd 0) = some out ∧
      ∀ l, l < p.sched[0].ids.length * p.sched[0].ids.length →
        ∃ gr, out.granted[l]? = some ((p.sched[0].ids.getD (l / p.sched[0].ids.length) 0,
            p.sched[0].ids.getD (l % p.sched[0].ids.length) 0), gr) ∧ fwdDemand p.fwd l ≤ gr := by
  obtain ⟨out, hrun, H⟩ := schedCore_fwd' hH O OS OO OC SO PB IO DO PR SH DX SK hprep I p.fwd
    hrecP hrecB hrecD h0
  exact ⟨out, hrun, fun l hl => H l hl (fwdDemand_lt (prepD0_fwd_lt hprep) l)⟩

end ZkFormal.NearV3.Sched
