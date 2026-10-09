import ZkFormal.NearV3.Candidates.SizeComponents
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Local
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableFacts
namespace ZkFormal.NearV3.Candidates.NativeSourceFour
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates

def trace (bs : List SrcpB) (rep : Nat→Bool) : Trace Fp :=
  ⟨fun _=>22,fun t r x=>Fp.ofNat (DedupRender.cell bs rep (t*(2^22-1)+r) x)⟩

/-- Actual original source renderer placed in four log22 partitions. -/
theorem complete {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (pub : List Fp) :
    let tr:=trace (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)
    TableLocal (SizeCount.sourceTable SourceLog22.firstTable) tr 0 pub ∧
    TableLocal (SizeCount.sourceTable (SourceLog22.middleTable 64 65)) tr 1 pub ∧
    TableLocal (SizeCount.sourceTable (SourceLog22.middleTable 65 66)) tr 2 pub ∧
    TableLocal (SizeCount.sourceTable SourceLog22.lastTable) tr 3 pub := by
  have ht:=DedupCompile.relD0a_table_facts h hp hf hw
  have hr:=DedupCompile.relD0a_row_bound h hp hf hw
  refine ⟨SourceLog22.source_local (SourceLog22.first_local ht (by change 1≤22;decide) (by change 22≤22;decide) ?_),
    SourceLog22.source_local (SourceLog22.middle_local ht (off:=2^22-1) (by decide) (by change 1≤22;decide) (by change 22≤22;decide) ?_),
    SourceLog22.source_local (SourceLog22.middle_local ht (off:=2*(2^22-1)) (by decide) (by change 1≤22;decide) (by change 22≤22;decide) ?_),
    SourceLog22.source_local (SourceLog22.last_local ht (off:=3*(2^22-1)) (by decide) (by change 1≤22;decide) (by change 22≤22;decide) ?_ ?_)⟩
  · intro r _ x;simp [trace]
  · intro r _ x;simp [trace]
  · intro r _ x;simp [trace]
  · change _≤3*(2^22-1)+2^22-1;omega
  · intro r _ x;simp [trace]

/-- Exact arity-three SIZE send from the same accepted source dictionary. -/
theorem size_traffic {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (pub : List Fp) (sd : Bool) (m : List Fp) :
    let bs:=DedupCompile.blocks p.lists w.entries
    SourceSizeTraffic.fourCount (trace bs (sourceRepeated p.lists)) 0 1 2 3 pub sd m=
      if sd=true ∧ [Fp.ofNat 2,Fp.ofNat (DedupRender.size bs),0]=m then 1 else 0 := by
  apply SourceSizeTraffic.four_size_count _ (sourceRepeated p.lists) (DedupCompile.relD0a_blocks_nonempty h hp w.entries)
    (H:=2^22) (by intro t _;rfl) _ (DedupCompile.relD0a_block_widths h hp hf hw)
    (by intro r _ x;simp [trace]) (by intro r _ x;simp [trace]) (by intro r _ x;simp [trace]) (by intro r _ x;simp [trace])
  have hr:=DedupCompile.relD0a_row_bound h hp hf hw
  omega
/-- Exact seven-trace SIZE conservation with actual accepted source partitions. -/
theorem balance {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (vs : List NodeS3) (es : List ValE) (hn : Render.NodeOk vs) (hv : Render.ValOk es)
    (pub : List Fp) (tn tv ts : Nat) (m : List Fp) :
    let bs:=DedupCompile.blocks p.lists w.entries
    let tr:=trace bs (sourceRepeated p.lists)
    let v:=SizeComponents.view vs es bs
    let counts:=SizeComponents.counts vs es
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node vs pub) tn pub B_SIZE true m+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value es pub) tv pub B_SIZE true m+
      SourceSizeTraffic.fourCount tr 0 1 2 3 pub true m+
      tableBusCount SizeCount.sizeTable.interactions (SizeCountReceiver.trace pub v counts) ts pub B_SIZE true m=
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node vs pub) tn pub B_SIZE false m+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value es pub) tv pub B_SIZE false m+
      SourceSizeTraffic.fourCount tr 0 1 2 3 pub false m+
      tableBusCount SizeCount.sizeTable.interactions (SizeCountReceiver.trace pub v counts) ts pub B_SIZE false m := by
  apply SizeComponents.balance _ (sourceRepeated p.lists)
    (DedupCompile.relD0a_blocks_nonempty h hp w.entries) (H:=2^22)
    (by intro t _;rfl) _ (DedupCompile.relD0a_block_widths h hp hf hw)
    (by intro r _ x;simp [trace]) (by intro r _ x;simp [trace])
    (by intro r _ x;simp [trace]) (by intro r _ x;simp [trace]) vs es hn hv
  have hr:=DedupCompile.relD0a_row_bound h hp hf hw
  omega

end ZkFormal.NearV3.Candidates.NativeSourceFour
