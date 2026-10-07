import ZkFormal
import ZkFormal.NearV3.BudgetCheck
import ZkFormal.NearV3.Extract.Node.Proof
import ZkFormal.NearV3.Extract.Ups.UpsLink
import ZkFormal.NearV3.Link.Post3OccSets
import ZkFormal.NearV3.Rcpt.BudgetCheck
import ZkFormal.NearV3.Rcpt.Extract.V.Key
import ZkFormal.NearV3.Rcpt.Link.Body
import ZkFormal.NearV3.Rcpt.Link.Keynib
import ZkFormal.NearV3.Rcpt.Link.Lex
import ZkFormal.NearV3.Rcpt.Link.Srec
import ZkFormal.NearV3.Rcpt.Render.AcctRender
import ZkFormal.NearV3.Rcpt.Render.AkeyRender
import ZkFormal.NearV3.Rcpt.Render.BndRender
import ZkFormal.NearV3.Rcpt.Render.SizeRender
import ZkFormal.NearV3.Rcpt.ShaRows
import ZkFormal.NearV3.Render.HeadRender
import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Render.NodeRender
import ZkFormal.NearV3.Render.UniqRender
import ZkFormal.NearV3.Render.UpsRender
import ZkFormal.NearV3.Render.ValRender
import ZkFormal.NearV3.Render.WalkRender
import ZkFormal.NearV3.Sched.BudgetCheck
import ZkFormal.NearV3.Sched.Complete.All
import ZkFormal.NearV3.Sched.Gen.Codec
import ZkFormal.NearV3.Sched.Gen.Lane
import ZkFormal.NearV3.Sched.Link.FwdPrep
import ZkFormal.NearV3.Sched.Link.KindSched
import ZkFormal.NearV3.Spec.TreeRecs
import ZkFormal.Size.V3Eval
import ZkFormal.Size.AlignedModel
import ZkFormal.Size.HonestAdmission
import ZkFormal.V3.RefundCodec

/-!
# Build gate for the integrated v3 proof work

Run `lake build ZkFormal.V3.Integration` under the host's heavy/taskset wrapper.
The historical `ZkFormal` root does not import the merged v3 trie, scheduler,
receipt, or deduplicated-size proof modules. This separate target checks their
interfaces together without changing the v1 build root or deployed packages.

Executable drivers (`V3.Tools`) and their compiler fast paths (`V3.Fast`) remain
separate targets. Unmerged WIP helpers are not imported. A successful build
checks the existing partial results, not the still-missing FactorSound,
FactorComplete, honestTrace_fits, or final admission certificate.
-/
