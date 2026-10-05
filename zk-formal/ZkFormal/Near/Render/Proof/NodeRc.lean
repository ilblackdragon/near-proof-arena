import ZkFormal.Near.Render.Proof.NodeFacts

/-!
# ZkFormal.Near.Render.Proof.NodeRc — cells of a node row at literal columns

`NodeCells.rc_*` for the indexed column families (`rc_state`, `rc_hbit`, …)
instantiated at every literal column, and the `node_rc` tactic rewriting every
cell of a node row (generated).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

namespace NodeRc
open NodeGen NodeCells

section
variable (I : Info) (u : Std.HashMap Edge Nat) (r : NRec)

theorem r14 : rowCell I u r 14 = b2n (r.f.state = 14) := rc_state I u r 14 (by decide) (by decide)
theorem r15 : rowCell I u r 15 = b2n (r.f.state = 15) := rc_state I u r 15 (by decide) (by decide)
theorem r16 : rowCell I u r 16 = b2n (r.f.state = 16) := rc_state I u r 16 (by decide) (by decide)
theorem r17 : rowCell I u r 17 = b2n (r.f.state = 17) := rc_state I u r 17 (by decide) (by decide)
theorem r18 : rowCell I u r 18 = b2n (r.f.state = 18) := rc_state I u r 18 (by decide) (by decide)
theorem r19 : rowCell I u r 19 = b2n (r.f.state = 19) := rc_state I u r 19 (by decide) (by decide)
theorem r20 : rowCell I u r 20 = b2n (r.f.state = 20) := rc_state I u r 20 (by decide) (by decide)
theorem r21 : rowCell I u r 21 = b2n (r.f.state = 21) := rc_state I u r 21 (by decide) (by decide)
theorem r22 : rowCell I u r 22 = b2n (r.f.state = 22) := rc_state I u r 22 (by decide) (by decide)
theorem r29 : rowCell I u r 29 = if r.f.nib then bitOf (r.b / 16) 0 else 0 := rc_hbit I u r 0 (by decide)
theorem r33 : rowCell I u r 33 = if r.f.nib then bitOf (r.b % 16) 0 else 0 := rc_lbit I u r 0 (by decide)
theorem r30 : rowCell I u r 30 = if r.f.nib then bitOf (r.b / 16) 1 else 0 := rc_hbit I u r 1 (by decide)
theorem r34 : rowCell I u r 34 = if r.f.nib then bitOf (r.b % 16) 1 else 0 := rc_lbit I u r 1 (by decide)
theorem r31 : rowCell I u r 31 = if r.f.nib then bitOf (r.b / 16) 2 else 0 := rc_hbit I u r 2 (by decide)
theorem r35 : rowCell I u r 35 = if r.f.nib then bitOf (r.b % 16) 2 else 0 := rc_lbit I u r 2 (by decide)
theorem r32 : rowCell I u r 32 = if r.f.nib then bitOf (r.b / 16) 3 else 0 := rc_hbit I u r 3 (by decide)
theorem r36 : rowCell I u r 36 = if r.f.nib then bitOf (r.b % 16) 3 else 0 := rc_lbit I u r 3 (by decide)
theorem r37 : rowCell I u r 37 = bitOf (bmvOf (I.nodeAt r.n)) 0 := rc_bm I u r 0 (by decide)
theorem r54 : rowCell I u r 54 = (match r.f.chw with | some w => b2n (w.slot = some 0) | none => 0) := rc_jj I u r 0 (by decide)
theorem r38 : rowCell I u r 38 = bitOf (bmvOf (I.nodeAt r.n)) 1 := rc_bm I u r 1 (by decide)
theorem r55 : rowCell I u r 55 = (match r.f.chw with | some w => b2n (w.slot = some 1) | none => 0) := rc_jj I u r 1 (by decide)
theorem r39 : rowCell I u r 39 = bitOf (bmvOf (I.nodeAt r.n)) 2 := rc_bm I u r 2 (by decide)
theorem r56 : rowCell I u r 56 = (match r.f.chw with | some w => b2n (w.slot = some 2) | none => 0) := rc_jj I u r 2 (by decide)
theorem r40 : rowCell I u r 40 = bitOf (bmvOf (I.nodeAt r.n)) 3 := rc_bm I u r 3 (by decide)
theorem r57 : rowCell I u r 57 = (match r.f.chw with | some w => b2n (w.slot = some 3) | none => 0) := rc_jj I u r 3 (by decide)
theorem r41 : rowCell I u r 41 = bitOf (bmvOf (I.nodeAt r.n)) 4 := rc_bm I u r 4 (by decide)
theorem r58 : rowCell I u r 58 = (match r.f.chw with | some w => b2n (w.slot = some 4) | none => 0) := rc_jj I u r 4 (by decide)
theorem r42 : rowCell I u r 42 = bitOf (bmvOf (I.nodeAt r.n)) 5 := rc_bm I u r 5 (by decide)
theorem r59 : rowCell I u r 59 = (match r.f.chw with | some w => b2n (w.slot = some 5) | none => 0) := rc_jj I u r 5 (by decide)
theorem r43 : rowCell I u r 43 = bitOf (bmvOf (I.nodeAt r.n)) 6 := rc_bm I u r 6 (by decide)
theorem r60 : rowCell I u r 60 = (match r.f.chw with | some w => b2n (w.slot = some 6) | none => 0) := rc_jj I u r 6 (by decide)
theorem r44 : rowCell I u r 44 = bitOf (bmvOf (I.nodeAt r.n)) 7 := rc_bm I u r 7 (by decide)
theorem r61 : rowCell I u r 61 = (match r.f.chw with | some w => b2n (w.slot = some 7) | none => 0) := rc_jj I u r 7 (by decide)
theorem r45 : rowCell I u r 45 = bitOf (bmvOf (I.nodeAt r.n)) 8 := rc_bm I u r 8 (by decide)
theorem r62 : rowCell I u r 62 = (match r.f.chw with | some w => b2n (w.slot = some 8) | none => 0) := rc_jj I u r 8 (by decide)
theorem r46 : rowCell I u r 46 = bitOf (bmvOf (I.nodeAt r.n)) 9 := rc_bm I u r 9 (by decide)
theorem r63 : rowCell I u r 63 = (match r.f.chw with | some w => b2n (w.slot = some 9) | none => 0) := rc_jj I u r 9 (by decide)
theorem r47 : rowCell I u r 47 = bitOf (bmvOf (I.nodeAt r.n)) 10 := rc_bm I u r 10 (by decide)
theorem r64 : rowCell I u r 64 = (match r.f.chw with | some w => b2n (w.slot = some 10) | none => 0) := rc_jj I u r 10 (by decide)
theorem r48 : rowCell I u r 48 = bitOf (bmvOf (I.nodeAt r.n)) 11 := rc_bm I u r 11 (by decide)
theorem r65 : rowCell I u r 65 = (match r.f.chw with | some w => b2n (w.slot = some 11) | none => 0) := rc_jj I u r 11 (by decide)
theorem r49 : rowCell I u r 49 = bitOf (bmvOf (I.nodeAt r.n)) 12 := rc_bm I u r 12 (by decide)
theorem r66 : rowCell I u r 66 = (match r.f.chw with | some w => b2n (w.slot = some 12) | none => 0) := rc_jj I u r 12 (by decide)
theorem r50 : rowCell I u r 50 = bitOf (bmvOf (I.nodeAt r.n)) 13 := rc_bm I u r 13 (by decide)
theorem r67 : rowCell I u r 67 = (match r.f.chw with | some w => b2n (w.slot = some 13) | none => 0) := rc_jj I u r 13 (by decide)
theorem r51 : rowCell I u r 51 = bitOf (bmvOf (I.nodeAt r.n)) 14 := rc_bm I u r 14 (by decide)
theorem r68 : rowCell I u r 68 = (match r.f.chw with | some w => b2n (w.slot = some 14) | none => 0) := rc_jj I u r 14 (by decide)
theorem r52 : rowCell I u r 52 = bitOf (bmvOf (I.nodeAt r.n)) 15 := rc_bm I u r 15 (by decide)
theorem r69 : rowCell I u r 69 = (match r.f.chw with | some w => b2n (w.slot = some 15) | none => 0) := rc_jj I u r 15 (by decide)
theorem r72 : rowCell I u r 72 = (match r.f.win with | some w => w.pre.getD (r.idx + 0) 0 | none => 0) := rc_reg I u r 0 (by decide)
theorem r104 : rowCell I u r 104 = (match r.f.win with | some w => w.post.getD (r.idx + 0) 0 | none => 0) := rc_preg I u r 0 (by decide)
theorem r73 : rowCell I u r 73 = (match r.f.win with | some w => w.pre.getD (r.idx + 1) 0 | none => 0) := rc_reg I u r 1 (by decide)
theorem r105 : rowCell I u r 105 = (match r.f.win with | some w => w.post.getD (r.idx + 1) 0 | none => 0) := rc_preg I u r 1 (by decide)
theorem r74 : rowCell I u r 74 = (match r.f.win with | some w => w.pre.getD (r.idx + 2) 0 | none => 0) := rc_reg I u r 2 (by decide)
theorem r106 : rowCell I u r 106 = (match r.f.win with | some w => w.post.getD (r.idx + 2) 0 | none => 0) := rc_preg I u r 2 (by decide)
theorem r75 : rowCell I u r 75 = (match r.f.win with | some w => w.pre.getD (r.idx + 3) 0 | none => 0) := rc_reg I u r 3 (by decide)
theorem r107 : rowCell I u r 107 = (match r.f.win with | some w => w.post.getD (r.idx + 3) 0 | none => 0) := rc_preg I u r 3 (by decide)
theorem r76 : rowCell I u r 76 = (match r.f.win with | some w => w.pre.getD (r.idx + 4) 0 | none => 0) := rc_reg I u r 4 (by decide)
theorem r108 : rowCell I u r 108 = (match r.f.win with | some w => w.post.getD (r.idx + 4) 0 | none => 0) := rc_preg I u r 4 (by decide)
theorem r77 : rowCell I u r 77 = (match r.f.win with | some w => w.pre.getD (r.idx + 5) 0 | none => 0) := rc_reg I u r 5 (by decide)
theorem r109 : rowCell I u r 109 = (match r.f.win with | some w => w.post.getD (r.idx + 5) 0 | none => 0) := rc_preg I u r 5 (by decide)
theorem r78 : rowCell I u r 78 = (match r.f.win with | some w => w.pre.getD (r.idx + 6) 0 | none => 0) := rc_reg I u r 6 (by decide)
theorem r110 : rowCell I u r 110 = (match r.f.win with | some w => w.post.getD (r.idx + 6) 0 | none => 0) := rc_preg I u r 6 (by decide)
theorem r79 : rowCell I u r 79 = (match r.f.win with | some w => w.pre.getD (r.idx + 7) 0 | none => 0) := rc_reg I u r 7 (by decide)
theorem r111 : rowCell I u r 111 = (match r.f.win with | some w => w.post.getD (r.idx + 7) 0 | none => 0) := rc_preg I u r 7 (by decide)
theorem r80 : rowCell I u r 80 = (match r.f.win with | some w => w.pre.getD (r.idx + 8) 0 | none => 0) := rc_reg I u r 8 (by decide)
theorem r112 : rowCell I u r 112 = (match r.f.win with | some w => w.post.getD (r.idx + 8) 0 | none => 0) := rc_preg I u r 8 (by decide)
theorem r81 : rowCell I u r 81 = (match r.f.win with | some w => w.pre.getD (r.idx + 9) 0 | none => 0) := rc_reg I u r 9 (by decide)
theorem r113 : rowCell I u r 113 = (match r.f.win with | some w => w.post.getD (r.idx + 9) 0 | none => 0) := rc_preg I u r 9 (by decide)
theorem r82 : rowCell I u r 82 = (match r.f.win with | some w => w.pre.getD (r.idx + 10) 0 | none => 0) := rc_reg I u r 10 (by decide)
theorem r114 : rowCell I u r 114 = (match r.f.win with | some w => w.post.getD (r.idx + 10) 0 | none => 0) := rc_preg I u r 10 (by decide)
theorem r83 : rowCell I u r 83 = (match r.f.win with | some w => w.pre.getD (r.idx + 11) 0 | none => 0) := rc_reg I u r 11 (by decide)
theorem r115 : rowCell I u r 115 = (match r.f.win with | some w => w.post.getD (r.idx + 11) 0 | none => 0) := rc_preg I u r 11 (by decide)
theorem r84 : rowCell I u r 84 = (match r.f.win with | some w => w.pre.getD (r.idx + 12) 0 | none => 0) := rc_reg I u r 12 (by decide)
theorem r116 : rowCell I u r 116 = (match r.f.win with | some w => w.post.getD (r.idx + 12) 0 | none => 0) := rc_preg I u r 12 (by decide)
theorem r85 : rowCell I u r 85 = (match r.f.win with | some w => w.pre.getD (r.idx + 13) 0 | none => 0) := rc_reg I u r 13 (by decide)
theorem r117 : rowCell I u r 117 = (match r.f.win with | some w => w.post.getD (r.idx + 13) 0 | none => 0) := rc_preg I u r 13 (by decide)
theorem r86 : rowCell I u r 86 = (match r.f.win with | some w => w.pre.getD (r.idx + 14) 0 | none => 0) := rc_reg I u r 14 (by decide)
theorem r118 : rowCell I u r 118 = (match r.f.win with | some w => w.post.getD (r.idx + 14) 0 | none => 0) := rc_preg I u r 14 (by decide)
theorem r87 : rowCell I u r 87 = (match r.f.win with | some w => w.pre.getD (r.idx + 15) 0 | none => 0) := rc_reg I u r 15 (by decide)
theorem r119 : rowCell I u r 119 = (match r.f.win with | some w => w.post.getD (r.idx + 15) 0 | none => 0) := rc_preg I u r 15 (by decide)
theorem r88 : rowCell I u r 88 = (match r.f.win with | some w => w.pre.getD (r.idx + 16) 0 | none => 0) := rc_reg I u r 16 (by decide)
theorem r120 : rowCell I u r 120 = (match r.f.win with | some w => w.post.getD (r.idx + 16) 0 | none => 0) := rc_preg I u r 16 (by decide)
theorem r89 : rowCell I u r 89 = (match r.f.win with | some w => w.pre.getD (r.idx + 17) 0 | none => 0) := rc_reg I u r 17 (by decide)
theorem r121 : rowCell I u r 121 = (match r.f.win with | some w => w.post.getD (r.idx + 17) 0 | none => 0) := rc_preg I u r 17 (by decide)
theorem r90 : rowCell I u r 90 = (match r.f.win with | some w => w.pre.getD (r.idx + 18) 0 | none => 0) := rc_reg I u r 18 (by decide)
theorem r122 : rowCell I u r 122 = (match r.f.win with | some w => w.post.getD (r.idx + 18) 0 | none => 0) := rc_preg I u r 18 (by decide)
theorem r91 : rowCell I u r 91 = (match r.f.win with | some w => w.pre.getD (r.idx + 19) 0 | none => 0) := rc_reg I u r 19 (by decide)
theorem r123 : rowCell I u r 123 = (match r.f.win with | some w => w.post.getD (r.idx + 19) 0 | none => 0) := rc_preg I u r 19 (by decide)
theorem r92 : rowCell I u r 92 = (match r.f.win with | some w => w.pre.getD (r.idx + 20) 0 | none => 0) := rc_reg I u r 20 (by decide)
theorem r124 : rowCell I u r 124 = (match r.f.win with | some w => w.post.getD (r.idx + 20) 0 | none => 0) := rc_preg I u r 20 (by decide)
theorem r93 : rowCell I u r 93 = (match r.f.win with | some w => w.pre.getD (r.idx + 21) 0 | none => 0) := rc_reg I u r 21 (by decide)
theorem r125 : rowCell I u r 125 = (match r.f.win with | some w => w.post.getD (r.idx + 21) 0 | none => 0) := rc_preg I u r 21 (by decide)
theorem r94 : rowCell I u r 94 = (match r.f.win with | some w => w.pre.getD (r.idx + 22) 0 | none => 0) := rc_reg I u r 22 (by decide)
theorem r126 : rowCell I u r 126 = (match r.f.win with | some w => w.post.getD (r.idx + 22) 0 | none => 0) := rc_preg I u r 22 (by decide)
theorem r95 : rowCell I u r 95 = (match r.f.win with | some w => w.pre.getD (r.idx + 23) 0 | none => 0) := rc_reg I u r 23 (by decide)
theorem r127 : rowCell I u r 127 = (match r.f.win with | some w => w.post.getD (r.idx + 23) 0 | none => 0) := rc_preg I u r 23 (by decide)
theorem r96 : rowCell I u r 96 = (match r.f.win with | some w => w.pre.getD (r.idx + 24) 0 | none => 0) := rc_reg I u r 24 (by decide)
theorem r128 : rowCell I u r 128 = (match r.f.win with | some w => w.post.getD (r.idx + 24) 0 | none => 0) := rc_preg I u r 24 (by decide)
theorem r97 : rowCell I u r 97 = (match r.f.win with | some w => w.pre.getD (r.idx + 25) 0 | none => 0) := rc_reg I u r 25 (by decide)
theorem r129 : rowCell I u r 129 = (match r.f.win with | some w => w.post.getD (r.idx + 25) 0 | none => 0) := rc_preg I u r 25 (by decide)
theorem r98 : rowCell I u r 98 = (match r.f.win with | some w => w.pre.getD (r.idx + 26) 0 | none => 0) := rc_reg I u r 26 (by decide)
theorem r130 : rowCell I u r 130 = (match r.f.win with | some w => w.post.getD (r.idx + 26) 0 | none => 0) := rc_preg I u r 26 (by decide)
theorem r99 : rowCell I u r 99 = (match r.f.win with | some w => w.pre.getD (r.idx + 27) 0 | none => 0) := rc_reg I u r 27 (by decide)
theorem r131 : rowCell I u r 131 = (match r.f.win with | some w => w.post.getD (r.idx + 27) 0 | none => 0) := rc_preg I u r 27 (by decide)
theorem r100 : rowCell I u r 100 = (match r.f.win with | some w => w.pre.getD (r.idx + 28) 0 | none => 0) := rc_reg I u r 28 (by decide)
theorem r132 : rowCell I u r 132 = (match r.f.win with | some w => w.post.getD (r.idx + 28) 0 | none => 0) := rc_preg I u r 28 (by decide)
theorem r101 : rowCell I u r 101 = (match r.f.win with | some w => w.pre.getD (r.idx + 29) 0 | none => 0) := rc_reg I u r 29 (by decide)
theorem r133 : rowCell I u r 133 = (match r.f.win with | some w => w.post.getD (r.idx + 29) 0 | none => 0) := rc_preg I u r 29 (by decide)
theorem r102 : rowCell I u r 102 = (match r.f.win with | some w => w.pre.getD (r.idx + 30) 0 | none => 0) := rc_reg I u r 30 (by decide)
theorem r134 : rowCell I u r 134 = (match r.f.win with | some w => w.post.getD (r.idx + 30) 0 | none => 0) := rc_preg I u r 30 (by decide)
theorem r103 : rowCell I u r 103 = (match r.f.win with | some w => w.pre.getD (r.idx + 31) 0 | none => 0) := rc_reg I u r 31 (by decide)
theorem r135 : rowCell I u r 135 = (match r.f.win with | some w => w.post.getD (r.idx + 31) 0 | none => 0) := rc_preg I u r 31 (by decide)

end

end NodeRc

/-- Rewrite every cell of a node row (`rowCell`) by its value. -/
syntax "node_rc" "[" (Lean.Parser.Tactic.simpLemma),* "]" : tactic
macro_rules
  | `(tactic| node_rc [$ts,*]) => `(tactic| simp only [NodeCells.rc_act, NodeCells.rc_nf, NodeCells.rc_nl, NodeCells.rc_sumr, NodeCells.rc_nid, NodeCells.rc_pos, NodeCells.rc_len, NodeCells.rc_depth, NodeCells.rc_b, NodeCells.rc_pb, NodeCells.rc_tl, NodeCells.rc_te, NodeCells.rc_tb1, NodeCells.rc_tb2, NodeCells.rc_idx, NodeCells.rc_fs, NodeCells.rc_fe, NodeCells.rc_hplen, NodeCells.rc_odd, NodeCells.rc_nokey, NodeCells.rc_nochild, NodeCells.rc_w, NodeCells.rc_lastw, NodeCells.rc_rv, NodeCells.rc_cid, NodeCells.rc_clen, NodeCells.rc_tv, NodeCells.rc_dI, NodeCells.rc_dL, NodeCells.rc_gD, NodeCells.rc_gP, NodeCells.rc_gV, NodeCells.rc_gA, NodeCells.rc_aI, NodeCells.rc_aS, NodeCells.rc_aN, NodeCells.rc_aJ, NodeCells.rc_mA, NodeCells.rc_mB, NodeCells.rc_sz, NodeCells.rc_res, NodeCells.rc_cres, NodeCells.rc_xres, NodeCells.rc_xrv, NodeCells.rc_xdead, NodeCells.rc_xlast0, NodeCells.rc_eext, NodeCells.rc_gB, NodeCells.rc_bN, NodeCells.rc_bJ, NodeRc.r14, NodeRc.r15, NodeRc.r16, NodeRc.r17, NodeRc.r18, NodeRc.r19, NodeRc.r20, NodeRc.r21, NodeRc.r22, NodeRc.r29, NodeRc.r30, NodeRc.r31, NodeRc.r32, NodeRc.r33, NodeRc.r34, NodeRc.r35, NodeRc.r36, NodeRc.r37, NodeRc.r38, NodeRc.r39, NodeRc.r40, NodeRc.r41, NodeRc.r42, NodeRc.r43, NodeRc.r44, NodeRc.r45, NodeRc.r46, NodeRc.r47, NodeRc.r48, NodeRc.r49, NodeRc.r50, NodeRc.r51, NodeRc.r52, NodeRc.r54, NodeRc.r55, NodeRc.r56, NodeRc.r57, NodeRc.r58, NodeRc.r59, NodeRc.r60, NodeRc.r61, NodeRc.r62, NodeRc.r63, NodeRc.r64, NodeRc.r65, NodeRc.r66, NodeRc.r67, NodeRc.r68, NodeRc.r69, NodeRc.r72, NodeRc.r73, NodeRc.r74, NodeRc.r75, NodeRc.r76, NodeRc.r77, NodeRc.r78, NodeRc.r79, NodeRc.r80, NodeRc.r81, NodeRc.r82, NodeRc.r83, NodeRc.r84, NodeRc.r85, NodeRc.r86, NodeRc.r87, NodeRc.r88, NodeRc.r89, NodeRc.r90, NodeRc.r91, NodeRc.r92, NodeRc.r93, NodeRc.r94, NodeRc.r95, NodeRc.r96, NodeRc.r97, NodeRc.r98, NodeRc.r99, NodeRc.r100, NodeRc.r101, NodeRc.r102, NodeRc.r103, NodeRc.r104, NodeRc.r105, NodeRc.r106, NodeRc.r107, NodeRc.r108, NodeRc.r109, NodeRc.r110, NodeRc.r111, NodeRc.r112, NodeRc.r113, NodeRc.r114, NodeRc.r115, NodeRc.r116, NodeRc.r117, NodeRc.r118, NodeRc.r119, NodeRc.r120, NodeRc.r121, NodeRc.r122, NodeRc.r123, NodeRc.r124, NodeRc.r125, NodeRc.r126, NodeRc.r127, NodeRc.r128, NodeRc.r129, NodeRc.r130, NodeRc.r131, NodeRc.r132, NodeRc.r133, NodeRc.r134, NodeRc.r135, $ts,*])

end ZkFormal.Near.Render
