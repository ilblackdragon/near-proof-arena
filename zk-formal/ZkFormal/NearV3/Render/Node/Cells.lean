import ZkFormal.NearV3.Render.Node.Seq

/-!
# ZkFormal.NearV3.Render.Node.Cells — cells of a node row at literal columns (generated)
-/

set_option maxRecDepth 4000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3
namespace Rc

section
variable (vs : List NodeS3) (r : NRec)

theorem c0 : rowCell vs r 0 = 1 := by
  rfl
theorem c1 : rowCell vs r 1 = b2n (r.pos = 0) := by
  rfl
theorem c2 : rowCell vs r 2 = b2n (r.pos + 1 = ((rec vs r.n).v.ser false).length) := by
  rfl
theorem c3 : rowCell vs r 3 = 0 := by
  rfl
theorem c4 : rowCell vs r 4 = r.n := by
  rfl
theorem c5 : rowCell vs r 5 = r.pos := by
  rfl
theorem c6 : rowCell vs r 6 = ((rec vs r.n).v.ser false).length := by
  rfl
theorem c7 : rowCell vs r 7 = (rec vs r.n).depth := by
  rfl
theorem c8 : rowCell vs r 8 = r.b := by
  rfl
theorem c9 : rowCell vs r 9 = r.pb := by
  rfl
theorem c10 : rowCell vs r 10 = (typeOf (rec vs r.n).v).1 := by
  rfl
theorem c11 : rowCell vs r 11 = (typeOf (rec vs r.n).v).2.1 := by
  rfl
theorem c12 : rowCell vs r 12 = (typeOf (rec vs r.n).v).2.2.1 := by
  rfl
theorem c13 : rowCell vs r 13 = (typeOf (rec vs r.n).v).2.2.2 := by
  rfl
theorem c14 : rowCell vs r 14 = b2n (r.f.state = 14) := by
  rfl
theorem c15 : rowCell vs r 15 = b2n (r.f.state = 15) := by
  rfl
theorem c16 : rowCell vs r 16 = b2n (r.f.state = 16) := by
  rfl
theorem c17 : rowCell vs r 17 = b2n (r.f.state = 17) := by
  rfl
theorem c18 : rowCell vs r 18 = b2n (r.f.state = 18) := by
  rfl
theorem c19 : rowCell vs r 19 = b2n (r.f.state = 19) := by
  rfl
theorem c20 : rowCell vs r 20 = b2n (r.f.state = 20) := by
  rfl
theorem c21 : rowCell vs r 21 = b2n (r.f.state = 21) := by
  rfl
theorem c22 : rowCell vs r 22 = b2n (r.f.state = 22) := by
  rfl
theorem c23 : rowCell vs r 23 = r.idx := by
  rfl
theorem c24 : rowCell vs r 24 = b2n (r.idx = 0) := by
  rfl
theorem c25 : rowCell vs r 25 = b2n (r.idx + 1 = r.f.len (hplenOf (rec vs r.n).v)) := by
  rfl
theorem c26 : rowCell vs r 26 = hplenOf (rec vs r.n).v := by
  rfl
theorem c27 : rowCell vs r 27 = oddOf (rec vs r.n).v := by
  rfl
theorem c28 : rowCell vs r 28 = nokeyOf (rec vs r.n).v := by
  rfl
theorem c29 : rowCell vs r 29 = (if r.f.nib || r.f.state == 15 then bitOf (r.b / 16) 0 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 0 else 0) := by
  rfl
theorem c30 : rowCell vs r 30 = (if r.f.nib || r.f.state == 15 then bitOf (r.b / 16) 1 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 1 else 0) := by
  rfl
theorem c31 : rowCell vs r 31 = (if r.f.nib || r.f.state == 15 then bitOf (r.b / 16) 2 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 2 else 0) := by
  rfl
theorem c32 : rowCell vs r 32 = (if r.f.nib || r.f.state == 15 then bitOf (r.b / 16) 3 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 3 else 0) := by
  rfl
theorem c33 : rowCell vs r 33 = (if r.f.nib || r.f.state == 15 then bitOf (r.b % 16) 0 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 4 else 0) := by
  rfl
theorem c34 : rowCell vs r 34 = (if r.f.nib || r.f.state == 15 then bitOf (r.b % 16) 1 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 5 else 0) := by
  rfl
theorem c35 : rowCell vs r 35 = (if r.f.nib || r.f.state == 15 then bitOf (r.b % 16) 2 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 6 else 0) := by
  rfl
theorem c36 : rowCell vs r 36 = (if r.f.nib || r.f.state == 15 then bitOf (r.b % 16) 3 else if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 7 else 0) := by
  rfl
theorem c37 : rowCell vs r 37 = bitOf (bmvOf (rec vs r.n).v) 0 := by
  rfl
theorem c38 : rowCell vs r 38 = bitOf (bmvOf (rec vs r.n).v) 1 := by
  rfl
theorem c39 : rowCell vs r 39 = bitOf (bmvOf (rec vs r.n).v) 2 := by
  rfl
theorem c40 : rowCell vs r 40 = bitOf (bmvOf (rec vs r.n).v) 3 := by
  rfl
theorem c41 : rowCell vs r 41 = bitOf (bmvOf (rec vs r.n).v) 4 := by
  rfl
theorem c42 : rowCell vs r 42 = bitOf (bmvOf (rec vs r.n).v) 5 := by
  rfl
theorem c43 : rowCell vs r 43 = bitOf (bmvOf (rec vs r.n).v) 6 := by
  rfl
theorem c44 : rowCell vs r 44 = bitOf (bmvOf (rec vs r.n).v) 7 := by
  rfl
theorem c45 : rowCell vs r 45 = bitOf (bmvOf (rec vs r.n).v) 8 := by
  rfl
theorem c46 : rowCell vs r 46 = bitOf (bmvOf (rec vs r.n).v) 9 := by
  rfl
theorem c47 : rowCell vs r 47 = bitOf (bmvOf (rec vs r.n).v) 10 := by
  rfl
theorem c48 : rowCell vs r 48 = bitOf (bmvOf (rec vs r.n).v) 11 := by
  rfl
theorem c49 : rowCell vs r 49 = bitOf (bmvOf (rec vs r.n).v) 12 := by
  rfl
theorem c50 : rowCell vs r 50 = bitOf (bmvOf (rec vs r.n).v) 13 := by
  rfl
theorem c51 : rowCell vs r 51 = bitOf (bmvOf (rec vs r.n).v) 14 := by
  rfl
theorem c52 : rowCell vs r 52 = bitOf (bmvOf (rec vs r.n).v) 15 := by
  rfl
theorem c53 : rowCell vs r 53 = nochildOf (rec vs r.n).v := by
  rfl
theorem c54 : rowCell vs r 54 = (match r.f.chw with | some w => b2n (w.slot = some 0) | none => 0) := by
  rfl
theorem c55 : rowCell vs r 55 = (match r.f.chw with | some w => b2n (w.slot = some 1) | none => 0) := by
  rfl
theorem c56 : rowCell vs r 56 = (match r.f.chw with | some w => b2n (w.slot = some 2) | none => 0) := by
  rfl
theorem c57 : rowCell vs r 57 = (match r.f.chw with | some w => b2n (w.slot = some 3) | none => 0) := by
  rfl
theorem c58 : rowCell vs r 58 = (match r.f.chw with | some w => b2n (w.slot = some 4) | none => 0) := by
  rfl
theorem c59 : rowCell vs r 59 = (match r.f.chw with | some w => b2n (w.slot = some 5) | none => 0) := by
  rfl
theorem c60 : rowCell vs r 60 = (match r.f.chw with | some w => b2n (w.slot = some 6) | none => 0) := by
  rfl
theorem c61 : rowCell vs r 61 = (match r.f.chw with | some w => b2n (w.slot = some 7) | none => 0) := by
  rfl
theorem c62 : rowCell vs r 62 = (match r.f.chw with | some w => b2n (w.slot = some 8) | none => 0) := by
  rfl
theorem c63 : rowCell vs r 63 = (match r.f.chw with | some w => b2n (w.slot = some 9) | none => 0) := by
  rfl
theorem c64 : rowCell vs r 64 = (match r.f.chw with | some w => b2n (w.slot = some 10) | none => 0) := by
  rfl
theorem c65 : rowCell vs r 65 = (match r.f.chw with | some w => b2n (w.slot = some 11) | none => 0) := by
  rfl
theorem c66 : rowCell vs r 66 = (match r.f.chw with | some w => b2n (w.slot = some 12) | none => 0) := by
  rfl
theorem c67 : rowCell vs r 67 = (match r.f.chw with | some w => b2n (w.slot = some 13) | none => 0) := by
  rfl
theorem c68 : rowCell vs r 68 = (match r.f.chw with | some w => b2n (w.slot = some 14) | none => 0) := by
  rfl
theorem c69 : rowCell vs r 69 = (match r.f.chw with | some w => b2n (w.slot = some 15) | none => 0) := by
  rfl
theorem c70 : rowCell vs r 70 = (match r.f.chw with | some w => w.w | none => 0) := by
  rfl
theorem c71 : rowCell vs r 71 = (match r.f.chw with | some w => b2n w.lastw | none => 0) := by
  rfl
theorem c72 : rowCell vs r 72 = (match r.f.win with | some w => w.pre.getD (r.idx + 0) 0 | none => 0) := by
  rfl
theorem c73 : rowCell vs r 73 = (match r.f.win with | some w => w.pre.getD (r.idx + 1) 0 | none => 0) := by
  rfl
theorem c74 : rowCell vs r 74 = (match r.f.win with | some w => w.pre.getD (r.idx + 2) 0 | none => 0) := by
  rfl
theorem c75 : rowCell vs r 75 = (match r.f.win with | some w => w.pre.getD (r.idx + 3) 0 | none => 0) := by
  rfl
theorem c76 : rowCell vs r 76 = (match r.f.win with | some w => w.pre.getD (r.idx + 4) 0 | none => 0) := by
  rfl
theorem c77 : rowCell vs r 77 = (match r.f.win with | some w => w.pre.getD (r.idx + 5) 0 | none => 0) := by
  rfl
theorem c78 : rowCell vs r 78 = (match r.f.win with | some w => w.pre.getD (r.idx + 6) 0 | none => 0) := by
  rfl
theorem c79 : rowCell vs r 79 = (match r.f.win with | some w => w.pre.getD (r.idx + 7) 0 | none => 0) := by
  rfl
theorem c80 : rowCell vs r 80 = (match r.f.win with | some w => w.pre.getD (r.idx + 8) 0 | none => 0) := by
  rfl
theorem c81 : rowCell vs r 81 = (match r.f.win with | some w => w.pre.getD (r.idx + 9) 0 | none => 0) := by
  rfl
theorem c82 : rowCell vs r 82 = (match r.f.win with | some w => w.pre.getD (r.idx + 10) 0 | none => 0) := by
  rfl
theorem c83 : rowCell vs r 83 = (match r.f.win with | some w => w.pre.getD (r.idx + 11) 0 | none => 0) := by
  rfl
theorem c84 : rowCell vs r 84 = (match r.f.win with | some w => w.pre.getD (r.idx + 12) 0 | none => 0) := by
  rfl
theorem c85 : rowCell vs r 85 = (match r.f.win with | some w => w.pre.getD (r.idx + 13) 0 | none => 0) := by
  rfl
theorem c86 : rowCell vs r 86 = (match r.f.win with | some w => w.pre.getD (r.idx + 14) 0 | none => 0) := by
  rfl
theorem c87 : rowCell vs r 87 = (match r.f.win with | some w => w.pre.getD (r.idx + 15) 0 | none => 0) := by
  rfl
theorem c88 : rowCell vs r 88 = (match r.f.win with | some w => w.pre.getD (r.idx + 16) 0 | none => 0) := by
  rfl
theorem c89 : rowCell vs r 89 = (match r.f.win with | some w => w.pre.getD (r.idx + 17) 0 | none => 0) := by
  rfl
theorem c90 : rowCell vs r 90 = (match r.f.win with | some w => w.pre.getD (r.idx + 18) 0 | none => 0) := by
  rfl
theorem c91 : rowCell vs r 91 = (match r.f.win with | some w => w.pre.getD (r.idx + 19) 0 | none => 0) := by
  rfl
theorem c92 : rowCell vs r 92 = (match r.f.win with | some w => w.pre.getD (r.idx + 20) 0 | none => 0) := by
  rfl
theorem c93 : rowCell vs r 93 = (match r.f.win with | some w => w.pre.getD (r.idx + 21) 0 | none => 0) := by
  rfl
theorem c94 : rowCell vs r 94 = (match r.f.win with | some w => w.pre.getD (r.idx + 22) 0 | none => 0) := by
  rfl
theorem c95 : rowCell vs r 95 = (match r.f.win with | some w => w.pre.getD (r.idx + 23) 0 | none => 0) := by
  rfl
theorem c96 : rowCell vs r 96 = (match r.f.win with | some w => w.pre.getD (r.idx + 24) 0 | none => 0) := by
  rfl
theorem c97 : rowCell vs r 97 = (match r.f.win with | some w => w.pre.getD (r.idx + 25) 0 | none => 0) := by
  rfl
theorem c98 : rowCell vs r 98 = (match r.f.win with | some w => w.pre.getD (r.idx + 26) 0 | none => 0) := by
  rfl
theorem c99 : rowCell vs r 99 = (match r.f.win with | some w => w.pre.getD (r.idx + 27) 0 | none => 0) := by
  rfl
theorem c100 : rowCell vs r 100 = (match r.f.win with | some w => w.pre.getD (r.idx + 28) 0 | none => 0) := by
  rfl
theorem c101 : rowCell vs r 101 = (match r.f.win with | some w => w.pre.getD (r.idx + 29) 0 | none => 0) := by
  rfl
theorem c102 : rowCell vs r 102 = (match r.f.win with | some w => w.pre.getD (r.idx + 30) 0 | none => 0) := by
  rfl
theorem c103 : rowCell vs r 103 = (match r.f.win with | some w => w.pre.getD (r.idx + 31) 0 | none => 0) := by
  rfl
theorem c104 : rowCell vs r 104 = (match r.f.win with | some w => w.post.getD (r.idx + 0) 0 | none => 0) := by
  rfl
theorem c105 : rowCell vs r 105 = (match r.f.win with | some w => w.post.getD (r.idx + 1) 0 | none => 0) := by
  rfl
theorem c106 : rowCell vs r 106 = (match r.f.win with | some w => w.post.getD (r.idx + 2) 0 | none => 0) := by
  rfl
theorem c107 : rowCell vs r 107 = (match r.f.win with | some w => w.post.getD (r.idx + 3) 0 | none => 0) := by
  rfl
theorem c108 : rowCell vs r 108 = (match r.f.win with | some w => w.post.getD (r.idx + 4) 0 | none => 0) := by
  rfl
theorem c109 : rowCell vs r 109 = (match r.f.win with | some w => w.post.getD (r.idx + 5) 0 | none => 0) := by
  rfl
theorem c110 : rowCell vs r 110 = (match r.f.win with | some w => w.post.getD (r.idx + 6) 0 | none => 0) := by
  rfl
theorem c111 : rowCell vs r 111 = (match r.f.win with | some w => w.post.getD (r.idx + 7) 0 | none => 0) := by
  rfl
theorem c112 : rowCell vs r 112 = (match r.f.win with | some w => w.post.getD (r.idx + 8) 0 | none => 0) := by
  rfl
theorem c113 : rowCell vs r 113 = (match r.f.win with | some w => w.post.getD (r.idx + 9) 0 | none => 0) := by
  rfl
theorem c114 : rowCell vs r 114 = (match r.f.win with | some w => w.post.getD (r.idx + 10) 0 | none => 0) := by
  rfl
theorem c115 : rowCell vs r 115 = (match r.f.win with | some w => w.post.getD (r.idx + 11) 0 | none => 0) := by
  rfl
theorem c116 : rowCell vs r 116 = (match r.f.win with | some w => w.post.getD (r.idx + 12) 0 | none => 0) := by
  rfl
theorem c117 : rowCell vs r 117 = (match r.f.win with | some w => w.post.getD (r.idx + 13) 0 | none => 0) := by
  rfl
theorem c118 : rowCell vs r 118 = (match r.f.win with | some w => w.post.getD (r.idx + 14) 0 | none => 0) := by
  rfl
theorem c119 : rowCell vs r 119 = (match r.f.win with | some w => w.post.getD (r.idx + 15) 0 | none => 0) := by
  rfl
theorem c120 : rowCell vs r 120 = (match r.f.win with | some w => w.post.getD (r.idx + 16) 0 | none => 0) := by
  rfl
theorem c121 : rowCell vs r 121 = (match r.f.win with | some w => w.post.getD (r.idx + 17) 0 | none => 0) := by
  rfl
theorem c122 : rowCell vs r 122 = (match r.f.win with | some w => w.post.getD (r.idx + 18) 0 | none => 0) := by
  rfl
theorem c123 : rowCell vs r 123 = (match r.f.win with | some w => w.post.getD (r.idx + 19) 0 | none => 0) := by
  rfl
theorem c124 : rowCell vs r 124 = (match r.f.win with | some w => w.post.getD (r.idx + 20) 0 | none => 0) := by
  rfl
theorem c125 : rowCell vs r 125 = (match r.f.win with | some w => w.post.getD (r.idx + 21) 0 | none => 0) := by
  rfl
theorem c126 : rowCell vs r 126 = (match r.f.win with | some w => w.post.getD (r.idx + 22) 0 | none => 0) := by
  rfl
theorem c127 : rowCell vs r 127 = (match r.f.win with | some w => w.post.getD (r.idx + 23) 0 | none => 0) := by
  rfl
theorem c128 : rowCell vs r 128 = (match r.f.win with | some w => w.post.getD (r.idx + 24) 0 | none => 0) := by
  rfl
theorem c129 : rowCell vs r 129 = (match r.f.win with | some w => w.post.getD (r.idx + 25) 0 | none => 0) := by
  rfl
theorem c130 : rowCell vs r 130 = (match r.f.win with | some w => w.post.getD (r.idx + 26) 0 | none => 0) := by
  rfl
theorem c131 : rowCell vs r 131 = (match r.f.win with | some w => w.post.getD (r.idx + 27) 0 | none => 0) := by
  rfl
theorem c132 : rowCell vs r 132 = (match r.f.win with | some w => w.post.getD (r.idx + 28) 0 | none => 0) := by
  rfl
theorem c133 : rowCell vs r 133 = (match r.f.win with | some w => w.post.getD (r.idx + 29) 0 | none => 0) := by
  rfl
theorem c134 : rowCell vs r 134 = (match r.f.win with | some w => w.post.getD (r.idx + 30) 0 | none => 0) := by
  rfl
theorem c135 : rowCell vs r 135 = (match r.f.win with | some w => w.post.getD (r.idx + 31) 0 | none => 0) := by
  rfl
theorem c136 : rowCell vs r 136 = (match r.f.chw with | some w => b2n w.look | none => 0) := by
  rfl
theorem c137 : rowCell vs r 137 = (match r.f.chw with | some w => w.cid | none => 0) := by
  rfl
theorem c138 : rowCell vs r 138 = (match r.f.chw with | some w => w.clen | none => 0) := by
  rfl
theorem c139 : rowCell vs r 139 = b2n (tvOf (rec vs r.n).v) := by
  rfl
theorem c140 : rowCell vs r 140 = (match digOf (rec vs r.n).v r with | some d => d.1 | none => 0) := by
  rfl
theorem c141 : rowCell vs r 141 = (match digOf (rec vs r.n).v r with | some d => d.2.1 | none => 0) := by
  rfl
theorem c142 : rowCell vs r 142 = (match digOf (rec vs r.n).v r with | some _ => 1 | none => 0) := by
  rfl
theorem c143 : rowCell vs r 143 = (match digOf (rec vs r.n).v r with | some (_, _, true) => 1 | _ => 0) := by
  rfl
theorem c144 : rowCell vs r 144 = b2n (r.pos = 0 ∧ (rec vs r.n).dup = true) := by
  rfl
theorem c145 : rowCell vs r 145 = gCell (edgeAOf vs r) := by
  rfl
theorem c146 : rowCell vs r 146 = eCell (edgeAOf vs r) 1 := by
  rfl
theorem c147 : rowCell vs r 147 = eCell (edgeAOf vs r) 2 := by
  rfl
theorem c148 : rowCell vs r 148 = eCell (edgeAOf vs r) 3 := by
  rfl
theorem c149 : rowCell vs r 149 = eCell (edgeAOf vs r) 4 := by
  rfl
theorem c150 : rowCell vs r 150 = uCell (rec vs r.n).uses (edgeAOf vs r) := by
  rfl
theorem c151 : rowCell vs r 151 = uCell (rec vs r.n).uses (edgeBOf vs r) := by
  rfl
theorem c152 : rowCell vs r 152 = szBefore vs r.n + (if (rec vs r.n).dup then 0 else r.pos) := by
  rfl
theorem c153 : rowCell vs r 153 = (rec vs r.n).res := by
  rfl
theorem c154 : rowCell vs r 154 = (match r.f.chw with | some w => w.cres | none => 0) := by
  rfl
theorem c155 : rowCell vs r 155 = xresOf (rec vs r.n).v := by
  rfl
theorem c156 : rowCell vs r 156 = b2n (xrvOf (rec vs r.n).v) := by
  rfl
theorem c157 : rowCell vs r 157 = b2n (xdeadOf (rec vs r.n).v) := by
  rfl
theorem c158 : rowCell vs r 158 = b2n (xlast0Of (rec vs r.n).v) := by
  rfl
theorem c159 : rowCell vs r 159 = b2n (eextOf (rec vs r.n).v) := by
  rfl
theorem c160 : rowCell vs r 160 = gCell (edgeBOf vs r) := by
  rfl
theorem c161 : rowCell vs r 161 = eCell (edgeBOf vs r) 3 := by
  rfl
theorem c162 : rowCell vs r 162 = eCell (edgeBOf vs r) 4 := by
  rfl
theorem c163 : rowCell vs r 163 = (rec vs r.n).tau := by
  rfl
theorem c164 : rowCell vs r 164 = (if r.f.isTag then bitOf ((rec vs r.n).depth + 112) 8 else 0) := by
  rfl
theorem c165 : rowCell vs r 165 = vidOf (rec vs r.n).v := by
  rfl
theorem c166 : rowCell vs r 166 = vlenOf (rec vs r.n).v := by
  rfl
theorem c167 : rowCell vs r 167 = b2n (twOf (rec vs r.n).v) := by
  rfl
theorem c168 : rowCell vs r 168 = (if r.f.state == 15 then le256 ((u32Bytes (hplenOf (rec vs r.n).v)).take (r.idx + 1)) else if r.f.isVlen then le256 ((((slotOf (rec vs r.n).v).map NSlot3.lenB).getD []).take (r.idx + 1)) else 0) := by
  rfl
theorem c169 : rowCell vs r 169 = (if r.f.isVlen || r.f.state == 15 then 256 ^ r.idx else 0) := by
  rfl
theorem c170 : rowCell vs r 170 = b2n (rec vs r.n).dup := by
  rfl
theorem c171 : rowCell vs r 171 = b2n (rec vs r.n).hd := by
  rfl
theorem c172 : rowCell vs r 172 = (rec vs r.n).repE := by
  rfl
theorem c173 : rowCell vs r 173 = (if r.f.isBm ∧ r.idx = 0 then (rec vs r.n).ubm else 0) := by
  rfl
theorem c174 : rowCell vs r 174 = eCell (edgeAOf vs r) 5 := by
  rfl
theorem c175 : rowCell vs r 175 = eCell (edgeBOf vs r) 5 := by
  rfl
theorem c176 : rowCell vs r 176 = eCell (edgeBOf vs r) 1 := by
  rfl
theorem c177 : rowCell vs r 177 = eCell (edgeBOf vs r) 2 := by
  rfl
theorem c178 : rowCell vs r 178 = b2n (isLeaf (rec vs r.n).v ∧ r.f.isMem ∧ r.idx = 0) := by
  rfl
theorem c179 : rowCell vs r 179 = xtgtOf r.n (rec vs r.n).v := by
  rfl
theorem c180 : rowCell vs r 180 = xtgJOf (rec vs r.n).v := by
  rfl
theorem c181 : rowCell vs r 181 = b2n ((r.f.isCh ∧ (match r.f.chw with | some w => w.look | none => false) = true) ∨ (r.f.isVh ∧ tvOf (rec vs r.n).v = true)) := by
  rfl
theorem c182 : rowCell vs r 182 = (if r.f.isCh then msgId K_NPRE (match r.f.chw with | some w => w.cid | none => 0) else if r.f.isVh then msgId K_VPRE (vidOf (rec vs r.n).v) else 0) := by
  rfl
theorem c183 : rowCell vs r 183 = (match digOf (rec vs r.n).v r with | some (_, _, true) => 1 | _ => 0) + (match digOf (rec vs r.n).v r with | some (_, _, false) => b2n (twOf (rec vs r.n).v) | _ => 0) := by
  rfl
theorem c184 : rowCell vs r 184 = b2n (r.f.isBm ∧ r.idx = 0) := by
  rfl
theorem c185 : rowCell vs r 185 = (rec vs r.n).mU.getD r.pos 0 := by
  rfl

end
end Rc

syntax "node_rc3" "[" (Lean.Parser.Tactic.simpLemma),* "]" : tactic
macro_rules
  | `(tactic| node_rc3 [$ts,*]) => `(tactic| simp only [Rc.c0, Rc.c1, Rc.c2, Rc.c3, Rc.c4, Rc.c5, Rc.c6, Rc.c7, Rc.c8, Rc.c9, Rc.c10, Rc.c11, Rc.c12, Rc.c13, Rc.c14, Rc.c15, Rc.c16, Rc.c17, Rc.c18, Rc.c19, Rc.c20, Rc.c21, Rc.c22, Rc.c23, Rc.c24, Rc.c25, Rc.c26, Rc.c27, Rc.c28, Rc.c29, Rc.c30, Rc.c31, Rc.c32, Rc.c33, Rc.c34, Rc.c35, Rc.c36, Rc.c37, Rc.c38, Rc.c39, Rc.c40, Rc.c41, Rc.c42, Rc.c43, Rc.c44, Rc.c45, Rc.c46, Rc.c47, Rc.c48, Rc.c49, Rc.c50, Rc.c51, Rc.c52, Rc.c53, Rc.c54, Rc.c55, Rc.c56, Rc.c57, Rc.c58, Rc.c59, Rc.c60, Rc.c61, Rc.c62, Rc.c63, Rc.c64, Rc.c65, Rc.c66, Rc.c67, Rc.c68, Rc.c69, Rc.c70, Rc.c71, Rc.c72, Rc.c73, Rc.c74, Rc.c75, Rc.c76, Rc.c77, Rc.c78, Rc.c79, Rc.c80, Rc.c81, Rc.c82, Rc.c83, Rc.c84, Rc.c85, Rc.c86, Rc.c87, Rc.c88, Rc.c89, Rc.c90, Rc.c91, Rc.c92, Rc.c93, Rc.c94, Rc.c95, Rc.c96, Rc.c97, Rc.c98, Rc.c99, Rc.c100, Rc.c101, Rc.c102, Rc.c103, Rc.c104, Rc.c105, Rc.c106, Rc.c107, Rc.c108, Rc.c109, Rc.c110, Rc.c111, Rc.c112, Rc.c113, Rc.c114, Rc.c115, Rc.c116, Rc.c117, Rc.c118, Rc.c119, Rc.c120, Rc.c121, Rc.c122, Rc.c123, Rc.c124, Rc.c125, Rc.c126, Rc.c127, Rc.c128, Rc.c129, Rc.c130, Rc.c131, Rc.c132, Rc.c133, Rc.c134, Rc.c135, Rc.c136, Rc.c137, Rc.c138, Rc.c139, Rc.c140, Rc.c141, Rc.c142, Rc.c143, Rc.c144, Rc.c145, Rc.c146, Rc.c147, Rc.c148, Rc.c149, Rc.c150, Rc.c151, Rc.c152, Rc.c153, Rc.c154, Rc.c155, Rc.c156, Rc.c157, Rc.c158, Rc.c159, Rc.c160, Rc.c161, Rc.c162, Rc.c163, Rc.c164, Rc.c165, Rc.c166, Rc.c167, Rc.c168, Rc.c169, Rc.c170, Rc.c171, Rc.c172, Rc.c173, Rc.c174, Rc.c175, Rc.c176, Rc.c177, Rc.c178, Rc.c179, Rc.c180, Rc.c181, Rc.c182, Rc.c183, Rc.c184, $ts,*])

end NodeGen3

end ZkFormal.NearV3.Render
