import ZkFormal.NearV3.Assembly.RcptEmittedTrace
open ZkFormal.NearV3.RcptV3
#eval (reg 0,reg 32,tok 0,tok 16,xb 0,xb 66,b)
#eval boolCols.filter (fun c=>tok 0≤c && c<tok 16)
#eval boolCols.filter (fun c=>reg 0≤c && c<reg 32)
#eval boolCols.filter (fun c=>c==j || c==nj || c==r || c==cj || c==o || c==oEnd || c==o2 || c==o2End || c==Lp || c==Lv || c==Ls || c==idx)
