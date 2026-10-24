#[path="support/receipt_batch_wire.rs"] mod wire;
fn main(){
 let dir=std::path::PathBuf::from(std::env::args().nth(1).unwrap());let mut cases=0;let mut negatives=0;
 for e in std::fs::read_dir(dir).unwrap(){let p=e.unwrap().path();if p.extension().is_none_or(|x|x!="public"){continue;}let public=std::fs::read(&p).unwrap();let ctx=std::fs::read(p.with_extension("context")).unwrap();let root=std::fs::read(p.with_extension("root")).unwrap();assert_eq!(wire::outcome_root(&public,&ctx).unwrap().as_slice(),root);cases+=1;let packed=wire::compact(&public).unwrap();assert_eq!(wire::expand(&packed).unwrap(),public);
 let mut bad=packed.clone();bad.push(0);assert!(wire::expand(&bad).is_err());negatives+=1;
 let mut bad=packed.clone();bad[32]^=1;assert!(wire::expand(&bad).is_err());negatives+=1;
 if packed.len()>36{let mut bad=packed.clone();bad[36]=255;assert!(wire::expand(&bad).is_err());negatives+=1;let mut bad=packed.clone();bad[37]=0;assert!(wire::expand(&bad).is_err());negatives+=1;}
  let wrong=|data:&[u8]|assert!(match wire::outcome_root(data,&ctx){Err(_)=>true,Ok(r)=>r.as_slice()!=root});
  let mut bad=ctx.clone();bad[0]^=1;assert!(wire::outcome_root(&public,&bad).is_err());negatives+=1;
  let mut bad=public.clone();bad[0]^=1;wrong(&bad);negatives+=1;
  wrong(&public[..public.len()-1]);negatives+=1;
  let mut bad=public.clone();bad.push(0);wrong(&bad);negatives+=1;
  if let Some(i)=public[24..].chunks_exact(88).position(|r|r[0]==1){let off=24+88*i;
   for delta in [8usize,24,56]{let mut bad=public.clone();bad[off+delta]^=1;wrong(&bad);negatives+=1;}
   let mut bad=public.clone();bad[off+16..off+24].fill(0);wrong(&bad);negatives+=1;
  }
  let i=public[24..].chunks_exact(88).position(|r|r[0]==0).unwrap();let mut bad=public.clone();bad[24+88*i+56]=1;wrong(&bad);negatives+=1;
 }
 assert_eq!(cases,66);println!("RECEIPT_BATCH_WIRE cases={cases} negatives={negatives} roots_match_independent_fixtures=true");
}
