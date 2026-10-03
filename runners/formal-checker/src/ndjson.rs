//! Trusted reader for the lean4export NDJSON format (v3.x) and structural
//! (Merkle) hashing of declarations.
//!
//! This is the judge's *independent* view of an environment: it never maps an
//! `.olean`, it parses plain data with strict index discipline (every
//! reference must point backwards), and it compares candidate declarations to
//! the judge's reference export by content hash. Binder names, binder info,
//! `mdata` and reducibility hints are ignored (they do not affect kernel
//! meaning); everything else — names, universe levels, literals, structure —
//! is hashed.

use serde_json::Value;
use sha2::{Digest as _, Sha256};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::io::BufRead;
use std::path::Path;

pub type H = [u8; 32];

#[derive(Debug, thiserror::Error)]
pub enum ExportError {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("malformed export line {line}: {msg}")]
    Malformed { line: usize, msg: String },
    #[error("export too large")]
    TooLarge,
}

#[derive(Clone, Debug)]
enum LevelNode {
    Zero,
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

#[derive(Clone, Debug)]
pub enum ExprNode {
    BVar(u64),
    Sort(u32),
    Const(u32, Vec<u32>),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32),
    Proj(u32, u64, u32),
    NatLit(String),
    StrLit(String),
    MData(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DeclKind {
    Axiom,
    Def,
    Thm,
    Opaque,
    Quot,
    Inductive,
    Ctor,
    Rec,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: DeclKind,
    pub name: String,
    pub level_params: Vec<String>,
    pub ty: u32,
    pub value: Option<u32>,
    pub is_unsafe: bool,
    pub is_partial: bool,
    /// Names this declaration structurally depends on beyond its exprs
    /// (inductive ↔ constructors, recursor ↔ inductive group).
    pub extra_deps: Vec<String>,
    /// Extra exprs (recursor rule right-hand sides).
    pub extra_exprs: Vec<u32>,
    /// Kind-specific metadata folded into the decl hash.
    pub meta: Vec<u8>,
}

pub struct Export {
    pub meta: Value,
    name_str: Vec<String>,
    levels: Vec<LevelNode>,
    level_h: Vec<H>,
    pub exprs: Vec<ExprNode>,
    expr_h: Vec<H>,
    pub decls: HashMap<String, Decl>,
    pub decl_order: Vec<String>,
}

fn h_init(tag: &[u8]) -> Sha256 {
    let mut h = Sha256::new();
    h.update((tag.len() as u64).to_le_bytes());
    h.update(tag);
    h
}
fn h_bytes(h: &mut Sha256, b: &[u8]) {
    h.update((b.len() as u64).to_le_bytes());
    h.update(b);
}

fn malformed(line: usize, msg: impl Into<String>) -> ExportError {
    ExportError::Malformed { line, msg: msg.into() }
}

fn as_u32(v: &Value, line: usize, what: &str) -> Result<u32, ExportError> {
    v.as_u64().and_then(|x| u32::try_from(x).ok()).ok_or_else(|| malformed(line, format!("bad {what}")))
}

impl Export {
    pub fn read(path: &Path, max_bytes: u64) -> Result<Self, ExportError> {
        let len = std::fs::metadata(path)?.len();
        if len > max_bytes {
            return Err(ExportError::TooLarge);
        }
        let f = std::io::BufReader::with_capacity(1 << 20, std::fs::File::open(path)?);
        let mut ex = Export {
            meta: Value::Null,
            name_str: vec![String::new()],
            levels: vec![LevelNode::Zero],
            level_h: vec![h_init(b"lz").finalize().into()],
            exprs: Vec::new(),
            expr_h: Vec::new(),
            decls: HashMap::new(),
            decl_order: Vec::new(),
        };
        for (i, line) in f.lines().enumerate() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            let v: Value = serde_json::from_str(&line).map_err(|e| malformed(i + 1, e.to_string()))?;
            ex.ingest(i + 1, v)?;
        }
        if ex.meta.is_null() {
            return Err(malformed(0, "missing meta header"));
        }
        Ok(ex)
    }

    fn name_ref(&self, v: &Value, line: usize) -> Result<u32, ExportError> {
        let i = as_u32(v, line, "name index")?;
        if (i as usize) < self.name_str.len() {
            Ok(i)
        } else {
            Err(malformed(line, "forward name reference"))
        }
    }
    fn level_ref(&self, v: &Value, line: usize) -> Result<u32, ExportError> {
        let i = as_u32(v, line, "level index")?;
        if (i as usize) < self.levels.len() {
            Ok(i)
        } else {
            Err(malformed(line, "forward level reference"))
        }
    }
    fn expr_ref(&self, v: &Value, line: usize) -> Result<u32, ExportError> {
        let i = as_u32(v, line, "expr index")?;
        if (i as usize) < self.exprs.len() {
            Ok(i)
        } else {
            Err(malformed(line, "forward expr reference"))
        }
    }

    pub fn name(&self, i: u32) -> &str {
        &self.name_str[i as usize]
    }

    fn ingest(&mut self, line: usize, v: Value) -> Result<(), ExportError> {
        let o = v.as_object().ok_or_else(|| malformed(line, "not an object"))?;
        if let Some(m) = o.get("meta") {
            if !self.meta.is_null() {
                return Err(malformed(line, "duplicate meta"));
            }
            self.meta = m.clone();
            return Ok(());
        }
        if let Some(idx) = o.get("in") {
            let idx = as_u32(idx, line, "in")?;
            if idx as usize != self.name_str.len() {
                return Err(malformed(line, "non-sequential name index"));
            }
            let s = if let Some(s) = o.get("str") {
                let pre = self.name_ref(&s["pre"], line)?;
                let comp = s["str"].as_str().ok_or_else(|| malformed(line, "name str"))?.to_string();
                let shown = if comp.is_empty() || comp.contains('.') || comp.starts_with(|c: char| c.is_ascii_digit()) {
                    format!("«{comp}»")
                } else {
                    comp.clone()
                };
                let p = &self.name_str[pre as usize];
                if p.is_empty() { shown } else { format!("{p}.{shown}") }
            } else if let Some(n) = o.get("num") {
                let pre = self.name_ref(&n["pre"], line)?;
                let k = n["i"].as_u64().ok_or_else(|| malformed(line, "name num"))?;
                let p = &self.name_str[pre as usize];
                if p.is_empty() { k.to_string() } else { format!("{p}.{k}") }
            } else {
                return Err(malformed(line, "unknown name node"));
            };
            self.name_str.push(s);
            return Ok(());
        }
        if let Some(idx) = o.get("il") {
            let idx = as_u32(idx, line, "il")?;
            if idx as usize != self.levels.len() {
                return Err(malformed(line, "non-sequential level index"));
            }
            let node = if let Some(x) = o.get("succ") {
                LevelNode::Succ(self.level_ref(x, line)?)
            } else if let Some(x) = o.get("max") {
                LevelNode::Max(self.level_ref(&x[0], line)?, self.level_ref(&x[1], line)?)
            } else if let Some(x) = o.get("imax") {
                LevelNode::IMax(self.level_ref(&x[0], line)?, self.level_ref(&x[1], line)?)
            } else if let Some(x) = o.get("param") {
                LevelNode::Param(self.name_ref(x, line)?)
            } else {
                return Err(malformed(line, "unknown level node"));
            };
            let h = self.hash_level(&node, None);
            self.levels.push(node);
            self.level_h.push(h);
            return Ok(());
        }
        if let Some(idx) = o.get("ie") {
            let idx = as_u32(idx, line, "ie")?;
            if idx as usize != self.exprs.len() {
                return Err(malformed(line, "non-sequential expr index"));
            }
            let node = if let Some(x) = o.get("bvar") {
                ExprNode::BVar(x.as_u64().ok_or_else(|| malformed(line, "bvar"))?)
            } else if let Some(x) = o.get("sort") {
                ExprNode::Sort(self.level_ref(x, line)?)
            } else if let Some(x) = o.get("const") {
                let n = self.name_ref(&x["name"], line)?;
                let us = x["us"].as_array().ok_or_else(|| malformed(line, "const us"))?;
                let us = us.iter().map(|u| self.level_ref(u, line)).collect::<Result<Vec<_>, _>>()?;
                ExprNode::Const(n, us)
            } else if let Some(x) = o.get("app") {
                ExprNode::App(self.expr_ref(&x["fn"], line)?, self.expr_ref(&x["arg"], line)?)
            } else if let Some(x) = o.get("lam") {
                self.name_ref(&x["name"], line)?;
                ExprNode::Lam(self.expr_ref(&x["type"], line)?, self.expr_ref(&x["body"], line)?)
            } else if let Some(x) = o.get("forallE") {
                self.name_ref(&x["name"], line)?;
                ExprNode::Pi(self.expr_ref(&x["type"], line)?, self.expr_ref(&x["body"], line)?)
            } else if let Some(x) = o.get("letE") {
                self.name_ref(&x["name"], line)?;
                ExprNode::Let(
                    self.expr_ref(&x["type"], line)?,
                    self.expr_ref(&x["value"], line)?,
                    self.expr_ref(&x["body"], line)?,
                )
            } else if let Some(x) = o.get("proj") {
                ExprNode::Proj(
                    self.name_ref(&x["typeName"], line)?,
                    x["idx"].as_u64().ok_or_else(|| malformed(line, "proj idx"))?,
                    self.expr_ref(&x["struct"], line)?,
                )
            } else if let Some(x) = o.get("natVal") {
                let s = x.as_str().ok_or_else(|| malformed(line, "natVal"))?;
                if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(malformed(line, "natVal not decimal"));
                }
                let t = s.trim_start_matches('0');
                ExprNode::NatLit(if t.is_empty() { "0".into() } else { t.into() })
            } else if let Some(x) = o.get("strVal") {
                ExprNode::StrLit(x.as_str().ok_or_else(|| malformed(line, "strVal"))?.to_string())
            } else if let Some(x) = o.get("mdata") {
                ExprNode::MData(self.expr_ref(&x["expr"], line)?)
            } else {
                return Err(malformed(line, "unknown expr node"));
            };
            let h = self.hash_expr_node(&node, None, &mut HashMap::new());
            self.exprs.push(node);
            self.expr_h.push(h);
            return Ok(());
        }
        self.ingest_decl(line, o)
    }

    fn names_of(&self, v: &Value, line: usize) -> Result<Vec<String>, ExportError> {
        let arr = v.as_array().ok_or_else(|| malformed(line, "expected name array"))?;
        arr.iter().map(|x| Ok(self.name(self.name_ref(x, line)?).to_string())).collect()
    }

    fn push_decl(&mut self, line: usize, d: Decl) -> Result<(), ExportError> {
        if self.decls.contains_key(&d.name) {
            return Err(malformed(line, format!("duplicate declaration {}", d.name)));
        }
        self.decl_order.push(d.name.clone());
        self.decls.insert(d.name.clone(), d);
        Ok(())
    }

    fn ingest_decl(&mut self, line: usize, o: &serde_json::Map<String, Value>) -> Result<(), ExportError> {
        let b = |v: &Value| v.as_bool().unwrap_or(false);
        let simple = |s: &Self, x: &Value, kind: DeclKind| -> Result<Decl, ExportError> {
            Ok(Decl {
                kind,
                name: s.name(s.name_ref(&x["name"], line)?).to_string(),
                level_params: s.names_of(&x["levelParams"], line)?,
                ty: s.expr_ref(&x["type"], line)?,
                value: None,
                is_unsafe: false,
                is_partial: false,
                extra_deps: vec![],
                extra_exprs: vec![],
                meta: vec![],
            })
        };
        if let Some(x) = o.get("axiom") {
            let mut d = simple(self, x, DeclKind::Axiom)?;
            d.is_unsafe = b(&x["isUnsafe"]);
            return self.push_decl(line, d);
        }
        if let Some(x) = o.get("def") {
            let mut d = simple(self, x, DeclKind::Def)?;
            d.value = Some(self.expr_ref(&x["value"], line)?);
            let safety = x["safety"].as_str().unwrap_or("safe");
            d.is_unsafe = safety == "unsafe";
            d.is_partial = safety == "partial";
            d.meta = safety.as_bytes().to_vec();
            return self.push_decl(line, d);
        }
        if let Some(x) = o.get("thm") {
            let mut d = simple(self, x, DeclKind::Thm)?;
            d.value = Some(self.expr_ref(&x["value"], line)?);
            return self.push_decl(line, d);
        }
        if let Some(x) = o.get("opaque") {
            let mut d = simple(self, x, DeclKind::Opaque)?;
            d.value = Some(self.expr_ref(&x["value"], line)?);
            d.is_unsafe = b(&x["isUnsafe"]);
            return self.push_decl(line, d);
        }
        if let Some(x) = o.get("quot") {
            let mut d = simple(self, x, DeclKind::Quot)?;
            d.meta = x["kind"].as_str().unwrap_or("").as_bytes().to_vec();
            return self.push_decl(line, d);
        }
        if let Some(x) = o.get("inductive") {
            // Group digest: every type and constructor with its metadata.
            let mut gh = h_init(b"ind-group");
            let types = x["types"].as_array().ok_or_else(|| malformed(line, "inductive types"))?;
            let ctors = x["ctors"].as_array().ok_or_else(|| malformed(line, "inductive ctors"))?;
            let recs = x["recs"].as_array().ok_or_else(|| malformed(line, "inductive recs"))?;
            let mut group_names = Vec::new();
            let mut pending = Vec::new();
            for t in types {
                let mut d = simple(self, t, DeclKind::Inductive)?;
                d.is_unsafe = b(&t["isUnsafe"]);
                let ctor_names = self.names_of(&t["ctors"], line)?;
                let all = self.names_of(&t["all"], line)?;
                for k in ["numParams", "numIndices", "numNested"] {
                    gh.update(t[k].as_u64().unwrap_or(u64::MAX).to_le_bytes());
                }
                gh.update([b(&t["isRec"]) as u8, d.is_unsafe as u8, b(&t["isReflexive"]) as u8]);
                h_bytes(&mut gh, d.name.as_bytes());
                h_bytes(&mut gh, &self.lps_bytes(&d.level_params));
                gh.update(self.expr_h[d.ty as usize]);
                for c in &ctor_names {
                    h_bytes(&mut gh, c.as_bytes());
                }
                d.extra_deps = ctor_names.into_iter().chain(all).collect();
                group_names.push(d.name.clone());
                pending.push(d);
            }
            for c in ctors {
                let mut d = simple(self, c, DeclKind::Ctor)?;
                d.is_unsafe = b(&c["isUnsafe"]);
                let induct = self.name(self.name_ref(&c["induct"], line)?).to_string();
                for k in ["cidx", "numParams", "numFields"] {
                    gh.update(c[k].as_u64().unwrap_or(u64::MAX).to_le_bytes());
                }
                h_bytes(&mut gh, d.name.as_bytes());
                h_bytes(&mut gh, induct.as_bytes());
                h_bytes(&mut gh, &self.lps_bytes(&d.level_params));
                gh.update(self.expr_h[d.ty as usize]);
                d.extra_deps = vec![induct];
                pending.push(d);
            }
            for r in recs {
                let mut d = simple(self, r, DeclKind::Rec)?;
                d.is_unsafe = b(&r["isUnsafe"]);
                d.extra_deps = self.names_of(&r["all"], line)?;
                let mut rm = Vec::new();
                for k in ["numParams", "numIndices", "numMotives", "numMinors"] {
                    rm.extend(r[k].as_u64().unwrap_or(u64::MAX).to_le_bytes());
                }
                rm.push(b(&r["k"]) as u8);
                for rule in r["rules"].as_array().ok_or_else(|| malformed(line, "rec rules"))? {
                    let rhs = self.expr_ref(&rule["rhs"], line)?;
                    let ctor = self.name(self.name_ref(&rule["ctor"], line)?).to_string();
                    rm.extend((ctor.len() as u64).to_le_bytes());
                    rm.extend(ctor.as_bytes());
                    rm.extend(rule["nfields"].as_u64().unwrap_or(u64::MAX).to_le_bytes());
                    rm.extend(self.expr_h[rhs as usize]);
                    d.extra_exprs.push(rhs);
                    d.extra_deps.push(ctor);
                }
                d.meta = rm;
                pending.push(d);
            }
            let group: H = gh.finalize().into();
            for mut d in pending {
                d.meta.extend_from_slice(&group);
                self.push_decl(line, d)?;
            }
            return Ok(());
        }
        Err(malformed(line, "unknown record"))
    }

    fn lps_bytes(&self, lps: &[String]) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend((lps.len() as u64).to_le_bytes());
        for l in lps {
            v.extend((l.len() as u64).to_le_bytes());
            v.extend(l.as_bytes());
        }
        v
    }

    fn hash_level(&self, n: &LevelNode, subst: Option<&HashMap<String, String>>) -> H {
        match n {
            LevelNode::Zero => h_init(b"lz").finalize().into(),
            LevelNode::Succ(a) => {
                let mut h = h_init(b"ls");
                h.update(self.level_hash(*a, subst));
                h.finalize().into()
            }
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => {
                let mut h = h_init(if matches!(n, LevelNode::Max(..)) { b"lm" } else { b"li" });
                h.update(self.level_hash(*a, subst));
                h.update(self.level_hash(*b, subst));
                h.finalize().into()
            }
            LevelNode::Param(nm) => {
                let mut h = h_init(b"lp");
                let s = self.name(*nm);
                let s = subst.and_then(|m| m.get(s)).map(String::as_str).unwrap_or(s);
                h_bytes(&mut h, s.as_bytes());
                h.finalize().into()
            }
        }
    }
    fn level_hash(&self, i: u32, subst: Option<&HashMap<String, String>>) -> H {
        match subst {
            None => self.level_h[i as usize],
            Some(_) => self.hash_level(&self.levels[i as usize], subst),
        }
    }

    fn hash_expr_node(&self, n: &ExprNode, subst: Option<&HashMap<String, String>>, memo: &mut HashMap<u32, H>) -> H {
        let sub = |i: u32, me: &Self, memo: &mut HashMap<u32, H>| -> H {
            match subst {
                None => me.expr_h[i as usize],
                Some(_) => me.expr_hash_subst(i, subst, memo),
            }
        };
        match n {
            ExprNode::BVar(i) => {
                let mut h = h_init(b"eb");
                h.update(i.to_le_bytes());
                h.finalize().into()
            }
            ExprNode::Sort(l) => {
                let mut h = h_init(b"es");
                h.update(self.level_hash(*l, subst));
                h.finalize().into()
            }
            ExprNode::Const(nm, us) => {
                let mut h = h_init(b"ec");
                h_bytes(&mut h, self.name(*nm).as_bytes());
                h.update((us.len() as u64).to_le_bytes());
                for u in us {
                    h.update(self.level_hash(*u, subst));
                }
                h.finalize().into()
            }
            ExprNode::App(f, a) => {
                let mut h = h_init(b"ea");
                h.update(sub(*f, self, memo));
                h.update(sub(*a, self, memo));
                h.finalize().into()
            }
            ExprNode::Lam(t, b) | ExprNode::Pi(t, b) => {
                let mut h = h_init(if matches!(n, ExprNode::Lam(..)) { b"el" } else { b"ep" });
                h.update(sub(*t, self, memo));
                h.update(sub(*b, self, memo));
                h.finalize().into()
            }
            ExprNode::Let(t, v, b) => {
                let mut h = h_init(b"ez");
                h.update(sub(*t, self, memo));
                h.update(sub(*v, self, memo));
                h.update(sub(*b, self, memo));
                h.finalize().into()
            }
            ExprNode::Proj(nm, i, e) => {
                let mut h = h_init(b"ej");
                h_bytes(&mut h, self.name(*nm).as_bytes());
                h.update(i.to_le_bytes());
                h.update(sub(*e, self, memo));
                h.finalize().into()
            }
            ExprNode::NatLit(s) => {
                let mut h = h_init(b"en");
                h_bytes(&mut h, s.as_bytes());
                h.finalize().into()
            }
            ExprNode::StrLit(s) => {
                let mut h = h_init(b"et");
                h_bytes(&mut h, s.as_bytes());
                h.finalize().into()
            }
            // mdata is transparent
            ExprNode::MData(e) => sub(*e, self, memo),
        }
    }

    fn expr_hash_subst(&self, i: u32, subst: Option<&HashMap<String, String>>, memo: &mut HashMap<u32, H>) -> H {
        if subst.is_none() {
            return self.expr_h[i as usize];
        }
        if let Some(h) = memo.get(&i) {
            return *h;
        }
        // Iterative-ish: recursion depth is bounded by expression depth; the
        // export is bounded in size, and we cap depth via an explicit stack.
        let h = stacker_hash(self, i, subst, memo);
        memo.insert(i, h);
        h
    }

    /// Structural hash of expression `i`, optionally renaming universe params.
    pub fn expr_hash(&self, i: u32, subst: Option<&HashMap<String, String>>) -> H {
        self.expr_hash_subst(i, subst, &mut HashMap::new())
    }

    /// Strip outer mdata.
    pub fn unmdata(&self, mut i: u32) -> u32 {
        while let ExprNode::MData(e) = self.exprs[i as usize] {
            i = e;
        }
        i
    }

    /// Content hash of a whole declaration (kind, name, universe params, type,
    /// value, safety, kind metadata).
    pub fn decl_hash(&self, d: &Decl) -> H {
        let mut h = h_init(b"decl");
        h_bytes(&mut h, format!("{:?}", d.kind).as_bytes());
        h_bytes(&mut h, d.name.as_bytes());
        h_bytes(&mut h, &self.lps_bytes(&d.level_params));
        h.update(self.expr_h[d.ty as usize]);
        match d.value {
            Some(v) => {
                h.update([1]);
                h.update(self.expr_h[v as usize]);
            }
            None => h.update([0]),
        }
        h.update([d.is_unsafe as u8, d.is_partial as u8]);
        h_bytes(&mut h, &d.meta);
        h.finalize().into()
    }

    /// Constant names occurring in expression `root` (DAG walk, shared memo).
    pub fn consts_in(&self, root: u32, seen: &mut HashSet<u32>, out: &mut BTreeSet<String>) {
        let mut stack = vec![root];
        while let Some(i) = stack.pop() {
            if !seen.insert(i) {
                continue;
            }
            match &self.exprs[i as usize] {
                ExprNode::Const(n, _) => {
                    out.insert(self.name(*n).to_string());
                }
                ExprNode::App(a, b) | ExprNode::Lam(a, b) | ExprNode::Pi(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                ExprNode::Let(a, b, c) => {
                    stack.extend([*a, *b, *c]);
                }
                ExprNode::Proj(n, _, e) => {
                    // projections depend on the structure type
                    out.insert(self.name(*n).to_string());
                    stack.push(*e);
                }
                ExprNode::MData(e) => stack.push(*e),
                _ => {}
            }
        }
    }

    pub fn decl_deps(&self, d: &Decl) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let mut seen = HashSet::new();
        self.consts_in(d.ty, &mut seen, &mut out);
        if let Some(v) = d.value {
            self.consts_in(v, &mut seen, &mut out);
        }
        for e in &d.extra_exprs {
            self.consts_in(*e, &mut seen, &mut out);
        }
        out.extend(d.extra_deps.iter().cloned());
        out
    }

    /// Transitive closure of declarations reachable from `roots`.
    /// Returns (present names, missing names).
    pub fn closure<I: IntoIterator<Item = String>>(&self, roots: I) -> (BTreeSet<String>, BTreeSet<String>) {
        let mut present = BTreeSet::new();
        let mut missing = BTreeSet::new();
        let mut stack: Vec<String> = roots.into_iter().collect();
        while let Some(n) = stack.pop() {
            if present.contains(&n) || missing.contains(&n) {
                continue;
            }
            match self.decls.get(&n) {
                None => {
                    missing.insert(n);
                }
                Some(d) => {
                    for dep in self.decl_deps(d) {
                        if !present.contains(&dep) {
                            stack.push(dep);
                        }
                    }
                    present.insert(n);
                }
            }
        }
        (present, missing)
    }

    /// If `e` is `@And.intro a b pa pb` return (pa, pb).
    pub fn as_and_intro(&self, e: u32) -> Option<(u32, u32)> {
        let e = self.unmdata(e);
        let ExprNode::App(f1, pb) = self.exprs[e as usize] else { return None };
        let ExprNode::App(f2, pa) = self.exprs[self.unmdata(f1) as usize] else { return None };
        let ExprNode::App(f3, _b) = self.exprs[self.unmdata(f2) as usize] else { return None };
        let ExprNode::App(f4, _a) = self.exprs[self.unmdata(f3) as usize] else { return None };
        match &self.exprs[self.unmdata(f4) as usize] {
            ExprNode::Const(n, _) if self.name(*n) == "And.intro" => Some((pa, pb)),
            _ => None,
        }
    }

    pub fn const_head(&self, e: u32) -> Option<(&str, &[u32])> {
        match &self.exprs[self.unmdata(e) as usize] {
            ExprNode::Const(n, us) => Some((self.name(*n), us.as_slice())),
            _ => None,
        }
    }

    pub fn level_is_param(&self, l: u32, name: &str) -> bool {
        matches!(self.levels[l as usize], LevelNode::Param(n) if self.name(n) == name)
    }
}

/// Explicit-stack structural hash with universe substitution (avoids deep recursion).
fn stacker_hash(ex: &Export, root: u32, subst: Option<&HashMap<String, String>>, memo: &mut HashMap<u32, H>) -> H {
    let mut stack = vec![(root, false)];
    while let Some((i, ready)) = stack.pop() {
        if memo.contains_key(&i) {
            continue;
        }
        let node = &ex.exprs[i as usize];
        let kids: Vec<u32> = match node {
            ExprNode::App(a, b) | ExprNode::Lam(a, b) | ExprNode::Pi(a, b) => vec![*a, *b],
            ExprNode::Let(a, b, c) => vec![*a, *b, *c],
            ExprNode::Proj(_, _, e) | ExprNode::MData(e) => vec![*e],
            _ => vec![],
        };
        if ready || kids.iter().all(|k| memo.contains_key(k)) {
            let h = ex.hash_expr_node(node, subst, memo);
            memo.insert(i, h);
        } else {
            stack.push((i, true));
            for k in kids {
                if !memo.contains_key(&k) {
                    stack.push((k, false));
                }
            }
        }
    }
    memo[&root]
}

/// Hash of `Expr.const name []` (same encoding as `hash_expr_node`).
pub fn const_hash(name: &str) -> H {
    let mut h = h_init(b"ec");
    h_bytes(&mut h, name.as_bytes());
    h.update(0u64.to_le_bytes());
    h.finalize().into()
}

impl Export {
    /// If `lam` is `fun x => body`, the structural hash of `body[x := c]`
    /// where `repl` is the hash of `c` (a closed term).
    pub fn lambda_body_instantiated(&self, lam: u32, repl: &H) -> Option<H> {
        let ExprNode::Lam(_, body) = self.exprs[self.unmdata(lam) as usize] else { return None };
        let mut memo = HashMap::new();
        Some(self.hash_inst(body, 0, repl, &mut memo))
    }

    fn hash_inst(&self, i: u32, depth: u64, repl: &H, memo: &mut HashMap<(u32, u64), H>) -> H {
        if let Some(h) = memo.get(&(i, depth)) {
            return *h;
        }
        let node = &self.exprs[i as usize];
        let h: H = match node {
            ExprNode::BVar(k) if *k == depth => *repl,
            ExprNode::BVar(k) if *k > depth => {
                let mut h = h_init(b"eb");
                h.update((k - 1).to_le_bytes());
                h.finalize().into()
            }
            ExprNode::App(f, a) => {
                let mut h = h_init(b"ea");
                h.update(self.hash_inst(*f, depth, repl, memo));
                h.update(self.hash_inst(*a, depth, repl, memo));
                h.finalize().into()
            }
            ExprNode::Lam(t, b) | ExprNode::Pi(t, b) => {
                let mut h = h_init(if matches!(node, ExprNode::Lam(..)) { b"el" } else { b"ep" });
                h.update(self.hash_inst(*t, depth, repl, memo));
                h.update(self.hash_inst(*b, depth + 1, repl, memo));
                h.finalize().into()
            }
            ExprNode::Let(t, v, b) => {
                let mut h = h_init(b"ez");
                h.update(self.hash_inst(*t, depth, repl, memo));
                h.update(self.hash_inst(*v, depth, repl, memo));
                h.update(self.hash_inst(*b, depth + 1, repl, memo));
                h.finalize().into()
            }
            ExprNode::Proj(nm, k, e) => {
                let mut h = h_init(b"ej");
                h_bytes(&mut h, self.name(*nm).as_bytes());
                h.update(k.to_le_bytes());
                h.update(self.hash_inst(*e, depth, repl, memo));
                h.finalize().into()
            }
            ExprNode::MData(e) => self.hash_inst(*e, depth, repl, memo),
            // closed leaves (bvars below depth, sorts, consts, literals)
            _ => self.expr_h[i as usize],
        };
        memo.insert((i, depth), h);
        h
    }

    /// `Expr.app (Expr.const f []) (Expr.const x [])` → `(f, x)`.
    pub fn as_app_of_consts(&self, e: u32) -> Option<(String, String)> {
        let ExprNode::App(f, x) = self.exprs[self.unmdata(e) as usize] else { return None };
        let (fname, fus) = self.const_head(f)?;
        let (xname, xus) = self.const_head(x)?;
        (fus.is_empty() && xus.is_empty()).then(|| (fname.to_string(), xname.to_string()))
    }
}

pub fn hex(h: &H) -> String {
    hex::encode(h)
}
