// rivet: verifies VER-074
//! claim-check: gate ordeal's documentation claims against live evidence (TR-074).
//!
//! A README is a claim about the system, the same species as a requirement.
//! `claims.yaml` (repo root) binds each load-bearing doc claim (what is
//! proven, by which theorem, what is trusted, every stated number, the
//! badges) to evidence this tool re-derives from the tree. The required Test
//! job runs it natively on every change, and the wasm32-wasip2 job runs it as
//! a component under wasmtime; drift between a claim and the source fails the
//! build.
//!
//!   wasmtime run --dir . claim-check.wasm claims.yaml
//!   cargo run --release --manifest-path tools/claim-check/Cargo.toml -- claims.yaml
//!
//! Usage:  claim-check [claims.yaml]     (default: ./claims.yaml)
//!         claim-check --self-test        (every predicate, both ways)
//! Exit:   0 = all claims hold · 1 = one or more drifted, or a malformed
//!         claims file · 2 = no claims declared
//!
//! Evidence predicates (all paths and globs resolve against the claims file's
//! directory, never the CWD; a glob that matches no file FAILS, so a predicate
//! can never green by measuring nothing):
//!
//! ```text
//!   file-exists   path              the proof / harness the claim rests on is present
//!   count-min     pattern glob min  PRESENCE: the pattern must appear >= min times
//!                                   (catches drift-to-absent: a theorem renamed away,
//!                                   a version bumped, a CI step deleted)
//!   count-max     pattern glob max  GROWTH: the pattern may appear <= max times
//!                                   (zero-sorry / zero-axiom claims: max 0)
//!   no-new        pattern glob recorded  alias of count-max with the ledger's count
//!   verbatim      text              the string is in the doc (whitespace-normalised:
//!                                   a sentence re-wrapped by an editor still matches,
//!                                   a sentence re-worded does not)
//!   set-equal     left right [waive]  two sets of names agree in BOTH directions; a side
//!                                   is {glob, name} (group 1 of each matching path) or
//!                                   {file, pattern [, after, before]} (group 1 of each
//!                                   match in the doc, optionally between two markers).
//!                                   An EMPTY side fails. `waive` is printed every run.
//!   count-equals  number set        a number stated in prose == the size of a set on disk
//! ```
//!
//! Claim shape:
//!
//! ```text
//!   - id: README-TRUSTED-BASE
//!     doc: README.md
//!     text: "…"      # optional; must appear in `doc` (normalised)
//!     epoch: "…"     # optional; what expires this claim even while its evidence
//!                    #   still passes (printed, so the reader sees the bound)
//!     evidence: [ {kind: …}, … ]
//! ```
//!
//! History: ported from `scripts/claim_check.py` (2026-11-27, #351), which it
//! matched on 944 of 944 cases before the script was retired. The Python
//! runtime semantics that reached the output (universal newlines,
//! `errors="ignore"` decoding, `str.isspace`, `repr`, `str()` of lists) are
//! still reproduced, so the output did not change at the switch.

use fancy_regex::Regex;
use rivet_yaml::Value;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::exit;

/// Where the Python script would raise (KeyError, TypeError, re.error, …) and
/// exit 1 with a traceback on stderr.
struct Internal(String);
type R<T> = Result<T, Internal>;

fn internal<T>(m: impl Into<String>) -> R<T> {
    Err(Internal(m.into()))
}

const DEFAULT_NAME: &str = r"([^/]+?)(?:\.[^/.]+)?$";

// ── Python runtime semantics ─────────────────────────────────────────────

/// `str.isspace()` (what `\s` and `str.strip()` use): Unicode White_Space plus
/// the four information separators U+001C..U+001F.
fn is_py_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// `_norm`: collapse every run of whitespace to one space, strip the ends.
fn norm(s: &str) -> String {
    s.split(is_py_space)
        .filter(|w| !w.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// `Path.read_text(errors="ignore")`: UTF-8, invalid bytes dropped, universal
/// newlines (`\r\n` and lone `\r` read as `\n`).
fn read_text(p: &Path) -> std::io::Result<String> {
    let bytes = std::fs::read(p)?;
    let mut out = String::with_capacity(bytes.len());
    let mut rest = &bytes[..];
    loop {
        match std::str::from_utf8(rest) {
            Ok(s) => {
                out.push_str(s);
                break;
            }
            Err(e) => {
                let ok = e.valid_up_to();
                out.push_str(std::str::from_utf8(&rest[..ok]).unwrap_or(""));
                match e.error_len() {
                    Some(n) => rest = &rest[ok + n..],
                    None => break, // truncated sequence at the end: ignored
                }
            }
        }
    }
    Ok(out.replace("\r\n", "\n").replace('\r', "\n"))
}

/// `repr(str)`.
fn py_repr_str(s: &str) -> String {
    let q = if s.contains('\'') && !s.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut o = String::new();
    o.push(q);
    for c in s.chars() {
        match c {
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if c == q => {
                o.push('\\');
                o.push(c);
            }
            c if (c as u32) < 0x20 || (0x7f..0xa0).contains(&(c as u32)) => {
                o.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => o.push(c),
        }
    }
    o.push(q);
    o
}

fn py_float(f: f64) -> String {
    if f.is_nan() {
        "nan".into()
    } else if f.is_infinite() {
        if f > 0.0 { "inf".into() } else { "-inf".into() }
    } else if f == f.trunc() && f.abs() < 1e16 {
        format!("{f:.1}")
    } else {
        format!("{f}")
    }
}

/// `repr(value)` for a YAML-loaded value.
fn py_repr(v: &Value) -> String {
    match v {
        Value::String(s) => py_repr_str(s),
        other => py_str(other),
    }
}

/// `str(value)` for a YAML-loaded value.
fn py_str(v: &Value) -> String {
    match v {
        Value::Null => "None".into(),
        Value::Bool(b) => if *b { "True" } else { "False" }.into(),
        Value::Number(n) => match (n.as_i64(), n.as_u64(), n.as_f64()) {
            (Some(i), _, _) => i.to_string(),
            (None, Some(u), _) => u.to_string(),
            (_, _, Some(f)) => py_float(f),
            _ => "?".into(),
        },
        Value::String(s) => s.clone(),
        Value::Sequence(xs) => format!(
            "[{}]",
            xs.iter().map(py_repr).collect::<Vec<_>>().join(", ")
        ),
        Value::Mapping(m) => format!(
            "{{{}}}",
            m.iter()
                .map(|(k, v)| format!("{}: {}", py_repr(k), py_repr(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Tagged(_) => "?".into(),
    }
}

/// Python truthiness of a loaded value.
fn truthy(v: Option<&Value>) -> bool {
    match v {
        None | Some(Value::Null) => false,
        Some(Value::Bool(b)) => *b,
        Some(Value::Number(n)) => n.as_f64().is_some_and(|f| f != 0.0),
        Some(Value::String(s)) => !s.is_empty(),
        Some(Value::Sequence(s)) => !s.is_empty(),
        Some(Value::Mapping(m)) => !m.is_empty(),
        Some(Value::Tagged(_)) => true,
    }
}

fn key<'a>(m: &'a Value, k: &str) -> R<&'a Value> {
    m.get(k)
        .ok_or_else(|| Internal(format!("KeyError: {}", py_repr_str(k))))
}

fn key_str<'a>(m: &'a Value, k: &str) -> R<&'a str> {
    key(m, k)?
        .as_str()
        .ok_or_else(|| Internal(format!("TypeError: {k} is not a string")))
}

fn key_int(m: &Value, k: &str) -> R<i64> {
    key(m, k)?
        .as_i64()
        .ok_or_else(|| Internal(format!("TypeError: {k} is not an integer")))
}

fn rx(pattern: &str, multiline: bool) -> R<Regex> {
    let p = if multiline {
        format!("(?m){pattern}")
    } else {
        pattern.to_string()
    };
    // Python's `re` has no backtracking cap; fancy-regex's default (10^6)
    // tripped on ARCH-SORRY-FREE-GATED over the Lean tree.
    fancy_regex::RegexBuilder::new(&p)
        .backtrack_limit(usize::MAX)
        .build()
        .map_err(|e| Internal(format!("re.error: {e} in /{pattern}/")))
}

/// `glob.glob(str(root / g), recursive=True)`.
fn pyglob(root: &Path, g: &str) -> R<Vec<PathBuf>> {
    let pat = root.join(g);
    let pat = pat
        .to_str()
        .ok_or_else(|| Internal("non-UTF-8 glob".into()))?;
    let opts = glob::MatchOptions {
        case_sensitive: true,
        require_literal_separator: true,
        require_literal_leading_dot: true,
    };
    let it = glob::glob_with(pat, opts).map_err(|e| Internal(format!("bad glob {g}: {e}")))?;
    Ok(it.filter_map(Result::ok).collect())
}

fn rel_posix(root: &Path, p: &Path) -> String {
    let r = p.strip_prefix(root).unwrap_or(p);
    r.components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/")
}

// ── the checker ──────────────────────────────────────────────────────────

fn globs_of(v: &Value) -> R<Vec<String>> {
    match v {
        Value::String(s) => Ok(vec![s.clone()]),
        Value::Sequence(xs) => xs
            .iter()
            .map(|x| {
                x.as_str()
                    .map(str::to_string)
                    .ok_or_else(|| Internal("TypeError: glob".into()))
            })
            .collect(),
        _ => internal("TypeError: glob must be a string or a list"),
    }
}

/// `_count`: (total matches, matched_any_file).
fn count(pattern: &str, globs: &Value, root: &Path) -> R<(usize, bool)> {
    let re = rx(pattern, true)?;
    let mut total = 0;
    let mut matched_any = false;
    for g in globs_of(globs)? {
        let mut files = pyglob(root, &g)?;
        files.sort_by(|a, b| a.to_string_lossy().cmp(&b.to_string_lossy()));
        for f in files {
            if f.is_file() {
                matched_any = true;
                let text = read_text(&f).map_err(|e| Internal(format!("{}: {e}", f.display())))?;
                for m in re.find_iter(&text) {
                    m.map_err(|e| Internal(format!("regex: {e}")))?;
                    total += 1;
                }
            }
        }
    }
    Ok((total, matched_any))
}

/// `re.findall` element: group 1 when the pattern has one group, the whole
/// match when it has none, the tuple of groups when it has more.
fn findall(re: &Regex, text: &str) -> R<Vec<String>> {
    let groups = re.captures_len() - 1;
    let mut out = Vec::new();
    for c in re.captures_iter(text) {
        let c = c.map_err(|e| Internal(format!("regex: {e}")))?;
        let g = |i: usize| c.get(i).map(|m| m.as_str()).unwrap_or("").to_string();
        out.push(match groups {
            0 => g(0),
            1 => g(1),
            n => {
                let parts: Vec<String> = (1..=n).map(|i| py_repr_str(&g(i))).collect();
                format!("({})", parts.join(", "))
            }
        });
    }
    Ok(out)
}

/// `_side`: a set of names, from paths on disk or from a doc.
fn side(spec: &Value, root: &Path) -> R<(BTreeSet<String>, Option<String>)> {
    if !spec.is_mapping() {
        return internal("TypeError: side must be a mapping");
    }
    if let Some(gv) = spec.get("glob") {
        let g = gv
            .as_str()
            .ok_or_else(|| Internal("TypeError: glob".into()))?;
        let name = match spec.get("name") {
            None => DEFAULT_NAME,
            Some(v) => v
                .as_str()
                .ok_or_else(|| Internal("TypeError: name".into()))?,
        };
        let re = rx(name, false)?;
        if re.captures_len() < 2 {
            return internal("IndexError: no such group");
        }
        let mut names = BTreeSet::new();
        for f in pyglob(root, g)? {
            let rel = rel_posix(root, &f);
            if let Some(c) = re
                .captures(&rel)
                .map_err(|e| Internal(format!("regex: {e}")))?
            {
                match c.get(1) {
                    Some(m) => names.insert(m.as_str().to_string()),
                    None => names.insert("None".to_string()),
                };
            }
        }
        let err = names
            .is_empty()
            .then(|| format!("side matched NO paths: glob {}", py_repr_str(g)));
        return Ok((names, err));
    }
    if spec.get("file").is_some() {
        let file = key_str(spec, "file")?;
        let p = root.join(file);
        if !p.exists() {
            return Ok((
                BTreeSet::new(),
                Some(format!("side file not found: {file}")),
            ));
        }
        let mut text = read_text(&p).map_err(|e| Internal(format!("{file}: {e}")))?;
        if truthy(spec.get("after")) {
            let after = key_str(spec, "after")?;
            match text.find(after) {
                None => {
                    return Ok((
                        BTreeSet::new(),
                        Some(format!(
                            "section start {} not found in {file}",
                            py_repr_str(after)
                        )),
                    ));
                }
                Some(i) => text = text[i + after.len()..].to_string(),
            }
        }
        if truthy(spec.get("before")) {
            let before = key_str(spec, "before")?;
            if let Some(j) = text.find(before) {
                text.truncate(j);
            }
        }
        let re = rx(key_str(spec, "pattern")?, true)?;
        let names: BTreeSet<String> = findall(&re, &text)?.into_iter().collect();
        let err = names
            .is_empty()
            .then(|| format!("side pattern matched NOTHING in {file}"));
        return Ok((names, err));
    }
    Ok((
        BTreeSet::new(),
        Some("side needs either glob or file".into()),
    ))
}

fn check_claim(c: &Value, root: &Path) -> R<Vec<String>> {
    let mut fails = Vec::new();
    let doc_name = key_str(c, "doc")?;
    let doc_path = root.join(doc_name);
    if !doc_path.exists() {
        return Ok(vec![format!("doc not found: {doc_name}")]);
    }
    let doc = read_text(&doc_path).map_err(|e| Internal(format!("{doc_name}: {e}")))?;
    let doc_n = norm(&doc);

    if !truthy(c.get("evidence")) {
        fails.push("no evidence predicates: the claim is checked against nothing".to_string());
    }

    let text: Option<&str> = match c.get("text") {
        None | Some(Value::Null) => None,
        Some(Value::String(s)) => Some(s.as_str()),
        Some(v) if !truthy(Some(v)) => None,
        Some(_) => return internal("TypeError: text must be a string"),
    };
    if let Some(t) = text.filter(|t| !t.is_empty())
        && !doc_n.contains(&norm(t))
    {
        fails.push(format!(
            "claim text not found in {doc_name}: \"{}\"",
            norm(t)
        ));
    }

    let evidence: &[Value] = match c.get("evidence") {
        None => &[],
        Some(Value::Sequence(xs)) => xs,
        Some(_) => return internal("TypeError: evidence must be a list"),
    };
    for ev in evidence {
        if !ev.is_mapping() {
            return internal("AttributeError: evidence item has no .get");
        }
        let kind = ev.get("kind");
        match kind.and_then(Value::as_str) {
            Some("verbatim") => {
                let s: Option<&str> = match ev.get("text") {
                    Some(Value::String(s)) => Some(s.as_str()),
                    Some(v) if !truthy(Some(v)) => None,
                    Some(_) => return internal("TypeError: verbatim text must be a string"),
                    None => text,
                };
                match s.filter(|s| !s.is_empty()) {
                    None => fails.push("verbatim predicate with no text".into()),
                    Some(s) => {
                        if !doc_n.contains(&norm(s)) {
                            fails.push(format!(
                                "verbatim string absent from {doc_name}: \"{}\"",
                                norm(s)
                            ));
                        }
                    }
                }
            }
            Some("file-exists") => {
                let p = key_str(ev, "path")?;
                if !root.join(p).exists() {
                    fails.push(format!("evidence file missing: {p}"));
                }
            }
            Some(k @ ("count-max" | "no-new")) => {
                let limit = if k == "count-max" {
                    key_int(ev, "max")?
                } else {
                    match ev.get("recorded") {
                        None => 0,
                        Some(_) => key_int(ev, "recorded")?,
                    }
                };
                let pattern = key_str(ev, "pattern")?;
                let globs = key(ev, "glob")?;
                let (n, matched) = count(pattern, globs, root)?;
                if !matched {
                    fails.push(format!(
                        "predicate matched NO files (measures nothing): glob {}",
                        py_str(globs)
                    ));
                } else if n as i64 > limit {
                    fails.push(format!(
                        "count grew: {n} > recorded max {limit}  [/{pattern}/ in {}]  — change the claim, not the number",
                        py_str(globs)
                    ));
                }
            }
            Some("count-min") => {
                let pattern = key_str(ev, "pattern")?;
                let globs = key(ev, "glob")?;
                let (n, matched) = count(pattern, globs, root)?;
                if !matched {
                    fails.push(format!(
                        "predicate matched NO files (measures nothing): glob {}",
                        py_str(globs)
                    ));
                } else {
                    let min = key_int(ev, "min")?;
                    if (n as i64) < min {
                        fails.push(format!(
                            "claim evidence absent: {n} < required min {min}  [/{pattern}/ in {}]  — the doc asserts it; the source no longer carries it",
                            py_str(globs)
                        ));
                    }
                }
            }
            Some("set-equal") => {
                let (left, el) = side(key(ev, "left")?, root)?;
                let (right, er) = side(key(ev, "right")?, root)?;
                for e in [&el, &er].into_iter().flatten() {
                    fails.push(format!("{e}  — an empty side compares nothing"));
                }
                if el.is_none() && er.is_none() {
                    let waived: BTreeSet<String> = match ev.get("waive") {
                        None => BTreeSet::new(),
                        Some(Value::Sequence(xs)) => xs.iter().map(py_str).collect(),
                        Some(Value::String(s)) => s.chars().map(String::from).collect(),
                        Some(_) => return internal("TypeError: waive must be a list"),
                    };
                    for w in &waived {
                        println!("    waived (debt, printed every run): {w}");
                    }
                    let only_l: Vec<&String> = left
                        .iter()
                        .filter(|x| !right.contains(*x) && !waived.contains(*x))
                        .collect();
                    let only_r: Vec<&String> = right
                        .iter()
                        .filter(|x| !left.contains(*x) && !waived.contains(*x))
                        .collect();
                    let join =
                        |v: &[&String]| v.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ");
                    if !only_l.is_empty() {
                        fails.push(format!("in left but not right: {}", join(&only_l)));
                    }
                    if !only_r.is_empty() {
                        fails.push(format!("in right but not left: {}", join(&only_r)));
                    }
                }
            }
            Some("count-equals") => {
                let (names, es) = side(key(ev, "set")?, root)?;
                let number = key(ev, "number")?;
                let nfile = key_str(number, "file")?;
                let npat = key_str(number, "pattern")?;
                let p = root.join(nfile);
                let m: Option<String> = if p.exists() {
                    let t = read_text(&p).map_err(|e| Internal(format!("{nfile}: {e}")))?;
                    let re = rx(npat, false)?;
                    match re
                        .captures(&t)
                        .map_err(|e| Internal(format!("regex: {e}")))?
                    {
                        None => None,
                        Some(c) => {
                            if re.captures_len() < 2 {
                                return internal("IndexError: no such group");
                            }
                            Some(c.get(1).map(|m| m.as_str().to_string()).unwrap_or_default())
                        }
                    }
                } else {
                    None
                };
                if let Some(es) = es {
                    fails.push(format!("{es}  — an empty side compares nothing"));
                } else {
                    match m {
                        None => fails.push(format!("stated number not found: /{npat}/ in {nfile}")),
                        Some(g) => {
                            let stated: i64 = g
                                .trim_matches(is_py_space)
                                .replace('_', "")
                                .parse()
                                .map_err(|_| Internal(format!("ValueError: int({g:?})")))?;
                            if stated != names.len() as i64 {
                                fails.push(format!(
                                    "{nfile} states {g}, the source holds {}",
                                    names.len()
                                ));
                            }
                        }
                    }
                }
            }
            _ => fails.push(format!(
                "unknown evidence kind: {}",
                kind.map(py_repr).unwrap_or_else(|| "None".into())
            )),
        }
    }
    Ok(fails)
}

// ── self-test ────────────────────────────────────────────────────────────

/// A fresh directory under $TMPDIR (default /tmp; under wasmtime, preopen one
/// there), removed on drop.
struct TempDir(PathBuf);
impl TempDir {
    fn new() -> std::io::Result<TempDir> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static N: AtomicU64 = AtomicU64::new(0);
        let base = std::env::var_os("TMPDIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| "/tmp".into());
        let t = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let p = base.join(format!(
            "claim-check-{t}-{}",
            N.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&p)?;
        Ok(TempDir(p))
    }
}
impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn yv(s: &str) -> Value {
    rivet_yaml::from_str(s).expect("self-test fixture YAML")
}

fn run_case(files: &[(&str, &str)], ev: &str, text: Option<&str>) -> R<bool> {
    let d = TempDir::new().map_err(|e| Internal(format!("tempdir: {e}")))?;
    let root = &d.0;
    for (rel, body) in files {
        let p = root.join(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).map_err(|e| Internal(e.to_string()))?;
        }
        std::fs::write(&p, body).map_err(|e| Internal(e.to_string()))?;
    }
    if !root.join("doc.md").exists() {
        std::fs::write(root.join("doc.md"), "x").map_err(|e| Internal(e.to_string()))?;
    }
    let mut claim = rivet_yaml::Mapping::new();
    claim.insert(Value::from("id"), Value::from("T"));
    claim.insert(Value::from("doc"), Value::from("doc.md"));
    claim.insert(Value::from("evidence"), Value::Sequence(vec![yv(ev)]));
    if let Some(t) = text {
        claim.insert(Value::from("text"), Value::from(t));
    }
    Ok(!check_claim(&Value::Mapping(claim), root)?.is_empty())
}

fn self_test() -> R<i32> {
    let two: &[(&str, &str)] = &[("s/a/SKILL.md", ""), ("s/b/SKILL.md", "")];
    let with_doc = |body: &'static str| -> Vec<(&'static str, &'static str)> {
        let mut v = vec![("s/a/SKILL.md", ""), ("s/b/SKILL.md", "")];
        v.push(("doc.md", body));
        v
    };
    let _ = two;
    let disk = r#"{glob: 's/*/SKILL.md', name: 's/([^/]+)/'}"#;
    let table = r#"{file: doc.md, pattern: '^- `([a-z]+)`', after: '## S', before: '## E'}"#;
    let src: Vec<(&str, &str)> = vec![
        ("p/A.lean", "theorem a : True := trivial\n"),
        ("p/B.lean", "theorem b : True := by sorry\n"),
    ];
    let se = |extra: &str| format!("{{kind: set-equal, left: {disk}, right: {table}{extra}}}");
    let ce = |pat: &str| {
        format!("{{kind: count-equals, number: {{file: doc.md, pattern: '{pat}'}}, set: {disk}}}")
    };
    let cn = r"# (\d+) custom";
    type Case<'a> = (&'a str, Vec<(&'a str, &'a str)>, String, bool);
    let cases: Vec<Case> = vec![
        (
            "verbatim: present -> holds",
            vec![("doc.md", "the trusted base is X\n")],
            "{kind: verbatim, text: 'the trusted base is X'}".into(),
            false,
        ),
        (
            "verbatim: re-wrapped -> still holds",
            vec![("doc.md", "the trusted\n  base is X\n")],
            "{kind: verbatim, text: 'the trusted base is X'}".into(),
            false,
        ),
        (
            "verbatim: re-worded -> fails",
            vec![("doc.md", "the trusted base is Y\n")],
            "{kind: verbatim, text: 'the trusted base is X'}".into(),
            true,
        ),
        (
            "verbatim: empty text -> fails",
            vec![("doc.md", "anything")],
            "{kind: verbatim, text: ''}".into(),
            true,
        ),
        (
            "claim text: absent -> fails",
            vec![("doc.md", "nothing")],
            "{kind: file-exists, path: doc.md}".into(),
            true,
        ),
        (
            "file-exists: present -> holds",
            vec![("p/A.lean", "")],
            "{kind: file-exists, path: p/A.lean}".into(),
            false,
        ),
        (
            "file-exists: missing -> fails",
            vec![],
            "{kind: file-exists, path: p/A.lean}".into(),
            true,
        ),
        (
            "count-min: present -> holds",
            src.clone(),
            r"{kind: count-min, pattern: '^theorem a\b', glob: 'p/*.lean', min: 1}".into(),
            false,
        ),
        (
            "count-min: pattern vanished -> fails",
            src.clone(),
            r"{kind: count-min, pattern: '^theorem zzz\b', glob: 'p/*.lean', min: 1}".into(),
            true,
        ),
        (
            "count-min: glob matches no file -> fails",
            src.clone(),
            r"{kind: count-min, pattern: '^theorem a\b', glob: 'q/*.lean', min: 1}".into(),
            true,
        ),
        (
            "count-max: under -> holds",
            src.clone(),
            r"{kind: count-max, pattern: ':= by sorry\b', glob: p/A.lean, max: 0}".into(),
            false,
        ),
        (
            "count-max: over -> fails",
            src.clone(),
            r"{kind: count-max, pattern: ':= by sorry\b', glob: 'p/*.lean', max: 0}".into(),
            true,
        ),
        (
            "count-max: glob matches no file -> fails",
            src.clone(),
            "{kind: count-max, pattern: sorry, glob: 'q/*.lean', max: 0}".into(),
            true,
        ),
        (
            "no-new: over recorded -> fails",
            src.clone(),
            "{kind: no-new, pattern: sorry, glob: 'p/*.lean', recorded: 0}".into(),
            true,
        ),
        (
            "set-equal: sets match -> holds",
            with_doc("## S\n- `a`\n- `b`\n## E\n"),
            se(""),
            false,
        ),
        (
            "set-equal: doc lacks one -> fails",
            with_doc("## S\n- `a`\n## E\n"),
            se(""),
            true,
        ),
        (
            "set-equal: doc lists a phantom -> fails",
            with_doc("## S\n- `a`\n- `b`\n- `c`\n## E\n"),
            se(""),
            true,
        ),
        (
            "set-equal: empty doc side -> FAILS, not 0 mismatches",
            with_doc("## S\n## E\n"),
            se(""),
            true,
        ),
        (
            "set-equal: empty disk side -> FAILS",
            vec![("doc.md", "## S\n- `a`\n## E\n")],
            se(""),
            true,
        ),
        (
            "set-equal: empty doc side, differences waived -> still FAILS",
            with_doc("## S\n## E\n"),
            se(", waive: [a, b]"),
            true,
        ),
        (
            "set-equal: empty disk side, differences waived -> still FAILS",
            vec![("doc.md", "## S\n- `a`\n## E\n")],
            se(", waive: [a]"),
            true,
        ),
        (
            "set-equal: waived name excluded",
            with_doc("## S\n- `a`\n## E\n"),
            se(", waive: [b]"),
            false,
        ),
        (
            "set-equal: section bounds respected",
            with_doc("- `z`\n## S\n- `a`\n- `b`\n## E\n- `y`\n"),
            se(""),
            false,
        ),
        (
            "count-equals: stated == actual -> holds",
            with_doc("# 2 custom skills"),
            ce(cn),
            false,
        ),
        (
            "count-equals: stated != actual -> fails",
            with_doc("# 18 custom skills"),
            ce(cn),
            true,
        ),
        (
            "count-equals: number missing -> fails",
            with_doc("no number here"),
            ce(cn),
            true,
        ),
        (
            "count-equals: empty set -> fails",
            vec![("doc.md", "# 0 custom skills")],
            ce(cn),
            true,
        ),
        (
            "unknown kind -> fails",
            vec![],
            "{kind: guess}".into(),
            true,
        ),
    ];
    let mut bad = 0;
    let mut total = cases.len();
    println!("claim_check self-test");
    for (name, files, ev, expect_fail) in &cases {
        let text = name.starts_with("claim text").then_some("nothing-here");
        let got = run_case(files, ev, text)?;
        let ok = got == *expect_fail;
        bad += usize::from(!ok);
        println!("  [{}] {name}", if ok { "ok  " } else { "FAIL" });
    }
    let d = TempDir::new().map_err(|e| Internal(format!("tempdir: {e}")))?;
    std::fs::write(d.0.join("doc.md"), "the claim text\n").map_err(|e| Internal(e.to_string()))?;
    for (name, claim) in [
        (
            "no evidence, id and doc only -> fails",
            "{id: T, doc: doc.md}",
        ),
        (
            "no evidence, empty list -> fails",
            "{id: T, doc: doc.md, evidence: []}",
        ),
        (
            "no evidence, text present -> fails",
            "{id: T, doc: doc.md, text: the claim text}",
        ),
    ] {
        let ok = !check_claim(&yv(claim), &d.0)?.is_empty();
        bad += usize::from(!ok);
        total += 1;
        println!("  [{}] {name}", if ok { "ok  " } else { "FAIL" });
    }
    println!("  {}/{total} cases hold", total - bad);
    Ok(if bad > 0 { 1 } else { 0 })
}

// ── main ─────────────────────────────────────────────────────────────────

fn run() -> R<i32> {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|a| a == "--self-test") {
        return self_test();
    }
    let args: Vec<&String> = argv.iter().filter(|a| !a.starts_with("--")).collect();
    let path = PathBuf::from(args.first().map(|s| s.as_str()).unwrap_or("claims.yaml"));
    if !path.exists() {
        eprintln!("claim_check: {} not found", path.display());
        return Ok(1);
    }
    let root = path.parent().map(Path::to_path_buf).unwrap_or_default();
    let src =
        std::fs::read_to_string(&path).map_err(|e| Internal(format!("{}: {e}", path.display())))?;
    let src = src.replace("\r\n", "\n").replace('\r', "\n");
    let data: Value = if src.trim().is_empty() {
        Value::Null
    } else {
        rivet_yaml::from_str(&src).map_err(|e| Internal(format!("yaml: {e}")))?
    };
    let claims: &[Value] = match &data {
        Value::Null => &[],
        Value::Mapping(_) => match data.get("claims") {
            None | Some(Value::Null) => &[],
            Some(Value::Sequence(xs)) => xs,
            Some(v) if !truthy(Some(v)) => &[],
            Some(_) => return internal("TypeError: claims must be a list"),
        },
        _ if !truthy(Some(&data)) => &[],
        _ => return internal("AttributeError: top level must be a mapping"),
    };
    if claims.is_empty() {
        eprintln!("claim_check: no claims declared — nothing to gate");
        return Ok(2);
    }
    let mut ids: Vec<Option<String>> = Vec::new();
    for c in claims {
        if !c.is_mapping() {
            return internal("AttributeError: claim must be a mapping");
        }
        ids.push(match c.get("id") {
            None | Some(Value::Null) => None,
            Some(v) => Some(py_str(v)),
        });
    }
    let mut dup: BTreeSet<&String> = BTreeSet::new();
    for (i, a) in ids.iter().enumerate() {
        if let Some(a) = a
            && ids[i + 1..].iter().any(|b| b.as_ref() == Some(a))
        {
            dup.insert(a);
        }
    }
    if !dup.is_empty() || ids.iter().any(Option::is_none) {
        eprintln!("claim_check: duplicate or missing claim ids: {dup:?}");
        return Ok(1);
    }

    let mut bad = 0;
    for c in claims {
        let fails = check_claim(c, &root)?;
        let id = py_str(key(c, "id")?);
        if fails.is_empty() {
            println!("✓ {id}");
        } else {
            bad += 1;
            println!("✗ {id}  ({})", py_str(key(c, "doc")?));
            for f in &fails {
                println!("    {f}");
            }
        }
        if truthy(c.get("epoch")) {
            println!("    epoch: {}", norm(&py_str(key(c, "epoch")?)));
        }
    }
    println!("\n{}/{} claims hold.", claims.len() - bad, claims.len());
    Ok(if bad > 0 { 1 } else { 0 })
}

fn main() {
    let code = match run() {
        Ok(c) => c,
        Err(Internal(m)) => {
            eprintln!("claim-check: {m}");
            1
        }
    };
    exit(code);
}
