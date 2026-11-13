/- The SMT-LIB model the certified query echo is proven against (issue #281,
   phase E1).

   This file is HAND-WRITTEN and it is a SPECIFICATION: nothing in it is
   proven equal to the SMT-LIB 2.6 standard. It is a small, explicit
   transcription of the part of the standard the echo printer
   (`kernel::echo_kernel`, `crates/ordeal-lrat/src/echo_kernel.rs`) can
   emit — the lexicon of §3.1 restricted to the printer's image, the
   scripts of §3.9 / §4.2 restricted to `set-logic`, `declare-const`,
   `declare-fun`, `assert` and a final `check-sat`, and the theories Core,
   FixedSizeBitVectors and ArraysEx with the QF_BV extensions — reviewed
   against the standard and validated by the Z3 parser differential (the
   echo leg, docs/design/query-echo.md §6). `lean/Echo.lean` proves the
   printer against it: the text the printer returns, READ BY THIS FILE,
   is satisfied exactly when the certified node list's roots are.

   What a reviewer has to read, top to bottom:

   * `SExp`, `render`, `renderScript` — the text of a script: `(` … `)`,
     one space between the items of a list, one newline after each
     command, `|…|` around a quoted symbol, `#b` and binary digits (most
     significant first), decimal numerals.
   * `lex` — the reader: a tokenizer (`lexAux`) and a stack parser
     (`parseGo`). `lex_render` (Echo.lean) is the round trip on the
     printer's image.
   * `Interp`, `Val`, `den` — an interpretation of the declared symbols
     and the value of a term under it, one arm per symbol; the operator
     arms are the `BitVec` operations `dagNodeVal` (BlasterDag.lean) uses,
     i.e. the operations Lean's own `bv_decide` maps the SMT-LIB symbols
     to.
   * `ScriptSat` — a script is satisfied by an interpretation: the
     commands are read in order, a declaration must be fresh, well
     sorted, allowed by the logic and not a reserved word; an assertion
     must be well sorted under the declarations so far and true.
   * `TextSat` — the same for a text: it lexes to a satisfied script. -/
import BlasterDag

open Aeneas Aeneas.Std
open kernel.blast_kernel.spec

namespace kernel.spec.smt

/- ══════════════════ TEXT ══════════════════ -/

/-- The bytes of an ASCII text. -/
def bytes (s : String) : List U8 := s.toList.map fun c => ⟨BitVec.ofNat 8 c.toNat⟩

/-- An S-expression of the printer's language. -/
inductive SExp where
  /-- A simple symbol or keyword, printed bare: `bvadd`, `_`, `=`. -/
  | sym (b : List U8)
  /-- A quoted symbol, printed `|b|`. SMT-LIB 2.6 §3.1 makes `|b|` and the
      simple symbol `b` the same symbol; the model keeps them apart in the
      SYNTAX (the printer quotes names and never operators) and makes
      them one in the SEMANTICS by refusing a declared name that is a
      reserved word or a theory symbol (`nameOk`). -/
  | qsym (b : List U8)
  /-- A decimal numeral. -/
  | num (n : Nat)
  /-- A binary constant `#b…`, its digits most significant first. -/
  | bin (bs : List Bool)
  /-- A parenthesized list. -/
  | list (xs : List SExp)

def cSp : U8 := 32#u8
def cNl : U8 := 10#u8
def cLp : U8 := 40#u8
def cRp : U8 := 41#u8
def cBar : U8 := 124#u8
def cBsl : U8 := 92#u8
def cHash : U8 := 35#u8
def cB : U8 := 98#u8
def c0 : U8 := 48#u8
def c1 : U8 := 49#u8

/-- The decimal digit `d` (`d < 10`). -/
def digit (d : Nat) : U8 := ⟨BitVec.ofNat 8 (48 + d)⟩

/-- The decimal numeral of `n`: no leading zeros, `0` is `0`. -/
def decDigits (n : Nat) : List U8 :=
  if n < 10 then [digit n] else decDigits (n / 10) ++ [digit (n % 10)]
decreasing_by omega

mutual
/-- The text of an S-expression. -/
def render : SExp → List U8
  | .sym b => b
  | .qsym b => cBar :: b ++ [cBar]
  | .num n => decDigits n
  | .bin bs => cHash :: cB :: bs.map fun b => if b then c1 else c0
  | .list xs => cLp :: (renderSp xs).drop 1 ++ [cRp]
/-- The items of a list, each after one space (`render` drops the first). -/
def renderSp : List SExp → List U8
  | [] => []
  | x :: xs => cSp :: render x ++ renderSp xs
end

/-- The text of a script: each command, then a newline. -/
def renderScript : List SExp → List U8
  | [] => []
  | c :: cs => render c ++ cNl :: renderScript cs

/- ══════════════════ THE READER ══════════════════ -/

/-- A token. -/
inductive Tok where
  | lp
  | rp
  | atom (e : SExp)

def isDigit (c : U8) : Bool := 48 ≤ c.val && c.val ≤ 57

/-- The value of a run of decimal digits. -/
def readDec (w : List U8) : Nat := w.foldl (fun n c => 10 * n + (c.val - 48)) 0

/-- A word (a maximal run of non-delimiter characters) as an atom: `#b`
    and binary digits is a binary constant, a run of digits a numeral,
    anything else that does not start with a digit or `#` a symbol. -/
def classify (w : List U8) : Option SExp :=
  match w with
  | [] => none
  | c :: r =>
    if c = cHash then
      match r with
      | [] => none
      | b :: ds =>
        if b = cB ∧ ds ≠ [] ∧ ds.all (fun d => d = c0 || d = c1) then some (.bin (ds.map fun d => d = c1))
        else none
    else if isDigit c then
      if r.all isDigit then some (.num (readDec w)) else none
    else some (.sym w)

/-- The tokenizer's state: between tokens, inside a word, inside `|…|`. -/
inductive LexSt where
  | idle
  | word (acc : List U8)
  | quoted (acc : List U8)

/-- The tokenizer: whitespace (space, newline) separates; `(` and `)` are
    tokens and end a word; `|` opens a quoted symbol that runs to the next
    `|` (a `\` inside is refused, as is a `|` inside a word). -/
def lexAux : LexSt → List U8 → Option (List Tok)
  | .idle, [] => some []
  | .word acc, [] => (classify acc).map fun e => [.atom e]
  | .quoted _, [] => none
  | .idle, c :: cs =>
    if c = cSp ∨ c = cNl then lexAux .idle cs
    else if c = cLp then (lexAux .idle cs).map (Tok.lp :: ·)
    else if c = cRp then (lexAux .idle cs).map (Tok.rp :: ·)
    else if c = cBar then lexAux (.quoted []) cs
    else lexAux (.word [c]) cs
  | .word acc, c :: cs =>
    if c = cSp ∨ c = cNl then
      (classify acc).bind fun e => (lexAux .idle cs).map (Tok.atom e :: ·)
    else if c = cLp then
      (classify acc).bind fun e => (lexAux .idle cs).map (fun ts => Tok.atom e :: Tok.lp :: ts)
    else if c = cRp then
      (classify acc).bind fun e => (lexAux .idle cs).map (fun ts => Tok.atom e :: Tok.rp :: ts)
    else if c = cBar then none
    else lexAux (.word (acc ++ [c])) cs
  | .quoted acc, c :: cs =>
    if c = cBar then (lexAux .idle cs).map (Tok.atom (.qsym acc) :: ·)
    else if c = cBsl then none
    else lexAux (.quoted (acc ++ [c])) cs

/-- The parser: a stack of the lists being read (each reversed), the
    current one on top. -/
def parseGo : List (List SExp) → List SExp → List Tok → Option (List SExp)
  | [], cur, [] => some cur.reverse
  | _ :: _, _, [] => none
  | st, cur, .atom e :: ts => parseGo st (e :: cur) ts
  | st, cur, .lp :: ts => parseGo (cur :: st) [] ts
  | [], _, .rp :: _ => none
  | top :: st, cur, .rp :: ts => parseGo st (.list cur.reverse :: top) ts

/-- **The reader**: the S-expressions of a text. -/
def lex (text : List U8) : Option (List SExp) :=
  (lexAux .idle text).bind (parseGo [] [])

/-- A character of a word: not whitespace, a parenthesis or `|`. -/
def wordCh (c : U8) : Bool := c != cSp && c != cNl && c != cLp && c != cRp && c != cBar

/-- A simple symbol the reader reads back as itself: non-empty, of word
    characters, not starting with a digit or `#`. -/
def symOk (b : List U8) : Bool :=
  match b with
  | [] => false
  | c :: _ => !isDigit c && c != cHash && b.all wordCh

/-- The bytes of a quoted symbol the reader reads back: no `|`, no `\`. -/
def qOk (b : List U8) : Bool := b.all fun d => d != cBar && d != cBsl

mutual
/-- The S-expressions `render` and `lex` round-trip on (`lex_render`). -/
def Printable : SExp → Prop
  | .sym b => symOk b = true
  | .qsym b => qOk b = true
  | .num _ => True
  | .bin bs => bs ≠ []
  | .list xs => PrintableL xs
def PrintableL : List SExp → Prop
  | [] => True
  | x :: xs => Printable x ∧ PrintableL xs
end

/- ══════════════════ MEANING ══════════════════ -/

/-- An interpretation of a script's declared symbols: a value for every
    bitvector constant at its width, a total map for every array, a total
    map from argument values for every function (coerced to the declared
    result width where it is applied). -/
structure Interp where
  cst : List U8 → (w : Nat) → BitVec w
  arr : List U8 → BitVec 32 → BitVec 8
  fn : List U8 → List DVal → DVal

/-- What a declaration gives a name: a bitvector sort, the array sort
    `(Array (_ BitVec 32) (_ BitVec 8))`, or a function rank. -/
inductive Decl where
  | bv (w : Nat)
  | arr
  | fn (args : List Nat) (w : Nat)

/-- A signature: the declarations so far, oldest first. -/
abbrev Sig := List (List U8 × Decl)

/-- The declaration of `n`, if any. -/
def Sig.get (sg : Sig) (n : List U8) : Option Decl :=
  match sg with
  | [] => none
  | (m, d) :: rest => if m = n then some d else Sig.get rest n

/-- The value of a term: a bitvector (with its width), a truth value or
    an array. -/
inductive Val where
  | bv (v : DVal)
  | bool (b : Bool)
  | arr (f : BitVec 32 → BitVec 8)

/-- The binary bitvector operations of one width (FixedSizeBitVectors and
    the QF_BV extensions). A shift is by the second operand's value. -/
def bvBinOp (op : List U8) : Option ((w : Nat) → BitVec w → BitVec w → BitVec w) :=
  if op = bytes "bvadd" then some fun _ x y => x + y
  else if op = bytes "bvsub" then some fun _ x y => x - y
  else if op = bytes "bvmul" then some fun _ x y => x * y
  else if op = bytes "bvudiv" then some fun _ x y => x.smtUDiv y
  else if op = bytes "bvurem" then some fun _ x y => x % y
  else if op = bytes "bvand" then some fun _ x y => x &&& y
  else if op = bytes "bvor" then some fun _ x y => x ||| y
  else if op = bytes "bvxor" then some fun _ x y => x ^^^ y
  else if op = bytes "bvshl" then some fun _ x y => x <<< y.toNat
  else if op = bytes "bvlshr" then some fun _ x y => x >>> y.toNat
  else if op = bytes "bvashr" then some fun _ x y => x.sshiftRight y.toNat
  else if op = bytes "bvsdiv" then some fun _ x y => x.smtSDiv y
  else if op = bytes "bvsrem" then some fun _ x y => x.srem y
  else none

/-- The binary predicates over bitvectors of one width. `=` and `distinct`
    are the bitvector instances only: the printer never compares formulas
    or arrays, and never prints them with more than two operands. -/
def bvCmpOp (op : List U8) : Option ((w : Nat) → BitVec w → BitVec w → Bool) :=
  if op = bytes "=" then some fun _ x y => decide (x = y)
  else if op = bytes "distinct" then some fun _ x y => decide (x ≠ y)
  else if op = bytes "bvult" then some fun _ x y => decide (x < y)
  else if op = bytes "bvule" then some fun _ x y => decide (x ≤ y)
  else if op = bytes "bvugt" then some fun _ x y => decide (y < x)
  else if op = bytes "bvuge" then some fun _ x y => decide (y ≤ x)
  else if op = bytes "bvslt" then some fun _ x y => x.slt y
  else if op = bytes "bvsle" then some fun _ x y => x.sle y
  else if op = bytes "bvsgt" then some fun _ x y => y.slt x
  else if op = bytes "bvsge" then some fun _ x y => y.sle x
  else none

/-- The unary bitvector operations. -/
def bvUnOp (op : List U8) : Option ((w : Nat) → BitVec w → BitVec w) :=
  if op = bytes "bvnot" then some fun _ x => ~~~x
  else if op = bytes "bvneg" then some fun _ x => -x
  else none

/-- The binary connectives. -/
def boolBinOp (op : List U8) : Option (Bool → Bool → Bool) :=
  if op = bytes "and" then some fun p q => p && q
  else if op = bytes "or" then some fun p q => p || q
  else none

/-- An application of a theory symbol to argument values: defined when
    the arguments have the sorts the symbol takes. -/
def denSym (op : List U8) : List Val → Option Val
  | [.bv x] => (bvUnOp op).map fun f => .bv ⟨x.1, f x.1 x.2⟩
  | [.bool p] => if op = bytes "not" then some (.bool !p) else none
  | [.bv x, .bv y] =>
    match bvBinOp op with
    | some f => if x.1 = y.1 then some (.bv ⟨x.1, f x.1 x.2 (toW x.1 y)⟩) else none
    | none =>
      match bvCmpOp op with
      | some p => if x.1 = y.1 then some (.bool (p x.1 x.2 (toW x.1 y))) else none
      | none => if op = bytes "concat" then some (.bv ⟨x.1 + y.1, x.2 ++ y.2⟩) else none
  | [.bool p, .bool q] => (boolBinOp op).map fun f => .bool (f p q)
  | [.bool c, .bv t, .bv e] =>
    if op = bytes "ite" ∧ t.1 = e.1 then some (.bv ⟨t.1, if c then t.2 else toW t.1 e⟩) else none
  | [.arr a, .bv i] =>
    if op = bytes "select" ∧ i.1 = 32 then some (.bv ⟨8, a (toW 32 i)⟩) else none
  | [.arr a, .bv i, .bv v] =>
    if op = bytes "store" ∧ i.1 = 32 ∧ v.1 = 8 then
      some (.arr fun j => if toW 32 i = j then toW 8 v else a j)
    else none
  | _ => none

/-- An application of an indexed symbol `(_ ix k)` to a bitvector: the
    two extensions and the two rotates (by `k` modulo the width). -/
def denIdx1 (ix : List U8) (k : Nat) (x : DVal) : Option Val :=
  if ix = bytes "zero_extend" then some (.bv ⟨x.1 + k, x.2.setWidth (x.1 + k)⟩)
  else if ix = bytes "sign_extend" then some (.bv ⟨x.1 + k, x.2.signExtend (x.1 + k)⟩)
  else if ix = bytes "rotate_left" then some (.bv ⟨x.1, x.2.rotateLeft (k % x.1)⟩)
  else if ix = bytes "rotate_right" then some (.bv ⟨x.1, x.2.rotateRight (k % x.1)⟩)
  else none

/-- Bitvector argument values (a function takes bitvectors only). -/
def bvArgs : List Val → Option (List DVal)
  | [] => some []
  | .bv v :: rest => (bvArgs rest).map (v :: ·)
  | _ :: _ => none

/-- A name in term position: a declared constant, array or nullary
    function. -/
def denName (I : Interp) (sg : Sig) (n : List U8) : Option Val :=
  match sg.get n with
  | some (.bv w) => some (.bv ⟨w, I.cst n w⟩)
  | some .arr => some (.arr (I.arr n))
  | some (.fn [] w) => some (.bv ⟨w, toW w (I.fn n [])⟩)
  | _ => none

/-- An application `(head a₁ … aₙ)` to the argument values: a theory
    symbol, an indexed symbol, or a declared function of that rank. -/
def denApp (I : Interp) (sg : Sig) : SExp → List Val → Option Val
  | .sym op, args => denSym op args
  | .list [.sym u, .sym ix, .num k], [.bv x] => if u = bytes "_" then denIdx1 ix k x else none
  | .list [.sym u, .sym ix, .num hi, .num lo], [.bv x] =>
    if u = bytes "_" ∧ ix = bytes "extract" ∧ lo ≤ hi ∧ hi < x.1 then
      some (.bv ⟨hi - lo + 1, x.2.extractLsb hi lo⟩)
    else none
  | .qsym f, a :: rest =>
    match sg.get f, bvArgs (a :: rest) with
    | some (.fn ws w), some vs =>
      if vs.map Sigma.fst = ws then some (.bv ⟨w, toW w (I.fn f vs)⟩) else none
    | _, _ => none
  | _, _ => none

mutual
/-- **The value of a term** under an interpretation and a signature:
    `none` when the term is not well sorted. -/
def den (I : Interp) (sg : Sig) : SExp → Option Val
  | .sym _ => none
  | .num _ => none
  | .bin bs =>
    if bs = [] then none
    else some (.bv ⟨bs.length, bvOfFn (fun j => bs.getD (bs.length - 1 - j) false) bs.length⟩)
  | .qsym n => denName I sg n
  | .list [] => none
  | .list (h :: args) => (denArgs I sg args).bind (denApp I sg h)
/-- The values of the arguments, all well sorted. -/
def denArgs (I : Interp) (sg : Sig) : List SExp → Option (List Val)
  | [] => some []
  | a :: rest =>
    match den I sg a, denArgs I sg rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
end

/- ══════════════════ SCRIPTS ══════════════════ -/

/-- The words a declared name may not be: SMT-LIB 2.6's reserved words
    (§3.1: the general ones, then the command names), then the symbols of
    the theories and logics a script is read in — Core, the logic names,
    ArraysEx, FixedSizeBitVectors and QF_BV's extensions. `|w|` is the
    symbol `w`, so quoting does not make these free. -/
def reservedWords : List (List U8) := [
  bytes "!", bytes "_", bytes "as", bytes "BINARY", bytes "DECIMAL", bytes "exists",
  bytes "HEXADECIMAL", bytes "forall", bytes "let", bytes "match", bytes "NUMERAL", bytes "par",
  bytes "STRING",
  bytes "assert", bytes "check-sat", bytes "check-sat-assuming", bytes "declare-const",
  bytes "declare-datatype", bytes "declare-datatypes", bytes "declare-fun", bytes "declare-sort",
  bytes "define-fun", bytes "define-fun-rec", bytes "define-funs-rec", bytes "define-sort",
  bytes "echo", bytes "exit", bytes "get-assertions", bytes "get-assignment", bytes "get-info",
  bytes "get-model", bytes "get-option", bytes "get-proof", bytes "get-unsat-assumptions",
  bytes "get-unsat-core", bytes "get-value", bytes "pop", bytes "push", bytes "reset",
  bytes "reset-assertions", bytes "set-info", bytes "set-logic", bytes "set-option",
  bytes "Bool", bytes "true", bytes "false", bytes "not", bytes "=>", bytes "and", bytes "or",
  bytes "xor", bytes "=", bytes "distinct", bytes "ite",
  bytes "QF_BV", bytes "QF_ABV", bytes "QF_AUFBV",
  bytes "Array", bytes "select", bytes "store",
  bytes "BitVec", bytes "concat", bytes "extract", bytes "repeat", bytes "zero_extend",
  bytes "sign_extend", bytes "rotate_left", bytes "rotate_right",
  bytes "bvnot", bytes "bvneg", bytes "bvand", bytes "bvor", bytes "bvxor", bytes "bvnand",
  bytes "bvnor", bytes "bvxnor", bytes "bvcomp", bytes "bvadd", bytes "bvsub", bytes "bvmul",
  bytes "bvudiv", bytes "bvurem", bytes "bvsdiv", bytes "bvsrem", bytes "bvsmod", bytes "bvshl",
  bytes "bvlshr", bytes "bvashr", bytes "bvult", bytes "bvule", bytes "bvugt", bytes "bvuge",
  bytes "bvslt", bytes "bvsle", bytes "bvsgt", bytes "bvsge"]

/-- A byte of a quoted symbol: printable ASCII other than `|` and `\`. -/
def quotable (c : U8) : Prop := 32 ≤ c.val ∧ c.val ≤ 126 ∧ c ≠ cBar ∧ c ≠ cBsl

/-- A name a script may declare: non-empty, of quotable bytes, not a
    reserved word or a theory symbol. -/
def nameOk (n : List U8) : Prop := n ≠ [] ∧ (∀ c ∈ n, quotable c) ∧ n ∉ reservedWords

/-- The sort `(_ BitVec w)`, `w ≥ 1`. -/
def bvSort : SExp → Option Nat
  | .list [.sym u, .sym b, .num w] =>
    if u = bytes "_" ∧ b = bytes "BitVec" ∧ 0 < w then some w else none
  | _ => none

/-- The sorts of a function's arguments. -/
def bvSorts : List SExp → Option (List Nat)
  | [] => some []
  | s :: rest =>
    match bvSort s, bvSorts rest with
    | some w, some ws => some (w :: ws)
    | _, _ => none

/-- The sort of a declared constant: a bitvector sort or
    `(Array (_ BitVec 32) (_ BitVec 8))`. -/
def constSort (s : SExp) : Option Decl :=
  match bvSort s with
  | some w => some (.bv w)
  | none =>
    match s with
    | .list [.sym a, i, e] =>
      if a = bytes "Array" ∧ bvSort i = some 32 ∧ bvSort e = some 8 then some .arr else none
    | _ => none

/-- A declaration command: `(declare-const |n| sort)` or
    `(declare-fun |n| (sort …) sort)`. -/
def declOf : SExp → Option (List U8 × Decl)
  | .list [.sym c, .qsym n, s] =>
    if c = bytes "declare-const" then (constSort s).map fun d => (n, d) else none
  | .list [.sym c, .qsym n, .list args, r] =>
    if c = bytes "declare-fun" then
      match bvSorts args, bvSort r with
      | some ws, some w => some (n, .fn ws w)
      | _, _ => none
    else none
  | _ => none

/-- What a logic lets a script declare: bitvector constants (and nullary
    functions, which are constants) everywhere, arrays in `QF_ABV` and
    `QF_AUFBV`, functions in `QF_AUFBV`. -/
def logicAllows (logic : List U8) : Decl → Prop
  | .bv _ => True
  | .arr => logic = bytes "QF_ABV" ∨ logic = bytes "QF_AUFBV"
  | .fn args _ => args = [] ∨ logic = bytes "QF_AUFBV"

/-- The body of a script, read in order under the signature so far: a
    declaration of a fresh, allowed name extends the signature; an
    assertion is well sorted and true; the last command is `(check-sat)`. -/
def BodySat (I : Interp) (logic : List U8) : Sig → List SExp → Prop
  | _, [] => False
  | sg, c :: rest =>
    (rest = [] ∧ c = .list [.sym (bytes "check-sat")]) ∨
    (rest ≠ [] ∧
      match declOf c with
      | some (n, d) =>
        nameOk n ∧ sg.get n = none ∧ logicAllows logic d ∧ BodySat I logic (sg ++ [(n, d)]) rest
      | none =>
        match c with
        | .list [.sym a, t] =>
          a = bytes "assert" ∧ den I sg t = some (.bool true) ∧ BodySat I logic sg rest
        | _ => False)

/-- **A script is satisfied by an interpretation**: it opens with
    `(set-logic L)` for one of the three logics, and its body is
    satisfied from the empty signature. -/
def ScriptSat (I : Interp) : List SExp → Prop
  | .list [.sym c, .sym logic] :: rest =>
    c = bytes "set-logic" ∧
      (logic = bytes "QF_BV" ∨ logic = bytes "QF_ABV" ∨ logic = bytes "QF_AUFBV") ∧
      BodySat I logic [] rest
  | _ => False

/-- **A text is satisfied by an interpretation**: it reads as a satisfied
    script. -/
def TextSat (I : Interp) (text : List U8) : Prop :=
  ∃ cs, lex text = some cs ∧ ScriptSat I cs

end kernel.spec.smt
