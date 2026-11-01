/-! A small JSON reader with exact rational numbers (core only, so the filter library does not link `Lean`). -/

namespace VcFilter

inductive Json where
  | null
  | bool (b : Bool)
  | num (q : Rat)
  | str (s : String)
  | arr (a : Array Json)
  | obj (kvs : List (String × Json))
  deriving Inhabited

namespace Json

abbrev Input := List Char

def skipWs : Input → Input
  | c :: cs => if c == ' ' || c == '\n' || c == '\t' || c == '\r' then skipWs cs else c :: cs
  | [] => []

def digits : Input → List Char × Input
  | c :: cs => if c.isDigit then let (d, r) := digits cs; (c :: d, r) else ([], c :: cs)
  | [] => ([], [])

def natOfDigits (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- `-?digits(.digits)?([eE][+-]?digits)?`, exactly. -/
def number (s : Input) : Except String (Rat × Input) := do
  let (neg, s) := match s with | '-' :: r => (true, r) | r => (false, r)
  let (ip, s) := digits s
  if ip.isEmpty then throw "bad number"
  let (fp, s) := match s with
    | '.' :: r => digits r
    | r => ([], r)
  let (eneg, ep, s) := match s with
    | 'e' :: '-' :: r | 'E' :: '-' :: r => let (d, r) := digits r; (true, d, r)
    | 'e' :: '+' :: r | 'E' :: '+' :: r | 'e' :: r | 'E' :: r => let (d, r) := digits r; (false, d, r)
    | r => (false, [], r)
  let m : Rat := mkRat (natOfDigits (ip ++ fp)) (10 ^ fp.length)
  let e := natOfDigits ep
  let q := if eneg then m / ((10 ^ e : Nat) : Rat) else m * ((10 ^ e : Nat) : Rat)
  return (if neg then -q else q, s)

def string : Input → List Char → Except String (String × Input)
  | '"' :: r, acc => pure (String.ofList acc.reverse, r)
  | '\\' :: c :: r, acc =>
    let d := match c with | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | c => c
    string r (d :: acc)
  | c :: r, acc => string r (c :: acc)
  | [], _ => throw "unterminated string"

mutual
def value : Nat → Input → Except String (Json × Input)
  | 0, _ => throw "nested too deeply"
  | fuel + 1, s =>
    match skipWs s with
    | 'n' :: 'u' :: 'l' :: 'l' :: r => pure (.null, r)
    | 't' :: 'r' :: 'u' :: 'e' :: r => pure (.bool true, r)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => pure (.bool false, r)
    | '"' :: r => do let (t, r) ← string r []; pure (.str t, r)
    | '[' :: r =>
      match skipWs r with
      | ']' :: r => pure (.arr #[], r)
      | _ => do let (xs, r) ← items fuel r #[]; pure (.arr xs, r)
    | '{' :: r =>
      match skipWs r with
      | '}' :: r => pure (.obj [], r)
      | _ => do let (kvs, r) ← members fuel r []; pure (.obj kvs.reverse, r)
    | r => do let (q, r) ← number r; pure (.num q, r)

def items : Nat → Input → Array Json → Except String (Array Json × Input)
  | 0, _, _ => throw "nested too deeply"
  | fuel + 1, s, acc => do
    let (v, r) ← value fuel s
    match skipWs r with
    | ',' :: r => items fuel r (acc.push v)
    | ']' :: r => pure (acc.push v, r)
    | _ => throw "expected , or ]"

def members : Nat → Input → List (String × Json) → Except String (List (String × Json) × Input)
  | 0, _, _ => throw "nested too deeply"
  | fuel + 1, s, acc => do
    let r ← match skipWs s with | '"' :: r => pure r | _ => throw "expected a key"
    let (k, r) ← string r []
    let r ← match skipWs r with | ':' :: r => pure r | _ => throw "expected :"
    let (v, r) ← value fuel r
    match skipWs r with
    | ',' :: r => members fuel r ((k, v) :: acc)
    | '}' :: r => pure ((k, v) :: acc, r)
    | _ => throw "expected , or }"
end

def parse (s : String) : Except String Json := do
  let cs := s.toList
  let (v, r) ← value (cs.length + 1) cs
  if (skipWs r).isEmpty then pure v else throw "trailing characters"

def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

#guard match parse "{\"a\": -1.25e1, \"b\": [1, \"x\\\"y\", null, {}], \"c\": true}" with
  | .ok j => match j.get? "a", j.get? "b" with
    | some (.num q), some (.arr xs) => q == -25/2 && xs.size == 4
    | _, _ => false
  | .error _ => false
#guard match parse "0.1" with | .ok (.num q) => q == 1/10 | _ => false
#guard match parse "[1, 2" with | .ok _ => false | .error _ => true
#guard match parse "{\"a\": 1} x" with | .ok _ => false | .error _ => true

end Json
end VcFilter
