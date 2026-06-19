import TltsCheck.Basic

/-! # Build typed timed automata / formulas from CLI-shaped (untyped) data, and check
The CLI builds a model as untyped rows (`RawAuto`) and a property as prefix tokens (`RawMt`);
`buildAndCheck` validates the clock/location indices, constructs the dependently-typed
`FinAutomaton (Fin n)` / `Mt (Fin k)`, and runs the verified `check`. -/

namespace TltsCheck

open DeepWiki.ReactiveSystems

deriving instance Repr for Cmp

/-- Untyped clock constraint (clocks referenced by index). -/
inductive RawCC where
  | true_ : RawCC
  | atom : Nat → Cmp → Nat → RawCC
  | and : RawCC → RawCC → RawCC
  deriving Repr, Inhabited

/-- Untyped timed-HML formula (clocks/actions by index/name). -/
inductive RawMt where
  | tt | ff
  | and : RawMt → RawMt → RawMt
  | or : RawMt → RawMt → RawMt
  | dia : String → RawMt → RawMt
  | box : String → RawMt → RawMt
  | ex : RawMt → RawMt
  | fa : RawMt → RawMt
  | reset : Nat → RawMt → RawMt
  | guard : RawCC → RawMt
  deriving Repr, Inhabited

/-- Untyped timed automaton: clock count, initial location, edges and per-location invariants. -/
structure RawAuto where
  numClocks : Nat
  init : Nat := 0
  /-- `(src, action, dst, guard, resets)`. -/
  edges : List (Nat × String × Nat × RawCC × List Nat) := []
  /-- `(location, invariant)`. -/
  invs : List (Nat × RawCC) := []
  deriving Repr, Inhabited

/-- Number of locations = one past the largest location index used anywhere (≥ 1). -/
def RawAuto.numLocs (R : RawAuto) : Nat :=
  let ls := R.init :: (R.edges.flatMap (fun e => [e.1, e.2.2.1]) ++ R.invs.map (·.1))
  ls.foldr max 0 + 1

/-- Validate a natural index into `Fin n`. -/
def natToFin (n i : Nat) (what : String) : Except String (Fin n) :=
  if h : i < n then pure ⟨i, h⟩ else throw s!"{what} index {i} out of range (have {n})"

/-- Build a typed clock constraint over `Fin n`. -/
def buildCC (n : Nat) : RawCC → Except String (ClockConstraint (Fin n))
  | .true_ => pure .true_
  | .atom clk cmp c => return .atom (← natToFin n clk "clock") cmp c
  | .and a b => return .and (← buildCC n a) (← buildCC n b)

/-- Build a typed formula over actions `String` and formula clocks `Fin k`. -/
def buildMt (k : Nat) : RawMt → Except String (Mt String (Fin k))
  | .tt => pure .tt
  | .ff => pure .ff
  | .and a b => return .and (← buildMt k a) (← buildMt k b)
  | .or a b => return .or (← buildMt k a) (← buildMt k b)
  | .dia a f => return .dia a (← buildMt k f)
  | .box a f => return .box a (← buildMt k f)
  | .ex f => return .existsDelay (← buildMt k f)
  | .fa f => return .forallDelay (← buildMt k f)
  | .reset clk f => return .reset (← natToFin k clk "formula clock") (← buildMt k f)
  | .guard cc => return .guard (← buildCC k cc)

/-- Largest formula-clock index used in a `RawMt` (for sizing `Fin k`); `0` ⇒ no clocks. -/
def RawMt.numClocks : RawMt → Nat
  | .tt | .ff => 0
  | .and a b | .or a b => max a.numClocks b.numClocks
  | .dia _ f | .box _ f | .ex f | .fa f => f.numClocks
  | .reset clk f => max (clk + 1) f.numClocks
  | .guard cc => ccClocks cc
where ccClocks : RawCC → Nat
  | .true_ => 0
  | .atom clk _ _ => clk + 1
  | .and a b => max (ccClocks a) (ccClocks b)

/-- Build the typed automaton `FinAutomaton (Fin numLocs) String (Fin numClocks)`. -/
def buildAuto (R : RawAuto) :
    Except String (FinAutomaton (Fin R.numLocs) String (Fin R.numClocks)) := do
  let n := R.numClocks
  let m := R.numLocs
  let edges ← R.edges.mapM fun (s, act, d, g, rs) => do
    let sF ← natToFin m s "source location"
    let dF ← natToFin m d "destination location"
    let gC ← buildCC n g
    let rsF ← rs.mapM (natToFin n · "reset clock")
    pure (sF, gC, act, rsF, dF)
  let invL ← R.invs.mapM fun (l, cc) => do
    let _ ← natToFin m l "invariant location"
    pure (l, ← buildCC n cc)
  pure { initial := ← natToFin m R.init "initial location"
       , edges := edges
       , inv := fun ℓ => (invL.find? (·.1 == ℓ.val)).elim .true_ (·.2) }

/-- Validate + build + run the verified checker. Returns the proved-correct `A ⊨ F`. -/
def buildAndCheck (R : RawAuto) (F : RawMt) : Except String Bool := do
  let A ← buildAuto R
  let F' ← buildMt F.numClocks F
  pure (check A F')

/-- Decode the `cmp` column value (an enum keyword) into a `Cmp` — a lookup, not a parser. -/
def cmpOfString : String → Option Cmp
  | "le" => some .le | "lt" => some .lt | "eq" => some .eq | "ge" => some .ge | "gt" => some .gt
  | _ => none

/-- The comparison's column keyword. -/
def cmpToKey : Cmp → String
  | .le => "le" | .lt => "lt" | .eq => "eq" | .ge => "ge" | .gt => "gt"

end TltsCheck
