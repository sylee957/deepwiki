import MinPlusCalc.Calc

/-! # `minplus` — an executable, proved-correct (min,plus) calculator over ℤ UPP sequences
A UPP sequence is given by `<vals> <period> <incr>`: stored values `v0,v1,…` followed by a positive
period `d` and increment `c`, denoting `f(n) = f(n-d) + c` past the stored prefix. The `add`/`min`
results are computed by `DeepWiki.UppSeq.add`/`min`, proved correct by `evalNat_add`/`evalNat_min`. -/

open MinPlusCalc DeepWiki

/-- Parse a comma-separated list of integers. -/
def parseVals (s : String) : Except String (List Int) :=
  (s.splitOn ",").mapM fun x =>
    match x.toInt? with
    | some i => .ok i
    | none => .error s!"bad integer '{x}'"

/-- Parse a required natural-number argument. -/
def reqNat (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected a number, got '{s}'")

/-- Parse a required integer argument. -/
def reqInt (s : String) : IO Int :=
  match s.toInt? with
  | some i => pure i
  | none => throw (IO.userError s!"expected an integer, got '{s}'")

/-- Build a validated `UppSeq ℤ` from three argument strings. -/
def reqUpp (vals period incr : String) : IO (UppSeq Int) := do
  match buildUpp ⟨← (match parseVals vals with | .ok v => pure v | .error m => throw (IO.userError m)),
      ← reqNat period, ← reqInt incr⟩ with
  | .ok u => pure u
  | .error m => throw (IO.userError m)

/-- Render a sampled sequence. -/
def fmt (xs : List Int) : String := ", ".intercalate (xs.map toString)

def usage : String := String.intercalate "\n"
  [ "usage: minplus <command>   (executable, proved-correct (min,plus) calculator over ℤ UPP sequences)",
    "  a UPP sequence is  <vals> <period> <incr>  where <vals>=v0,v1,…  and  f(n)=f(n-period)+incr",
    "  past the stored prefix.",
    "    eval <vals> <period> <incr> <n>                 print f(n)",
    "    seq  <vals> <period> <incr> <k>                 print f(0..k-1)",
    "    add  <v1> <p1> <c1> <v2> <p2> <c2> <k>          print (f+g)(0..k-1)   [proved: evalNat_add]",
    "    min  <v1> <p1> <c1> <v2> <p2> <c2> <k>          print (f⊓g)(0..k-1)   [proved (balanced): evalNat_min]" ]

def main (args : List String) : IO Unit := do
  match args with
  | ["eval", v, p, c, n] =>
      let u ← reqUpp v p c
      IO.println (u.evalNat (← reqNat n))
  | ["seq", v, p, c, k] =>
      let u ← reqUpp v p c
      IO.println (fmt (sample u (← reqNat k)))
  | ["add", v1, p1, c1, v2, p2, c2, k] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      IO.println (fmt (sample (u1.add u2) (← reqNat k)))
  | ["min", v1, p1, c1, v2, p2, c2, k] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      -- only the balanced case (equal asymptotic slopes c₁/d₁ = c₂/d₂) is proved correct
      if u1.incr * (u2.period : Int) = u2.incr * (u1.period : Int) then
        IO.println (fmt (sample (u1.min u2) (← reqNat k)))
      else
        throw (IO.userError s!"min: only the balanced case is proved correct, but the slopes \
{u1.incr}/{u1.period} and {u2.incr}/{u2.period} differ. General min needs the dominant-slope \
crossover (not yet implemented), so refusing rather than print an unproved result.")
  | _ => IO.println usage
