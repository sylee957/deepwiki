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
    "    min  <v1> <p1> <c1> <v2> <p2> <c2> <k>          print (f⊓g)(0..k-1)   [pointwise; UPP by min_evalNat_add_lcm]",
    "    max  <v1> <p1> <c1> <v2> <p2> <c2> <k>          print (f⊔g)(0..k-1)   [pointwise; UPP by max_evalNat_add_lcm]",
    "    conv <v1> <p1> <c1> <v2> <p2> <c2> <k>          print (f⊗g)(0..k-1)   [⨅ k≤n f(k)+g(n-k); proved: convNat_le/_eq]",
    "    convupp <v1> <p1> <c1> <v2> <p2> <c2>           print f⊗g AS A UPP SEQUENCE  [composable; convFrom/evalNat_convFrom]",
    "    addupp <v1> <p1> <c1> <v2> <p2> <c2>            print f+g AS A UPP SEQUENCE  [UppSeq.add / evalNat_add]",
    "    minupp <v1> <p1> <c1> <v2> <p2> <c2>            print f⊓g AS A UPP SEQUENCE  [minUpp; min_evalNat_add_lcm_window]",
    "    maxupp <v1> <p1> <c1> <v2> <p2> <c2>            print f⊔g AS A UPP SEQUENCE  [maxUpp; max_evalNat_add_lcm_window]",
    "    deconv <v1> <p1> <c1> <v2> <p2> <c2> <k>        print (f⊘g)(0..k-1)   [⨆_k f(n+k)-g(k); needs slope f ≤ slope g; deconvNat_isGreatest]" ]

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
      -- the pointwise minimum, correct by definition (and UPP by min_evalNat_add_lcm)
      IO.println (fmt ((List.range (← reqNat k)).map (fun n => Min.min (u1.evalNat n) (u2.evalNat n))))
  | ["max", v1, p1, c1, v2, p2, c2, k] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      -- the pointwise maximum, correct by definition (and UPP by max_evalNat_add_lcm)
      IO.println (fmt ((List.range (← reqNat k)).map (fun n => Max.max (u1.evalNat n) (u2.evalNat n))))
  | ["conv", v1, p1, c1, v2, p2, c2, k] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      IO.println (fmt ((List.range (← reqNat k)).map (fun n => u1.convNat u2 n)))
  | ["convupp", v1, p1, c1, v2, p2, c2] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      -- the convolution as an actual UPP sequence (prefix, period, increment) — composable
      IO.println (renderUpp (convUpp u1 u2))
  | ["addupp", v1, p1, c1, v2, p2, c2] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      IO.println (renderUpp (u1.add u2))
  | ["minupp", v1, p1, c1, v2, p2, c2] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      IO.println (renderUpp (minUpp u1 u2))
  | ["maxupp", v1, p1, c1, v2, p2, c2] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      IO.println (renderUpp (maxUpp u1 u2))
  | ["deconv", v1, p1, c1, v2, p2, c2, k] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      -- finite only when slope(f) ≤ slope(g); otherwise f ⊘ g = +∞ (not representable)
      if slope u1 u2 ≤ slope u2 u1 then
        IO.println (fmt ((List.range (← reqNat k)).map (fun n => u1.deconvNat u2 n)))
      else
        throw (IO.userError "deconv f ⊘ g requires slope(f) ≤ slope(g) (else the deconvolution is +∞)")
  | _ => IO.println usage
