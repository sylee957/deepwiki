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

/-- Render a sampled `WithTop ℤ` sequence, printing the top element `⊤` (`+∞`) as `inf`. -/
def fmtWT (xs : List (WithTop ℤ)) : String :=
  ", ".intercalate (xs.map fun x => match x with | none => "inf" | some z => toString z)

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
    "    deconv <v1> <p1> <c1> <v2> <p2> <c2> <k>        print (f⊘g)(0..k-1)   [⨆_k f(n+k)-g(k); needs slope f ≤ slope g; deconvNat_isGreatest]",
    "    deconvupp <v1> <p1> <c1> <v2> <p2> <c2>         print f⊘g AS A UPP SEQUENCE  [deconvUpp; deconvNat_add_period; needs slope f ≤ slope g]",
    "    backlog <vα> <pα> <cα> <vβ> <pβ> <cβ>           print the backlog bound supₜ(α(t)-β(t)) = (α⊘β)(0)  [needs slope α ≤ slope β]",
    "    delay <vα> <pα> <cα> <vβ> <pβ> <cβ>             print the delay bound min{d : ∀t α(t)≤β(t+d)}  [needs slope α ≤ slope β]",
    "    closure <vals> <period> <incr> <k>              print the sub-additive closure f*(0..k-1) = ⨅ₘ f^⊗ᵐ  [closureApproxNat; exact for f(0)=0]",
    "    residual <vβ> <pβ> <cβ> <vα> <pα> <cα> <k>      print the residual service curve [β-α]⁺↑(0..k-1)  [leftover service; residualAt, intro/elim/mono proved]",
    "    tandem <α:v p c> <β1:v p c> <β2:v p c>          print end-to-end service curve β1∗β2 + backlog + delay through two tandem servers  [concatenation; pay bursts only once]" ]

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
  | ["deconvupp", v1, p1, c1, v2, p2, c2] =>
      let u1 ← reqUpp v1 p1 c1
      let u2 ← reqUpp v2 p2 c2
      if slope u1 u2 ≤ slope u2 u1 then
        IO.println (renderUpp (deconvUpp u1 u2))
      else
        throw (IO.userError "deconvupp f ⊘ g requires slope(f) ≤ slope(g) (else the deconvolution is +∞)")
  | ["backlog", va, pa, ca, vb, pb, cb] =>
      let a ← reqUpp va pa ca
      let b ← reqUpp vb pb cb
      if slope a b ≤ slope b a then
        IO.println s!"backlog bound = {backlogBound a b}"
      else
        throw (IO.userError "backlog requires slope(α) ≤ slope(β) (else the backlog is unbounded)")
  | ["delay", va, pa, ca, vb, pb, cb] =>
      let a ← reqUpp va pa ca
      let b ← reqUpp vb pb cb
      if slope a b ≤ slope b a then
        IO.println s!"delay bound = {delayBound a b}"
      else
        throw (IO.userError "delay requires slope(α) ≤ slope(β) (else the delay is unbounded)")
  | ["closure", v, p, c, k] =>
      let u ← reqUpp v p c
      -- exact closure needs f(0) ≥ 0 (else f* = -∞ from iterating the negative origin step)
      if u.evalNat 0 < 0 then
        throw (IO.userError "closure requires f(0) ≥ 0 (else the sub-additive closure is -∞)")
      else
        IO.println (fmtWT (closureSample u (← reqNat k)))
  | ["residual", vβ, pβ, cβ, vα, pα, cα, k] =>
      let β ← reqUpp vβ pβ cβ
      let α ← reqUpp vα pα cα
      IO.println (fmt (residualSample β α (← reqNat k)))
  | ["tandem", va, pa, ca, v1, p1, c1, v2, p2, c2] =>
      let α ← reqUpp va pa ca
      let β₁ ← reqUpp v1 p1 c1
      let β₂ ← reqUpp v2 p2 c2
      -- end-to-end service curve of the two servers in series (concatenation theorem: β₁∗β₂)
      let β := convUpp β₁ β₂
      IO.println s!"end-to-end service curve β₁∗β₂ = {renderUpp β}"
      if slope α β ≤ slope β α then
        IO.println s!"end-to-end backlog bound = {backlogBound α β}"
        IO.println s!"end-to-end delay bound   = {delayBound α β}   (pay bursts only once)"
      else
        throw (IO.userError "tandem requires slope(α) ≤ slope(β₁∗β₂) (else backlog/delay unbounded)")
  | _ => IO.println usage
