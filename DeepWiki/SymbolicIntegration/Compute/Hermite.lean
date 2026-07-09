import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Computable Hermite reduction over `ℚ`
Computes the rational part of `∫ A/D` as `(g, B, D*)` with `∫ A/D = g + ∫ B/D*` and `D*` squarefree,
on the dense coefficient carrier `DensePoly ℚ := List ℚ`. `ratIntegrate` combines it with `lrtLogPart` for
the full `∫A/D = rational part + log part`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Rational-function arithmetic on `DensePoly ℚ × DensePoly ℚ` (numerator, denominator) -/

/-- Rational function as a `(numerator, denominator)` pair of `DensePoly ℚ`s. -/
abbrev QFun := DensePoly ℚ × DensePoly ℚ

/-- Zero rational function `0/1`. -/
def qzero : QFun := ([], [1])

/-- Addition of rational functions `a/b + c/d = (a·d + c·b)/(b·d)` (no gcd reduction). -/
def qadd (x y : QFun) : QFun :=
  let (a, b) := x
  let (c, d) := y
  (cadd (cmul a d) (cmul c b), cmul b d)

/-! ### Computable Bézout / Diophantine solver on `DensePoly ℚ` -/

/-- Diophantine/Bézout solver `cdiophantine fuel p q rhs = (B, C)` solving `B·p + C·q = rhs` with
`deg B < deg q`, for coprime `p, q`. -/
def cdiophantine (fuel : ℕ) (p q rhs : DensePoly ℚ) : DensePoly ℚ × DensePoly ℚ :=
  let (g, s, t) := cgcdExt fuel p q
  let gc : ℚ := clead g
  let S := cscale gc⁻¹ (cmul rhs s)
  let T := cscale gc⁻¹ (cmul rhs t)
  let (quo, B) := cdivmod fuel S q
  let C := cadd T (cmul quo p)
  (cnorm B, cnorm C)

/-! ### The computable quadratic Hermite reduction (per squarefree factor) -/

/-- Inner Hermite loop over one squarefree factor `V` of multiplicity `i`: with `U = D/Vⁱ`, peel the
rational pieces `B/Vʲ` (`j = i−1 … 1`) into `g`, returning the rational part `g` and the final
numerator `A`. -/
def hermiteInner (fuel : ℕ) (V U : DensePoly ℚ) : ℕ → DensePoly ℚ → QFun → QFun × DensePoly ℚ
  | 0, A, g => (g, A)
  | j + 1, A, g =>
    let jval : ℚ := (j : ℚ) + 1
    let Vderiv := cderiv V
    let p := cmul U Vderiv
    let rhs := cscale (-jval⁻¹) A                         -- `−A/j`
    let (B, C) := cdiophantine fuel p V rhs
    -- summand `B/Vʲ`: denominator is `V` raised to power `j+1`.
    let Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1]
    let g' := qadd g (B, Vpow)
    let A' := csub (cscale (-jval) C) (cmul U (cderiv B))  -- `A ← −j·C − U·B'`
    hermiteInner fuel V U j A' g'

/-- Quadratic Hermite reduction `hermiteReduce fuel A D = ((gnum, gden), (B, Dstar))`: returns the
rational part `g = gnum/gden` and the reduced integrand `B/Dstar` with `Dstar` squarefree, so
`∫ A/D = g + ∫ B/Dstar`. -/
def hermiteReduce (fuel : ℕ) (A D : DensePoly ℚ) : QFun × QFun :=
  let factors := csqfreeFactor fuel D
  let Dstar := factors.foldl (fun acc (Vi, _) => cmul acc Vi) [1]
  -- Accumulate the rational part `g`. Each factor of multiplicity `i ≥ 2` contributes via `hermiteInner`
  -- against the global numerator `A` over `D` (the inner solve uses `U = D/Vⁱ`, so `B/Vʲ` is correctly
  -- scaled relative to the full `A/D`).
  let g : QFun := factors.foldl
    (fun (gAcc : QFun) (Vi, i) =>
      if i ≤ 1 then gAcc
      else
        let Vi_pow := (List.range i).foldl (fun acc _ => cmul acc Vi) [1]
        let U := cdiv fuel D Vi_pow
        let (gloc, _) := hermiteInner fuel Vi U (i - 1) A qzero
        qadd gAcc gloc)
    qzero
  let (gnum, gden) := g
  -- residual numerator `B` over `Dstar`, from `A/D − g' = B/Dstar`:
  -- `(A·gden² − D·(gnum'·gden − gnum·gden'))·Dstar / (D·gden²)` (exact division to a polynomial).
  let gprimeNum := csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))
  let gden2 := cmul gden gden
  let resNum := csub (cmul A gden2) (cmul D gprimeNum)
  let resDen := cmul D gden2
  let Bres := cdiv fuel (cmul resNum Dstar) resDen
  ((cnorm gnum, cnorm gden), (cnorm Bres, cnorm Dstar))

/-! ### Full rational integrator: Hermite rational part + LRT log part -/

/-- Full rational-function integrator `ratIntegrate fuel A D = ((gnum, gden), logpart)`: the Hermite
rational part `gnum/gden` plus the logarithmic part of the residual `∫B/Dstar`, giving
`∫ A/D = gnum/gden + ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`. -/
def ratIntegrate (fuel : ℕ) (A D : DensePoly ℚ) : QFun × List (DensePoly ℚ × BPoly) :=
  let ((gnum, gden), (B, Dstar)) := hermiteReduce fuel A D
  ((gnum, gden), lrtLogPart fuel B Dstar)

/-! ### Correctness against the noncomputable Hermite theory
Under the `toPoly` bridge, `hermiteReduce` produces a valid Hermite reduction on all inputs — the
residual identity `g' + B/Dstar = A/D` — proven in `HermiteCorrectness`. -/

end Compute

end DeepWiki.SymbolicIntegration
