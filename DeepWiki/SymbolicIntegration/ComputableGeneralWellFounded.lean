import DeepWiki.SymbolicIntegration.ComputableGeneralQuotient
import DeepWiki.SymbolicIntegration.ComputableGeneralSetup
import DeepWiki.SymbolicIntegration.ComputableFuelFreeDiophantine

/-! # Fuel-free GENERAL (non-radical) algebraic-function integration

The radical arc (`ComputableRadicalWellFounded`) made the simple-radical integrator fuel-free by converting
its three Case-1/2/3 Hermite descents to well-founded recursion. The GENERAL (arbitrary plane curve
`K(x)[y]/(f)`) integrator is a **different shape** — and the difference IS the measure subtlety the conversion
has to isolate:

**★ The general engine has NO recursion of its own — no Case-1/2/3 descents, no termination measure.** It
deliberately **sidesteps** the Hermite/pole-order reduction (that integrand-splitting front-end is deferred)
and exhibits BOTH the rational part `v` and the log argument `u` as a single **`K`-linear solve over the
integral basis**: `afRationalSolveWf` / `afLogArgSolveWf` build a finite `ℚ`-matrix (`afRatMatrixWf` /
`afLogMatrixWf`)
of the undetermined-coefficient system `afDeriv f (Σ c_{ij} xʲ wᵢ) = integrand` and solve it by the
non-recursive field solver `kernelBasisG` / `gaussElimG`. So — unlike the radical engine — there are **no
`…IterateWf` analogues to build**; the entire fuel-free conversion is **pure leaf substitution**.

**The single external-fuel leaf.** The fuel the general pipeline carries is threaded down one chain to exactly
one external-fuel call: `afDeriv fuel f u` (the general derivation) → `afYprime fuel f` (the implicit
derivative `y' = −f_x·f_y⁻¹`) → `afFyInv fuel f` (the inverse `f_y⁻¹ mod f`) → **`cdiophantineG fuel (afFy f)
f [1]`** (the Bézout cofactor `s` of `s·f_y + t·f = 1`). Everything else is already fuel-free: `afReduce` /
`afMul` carry a **self-computed** bound `cmodG ((p).length + 1) …` (not an external `ℕ`), and the matrix
extraction (`nums`/`dens`/`cleared`/rows) + `kernelBasisG` are flat. So the whole conversion bottoms at
swapping `cdiophantineG` for the fuel-free `cdiophantineGWf` (`ComputableFuelFreeDiophantine`, the same leaf
the radical `radPartialFractionCoprime` uses).

This file therefore builds, by leaf substitution:

* **Part 1 — the fuel-free general derivation** `afFyInvWf` / `afYprimeWf` / `afDerivWf` (the one leaf chain),
  `[CField α] [CDiffField α]`-generic like the originals, with the quotient invariant proved directly from
  the fuel-free `cdiophantineGWf` leaf.
* **Part 2 — the fuel-free flat solvers** `afRatColumnsWf` / `afRatMatrixWf` / `afRationalSolveWf` and the log
  analogues `afLogResidualWf` / `afLogColumnsWf` / `afLogMatrixWf` / `afLogArgSolveWf` — flat substitution of
  `afDerivWf` for `afDeriv` (the matrix extraction + `kernelBasisG` are shared verbatim, non-recursive).
* **Part 3 — the fuel-free top-level** `afIntegrateAlgebraicWf` (the general `∫ = v + Σ log u`) + the
  Wf validation below.
* **Part 4 — ★ a direct `native_decide` validation**: `afIntegrateAlgebraicWf` returns a combined integral
  `∫ (y + afDeriv(y)/y) dx = (3/5)xy + log y` on the cuspidal cubic `y³ = x²`, and the output is checked
  with `afDerivWf`, so `D(∫f) = f` holds of the **fuel-free** output.

Every `…Wf` is `[CField α]`-only on the fuel-free fragment (plus `[CDiffField α]` where the derivation needs
the base `d/dx`) — never `[CFieldSpec α]` on the runtime ops, so the whole arc still `native_decide`s over the
noncomputable `ℚ(x)` carrier. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ## Part 1 — the fuel-free general derivation `afDerivWf` (the one leaf chain)

`afDeriv fuel f u = afReduce f (u.map cderiv + cderivG u · afYprime fuel f)`, and the only external fuel is in
`afYprime fuel f = afReduce f (−f_x · afFyInv fuel f)`, whose fuel is in
`afFyInv fuel f = (cdiophantineG fuel (afFy f) f [1]).1`. Swap that one leaf for the fuel-free
`cdiophantineGWf` and the whole derivation is fuel-free; `afReduce` / `afMul` are already self-bounded. -/

/-- **Fuel-free `f_y⁻¹ mod f`** `afFyInvWf f = (cdiophantineGWf (afFy f) f [1]).1`: the fuel-free companion of
`afFyInv`, the first Bézout cofactor `s` of `s·f_y + t·f = 1` computed by the fuel-free `cdiophantineGWf`
(`ComputableFuelFreeDiophantine`) instead of `cdiophantineG fuel`. **No fuel at runtime.** The inverse of
`∂f/∂y` in `K(x)[y]/(f)` (valid for separable `f`), degree `< deg f`. -/
def afFyInvWf (f : CPolyG α) : CPolyG α :=
  (cdiophantineGWf (afFy f) f [CField.one]).1

variable [CDiffField α]

/-- **The fuel-free implicit derivative** `afYprimeWf f = afReduce f (−f_x · afFyInvWf f)`: the fuel-free
companion of `afYprime`, `y' = −(∂f/∂x)·(∂f/∂y)⁻¹ mod f` with the fuel-free inverse `afFyInvWf`. `afReduce`
is self-bounded (`cmodG ((p).length + 1) …`), so this carries **no fuel**. -/
def afYprimeWf (f : CPolyG α) : CPolyG α :=
  afReduce f (cmulG (cnegG (afFx f)) (afFyInvWf f))

/-- **The fuel-free GENERAL derivation** `afDerivWf f u = afReduce f (u.map cderiv + cderivG u · afYprimeWf f)`:
the fuel-free companion of `afDeriv`, the product rule `D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'` with the
fuel-free implicit derivative `afYprimeWf`. **No fuel at runtime** (the one external-fuel leaf, the
`f_y`-inversion, is now `afFyInvWf`/`cdiophantineGWf`). `[CField α] [CDiffField α]`-generic, so it
`native_decide`s. -/
def afDerivWf (f u : CPolyG α) : CPolyG α :=
  afReduce f (caddG ((u : List α).map CDiffField.cderiv) (cmulG (cderivG u) (afYprimeWf f)))

section WfInvariant

variable [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The Wf derivation invariant

The shared quotient API lives in `ComputableGeneralQuotient`. The derivation-invariant proof works directly
for `afDerivWf`, replacing the single `cdiophantineG` Bézout leaf by `cdiophantineGWf` and phrasing
separability as the fuel-free gcd being a nonzero constant. -/

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **`afDerivWf = afReduce f ∘ cmonomialDeriv (afYprimeWf f)`** definitionally. -/
theorem afDerivWf_eq_afReduce_cmonomialDeriv (f u : CPolyG α) :
    afDerivWf f u = afReduce f (cmonomialDeriv (afYprimeWf f) u) := rfl

/-- The Wf keystone: `afDerivWf` realizes `implicitDeriv (toPolyG (afYprimeWf f))` in the quotient. -/
theorem mk_toPolyG_afDerivWf (f u : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f u))
      = Ideal.Quotient.mk (afIdeal f)
          (Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG u)) := by
  rw [afDerivWf_eq_afReduce_cmonomialDeriv, mk_toPolyG_afReduce f _ hf, toPolyG_cmonomialDeriv]

/-- `afDerivWf` is additive modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_add (f a b : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (caddG a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f a))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f b)) := by
  rw [mk_toPolyG_afDerivWf f _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf, toPolyG_caddG, map_add, map_add]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Fuel-free Bézout inverse of `f_y` in the quotient. -/
theorem mk_toPolyG_afFyInvWf_mul_afFy (f : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f)
        (toPolyG (afFyInvWf f) * toPolyG (afFy f)) = 1 := by
  have hbez := toPolyG_cdiophantineGWf (afFy f) f [CField.one] hf hgdeg hgne
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [hone] at hbez
  rw [show toPolyG (afFyInvWf f) * toPolyG (afFy f)
      = 1 - toPolyG (cdiophantineGWf (afFy f) f [CField.one]).2 * toPolyG f from by
        rw [afFyInvWf]; linear_combination hbez]
  have hmem : Ideal.Quotient.mk (afIdeal f)
      (toPolyG (cdiophantineGWf (afFy f) f [CField.one]).2 * toPolyG f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (mul_curve_mem f _)
  rw [map_sub, hmem, map_one, sub_zero]

/-- The Wf implicit derivation kills the curve generator modulo its ideal. -/
theorem implicitDerivWf_curve_mem (f : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG f) ∈ afIdeal f := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [show Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG f)
      = Differential.mapCoeffs (toPolyG f)
        + toPolyG (afYprimeWf f) * Polynomial.derivative (toPolyG f) from by
        simp [Differential.implicitDeriv, derivative']]
  rw [mapCoeffs_toPolyG_eq_afFx, derivative_toPolyG_eq_afFy]
  have hyp : Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprimeWf f))
      = Ideal.Quotient.mk (afIdeal f) (- toPolyG (afFx f) * toPolyG (afFyInvWf f)) := by
    rw [afYprimeWf, mk_toPolyG_afReduce f _ hf, toPolyG_cmulG, toPolyG_cnegG]
  rw [map_add, map_mul, hyp, ← map_mul]
  have hfyinv := mk_toPolyG_afFyInvWf_mul_afFy f hf hgdeg hgne
  rw [show - toPolyG (afFx f) * toPolyG (afFyInvWf f) * toPolyG (afFy f)
      = - (toPolyG (afFx f) * (toPolyG (afFyInvWf f) * toPolyG (afFy f))) from by ring,
    map_neg, map_mul, hfyinv, mul_one, add_neg_cancel]

/-- The Wf implicit derivation maps `afIdeal f` into itself. -/
theorem implicitDerivWf_mem_afIdeal (f : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    {x : (CFieldSpec.K α)[X]} (hx : x ∈ afIdeal f) :
    Differential.implicitDeriv (toPolyG (afYprimeWf f)) x ∈ afIdeal f := by
  rw [afIdeal, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · exact implicitDerivWf_curve_mem f hf hgdeg hgne
  · exact Ideal.subset_span (Set.mem_singleton _)

/-- The Wf implicit derivation descends to the quotient by `afIdeal f`. -/
theorem mk_implicitDerivWf_congr (f : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    {p q : (CFieldSpec.K α)[X]}
    (hpq : Ideal.Quotient.mk (afIdeal f) p = Ideal.Quotient.mk (afIdeal f) q) :
    Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprimeWf f)) p)
      = Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprimeWf f)) q) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply implicitDerivWf_mem_afIdeal f hf hgdeg hgne
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpq, sub_self]

/-- `afDerivWf` is Leibniz modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_afMul (f a b : CPolyG α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afMul f a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f (afDerivWf f a) b))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f a (afDerivWf f b))) := by
  set yp := toPolyG (afYprimeWf f) with hyp
  set A := toPolyG a with hA
  set B := toPolyG b with hB
  rw [mk_toPolyG_afDerivWf f _ hf, ← hyp]
  rw [mk_implicitDerivWf_congr f hf hgdeg hgne (mk_toPolyG_afMul f a b hf)]
  rw [mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf, ← hyp, ← hA, ← hB]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  ring

/-- `afDerivWf` kills `1` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_one (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f [CField.one])) = 0 := by
  rw [mk_toPolyG_afDerivWf f _ hf]
  have h1 : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [h1, Derivation.map_one_eq_zero, map_zero]

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip certificate is the free-polynomial integrand identity. -/
theorem toPolyG_afDerivWf_eq_of_roundtrip (f v g : CPolyG α)
    (hcheck : cisZeroG (csubG (afDerivWf f v) g) = true) :
    toPolyG (afDerivWf f v) = toPolyG g := by
  simpa [cisZeroG_iff, sub_eq_zero] using hcheck

end WfInvariant

end CPolyG

/-! ## Part 2 — the fuel-free flat solvers (leaf-substitute `afDerivWf` for `afDeriv`)

The general rational and log argument solves are flat: build a `ℚ`-matrix and solve it with `kernelBasisG`.
The old fuel-bearing piece was the columns' `afDeriv`; the Wf path computes those columns with `afDerivWf`.
The matrix extraction and `kernelBasisG` are shared verbatim. The general engine is specialized to
`QFunNZG ℚ`, so these are too. -/

/-- **Fuel-free rational-part residual columns** `afRatColumnsWf f basis degBound integrand`: the fuel-free
companion of `afRatColumns`, the per-monomial derivatives `afDerivWf f (xʲ wᵢ)` followed by the forced
`−integrand` column. -/
def afRatColumnsWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (CPolyG (QFunNZG ℚ)) :=
  (afRatMonomials basis degBound).map (afDerivWf f) ++ [cnegG integrand]

/-- **Fuel-free `ℚ`-matrix of the rational-part system** `afRatMatrixWf f basis degBound integrand`: the
fuel-free companion of `afRatMatrix`, identical matrix extraction (clear each `K(x)` coordinate to numerators
over a common denominator, read off `x`-power coefficients) on the fuel-free columns `afRatColumnsWf`. The
extraction is shared verbatim (non-recursive). -/
def afRatMatrixWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (List ℚ) × ℕ :=
  let cols := afRatColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdegG f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → QFunNZG ℚ := fun k => (cols[k]!).getD i CField.zero
    let nums : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.1)
    let dens : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.2)
    let cleared : List (CPolyG ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmulG acc (dens[l]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- **★ Fuel-free general rational-part solve** `afRationalSolveWf f basis degBound integrand = some v`: the
fuel-free companion of `afRationalSolve`, deriving the rational part `v = Σ c_{ij} xʲ wᵢ` with `afDeriv f v =
integrand` by the `K`-linear solve over the integral basis — same flat structure (build `afRatMatrixWf`, find
a kernel vector with nonzero RHS coordinate, normalize, reassemble `v`), **no fuel at runtime**. -/
def afRationalSolveWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : Option (CPolyG (QFunNZG ℚ)) :=
  let (rows, nCols) := afRatMatrixWf f basis degBound integrand
  let kers := kernelBasisG nCols rows
  match kers.find? (fun c => c.getD (nCols - 1) 0 ≠ 0) with
  | none => none
  | some c =>
    let rhs := c.getD (nCols - 1) 0
    let monos := afRatMonomials basis degBound
    let v : CPolyG (QFunNZG ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0 / rhs
        caddG acc (cscaleG (qxOfNum [coeff]) (monos.getD idx []))) ([] : CPolyG (QFunNZG ℚ))
    some v

/-- **Fuel-free log-derivative residual** `afLogResidualWf f integrand u = afDerivWf f u − afMul f u
integrand`: the fuel-free companion of `afLogResidual` (`afMul` is self-bounded, so only `afDerivWf` changes). -/
def afLogResidualWf (f integrand u : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  csubG (afDerivWf f u) (afMul f u integrand)

/-- **Fuel-free log-argument residual columns** `afLogColumnsWf f basis degBound integrand`: the fuel-free
companion of `afLogColumns`, the per-monomial log-derivative residuals `afLogResidualWf f integrand (xʲ wᵢ)`
(no forced `−integrand` column — the log system is homogeneous in `u`). -/
def afLogColumnsWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (CPolyG (QFunNZG ℚ)) :=
  (afRatMonomials basis degBound).map (afLogResidualWf f integrand)

/-- **Fuel-free `ℚ`-matrix of the log-argument system** `afLogMatrixWf f basis degBound integrand`: the
fuel-free companion of `afLogMatrix`, identical matrix extraction on the fuel-free homogeneous columns
`afLogColumnsWf`. The extraction is shared verbatim (non-recursive). -/
def afLogMatrixWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (List ℚ) × ℕ :=
  let cols := afLogColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdegG f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → QFunNZG ℚ := fun k => (cols[k]!).getD i CField.zero
    let nums : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.1)
    let dens : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.2)
    let cleared : List (CPolyG ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmulG acc (dens[l]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- **★ Fuel-free general log-argument solve** `afLogArgSolveWf f basis degBound integrand = some u`: the
fuel-free companion of `afLogArgSolve`, deriving the log argument `u = Σ c_{ij} xʲ wᵢ` with `afDeriv f u =
afMul f u integrand` (`∫ integrand = log u`) by the homogeneous `K`-linear solve — same flat structure (build
`afLogMatrixWf`, find the first nonzero kernel vector, reassemble `u`), **no fuel at runtime**. -/
def afLogArgSolveWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : Option (CPolyG (QFunNZG ℚ)) :=
  let (rows, nCols) := afLogMatrixWf f basis degBound integrand
  let kers := kernelBasisG nCols rows
  match kers.find? (fun c => c.any (fun a => a ≠ 0)) with
  | none => none
  | some c =>
    let monos := afRatMonomials basis degBound
    let u : CPolyG (QFunNZG ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0
        caddG acc (cscaleG (qxOfNum [coeff]) (monos.getD idx []))) ([] : CPolyG (QFunNZG ℚ))
    some u

/-! ## Part 3 — the fuel-free top-level `afIntegrateAlgebraicWf` (the general `∫ = v + Σ log u`)

The general top-level is one flat `match` over `afRationalSolveWf` (rational part) + `afLogArgSolveWf` (log
part). Pure substitution, not self-recursive. -/

/-- **★ The fuel-free general-curve integrator** `afIntegrateAlgebraicWf f basis degBound ratIntegrand
logIntegrand = some (v, u)`: the fuel-free companion of `afIntegrateAlgebraic`, producing the general
`∫ (ratIntegrand + logIntegrand) dx = v + log u` (principal case) — the rational part `v` by
`afRationalSolveWf` (`afDeriv f v = ratIntegrand`) and the log argument `u` by `afLogArgSolveWf` (`afDeriv f u
= afMul f u logIntegrand`), both `K`-linear solves over the integral basis through the fuel-free general
derivation `afDerivWf`. `none` if either solve fails. **No fuel at runtime**; not self-recursive (no
`termination_by`). The general analogue of `cIntegrateAlgebraicWf`. -/
def afIntegrateAlgebraicWf (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ)) :
    Option (CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  match afRationalSolveWf f basis degBound ratIntegrand,
        afLogArgSolveWf f basis degBound logIntegrand with
  | some v, some u => some (v, u)
  | _, _ => none

/-! ## Part 4 — ★ top-level `native_decide` validation: the GENERAL integrator is fuel-free

The fuel-free top-level returns the expected combined integral and the derivative checks are made with
`afDerivWf`, so the `D(∫f) = f` validation holds of the **fuel-free** output. The cuspidal-cubic combined
integral `∫ (y + afDerivWf(y)/y) dx = (3/5)xy + log y` on `y³ = x²` is the witness. -/

/-- The rational summand input for the fuel-free cuspidal-cubic combined validation. -/
def gcCombineRatIntegrandWf : CPolyG (QFunNZG ℚ) := gcuspCubicY

/-- The log-derivative input for the fuel-free cuspidal-cubic combined validation. -/
def gcCombineLogIntegrandWf : CPolyG (QFunNZG ℚ) :=
  afMul gcuspCubicF (afDerivWf gcuspCubicF gcuspCubicY)
    [CField.zero, CField.zero, qxOfFrac [1] [0, 0, 1] (by decide)]

/-- **The fuel-free general integrator run** `afIntegrateAlgebraicWf …`'s data, on the cuspidal cubic
`y³ = x²` combined integral `∫ (y + afDerivWf(y)/y) dx`. -/
def gcCombineSolvedWf : Option (CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  afIntegrateAlgebraicWf gcuspCubicF gcuspCubicBasis 2 gcCombineRatIntegrandWf gcCombineLogIntegrandWf

/-- **★★ The FUEL-FREE general-curve integrator integrates `∫ (y + afDeriv(y)/y) dx = (3/5)xy + log y`**
(`native_decide`). The fuel-free `afIntegrateAlgebraicWf` derives the rational part `v = (3/5)x·y`
(`afDerivWf f v = y`) AND the log argument `u` a nonzero multiple of `y` (`afDerivWf f u = afMul f u logIntegrand`,
`∫ afDeriv(y)/y = log y`) on the cuspidal cubic `y³ = x²` — both by `K`-linear solves through the GENERAL
derivation `afDerivWf`, **with no `ℕ`-fuel**. Checked, on the fuel-free output, by `afDerivWf f v − y`
vanishing, `v = (3/5)xy`, the Wf log-residual vanishing on `u`, and `u` a nonzero multiple of `y`.
**The general-curve integrator now integrates end-to-end with no fuel** — the
last piece of the algebraic engine's fuel-free conversion. -/
theorem afIntegrateAlgebraicWf_cuspCubic_combine :
    (gcCombineSolvedWf.map (fun p =>
      let v := p.1
      let u := p.2
      cisZeroG (csubG (afDerivWf gcuspCubicF v) gcCombineRatIntegrandWf)
      && cisZeroG (csubG v [CField.zero, qxOfNum [0, 3/5]])
      && cisZeroG (afLogResidualWf gcuspCubicF gcCombineLogIntegrandWf u)
      && cisZeroG [u.getD 0 CField.zero]
      && !cisZeroG [u.getD 1 CField.zero])) = some true := by native_decide

/-! ### `#print axioms` — the fuel-free general algebraic integrator

The `…Wf` defs are fuel-free by **pure leaf substitution** (the general engine has no recursion / measure of
its own — the measure subtlety vs the radical case is that there is **none**). `#print axioms` on the Wf
proofs shows the standard `[propext, Quot.sound]` on quotient soundness, **no `sorryAx`**; the
`native_decide` validation theorem adds only the native compiler axiom. -/

-- The Wf quotient invariant and Leibniz law for the general derivation:
#print axioms CPolyG.mk_toPolyG_afDerivWf
#print axioms CPolyG.mk_toPolyG_afDerivWf_afMul

-- ★★ The fuel-free general integrator integrates end-to-end (D(∫f) = f):
#print axioms afIntegrateAlgebraicWf_cuspCubic_combine

end DeepWiki.SymbolicIntegration
