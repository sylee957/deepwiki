import DeepWiki.SymbolicIntegration.ComputableGeneralQuotient

/-! # The general derivation invariant: `afDeriv` is a genuine derivation
`ComputableGeneralDerivation` builds the GENERAL carrier derivation `afDeriv fuel f` on
`K(x)[y]/(f)` for an **arbitrary monic curve** `f` — beyond the hyperelliptic diagonal `radDeriv` — out
of the implicit derivative `y' = −f_x/f_y` (`afYprime`, the field-inverted `f_y` via the Bézout cofactor
`cdiophantineG (afFy f) f [1]`), and *validates* it on examples by `native_decide` (the cuspidal cubic
`y³ = x²`, the conservativity `afDeriv (y² − ρ) = radDeriv 2 ρ`). This file makes "`afDeriv` is a
derivation" a **general theorem** — additive and Leibniz — over an arbitrary base
`[CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]`, mirroring the radical template
`ComputableRadicalDerivationInvariant`.

The carrier `K(x)[y]/(f)` *is* the quotient `K[X] ⧸ (toPolyG f)` (treating the formal variable `X` as the
generator `y`), so — exactly as in the radical case — the faithful statements live **in that quotient**,
read through the Horner bridge `toPolyG`. Because `afDeriv = afReduce f ∘ (the un-reduced derivation)`,
**every** `afDeriv` law (even additivity) is a quotient statement modulo `afIdeal f = (toPolyG f)`. The
keystone is

* **`mk_toPolyG_afDeriv`** — `afDeriv` realizes Mathlib's `implicitDeriv (toPolyG yprime)` in the
  quotient: `mk (toPolyG (afDeriv fuel f u)) = mk (implicitDeriv (toPolyG (afYprime fuel f)) (toPolyG u))`
  with `yprime = afYprime fuel f = −f_x·f_y⁻¹`. The general analogue of `toPolyG_radDeriv` — the radical's
  `ℓ = f'/(nf)` and the diagonal rule `y' = ℓ·y` become the general `yprime = −f_x/f_y` and the
  implicit-function-theorem total derivative. The realization is exact in `K[X]` *before* the `afReduce`
  fold (`afDeriv = afReduce f (cmonomialDeriv yprime u)`, `cmonomialDeriv` realizing `implicitDeriv` via
  `toPolyG_cmonomialDeriv`); the fold only changes the polynomial by a multiple of `toPolyG f`, so it is
  invisible in the quotient (`mk_toPolyG_afReduce`).

From the keystone, since `implicitDeriv v` is a Mathlib `Derivation` (hence ℤ-linear and Leibniz):

* **`mk_toPolyG_afDeriv_add`** (additivity) — `afDeriv` commutes with `caddG` in the quotient (the
  ℤ-linearity of `implicitDeriv`). The clean floor.
* **`mk_toPolyG_afDeriv_afMul`** (Leibniz) — the product rule for `afMul` in the carrier
  `K[X] ⧸ (toPolyG f)`, valid when the curve is **separable** (`gcd(f, f_y)` a nonzero constant, so `f_y`
  is a unit). The pieces mirror the radical template: (i) `afReduce`/`afMul` change a polynomial only by a
  multiple of `toPolyG f` (`mk_toPolyG_afReduce`, `mk_toPolyG_afMul`), so `afMul ≡ ·` in the quotient;
  (ii) the crux `implicitDeriv_curve_mem`: `D(toPolyG f) ∈ afIdeal f` — the general consistency relation
  `f_x + f_y·y' = 0`, which holds because `afYprime` is **defined** as `−f_x·f_y⁻¹` (so `f_y·yprime ≡ −f_x`
  in the field, the Bézout `f_y⁻¹·f_y ≡ 1`) — so `D` descends to the quotient (`mk_implicitDeriv_congr`);
  (iii) the free-polynomial Leibniz of the Mathlib derivation `implicitDeriv`.

Both additivity and Leibniz are proven **generally** and **axiom-clean** (`[propext, Classical.choice,
Quot.sound]`, no `native_decide`, no `sorry`). They are the derivation axioms underwriting the eventual
**general-curve soundness** `D(∫f) = f` (the non-hyperelliptic analogue of the radical capstone): the
coupled eq.-11 Hermite reduction and the divisor/log machinery only *mean* anything once `afDeriv` is
proven additive and Leibniz. The `afDeriv = implicitDeriv` keystone carries over verbatim from the radical
template — only the implicit rule changes (the general `−f_x/f_y` for the diagonal `ℓ·y`), so the proof
*shape* is identical, with the radical's scalar non-degeneracy `n·toK f ≠ 0` replaced by the curve's
separability (the Bézout-cofactor hypotheses of `toPolyG_cdiophantineG`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-! ### The keystone: `afDeriv` realizes `implicitDeriv (toPolyG yprime)` in the quotient

`afDeriv fuel f u = afReduce f (cmonomialDeriv yprime u)` (definitionally — both unfold to `afReduce f
(caddG (u.map cderiv) (cmulG (cderivG u) yprime))`), with `yprime = afYprime fuel f`. The un-reduced
`cmonomialDeriv yprime u` realizes Mathlib's `implicitDeriv (toPolyG yprime) (toPolyG u)`
(`toPolyG_cmonomialDeriv`), and `afReduce` is invisible in the quotient (`mk_toPolyG_afReduce`). So the
general derivation IS `implicitDeriv` for the rule `y' = −f_x/f_y`, read mod `f`. -/

variable [CDiffField α] [CDiffFieldSpec α]

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **`afDeriv = afReduce f ∘ cmonomialDeriv yprime`** — `afDeriv fuel f u = afReduce f (cmonomialDeriv
(afYprime fuel f) u)`, definitionally (both sides unfold to `afReduce f (caddG (u.map cderiv) (cmulG
(cderivG u) (afYprime fuel f)))`). The bridge identifying the general derivation with the monomial
derivation `D = κ_D + yprime·d/dy` reduced `mod f`. -/
theorem afDeriv_eq_afReduce_cmonomialDeriv (fuel : ℕ) (f u : CPolyG α) :
    afDeriv fuel f u = afReduce f (cmonomialDeriv (afYprime fuel f) u) := rfl

/-- **★ The keystone — `afDeriv` realizes `implicitDeriv (toPolyG yprime)` in the quotient**: through the
Horner bridge `toPolyG` (with `X` the generator `y`), `mk (toPolyG (afDeriv fuel f u)) = mk (implicitDeriv
(toPolyG (afYprime fuel f)) (toPolyG u))`, the general analogue of `toPolyG_radDeriv`. `afDeriv =
afReduce f (cmonomialDeriv yprime u)` (`afDeriv_eq_afReduce_cmonomialDeriv`), `cmonomialDeriv` realizes
`implicitDeriv` (`toPolyG_cmonomialDeriv`), and `afReduce` is invisible mod `f` (`mk_toPolyG_afReduce`).
The implicit-function-theorem derivation `y' = −f_x/f_y` as an honest quotient identity; the source of
additivity and Leibniz. -/
theorem mk_toPolyG_afDeriv (fuel : ℕ) (f u : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f u))
      = Ideal.Quotient.mk (afIdeal f)
          (Differential.implicitDeriv (toPolyG (afYprime fuel f)) (toPolyG u)) := by
  rw [afDeriv_eq_afReduce_cmonomialDeriv, mk_toPolyG_afReduce f _ hf, toPolyG_cmonomialDeriv]

/-! ### Additivity: `afDeriv` commutes with `caddG` (the clean floor)

`afDeriv` realizes the Mathlib derivation `implicitDeriv (toPolyG yprime)` in the quotient
(`mk_toPolyG_afDeriv`); since `caddG` realizes `K[X]`-addition (`toPolyG_caddG`) and `implicitDeriv` is
ℤ-linear, additivity is immediate. (Even additivity is a quotient statement here, because `afDeriv`
applies `afReduce` — unlike the diagonal `radDeriv`, which was exact in `K[X]`.) -/

/-- **★ `afDeriv` is additive** — `mk (toPolyG (afDeriv fuel f (caddG a b))) = mk (toPolyG (afDeriv fuel f
a)) + mk (toPolyG (afDeriv fuel f b))` in the carrier `K[X] ⧸ (toPolyG f)`, for a nonzero curve `f`. From
the keystone `mk_toPolyG_afDeriv`, `caddG`-as-addition (`toPolyG_caddG`), and the additivity of the Mathlib
derivation `implicitDeriv`. The first derivation axiom — the clean floor. -/
theorem mk_toPolyG_afDeriv_add (fuel : ℕ) (f a b : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f (caddG a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f a))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f b)) := by
  rw [mk_toPolyG_afDeriv fuel f _ hf, mk_toPolyG_afDeriv fuel f a hf, mk_toPolyG_afDeriv fuel f b hf,
    toPolyG_caddG, map_add, map_add]

/-! ### The crux `D(toPolyG f) ∈ afIdeal f` and the descent of `D` to the quotient

`D := implicitDeriv (toPolyG yprime)` (the derivation realized by `afDeriv`, `mk_toPolyG_afDeriv`) is a
Mathlib `Derivation`; the algebraic extension is a genuine differential extension exactly when `D` maps the
curve ideal into itself. This rests on the general consistency relation `f_x + f_y·y' = 0` (which holds
because `afYprime = −f_x·f_y⁻¹` with `f_y⁻¹·f_y ≡ 1`, the Bézout cofactor `afFyInv`): then `D(toPolyG f) =
mapCoeffs(toPolyG f) + toPolyG yprime·derivative(toPolyG f) = toPolyG f_x + toPolyG yprime·toPolyG f_y ≡
toPolyG f_x − toPolyG f_x = 0 (mod toPolyG f)`. The non-degeneracy is the curve's **separability**:
`gcd(f, f_y)` a nonzero constant, the Bézout-solvability of `f_y⁻¹` (the hypotheses of
`toPolyG_cdiophantineG`). -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`f_y⁻¹ · f_y ≡ 1 mod f` (the Bézout cofactor)** — `mk (afIdeal f) (toPolyG (afFyInv fuel f) ·
toPolyG (afFy f)) = 1`, valid when the curve is **separable** (`gcd(afFy f, f)` a nonzero constant — the
Bézout-cofactor hypotheses `hg`/`hgc`, with `cnormG f ≠ []`). `afFyInv = (cdiophantineG fuel (afFy f) f
[1]).1` solves `s·f_y + t·f = 1` (`toPolyG_cdiophantineG`), so `s·f_y ≡ 1 (mod f)`. The field-inversion of
`f_y` that `afYprime = −f_x·f_y⁻¹` rests on. -/
theorem mk_toPolyG_afFyInv_mul_afFy (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (hg : toPolyG (cgcdExtG fuel (afFy f) f).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1)))
    (hgc : CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1) ≠ 0) :
    Ideal.Quotient.mk (afIdeal f)
        (toPolyG (afFyInv fuel f) * toPolyG (afFy f)) = 1 := by
  have hbez := toPolyG_cdiophantineG fuel (afFy f) f [CField.one] hf hg hgc
  -- `toPolyG [1] = 1`
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [hone] at hbez
  -- `afFyInv = (cdiophantineG …).1`, so `s·f_y + c·f = 1`; mod `f` the `c·f` term dies, leaving `s·f_y ≡ 1`
  rw [show toPolyG (afFyInv fuel f) * toPolyG (afFy f)
      = 1 - toPolyG (cdiophantineG fuel (afFy f) f [CField.one]).2 * toPolyG f from by
        rw [afFyInv]; linear_combination hbez]
  -- `mk (c·toPolyG f) = 0` since `c·toPolyG f ∈ afIdeal f`
  have hmem : Ideal.Quotient.mk (afIdeal f)
      (toPolyG (cdiophantineG fuel (afFy f) f [CField.one]).2 * toPolyG f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (mul_curve_mem f _)
  rw [map_sub, hmem, map_one, sub_zero]

/-- **★ The crux — the `afDeriv` derivation kills the curve generator modulo its ideal**: `D(toPolyG f) ∈
afIdeal f` where `D = implicitDeriv (toPolyG (afYprime fuel f))` is the derivation `afDeriv` realizes,
valid when the curve is **separable** (Bézout-solvable `f_y⁻¹`, `cnormG f ≠ []`). The general consistency
relation `f_x + f_y·y' = 0`: computing `D(toPolyG f) = mapCoeffs(toPolyG f) + toPolyG yprime · derivative
(toPolyG f) = toPolyG f_x + toPolyG yprime · toPolyG f_y`, then using `yprime ≡ −f_x·f_y⁻¹` and `f_y⁻¹·f_y
≡ 1` makes the image `≡ toPolyG f_x − toPolyG f_x = 0`. This is `D(f(x,y)) = f_x + f_y·y' = 0`, the
relation that makes `y' = −f_x/f_y` a *consistent* derivation on the curve `f = 0`. The general analogue of
`implicitDeriv_radicand_mem`. -/
theorem implicitDeriv_curve_mem (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (hg : toPolyG (cgcdExtG fuel (afFy f) f).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1)))
    (hgc : CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1) ≠ 0) :
    Differential.implicitDeriv (toPolyG (afYprime fuel f)) (toPolyG f) ∈ afIdeal f := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  -- `D q = mapCoeffs q + yprime · derivative q`
  rw [show Differential.implicitDeriv (toPolyG (afYprime fuel f)) (toPolyG f)
      = Differential.mapCoeffs (toPolyG f)
        + toPolyG (afYprime fuel f) * Polynomial.derivative (toPolyG f) from by
        simp [Differential.implicitDeriv, derivative']]
  rw [mapCoeffs_toPolyG_eq_afFx, derivative_toPolyG_eq_afFy]
  -- `yprime = afReduce f (−f_x · f_y⁻¹)`, so `mk yprime = mk (−f_x · f_y⁻¹)`
  have hyp : Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprime fuel f))
      = Ideal.Quotient.mk (afIdeal f) (- toPolyG (afFx f) * toPolyG (afFyInv fuel f)) := by
    rw [afYprime, mk_toPolyG_afReduce f _ hf, toPolyG_cmulG, toPolyG_cnegG]
  -- push `mk` through `f_x + yprime · f_y`, substitute `mk yprime`, and use `f_y⁻¹·f_y ≡ 1`
  rw [map_add, map_mul, hyp, ← map_mul]
  have hfyinv := mk_toPolyG_afFyInv_mul_afFy fuel f hf hg hgc
  rw [show - toPolyG (afFx f) * toPolyG (afFyInv fuel f) * toPolyG (afFy f)
      = - (toPolyG (afFx f) * (toPolyG (afFyInv fuel f) * toPolyG (afFy f))) from by ring,
    map_neg, map_mul, hfyinv, mul_one, add_neg_cancel]

/-- **The `afDeriv` derivation maps `afIdeal f` into itself** (separable curve): for any `x ∈ afIdeal f`,
`D x ∈ afIdeal f` with `D = implicitDeriv (toPolyG (afYprime fuel f))`. Since `afIdeal` is principal
(`x = c·toPolyG f`) and `D` is a derivation, `D x = Dc·toPolyG f + c·D(toPolyG f) ∈ afIdeal f` (both
summands, the second by the crux `implicitDeriv_curve_mem`). The descent of `D` to the quotient carrier;
the general analogue of `implicitDeriv_mem_radIdeal`. -/
theorem implicitDeriv_mem_afIdeal (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (hg : toPolyG (cgcdExtG fuel (afFy f) f).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1)))
    (hgc : CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1) ≠ 0)
    {x : (CFieldSpec.K α)[X]} (hx : x ∈ afIdeal f) :
    Differential.implicitDeriv (toPolyG (afYprime fuel f)) x ∈ afIdeal f := by
  rw [afIdeal, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  -- `D(c·g) = c·D g + g·D c`: first summand in `I` by the crux (`D g ∈ I`), second since `g ∈ I`
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · exact implicitDeriv_curve_mem fuel f hf hg hgc
  · exact Ideal.subset_span (Set.mem_singleton _)

/-- **`D` descends to the quotient**: if `mk (afIdeal f) p = mk (afIdeal f) q`, then `mk (D p) = mk (D q)`
(with `D = implicitDeriv (toPolyG (afYprime fuel f))`), for a separable curve `f`. The two arguments differ
by an element of `afIdeal f`, which `D` keeps in `afIdeal f` (`implicitDeriv_mem_afIdeal`); the derivation
is ℤ-linear so the difference of images is `D(p − q) ∈ afIdeal f`. The general analogue of
`mk_implicitDeriv_congr`. -/
theorem mk_implicitDeriv_congr (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ [])
    (hg : toPolyG (cgcdExtG fuel (afFy f) f).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1)))
    (hgc : CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1) ≠ 0)
    {p q : (CFieldSpec.K α)[X]}
    (hpq : Ideal.Quotient.mk (afIdeal f) p = Ideal.Quotient.mk (afIdeal f) q) :
    Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprime fuel f)) p)
      = Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprime fuel f)) q) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply implicitDeriv_mem_afIdeal fuel f hf hg hgc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpq, sub_self]

/-! ### ★ The Leibniz law for `afDeriv`, modulo the curve ideal

All pieces assemble: `afDeriv` realizes the derivation `D = implicitDeriv (toPolyG yprime)`
(`mk_toPolyG_afDeriv`); `afMul ≡ ·` modulo `afIdeal f` (`mk_toPolyG_afMul`); `D` is a Mathlib derivation
(so free-polynomial Leibniz) that descends to `K[X] ⧸ (toPolyG f)` (`mk_implicitDeriv_congr`). The product
rule for `afMul` therefore holds in the carrier — the general analogue of `mk_toPolyG_radDeriv_radMul`. -/

/-- **★ `afDeriv` is Leibniz (modulo the curve ideal)** — the product rule in the carrier `K[X] ⧸ (toPolyG
f)`: `mk (toPolyG (afDeriv fuel f (afMul f a b))) = mk (toPolyG (afMul f (afDeriv fuel f a) b)) + mk
(toPolyG (afMul f a (afDeriv fuel f b)))`, valid when the curve `f` is **separable** (`gcd(afFy f, f)` a
nonzero constant — the Bézout-cofactor hypotheses, with `cnormG f ≠ []`). Assembled from the keystone
`mk_toPolyG_afDeriv`, `afMul`-as-product `mk_toPolyG_afMul`, the descent `mk_implicitDeriv_congr`, and the
free-polynomial Leibniz of the Mathlib derivation `implicitDeriv`. The product-rule derivation axiom for
the general algebraic-function carrier. -/
theorem mk_toPolyG_afDeriv_afMul (fuel : ℕ) (f a b : CPolyG α) (hf : cnormG f ≠ [])
    (hg : toPolyG (cgcdExtG fuel (afFy f) f).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1)))
    (hgc : CFieldSpec.toK (cleadG (cgcdExtG fuel (afFy f) f).1) ≠ 0) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f (afMul f a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f (afDeriv fuel f a) b))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f a (afDeriv fuel f b))) := by
  -- abbreviations
  set yp := toPolyG (afYprime fuel f) with hyp
  set A := toPolyG a with hA
  set B := toPolyG b with hB
  -- LHS: afDeriv realizes `D`, then `afMul ≡ A·B`, then `D` descends
  rw [mk_toPolyG_afDeriv fuel f _ hf, ← hyp]
  rw [mk_implicitDeriv_congr fuel f hf hg hgc (mk_toPolyG_afMul f a b hf)]
  -- RHS: each `afMul` is a product; each inner `afDeriv` realizes `D`
  rw [mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afDeriv fuel f a hf,
    mk_toPolyG_afDeriv fuel f b hf, ← hyp, ← hA, ← hB]
  -- free-polynomial Leibniz of `D` (a Mathlib derivation), pushed through `mk`
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  ring

/-! ### The remaining derivation axioms: `afDeriv` kills constants

`afDeriv` annihilates `1` (and the base constants), exactly as a derivation must. Immediate from the
keystone `mk_toPolyG_afDeriv` and `map_one_eq_zero` of the Mathlib derivation `implicitDeriv`. -/

/-- **`afDeriv` kills `1`** — `mk (toPolyG (afDeriv fuel f [1])) = 0` in the carrier `K[X] ⧸ (toPolyG f)`
(`toPolyG [1] = 1`, and `implicitDeriv v 1 = 0`: a derivation annihilates the unit), for a nonzero curve
`f`. The general analogue of `toPolyG_radDeriv_radOne` (validated by `native_decide` as
`gcuspCubic_deriv_one_eq_zero`). -/
theorem mk_toPolyG_afDeriv_one (fuel : ℕ) (f : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDeriv fuel f [CField.one])) = 0 := by
  rw [mk_toPolyG_afDeriv fuel f _ hf]
  have h1 : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [h1, Derivation.map_one_eq_zero, map_zero]

end CPolyG

/-! ### `#print axioms` — the general derivation invariant is axiom-clean

The keystone, additivity, the crux, and Leibniz carry **only** the standard `[propext, Classical.choice,
Quot.sound]` — no `native_decide` compiler axiom, no `sorry`. `afDeriv` is a genuine derivation (additive +
Leibniz) on the GENERAL carrier `K(x)[y]/(f)` for an arbitrary separable monic curve `f`, as a general
theorem — not a `native_decide`-validated example. The `afDeriv = implicitDeriv` keystone carries over
verbatim from the radical template `ComputableRadicalDerivationInvariant`; only the implicit rule changes
(`−f_x/f_y` for the diagonal `ℓ·y`). -/

-- The keystone (afDeriv realizes Mathlib's implicitDeriv mod f) and additivity:
#print axioms CPolyG.mk_toPolyG_afDeriv
#print axioms CPolyG.mk_toPolyG_afDeriv_add

-- The crux (afDeriv kills the curve generator mod its ideal) and Leibniz in the carrier:
#print axioms CPolyG.implicitDeriv_curve_mem
#print axioms CPolyG.mk_toPolyG_afDeriv_afMul

end DeepWiki.SymbolicIntegration
