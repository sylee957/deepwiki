import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.ResidueMultiplicity

/-! # Recognizing logarithmic derivatives (Bronstein §2.9)
For `f = A/D ∈ K(x)` with `D` squarefree, `deg A < deg D`, the criterion of §2.9 (Mařík): `f` is the
logarithmic derivative of a rational function — `∃ u ∈ K(x)*, f = logDeriv u` — **iff** all the residues
`A(α)/D'(α)` (the roots of the Rothstein–Trager resultant, by `roots_rtResultant`) are integers (lie in
the image of `ℤ → K`). Both directions are proved (packaged as `isLogDeriv_iff_integer_residues`).
`⟸` (`isLogDeriv_of_integer_residues`): grouping the simple-root residue decomposition
`ratFunc_eq_sum_residue_grouped` by residue value, each integer residue `nₐ` turns the grouped factor
`Gₐ = ∏_{res α = a}(X−α)` into a power `Gₐ^{nₐ}`, so `A/D = logDeriv(∏ₐ Gₐ^{nₐ})`.
`⟹` (`integer_residues_of_isLogDeriv`): the simple-pole residue functional `residueAt α f = ((X−α)·f)(α)`
reads `A(α)/D'(α)` from `A/D` (simple root) and the integer `ord_α(num u) − ord_α(denom u)` from
`logDeriv u`; the hypothesis `A/D = logDeriv u` equates them. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
open scoped Differential in
/-- The constant residue `C a` as a rational function equals the integer scalar `(n : K(x))` when
`a = (n : K)`: `algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K)`. -/
theorem algebraMap_C_intCast (n : ℤ) :
    algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K) := by
  rw [show (C (n : K)) = ((n : K[X])) from by simp, map_intCast]

open scoped Classical in
open scoped Differential in
/-- The explicit logarithmic-derivative witness `u = ∏ₐ Gₐ^{nₐ}` for the §2.9 criterion: the product,
over the distinct residue values `a` of `A/D`, of the Rothstein–Trager factor
`Ḡₐ = algebraMap(∏_{res α = a}(X − α))` raised to the integer `nₐ` chosen for that residue. Nonzero
(a `zpow`-product of nonzero polynomials), it satisfies `A/D = logDeriv u` (`logDeriv_intResidues_witness`). -/
noncomputable def intResiduesWitness (s : Finset K) (A : K[X]) (n : K → ℤ) : RatFunc K :=
  ∏ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
    (algebraMap K[X] (RatFunc K)
        (∏ α ∈ s.filter (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
          (X - C α))) ^ n a

open scoped Classical in
/-- The witness `intResiduesWitness s A n` is nonzero — a `zpow`-product of nonzero `Ḡₐ`. -/
theorem intResiduesWitness_ne_zero (s : Finset K) (A : K[X]) (n : K → ℤ) :
    intResiduesWitness s A n ≠ 0 := by
  rw [intResiduesWitness]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ ?_
  refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr ?_
  exact Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, `⟸` direction** (Bronstein §2.9, p.72): if every residue
`a = A(α)/D'(α)` of `A/D` is an integer in `K` (witnessed by `n a : ℤ` with `(n a : K) = a`), then
`A/D = logDeriv u` with `u = ∏ₐ Gₐ^{nₐ}` the explicit `intResiduesWitness`. Grouping
`ratFunc_eq_sum_residue_grouped` by residue value, each term `C a · logDeriv(Ḡₐ)` becomes
`(nₐ : K(x)) · logDeriv(Ḡₐ) = logDeriv(Ḡₐ^{nₐ})`; summing is `logDeriv(∏ₐ Ḡₐ^{nₐ})` by
`logDeriv_prod_zpow`. (For `D = ∏_{α∈s}(X−α)` squarefree with roots `s`, `deg A < #s`.) -/
theorem logDeriv_intResiduesWitness (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (n : K → ℤ)
    (hn : ∀ α ∈ s, ((n (A.eval α / eval α (derivative (Lagrange.nodal s id))) : K))
      = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = Differential.logDeriv (intResiduesWitness s A n) := by
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  -- nonzero of each grouped factor `Ḡₐ`
  have hGne : ∀ a ∈ s.image res, algebraMap K[X] (RatFunc K)
      (∏ α ∈ s.filter (fun α => res α = a), (X - C α)) ≠ 0 := fun a _ =>
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α)
  -- residue values in the image are integers
  have hint : ∀ a ∈ s.image res, ((n a : K)) = a := by
    intro a ha
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ha
    exact hn α hα
  rw [ratFunc_eq_sum_residue_grouped s A hA, intResiduesWitness, ← hres,
    logDeriv_prod_zpow _ _ _ hGne]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  rw [← algebraMap_C_intCast (n a), hint a ha]

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, `⟸`** (Bronstein §2.9, p.72), existential form: if every
residue `A(α)/D'(α)` of `A/D` is an integer in `K`, then `A/D` is the logarithmic derivative of a
*nonzero* rational function — `∃ u ≠ 0, A/D = logDeriv u`. The witness is `intResiduesWitness`. -/
theorem isLogDeriv_of_integer_residues (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (hint : ∀ α ∈ s, ∃ m : ℤ, ((m : K)) = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    ∃ u : RatFunc K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        = Differential.logDeriv u := by
  classical
  -- choose an integer exponent for each residue value
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  have hex : ∀ a : K, (∃ α ∈ s, res α = a) → ∃ m : ℤ, ((m : K)) = a := by
    rintro a ⟨α, hα, rfl⟩; exact hint α hα
  let n : K → ℤ := fun a => if h : ∃ α ∈ s, res α = a then (hex a h).choose else 0
  have hn : ∀ α ∈ s, ((n (res α) : K)) = res α := by
    intro α hα
    have h : ∃ β ∈ s, res β = res α := ⟨α, hα, rfl⟩
    simp only [n, dif_pos h]
    exact (hex (res α) h).choose_spec
  refine ⟨intResiduesWitness s A n, intResiduesWitness_ne_zero s A n,
    logDeriv_intResiduesWitness s A hA n hn⟩

open scoped Classical in
open scoped Differential in
-- The `⟸` direction: integer residues give a logarithmic-derivative witness for `A/D`.
example (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (hint : ∀ α ∈ s, ∃ m : ℤ, ((m : K)) = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    ∃ u : RatFunc K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        = Differential.logDeriv u :=
  isLogDeriv_of_integer_residues s A hA hint

/-! ## Numerator log-derivative as a sum over roots (toward the `⟹` direction) -/

open scoped Classical in
open scoped Differential in
/-- **Log-derivative of a polynomial as a root sum** (Bronstein §2.9, the `⟹`-direction ingredient):
over an algebraically closed field, for nonzero `N : K[X]`, the rational-function logarithmic derivative
`logDeriv(N) = ∑_{β ∈ N.roots} logDeriv(X − β) = ∑_β 1/(X − β)` — the sum over the roots of `N` with
multiplicity (each `(X−β)^{m}` contributing `m` copies). From `N = lc(N)·∏_β(X−β)` (`Splits.eq_prod_roots`,
`N` splits over `K̄`) and `logDeriv_multisetProd`; the leading constant drops (`logDeriv` kills constants).
This is `N′/N = ∑ m_β/(X−β)`, whose residue at a simple pole `α` is the root multiplicity `m_α ∈ ℤ`. -/
theorem logDeriv_algebraMap_eq_sum_roots [IsAlgClosed K] (N : K[X]) (hN : N ≠ 0) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
      = (N.roots.map (fun β => Differential.logDeriv
          (algebraMap K[X] (RatFunc K) (X - C β)))).sum := by
  have hsplit : N.Splits := IsAlgClosed.splits N
  have hlc : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hN
  -- the constant `C lc` has zero log-derivative
  have hCconst : Differential.logDeriv (algebraMap K[X] (RatFunc K) (C N.leadingCoeff)) = 0 := by
    rw [Differential.logDeriv_eq_zero,
      show (algebraMap K[X] (RatFunc K) (C N.leadingCoeff))′
        = ratFuncDeriv _ from rfl, ratFuncDeriv_algebraMap, derivative_C, map_zero]
  -- nonzero of the constant and the product factors
  have hCne : algebraMap K[X] (RatFunc K) (C N.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hlc)
  have hProd : ((N.roots.map (X - C ·)).prod : K[X]) ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    simp only [Multiset.mem_map, not_exists]
    exact fun β => fun ⟨_, h⟩ => X_sub_C_ne_zero β h
  have hPne : algebraMap K[X] (RatFunc K) ((N.roots.map (X - C ·)).prod) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hProd
  -- `N = C lc · ∏_β (X − β)`, push through `algebraMap` on the LHS only
  conv_lhs => rw [hsplit.eq_prod_roots]
  rw [map_mul, Differential.logDeriv_mul _ _ hCne hPne, hCconst, zero_add, map_multiset_prod,
    Multiset.map_map, Differential.logDeriv_multisetProd]
  · exact congrArg Multiset.sum (Multiset.map_congr rfl fun β _ => rfl)
  · exact fun x _ => (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero x)

open scoped Classical in
open scoped Differential in
-- `logDeriv(N) = ∑_{β ∈ N.roots} logDeriv(X−β)`: the numerator log-derivative is the root sum.
example [IsAlgClosed K] (N : K[X]) (hN : N ≠ 0) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
      = (N.roots.map (fun β => Differential.logDeriv
          (algebraMap K[X] (RatFunc K) (X - C β)))).sum :=
  logDeriv_algebraMap_eq_sum_roots N hN

/-! ## The simple-pole residue functional (toward the `⟹` direction)
The residue of `f ∈ K(x)` at a *simple* pole `α` is extracted by multiplying by `X − α` (which
cancels the pole) and evaluating at `α`: `residueAt α f = ((X − α)·f)(α)`. Both `A/D` (with `D`
squarefree) and `logDeriv u` have only simple poles, so this functional reads off both residues. -/

/-- A divisor of a polynomial nonzero at `α` is itself nonzero at `α` — `g ∣ h`, `h(α) ≠ 0 ⟹ g(α) ≠ 0`. -/
theorem eval_ne_zero_of_dvd {α : K} {g h : K[X]} (hdvd : g ∣ h) (hh : h.eval α ≠ 0) :
    g.eval α ≠ 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [eval_mul] at hh
  exact left_ne_zero_of_mul hh

/-- **Evaluation of a pole-free quotient**: when `h(α) ≠ 0`, the rational function `g/h ∈ K(x)`
evaluates at `α` to the field quotient `g(α)/h(α)` — `RatFunc.eval` clears the (reduced) denominator,
which divides `h` (`denom_div_dvd`) and so is also nonzero at `α`, letting the cross-multiplication
`num·h = g·denom` evaluate to `g(α)/h(α)`. -/
theorem eval_algebraMap_div (α : K) (g h : K[X]) (hh : h.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h)
      = g.eval α / h.eval α := by
  set x : RatFunc K := algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h with hx
  have hh0 : h ≠ 0 := fun h0 => hh (by rw [h0, eval_zero])
  have hdenom : (RatFunc.denom x).eval α ≠ 0 :=
    eval_ne_zero_of_dvd (RatFunc.denom_div_dvd g h) hh
  -- cross-multiplication `num x · h = g · denom x`, from `num x / denom x = g / h`
  have hcross : RatFunc.num x * h = g * RatFunc.denom x := by
    have hd := RatFunc.denom_ne_zero x
    have heq : algebraMap K[X] (RatFunc K) (RatFunc.num x)
          / algebraMap K[X] (RatFunc K) (RatFunc.denom x)
        = algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h :=
      (RatFunc.num_div_denom x).trans hx
    rw [div_eq_div_iff
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hd)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hh0),
      ← map_mul, ← map_mul] at heq
    exact RatFunc.algebraMap_injective K heq
  have heval : (RatFunc.num x).eval α * h.eval α = g.eval α * (RatFunc.denom x).eval α := by
    simpa only [eval_mul] using congrArg (Polynomial.eval α) hcross
  rw [RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id, div_eq_div_iff hdenom hh]
  exact heval

/-- **The simple-pole residue functional** `residueAt α f = ((X − α)·f)(α)`: multiply `f ∈ K(x)` by
`X − α` to cancel a simple pole at `α`, then evaluate at `α`. For `f` with at most a simple pole at
`α`, this is the residue (the coefficient of `1/(X − α)` in the partial fraction of `f`). -/
noncomputable def residueAt (α : K) (f : RatFunc K) : K :=
  RatFunc.eval (RingHom.id K) α (algebraMap K[X] (RatFunc K) (X - C α) * f)

open scoped Classical in
/-- **Residue from a pole-free reduced form**: if `(X − α)·f = g/h` in `K(x)` with `h(α) ≠ 0`, then
`residueAt α f = g(α)/h(α)`. The intro/elim API for `residueAt`: a residue computation reduces to
exhibiting the once-multiplied function as a quotient regular at `α`. -/
theorem residueAt_of_mul_X_sub_C (α : K) (f : RatFunc K) (g h : K[X]) (hh : h.eval α ≠ 0)
    (heq : algebraMap K[X] (RatFunc K) (X - C α) * f
      = algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h) :
    residueAt α f = g.eval α / h.eval α := by
  rw [residueAt, heq, eval_algebraMap_div α g h hh]

open scoped Classical in
/-- **Residue of `A/D` at a simple root** (computation 1, Bronstein §2.9): for `D = (X − α)·E` with
`E(α) ≠ 0` (so `α` is a simple root and `D'(α) = E(α)`), the residue of `A/D` at `α` is
`A(α)/E(α) = A(α)/D'(α)`. Multiplying `A/D` by `X − α` cancels the simple pole to `A/E`, which is
pole-free at `α`. -/
theorem residueAt_div_eq_residue (A E : K[X]) (α : K) (hE : E.eval α ≠ 0) :
    residueAt α (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) ((X - C α) * E))
      = A.eval α / (derivative ((X - C α) * E)).eval α := by
  rw [residue_eq_eval_div_eval_derivative]
  refine residueAt_of_mul_X_sub_C α _ A E hE ?_
  have hXne : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hEne : algebraMap K[X] (RatFunc K) E ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hE (by rw [h0, eval_zero]))
  rw [map_mul]
  field_simp

/-- **Factorization of `(X − α)·N'` along the root multiplicity** (computation 2, the polynomial core):
for `N = (X − α)^k · N₁`, `(X − α)·N' = (X − α)^k · (k·N₁ + (X − α)·N₁')` — the `(X − α)^k` common factor
that cancels against `N` in `(X − α)·(N'/N)`, leaving the regular-at-`α` quotient
`(k·N₁ + (X − α)·N₁')/N₁`. -/
theorem mul_X_sub_C_derivative_pow_mul (α : K) (k : ℕ) (N₁ : K[X]) :
    (X - C α) * derivative ((X - C α) ^ k * N₁)
      = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
  rw [derivative_mul, derivative_pow, derivative_X_sub_C, mul_one]
  cases k with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel]; ring

open scoped Differential in
/-- `logDeriv` of a polynomial in `K(x)` is `N'/N`: `logDeriv(algebraMap N) = algebraMap(N')/algebraMap(N)`.
-/
theorem logDeriv_algebraMap_eq (N : K[X]) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
      = algebraMap K[X] (RatFunc K) (derivative N) / algebraMap K[X] (RatFunc K) N := by
  rw [Differential.logDeriv,
    show (algebraMap K[X] (RatFunc K) N)′ = ratFuncDeriv _ from rfl, ratFuncDeriv_algebraMap]

open scoped Classical in
open scoped Differential in
/-- **Residue of `logDeriv N` at `α` is the root multiplicity** (computation 2, Bronstein §2.9): for
nonzero `N : K[X]`, the residue at `α` of the logarithmic derivative `N'/N` is the multiplicity of `α`
as a root of `N` — `residueAt α (logDeriv N) = (rootMultiplicity α N : K)`. Writing `N = (X − α)^k·N₁`
with `N₁(α) ≠ 0` (`k = rootMultiplicity α N`), `(X − α)·(N'/N) = (k·N₁ + (X − α)·N₁')/N₁`, regular at
`α` and evaluating there to `(k·N₁(α) + 0)/N₁(α) = k`. -/
theorem residueAt_logDeriv_eq_rootMultiplicity (N : K[X]) (hN : N ≠ 0) (α : K) :
    residueAt α (Differential.logDeriv (algebraMap K[X] (RatFunc K) N))
      = (N.rootMultiplicity α : K) := by
  set k := N.rootMultiplicity α with hk
  obtain ⟨N₁, hNeq, hndvd⟩ := N.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hN α
  rw [← hk] at hNeq
  -- `N₁(α) ≠ 0` from `¬(X − α) ∣ N₁`
  have hN₁ : N₁.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  have hN₁0 : N₁ ≠ 0 := fun h0 => hN₁ (by rw [h0, eval_zero])
  rw [logDeriv_algebraMap_eq]
  -- reduce to the regular quotient `(k·N₁ + (X−α)·N₁')/N₁`
  refine (residueAt_of_mul_X_sub_C α _ (C (k : K) * N₁ + (X - C α) * derivative N₁) N₁ hN₁ ?_).trans ?_
  · -- the RatFunc identity, from the polynomial factorization, canceling `(X−α)^k`
    have hpoly : (X - C α) * derivative N
        = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
      rw [hNeq]; exact mul_X_sub_C_derivative_pow_mul α k N₁
    have hN₁ne : algebraMap K[X] (RatFunc K) N₁ ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN₁0
    have hNne : algebraMap K[X] (RatFunc K) N ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN
    have hpkne : algebraMap K[X] (RatFunc K) ((X - C α) ^ k) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (pow_ne_zero _ (X_sub_C_ne_zero α))
    rw [← mul_div_assoc, ← map_mul, hpoly, hNeq]
    simp only [map_mul]
    rw [mul_div_mul_left (G₀ := RatFunc K) _ _ hpkne]
  · -- evaluate `(k·N₁ + (X−α)·N₁')/N₁` at `α`: numerator `= k·N₁(α)`, ratio `= k`
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
    rw [mul_div_assoc, div_self hN₁, mul_one]

open scoped Classical in
/-- **Additivity of the residue at a simple pole**: if `(X − α)·f = a/b` and `(X − α)·g = c/d` are both
pole-free at `α` (`b(α), d(α) ≠ 0`), then `residueAt α (f − g) = residueAt α f − residueAt α g`. The
once-multiplied difference `(X − α)·(f − g) = (a·d − c·b)/(b·d)` is again pole-free at `α`. -/
theorem residueAt_sub_of_witnesses (α : K) (f g : RatFunc K) (a b c d : K[X])
    (hb : b.eval α ≠ 0) (hd : d.eval α ≠ 0)
    (hf : algebraMap K[X] (RatFunc K) (X - C α) * f
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
    (hg : algebraMap K[X] (RatFunc K) (X - C α) * g
      = algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) d) :
    residueAt α (f - g) = a.eval α / b.eval α - c.eval α / d.eval α := by
  have hbne : algebraMap K[X] (RatFunc K) b ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hb (by rw [h0, eval_zero]))
  have hdne : algebraMap K[X] (RatFunc K) d ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hd (by rw [h0, eval_zero]))
  have hbd : (b * d).eval α ≠ 0 := by rw [eval_mul]; exact mul_ne_zero hb hd
  rw [residueAt_of_mul_X_sub_C α (f - g) (a * d - c * b) (b * d) hbd ?_]
  · rw [eval_sub, eval_mul, eval_mul, eval_mul, div_sub_div _ _ hb hd]
    ring_nf
  · rw [mul_sub, hf, hg, map_sub, map_mul, map_mul, map_mul, div_sub_div _ _ hbne hdne,
      mul_comm (algebraMap K[X] (RatFunc K) c)]

open scoped Classical in
open scoped Differential in
/-- **Pole-free witness for `(X − α)·logDeriv N`** (computation 2, the reduced quotient): for nonzero
`N = (X − α)^k·N₁` (`k = rootMultiplicity α N`, `N₁(α) ≠ 0`), the once-multiplied logarithmic derivative
is the quotient `(k·N₁ + (X − α)·N₁')/N₁`, regular at `α`. Exposing the witness (the `(X − α)^k`
cancellation from `residueAt_logDeriv_eq_rootMultiplicity`) lets `residueAt_sub_of_witnesses` combine
two logarithmic derivatives. -/
theorem mul_X_sub_C_logDeriv_reduced (N : K[X]) (hN : N ≠ 0) (α : K) :
    ∃ N₁ : K[X], N₁.eval α ≠ 0 ∧
      algebraMap K[X] (RatFunc K) (X - C α)
          * Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
        = algebraMap K[X] (RatFunc K) (C (N.rootMultiplicity α : K) * N₁ + (X - C α) * derivative N₁)
          / algebraMap K[X] (RatFunc K) N₁ := by
  set k := N.rootMultiplicity α with hk
  obtain ⟨N₁, hNeq, hndvd⟩ := N.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hN α
  rw [← hk] at hNeq
  have hN₁ : N₁.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  refine ⟨N₁, hN₁, ?_⟩
  have hN₁0 : N₁ ≠ 0 := fun h0 => hN₁ (by rw [h0, eval_zero])
  have hpoly : (X - C α) * derivative N
      = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
    rw [hNeq]; exact mul_X_sub_C_derivative_pow_mul α k N₁
  have hpkne : algebraMap K[X] (RatFunc K) ((X - C α) ^ k) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (pow_ne_zero _ (X_sub_C_ne_zero α))
  rw [logDeriv_algebraMap_eq, ← mul_div_assoc, ← map_mul, hpoly, hNeq]
  simp only [map_mul]
  rw [mul_div_mul_left (G₀ := RatFunc K) _ _ hpkne]

open scoped Classical in
open scoped Differential in
/-- **Residue of `logDeriv (N/M)` is an integer** (computation 2, the difference form, Bronstein §2.9):
for nonzero `N, M : K[X]`, the residue at `α` of `logDeriv(N/M) = N'/N − M'/M` is the integer
`rootMultiplicity α N − rootMultiplicity α M`. The two simple-pole residues
(`residueAt_logDeriv_eq_rootMultiplicity`) subtract through `residueAt_sub_of_witnesses`. -/
theorem residueAt_logDeriv_div_eq_int (N M : K[X]) (hN : N ≠ 0) (hM : M ≠ 0) (α : K) :
    residueAt α (Differential.logDeriv (algebraMap K[X] (RatFunc K) N
        / algebraMap K[X] (RatFunc K) M))
      = ((N.rootMultiplicity α : ℤ) - (M.rootMultiplicity α : ℤ) : K) := by
  obtain ⟨N₁, hN₁, hNwit⟩ := mul_X_sub_C_logDeriv_reduced N hN α
  obtain ⟨M₁, hM₁, hMwit⟩ := mul_X_sub_C_logDeriv_reduced M hM α
  have hdiv : Differential.logDeriv (algebraMap K[X] (RatFunc K) N
        / algebraMap K[X] (RatFunc K) M)
      = Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
        - Differential.logDeriv (algebraMap K[X] (RatFunc K) M) :=
    Differential.logDeriv_div _ _
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hM)
  rw [hdiv, residueAt_sub_of_witnesses α _ _ _ N₁ _ M₁ hN₁ hM₁ hNwit hMwit]
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
  rw [mul_div_assoc, div_self hN₁, mul_one, mul_div_assoc, div_self hM₁, mul_one]
  push_cast
  ring

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, `⟹` direction** (Bronstein §2.9, p.72, Mařík): over an
algebraically closed field, if `A/D` (with `D` squarefree, `deg A < deg D`) is the logarithmic
derivative of some nonzero `u ∈ K(x)*`, then at every root `α` of `D` the residue `A(α)/D'(α)` is an
*integer* in `K` — `∃ n : ℤ, A(α)/D'(α) = (n : K)`, namely `n = ord_α(num u) − ord_α(denom u)`. Proof:
the residue functional `residueAt α` reads `A(α)/D'(α)` from `A/D` (`residueAt_div_eq_residue`, `D`
having `α` as a simple root) and `ord_α(num u) − ord_α(denom u)` from `logDeriv u`
(`residueAt_logDeriv_div_eq_int`); the hypothesis `A/D = logDeriv u` equates them. -/
theorem integer_residues_of_isLogDeriv [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (u : RatFunc K) (hu : u ≠ 0)
    (hlog : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
      = Differential.logDeriv u) (α : K) (hα : D.IsRoot α) :
    ∃ n : ℤ, A.eval α / (derivative D).eval α = (n : K) := by
  -- `D = (X − α)·E` with `E(α) ≠ 0` (`α` a simple root of squarefree `D`)
  have hD0 : D ≠ 0 := hD.ne_zero
  have hmult : D.rootMultiplicity α = 1 :=
    le_antisymm (rootMultiplicity_le_one_of_separable hD α)
      ((rootMultiplicity_pos hD0).mpr hα)
  obtain ⟨E, hDeq, hndvd⟩ := D.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hD0 α
  rw [hmult, pow_one] at hDeq
  have hE : E.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  -- write `u = num u / denom u` (both nonzero)
  have hNu : RatFunc.num u ≠ 0 := RatFunc.num_ne_zero hu
  have hMu : RatFunc.denom u ≠ 0 := RatFunc.denom_ne_zero u
  refine ⟨(RatFunc.num u).rootMultiplicity α - (RatFunc.denom u).rootMultiplicity α, ?_⟩
  -- the residue read two ways via the hypothesis `A/D = logDeriv u`
  have hres1 : residueAt α (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D)
      = A.eval α / (derivative D).eval α := by
    rw [hDeq]; exact residueAt_div_eq_residue A E α hE
  have hres2 : residueAt α (Differential.logDeriv u)
      = (((RatFunc.num u).rootMultiplicity α : ℤ)
          - ((RatFunc.denom u).rootMultiplicity α : ℤ) : K) := by
    conv_lhs => rw [← RatFunc.num_div_denom u]
    exact residueAt_logDeriv_div_eq_int (RatFunc.num u) (RatFunc.denom u) hNu hMu α
  rw [← hres1, hlog, hres2]
  push_cast
  ring

open scoped Classical in
open scoped Differential in
-- The `⟹` direction: a logarithmic-derivative `A/D` has integer residues at the roots of `D`.
example [IsAlgClosed K] (A D : K[X]) (hD : D.Separable) (u : RatFunc K) (hu : u ≠ 0)
    (hlog : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
      = Differential.logDeriv u) (α : K) (hα : D.IsRoot α) :
    ∃ n : ℤ, A.eval α / (derivative D).eval α = (n : K) :=
  integer_residues_of_isLogDeriv A D hD u hu hlog α hα

/-- `nodal s id = ∏_{α∈s}(X − α)` is separable: a product of distinct linear factors. -/
theorem separable_nodal (s : Finset K) : (Lagrange.nodal s id).Separable := by
  rw [Lagrange.nodal_eq]
  exact separable_prod_X_sub_C_iff'.mpr (fun x _ y _ h => h)

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, the criterion** (Bronstein §2.9, p.72, Mařík — both
directions): over an algebraically closed field, for squarefree `D = ∏_{α∈s}(X − α)` (`s` the distinct
roots) and `deg A < #s`, the proper fraction `A/D` is the logarithmic derivative of some nonzero
`u ∈ K(x)*` **iff** every residue `A(α)/D'(α)` (`α ∈ s`) is an integer in `K`. The `⟹` is
`integer_residues_of_isLogDeriv` (specialized to `D = nodal s id`, whose roots are `s` and which is
separable by `separable_nodal`); the `⟸` is `isLogDeriv_of_integer_residues` (the explicit
`∏ₐ Gₐ^{nₐ}` witness). -/
theorem isLogDeriv_iff_integer_residues [IsAlgClosed K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    (∃ u : RatFunc K, u ≠ 0 ∧
        algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
          = Differential.logDeriv u)
      ↔ (∀ α ∈ s, ∃ n : ℤ,
          A.eval α / eval α (derivative (Lagrange.nodal s id)) = (n : K)) := by
  constructor
  · rintro ⟨u, hu, hlog⟩ α hα
    refine integer_residues_of_isLogDeriv A (Lagrange.nodal s id) (separable_nodal s) u hu hlog α ?_
    exact Lagrange.eval_nodal_at_node (v := id) hα
  · intro hint
    obtain ⟨u, hu, hlog⟩ := isLogDeriv_of_integer_residues s A hA
      (fun α hα => (hint α hα).imp fun _ h => h.symm)
    exact ⟨u, hu, hlog⟩

open scoped Classical in
open scoped Differential in
-- The packaged criterion: `A/D = logDeriv u` (some `u ≠ 0`) ↔ all residues `A(α)/D'(α)` are integers.
example [IsAlgClosed K] (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    (∃ u : RatFunc K, u ≠ 0 ∧
        algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
          = Differential.logDeriv u)
      ↔ (∀ α ∈ s, ∃ n : ℤ,
          A.eval α / eval α (derivative (Lagrange.nodal s id)) = (n : K)) :=
  isLogDeriv_iff_integer_residues s A hA

end DeepWiki.SymbolicIntegration
