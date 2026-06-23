import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # A minimal polynomial-time many-one (Karp) reduction framework
This file builds the *minimal but faithful* Karp-reduction algebra needed to state
NP-hardness of decision problems (used for DNC Theorem 10.2). A Karp reduction from a
decision problem `P : σ → Prop` to `Q : τ → Prop` is a map `f : σ → τ` that is

* **correct** as a many-one reduction — `∀ x, P x ↔ Q (f x)` (the bi-implication that
  Mathlib's `ManyOneReducible` also requires), and
* **polynomial-time** computable.

**Honest cost model.** A faithful Turing-machine time-cost model is out of scope (Mathlib
does not provide one). We model poly-time by a *polynomial size bound*: a `size : · → ℕ`
encoding-size function and a `Polynomial ℕ` with `∀ x, size (f x) ≤ poly.eval (size x)`.
This is a **structural proxy**, not a TM cost model: it bounds the *output size* of the
reduction by a polynomial in the *input size*. For the simple structural reductions used
here (the output is built from the input by a fixed local rule) this size bound is the
checkable witness that the map is poly-time; we make the proxy explicit rather than fake a
machine model. The size function is a *parameter* of the reduction (any encoding size),
so the algebra below is generic over the chosen `size`.

The algebra: `KarpReduction` is reflexive (`KarpReduction.id`) and transitive
(`KarpReduction.comp`) — composing reductions composes their polynomials and correctness.
-/

namespace DeepWiki

open Polynomial

/-! ## Monotonicity of `ℕ`-polynomial evaluation
The size-bound composition needs that a `Polynomial ℕ` is monotone in its argument: with
all coefficients in `ℕ` (nonneg), `a ≤ b → p.eval a ≤ p.eval b`. -/

/-- A `Polynomial ℕ` evaluates monotonically: nonneg `ℕ` coefficients make `eval` monotone
(`a ≤ b → p.eval a ≤ p.eval b`). -/
theorem Polynomial.eval_le_eval_of_le_nat {p : Polynomial ℕ} {a b : ℕ} (hab : a ≤ b) :
    p.eval a ≤ p.eval b := by
  classical
  rw [Polynomial.eval_eq_sum_range (p := p) a, Polynomial.eval_eq_sum_range (p := p) b]
  exact Finset.sum_le_sum fun i _ =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

/-- `Polynomial.eval · p` is monotone over `ℕ` (the monotone-function packaging of
`eval_le_eval_of_le_nat`). -/
theorem Polynomial.eval_mono_nat (p : Polynomial ℕ) : Monotone (p.eval ·) :=
  fun _ _ hab => Polynomial.eval_le_eval_of_le_nat hab

/-! ## The Karp reduction structure
A polynomial-time many-one (Karp) reduction `P ≤ₖ Q`: a map `toFun` with many-one
correctness and a polynomial output-size bound (the honest poly-time proxy). -/

/-- A **polynomial-time many-one (Karp) reduction** from `P : σ → Prop` to `Q : τ → Prop`,
relative to encoding-size functions `sizeσ`, `sizeτ`. It bundles:
* `toFun : σ → τ`, the reduction map;
* `correct : ∀ x, P x ↔ Q (toFun x)`, many-one correctness;
* `poly : Polynomial ℕ` with `size_bound : ∀ x, sizeτ (toFun x) ≤ poly.eval (sizeσ x)`,
  the **honest poly-time proxy** (a polynomial bound on output size in terms of input
  size; NOT a Turing-machine time bound — see the module docstring). -/
structure KarpReduction {σ τ : Type*} (sizeσ : σ → ℕ) (sizeτ : τ → ℕ)
    (P : σ → Prop) (Q : τ → Prop) where
  /-- The reduction map `σ → τ`. -/
  toFun : σ → τ
  /-- Many-one correctness: `P x ↔ Q (toFun x)`. -/
  correct : ∀ x, P x ↔ Q (toFun x)
  /-- The polynomial bounding the output size in the input size (poly-time proxy). -/
  poly : Polynomial ℕ
  /-- The output size is polynomially bounded by the input size. -/
  size_bound : ∀ x, sizeτ (toFun x) ≤ poly.eval (sizeσ x)

namespace KarpReduction

variable {σ τ ρ : Type*} {sizeσ : σ → ℕ} {sizeτ : τ → ℕ} {sizeρ : ρ → ℕ}
  {P : σ → Prop} {Q : τ → Prop} {S : ρ → Prop}

/-- A Karp reduction yields the many-one bi-implication `P x ↔ Q (f x)`. -/
theorem apply_correct (R : KarpReduction sizeσ sizeτ P Q) (x : σ) :
    P x ↔ Q (R.toFun x) := R.correct x

/-- **Reflexivity**: the identity map is a Karp reduction `P ≤ₖ P` (correctness is
`Iff.rfl`; the output-size bound is the linear polynomial `X`, since `size x ≤ size x`). -/
noncomputable def id (sizeσ : σ → ℕ) (P : σ → Prop) : KarpReduction sizeσ sizeσ P P where
  toFun := _root_.id
  correct _ := Iff.rfl
  poly := Polynomial.X
  size_bound x := by simp

/-- **Transitivity (composition)**: Karp reductions compose. `P ≤ₖ Q` and `Q ≤ₖ S` give
`P ≤ₖ S` via the composed map, the composed correctness, and the **composed polynomial**
`poly₂.comp poly₁` (output size `≤ poly₂(poly₁(input size))`, using that `poly₂` is
monotone over `ℕ`). This is the basic algebra making "NP-hardness via reduction"
transitive. -/
noncomputable def comp (R₂ : KarpReduction sizeτ sizeρ Q S)
    (R₁ : KarpReduction sizeσ sizeτ P Q) :
    KarpReduction sizeσ sizeρ P S where
  toFun := R₂.toFun ∘ R₁.toFun
  correct x := (R₁.correct x).trans (R₂.correct (R₁.toFun x))
  poly := R₂.poly.comp R₁.poly
  size_bound x := by
    calc sizeρ (R₂.toFun (R₁.toFun x))
        ≤ R₂.poly.eval (sizeτ (R₁.toFun x)) := R₂.size_bound (R₁.toFun x)
      _ ≤ R₂.poly.eval (R₁.poly.eval (sizeσ x)) :=
          Polynomial.eval_le_eval_of_le_nat (R₁.size_bound x)
      _ = (R₂.poly.comp R₁.poly).eval (sizeσ x) := by rw [Polynomial.eval_comp]

/-! ## NP-hardness relative to a fixed hard problem
A faithful absolute `NPHard` needs the class `NP` and a known-NP-complete seed problem,
which require a Turing-machine framework Mathlib lacks. The achievable, faithful headline
is NP-hardness **relative to** a named hard problem `H`: `Q` is NP-hard via `H` when `H`
Karp-reduces to `Q`. If `H` is NP-hard (an external fact), so is `Q`. -/

/-- **`Q` is NP-hard relative to `H`**: there is a Karp reduction from the hard problem `H`
to `Q`. This is the faithful, formalizable form of NP-hardness — given separately that `H`
is NP-hard (the external completeness fact), `Q` is NP-hard. -/
def IsNPHardVia {σ τ : Type*} (sizeσ : σ → ℕ) (sizeτ : τ → ℕ)
    (H : σ → Prop) (Q : τ → Prop) : Prop :=
  Nonempty (KarpReduction sizeσ sizeτ H Q)

/-- NP-hardness-via transfers along Karp reductions: if `Q` is NP-hard via `H` and `Q`
Karp-reduces to `S`, then `S` is NP-hard via `H` (compose the witnesses). -/
theorem IsNPHardVia.trans {σ τ ρ : Type*} {sizeσ : σ → ℕ} {sizeτ : τ → ℕ} {sizeρ : ρ → ℕ}
    {H : σ → Prop} {Q : τ → Prop} {S : ρ → Prop}
    (hHQ : IsNPHardVia sizeσ sizeτ H Q) (hQS : Nonempty (KarpReduction sizeτ sizeρ Q S)) :
    IsNPHardVia sizeσ sizeρ H S :=
  ⟨hQS.some.comp hHQ.some⟩

end KarpReduction

/-! ## An abstract verifier-based class `NP` (faithfully partial)
For completeness we record a faithful *verifier* skeleton of NP — a problem is in `NP` when
membership has a polynomially-bounded certificate checked by a decidable predicate — and the
absolute `IsNPHard Q := every NP problem Karp-reduces to Q`. The verifier's *checker* here is
only required *decidable*, not poly-time (a faithful poly-time checker again needs a machine
cost model); the size bound on the certificate is the honest proxy. We do **not** claim any
concrete problem is `NP`-complete from this skeleton — `IsNPHardVia` against a *cited*
NP-complete seed (Exact-3-Cover, Garey-Johnson) is the headline used downstream. -/

/-- `P : σ → Prop` is in **NP** (verifier form): membership `P x` is witnessed by a
certificate `c : Cert` whose size is polynomially bounded in `size x`, checked by a
decidable `check`. (The checker is required decidable, not poly-time — the poly-time of the
checker again needs a machine cost model out of scope; this is the honest partial form.) -/
structure IsInNP {σ : Type*} (sizeσ : σ → ℕ) (P : σ → Prop) where
  /-- The certificate type (encodable, so pinned to `Type`). -/
  Cert : Type
  /-- The size of a certificate. -/
  sizeCert : Cert → ℕ
  /-- The (decidable) verifier predicate. -/
  check : σ → Cert → Prop
  /-- The verifier is decidable. -/
  decCheck : ∀ x c, Decidable (check x c)
  /-- The polynomial bounding certificate size in input size. -/
  certPoly : Polynomial ℕ
  /-- Soundness and completeness with a polynomially-bounded certificate: `P x` holds iff
  some certificate of polynomially-bounded size passes the check. -/
  spec : ∀ x, P x ↔ ∃ c, sizeCert c ≤ certPoly.eval (sizeσ x) ∧ check x c

/-- **`Q` is NP-hard** (absolute, verifier form): every NP problem Karp-reduces to `Q`.
This is the absolute headline; it is only *usable* once a concrete NP-complete seed is
available, which needs the full machine framework. The relative `IsNPHardVia` against a
cited NP-complete seed is what we instantiate. -/
def IsNPHard {τ : Type*} (sizeτ : τ → ℕ) (Q : τ → Prop) : Prop :=
  ∀ (σ : Type) (sizeσ : σ → ℕ) (P : σ → Prop),
    IsInNP sizeσ P → Nonempty (KarpReduction sizeσ sizeτ P Q)

/-- If `Q` is NP-hard (absolute) and `H` is in NP, then `Q` is NP-hard via `H`: instantiate
the absolute hardness at `H`. (Pairs the two forms: absolute hardness implies hardness via
any NP problem.) -/
theorem IsNPHard.isNPHardVia {σ : Type} {τ : Type*} {sizeσ : σ → ℕ} {sizeτ : τ → ℕ}
    {H : σ → Prop} {Q : τ → Prop}
    (hQ : IsNPHard sizeτ Q) (hH : IsInNP sizeσ H) :
    KarpReduction.IsNPHardVia sizeσ sizeτ H Q :=
  hQ σ sizeσ H hH

end DeepWiki
