import Leanproofs.MinPlus.Convolution

/-!
# `(F, ∧, ∗)` is a complete commutative dioid (Proposition 2.3)

The set of (min,plus) functions `F = ℝ⁺ → R̄min` (`Leanproofs.MinPlus.Convolution`), equipped with
the pointwise minimum `⊕ = ∧` as sum and the convolution `⊗ = ∗` as product, forms a **complete
commutative dioid** (Proposition 2.3), with

* zero `ε : t ↦ +∞`  (the dioid `𝟘` of `R̄min` at every point),
* unit `e : 0 ↦ 0, t > 0 ↦ +∞`  (the dioid `𝟙` at `0`, `𝟘` elsewhere),
* top `⊤ : t ↦ −∞`  (the dioid top of `R̄min` at every point).

## Why a newtype

The bare function space `F = ℝ≥0 → R̄min` already carries `Pi.commSemiring`, whose product is the
**pointwise** product `(f * g) t = f t * g t`. We need the product to be **convolution**, so we wrap
`F` in a single-field structure `FunDioid` (à la `MinPlus.D`). The wrapper inherits *none* of `F`'s
pointwise algebra: only the complete lattice (transported from the pointwise one on `F`, whose join
`⊔` is precisely the dioid sum `∧`) and the dioid `CommSemiring`/`Dioid`/`CompleteDioid` attached
explicitly below. In particular the only `Mul (FunDioid)` is the convolution — no `Pi.mul` diamond.

The pointwise join `⊔` on `F = ℝ≥0 → R̄min` is, at each point, the join of `R̄min`, which (since the
canonical order of `R̄min` reverses the numeric order) is the numeric minimum `∧`. So the
transported lattice join on `FunDioid` is the book's dioid sum, and the transported `⊥ = ε`.
-/

namespace NetworkCalculus

open scoped Computability NNReal

/-! ### Convolution distributes over an arbitrary pointwise supremum

The single piece of completeness content: convolution `∗` is lower semi-continuous in its second
argument, i.e. it distributes over an arbitrary *pointwise* supremum `⨆ i, g i` of functions in
`F`. This is `CompleteDioid.mul_iSup` on the scalar `R̄min`, pushed through the two `⨆`'s of the
convolution and swapped by `iSup_comm`. -/

/-- **Lower semi-continuity of `∗`.** Convolution distributes over an arbitrary pointwise supremum:
`f ∗ (⨆ i, g i) = ⨆ i, (f ∗ g i)`, where `⨆` is the pointwise supremum on `F`. -/
theorem conv_iSup {ι : Sort*} (f : F) (g : ι → F) :
    (f ∗ ⨆ i, g i) = ⨆ i, (f ∗ g i) := by
  funext t
  rw [iSup_apply, conv_apply]
  calc
    (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, f p.val.1 * (⨆ i, g i) p.val.2)
        = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, ⨆ i, f p.val.1 * g i p.val.2 := by
          refine iSup_congr fun p => ?_
          rw [iSup_apply, CompleteDioid.mul_iSup]
      _ = ⨆ i, ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, f p.val.1 * g i p.val.2 := iSup_comm
      _ = ⨆ i, (f ∗ g i) t := by
          refine iSup_congr fun i => ?_
          rw [conv_apply]

/-! ### The (min,plus) function dioid carrier -/

/-- The carrier of the (min,plus) **function dioid** (Proposition 2.3): a **newtype** wrapping
`F = ℝ⁺ → R̄min`. Wrapping `F` in a structure means `FunDioid` inherits none of `F`'s pointwise
algebra; only the complete lattice (transported below) and the dioid algebra we attach explicitly
live on it. The dioid is `⊕ = ∧` (pointwise minimum), `⊗ = ∗` (convolution), `𝟘 = ε`, `𝟙 = e`. -/
structure FunDioid where ofFun ::
  /-- The underlying (min,plus) function in `F`. -/
  toFun : F

namespace FunDioid

/-- The defining equivalence `FunDioid ≃ F`, used to transport the pointwise complete lattice. -/
def toFunEquiv : FunDioid ≃ F :=
  ⟨toFun, ofFun, fun ⟨_⟩ => rfl, fun _ => rfl⟩

/-- The projection `toFun` is injective (single-field structure). -/
theorem toFun_injective : Function.Injective toFun :=
  fun a b h => by cases a; cases b; cases h; rfl

@[simp] theorem ofFun_toFun (a : FunDioid) : FunDioid.ofFun a.toFun = a := rfl
@[simp] theorem toFun_ofFun (a : F) : (FunDioid.ofFun a).toFun = a := rfl

/-! #### The complete lattice, transported pointwise from `F`

The complete lattice on `F = ℝ≥0 → R̄min` is `Pi.instCompleteLattice`, whose join `⊔` is the
*pointwise* join of `R̄min`. Transporting it through `toFunEquiv` puts that lattice on `FunDioid`;
its join is the book's dioid sum `∧` (`sup_eq_add`/`add_eq_sup'` below) and its bottom is `ε`. -/

/-- The complete lattice on `FunDioid`, transported from the pointwise complete lattice on `F`. Its
join `⊔` is the pointwise join of `R̄min` (= the numeric minimum `∧`, the dioid sum) and its bottom
`⊥` is `ε : t ↦ +∞`. -/
noncomputable instance instCompleteLattice : CompleteLattice FunDioid :=
  Equiv.completeLattice toFunEquiv

/-- `toFun` is monotone for the transported order (it is an order iso onto `F` pointwise). -/
theorem le_def (a b : FunDioid) : a ≤ b ↔ a.toFun ≤ b.toFun := Iff.rfl

/-! #### The dioid operations

`⊕ = ∧` (pointwise `R̄min` sum), `⊗ = ∗` (convolution), `𝟘 = ε`, `𝟙 = e`, plus the idempotent
`nsmul`/`natCast`. -/

/-- The dioid sum `⊕ = ∧`: the pointwise `R̄min` dioid sum (= pointwise minimum). -/
noncomputable def add (a b : FunDioid) : FunDioid :=
  FunDioid.ofFun (fun t => a.toFun t + b.toFun t)
/-- The dioid product `⊗ = ∗`: the convolution. -/
noncomputable def mul (a b : FunDioid) : FunDioid := FunDioid.ofFun (a.toFun ∗ b.toFun)
/-- The additive neutral `𝟘 = ε : t ↦ +∞` (the dioid zero of `R̄min` everywhere). -/
noncomputable def zero : FunDioid := FunDioid.ofFun (fun _ => (0 : RbarMin))
/-- The multiplicative neutral `𝟙 = e : 0 ↦ 0, t > 0 ↦ +∞`. -/
noncomputable def one : FunDioid :=
  FunDioid.ofFun (fun t => if t = 0 then (1 : RbarMin) else (0 : RbarMin))
/-- Idempotent scalar action: `0 • a = 𝟘`, `(n+1) • a = a`. -/
noncomputable def nsmul (n : ℕ) (a : FunDioid) : FunDioid :=
  FunDioid.ofFun (if n = 0 then (fun _ => (0 : RbarMin)) else a.toFun)
/-- The natural-number cast, collapsed by idempotency: `↑0 = 𝟘`, `↑(n+1) = 𝟙 = e`. -/
noncomputable def natCast (n : ℕ) : FunDioid :=
  FunDioid.ofFun (if n = 0 then (fun _ => (0 : RbarMin))
    else (fun t => if t = 0 then (1 : RbarMin) else (0 : RbarMin)))

/-! #### Semiring laws

Each law is a named theorem about the operations above; the `CommSemiring` instance is then a flat
assembly. `⊕ = ∧` carries its commutative-monoid laws pointwise from `R̄min`; `⊗ = ∗` carries its
monoid laws from `conv_assoc`/`conv_comm`; `𝟘 = ε` is neutral for `∧` and absorbing for `∗`; the
`nsmul`/`natCast` recursions collapse by idempotency of `∧`. -/

theorem add_assoc' (a b c : FunDioid) : add (add a b) c = add a (add b c) :=
  toFun_injective (funext fun _ => add_assoc _ _ _)

theorem add_comm' (a b : FunDioid) : add a b = add b a :=
  toFun_injective (funext fun _ => add_comm _ _)

/-- `𝟘 = ε` is neutral for `⊕ = ∧`: `ε + a = a` pointwise (`ε t = (0 : R̄min)`). -/
theorem zero_add' (a : FunDioid) : add zero a = a :=
  toFun_injective (funext fun _ => zero_add _)

/-- `𝟘 = ε` is neutral for `⊕ = ∧`: `a + ε = a` pointwise. -/
theorem add_zero' (a : FunDioid) : add a zero = a :=
  toFun_injective (funext fun _ => add_zero _)

theorem nsmul_zero' (a : FunDioid) : nsmul 0 a = zero := by
  apply toFun_injective
  show (if (0 : ℕ) = 0 then (fun _ => (0 : RbarMin)) else a.toFun) = fun _ => (0 : RbarMin)
  rw [if_pos rfl]

theorem nsmul_succ' (n : ℕ) (a : FunDioid) : nsmul (n + 1) a = add (nsmul n a) a := by
  apply toFun_injective
  show (if n + 1 = 0 then (fun _ => (0 : RbarMin)) else a.toFun)
     = fun t => (if n = 0 then (fun _ => (0 : RbarMin)) else a.toFun) t + a.toFun t
  rw [if_neg (Nat.succ_ne_zero n)]
  funext t
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (zero_add _).symm
  · rw [if_neg h.ne']; exact (add_idem _).symm

theorem mul_assoc' (a b c : FunDioid) : mul (mul a b) c = mul a (mul b c) :=
  toFun_injective (conv_assoc _ _ _)

theorem mul_comm' (a b : FunDioid) : mul a b = mul b a :=
  toFun_injective (conv_comm _ _)

theorem one_mul' (a : FunDioid) : mul one a = a := by
  apply toFun_injective
  show one.toFun ∗ a.toFun = a.toFun
  funext t
  apply le_antisymm
  · apply conv_le
    intro u s hus
    by_cases hu : u = 0
    · subst hu; rw [zero_add] at hus; subst hus
      show (if (0 : ℝ≥0) = 0 then (1 : RbarMin) else 0) * a.toFun s ≤ a.toFun s
      rw [if_pos rfl, one_mul]
    · show (if u = 0 then (1 : RbarMin) else 0) * a.toFun s ≤ a.toFun t
      rw [if_neg hu, zero_mul]; exact bot_le
  · have := conv_ge one.toFun a.toFun (u := 0) (s := t) (zero_add t)
    show a.toFun t ≤ (one.toFun ∗ a.toFun) t
    have e : one.toFun 0 = 1 := if_pos rfl
    rw [e, one_mul] at this; exact this

theorem mul_one' (a : FunDioid) : mul a one = a := by
  rw [mul_comm']; exact one_mul' a

/-- `𝟘 = ε` is absorbing for `⊗ = ∗`: `ε ∗ a = ε` (each summand `ε u * a s = ⊥`). -/
theorem zero_mul' (a : FunDioid) : mul zero a = zero := by
  apply toFun_injective
  show zero.toFun ∗ a.toFun = zero.toFun
  funext t
  apply le_antisymm
  · apply conv_le
    intro u s hus
    show (0 : RbarMin) * a.toFun s ≤ (0 : RbarMin)
    rw [zero_mul]
  · show zero.toFun t ≤ (zero.toFun ∗ a.toFun) t
    exact bot_le

theorem mul_zero' (a : FunDioid) : mul a zero = zero := by
  rw [mul_comm']; exact zero_mul' a

theorem natCast_zero' : (natCast 0 : FunDioid) = zero := by
  apply toFun_injective
  show (if (0 : ℕ) = 0 then (fun _ => (0 : RbarMin)) else (fun _ => (1 : RbarMin)))
     = fun _ => (0 : RbarMin)
  rw [if_pos rfl]

theorem natCast_succ' (n : ℕ) : (natCast (n + 1) : FunDioid) = add (natCast n) one := by
  apply toFun_injective
  show (if n + 1 = 0 then (fun _ => (0 : RbarMin))
          else (fun t => if t = 0 then (1 : RbarMin) else (0 : RbarMin)))
     = fun t => (if n = 0 then (fun _ => (0 : RbarMin))
          else (fun t => if t = 0 then (1 : RbarMin) else (0 : RbarMin))) t + one.toFun t
  rw [if_neg (Nat.succ_ne_zero n)]
  funext t
  show one.toFun t = (if n = 0 then (fun _ => (0 : RbarMin))
          else (fun t => if t = 0 then (1 : RbarMin) else (0 : RbarMin))) t + one.toFun t
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (zero_add _).symm
  · rw [if_neg h.ne']; exact (add_idem _).symm

/-- Left-distributivity of `⊗ = ∗` over `⊕ = ∧`: `f ∗ (g ∧ h) = (f ∗ g) ∧ (f ∗ h)`, which is
`conv_sup` (the dioid sum `∧` is the pointwise `R̄min` sum `= ⊔`). -/
theorem left_distrib' (a b c : FunDioid) : mul a (add b c) = add (mul a b) (mul a c) := by
  apply toFun_injective
  show a.toFun ∗ (fun t => b.toFun t + c.toFun t) = fun t => (a.toFun ∗ b.toFun) t + (a.toFun ∗ c.toFun) t
  simp_rw [add_eq_sup]
  exact conv_sup a.toFun b.toFun c.toFun

/-- Right-distributivity of `⊗ = ∗` over `⊕ = ∧`, from `left_distrib'` and commutativity of `∗`. -/
theorem right_distrib' (a b c : FunDioid) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm', left_distrib', mul_comm' a c, mul_comm' b c]

/-- The (min,plus) commutative semiring on `FunDioid`, assembled from the named operations and
laws. -/
noncomputable instance commSemiring : CommSemiring FunDioid where
  add := add
  add_assoc := add_assoc'
  add_comm := add_comm'
  zero := zero
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmul
  nsmul_zero := nsmul_zero'
  nsmul_succ := nsmul_succ'
  mul := mul
  mul_assoc := mul_assoc'
  mul_comm := mul_comm'
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  natCast := natCast
  natCast_zero := natCast_zero'
  natCast_succ := natCast_succ'
  left_distrib := left_distrib'
  right_distrib := right_distrib'

/-- The transported join `⊔` on `FunDioid` is the *pointwise* `R̄min` join, which equals the dioid
sum `⊕ = ∧` (pointwise `R̄min` sum) by `add_eq_sup`. -/
theorem add_eq_sup' (a b : FunDioid) : a + b = a ⊔ b := by
  apply toFun_injective
  show (fun t => a.toFun t + b.toFun t) = (a ⊔ b).toFun
  funext t
  show a.toFun t + b.toFun t = (a ⊔ b).toFun t
  rw [add_eq_sup]
  rfl

/-- The (min,plus) **function dioid** on `FunDioid`: the canonical order `a ≼ b ↔ a ∧ b = b` is the
pointwise (reversed-numeric) order, with `⊕ = ∧` the join and `𝟘 = ε` the bottom. -/
noncomputable instance dioid : Dioid FunDioid :=
  { commSemiring, (inferInstance : CompleteLattice FunDioid) with
    add_eq_sup := add_eq_sup' }

/-! #### Completeness (lower semi-continuity)

The product `⊗ = ∗` distributes over an arbitrary dioid sum `⨆`. The transported `sSup`/`⨆` on
`FunDioid` is the *pointwise* `R̄min` supremum, so this is exactly `conv_iSup` transported through
the equivalence. -/

/-- `mul` (the dioid product `⊗`) unfolds to convolution on the underlying functions. -/
theorem mul_toFun (a b : FunDioid) : (a * b).toFun = a.toFun ∗ b.toFun := rfl

/-- `toFun` turns the transported `sSup` into the pointwise `R̄min` supremum. The transported
`sSup s = toFunEquiv.symm (⨆ a ∈ s, toFunEquiv a)`, which unfolds to the pointwise `⨆`. -/
theorem toFun_sSup (s : Set FunDioid) : (sSup s).toFun = ⨆ a ∈ s, (a : FunDioid).toFun := rfl

theorem toFun_iSup {ι : Sort*} (g : ι → FunDioid) : (⨆ i, g i).toFun = ⨆ i, (g i).toFun := by
  rw [iSup, toFun_sSup, iSup_range]

/-- The (min,plus) **complete dioid** on `FunDioid` (Proposition 2.3), assembled from the dioid and
the transported complete lattice. The lower-semicontinuity field `mul_sSup`
(`a ∗ ⨆ s = ⨆ b ∈ s, a ∗ b`) is `conv_iSup` transported through `toFunEquiv`: the transported `sSup`
is the pointwise `R̄min` supremum, and convolution distributes over it (`conv_iSup`). -/
noncomputable instance completeDioid : CompleteDioid FunDioid :=
  { dioid, (inferInstance : CompleteLattice FunDioid) with
    mul_sSup := fun a s => by
      apply toFun_injective
      rw [mul_toFun, toFun_sSup,
        ← iSup_subtype'' s (fun b : FunDioid => b.toFun), conv_iSup]
      rw [show (⨆ b ∈ s, a * b) = ⨆ b : s, a * (b : FunDioid) from
        (iSup_subtype'' s (fun b : FunDioid => a * b)).symm, toFun_iSup]
      refine iSup_congr fun b => ?_
      rw [mul_toFun] }

/-- **Proposition 2.3.** `(F, ∧, ∗)` is a **complete commutative dioid**, with zero `ε : t ↦ +∞`,
unit `e : 0 ↦ 0`/`t > 0 ↦ +∞`, and top `⊤ : t ↦ −∞`. -/
noncomputable example : CompleteDioid FunDioid := inferInstance

/-! ### Isotony [2.4]

`[2.4]` — the isotony of `∧` and `∗` with respect to the canonical (dioid) order — is, as the book
notes, a *direct consequence of Theorem 2.1*: it is the generic dioid isotony
(`Dioid.add_le_add_right'`/`mul_le_mul_right'`) specialized to the dioid `FunDioid`. We record it
under the book's names rather than re-prove anything. -/

/-- **[2.4], first part.** `f ≼ g ⟹ f ∧ h ≼ g ∧ h` (isotony of the dioid sum `∧`). -/
theorem inf_le_inf_left' {f g : FunDioid} (h : f ≤ g) (k : FunDioid) : f + k ≤ g + k :=
  Dioid.add_le_add_right' h k

/-- **[2.4], second part.** `f ≼ g ⟹ f ∗ h ≼ g ∗ h` (isotony of the convolution `∗`). -/
theorem conv_le_conv_right {f g : FunDioid} (h : f ≤ g) (k : FunDioid) : f * k ≤ g * k :=
  Dioid.mul_le_mul_right' h k

end FunDioid

end NetworkCalculus
