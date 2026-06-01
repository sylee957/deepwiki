import Leanproofs.MinPlus.CompleteDioid

/-!
# A reusable builder for (min,plus) dioids

Both `Rmin = ℝ ∪ {+∞}` and `R⁺min = ℝ≥0 ∪ {+∞}` are the order-dual of a linearly ordered additive
monoid with a top, equipped with `⊕ = min` and `⊗ = +`. This module factors that shared
construction once, so each concrete carrier is a short instance application.

* `MinPlus.Carrier M` — the data needed for the **dioid** layer: a `LinearOrder` + `OrderTop` +
  `AddCommMonoid` with an absorbing top and monotone addition. It yields `CommSemiring (D M)` and
  `Dioid (D M)`.
* `MinPlus.CompleteCarrier M` — adds a `CompleteLinearOrder` and lower semi-continuity of `+`
  (distributivity over arbitrary numeric infima). It yields `CompleteDioid (D M)`.

The carrier `D M` is a **newtype** wrapping `M`. It deliberately inherits **none** of `M`'s
algebraic instances: only the order/lattice (transported from `Mᵒᵈ`) and the dioid
`CommSemiring`/`Dioid`/`CompleteDioid` that we attach explicitly live on `D M`. In particular the
dioid product `⊗` is the *only* `Mul (D M)` — there is no stray `Mul` lifted from a numeric
multiplication on `M`. The order on `D M` is the reverse of the numeric order on `M`: `a ≼ b ↔
b.toDual ≤ a.toDual`, so `⊕ = min` is the lattice join and `𝟘 = ⊤` is the bottom.
-/

namespace NetworkCalculus

open scoped Computability  -- `add_eq_sup : a + b = a ⊔ b`

namespace MinPlus

/-! ### The dioid carrier -/

/-- Data for the (min,plus) **dioid** construction on `D M`: a linearly ordered additive
commutative monoid with a top `⊤` that is absorbing for `+` and whose addition is monotone. -/
class Carrier (M : Type*) extends LinearOrder M, OrderTop M, AddCommMonoid M where
  /-- `⊤` (which becomes the dioid neutral `𝟘`) is absorbing for `+` (the dioid product). -/
  add_top' : ∀ a : M, a + ⊤ = ⊤
  /-- Addition is monotone (the dioid product is isotone). -/
  add_le_add_left' : ∀ {a b : M}, a ≤ b → ∀ c : M, c + a ≤ c + b

namespace Carrier
variable {M : Type*} [Carrier M]

theorem top_add' (a : M) : ⊤ + a = ⊤ := by rw [add_comm]; exact add_top' a
theorem add_le_add_right' {a b : M} (h : a ≤ b) (c : M) : a + c ≤ b + c := by
  rw [add_comm a, add_comm b]; exact add_le_add_left' h c

end Carrier

/-- The (min,plus) dioid carrier: a **newtype** wrapping `M`. Wrapping `M` in a structure means
`D M` inherits none of `M`'s algebraic instances; only the order/lattice and the dioid algebra we
attach below live on it. The dioid is `⊕ = min`, `⊗ = +`, `𝟘 = ⊤`, `𝟙 = 0`, with the canonical
order the reverse of the numeric order on `M`. -/
structure D (M : Type*) where ofDual ::
  /-- The underlying element of `M` (with the *reversed* order). -/
  toDual : M

namespace D

/-- The defining equivalence `D M ≃ Mᵒᵈ`, used to transport the order/lattice from `Mᵒᵈ`. -/
def toDualEquiv {M : Type*} : D M ≃ Mᵒᵈ :=
  ⟨fun x => OrderDual.toDual x.toDual, fun y => ⟨OrderDual.ofDual y⟩, fun ⟨_⟩ => rfl, fun _ => rfl⟩

/-- The projection `toDual` is injective (single-field structure). -/
theorem toDual_injective {M : Type*} : Function.Injective (toDual (M := M)) :=
  fun a b h => by cases a; cases b; cases h; rfl

@[simp] theorem ofDual_toDual {M : Type*} (a : D M) : D.ofDual a.toDual = a := rfl
@[simp] theorem toDual_ofDual {M : Type*} (a : M) : (D.ofDual a).toDual = a := rfl

/-! #### Order/lattice transported from `Mᵒᵈ` -/

/-- The complete lattice on `D M`, transported from `Mᵒᵈ`. Its order is the reverse of the numeric
order on `M`, its join `⊔ = min` and its bottom `⊥ = ⊤`. -/
noncomputable instance instCompleteLattice {M : Type*} [CompleteLattice M] :
    CompleteLattice (D M) :=
  Equiv.completeLattice toDualEquiv

/-- The lattice on `D M` (dioid layer), transported from `Mᵒᵈ`. -/
noncomputable instance instLattice {M : Type*} [Lattice M] : Lattice (D M) :=
  Equiv.lattice toDualEquiv

variable {M : Type*} [Carrier M]

/-- The canonical (reversed) order on `D M`: `a ≼ b ↔ b.toDual ≤ a.toDual`. The order on `D M` is
the one transported from `Mᵒᵈ` through `toDualEquiv`. -/
theorem le_def (a b : D M) : a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl

/-- The order-bottom on `D M`: `⊥ = ⊤` numerically (the dioid neutral `𝟘`). -/
instance instOrderBot : OrderBot (D M) where
  bot := D.ofDual ⊤
  bot_le _ := (le_def _ _).mpr le_top

/-! #### The dioid operations

`⊕ = min`, `⊗ = +`, `𝟘 = ⊤`, `𝟙 = 0`, plus the idempotent `nsmul`/`natCast`. -/

/-- The dioid sum `⊕ = min`. -/
def add (a b : D M) : D M := D.ofDual (min a.toDual b.toDual)
/-- The dioid product `⊗ = +`. -/
def mul (a b : D M) : D M := D.ofDual (a.toDual + b.toDual)
/-- The additive neutral `𝟘 = ⊤`. -/
def zero : D M := D.ofDual ⊤
/-- The multiplicative neutral `𝟙 = 0`. -/
def one : D M := D.ofDual 0
/-- Idempotent scalar action: `0 • a = 𝟘`, `(n+1) • a = a`. -/
def nsmul (n : ℕ) (a : D M) : D M := D.ofDual (if n = 0 then ⊤ else a.toDual)
/-- The natural-number cast, collapsed by idempotency: `↑0 = 𝟘`, `↑(n+1) = 𝟙`. -/
def natCast (n : ℕ) : D M := D.ofDual (if n = 0 then ⊤ else (0 : M))

/-! #### Semiring laws

Each law is a named theorem about the operations above; the `CommSemiring` instance is then a flat
assembly of these. `⊕ = min` carries its commutative-monoid laws from `min` on `M`; `⊗ = +` carries
its monoid laws from `+`; `𝟘 = ⊤` is neutral for `min` and absorbing for `+`; and the `nsmul`/
`natCast` recursions collapse by idempotency of `min`. -/

theorem add_assoc' (a b c : D M) : add (add a b) c = add a (add b c) :=
  toDual_injective (min_assoc _ _ _)

theorem add_comm' (a b : D M) : add a b = add b a :=
  toDual_injective (min_comm _ _)

/-- `𝟘 = ⊤` is neutral for `⊕ = min`: `min ⊤ a = a`. -/
theorem zero_add' (a : D M) : add zero a = a :=
  toDual_injective (min_eq_right le_top)

/-- `𝟘 = ⊤` is neutral for `⊕ = min`: `min a ⊤ = a`. -/
theorem add_zero' (a : D M) : add a zero = a :=
  toDual_injective (min_eq_left le_top)

theorem nsmul_zero' (a : D M) : nsmul 0 a = zero := by
  show D.ofDual (if (0 : ℕ) = 0 then ⊤ else _) = D.ofDual ⊤
  rw [if_pos rfl]

theorem nsmul_succ' (n : ℕ) (a : D M) : nsmul (n + 1) a = add (nsmul n a) a := by
  apply toDual_injective
  show (if n + 1 = 0 then ⊤ else a.toDual)
     = min (if n = 0 then ⊤ else a.toDual) a.toDual
  rw [if_neg (Nat.succ_ne_zero n)]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (min_eq_right le_top).symm
  · rw [if_neg h.ne']; exact (min_self _).symm

theorem mul_assoc' (a b c : D M) : mul (mul a b) c = mul a (mul b c) :=
  toDual_injective (add_assoc _ _ _)

theorem mul_comm' (a b : D M) : mul a b = mul b a :=
  toDual_injective (add_comm _ _)

theorem one_mul' (a : D M) : mul one a = a :=
  toDual_injective (zero_add a.toDual)

theorem mul_one' (a : D M) : mul a one = a :=
  toDual_injective (add_zero a.toDual)

/-- `𝟘 = ⊤` is absorbing for `⊗ = +`: `⊤ + a = ⊤`. -/
theorem zero_mul' (a : D M) : mul zero a = zero :=
  toDual_injective (Carrier.top_add' a.toDual)

/-- `𝟘 = ⊤` is absorbing for `⊗ = +`: `a + ⊤ = ⊤`. -/
theorem mul_zero' (a : D M) : mul a zero = zero :=
  toDual_injective (Carrier.add_top' a.toDual)

theorem natCast_zero' : (natCast 0 : D M) = zero := by
  show D.ofDual (if (0 : ℕ) = 0 then ⊤ else (0 : M)) = D.ofDual ⊤
  rw [if_pos rfl]

theorem natCast_succ' (n : ℕ) : (natCast (n + 1) : D M) = add (natCast n) one := by
  apply toDual_injective
  show (if n + 1 = 0 then ⊤ else (0 : M))
     = min (if n = 0 then ⊤ else (0 : M)) (0 : M)
  rw [if_neg (Nat.succ_ne_zero n)]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [if_pos rfl]; exact (min_eq_right le_top).symm
  · rw [if_neg h.ne']; exact (min_self _).symm

/-- Left-distributivity of `⊗ = +` over `⊕ = min`, from monotonicity of addition. -/
theorem left_distrib' (a b c : D M) : mul a (add b c) = add (mul a b) (mul a c) :=
  toDual_injective <|
    (Monotone.map_min (f := fun x : M => a.toDual + x)
      fun _ _ h => Carrier.add_le_add_left' h _)

/-- Right-distributivity of `⊗ = +` over `⊕ = min`, from monotonicity of addition. -/
theorem right_distrib' (a b c : D M) : mul (add a b) c = add (mul a c) (mul b c) :=
  toDual_injective <|
    (Monotone.map_min (f := fun x : M => x + c.toDual)
      fun _ _ h => Carrier.add_le_add_right' h _)

/-- The (min,plus) commutative semiring on `D M`, assembled from the named operations and laws. -/
noncomputable instance commSemiring : CommSemiring (D M) where
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

/-- The transported join `⊔` on `D M` equals `⊕ = min`. The `Equiv.lattice` transport defines
`a ⊔ b = toDualEquiv.symm (toDualEquiv a ⊔ toDualEquiv b)`, and in `Mᵒᵈ` the join is the numeric
`min`, so this reduces to `D.ofDual (min a.toDual b.toDual)`. -/
theorem sup_eq_add (a b : D M) : a ⊔ b = add a b := rfl

/-- `⊕ = min` is the lattice join for the canonical (reversed) order. -/
theorem add_eq_sup' (a b : D M) : add a b = a ⊔ b := (sup_eq_add a b).symm

/-- The (min,plus) **dioid** on `D M`: the canonical order `a ≼ b ↔ min a b = b` is the reverse of
the numeric order, with `⊕ = min` the join and `𝟘 = ⊤` the bottom. -/
noncomputable instance dioid : Dioid (D M) :=
  { commSemiring, (inferInstance : Lattice (D M)), (inferInstance : OrderBot (D M)) with
    add_eq_sup := add_eq_sup' }

end D

/-! ### The complete dioid carrier -/

/-- Data for the (min,plus) **complete dioid** construction on `D M`: additionally a complete
lattice with **lower-semicontinuous** addition, i.e. `+` distributes over arbitrary numeric infima
(`add_sInf'`). For `ℝ≥0∞` this follows from `ENNReal.add_iInf`.

The lower-semicontinuity field is phrased over a `Set M` (so the class stays in `M`'s single
universe and remains usable as an instance without leaking a phantom index universe); the indexed
`add_iInf'` form over any `ι : Sort*` is derived as a theorem below. -/
class CompleteCarrier (M : Type*) extends Carrier M, CompleteLinearOrder M where
  /-- Lower semi-continuity: `+` distributes over the infimum of an arbitrary set. -/
  add_sInf' : ∀ (a : M) (s : Set M), (a + sInf s) = ⨅ b ∈ s, a + b

namespace CompleteCarrier
variable {M : Type*} [CompleteCarrier M]

/-- Lower semi-continuity in indexed form (over any `ι : Sort*`), derived from `add_sInf'`. -/
theorem add_iInf' {ι : Sort*} (a : M) (f : ι → M) : (a + ⨅ i, f i) = ⨅ i, a + f i := by
  rw [iInf, add_sInf', iInf_range]

end CompleteCarrier

namespace D

variable {M : Type*}

/-- `toDual` turns the transported bounded `⨆` into the numeric bounded `⨅` — through the order
dual. The transported `sSup s = toDualEquiv.symm (⨆ a ∈ s, toDualEquiv a)`, and in `Mᵒᵈ` that
bounded join is the numeric bounded infimum, definitionally. -/
theorem toDual_sSup_bdd [CompleteLattice M] (s : Set (D M)) :
    (sSup s).toDual = ⨅ a ∈ s, (a : D M).toDual := by
  show (toDualEquiv.symm (⨆ a ∈ s, toDualEquiv a)).toDual = _
  rfl

theorem toDual_iSup_eq [CompleteLattice M] {ι : Sort*} (g : ι → D M) :
    (⨆ i, g i).toDual = ⨅ i, (g i).toDual := by
  rw [iSup, toDual_sSup_bdd, iInf_range]

theorem toDual_sSup_eq [CompleteLattice M] (s : Set (D M)) :
    (sSup s).toDual = ⨅ b : s, (b : D M).toDual := by
  rw [toDual_sSup_bdd, iInf_subtype]

theorem toDual_biSup_eq [CompleteLattice M] (s : Set (D M)) (f : D M → D M) :
    (⨆ b ∈ s, f b).toDual = ⨅ b : s, (f (b : D M)).toDual := by
  rw [iSup_subtype']; exact toDual_iSup_eq _

/-- The (min,plus) **complete dioid** on `D M`, assembled from the dioid and the complete lattice.

The lower-semicontinuity field `mul_sSup` (`a ⊗ ⨆ s = ⨆ b∈s, a ⊗ b`) is exactly the carrier's
`add_iInf'` transported through the order dual (`sSup` ↦ numeric `sInf`/`⨅`). It is given inline:
unlike the algebraic laws above, the higher-order rewrite by `add_iInf'` only resolves with the
field's expected type guiding unification, so it does not factor cleanly into a standalone lemma. -/
noncomputable instance completeDioid [CompleteCarrier M] : CompleteDioid (D M) :=
  { dioid, (inferInstance : CompleteLattice (D M)) with
    mul_sSup := fun a s => toDual_injective (by
      show a.toDual + (sSup s).toDual = (⨆ b ∈ s, a * b).toDual
      rw [toDual_sSup_eq, toDual_biSup_eq, CompleteCarrier.add_iInf']
      rfl) }

end D

end MinPlus

end NetworkCalculus
