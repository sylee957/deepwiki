import Leanproofs.MinPlus.CompleteDioid
import Mathlib.Order.CompleteLattice.Lemmas
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.LatticeIntervals

/-!
# Generic sub-complete-dioid builder

Two function classes — `F⁺` and `F↑` (in `Leanproofs.MinPlus.FunctionClassDioids`) — are both
*sub-complete-dioids* of the ambient complete dioid `FunDioid`: subsets closed under the dioid
operations `𝟘, 𝟙, ⊕, ⊗` and under **arbitrary** dioid sums `sSup`, on which the restricted
structure is again a complete commutative dioid. Their derivations were identical line for line,
differing only in the closure proofs.

This module factors that pattern out once. A `SubCompleteDioid α` packages the closure data over an
arbitrary `CompleteDioid α`; from it the subtype `S.Sub = {a // a ∈ S.carrier}` is given,
generically:

* a `CompleteLattice` via `completeLatticeOfSup`, where `sSup` is the ambient `sSup` restricted to
  the carrier. Its top is `sSup carrier` — the **adjusted top** mechanism (the subtype's `⊤ =
  sSup univ` becomes `sSup carrier`, *not* the ambient `⊤`);
* all algebraic instances `Zero/One/Add/Mul/SMul ℕ/NatCast` from the closure fields
  (`nsmul`/`natCast` closure being *derived* by induction from `add`/`zero`/`one`);
* a `CommSemiring`, a `Dioid` (`add_eq_sup` from the ambient one), and a `CompleteDioid`
  (`mul_sSup` transported from the ambient `CompleteDioid.mul_sSup`).

An application then supplies only the carrier and its six closure proofs.
-/

namespace NetworkCalculus

open scoped Computability

/-- The closure data exhibiting a subset of a complete dioid `α` as a **sub-complete-dioid**: it
contains `𝟘 = 0` and `𝟙 = 1`, and is closed under `⊕ = (+)`, `⊗ = (*)`, and **arbitrary** dioid
sums `sSup`. (Closure under `n • _` and `↑n` is *derived*, not required here — see `nsmul_mem`,
`natCast_mem`.) -/
structure SubCompleteDioid (α : Type*) [CompleteDioid α] where
  /-- The underlying subset of `α`. -/
  carrier : Set α
  /-- The dioid zero `𝟘 = 0` lies in the carrier. -/
  zero_mem : (0 : α) ∈ carrier
  /-- The dioid one `𝟙 = 1` lies in the carrier. -/
  one_mem : (1 : α) ∈ carrier
  /-- The carrier is closed under the dioid sum `⊕ = (+)`. -/
  add_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  /-- The carrier is closed under the dioid product `⊗ = (*)`. -/
  mul_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The carrier is closed under arbitrary dioid sums `sSup`. -/
  sSup_mem : ∀ {T : Set α}, (∀ a ∈ T, a ∈ carrier) → sSup T ∈ carrier

namespace SubCompleteDioid

variable {α : Type*} [CompleteDioid α] (S : SubCompleteDioid α)

/-- The carrier as a type: the underlying subtype `{a // a ∈ S.carrier}`. -/
def Sub : Type _ := {a : α // a ∈ S.carrier}

/-- The underlying element of `α` of an element of the sub-dioid. -/
def val (x : S.Sub) : α := x.1

theorem property (x : S.Sub) : x.val ∈ S.carrier := x.2

@[ext] theorem ext {x y : S.Sub} (h : x.val = y.val) : x = y := Subtype.ext h

/-- Package an element of the carrier as an element of the sub-dioid. -/
def pack (a : α) (ha : a ∈ S.carrier) : S.Sub := ⟨a, ha⟩

@[simp] theorem val_pack (a : α) (ha : a ∈ S.carrier) : (S.pack a ha).val = a := rfl

/-! ### Derived closure facts -/

/-- The carrier is closed under the idempotent scalar action `n • _`: `n • a` is a finite dioid
sum of `a` (or `0`), built by induction from `zero_mem`/`add_mem`. -/
theorem nsmul_mem (n : ℕ) {a : α} (ha : a ∈ S.carrier) : n • a ∈ S.carrier := by
  induction n with
  | zero => rw [zero_nsmul]; exact S.zero_mem
  | succ k ih => rw [succ_nsmul]; exact S.add_mem ih ha

/-- The carrier is closed under the natural-number cast `↑n`: `↑n` is `0` or a sum of `1`s, built
by induction from `zero_mem`/`one_mem`/`add_mem`. -/
theorem natCast_mem (n : ℕ) : ((n : ℕ) : α) ∈ S.carrier := by
  cases n with
  | zero => rw [Nat.cast_zero]; exact S.zero_mem
  | succ k => rw [Nat.cast_succ]; exact S.add_mem (natCast_mem k) S.one_mem

/-! ### The complete lattice on the sub-dioid

The supremum is the ambient `sSup` restricted to the carrier (`sSup_mem`); it is still the least
upper bound, so `completeLatticeOfSup` produces the complete lattice. Its top is `sSup carrier` (the
image of `univ`) — the **adjusted top**. -/

instance instPartialOrder : PartialOrder S.Sub := Subtype.partialOrder _

theorem le_def (x y : S.Sub) : x ≤ y ↔ x.val ≤ y.val := Iff.rfl

/-- The supremum on the sub-dioid: the ambient `sSup`, which stays in the carrier. -/
noncomputable instance instSupSet : SupSet S.Sub :=
  ⟨fun T => S.pack (sSup (S.val '' T)) (S.sSup_mem fun a ha => by
    obtain ⟨x, _, rfl⟩ := ha; exact x.property)⟩

@[simp] theorem val_sSup (T : Set S.Sub) : (sSup T).val = sSup (S.val '' T) := rfl

/-- The restricted `sSup` is the least upper bound in the sub-dioid (inherited from `α`). -/
theorem isLUB_sSup (T : Set S.Sub) : IsLUB T (sSup T) := by
  constructor
  · intro x hx
    rw [le_def, val_sSup]
    exact le_sSup ⟨x, hx, rfl⟩
  · intro b hb
    rw [le_def, val_sSup]
    refine sSup_le ?_
    rintro f ⟨x, hx, rfl⟩
    exact hb hx

noncomputable instance instCompleteLattice : CompleteLattice S.Sub :=
  completeLatticeOfSup S.Sub S.isLUB_sSup

/-- **The top of the sub-dioid is `sSup carrier`** — the adjusted top: `⊤ = sSup univ`, whose value
is the supremum of the whole carrier (`= sSup carrier`), *not* the ambient `⊤`. -/
theorem val_top : (⊤ : S.Sub).val = sSup S.carrier := by
  show (sSup (Set.univ : Set S.Sub)).val = sSup S.carrier
  rw [val_sSup]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro a ⟨x, _, rfl⟩; exact x.property
  · intro a ha; exact ⟨S.pack a ha, Set.mem_univ _, rfl⟩

/-- The lattice join `⊔` on the sub-dioid (which `completeLatticeOfSup` defines as `sSup {x, y}`)
restricts to the ambient join. -/
theorem val_sup (x y : S.Sub) : (x ⊔ y).val = x.val ⊔ y.val := by
  show (sSup ({x, y} : Set S.Sub)).val = x.val ⊔ y.val
  rw [val_sSup, Set.image_pair, sSup_pair]; rfl

theorem val_biSup {ι : Sort*} (f : ι → S.Sub) (p : ι → Prop) :
    (⨆ i, ⨆ (_ : p i), f i).val = ⨆ i, ⨆ (_ : p i), (f i).val := by
  rw [iSup_subtype', iSup_subtype']
  rw [show (⨆ i : {i // p i}, f i.1) = sSup (Set.range fun i : {i // p i} => f i.1) from
    (sSup_range).symm, val_sSup, ← Set.range_comp, sSup_range]
  rfl

/-! ### The dioid operations on the sub-dioid

Each operation is the ambient one applied through `val`, kept in the carrier by the closure fields
(`nsmul`/`natCast` by the derived `nsmul_mem`/`natCast_mem`). -/

noncomputable instance instZero : Zero S.Sub := ⟨S.pack 0 S.zero_mem⟩
noncomputable instance instOne : One S.Sub := ⟨S.pack 1 S.one_mem⟩
noncomputable instance instAdd : Add S.Sub :=
  ⟨fun x y => S.pack (x.val + y.val) (S.add_mem x.property y.property)⟩
noncomputable instance instMul : Mul S.Sub :=
  ⟨fun x y => S.pack (x.val * y.val) (S.mul_mem x.property y.property)⟩
noncomputable instance instSMul : SMul ℕ S.Sub :=
  ⟨fun n x => S.pack (n • x.val) (S.nsmul_mem n x.property)⟩
noncomputable instance instNatCast : NatCast S.Sub := ⟨fun n => S.pack (n : α) (S.natCast_mem n)⟩

@[simp] theorem val_zero : (0 : S.Sub).val = 0 := rfl
@[simp] theorem val_one : (1 : S.Sub).val = 1 := rfl
@[simp] theorem val_add (x y : S.Sub) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_mul (x y : S.Sub) : (x * y).val = x.val * y.val := rfl
@[simp] theorem val_nsmul (n : ℕ) (x : S.Sub) : (n • x).val = n • x.val := rfl
@[simp] theorem val_natCast (n : ℕ) : (NatCast.natCast n : S.Sub).val = (n : α) := rfl

/-- The (commutative) semiring on the sub-dioid, with every law the ambient `α` law projected
through `val` (`SubCompleteDioid.ext`). -/
noncomputable instance instCommSemiring : CommSemiring S.Sub where
  add_assoc a b c := S.ext <| by rw [val_add, val_add, val_add, val_add, add_assoc]
  add_comm a b := S.ext <| by rw [val_add, val_add, add_comm]
  zero_add a := S.ext <| by rw [val_add, val_zero, zero_add]
  add_zero a := S.ext <| by rw [val_add, val_zero, add_zero]
  nsmul := (· • ·)
  nsmul_zero a := S.ext <| by rw [val_nsmul, val_zero, zero_nsmul]
  nsmul_succ n a := S.ext <| by rw [val_nsmul, val_add, val_nsmul, succ_nsmul]
  mul_assoc a b c := S.ext <| by rw [val_mul, val_mul, val_mul, val_mul, mul_assoc]
  mul_comm a b := S.ext <| by rw [val_mul, val_mul, mul_comm]
  one_mul a := S.ext <| by rw [val_mul, val_one, one_mul]
  mul_one a := S.ext <| by rw [val_mul, val_one, mul_one]
  zero_mul a := S.ext <| by rw [val_mul, val_zero, zero_mul]
  mul_zero a := S.ext <| by rw [val_mul, val_zero, mul_zero]
  natCast := fun n => (n : S.Sub)
  natCast_zero := S.ext <| by rw [val_natCast, val_zero, Nat.cast_zero]
  natCast_succ n := S.ext <| by rw [val_natCast, val_add, val_natCast, val_one, Nat.cast_succ]
  left_distrib a b c := S.ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, left_distrib]
  right_distrib a b c := S.ext <| by rw [val_mul, val_add, val_add, val_mul, val_mul, right_distrib]

/-- The dioid sum `⊕` on the sub-dioid is the lattice join `⊔` (from the ambient `add_eq_sup`). -/
theorem add_eq_sup' (x y : S.Sub) : x + y = x ⊔ y :=
  S.ext (by rw [val_add, val_sup, add_eq_sup])

/-- The (idempotent commutative) **dioid** on the sub-dioid: the canonical order is the restriction
of `α`'s. -/
noncomputable instance instDioid : Dioid S.Sub :=
  { instCommSemiring S, (instCompleteLattice S : CompleteLattice S.Sub) with
    add_eq_sup := S.add_eq_sup' }

/-- The dioid product `⊗` on the sub-dioid distributes over an arbitrary dioid `sSup`: the supremum
restricts to the ambient one (`val_sSup`), so this is the ambient `CompleteDioid.mul_sSup`
projected through `val`. -/
theorem mul_sSup' (a : S.Sub) (T : Set S.Sub) : a * sSup T = ⨆ b ∈ T, a * b := by
  apply S.ext
  rw [val_mul, val_sSup, CompleteDioid.mul_sSup a.val (S.val '' T), iSup_image, S.val_biSup]
  exact iSup_congr fun b => iSup_congr fun _ => (val_mul S a b).symm

/-- **The sub-dioid is a complete commutative dioid**, with the adjusted top `sSup carrier`
(`val_top`). -/
noncomputable instance instCompleteDioid : CompleteDioid S.Sub :=
  { instDioid S, (instCompleteLattice S : CompleteLattice S.Sub) with
    mul_sSup := S.mul_sSup' }

end SubCompleteDioid

end NetworkCalculus
