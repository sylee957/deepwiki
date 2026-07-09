import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic

/-! # GCD basics

Abstract gcd predicates, uniqueness up to units, and gcd cancellation lemmas.
-/

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommMonoidWithZero R]

/-- `z` is a greatest common divisor of `x` and `y`: it divides both, and every common divisor
of `x` and `y` divides it. -/
def IsGCD (x y z : R) : Prop := z ∣ x ∧ z ∣ y ∧ ∀ t, t ∣ x → t ∣ y → t ∣ z

/-- A gcd divides its first argument. -/
theorem IsGCD.dvd_left {x y z : R} (h : IsGCD x y z) : z ∣ x := h.1

/-- A gcd divides its second argument. -/
theorem IsGCD.dvd_right {x y z : R} (h : IsGCD x y z) : z ∣ y := h.2.1

/-- A gcd is divisible by every common divisor. -/
theorem IsGCD.dvd {x y z t : R} (h : IsGCD x y z) (hx : t ∣ x) (hy : t ∣ y) : t ∣ z :=
  h.2.2 t hx hy

/-- The gcd predicate is symmetric in its two arguments. -/
theorem IsGCD.symm {x y z : R} (h : IsGCD x y z) : IsGCD y x z :=
  ⟨h.2.1, h.1, fun t hy hx => h.2.2 t hx hy⟩

/-- A gcd is unique up to multiplication by a unit: two gcds of the same pair are `Associated`. -/
theorem IsGCD.associated [IsCancelMulZero R] {x y z t : R} (hz : IsGCD x y z) (ht : IsGCD x y t) :
    Associated z t :=
  associated_of_dvd_dvd (ht.dvd hz.dvd_left hz.dvd_right) (hz.dvd ht.dvd_left ht.dvd_right)

section GCDMonoid
variable {R : Type*} [CommMonoidWithZero R] [NormalizedGCDMonoid R]

/-- gcd multiplicativity across coprime factors: if `gcd a b` is a unit then
`gcd (a·b) c` is associated to `gcd a c · gcd b c`. -/
theorem associated_gcd_mul_of_isUnit_gcd {a b : R} (hab : IsUnit (gcd a b)) (c : R) :
    Associated (gcd (a * b) c) (gcd a c * gcd b c) := by
  refine associated_of_dvd_dvd ?_ ?_
  · rw [gcd_comm a c, gcd_comm b c, gcd_comm (a * b) c]
    exact gcd_mul_dvd_mul_gcd c a b
  · refine dvd_gcd (mul_dvd_mul (gcd_dvd_left a c) (gcd_dvd_left b c)) ?_
    have hcop : IsUnit (gcd (gcd a c) (gcd b c)) :=
      isUnit_of_dvd_unit
        (dvd_gcd ((gcd_dvd_left _ _).trans (gcd_dvd_left a c))
                 ((gcd_dvd_right _ _).trans (gcd_dvd_left b c))) hab
    have hlcm : lcm (gcd a c) (gcd b c) ∣ c :=
      lcm_dvd_iff.mpr ⟨gcd_dvd_right a c, gcd_dvd_right b c⟩
    have step1 : gcd (gcd a c) (gcd b c) * lcm (gcd a c) (gcd b c) ∣ lcm (gcd a c) (gcd b c) :=
      (hcop.mul_left_dvd).mpr dvd_rfl
    exact ((gcd_mul_lcm (gcd a c) (gcd b c)).symm.dvd.trans step1).trans hlcm

/-- Coprime cancellation (divisibility form): if `gcd x b` is a unit and `x ∣ b·c` then `x ∣ c`. -/
theorem dvd_of_dvd_mul_of_isUnit_gcd {x b c : R} (hxb : IsUnit (gcd x b)) (h : x ∣ b * c) :
    x ∣ c := by
  have hx : x ∣ gcd (x * c) (b * c) := dvd_gcd (dvd_mul_right x c) h
  have e1 : Associated (gcd (x * c) (b * c)) (gcd x b * c) := gcd_mul_right' c x b
  have e2 : gcd x b * c ∣ c := hxb.mul_left_dvd.mpr dvd_rfl
  exact (hx.trans e1.dvd).trans e2

/-- Coprime cancellation (gcd form): if `gcd a b` is a unit then `gcd a (b·c) ~ gcd a c`. -/
theorem associated_gcd_mul_left_cancel {a b c : R} (hab : IsUnit (gcd a b)) :
    Associated (gcd a (b * c)) (gcd a c) := by
  refine associated_of_dvd_dvd ?_
    (dvd_gcd (gcd_dvd_left a c) ((gcd_dvd_right a c).trans (dvd_mul_left c b)))
  refine dvd_gcd (gcd_dvd_left _ _) (dvd_of_dvd_mul_of_isUnit_gcd (b := b) ?_ (gcd_dvd_right a (b * c)))
  exact isUnit_of_dvd_unit (dvd_gcd ((gcd_dvd_left _ _).trans (gcd_dvd_left a (b * c)))
    (gcd_dvd_right _ _)) hab

/-- Coprimality is preserved by finite products: if `x` is coprime to each `f i` (`i ∈ s`,
unit `gcd x (f i)`) then `x` is coprime to `∏ f i`. -/
theorem isUnit_gcd_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : R) (f : ι → R)
    (h : ∀ i ∈ s, IsUnit (gcd x (f i))) : IsUnit (gcd x (∏ i ∈ s, f i)) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact isUnit_of_dvd_one (gcd_dvd_right x 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isUnit_of_dvd_unit (gcd_mul_dvd_mul_gcd x (f a) _)
      ((h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GCDMonoid

section GCDRing
variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R]

/-- gcd absorbs a multiple of its first argument: `gcd a (b + a·c) ~ gcd a b`. -/
theorem associated_gcd_add_mul (a b c : R) : Associated (gcd a (b + a * c)) (gcd a b) := by
  refine associated_of_dvd_dvd (dvd_gcd (gcd_dvd_left _ _) ?_) (dvd_gcd (gcd_dvd_left _ _) ?_)
  · have : gcd a (b + a * c) ∣ (b + a * c) - a * c :=
      dvd_sub (gcd_dvd_right _ _) ((gcd_dvd_left _ _).mul_right c)
    rwa [add_sub_cancel_right] at this
  · exact dvd_add (gcd_dvd_right _ _) ((gcd_dvd_left _ _).mul_right c)

end GCDRing

end DeepWiki.SymbolicIntegration
