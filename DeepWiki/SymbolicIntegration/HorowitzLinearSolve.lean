import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The Horowitz–Ostrogradsky linear solve (Bronstein §2.3)
The Horowitz method finds the numerators `B, C` of `∫ A/D = B/D⁻ + ∫ C/D*` by a *linear system* over
`K` — without factoring `D`. With `D⁻ = gcd(D, D')`, `D* = D/D⁻`, and the Horowitz polynomial `E` (with
`E·D⁻ = D⁻′·D*`), the defining identity `A = B′·D* − B·E + C·D⁻` is `K`-linear in the coefficients of
`B` (degree `< deg D⁻`) and `C` (degree `< deg D*`). This file packages that as a `K`-linear map
`horowitzLinear` and shows it maps the degree-bounded coordinate spaces into `degreeLT (deg D⁻ + deg D*)`;
"the solve exists and is unique" then reduces to its injectivity (a root-multiplicity argument, separate). -/

open Polynomial

noncomputable section

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The **Horowitz linear operator** at the ambient `K[X]` level: `(B, C) ↦ B′·D* − B·E + C·D⁻`,
`K`-linear in `(B, C)`. -/
def horowitzLinear (Dminus Dstar E : K[X]) : (K[X] × K[X]) →ₗ[K] K[X] where
  toFun BC := derivative BC.1 * Dstar - BC.1 * E + BC.2 * Dminus
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, derivative_add]; ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, derivative_smul, smul_mul_assoc, smul_sub, smul_add,
      RingHom.id_apply]

@[simp] theorem horowitzLinear_apply (Dminus Dstar E B C : K[X]) :
    horowitzLinear Dminus Dstar E (B, C) = derivative B * Dstar - B * E + C * Dminus := rfl

/-- Degree helper: `deg p < a` and `deg q ≤ b` give `deg (p·q) < a + b` (over a field). -/
private theorem degree_mul_lt_of_lt_of_le {p q : K[X]} {a b : ℕ} (hp : p.degree < (a : WithBot ℕ))
    (hq : q.degree ≤ (b : WithBot ℕ)) : (p * q).degree < ((a + b : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne (p * q) 0 with h | h
  · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree h, Nat.cast_lt]
    have hpn : p.natDegree < a := by
      rw [degree_eq_natDegree (left_ne_zero_of_mul h), Nat.cast_lt] at hp; exact hp
    have hqn : q.natDegree ≤ b := by
      rw [degree_eq_natDegree (right_ne_zero_of_mul h), Nat.cast_le] at hq; exact hq
    exact lt_of_le_of_lt natDegree_mul_le (by omega)

/-- The Horowitz operator sends degree-bounded `(B, C)` into `degreeLT (deg D⁻ + deg D*)`: with
`deg B < deg D⁻ =: m`, `deg C < deg D* =: n`, and `deg E < n` (forced by `E·D⁻ = D⁻′·D*`), each of
`B′·D*`, `B·E`, `C·D⁻` has degree `< m + n`. -/
theorem horowitzLinear_mem_degreeLT {Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E.degree < Dstar.natDegree) {B C : K[X]}
    (hB : B ∈ degreeLT K Dminus.natDegree) (hC : C ∈ degreeLT K Dstar.natDegree) :
    horowitzLinear Dminus Dstar E (B, C)
      ∈ degreeLT K (Dminus.natDegree + Dstar.natDegree) := by
  rw [mem_degreeLT] at hB hC ⊢
  set m := Dminus.natDegree
  set n := Dstar.natDegree
  have hDmdeg : Dminus.degree = (m : WithBot ℕ) := degree_eq_natDegree hDm
  have hDsdeg : Dstar.degree = (n : WithBot ℕ) := degree_eq_natDegree hDs
  have hBderiv : (derivative B).degree < (m : WithBot ℕ) := by
    rcases eq_or_ne B 0 with hB0 | hB0
    · simp [hB0]
    · exact (degree_derivative_lt hB0).trans hB
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (lt_of_le_of_lt (degree_sub_le _ _)
    (max_lt ?_ ?_)) ?_)
  · exact degree_mul_lt_of_lt_of_le hBderiv (le_of_eq hDsdeg)
  · exact degree_mul_lt_of_lt_of_le hB (le_of_lt hE)
  · rw [Nat.add_comm m n]; exact degree_mul_lt_of_lt_of_le hC (le_of_eq hDmdeg)

/-- The Horowitz operator as a `K`-linear map between the **degree-bounded coordinate spaces**
`degreeLT (deg D⁻) × degreeLT (deg D*) → degreeLT (deg D⁻ + deg D*)`. Both have `K`-dimension
`deg D⁻ + deg D*`, so this map is injective iff surjective — the basis of "the solve exists and is
unique iff the operator is injective". -/
def horowitzMap {Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E.degree < Dstar.natDegree) :
    (degreeLT K Dminus.natDegree × degreeLT K Dstar.natDegree) →ₗ[K]
      degreeLT K (Dminus.natDegree + Dstar.natDegree) :=
  LinearMap.codRestrict _
    ((horowitzLinear Dminus Dstar E).comp
      ((degreeLT K Dminus.natDegree).subtype.prodMap (degreeLT K Dstar.natDegree).subtype))
    (fun BC => horowitzLinear_mem_degreeLT hDm hDs hE BC.1.2 BC.2.2)

@[simp] theorem horowitzMap_coe_apply {Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E.degree < Dstar.natDegree) (BC : degreeLT K Dminus.natDegree × degreeLT K Dstar.natDegree) :
    (horowitzMap hDm hDs hE BC : K[X])
      = derivative (BC.1 : K[X]) * Dstar - (BC.1 : K[X]) * E + (BC.2 : K[X]) * Dminus := rfl

/-- `finrank` of the Horowitz domain `degreeLT m × degreeLT n` is `m + n` (each factor has the
`Fin`-power basis `degreeLTEquiv`). -/
theorem finrank_degreeLT_prod (m n : ℕ) :
    Module.finrank K (degreeLT K m × degreeLT K n) = m + n := by
  rw [Module.finrank_prod, (degreeLTEquiv K m).finrank_eq, (degreeLTEquiv K n).finrank_eq,
    Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, Fintype.card_fin]

/-- **The Horowitz solve, reduced to injectivity** (§2.3): if the Horowitz operator is injective, then
for every numerator `A` with `deg A < deg D⁻ + deg D*` there exist **unique** degree-bounded `B, C` with
`A = B′·D* − B·E + C·D⁻` — so `∫ A/D = B/D⁻ + ∫ C/D*` with `B, C` found by the linear system. (By
`injective_iff_surjective` on the equal-dimension coordinate spaces; injectivity is the remaining
root-multiplicity lemma.) -/
theorem exists_unique_horowitz_of_injective {Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E.degree < Dstar.natDegree) (hinj : Function.Injective (horowitzMap hDm hDs hE))
    {A : K[X]} (hA : A ∈ degreeLT K (Dminus.natDegree + Dstar.natDegree)) :
    ∃! BC : degreeLT K Dminus.natDegree × degreeLT K Dstar.natDegree,
      derivative (BC.1 : K[X]) * Dstar - (BC.1 : K[X]) * E + (BC.2 : K[X]) * Dminus = A := by
  have hfr : Module.finrank K (degreeLT K Dminus.natDegree × degreeLT K Dstar.natDegree)
      = Module.finrank K (degreeLT K (Dminus.natDegree + Dstar.natDegree)) := by
    rw [finrank_degreeLT_prod, (degreeLTEquiv K _).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  have hsurj : Function.Surjective (horowitzMap hDm hDs hE) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
  obtain ⟨BC, hBC⟩ := hsurj ⟨A, hA⟩
  have hval : derivative (BC.1 : K[X]) * Dstar - (BC.1 : K[X]) * E + (BC.2 : K[X]) * Dminus = A := by
    rw [← horowitzMap_coe_apply hDm hDs hE BC]; exact congrArg Subtype.val hBC
  refine ⟨BC, hval, fun BC' hBC' => ?_⟩
  apply hinj
  apply Subtype.ext
  rw [horowitzMap_coe_apply, horowitzMap_coe_apply, hBC', hval]

end DeepWiki.SymbolicIntegration

end
