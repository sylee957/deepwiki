import DeepWiki.CAlgebra.Squarefree.Basic
import DeepWiki.Algebra.SquarefreeYun

/-! # Yun's squarefree decomposition — self-validating

Yun's sweep computes the staircase factors from one initial `gcd(p, deriv p)` plus gcds of
the much smaller pairs `(cᵢ, dᵢ)`. Correctness is proven directly from the sum-free ghost
invariant `IsYunState` — the loop state `(c, d)` satisfies `d·g = c·deriv g` for a ghost
divisor `g` whose primes `c` covers — with each step validated by the Mathlib-side
`Polynomial.yun_step` through the bridge. The ghost's size strictly drops while it is a
nonunit, so the fuel `p.size` provably suffices; no runtime validation remains. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- The Yun loop invariant: `(c, d)` is a Yun state for the ghost `g` — `c` squarefree and
covering the primes of `g`, with the state identity `d * g = c * deriv g`. -/
def IsYunState (g c d : DensePoly R) : Prop :=
  g ≠ 0 ∧ c ≠ 0 ∧ Squarefree c ∧ (∀ q, Prime q → q ∣ g → q ∣ c) ∧ d * g = c * deriv g

/-- One Yun sweep: emit `gcd(c, d)`, divide it out, and update the derivative accumulator. -/
private def yunAux : ℕ → DensePoly R → DensePoly R → List (DensePoly R)
  | 0, _, _ => []
  | fuel + 1, c, d =>
    if c.size ≤ 1 then []
    else
      DensePolyGcd.gcd c d ::
        yunAux fuel (div c (DensePolyGcd.gcd c d))
          (div d (DensePolyGcd.gcd c d) - deriv (div c (DensePolyGcd.gcd c d)))

/-- A constant first component exits the sweep immediately, whatever the fuel. -/
private theorem yunAux_eq_nil {c d : DensePoly R} (hc : c.size ≤ 1) :
    ∀ fuel, yunAux fuel c d = ([] : List (DensePoly R))
  | 0 => rfl
  | fuel + 1 => by rw [yunAux, if_pos hc]

/-- **The transported Yun step**: dividing out a gcd of the state pair yields a Yun state for
the ghost quotient. The prime-multiplicity content is `Polynomial.yun_step`, pulled through
the bridge. -/
theorem IsYunState.step [CharZero R] {g c d : DensePoly R} (h : IsYunState g c d) :
    div c (DensePolyGcd.gcd c d) ∣ g ∧
    IsYunState (div g (div c (DensePolyGcd.gcd c d))) (div c (DensePolyGcd.gcd c d))
      (div d (DensePolyGcd.gcd c d) - deriv (div c (DensePolyGcd.gcd c d))) := by
  obtain ⟨hg, hc0, hcsf, hcov, hid⟩ := h
  set P := DensePolyGcd.gcd c d with hPdef
  set c₂ := div c P with hc2def
  have hPc : P ∣ c := DensePolyGcd.gcd_dvd_left c d
  have hPd : P ∣ d := DensePolyGcd.gcd_dvd_right c d
  have hP0 : P ≠ 0 := fun h0 => hc0 (zero_dvd_iff.mp (h0 ▸ hPc))
  have hPc' : P * c₂ = c := EuclideanDomain.mul_div_cancel' hP0 hPc
  have hc20 : c₂ ≠ 0 := fun h0 => hc0 (by rw [← hPc', h0, mul_zero])
  have hcov' : ∀ Q, Prime Q → Q ∣ toPolynomial g → Q ∣ toPolynomial c := by
    intro Q hQ hQg
    obtain ⟨q, rfl⟩ : ∃ q, toPolynomial q = Q := ⟨ofPolynomial Q, toPolynomial_ofPolynomial Q⟩
    exact toPolynomial_dvd (hcov q (prime_toPolynomial_iff.mp hQ) (dvd_of_toPolynomial_dvd hQg))
  have hid' : toPolynomial d * toPolynomial g
      = toPolynomial c * Polynomial.derivative (toPolynomial g) := by
    have h1 := congrArg toPolynomial hid
    simpa [toPolynomial_mul, toPolynomial_deriv] using h1
  have hPuniv' : ∀ E, E ∣ toPolynomial c → E ∣ toPolynomial d → E ∣ toPolynomial P := by
    intro E h1 h2
    obtain ⟨e, rfl⟩ : ∃ e, toPolynomial e = E := ⟨ofPolynomial E, toPolynomial_ofPolynomial E⟩
    exact toPolynomial_dvd
      (DensePolyGcd.dvd_gcd c d (dvd_of_toPolynomial_dvd h1) (dvd_of_toPolynomial_dvd h2))
  obtain ⟨hdvdP, hcovP, hidP⟩ := Polynomial.yun_step (toPolynomial_ne_zero hg)
    (toPolynomial_ne_zero hc0) (squarefree_toPolynomial_iff.mpr hcsf) hcov' hid'
    (toPolynomial_dvd hPc) (toPolynomial_dvd hPd) hPuniv'
  have htc2 : toPolynomial c₂ = toPolynomial c / toPolynomial P := toPolynomial_div_of_dvd hPc
  have hc2g : c₂ ∣ g := dvd_of_toPolynomial_dvd (by rw [htc2]; exact hdvdP)
  have hg2' : c₂ * div g c₂ = g := EuclideanDomain.mul_div_cancel' hc20 hc2g
  have hg20 : div g c₂ ≠ 0 := fun h0 => hg (by rw [← hg2', h0, mul_zero])
  have htg2 : toPolynomial (div g c₂) = toPolynomial g / toPolynomial c₂ :=
    toPolynomial_div_of_dvd hc2g
  refine ⟨hc2g, hg20, hc20,
    hcsf.squarefree_of_dvd ⟨P, hPc'.symm.trans (mul_comm P c₂)⟩, ?_, ?_⟩
  · -- coverage for the new ghost
    intro q hq hqg2
    apply dvd_of_toPolynomial_dvd
    rw [htc2]
    apply hcovP _ (prime_toPolynomial_iff.mpr hq)
    have h1 : toPolynomial q ∣ toPolynomial (div g c₂) := toPolynomial_dvd hqg2
    rw [htg2, htc2] at h1
    exact h1
  · -- the state identity for the new pair
    apply toPolynomial_injective
    have htd2 : toPolynomial (div d P) = toPolynomial d / toPolynomial P :=
      toPolynomial_div_of_dvd hPd
    simp only [toPolynomial_mul, toPolynomial_sub, toPolynomial_deriv, htd2, htg2, htc2]
    exact hidP

/-- The main induction over the Yun sweep: from any Yun state whose ghost fits the fuel, the
emitted factors are squarefree, reconstruct `c·g` with staircase exponents, and multiply to
the state's squarefree component `c`. -/
private theorem yunAux_spec [CharZero R] :
    ∀ fuel {g c d : DensePoly R}, IsYunState g c d → g.size ≤ fuel →
      (∀ f ∈ yunAux fuel c d, Squarefree f) ∧
      Associated (c * g) (powProd (yunAux fuel c d) 1) ∧
      Associated c (yunAux fuel c d).prod := by
  intro fuel
  induction fuel with
  | zero =>
    intro g c d h hfuel
    exact absurd (eq_zero_of_size_zero (Nat.le_zero.mp hfuel)) h.1
  | succ fuel ih =>
    intro g c d h hfuel
    obtain ⟨hg, hc0, hcsf, hcov, hid⟩ := h
    by_cases hc1 : c.size ≤ 1
    · -- exit: `c` is a unit, hence so is the ghost
      rw [yunAux, if_pos hc1]
      have hcu : IsUnit c := isUnit_iff_size_eq_one.mpr (by
        have h0 : c.size ≠ 0 := fun h0 => hc0 (eq_zero_of_size_zero h0)
        omega)
      have hgu : IsUnit g := by
        by_contra hgu
        obtain ⟨q, hqirr, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg
        have hq := UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirr
        exact hq.not_unit (isUnit_of_dvd_unit (hcov q hq hqg) hcu)
      refine ⟨by simp, ?_, ?_⟩
      · show Associated (c * g) (powProd [] 1)
        exact associated_one_iff_isUnit.mpr (hcu.mul hgu)
      · rw [List.prod_nil]
        exact associated_one_iff_isUnit.mpr hcu
    · -- emit `P := gcd c d` and recurse on the ghost quotient
      rw [yunAux, if_neg hc1]
      obtain ⟨hc2g, hnew⟩ := IsYunState.step ⟨hg, hc0, hcsf, hcov, hid⟩
      set P := DensePolyGcd.gcd c d with hPdef
      set c₂ := div c P with hc2def
      set d₂ := div d P - deriv c₂ with hd2def
      set g₂ := div g c₂ with hg2def
      have hP0 : P ≠ 0 := fun h0 => hc0 (zero_dvd_iff.mp (h0 ▸ DensePolyGcd.gcd_dvd_left c d))
      have hPc' : P * c₂ = c :=
        EuclideanDomain.mul_div_cancel' hP0 (DensePolyGcd.gcd_dvd_left c d)
      have hc20 : c₂ ≠ 0 := hnew.2.1
      have hg2' : c₂ * g₂ = g := EuclideanDomain.mul_div_cancel' hc20 hc2g
      have hPsf : Squarefree P := hcsf.squarefree_of_dvd (DensePolyGcd.gcd_dvd_left c d)
      by_cases hc2u : IsUnit c₂
      · -- final factor: the remaining ghost is a unit, the tail sweep is empty
        rw [yunAux_eq_nil (isUnit_iff_size_eq_one.mp hc2u).le fuel]
        have hg2u : IsUnit g₂ := by
          by_contra hgu
          obtain ⟨q, hqirr, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hnew.1
          have hq := UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirr
          exact hq.not_unit (isUnit_of_dvd_unit (hnew.2.2.2.1 q hq hqg) hc2u)
        refine ⟨?_, ?_, ?_⟩
        · intro f hf
          rw [List.mem_singleton] at hf
          subst hf; exact hPsf
        · have hcg : c * g = P * (c₂ * (c₂ * g₂)) := by rw [← hPc', ← hg2']; ring
          show Associated (c * g) (P ^ 1 * powProd [] 2)
          rw [hcg, pow_one, show powProd ([] : List (DensePoly R)) 2 = 1 from rfl, mul_one]
          exact Associated.symm
            ⟨(hc2u.mul (hc2u.mul hg2u)).unit, by rw [IsUnit.unit_spec]⟩
        · rw [List.prod_cons, List.prod_nil, mul_one, ← hPc']
          exact Associated.symm ⟨hc2u.unit, by rw [IsUnit.unit_spec]⟩
      · -- recursive step: the ghost strictly shrinks
        have hc2size : 2 ≤ c₂.size := by
          have h1 : c₂.size ≠ 0 := fun h0 => hc20 (eq_zero_of_size_zero h0)
          have h2 : c₂.size ≠ 1 := fun h1 => hc2u (isUnit_iff_size_eq_one.mpr h1)
          omega
        have hg2size : g₂.size < g.size := by
          have hmul := size_mul hc20 hnew.1
          rw [hg2'] at hmul
          omega
        obtain ⟨ih1, ih2, ih3⟩ := ih hnew (by omega)
        refine ⟨?_, ?_, ?_⟩
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hPsf
          · exact ih1 f hf
        · rw [powProd, pow_one, powProd_succ]
          have hcg : c * g = P * ((c₂ * g₂) * c₂) := by rw [← hPc', ← hg2']; ring
          rw [hcg]
          exact (Associated.refl P).mul_mul (ih2.mul_mul ih3)
        · rw [List.prod_cons, ← hPc']
          exact (Associated.refl P).mul_mul ih3

/-- Yun's squarefree decomposition: the sweep with fuel `p.size`, started at
`c₁ = sqfreePart p`, `d₁ = p′/gcd(p,p′) − c₁′`. Proven correct by the ghost invariant. -/
def sqfDecompYun [CharZero R] (p : DensePoly R) : List (DensePoly R) :=
  yunAux p.size (sqfreePart p)
    (div (deriv p) (DensePolyGcd.gcd p (deriv p)) - deriv (sqfreePart p))

/-- Yun's initial pair is a Yun state for the ghost `gcd(p, deriv p)`. -/
private theorem isYunState_init [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    IsYunState (DensePolyGcd.gcd p (deriv p)) (sqfreePart p)
      (div (deriv p) (DensePolyGcd.gcd p (deriv p)) - deriv (sqfreePart p)) := by
  set g := DensePolyGcd.gcd p (deriv p) with hgdef
  set c := sqfreePart p with hcdef
  have hg0 : g ≠ 0 := DensePolyGcd.gcd_ne_zero_of_left hp _
  have hc0 : c ≠ 0 := sqfreePart_ne_zero hp
  have hgc : g * c = p := gcd_deriv_mul_sqfreePart hp
  have hgd : g ∣ deriv p := DensePolyGcd.gcd_dvd_right p (deriv p)
  have hgd' : g * div (deriv p) g = deriv p := EuclideanDomain.mul_div_cancel' hg0 hgd
  refine ⟨hg0, hc0, squarefree_sqfreePart hp, ?_, ?_⟩
  · -- prime coverage, via the Polynomial-side coverage keystone
    intro q hq hqg
    have hqp : q ∣ p := hqg.trans ⟨c, hgc.symm⟩
    have h1 : toPolynomial q ∣ toPolynomial p /
        EuclideanDomain.gcd (toPolynomial p) (Polynomial.derivative (toPolynomial p)) :=
      Polynomial.irreducible_dvd_div_gcd_derivative (toPolynomial_ne_zero hp)
        (prime_toPolynomial_iff.mpr hq).irreducible (toPolynomial_dvd hqp)
    exact dvd_of_toPolynomial_dvd (h1.trans (toPolynomial_sqfreePart_associated hp).symm.dvd)
  · -- the state identity, from the product rule on `p = g·c`
    have hd : deriv p = deriv g * c + g * deriv c := by rw [← hgc, deriv_mul]
    have hcalc : (div (deriv p) g - deriv c) * g = deriv p - deriv c * g := by
      rw [sub_mul]
      congr 1
      rw [mul_comm, hgd']
    rw [hcalc, hd]
    ring

/-- Every factor produced by Yun's decomposition is squarefree. -/
theorem squarefree_of_mem_sqfDecompYun [CharZero R] {p f : DensePoly R}
    (hf : f ∈ sqfDecompYun p) : Squarefree f := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [sqfDecompYun, size_zero] at hf
    exact absurd hf (List.not_mem_nil)
  · obtain ⟨h1, -, -⟩ := yunAux_spec p.size (isYunState_init hp)
      (size_le_size_of_dvd hp (DensePolyGcd.gcd_dvd_left p (deriv p)))
    exact h1 f hf

/-- **Exponent-exact reconstruction for Yun**: identical contract to `sqfDecompMusser_spec`,
proven directly from the ghost invariant. -/
theorem sqfDecompYun_spec [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Associated p (powProd (sqfDecompYun p) 1) ∧
      Associated (sqfreePart p) (sqfDecompYun p).prod := by
  obtain ⟨-, h2, h3⟩ := yunAux_spec p.size (isYunState_init hp)
    (size_le_size_of_dvd hp (DensePolyGcd.gcd_dvd_left p (deriv p)))
  rw [sqfDecompYun]
  refine ⟨?_, h3⟩
  have hgc : sqfreePart p * DensePolyGcd.gcd p (deriv p) = p := by
    rw [mul_comm]; exact gcd_deriv_mul_sqfreePart hp
  rwa [hgc] at h2

end DensePoly

end DeepWiki.CAlgebra
