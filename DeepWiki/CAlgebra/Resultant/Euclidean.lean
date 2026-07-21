import DeepWiki.CAlgebra.Resultant.Sylvester
import DeepWiki.CAlgebra.Resultant.Descent

/-! # Resultant via the pseudo-remainder sequence

The resultant projection of the descent kernel (`DeepWiki/CAlgebra/Resultant/Descent`),
over a computable Euclidean domain of coefficients: `resultantOfTrace` folds the kernel's
trace — pad slack degree bounds down, consume one entry per pseudo-division step,
correcting by signs, extracted constants, and leading-coefficient powers. Each branch
mirrors one Mathlib resultant identity (`resultant_add_mul_right`,
`resultant_C_mul_right`, `resultant_add_left_deg`, `resultant_add_right_deg`,
`resultant_comm`, and the constant/zero base cases), so the equivalence with the
Sylvester-determinant resultant is a functional induction gluing those identities —
polynomial-time where the determinant is factorial. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u v

namespace DensePoly

variable {S : Type u} [EuclideanDomain S] [DecidableEq S]

/-! ### Bridges (any coefficient ring) -/

private theorem natDeg_bridge {f : DensePoly S} (hf : f ≠ 0) :
    (toPolynomial f).natDegree = f.size - 1 := by
  rw [natDegree_toPolynomial, degree?, if_neg (fun h0 => hf (eq_zero_of_size_zero h0))]
  rfl

private theorem lc_bridge {f : DensePoly S} (hf : f ≠ 0) :
    (toPolynomial f).leadingCoeff = f.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDeg_bridge hf, coeff_toPolynomial, leadingCoeff]

omit [DecidableEq S] in
private theorem ed_mul_div_cancel_left {a b : S} (ha : a ≠ 0) : a * b / a = b :=
  mul_left_cancel₀ ha (EuclideanDomain.mul_div_cancel' ha (Dvd.intro b rfl))

/-! ### The resultant fold -/

/-- The remainder the next fold step consumes: the tail's head divisor, `0` at the end of
the walk. -/
private def nextElem : List (DensePoly S × S) → DensePoly S
  | [] => 0
  | (r, _) :: _ => r

/-- **The resultant projection of the kernel**, a fold over the trace: pad slack degree
bounds down, handle the constant and zero base cases, and consume one trace entry per
pseudo-division step — correcting by signs, the extracted constant, and
leading-coefficient powers (exact divisions). Each branch mirrors one Mathlib resultant
identity; entries are consumed in the size-ordered orientation (the entry swap lives in
`resultantDescent`). -/
def resultantOfTrace (trace : List (DensePoly S × S)) (f g : DensePoly S) (m n : ℕ) : S :=
  if hf0 : f = 0 then 0 ^ n * g.coeff 0 ^ m
  else if hg0 : g = 0 then 0 ^ m * f.coeff 0 ^ n
  else if m + 1 < f.size then 0
  else if n + 1 < g.size then 0
  else if _ : f.size ≤ m then
    (-1 : S) ^ (n * (m - (f.size - 1))) * g.coeff n ^ (m - (f.size - 1))
      * resultantOfTrace trace f g (f.size - 1) n
  else if _ : g.size ≤ n then
    f.coeff m ^ (n - (g.size - 1)) * resultantOfTrace trace f g m (g.size - 1)
  else if n = 0 then g.coeff 0 ^ m
  else if m = 0 then f.coeff 0 ^ n
  else
    match trace with
    | [] => 0
    | (_, β) :: rest =>
        (-1 : S) ^ (m * n)
          * (β ^ n * resultantOfTrace rest g (nextElem rest) n m
            / g.leadingCoeff ^ ((f.size + 1 - g.size) * n))
  termination_by (trace.length, m + n)
  decreasing_by
    · apply Prod.Lex.right
      have h1 : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
      omega
    · apply Prod.Lex.right
      have h1 : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
      omega
    · apply Prod.Lex.left
      simp

/-- **The resultant on the kernel**: order the entry pair (one `resultant_comm` sign), walk
the kernel, fold the trace. The bound parameters are recursion state — public entries fix
them at the canonical degrees. -/
def resultantDescent {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) (m n : ℕ) : S :=
  if f.size < g.size then
    (-1 : S) ^ (m * n) * resultantOfTrace (descentTrace clean hsize st g f) g f n m
  else resultantOfTrace (descentTrace clean hsize st f g) f g m n

/-! ### Equivalence with the Sylvester determinant -/

/-- The fold equivalence along a kernel trace: the strip identity and invariant persistence
are required only at the states the walk visits, in the size-ordered orientation. Each
branch is one Mathlib resultant identity, the strip costing one `resultant_C_mul_right`. -/
private theorem resultantOfTrace_eq {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (I : σ → DensePoly S → DensePoly S → Prop)
    (hclean : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      C (clean st f g (pseudoMod f g)).1 * (clean st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      I (clean st f g (pseudoMod f g)).2.2 g (clean st f g (pseudoMod f g)).2.1)
    (trace : List (DensePoly S × S)) (f g : DensePoly S) (m n : ℕ) :
    (∃ st, trace = descentTrace clean hsize st f g ∧ I st f g) →
    (2 ≤ g.size → g.size ≤ f.size) →
    (toPolynomial f).natDegree ≤ m → (toPolynomial g).natDegree ≤ n →
    resultantOfTrace trace f g m n
      = (toPolynomial f).resultant (toPolynomial g) m n := by
  induction trace, f, g, m, n using resultantOfTrace.induct with
  | case1 trace g m n =>
      intro _ _ hm hn
      rw [resultantOfTrace.eq_def, dif_pos rfl, toPolynomial_zero, Polynomial.resultant_zero_left,
        coeff_toPolynomial]
  | case2 trace f m n hf0 =>
      intro _ _ hm hn
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_pos rfl, toPolynomial_zero,
        Polynomial.resultant_zero_right, coeff_toPolynomial]
  | case3 trace f g m n hf0 hg0 hm1 =>
      intro _ _ hm hn
      rw [natDeg_bridge hf0] at hm
      exact absurd hm1 (by omega)
  | case4 trace f g m n hf0 hg0 hm1 hn1 =>
      intro _ _ hm hn
      rw [natDeg_bridge hg0] at hn
      exact absurd hn1 (by omega)
  | case5 trace f g m n hf0 hg0 hm1 hn1 hmd ih =>
      intro hex hord hm hn
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_pos hmd]
      rw [ih hex hord (le_of_eq (natDeg_bridge hf0)) hn]
      have hkey := Polynomial.resultant_add_left_deg (f := toPolynomial f)
        (g := toPolynomial g) (m := f.size - 1) (n := n) (k := m - (f.size - 1))
        (le_of_eq (natDeg_bridge hf0))
      rw [show f.size - 1 + (m - (f.size - 1)) = m from by
        have : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
        omega] at hkey
      rw [hkey, coeff_toPolynomial]
  | case6 trace f g m n hf0 hg0 hm1 hn1 hmd hnd ih =>
      intro hex hord hm hn
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_pos hnd]
      rw [ih hex hord hm (le_of_eq (natDeg_bridge hg0))]
      have hkey := Polynomial.resultant_add_right_deg (f := toPolynomial f)
        (g := toPolynomial g) (m := m) (n := g.size - 1) (n - (g.size - 1))
        (le_of_eq (natDeg_bridge hg0))
      rw [show g.size - 1 + (n - (g.size - 1)) = n from by
        have : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
        omega] at hkey
      rw [hkey, coeff_toPolynomial]
  | case7 trace f g m hf0 hg0 hm1 hmd hn1 hnd =>
      intro _ _ hm hn
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_pos rfl]
      have hg1 : g.size = 1 := by
        have : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
        omega
      rw [show toPolynomial g = Polynomial.C (g.coeff 0) from by
        conv_lhs => rw [eq_C_of_size_eq_one hg1]
        rw [toPolynomial_C]]
      rw [Polynomial.resultant_C_zero_right]
  | case8 trace f g n hf0 hg0 hn1 hnd hn0 hm1 hmd =>
      intro _ _ hm hn
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1, dif_neg hmd,
        dif_neg hnd, if_neg hn0, if_pos rfl]
      have hf1 : f.size = 1 := by
        have : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
        omega
      rw [show toPolynomial f = Polynomial.C (f.coeff 0) from by
        conv_lhs => rw [eq_C_of_size_eq_one hf1]
        rw [toPolynomial_C]]
      rw [Polynomial.resultant_C_zero_left]
  | case9 f g m n hf0 hg0 hm1 hn1 hmd hnd hn0 hm0 =>
      rintro ⟨st, htr, hI⟩ hord hm hn
      have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
      rw [descentTrace_of_size_ne_zero clean hsize st f g hgz] at htr
      simp at htr
  | case10 f g m n hf0 hg0 hm1 hn1 hmd hnd hn0 hm0 a β rest ih =>
      rintro ⟨st, htr, hI⟩ hord hm hn
      have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
      have hg2 : 2 ≤ g.size := by
        rw [natDeg_bridge hg0] at hn
        omega
      have hfg : g.size ≤ f.size := hord hg2
      rw [descentTrace_of_size_ne_zero clean hsize st f g hgz] at htr
      injection htr with hhead htail
      injection hhead with ha hβ
      subst hβ htail
      rw [ha]
      have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hgz
      have hlcp : g.leadingCoeff ^ ((f.size + 1 - g.size) * n) ≠ 0 := pow_ne_zero _ hlc
      have hnext : nextElem (descentTrace clean hsize (clean st f g (pseudoMod f g)).2.2 g
          (clean st f g (pseudoMod f g)).2.1) = (clean st f g (pseudoMod f g)).2.1 := by
        rcases eq_or_ne (clean st f g (pseudoMod f g)).2.1.size 0 with h0 | h0
        · rw [descentTrace_of_size_eq_zero _ _ _ _ _ h0, nextElem]
          exact (eq_zero_of_size_zero h0).symm
        · rw [descentTrace_of_size_ne_zero _ _ _ _ _ h0]
          rfl
      have hr_deg : (toPolynomial (clean st f g (pseudoMod f g)).2.1).natDegree ≤ m := by
        rcases eq_or_ne (clean st f g (pseudoMod f g)).2.1 0 with hr0 | hr0
        · simp [hr0]
        · have h1 := pseudoMod_size_lt hgz f
          have h2 := hsize st f g (pseudoMod f g)
          rw [natDeg_bridge hr0]
          rw [natDeg_bridge hf0] at hm
          omega
      rw [resultantOfTrace.eq_def, dif_neg hf0, dif_neg hg0, if_neg hm1, if_neg hn1,
        dif_neg hmd, dif_neg hnd, if_neg hn0, if_neg hm0]
      dsimp only
      rw [hnext] at ih
      rw [hnext]
      rw [ih ⟨(clean st f g (pseudoMod f g)).2.2, rfl, hstep st f g hg2 hfg hI⟩
        (fun h2 => by
          have h1 := pseudoMod_size_lt hgz f
          have h3 := hsize st f g (pseudoMod f g)
          omega)
        (by rw [natDeg_bridge hg0]; omega) hr_deg]
      have hcr : Polynomial.C (clean st f g (pseudoMod f g)).1
            * toPolynomial (clean st f g (pseudoMod f g)).2.1
          = toPolynomial (pseudoMod f g) := by
        have h := congrArg toPolynomial (hclean st f g hg2 hfg hI)
        simpa [toPolynomial_mul, toPolynomial_C] using h
      have hchain : (clean st f g (pseudoMod f g)).1 ^ n
            * (toPolynomial g).resultant (toPolynomial (clean st f g (pseudoMod f g)).2.1) n m
          = g.leadingCoeff ^ ((f.size + 1 - g.size) * n)
            * (toPolynomial g).resultant (toPolynomial f) n m := by
        rw [← Polynomial.resultant_C_mul_right, hcr]
        have hCf : Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f
            = toPolynomial (pseudoMod f g)
              + toPolynomial g * toPolynomial (pseudoDiv f g) := by
          rw [← toPolynomial_pseudoDivMod hgz f]
          ring
        calc (toPolynomial g).resultant (toPolynomial (pseudoMod f g)) n m
            = (toPolynomial g).resultant
                (toPolynomial (pseudoMod f g)
                  + toPolynomial g * toPolynomial (pseudoDiv f g)) n m := by
              rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
              · rw [hq0, toPolynomial_zero, mul_zero, add_zero]
              · rw [Polynomial.resultant_add_mul_right _ _ _ _ _
                  (by
                    have h1 := pseudoDiv_natDegree_le hg0 hfg hq0
                    rw [natDeg_bridge hg0] at hn
                    rw [natDeg_bridge hf0] at hm
                    omega)
                  (by rw [natDeg_bridge hg0]; omega)]
          _ = (toPolynomial g).resultant
                (Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f)
                n m := by rw [hCf]
          _ = g.leadingCoeff ^ ((f.size + 1 - g.size) * n)
              * (toPolynomial g).resultant (toPolynomial f) n m := by
              rw [Polynomial.resultant_C_mul_right, ← pow_mul]
      rw [hchain, ed_mul_div_cancel_left hlcp]
      rw [Polynomial.resultant_comm, mul_comm n m, ← mul_assoc, ← pow_add, ← two_mul,
        pow_mul]
      simp

/-- **The invariant-carrying descent equivalence**: the reconstruction identity is required
only at states satisfying `I`, only for the pseudo-remainders actually cleaned; `I` must
hold at entry, be closed under swapping the pair (the entry commutation), and be preserved
into the walk. -/
theorem resultantDescent_eq_of_invariant {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (I : σ → DensePoly S → DensePoly S → Prop)
    (hclean : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      C (clean st f g (pseudoMod f g)).1 * (clean st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      I (clean st f g (pseudoMod f g)).2.2 g (clean st f g (pseudoMod f g)).2.1)
    (hswap : ∀ st f g, f.size < g.size → I st f g → I st g f)
    (st : σ) (f g : DensePoly S) (m n : ℕ) :
    I st f g →
    (toPolynomial f).natDegree ≤ m → (toPolynomial g).natDegree ≤ n →
    resultantDescent clean hsize st f g m n
      = (toPolynomial f).resultant (toPolynomial g) m n := by
  intro hI hm hn
  rw [resultantDescent]
  by_cases hfg : f.size < g.size
  · rw [if_pos hfg]
    rw [resultantOfTrace_eq clean hsize I hclean hstep _ g f n m
      ⟨st, rfl, hswap st f g hfg hI⟩ (fun _ => by omega) hn hm]
    rw [Polynomial.resultant_comm, mul_comm n m, ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul]
    simp
  · rw [if_neg hfg]
    exact resultantOfTrace_eq clean hsize I hclean hstep _ f g m n
      ⟨st, rfl, hI⟩ (fun _ => by omega) hm hn

/-- **The unconditional descent equivalence**: the trivial-invariant specialization, for
`clean`s whose reconstruction identity holds at every state. -/
theorem resultantDescent_eq {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (hclean : ∀ st f g r, C (clean st f g r).1 * (clean st f g r).2.1 = r)
    (st : σ) (f g : DensePoly S) (m n : ℕ) :
    (toPolynomial f).natDegree ≤ m → (toPolynomial g).natDegree ≤ n →
    resultantDescent clean hsize st f g m n
      = (toPolynomial f).resultant (toPolynomial g) m n :=
  resultantDescent_eq_of_invariant clean hsize (fun _ _ _ => True)
    (fun st f g _ _ _ => hclean st f g (pseudoMod f g))
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) st f g m n trivial

/-- **Resultant by the pseudo-remainder sequence** at the canonical degrees — the trivial
instantiation of the descent (no stripping). -/
def resultantPRSEuclidean (f g : DensePoly S) : S :=
  resultantDescent (σ := PUnit.{1}) (fun _ _ _ r => (1, r, PUnit.unit))
    (fun _ _ _ _ => le_refl _) PUnit.unit f g (f.size - 1) (g.size - 1)

/-- **The PRS resultant agrees with the Sylvester-determinant resultant** at the canonical
degrees — hypothesis-free: functional induction over the descent, each branch discharged by
the matching Mathlib identity. -/
theorem resultantPRSEuclidean_eq (f g : DensePoly S) :
    resultantPRSEuclidean f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSEuclidean, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq (σ := PUnit.{1}) _ _
    (fun _ _ _ r => by rw [← one_def, one_mul]) PUnit.unit f g _ _
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

end DensePoly

end DeepWiki.CAlgebra
