import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Yun

/-! # Polynomial Yun loop state

Abstract loop state, emitted factors, and powered-product reconstruction for Yun factorization.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeYunState

variable {K : Type*} [Field K]

open Classical in
/-- Abstract Yun numerator `Babs A i = squarefreePart (deflation A (i−1))`. -/
noncomputable def Babs (A : K[X]) (i : ℕ) : K[X] :=
  squarefreePart (deflation A (i - 1))

open Classical in
/-- Abstract Yun derivative-polynomial `Dabs A i = Yun A i − (Babs A i)′`. -/
noncomputable def Dabs (A : K[X]) (i : ℕ) : K[X] :=
  Yun A i - derivative (squarefreePart (deflation A (i - 1)))

open Classical in
/-- The Yun loop invariant: `(b,d)` is a common nonzero constant multiple of `(Babs A i,Dabs A i)`. -/
def YunInv (A : K[X]) (i : ℕ) (b d : K[X]) : Prop :=
  ∃ c : K, c ≠ 0 ∧ b = Polynomial.C c * Babs A i ∧ d = Polynomial.C c * Dabs A i

end SquarefreeYunState

section SquarefreeYunStateLemmas

variable {K : Type*} [Field K]

open Classical in
/-- `Dabs A i = sqfreeFactPart A i * Yun A (i+1)`. -/
theorem Dabs_eq_mul (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    Dabs A i = sqfreeFactPart A i * Yun A (i + 1) := by
  rw [Dabs]; exact Yun_sub_derivative_squarefreePart A i hi hA

open Classical in
/-- `Babs A i = sqfreeFactPart A i * Babs A (i+1)`. -/
theorem Babs_eq_mul (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    Babs A i = sqfreeFactPart A i * Babs A (i + 1) := by
  rw [Babs, Babs, Nat.add_sub_cancel, ← squarefreePart_deflation_mul_sqfreeFactPart A i hi hA,
    mul_comm]

open UniqueFactorizationMonoid in
open Classical in
/-- `gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart A i)`. -/
theorem gcd_Babs_Dabs [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart A i) := by
  rw [Babs_eq_mul A i hi hA, Dabs_eq_mul A i hi hA, gcd_mul_left]
  have hrp : IsRelPrime (Babs A (i + 1)) (Yun A (i + 1)) := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rw [Babs]; rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd (Babs A (i + 1)) (Yun A (i + 1))) :=
    gcd_isUnit_iff_isRelPrime.mpr hrp
  rw [(normalize_eq_one.mpr hunit ▸ (normalize_gcd (Babs A (i + 1)) (Yun A (i + 1))).symm :
    gcd (Babs A (i + 1)) (Yun A (i + 1)) = 1), mul_one]

open UniqueFactorizationMonoid in
open Classical in
/-- One Yun step preserves `YunInv` and emits `normalize (sqfreeFactPart A i)`. -/
theorem yunStep_preserves [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    gcd b d = normalize (sqfreeFactPart A i) ∧
      YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  obtain ⟨c, hc, hb, hd⟩ := hinv
  set V := sqfreeFactPart A i with hV
  have hV0 : V ≠ 0 := sqfreeFactPart_ne_zero A i
  set w := V.leadingCoeff with hw
  have hw0 : w ≠ 0 := leadingCoeff_ne_zero.mpr hV0
  set Vn := normalize V with hVn
  have hVn0 : Vn ≠ 0 := by rw [hVn]; simpa using hV0
  have hgcd : gcd b d = Vn := by
    rw [hb, hd, gcd_mul_left, normalize_eq_one.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)),
      one_mul, gcd_Babs_Dabs A i hi hA, ← hV, ← hVn]
  have hVeq : V = Polynomial.C w * Vn := self_eq_C_leadingCoeff_mul_normalize V hV0
  have hbfact : b = Vn * (Polynomial.C (c * w) * Babs A (i + 1)) := by
    rw [hb, Babs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  have hdfact : d = Vn * (Polynomial.C (c * w) * Yun A (i + 1)) := by
    rw [hd, Dabs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  have hb' : b / gcd b d = Polynomial.C (c * w) * Babs A (i + 1) := by
    rw [hgcd, hbfact, mul_div_cancel_left₀ _ hVn0]
  have hd' : d / gcd b d = Polynomial.C (c * w) * Yun A (i + 1) := by
    rw [hgcd, hdfact, mul_div_cancel_left₀ _ hVn0]
  refine ⟨hgcd, c * w, mul_ne_zero hc hw0, hb', ?_⟩
  rw [hd', hb', derivative_C_mul, Dabs, Nat.add_sub_cancel, Babs, Nat.add_sub_cancel, mul_sub]

open UniqueFactorizationMonoid in
open Classical in
/-- The factor emitted by one Yun step is associated to the `i`-th squarefree part. -/
theorem yunStep_emit_assoc [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  rw [(yunStep_preserves A i hi hA hinv).1]
  exact normalize_associated (sqfreeFactPart A i)

open Classical in
/-- Abstract Yun loop emitting `gcd b d` and recursing on the deflated pair. -/
noncomputable def yunLoopAbs (A : K[X]) : K[X] × K[X] → ℕ → ℕ → List K[X]
  | _, _, 0 => []
  | (b, d), i, (n + 1) =>
      gcd b d :: yunLoopAbs A (b / gcd b d, d / gcd b d - derivative (b / gcd b d)) (i + 1) n

open Classical in
/-- The abstract Yun loop is factorwise associated to consecutive squarefree parts. -/
theorem yunLoopAbs_forall₂ [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      List.Forall₂ Associated (yunLoopAbs A (b, d) i n)
        ((List.range n).map (fun j => sqfreeFactPart A (i + j))) := by
  intro n
  induction n with
  | zero => intro i b d _ _; simp [yunLoopAbs]
  | succ n ih =>
    intro i b d hi hinv
    rw [yunLoopAbs, List.range_succ_eq_map, List.map_cons]
    refine List.Forall₂.cons (yunStep_emit_assoc A i hi hA hinv) ?_
    have hstep := (yunStep_preserves A i hi hA hinv).2
    have htail := ih (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d))
      (by omega) hstep
    rw [List.map_map]
    have hreindex : (List.range n).map ((fun j => sqfreeFactPart A (i + j)) ∘ Nat.succ)
        = (List.range n).map (fun j => sqfreeFactPart A ((i + 1) + j)) :=
      List.map_congr_left (fun j _ => by simp only [Function.comp_apply]; congr 1; omega)
    rw [hreindex]
    exact htail

open Classical in
/-- Every factor emitted by the abstract Yun loop is squarefree. -/
theorem yunLoopAbs_squarefree [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      ∀ V ∈ yunLoopAbs A (b, d) i n, Squarefree V := by
  intro n
  induction n with
  | zero => intro i b d _ _ V hV; simp [yunLoopAbs] at hV
  | succ n ih =>
    intro i b d hi hinv V hV
    rw [yunLoopAbs, List.mem_cons] at hV
    rcases hV with rfl | hV
    · exact squarefree_of_associated_sqfreeFactPart A i (yunStep_emit_assoc A i hi hA hinv)
    · exact ih (i + 1) _ _ (by omega) (yunStep_preserves A i hi hA hinv).2 V hV

open Classical in
/-- Distinct-position factors emitted by the abstract Yun loop are relatively prime. -/
theorem yunLoopAbs_pairwise_isRelPrime [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d)
    {p q : ℕ} (hpq : p ≠ q) (hp : p < (yunLoopAbs A (b, d) i n).length)
    (hq : q < (yunLoopAbs A (b, d) i n).length) :
    IsRelPrime ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩)
      ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) := by
  have hF := yunLoopAbs_forall₂ A hA n i b d hi hinv
  have hlen : (yunLoopAbs A (b, d) i n).length
      = ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hF.length_eq
  have hp' : p < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hp
  have hq' : q < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hq
  have hAp : Associated ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩) (sqfreeFactPart A (i + p)) := by
    have h := hF.get hp hp'
    simpa using h
  have hAq : Associated ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) (sqfreeFactPart A (i + q)) := by
    have h := hF.get hq hq'
    simpa using h
  exact isRelPrime_of_associated_sqfreeFactPart A (by omega : i + p ≠ i + q) hAp hAq

open Classical in
/-- The abstract Yun loop product is associated to the product of consecutive squarefree parts. -/
theorem yunLoopAbs_prod_assoc [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (yunLoopAbs A (b, d) i n).prod
      (((List.range n).map (fun j => sqfreeFactPart A (i + j))).prod) :=
  List.rel_prod (R := Associated) (Associated.refl 1)
    (fun _ _ hx _ _ hy => hx.mul_mul hy) (yunLoopAbs_forall₂ A hA n i b d hi hinv)

open Classical in
/-- Powered product of `[e₀,e₁,…]`: `∏ₖ eₖ^(i+k)`. -/
noncomputable def prodPow (i : ℕ) : List K[X] → K[X]
  | [] => 1
  | e :: es => e ^ i * prodPow (i + 1) es

open Classical in
/-- `prodPow` respects factorwise association. -/
theorem prodPow_associated {l₁ l₂ : List K[X]} (h : List.Forall₂ Associated l₁ l₂) (i : ℕ) :
    Associated (prodPow i l₁) (prodPow i l₂) := by
  induction h generalizing i with
  | nil => exact Associated.refl _
  | cons hhd _ ih => exact hhd.pow_pow.mul_mul (ih (i + 1))

open Classical in
/-- `prodPow` over an appended singleton raises the last factor to `i + L.length`. -/
theorem prodPow_append_singleton (i : ℕ) (L : List K[X]) (x : K[X]) :
    prodPow i (L ++ [x]) = prodPow i L * x ^ (i + L.length) := by
  induction L generalizing i with
  | nil => simp [prodPow]
  | cons a L ih =>
    rw [List.cons_append, prodPow, prodPow, ih (i + 1), List.length_cons,
      show i + 1 + L.length = i + (L.length + 1) from by omega]
    ring

open Classical in
/-- `prodPow i` of a `range` map is the corresponding `Finset.range` powered product. -/
theorem prodPow_range_map_eq_finset (i n : ℕ) (f : ℕ → K[X]) :
    prodPow i ((List.range n).map f) = ∏ k ∈ Finset.range n, f k ^ (i + k) := by
  induction n with
  | zero => simp [prodPow]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, prodPow_append_singleton,
      ih, Finset.prod_range_succ, List.length_map, List.length_range]

open Classical UniqueFactorizationMonoid in
/-- `prodPow` over enough squarefree parts reconstructs `A.primPart` up to association. -/
theorem prodPow_one_sqfreeFactPart_range_associated [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n : ℕ)
    (hn : (normalizedFactors A.primPart).toFinset.sup
      (fun P => (normalizedFactors A.primPart).count P) ≤ n) :
    Associated (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) A.primPart := by
  rw [prodPow_range_map_eq_finset]
  have hIco : ∏ k ∈ Finset.range n, sqfreeFactPart A (1 + k) ^ (1 + k)
      = ∏ m ∈ Finset.Ico 1 (n + 1), sqfreeFactPart A m ^ m := by
    rw [Finset.prod_Ico_eq_prod_range]
    exact (Finset.prod_congr (by rw [Nat.add_sub_cancel]) (fun k _ => rfl)).symm
  set image := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with himage
  have hsub : image ⊆ Finset.Ico 1 (n + 1) := by
    intro i hi
    rw [himage, Finset.mem_image] at hi
    obtain ⟨P, hP, rfl⟩ := hi
    rw [Finset.mem_Ico]
    refine ⟨Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hP), ?_⟩
    have : (normalizedFactors A.primPart).count P ≤ (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) :=
      Finset.le_sup (f := fun P => (normalizedFactors A.primPart).count P) hP
    omega
  have hoff : ∀ m ∈ Finset.Ico 1 (n + 1), m ∉ image → sqfreeFactPart A m ^ m = 1 := by
    intro m _ hm
    have h1 : sqfreeFactPart A m = 1 := by
      rw [sqfreeFactPart, Finset.prod_eq_one]
      intro P hP
      rw [Finset.mem_filter] at hP
      exact absurd (hP.2 ▸ Finset.mem_image_of_mem _ hP.1) hm
    rw [h1, one_pow]
  rw [hIco, ← Finset.prod_subset hsub hoff]
  exact (primPart_associated_prod_sqfreeFactPart A hA).symm

open Classical in
/-- The powered product of the abstract Yun loop matches the powered squarefree parts up to association. -/
theorem yunLoopAbs_prodPow_assoc [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (prodPow i (yunLoopAbs A (b, d) i n))
      (prodPow i ((List.range n).map (fun j => sqfreeFactPart A (i + j)))) :=
  prodPow_associated (yunLoopAbs_forall₂ A hA n i b d hi hinv) i

end SquarefreeYunStateLemmas

end DeepWiki.SymbolicIntegration
