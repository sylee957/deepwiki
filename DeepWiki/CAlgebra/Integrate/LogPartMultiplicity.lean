import DeepWiki.CAlgebra.Integrate.LogPart

/-! # The multiplicity bridge

Roots of the dispatched squarefree-decomposition factors, read through `toPolynomial`:
a root of the `j`-th factor is a root of the input with multiplicity exactly `j + 1`,
and every root arises this way. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

/-! ### The multiplicity bridge: roots of squarefree-decomposition factors -/

section MultBridge

variable {R : Type u} [Field R]

/-- The staircase power product over Mathlib polynomials (the `powProd` mirror). -/
private noncomputable def powProdP : List (Polynomial R) → ℕ → Polynomial R
  | [], _ => 1
  | f :: L, n => f ^ n * powProdP L (n + 1)

private theorem powProdP_ne_zero {L : List (Polynomial R)} (h0 : ∀ f ∈ L, f ≠ 0) (n : ℕ) :
    powProdP L n ≠ 0 := by
  induction L generalizing n with
  | nil => exact one_ne_zero
  | cons f T ih =>
      exact mul_ne_zero (pow_ne_zero _ (h0 f List.mem_cons_self))
        (ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx)) (n + 1))

private theorem rootMultiplicity_pow' (f : Polynomial R) (hf : f ≠ 0) (a : R) (n : ℕ) :
    (f ^ n).rootMultiplicity a = n * f.rootMultiplicity a := by
  induction n with
  | zero =>
      rw [pow_zero, zero_mul]
      exact Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
      ring

private theorem rootMultiplicity_eq_one_of_squarefree {f : Polynomial R}
    (hsf : Squarefree f) (a : R) (hroot : f.IsRoot a) : f.rootMultiplicity a = 1 := by
  have hf0 : f ≠ 0 := hsf.ne_zero
  have h1 : 0 < f.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hf0).mpr hroot
  by_contra hne
  have h2 : 2 ≤ f.rootMultiplicity a := by omega
  have hdvd : (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a) ∣ f :=
    dvd_trans (by rw [← sq]; exact pow_dvd_pow _ h2)
      (Polynomial.pow_rootMultiplicity_dvd f a)
  exact Polynomial.not_isUnit_X_sub_C a (hsf _ hdvd)

private theorem isRoot_powProdP {L : List (Polynomial R)} {n : ℕ} (hn : 1 ≤ n) (a : R)
    (h0 : ∀ f ∈ L, f ≠ 0) :
    (powProdP L n).IsRoot a ↔ ∃ f ∈ L, f.IsRoot a := by
  induction L generalizing n with
  | nil =>
      simp [powProdP, Polynomial.IsRoot]
  | cons f T ih =>
      show (f ^ n * powProdP T (n + 1)).IsRoot a ↔ _
      rw [show ∀ q : Polynomial R, q.IsRoot a ↔ Polynomial.eval a q = 0 from fun q => Iff.rfl]
      rw [Polynomial.eval_mul, Polynomial.eval_pow, mul_eq_zero,
        pow_eq_zero_iff (by omega : n ≠ 0)]
      constructor
      · rintro (h | h)
        · exact ⟨f, List.mem_cons_self, h⟩
        · obtain ⟨g, hgT, hgr⟩ := (ih (by omega)
            (fun x hx => h0 x (List.mem_cons_of_mem _ hx))).mp h
          exact ⟨g, List.mem_cons_of_mem _ hgT, hgr⟩
      · rintro ⟨g, hg, hgr⟩
        rcases List.mem_cons.mp hg with rfl | hgT
        · exact Or.inl hgr
        · exact Or.inr ((ih (by omega)
            (fun x hx => h0 x (List.mem_cons_of_mem _ hx))).mpr ⟨g, hgT, hgr⟩)

private theorem rootMultiplicity_powProdP {L : List (Polynomial R)}
    (hsf : Squarefree L.prod) (a : R) {j : ℕ} (hj : j < L.length)
    (hroot : (L[j]).IsRoot a) (n : ℕ) (hn : 1 ≤ n) :
    (powProdP L n).rootMultiplicity a = n + j := by
  induction L generalizing n j with
  | nil => simp at hj
  | cons f T ih =>
      have hprod0 : (f :: T).prod ≠ 0 := hsf.ne_zero
      have hf0 : f ≠ 0 := fun h => hprod0 (by rw [List.prod_cons, h, zero_mul])
      have hT0 : T.prod ≠ 0 := fun h => hprod0 (by rw [List.prod_cons, h, mul_zero])
      have hTe0 : ∀ g ∈ T, g ≠ 0 := fun g hg h0 =>
        hT0 (List.prod_eq_zero (h0 ▸ hg))
      have hmulsplit : (powProdP (f :: T) n).rootMultiplicity a
          = n * f.rootMultiplicity a + (powProdP T (n + 1)).rootMultiplicity a := by
        show (f ^ n * powProdP T (n + 1)).rootMultiplicity a = _
        rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf0)
          (powProdP_ne_zero hTe0 _)), rootMultiplicity_pow' f hf0]
      rcases j with _ | j'
      · have hfr : f.IsRoot a := by simpa using hroot
        have hf1 : f.rootMultiplicity a = 1 :=
          rootMultiplicity_eq_one_of_squarefree
            (hsf.squarefree_of_dvd (by rw [List.prod_cons]; exact dvd_mul_right _ _))
            a hfr
        have hTnot : ¬ (powProdP T (n + 1)).IsRoot a := by
          rw [isRoot_powProdP (by omega) a hTe0]
          rintro ⟨g, hgT, hgr⟩
          have hd : (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a)
              ∣ (f :: T).prod := by
            rw [List.prod_cons]
            exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hfr)
              (dvd_trans (Polynomial.dvd_iff_isRoot.mpr hgr) (List.dvd_prod hgT))
          exact Polynomial.not_isUnit_X_sub_C a (hsf _ hd)
        rw [hmulsplit, hf1, Polynomial.rootMultiplicity_eq_zero hTnot]
        omega
      · have hj' : j' < T.length := by simpa using hj
        have hTj : (T[j']).IsRoot a := by simpa using hroot
        have hfnot : ¬ f.IsRoot a := by
          intro hfr
          have hd : (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a)
              ∣ (f :: T).prod := by
            rw [List.prod_cons]
            exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hfr)
              (dvd_trans (Polynomial.dvd_iff_isRoot.mpr hTj)
                (List.dvd_prod (List.getElem_mem hj')))
          exact Polynomial.not_isUnit_X_sub_C a (hsf _ hd)
        have hsfT : Squarefree T.prod :=
          hsf.squarefree_of_dvd (by rw [List.prod_cons]; exact dvd_mul_left _ _)
        rw [hmulsplit, Polynomial.rootMultiplicity_eq_zero hfnot,
          ih hsfT hj' hTj (n + 1) (by omega)]
        omega

private theorem rootMultiplicity_eq_of_associated {p q : Polynomial R}
    (h : Associated p q) (hp : p ≠ 0) (a : R) :
    p.rootMultiplicity a = q.rootMultiplicity a := by
  obtain ⟨u, hu⟩ := h
  have hune : (↑u : Polynomial R) ≠ 0 := Units.ne_zero u
  have hnotroot : ¬ (↑u : Polynomial R).IsRoot a := by
    obtain ⟨r, hru, hrC⟩ := Polynomial.isUnit_iff.mp u.isUnit
    rw [← hrC]
    simpa [Polynomial.IsRoot] using hru.ne_zero
  rw [← hu, Polynomial.rootMultiplicity_mul (by rw [hu]; exact fun h0 => hp (by
    rw [← hu] at h0
    exact (mul_eq_zero.mp h0).elim id (fun hc => absurd hc hune))),
    Polynomial.rootMultiplicity_eq_zero hnotroot, add_zero]

end MultBridge

section SqfMult

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R]

omit [CharZero R] [DensePolyGcd R] [DensePolySquarefree R] in
private theorem toPolynomial_powProd (L : List (DensePoly R)) (n : ℕ) :
    toPolynomial (powProd L n) = powProdP (L.map toPolynomial) n := by
  induction L generalizing n with
  | nil =>
      show toPolynomial 1 = 1
      exact toPolynomial_one
  | cons f T ih =>
      show toPolynomial (f ^ n * powProd T (n + 1)) = _
      rw [toPolynomial_mul, ih]
      show toPolynomial (f ^ n) * _ = (toPolynomial f) ^ n * _
      rw [show toPolynomial (f ^ n) = (toPolynomial f) ^ n from map_pow (equiv (R := R)) f n]

/-- **The multiplicity readout of the dispatched squarefree decomposition**: a root of the
`j`-th factor is a root of the input with multiplicity exactly `j + 1`. -/
theorem rootMultiplicity_of_sqfDecomp_root {p : DensePoly R} (hp : p ≠ 0) {j : ℕ}
    (hj : j < (DensePolySquarefree.sqfDecomp p).length) {a : R}
    (hroot : (toPolynomial (DensePolySquarefree.sqfDecomp p)[j]).IsRoot a) :
    (toPolynomial p).rootMultiplicity a = j + 1 := by
  set L := DensePolySquarefree.sqfDecomp p with hL
  -- the bridged factor list and its squarefree product
  have hfac0 : ∀ f ∈ L.map toPolynomial, f ≠ 0 := by
    intro f hf
    obtain ⟨g, hgL, rfl⟩ := List.mem_map.mp hf
    exact toPolynomial_ne_zero
      (DensePolySquarefree.squarefree_of_mem hgL).ne_zero
  have hprodbr : (L.map toPolynomial).prod = toPolynomial L.prod :=
    (map_list_prod ((equiv (R := R)) : DensePoly R →+* Polynomial R) L).symm
  have hsfprod : Squarefree ((L.map toPolynomial).prod) := by
    rw [hprodbr]
    have hassoc := DensePolySquarefree.associated_prod (p := p) hp
    have hsfpart : Squarefree (toPolynomial (sqfreePart p)) :=
      squarefree_toPolynomial_iff.mpr (squarefree_sqfreePart hp)
    exact hsfpart.squarefree_of_dvd
      (map_dvd ((equiv (R := R)) : DensePoly R →+* Polynomial R) hassoc.symm.dvd)
  -- transport the multiplicity along `p ~ powProd L 1`
  have hassocp := DensePolySquarefree.associated_powProd (p := p) hp
  have hassocbr : Associated (toPolynomial p) (powProdP (L.map toPolynomial) 1) := by
    rw [← toPolynomial_powProd]
    exact hassocp.map ((equiv (R := R)) : DensePoly R →+* Polynomial R)
  rw [rootMultiplicity_eq_of_associated hassocbr (toPolynomial_ne_zero hp) a,
    rootMultiplicity_powProdP hsfprod a (by simpa using hj)
      (by rw [List.getElem_map]; exact hroot) 1 le_rfl]
  omega

omit [CharZero R] in
/-- A root of the input is a root of some dispatched squarefree-decomposition factor. -/
theorem exists_sqfDecomp_root_of_isRoot {p : DensePoly R} (hp : p ≠ 0) {a : R}
    (ha : (toPolynomial p).IsRoot a) :
    ∃ j, ∃ _ : j < (DensePolySquarefree.sqfDecomp p).length,
      (toPolynomial (DensePolySquarefree.sqfDecomp p)[j]).IsRoot a := by
  set L := DensePolySquarefree.sqfDecomp p with hL
  have hfac0 : ∀ f ∈ L.map toPolynomial, f ≠ 0 := by
    intro f hf
    obtain ⟨g0, hg0L, rfl⟩ := List.mem_map.mp hf
    exact toPolynomial_ne_zero (DensePolySquarefree.squarefree_of_mem hg0L).ne_zero
  have hassocbr : Associated (toPolynomial p) (powProdP (L.map toPolynomial) 1) := by
    rw [← toPolynomial_powProd]
    exact (DensePolySquarefree.associated_powProd (p := p) hp).map
      ((equiv (R := R)) : DensePoly R →+* Polynomial R)
  have hroot2 : (powProdP (L.map toPolynomial) 1).IsRoot a := by
    rw [← Polynomial.dvd_iff_isRoot] at ha ⊢
    exact dvd_trans ha hassocbr.dvd
  obtain ⟨f, hfmem, hfroot⟩ := (isRoot_powProdP le_rfl a hfac0).mp hroot2
  obtain ⟨g0, hg0mem, rfl⟩ := List.mem_map.mp hfmem
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hg0mem
  exact ⟨j, hj, by rw [hjeq]; exact hfroot⟩

end SqfMult

end DensePoly

end DeepWiki.CAlgebra
