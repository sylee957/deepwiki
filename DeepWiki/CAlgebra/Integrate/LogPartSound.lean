import DeepWiki.CAlgebra.Integrate.LogPart
import DeepWiki.CAlgebra.Integrate.LogPartChain
import DeepWiki.CAlgebra.Integrate.LogPartMultiplicity
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtData
import DeepWiki.Algebra.SimilaritySpecialize
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtLogForm

/-! # Log-part soundness: the resultant square

Commuting squares from the computable Lazard–Rioboo–Trager pipeline
(`DeepWiki/CAlgebra/Integrate/LogPart`) into the engine-independent Rothstein–Trager layer
(`DeepWiki/SymbolicIntegration/RationalIntegrationAlgorithms/RothsteinTrager`). This file:
the dispatched bivariate resultant, read through the bridge, is the abstract
Rothstein–Trager resultant, and the walk endpoints specialize to the abstract LRT
output consumed through the `RtData` boundary record. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

open scoped Differential FormalDiff

section ResultantSquare

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R]

/-- **The Rothstein–Trager resultant square**: the engine's dispatched bivariate resultant,
read through `toPolynomial`, is the abstract Rothstein–Trager resultant `res_x(D, A − t·D′)`
at its canonical degrees. -/
theorem toPolynomial_rtResultant (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) :
    toPolynomial (rtResultant b d)
      = SymbolicIntegration.rtResultant (toPolynomial b) (toPolynomial d) := by
  have hm : (toPolynomial (liftX d)).natDegree = (toPolynomial d).natDegree := by
    rw [← toPolynomial₂_natDegree]
    exact liftX_natDegree₂ d
  have hn : (toPolynomial (liftX b - zC * liftX (d′))).natDegree
      = (toPolynomial d).natDegree - 1 := by
    rw [← toPolynomial₂_natDegree]
    exact operand_natDegree₂ b d hd2 hbd
  rw [rtResultant, DensePolyResultant.resultant_eq, hm, hn, toPolynomial_resultant₂,
    toPolynomial₂_liftX, operand_bridge, SymbolicIntegration.rtResultant]

end ResultantSquare

section Endpoint

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]

open DeepWiki.SymbolicIntegration in
/-- **The per-element endpoint** (gcd-free form): a dispatched sequence element,
specialized at any point where the determinantal LRT subresultant at the element's degree
survives, is similar to that specialized subresultant. The entry element is the top-index
subresultant on the nose; later elements specialize through primitivity. The
`gcd`-similarity composition happens in the abstract layer's own instance context. -/
theorem prs_elem_isSimilar_lrtSubresultant_eval (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) (a : R) (S : DensePoly (DensePoly R))
    (hS : S ∈ DensePolyPRS.prs (liftX d) (liftX b - zC * liftX (d′)))
    (hXa : (lrtSubresultant (toPolynomial b) (toPolynomial d)
        ((toPolynomial₂ S).natDegree)).map (Polynomial.evalRingHom a) ≠ 0) :
    IsSimilar ((toPolynomial₂ S).map (Polynomial.evalRingHom a))
      ((lrtSubresultant (toPolynomial b) (toPolynomial d)
        ((toPolynomial₂ S).natDegree)).map (Polynomial.evalRingHom a)) := by
  have hd0 : d ≠ 0 := fun h => by rw [h, size_zero] at hd2; omega
  have hopne : (liftX b - zC * liftX (d′)) ≠ 0 := operand_ne_zero b d hd2 hbd
  have hlxsize : (liftX d).size = d.size := liftX_size d
  have hopsize : (liftX b - zC * liftX (d′)).size = d.size - 1 := operand_size b d hd2 hbd
  have hident := entry_subresultant_eq_lrt b d hd2 hbd ((toPolynomial₂ S).natDegree)
  rcases prs_shape_mem _ _ S hS with hSg | ⟨prem, hprem0, hSzp⟩
  · -- the entry element IS the top-index subresultant (unit constants)
    have hid0 : lrtSubresultant (toPolynomial b) (toPolynomial d)
        ((toPolynomial₂ S).natDegree) = toPolynomial₂ S := by
      rw [← hident, hSg]
      have hdeq : (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree
          = (toPolynomial₂ (liftX d)).natDegree - 1 := by
        rw [operand_natDegree₂ b d hd2 hbd, liftX_natDegree₂]
      rw [hdeq]
      have hddeg : 1 ≤ (toPolynomial₂ (liftX d)).natDegree := by
        rw [natDegree₂_eq_size_sub_one, liftX_size]
        omega
      have hkey := subresultant_deg_ge_normal (toPolynomial₂ (liftX d))
        (toPolynomial₂ (liftX b - zC * liftX (d′)))
        (toPolynomial₂ (liftX d)).natDegree
        ((toPolynomial₂ (liftX d)).natDegree - 1)
        ((toPolynomial₂ (liftX d)).natDegree - 1)
        (le_of_eq hdeq) (by omega) (by omega) le_rfl
      rw [hkey, Nat.sub_self, show (toPolynomial₂ (liftX d)).natDegree
          - ((toPolynomial₂ (liftX d)).natDegree - 1) - 1 = 0 from by omega,
        pow_zero, pow_zero, one_mul, map_one, one_mul]
    rw [hid0]
  · -- a strict walk element: primitive, so the `K[t]`-similarity specializes
    have hsim0 := prs_mem_isSimilar_subresultant (liftX d) (liftX b - zC * liftX (d′))
      (by rw [hlxsize, hopsize]; omega) hopne S hS
    rw [hident] at hsim0
    have hcontent : (toPolynomial₂ S).content = 1 := by
      rw [hSzp]
      exact content_toPolynomial₂_zPrimitive hprem0
    exact isSimilar_map_eval_of_content_eq_one a hcontent hsim0.symm hXa

end Endpoint

/-! ### The capstone: soundness of the produced log terms -/

section Capstone

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

open DeepWiki.SymbolicIntegration in
/-- **Soundness of the Lazard–Rioboo–Trager log terms**: over an algebraically closed
field, for every pair `(Q, S)` the algorithm produces and every root `a` of `Q`, the
specialized bridged log argument is similar to the Rothstein–Trager residue gcd
`rtLogGcd A D a = gcd(D, A − a·D′)` — so `a · log S(a, x)` contributes exactly the
residue-`a` part of `∫ A/D`. -/
theorem lrtLogTerms_isSimilar_gcd (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) (hdsep : (toPolynomial d).Separable)
    {Q : DensePoly R} {S : DensePoly (DensePoly R)}
    (hmem : (Q, S) ∈ lrtLogTerms b d) {a : R} (haQ : (toPolynomial Q).IsRoot a) :
    IsSimilar ((toPolynomial₂ S).map (Polynomial.evalRingHom a))
      (rtLogGcd (toPolynomial b) (toPolynomial d) a) := by
  have hd0 : d ≠ 0 := fun h => by rw [h, size_zero] at hd2; omega
  have hD0 : toPolynomial d ≠ 0 := toPolynomial_ne_zero hd0
  have hA : (toPolynomial b).natDegree < (toPolynomial d).natDegree := by
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  -- unpack the membership
  simp only [lrtLogTerms, List.mem_filterMap] at hmem
  obtain ⟨Qi, hQiMem, hQiEq⟩ := hmem
  by_cases hQsz : Qi.1.size ≤ 1
  · rw [if_pos hQsz] at hQiEq
    exact absurd hQiEq (by simp)
  rw [if_neg hQsz] at hQiEq
  have hpair := Option.some.inj hQiEq
  have hQeq : Qi.1 = Q := congrArg Prod.fst hpair
  have hSeq := congrArg Prod.snd hpair
  dsimp only at hSeq
  obtain ⟨j, hjlen, hQiget⟩ := List.exists_mem_zipIdx.mp ⟨Qi, hQiMem, rfl⟩
  have hQi1 : (DensePolySquarefree.sqfDecomp (rtResultant b d))[j] = Qi.1 :=
    (congrArg Prod.fst hQiget).symm
  have hQi2 : j = Qi.2 := by
    have h := congrArg Prod.snd hQiget
    simp only at h
    omega
  have hrtne : rtResultant b d ≠ 0 := by
    intro h0
    apply rtResultant_ne_zero (toPolynomial b) (toPolynomial d) hdsep hA
    rw [← toPolynomial_rtResultant b d hd2 hbd, h0, toPolynomial_zero]
  have hmul : (SymbolicIntegration.rtResultant (toPolynomial b)
      (toPolynomial d)).rootMultiplicity a = j + 1 := by
    rw [← toPolynomial_rtResultant b d hd2 hbd]
    refine rootMultiplicity_of_sqfDecomp_root hrtne hjlen ?_
    rw [hQi1, hQeq]
    exact haQ
  have hile : j + 1 ≤ (toPolynomial d).natDegree := by
    rw [← hmul]
    exact (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).rootMultiplicity_le
  have hile' : j + 1 ≤ d.size - 1 := by
    rw [natDegree_toPolynomial_eq_size_sub_one] at hile
    exact hile
  have hgcdeq := rtData_gcdVal (toPolynomial b) (toPolynomial d) hdsep hA a
  have hgne := (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).ne_zero
  have hgdeg := (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).natDegree_eq
  have hsim := (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).output_sim
  rw [hgcdeq] at hgne hgdeg hsim
  by_cases hfall : Qi.2 + 2 = d.size
  · -- fallback: `S = liftX d`, multiplicity `deg D`
    rw [if_pos hfall] at hSeq
    have hieq : (SymbolicIntegration.rtResultant (toPolynomial b)
        (toPolynomial d)).rootMultiplicity a = (toPolynomial d).natDegree := by
      rw [hmul, natDegree_toPolynomial_eq_size_sub_one]
      omega
    rw [if_pos hieq] at hsim
    have hmapid : (toPolynomial₂ S).map (Polynomial.evalRingHom a)
        = ((toPolynomial d).map Polynomial.C).map (Polynomial.evalRingHom a) := by
      rw [← hSeq, toPolynomial₂_liftX]
    rw [hmapid]
    exact hsim
  · -- the `find?` branch
    rw [if_neg hfall] at hSeq
    have hilt : (SymbolicIntegration.rtResultant (toPolynomial b)
        (toPolynomial d)).rootMultiplicity a < (toPolynomial d).natDegree := by
      rw [hmul, natDegree_toPolynomial_eq_size_sub_one]
      omega
    rw [if_neg (ne_of_lt hilt)] at hsim
    have hXane : (lrtSubresultant (toPolynomial b) (toPolynomial d)
        ((SymbolicIntegration.rtResultant (toPolynomial b)
          (toPolynomial d)).rootMultiplicity a)).map (Polynomial.evalRingHom a) ≠ 0 := by
      intro h0
      obtain ⟨u1, u2, hu1, hu2, hueq⟩ := hsim
      rw [h0, mul_zero] at hueq
      rcases mul_eq_zero.mp hueq.symm with h | h
      · rw [Polynomial.C_eq_zero] at h
        exact hu2 h
      · exact hgne h
    have hdeg_spec : ((lrtSubresultant (toPolynomial b) (toPolynomial d)
        ((SymbolicIntegration.rtResultant (toPolynomial b)
          (toPolynomial d)).rootMultiplicity a)).map
          (Polynomial.evalRingHom a)).natDegree = j + 1 := by
      rw [hsim.natDegree_eq, hgdeg, hmul]
    rcases hfind : (DensePolyPRS.prs (liftX d)
        (liftX b - zC * liftX (d′))).find? (fun S' => S'.size = Qi.2 + 2) with _ | S₀
    · -- impossible: coverage produces the element `find?` would have found
      exfalso
      have hpsc : (subresultant (toPolynomial₂ (liftX d))
          (toPolynomial₂ (liftX b - zC * liftX (d′)))
          (toPolynomial₂ (liftX d)).natDegree
          (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree (j + 1)).coeff (j + 1)
            ≠ 0 := by
        rw [entry_subresultant_eq_lrt b d hd2 hbd]
        intro h0
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hXane
        rw [Polynomial.leadingCoeff, hdeg_spec, Polynomial.coeff_map, hmul, h0,
          map_zero] at hlc
        exact hlc rfl
      obtain ⟨S', hS'mem, hS'sz⟩ := prs_covers (liftX d) (liftX b - zC * liftX (d′))
        (by rw [liftX_size d, operand_size b d hd2 hbd]; omega)
        (operand_ne_zero b d hd2 hbd) (j + 1)
        (by rw [operand_size b d hd2 hbd]; omega) hpsc
      have hnone := List.find?_eq_none.mp hfind S' hS'mem
      simp only [decide_eq_true_eq] at hnone
      exact hnone (by omega)
    · -- found: compose the endpoint with the abstract similarity
      rw [hfind] at hSeq
      dsimp only at hSeq
      have hS₀mem := List.mem_of_find?_eq_some hfind
      have hS₀sz : S₀.size = Qi.2 + 2 := by
        have := List.find?_some hfind
        simpa using this
      have hS₀deg : (toPolynomial₂ S₀).natDegree
          = (SymbolicIntegration.rtResultant (toPolynomial b)
              (toPolynomial d)).rootMultiplicity a := by
        rw [natDegree₂_eq_size_sub_one, hS₀sz, hmul]
        omega
      have hspec := prs_elem_isSimilar_lrtSubresultant_eval b d hd2 hbd a S₀ hS₀mem
        (by rw [hS₀deg]; exact hXane)
      rw [hS₀deg] at hspec
      rw [← hSeq]
      exact hspec.trans hsim

open DeepWiki.SymbolicIntegration in
/-- The specialized log argument covering the residue `a`: the produced `S` of a pair whose
`Q` has `a` as a root, specialized at `a` — and `1` when no pair covers `a` (non-residues). -/
noncomputable def lrtLogArg (b d : DensePoly R) (a : R) : Polynomial R :=
  if h : ∃ QS ∈ lrtLogTerms b d, (toPolynomial QS.1).IsRoot a
  then (toPolynomial₂ h.choose.2).map (Polynomial.evalRingHom a)
  else 1

/-- The residues of a canonical fraction: `A(α)/D′(α)` over the roots of `D`. -/
noncomputable def residueSet (g : DenseFrac R) : Finset R :=
  (toPolynomial g.den.toPoly).roots.toFinset.image
    (fun α => (toPolynomial g.num).eval α
      / (Polynomial.derivative (toPolynomial g.den.toPoly)).eval α)

omit [CharZero R] [DensePolyGcd R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- Membership reading of `residueSet`: the residues are the values `A(α)/D′(α)` at
roots `α` of `D`. -/
theorem mem_residueSet_iff {g : DenseFrac R} {a : R} :
    a ∈ residueSet g ↔ ∃ α ∈ (toPolynomial g.den.toPoly).roots.toFinset,
      (toPolynomial g.num).eval α
        / (Polynomial.derivative (toPolynomial g.den.toPoly)).eval α = a := by
  simp [residueSet]

open DeepWiki.SymbolicIntegration in
/-- One log term of the LRT output: `a · logDeriv S(a, x)`, with the log-derivative's
`Differential` instance baked in (the instance-boundary discipline, as for `rtLogGcd`). -/
noncomputable def lrtLogTerm (g : DenseFrac R) (a : R) : RatFunc R :=
  algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
    * @Differential.logDeriv (RatFunc R) _
        SymbolicIntegration.instDifferentialRatFunc_deepWiki
        (algebraMap (Polynomial R) (RatFunc R) (lrtLogArg g.num g.den.toPoly a))

open DeepWiki.SymbolicIntegration in
omit [CharZero R] [IsAlgClosed R] in
/-- Unfolding reading of `lrtLogTerm`. -/
theorem lrtLogTerm_def (g : DenseFrac R) (a : R) :
    lrtLogTerm g a
      = algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
        * @Differential.logDeriv (RatFunc R) _
            SymbolicIntegration.instDifferentialRatFunc_deepWiki
            (algebraMap (Polynomial R) (RatFunc R) (lrtLogArg g.num g.den.toPoly a)) :=
  rfl

open DeepWiki.SymbolicIntegration in
/-- The derivative of the formal sum of logarithms `∑_{a ∈ s} a · log (u a)` — residues
as coefficients, polynomial log arguments. `log` itself does not exist in `RatFunc R`;
`∑ a · logDeriv (u a)` is its differential-algebra reading, with the `Differential`
instance baked in. -/
noncomputable def logSumDeriv (s : Finset R) (u : R → Polynomial R) : RatFunc R :=
  ∑ a ∈ s, algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
    * @Differential.logDeriv (RatFunc R) _
        SymbolicIntegration.instDifferentialRatFunc_deepWiki
        (algebraMap (Polynomial R) (RatFunc R) (u a))

omit [CharZero R] [IsAlgClosed R] in
/-- The LRT log sum's derivative is the sum of the log terms. -/
theorem logSumDeriv_lrtLogArg (g : DenseFrac R) :
    logSumDeriv (residueSet g) (lrtLogArg g.num g.den.toPoly)
      = ∑ a ∈ residueSet g, lrtLogTerm g a := rfl

/-- Sum of `f α` over the distinct roots of `Q`. -/
noncomputable def rootSum (Q : Polynomial R) (f : R → RatFunc R) : RatFunc R :=
  ∑ α ∈ Q.roots.toFinset, f α

open DeepWiki.SymbolicIntegration in
/-- The root-sum log term of one produced pair `(Q, S)`: the derivative of
`∑_{Q(α)=0} α · log S(α, x)` — the classical `RootSum` presentation of one log-term
class, with no residue selection. -/
noncomputable def lrtPairTerm (QS : DensePoly R × DensePoly (DensePoly R)) : RatFunc R :=
  rootSum (toPolynomial QS.1) fun α =>
    algebraMap (Polynomial R) (RatFunc R) (Polynomial.C α)
      * @Differential.logDeriv (RatFunc R) _
          SymbolicIntegration.instDifferentialRatFunc_deepWiki
          (algebraMap (Polynomial R) (RatFunc R)
            ((toPolynomial₂ QS.2).map (Polynomial.evalRingHom α)))

private theorem getElem_mul_getElem_dvd_prod {M : Type*} [CommMonoid M] :
    ∀ (l : List M) (j k : ℕ), ∀ (hj : j < l.length) (hk : k < l.length), j ≠ k →
      l[j] * l[k] ∣ l.prod := by
  intro l
  induction l with
  | nil => intro j k hj; simp at hj
  | cons a t ih =>
      intro j k hj hk hne
      rcases j with _ | j <;> rcases k with _ | k
      · omega
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
        exact mul_dvd_mul_left a (List.dvd_prod (List.getElem_mem _))
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
        rw [mul_comm]
        exact mul_dvd_mul_left a (List.dvd_prod (List.getElem_mem _))
      · simp only [List.getElem_cons_succ, List.prod_cons]
        exact Dvd.dvd.mul_left
          (ih j k (by simpa using hj) (by simpa using hk) (by omega)) a

omit [IsAlgClosed R] in
/-- Distinct squarefree-decomposition factors share no root (the plain factor product is
squarefree). -/
private theorem sqfDecomp_no_common_root {p : DensePoly R} (hp : p ≠ 0) {j k : ℕ}
    (hj : j < (DensePolySquarefree.sqfDecomp p).length)
    (hk : k < (DensePolySquarefree.sqfDecomp p).length) (hne : j ≠ k) {α : R}
    (hrj : (toPolynomial (DensePolySquarefree.sqfDecomp p)[j]).IsRoot α)
    (hrk : (toPolynomial (DensePolySquarefree.sqfDecomp p)[k]).IsRoot α) : False := by
  set L := DensePolySquarefree.sqfDecomp p with hL
  have hsf : Squarefree (toPolynomial L.prod) :=
    squarefree_toPolynomial_iff.mpr
      (squarefree_of_associated (DensePolySquarefree.associated_prod hp)
        (squarefree_sqfreePart hp))
  have hdvd : toPolynomial L[j] * toPolynomial L[k] ∣ toPolynomial L.prod := by
    rw [← toPolynomial_mul]
    exact map_dvd (equiv (R := R) : DensePoly R →+* Polynomial R)
      (getElem_mul_getElem_dvd_prod L j k hj hk hne)
  have hsq : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C α)
      ∣ toPolynomial L.prod :=
    dvd_trans (mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hrj)
      (Polynomial.dvd_iff_isRoot.mpr hrk)) hdvd
  exact Polynomial.not_isUnit_X_sub_C α (hsf _ hsq)

omit [CharZero R] [IsAlgClosed R] in
/-- A member of `lrtLogTerms` is the image of a decomposition index. -/
private theorem exists_index_of_mem_lrtLogTerms {b d : DensePoly R}
    {QS : DensePoly R × DensePoly (DensePoly R)} (h : QS ∈ lrtLogTerms b d) :
    ∃ j, ∃ hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length,
      QS.1 = (DensePolySquarefree.sqfDecomp (rtResultant b d))[j] := by
  rw [lrtLogTerms, List.mem_filterMap] at h
  obtain ⟨Qi, hQi, hf⟩ := h
  obtain ⟨j, hjlen, hgot⟩ := List.mem_iff_getElem.mp hQi
  have hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hjlen
  have hQi_eq : Qi = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
    rw [← hgot, List.getElem_zipIdx]
    simp
  subst hQi_eq
  dsimp only at hf
  by_cases hsz : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1
  · rw [if_pos hsz] at hf
    simp at hf
  · rw [if_neg hsz, Option.some_inj] at hf
    exact ⟨j, hj, by rw [← hf]⟩

omit [IsAlgClosed R] in
/-- **Covering uniqueness**: two produced pairs sharing a root coincide. -/
private theorem lrt_covering_unique {b d : DensePoly R}
    (hrt : rtResultant b d ≠ 0) {QS QS' : DensePoly R × DensePoly (DensePoly R)}
    (h1 : QS ∈ lrtLogTerms b d) (h2 : QS' ∈ lrtLogTerms b d) {α : R}
    (hr1 : (toPolynomial QS.1).IsRoot α) (hr2 : (toPolynomial QS'.1).IsRoot α) :
    QS = QS' := by
  rw [lrtLogTerms, List.mem_filterMap] at h1 h2
  obtain ⟨Qi, hQi, hf1⟩ := h1
  obtain ⟨Qi', hQi', hf2⟩ := h2
  obtain ⟨j, hjlen, hgot⟩ := List.mem_iff_getElem.mp hQi
  obtain ⟨k, hklen, hgot'⟩ := List.mem_iff_getElem.mp hQi'
  have hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hjlen
  have hk : k < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hklen
  have hQi_eq : Qi = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
    rw [← hgot, List.getElem_zipIdx]; simp
  have hQi'_eq : Qi' = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[k], k) := by
    rw [← hgot', List.getElem_zipIdx]; simp
  subst hQi_eq
  subst hQi'_eq
  dsimp only at hf1 hf2
  by_cases hsz1 : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1
  · rw [if_pos hsz1] at hf1
    simp at hf1
  by_cases hsz2 : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[k]).size ≤ 1
  · rw [if_pos hsz2] at hf2
    simp at hf2
  rw [if_neg hsz1, Option.some_inj] at hf1
  rw [if_neg hsz2, Option.some_inj] at hf2
  rcases eq_or_ne j k with rfl | hne
  · rw [← hf1, ← hf2]
  · rw [← hf1] at hr1
    rw [← hf2] at hr2
    exact absurd (sqfDecomp_no_common_root hrt hj hk hne hr1 hr2) not_false

omit [IsAlgClosed R] in
/-- The produced log argument at a covered residue is the covering pair's
specialization. -/
private theorem lrtLogArg_eq_of_mem {b d : DensePoly R} (hrt : rtResultant b d ≠ 0)
    {QS : DensePoly R × DensePoly (DensePoly R)} (hmem : QS ∈ lrtLogTerms b d) {α : R}
    (hroot : (toPolynomial QS.1).IsRoot α) :
    lrtLogArg b d α = (toPolynomial₂ QS.2).map (Polynomial.evalRingHom α) := by
  have hex : ∃ QS' ∈ lrtLogTerms b d, (toPolynomial QS'.1).IsRoot α := ⟨QS, hmem, hroot⟩
  rw [lrtLogArg, dif_pos hex,
    lrt_covering_unique hrt hex.choose_spec.1 hmem hex.choose_spec.2 hroot]

omit [CharZero R] [IsAlgClosed R] in
/-- The `j`-th nonconstant decomposition factor yields a produced pair. -/
private theorem mem_lrtLogTerms_of_index {b d : DensePoly R} {j : ℕ}
    (hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length)
    (hsz : ¬ ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1) :
    ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j],
      if j + 2 = d.size then liftX d
      else match (DensePolyPRS.prs (liftX d)
          (liftX b - zC * liftX (d′))).find? (fun S => S.size = j + 2) with
        | some S => S
        | none => liftX d) ∈ lrtLogTerms b d := by
  rw [lrtLogTerms, List.mem_filterMap]
  refine ⟨((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j), ?_, ?_⟩
  · have hlen : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx.length := by
      simpa using hj
    have hget : (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx[j]
        = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
      rw [List.getElem_zipIdx]
      simp
    rw [← hget]
    exact List.getElem_mem hlen
  · dsimp only
    rw [if_neg hsz]
    rfl

private theorem sum_map_filterMap {α β M : Type*} [AddCommMonoid M]
    (f : α → Option β) (g : β → M) :
    ∀ l : List α, ((l.filterMap f).map g).sum
      = (l.map fun a => ((f a).map g).getD 0).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      rcases hfa : f a with _ | b
      · rw [List.filterMap_cons_none hfa, List.map_cons, List.sum_cons, hfa]
        simpa using ih
      · rw [List.filterMap_cons_some hfa, List.map_cons, List.sum_cons, List.map_cons,
          List.sum_cons, hfa]
        simp only [Option.map_some, Option.getD_some]
        rw [ih]

private theorem sum_map_zipIdx {α M : Type*} [AddCommMonoid M] (h : α × ℕ → M) (d₀ : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map h).sum
      = ∑ j ∈ Finset.range l.length, h (l.getD j d₀, n + j) := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons a t ih =>
      intro n
      rw [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons,
        Finset.sum_range_succ', ih (n + 1)]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show n + 1 + j = n + (j + 1) from by omega]

/-- **The regrouping**: the residue-indexed sum of log terms is the pair-indexed sum of
root-sum terms. -/
private theorem residue_sum_eq_pair_sum (g : DenseFrac R) (hnum : g.num ≠ 0)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    ∑ a ∈ residueSet g, lrtLogTerm g a
      = ((lrtLogTerms g.num g.den.toPoly).map lrtPairTerm).sum := by
  have hden0 : g.den.toPoly ≠ 0 := g.den.ne_zero
  have hdeg := RatFunc.degree_lt_of_isProper_of_eq_div (toPolynomial_ne_zero hden0)
    (x := DenseFrac.toRatFunc g) rfl hprop
  have hbd : g.num.size < g.den.toPoly.size := by
    have hn0 : toPolynomial g.num ≠ 0 := toPolynomial_ne_zero hnum
    have hdeg' : (toPolynomial g.num).natDegree
        < (toPolynomial g.den.toPoly).natDegree :=
      Polynomial.natDegree_lt_natDegree hn0 hdeg
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
      at hdeg'
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    have h2 : g.den.toPoly.size ≠ 0 := fun hz => hden0 (eq_zero_of_size_zero hz)
    omega
  have hd2 : 2 ≤ g.den.toPoly.size := by
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    omega
  have hsep : (toPolynomial g.den.toPoly).Separable :=
    (PerfectField.separable_iff_squarefree).mpr (squarefree_toPolynomial_iff.mpr hsf)
  have hA : (toPolynomial g.num).natDegree < (toPolynomial g.den.toPoly).natDegree := by
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  have hrtabs := SymbolicIntegration.rtResultant_ne_zero (toPolynomial g.num)
    (toPolynomial g.den.toPoly) hsep hA
  have hrt : rtResultant g.num g.den.toPoly ≠ 0 := fun h0 => hrtabs (by
    rw [← toPolynomial_rtResultant g.num g.den.toPoly hd2 hbd, h0, toPolynomial_zero])
  set L := DensePolySquarefree.sqfDecomp (rtResultant g.num g.den.toPoly) with hLdef
  have hQne : ∀ (j : ℕ) (hj : j < L.length), toPolynomial (L[j]'hj) ≠ 0 := fun j hj =>
    toPolynomial_ne_zero
      (DensePolySquarefree.squarefree_of_mem (List.getElem_mem hj)).ne_zero
  -- the residue set is the disjoint union of the factor root sets
  have hres : residueSet g = (Finset.range L.length).biUnion
      (fun j => (toPolynomial (L.getD j 0)).roots.toFinset) := by
    have hres0 : residueSet g
        = (SymbolicIntegration.rtResultant (toPolynomial g.num)
            (toPolynomial g.den.toPoly)).roots.toFinset := by
      unfold residueSet
      ext α
      have h := Finset.ext_iff.mp (SymbolicIntegration.image_residue_eq_roots_rtResultant
        (toPolynomial g.num) (toPolynomial g.den.toPoly) hsep hA) α
      simp only [Finset.mem_image, Multiset.mem_toFinset] at h ⊢
      exact h
    rw [hres0]
    ext α
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hrtabs, Finset.mem_biUnion]
    constructor
    · intro hα
      have hroot : (toPolynomial (rtResultant g.num g.den.toPoly)).IsRoot α := by
        rw [toPolynomial_rtResultant g.num g.den.toPoly hd2 hbd]
        exact hα
      obtain ⟨j, hj, hjr⟩ := exists_sqfDecomp_root_of_isRoot hrt hroot
      refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
        Multiset.mem_toFinset, Polynomial.mem_roots (hQne _ hj)]
      exact hjr
    · rintro ⟨j, hjr, hα⟩
      rw [Finset.mem_range] at hjr
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some,
        Multiset.mem_toFinset, Polynomial.mem_roots (hQne _ hjr)] at hα
      have hmul := rootMultiplicity_of_sqfDecomp_root hrt hjr hα
      have hroot : (toPolynomial (rtResultant g.num g.den.toPoly)).IsRoot α :=
        (Polynomial.rootMultiplicity_pos (toPolynomial_ne_zero hrt)).mp
          (by rw [hmul]; omega)
      rw [← toPolynomial_rtResultant g.num g.den.toPoly hd2 hbd]
      exact hroot
  have hdisj : (Finset.range L.length : Set ℕ).PairwiseDisjoint
      (fun j => (toPolynomial (L.getD j 0)).roots.toFinset) := by
    intro j hj k hk hne
    rw [Finset.coe_range, Set.mem_Iio] at hj hk
    refine Finset.disjoint_left.mpr fun α h1 h2 => ?_
    dsimp only at h1 h2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
      Multiset.mem_toFinset, Polynomial.mem_roots (hQne _ hj)] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some,
      Multiset.mem_toFinset, Polynomial.mem_roots (hQne _ hk)] at h2
    exact absurd (sqfDecomp_no_common_root hrt hj hk hne h1 h2) not_false
  rw [hres, Finset.sum_biUnion hdisj, lrtLogTerms, sum_map_filterMap,
    sum_map_zipIdx _ 0]
  refine Finset.sum_congr rfl fun j hjr => ?_
  rw [Finset.mem_range] at hjr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some]
  dsimp only
  rw [zero_add]
  by_cases hsz : (L[j]).size ≤ 1
  · rw [if_pos hsz]
    have hdeg0 : (toPolynomial L[j]).natDegree = 0 := by
      rw [natDegree_toPolynomial_eq_size_sub_one]
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
    rw [← hc, Polynomial.roots_C]
    simp
  · rw [if_neg hsz]
    simp only [Option.map_some, Option.getD_some]
    rw [lrtPairTerm, rootSum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hQne _ hjr)] at hα
    rw [lrtLogTerm_def,
      lrtLogArg_eq_of_mem hrt (mem_lrtLogTerms_of_index hjr hsz) hα]
    rfl

open DeepWiki.SymbolicIntegration in
/-- Raw core of the summed log-part soundness, on a numerator/denominator pair with size
and separability hypotheses; the public form is `lrtLogTerms_sum_sound`. -/
private theorem lrtLogTerms_sum_sound_core (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) (hdsep : (toPolynomial d).Separable) :
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial b)
        / algebraMap (Polynomial R) (RatFunc R) (toPolynomial d)
      = ∑ a ∈ (toPolynomial d).roots.toFinset.image
            (fun α => (toPolynomial b).eval α
              / (Polynomial.derivative (toPolynomial d)).eval α),
          algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
            * @Differential.logDeriv (RatFunc R) _
                SymbolicIntegration.instDifferentialRatFunc_deepWiki
                (algebraMap (Polynomial R) (RatFunc R) (lrtLogArg b d a)) := by
  have hd0 : d ≠ 0 := fun h => by rw [h, size_zero] at hd2; omega
  have hD0 : toPolynomial d ≠ 0 := toPolynomial_ne_zero hd0
  have hA : (toPolynomial b).natDegree < (toPolynomial d).natDegree := by
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  refine (ratFunc_eq_sum_rtLogGcd (toPolynomial b) (toPolynomial d) hdsep hA
    (lrtLogArg b d) ?_).trans ?_
  swap
  · -- the index set is instance-independent
    apply Finset.sum_congr
    · ext x
      simp [Finset.mem_image, Multiset.mem_toFinset]
    · intro x _
      rfl
  intro a
  rw [lrtLogArg]
  split
  case isTrue h =>
    exact lrtLogTerms_isSimilar_gcd b d hd2 hbd hdsep h.choose_spec.1 h.choose_spec.2
  case isFalse h =>
    -- `a` is not a residue: the gcd is a nonzero constant, similar to `1`
    have hgcdeq := rtData_gcdVal (toPolynomial b) (toPolynomial d) hdsep hA a
    have hgne := (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).ne_zero
    have hgdeg := (rtData (toPolynomial b) (toPolynomial d) hdsep hA a).natDegree_eq
    rw [hgcdeq] at hgne hgdeg
    have hmul0 : (SymbolicIntegration.rtResultant (toPolynomial b)
        (toPolynomial d)).rootMultiplicity a = 0 := by
      by_contra hne
      have hrtabsne := rtResultant_ne_zero (toPolynomial b) (toPolynomial d) hdsep hA
      have hrtne : rtResultant b d ≠ 0 := by
        intro h0
        apply hrtabsne
        rw [← toPolynomial_rtResultant b d hd2 hbd, h0, toPolynomial_zero]
      have hroot : (toPolynomial (rtResultant b d)).IsRoot a := by
        have hpos : 0 < (SymbolicIntegration.rtResultant (toPolynomial b)
            (toPolynomial d)).rootMultiplicity a := Nat.pos_of_ne_zero hne
        rw [toPolynomial_rtResultant b d hd2 hbd]
        exact (Polynomial.rootMultiplicity_pos hrtabsne).mp hpos
      obtain ⟨j, hj, hjroot⟩ := exists_sqfDecomp_root_of_isRoot hrtne hroot
      have hfsz : ¬ (DensePolySquarefree.sqfDecomp (rtResultant b d))[j].size ≤ 1 := by
        intro hsz
        rcases Nat.lt_or_ge (DensePolySquarefree.sqfDecomp (rtResultant b d))[j].size 1
          with h1 | h1
        · have : (DensePolySquarefree.sqfDecomp (rtResultant b d))[j] = 0 :=
            eq_zero_of_size_zero (by omega)
          rw [this, toPolynomial_zero] at hjroot
          exact (DensePolySquarefree.squarefree_of_mem
            (List.getElem_mem hj)).ne_zero this
        · have hsz1 : (DensePolySquarefree.sqfDecomp (rtResultant b d))[j].size = 1 := by
            omega
          have hC := eq_C_of_size_eq_one hsz1
          rw [hC, toPolynomial_C] at hjroot
          have hc0 : (DensePolySquarefree.sqfDecomp (rtResultant b d))[j].coeff 0 = 0 := by
            simpa [Polynomial.IsRoot] using hjroot
          apply (DensePolySquarefree.squarefree_of_mem (List.getElem_mem hj)).ne_zero
          apply toPolynomial_injective
          rw [hC, hc0, toPolynomial_C, map_zero, toPolynomial_zero]
      apply h
      refine ⟨((DensePolySquarefree.sqfDecomp (rtResultant b d))[j],
        if j + 2 = d.size then liftX d
        else match (DensePolyPRS.prs (liftX d)
            (liftX b - zC * liftX (d′))).find? (fun S' => S'.size = j + 2) with
          | some S₀ => S₀
          | none => liftX d), ?_, hjroot⟩
      simp only [lrtLogTerms, List.mem_filterMap]
      refine ⟨((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j), ?_, ?_⟩
      · have hlen : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx.length := by
          rw [List.length_zipIdx]
          exact hj
        have hget : (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx[j]
            = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
          rw [List.getElem_zipIdx]
          simp
        rw [← hget]
        exact List.getElem_mem hlen
      · rw [if_neg hfsz]
        rfl
    have hgdeg0 : (rtLogGcd (toPolynomial b) (toPolynomial d) a).natDegree = 0 := by
      rw [hgdeg, hmul0]
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hgdeg0
    have hcne : c ≠ 0 := by
      intro h0
      apply hgne
      rw [← hc, h0, map_zero]
    exact ⟨c, 1, hcne, one_ne_zero, by rw [← hc, map_one, one_mul, mul_one]⟩

open DeepWiki.SymbolicIntegration in
/-- **Summed soundness of the log part — the fraction is the derivative of a sum of
logarithms**: over an algebraically closed field, a proper canonical fraction with
squarefree denominator and nonzero numerator is the (formal) derivative of
`∑_{a ∈ residues} a · log S(a, x)`, where `S` is the produced log argument covering `a`
(and `1` at non-residues). The hypotheses are exactly `hermiteReduce`'s exports
(`logPart_isProper`, `logPart_den_squarefree`), so the logarithmic stage applies to the
Hermite output directly — the engine's rational integration is theorem-backed end to end. -/
theorem lrtLogTerms_sum_sound (g : DenseFrac R) (hnum : g.num ≠ 0)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    DenseFrac.toRatFunc g
      = logSumDeriv (residueSet g) (lrtLogArg g.num g.den.toPoly) := by
  have hden0 : g.den.toPoly ≠ 0 := g.den.ne_zero
  have hdeg := RatFunc.degree_lt_of_isProper_of_eq_div (toPolynomial_ne_zero hden0)
    (x := DenseFrac.toRatFunc g) rfl hprop
  have hbd : g.num.size < g.den.toPoly.size := by
    have hn0 : toPolynomial g.num ≠ 0 := toPolynomial_ne_zero hnum
    have hdeg' : (toPolynomial g.num).natDegree
        < (toPolynomial g.den.toPoly).natDegree :=
      Polynomial.natDegree_lt_natDegree hn0 hdeg
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
      at hdeg'
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    have h2 : g.den.toPoly.size ≠ 0 := fun hz => hden0 (eq_zero_of_size_zero hz)
    omega
  have hd2 : 2 ≤ g.den.toPoly.size := by
    have h1 : g.num.size ≠ 0 := fun hz => hnum (eq_zero_of_size_zero hz)
    omega
  have hsep : (toPolynomial g.den.toPoly).Separable :=
    (PerfectField.separable_iff_squarefree).mpr (squarefree_toPolynomial_iff.mpr hsf)
  rw [DenseFrac.toRatFunc]
  exact lrtLogTerms_sum_sound_core g.num g.den.toPoly hd2 hbd hsep

open DeepWiki.SymbolicIntegration in
/-- **The derivative of an LRT result**: the formal derivative of the represented sum of
logarithms `∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)`, read in `RatFunc R` — the record's
denotation. -/
noncomputable def LrtResult.deriv (res : LrtResult R) : RatFunc R :=
  (res.terms.map lrtPairTerm).sum

open DeepWiki.SymbolicIntegration in
/-- **Soundness of the bundled LRT stage**: `D(∫ g) = g` — the derivative of the produced
`RootSum` data `∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)` is the fraction, with no residue
selection and the log data over the base field. The hypotheses are exactly
`hermiteReduce`'s exports. -/
theorem lrtIntegrate_sound (g : DenseFrac R) (hnum : g.num ≠ 0)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    (lrtIntegrate g).deriv = DenseFrac.toRatFunc g := by
  rw [lrtLogTerms_sum_sound g hnum hsf hprop, logSumDeriv_lrtLogArg]
  exact (residue_sum_eq_pair_sum g hnum hsf hprop).symm

end Capstone

end DensePoly

end DeepWiki.CAlgebra