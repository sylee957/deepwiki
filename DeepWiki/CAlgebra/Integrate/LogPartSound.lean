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

open DeepWiki.SymbolicIntegration in
/-- **Summed soundness of the log part**: over an algebraically closed field, for separable
`D` and a proper integrand, `A/D` equals the sum over the residues of
`a · logDeriv S(a, x)`, where `S` is the produced log argument covering `a` (and `1` at
non-residues). Together with `hermiteReduce`'s exports this is the full logarithmic stage
of rational integration. -/
theorem lrtLogTerms_sum_sound (b d : DensePoly R) (hd2 : 2 ≤ d.size)
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
/-- **The Hermite output feeds the log stage**: the `logPart` exported by `hermiteReduce`
satisfies every hypothesis of the summed log-part soundness — its denominator is squarefree
(hence separable over a perfect field) and the fraction is proper. Together with
`hermiteReduce_spec`, the engine's rational integration is theorem-backed end to end over
an algebraically closed field. -/
theorem hermiteReduce_logPart_sum_sound (f : DenseFrac R)
    (hnum : (hermiteReduce f).logPart.num ≠ 0) :
    DenseFrac.toRatFunc (hermiteReduce f).logPart
      = ∑ a ∈ (toPolynomial (hermiteReduce f).logPart.den.toPoly).roots.toFinset.image
            (fun α => (toPolynomial (hermiteReduce f).logPart.num).eval α
              / (Polynomial.derivative
                  (toPolynomial (hermiteReduce f).logPart.den.toPoly)).eval α),
          algebraMap (Polynomial R) (RatFunc R) (Polynomial.C a)
            * @Differential.logDeriv (RatFunc R) _
                SymbolicIntegration.instDifferentialRatFunc_deepWiki
                (algebraMap (Polynomial R) (RatFunc R)
                  (lrtLogArg (hermiteReduce f).logPart.num
                    (hermiteReduce f).logPart.den.toPoly a)) := by
  have hden0 : (hermiteReduce f).logPart.den.toPoly ≠ 0 := fun h0 => by
    have hm := (hermiteReduce f).logPart.den.monic
    rw [h0] at hm
    exact one_ne_zero (hm.symm.trans rfl)
  have hprop := hermiteReduce_logPart_isProper f
  have hdeg := RatFunc.degree_lt_of_isProper_of_eq_div (toPolynomial_ne_zero hden0)
    (x := DenseFrac.toRatFunc (hermiteReduce f).logPart) rfl hprop
  have hbd : (hermiteReduce f).logPart.num.size
      < (hermiteReduce f).logPart.den.toPoly.size := by
    have hn0 : toPolynomial (hermiteReduce f).logPart.num ≠ 0 := toPolynomial_ne_zero hnum
    have hdeg' : (toPolynomial (hermiteReduce f).logPart.num).natDegree
        < (toPolynomial (hermiteReduce f).logPart.den.toPoly).natDegree :=
      Polynomial.natDegree_lt_natDegree hn0 hdeg
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
      at hdeg'
    have h1 : (hermiteReduce f).logPart.num.size ≠ 0 := fun hz =>
      hnum (eq_zero_of_size_zero hz)
    have h2 : (hermiteReduce f).logPart.den.toPoly.size ≠ 0 := fun hz =>
      hden0 (eq_zero_of_size_zero hz)
    omega
  have hd2 : 2 ≤ (hermiteReduce f).logPart.den.toPoly.size := by
    have h1 : (hermiteReduce f).logPart.num.size ≠ 0 := fun hz =>
      hnum (eq_zero_of_size_zero hz)
    omega
  have hsep : (toPolynomial (hermiteReduce f).logPart.den.toPoly).Separable :=
    (PerfectField.separable_iff_squarefree).mpr
      (squarefree_toPolynomial_iff.mpr (hermiteReduce f).logPart_den_squarefree)
  rw [DenseFrac.toRatFunc]
  exact lrtLogTerms_sum_sound (hermiteReduce f).logPart.num
    (hermiteReduce f).logPart.den.toPoly hd2 hbd hsep

end Capstone

end DensePoly

end DeepWiki.CAlgebra