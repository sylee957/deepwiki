import DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness

/-! # LRT monic-log regularity (Bronstein §2 Exercise 2.7, the reachable core)
Exercise 2.7 asks to modify Lazard–Rioboo–Trager so the polynomials inside the logarithms are *monic*
in `x`; this is possible exactly because, at a residue `a` of multiplicity `i` in the Rothstein–Trager
resultant `R`, the specialized `i`-th LRT subresultant has `x`-degree *exactly* `i`, so its leading
`x`-coefficient — the `i`-th principal subresultant coefficient — is nonzero there. This file proves
that regularity (`leadingCoeff_lrtSubresultant_eval_ne_zero`) from the existing similarity
(`lazardRiobooTrager_isSimilar_gcd`) and multiplicity (`rootMultiplicity_rtResultant_eq_natDegree_gcd`)
bridges, and packages it as coprimality of the principal subresultant coefficient (over `K[t]`) to the
distinct-residue factor `Qᵢ := ∏_{a : rootMult a R = i}(t − a)`, the "unit in `K[t]/(Qᵢ)`" fact. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K] [IsAlgClosed K]

open scoped Classical in
/-- **Exercise 2.7, the regularity core**: at a residue `a` (a root of the Rothstein–Trager resultant
`R = rtResultant A D`) of multiplicity `i < deg D`, the specialized `i`-th LRT subresultant has `x`-degree
*exactly* `i`, so its leading `x`-coefficient — the `i`-th principal subresultant coefficient `sᵢ(a)` — is
**nonzero**. From `lazardRiobooTrager_isSimilar_gcd` (the specialized subresultant is *similar* to
`gcd(D, A − a·D')`), `IsSimilar.natDegree_eq` gives `deg = deg gcd`, and
`rootMultiplicity_rtResultant_eq_natDegree_gcd` rewrites `deg gcd = rootMultiplicity a R = i`; since `a`
is a root of `R`, `i ≥ 1 > 0`, so the polynomial is nonzero and its top coefficient is its (nonzero)
leading coefficient. -/
theorem leadingCoeff_lrtSubresultant_eval_ne_zero
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (ha : (rtResultant A D).IsRoot a)
    (hi : (rtResultant A D).rootMultiplicity a < D.natDegree) :
    ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a)).coeff ((rtResultant A D).rootMultiplicity a) ≠ 0 := by
  set i := (rtResultant A D).rootMultiplicity a with hidef
  set S := (lrtSubresultant A D i).map (Polynomial.evalRingHom a) with hS
  have hD0 : D ≠ 0 := hD.ne_zero
  -- `R ≠ 0`: its `K[t]`-product form is a nonzero scalar times monic-ish linear factors (each
  -- `C(A α) − X·C(D'α)` has nonzero `X`-coefficient `−C(D'α)`, as `D'(α) ≠ 0` by separability).
  have hRne : rtResultant A D ≠ 0 := by
    rw [rtResultant_eq_prod_roots A D hA]
    refine mul_ne_zero (pow_ne_zero _ ?_) (Multiset.prod_ne_zero ?_)
    · exact fun h => hD0 (by simpa [C_eq_zero, leadingCoeff_eq_zero] using h)
    · intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨α, hα, hαeq⟩ := hmem
      have hdα : (derivative D).eval α ≠ 0 := by
        have hr : D.IsRoot α := (mem_roots hD0).mp hα
        have := hD.eval₂_derivative_ne_zero (RingHom.id K)
          (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hr)
        simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
      apply hdα
      have hcoeff := congrArg (fun p => Polynomial.coeff p 1) hαeq
      simpa [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C] using hcoeff.symm
  -- `a` is a genuine root, so its multiplicity `i` is positive.
  have hipos : 0 < i := by
    rw [hidef]; exact (rootMultiplicity_pos hRne).mpr ha
  -- the specialized subresultant is similar to the Rothstein–Trager gcd ⟹ same `natDegree`
  have hsim := lazardRiobooTrager_isSimilar_gcd A D hD hA a hi
  have hdeg : S.natDegree = (gcd D (A - C a * derivative D)).natDegree := hsim.natDegree_eq
  -- the multiplicity bridge: `deg gcd = i`
  have hmul : (gcd D (A - C a * derivative D)).natDegree = i :=
    (rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a).symm
  have hSdeg : S.natDegree = i := hdeg.trans hmul
  -- `deg S = i > 0`, so `S ≠ 0` and its `i`-th coefficient is its nonzero leading coefficient
  have hSne : S ≠ 0 := fun h => by simp [h] at hSdeg; omega
  rw [← hSdeg, ← leadingCoeff]
  exact leadingCoeff_ne_zero.mpr hSne

open scoped Classical in
-- The `i`-th principal subresultant coefficient is nonzero at a multiplicity-`i` residue (`i < deg D`).
example (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (ha : (rtResultant A D).IsRoot a)
    (hi : (rtResultant A D).rootMultiplicity a < D.natDegree) :
    ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a)).coeff ((rtResultant A D).rootMultiplicity a) ≠ 0 :=
  leadingCoeff_lrtSubresultant_eval_ne_zero A D hD hA a ha hi

end DeepWiki.SymbolicIntegration
