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

/-- The `i`-th **principal subresultant coefficient** `sᵢ ∈ K[t]`: the leading `x`-coefficient
`(lrtSubresultant A D i).coeff i` of the `i`-th LRT subresultant, viewed as a polynomial in `t`. Its
specialization at `a` is the top coefficient of the specialized subresultant
(`lrtPsc_eval`). -/
noncomputable def lrtPsc (A D : K[X]) (i : ℕ) : K[X] := (lrtSubresultant A D i).coeff i

omit [IsAlgClosed K] in
/-- **Specialization of the principal subresultant coefficient**: `sᵢ(a) = (lrtPsc A D i).eval a` equals
the `i`-th coefficient of the specialized subresultant `Sᵢ(D, A − a·D')` — `coeff_map` for `t ↦ a`. -/
theorem lrtPsc_eval (A D : K[X]) (i : ℕ) (a : K) :
    (lrtPsc A D i).eval a
      = ((lrtSubresultant A D i).map (Polynomial.evalRingHom a)).coeff i := by
  rw [lrtPsc, Polynomial.coeff_map]
  simp only [Polynomial.coe_evalRingHom]

open scoped Classical in
/-- The distinct **residues of multiplicity exactly `i`** in the Rothstein–Trager resultant
`R = rtResultant A D`: the roots `a` of `R` with `rootMultiplicity a R = i`. These are the values the LRT
algorithm groups under one degree-`i` subresultant. -/
noncomputable def residueSetOfMult (A D : K[X]) (i : ℕ) : Finset K :=
  (rtResultant A D).roots.toFinset.filter (fun a => (rtResultant A D).rootMultiplicity a = i)

open scoped Classical in
/-- **`Qᵢ`**, the multiplicity-`i` factor of the Rothstein–Trager resultant: the monic squarefree
`Qᵢ := ∏_{a : rootMult a R = i}(t − a)` over the distinct residues of multiplicity exactly `i`
(a divisor of `R`'s radical, hence squarefree). -/
noncomputable def lrtQ (A D : K[X]) (i : ℕ) : K[X] :=
  (residueSetOfMult A D i).prod (fun a => X - C a)

open scoped Classical in
/-- **Exercise 2.7, the unit-in-`K[t]/(Qᵢ)` packaging**: the `i`-th principal subresultant coefficient
`sᵢ = lrtPsc A D i` is **coprime** to the multiplicity-`i` factor `Qᵢ = lrtQ A D i` (for `0 < i < deg D`),
i.e. `sᵢ` is a **unit in `K[t]/(Qᵢ)`** — exactly what makes monic-normalizing the LRT logarithm arguments
legitimate. Each linear factor `t − a` of `Qᵢ` has `a` a residue of multiplicity `i`, so by the regularity
core `leadingCoeff_lrtSubresultant_eval_ne_zero` (through `lrtPsc_eval`) `sᵢ(a) ≠ 0`, i.e. `t − a ∤ sᵢ`;
since `t − a` is prime, `sᵢ` is coprime to it (`Prime.coprime_iff_not_dvd` + `dvd_iff_isRoot`), and
`IsCoprime.prod_right` folds this over the factors of `Qᵢ`. -/
theorem isCoprime_lrtPsc_lrtQ
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (i : ℕ) (hi : i < D.natDegree) :
    IsCoprime (lrtPsc A D i) (lrtQ A D i) := by
  rw [lrtQ]
  refine IsCoprime.prod_right (fun a hain => ?_)
  rw [residueSetOfMult, Finset.mem_filter, Multiset.mem_toFinset] at hain
  obtain ⟨haroot, hamult⟩ := hain
  -- `a` is a root of `R` (so `IsRoot`) of multiplicity `i`
  have hRne : rtResultant A D ≠ 0 := fun h => by
    rw [h, Polynomial.roots_zero] at haroot; exact absurd haroot (Multiset.notMem_zero a)
  have haR : (rtResultant A D).IsRoot a := by
    rw [← Polynomial.mem_roots hRne]; exact haroot
  have hi' : (rtResultant A D).rootMultiplicity a < D.natDegree := hamult ▸ hi
  -- `sᵢ(a) ≠ 0` from the regularity core, then `t − a` is coprime to `sᵢ`
  have hne : (lrtPsc A D i).eval a ≠ 0 := by
    rw [lrtPsc_eval, ← hamult]
    exact leadingCoeff_lrtSubresultant_eval_ne_zero A D hD hA a haR hi'
  refine ((Polynomial.prime_X_sub_C a).coprime_iff_not_dvd.mpr ?_).symm
  rw [Polynomial.dvd_iff_isRoot]
  exact hne

open scoped Classical in
-- `sᵢ` is a unit in `K[t]/(Qᵢ)` (coprime to `Qᵢ`) — Exercise 2.7's required fact.
example (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (i : ℕ) (hi : i < D.natDegree) :
    IsCoprime (lrtPsc A D i) (lrtQ A D i) :=
  isCoprime_lrtPsc_lrtQ A D hD hA i hi

end DeepWiki.SymbolicIntegration
