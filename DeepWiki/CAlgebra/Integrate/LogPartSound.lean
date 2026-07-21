import DeepWiki.CAlgebra.Integrate.LogPart
import DeepWiki.CAlgebra.Integrate.LogPartChain
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LazardRiobooTragerCorrectness
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtLogForm

/-! # Log-part soundness: the resultant square

Commuting squares from the computable Lazard–Rioboo–Trager pipeline
(`DeepWiki/CAlgebra/Integrate/LogPart`) into the engine-independent Rothstein–Trager layer
(`DeepWiki/SymbolicIntegration/RationalIntegrationAlgorithms/RothsteinTrager`). This file:
the dispatched bivariate resultant, read through the bridge, is the abstract
Rothstein–Trager resultant. A deliberate leaf — the determinantal theory it imports stays
off the computable pipeline's import cone. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

open scoped Differential FormalDiff

section ResultantSquare

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R]

omit [CharZero R] in
/-- The bridged second operand. -/
theorem operand_bridge (b d : DensePoly R) :
    toPolynomial₂ (liftX b - zC * liftX (d′))
      = (toPolynomial b).map Polynomial.C
        - Polynomial.C Polynomial.X
          * (Polynomial.derivative (toPolynomial d)).map Polynomial.C := by
  rw [toPolynomial₂_sub, toPolynomial₂_mul, toPolynomial₂_liftX, toPolynomial₂_liftX,
    toPolynomial₂_zC, toPolynomial_deriv]

omit [CharZero R] in
/-- The `x`-lift of a nonzero polynomial is nonzero. -/
theorem liftX_ne_zero {d : DensePoly R} (hd0 : d ≠ 0) : liftX d ≠ 0 := fun h0 => by
  have h1 := toPolynomial₂_liftX d
  rw [h0, toPolynomial₂_zero] at h1
  have h2 := (Polynomial.map_eq_zero_iff Polynomial.C_injective).mp h1.symm
  exact hd0 (toPolynomial_injective (by rw [h2, toPolynomial_zero]))

omit [CharZero R] in
/-- The `x`-lift preserves the size. -/
theorem liftX_size (d : DensePoly R) : (liftX d).size = d.size := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rfl
  · have h1 : (toPolynomial₂ (liftX d)).natDegree = (toPolynomial d).natDegree := by
      rw [toPolynomial₂_liftX,
        Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    rw [natDegree₂_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one] at h1
    have h2 : (liftX d).size ≠ 0 := fun h0 => liftX_ne_zero hd0 (eq_zero_of_size_zero h0)
    have h3 : d.size ≠ 0 := fun h0 => hd0 (eq_zero_of_size_zero h0)
    omega

omit [CharZero R] in
/-- Degree corollary of `liftX_size`. -/
theorem liftX_natDegree₂ (d : DensePoly R) :
    (toPolynomial₂ (liftX d)).natDegree = (toPolynomial d).natDegree := by
  rw [natDegree₂_eq_size_sub_one, liftX_size, natDegree_toPolynomial_eq_size_sub_one]

/-- The second operand is nonzero. -/
theorem operand_ne_zero (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (liftX b - zC * liftX (d′)) ≠ 0 := by
  intro h0
  refine SymbolicIntegration.rtResultant_operand_coeff_ne_zero (toPolynomial b)
    (toPolynomial d) ?_ ?_
  · rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  · rw [← operand_bridge, h0, toPolynomial₂_zero, Polynomial.coeff_zero]

/-- Bridged corollary of `operand_ne_zero`. -/
theorem operand_ne_zero₂ (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    toPolynomial₂ (liftX b - zC * liftX (d′)) ≠ 0 :=
  toPolynomial₂_ne_zero (operand_ne_zero b d hd2 hbd)

/-- The second operand's size is `d.size − 1`. -/
theorem operand_size (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (liftX b - zC * liftX (d′)).size = d.size - 1 := by
  have h1 : (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree
      = (toPolynomial d).natDegree - 1 := by
    rw [operand_bridge]
    refine SymbolicIntegration.natDegree_rtResultant_operand _ _ ?_
    rw [natDegree_toPolynomial_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one]
    omega
  rw [natDegree₂_eq_size_sub_one, natDegree_toPolynomial_eq_size_sub_one] at h1
  have h2 : (liftX b - zC * liftX (d′)).size ≠ 0 := fun h0 =>
    operand_ne_zero b d hd2 hbd (eq_zero_of_size_zero h0)
  omega

/-- Degree corollary of `operand_size`. -/
theorem operand_natDegree₂ (b d : DensePoly R) (hd2 : 2 ≤ d.size) (hbd : b.size < d.size) :
    (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree
      = (toPolynomial d).natDegree - 1 := by
  rw [natDegree₂_eq_size_sub_one, operand_size b d hd2 hbd,
    natDegree_toPolynomial_eq_size_sub_one]

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

/-! ### The chain view of the dispatched sequence -/

section Chain

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open DeepWiki.SymbolicIntegration in
/-- **The dispatched sequence element is similar to the determinantal subresultant at its
own degree** (the Lazard–Rioboo–Trager similarity square, generic entry): for a
size-ordered entry pair, the `k`-th element (`k ≥ 1`) of the dispatched bivariate sequence,
read through the bridge, is `IsSimilar` to the subresultant of the bridged entry pair at
the element's degree. -/
theorem prs_isSimilar_subresultant (f g : DensePoly (DensePoly R))
    (hfg : g.size ≤ f.size) (k : ℕ) (S : DensePoly (DensePoly R)) (hk : 1 ≤ k)
    (hS : (DensePolyPRS.prs f g)[k]? = some S) :
    IsSimilar
      (subresultant (toPolynomial₂ f) (toPolynomial₂ g)
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree
        ((toPolynomial₂ S).natDegree))
      (toPolynomial₂ S) := by
  have w := WalkData.ofGetElem? f g hfg hS
  have hSz : S = zChain f g (k + 1) := prs_getElem?_eq_zChain f g k S hS
  have hm2 : k - 1 + 2 = k + 1 := by omega
  have happ := subresultant_prs_similar_elt (walkF f g) (walkAlpha f g) (walkBeta f g)
    (walkQ f g) (k - 1)
    (fun l hl => w.alpha_ne_zero l (by omega))
    (fun l hl => w.beta_ne_zero l (by omega))
    (fun l hl => w.F_lc_ne_zero l (by omega))
    (fun l hl => w.F_deg_step l (by omega))
    (fun l hl => by rw [hm2]; exact w.F_deg_last_lt l (by omega))
    (fun l hl => w.Q_deg_le l (by omega))
    w.rel
    (by rw [hm2]; exact w.F_ne_zero k le_rfl)
  rw [hm2] at happ
  rw [hSz]
  simpa only [walkF, zChain_zero, zChain_one] using happ

open DeepWiki.SymbolicIntegration in
/-- **Every dispatched sequence element is similar to the entry subresultant at its own
degree** — the membership form of the similarity square, covering the entry element itself
(`k = 0`, via the degenerate closed form `subresultant_deg_ge_normal`) and every later
element (via the chain telescope). -/
theorem prs_mem_isSimilar_subresultant (f g : DensePoly (DensePoly R))
    (hfg : g.size < f.size) (hg0 : g ≠ 0) (S : DensePoly (DensePoly R))
    (hS : S ∈ DensePolyPRS.prs f g) :
    IsSimilar
      (subresultant (toPolynomial₂ f) (toPolynomial₂ g)
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree
        ((toPolynomial₂ S).natDegree))
      (toPolynomial₂ S) := by
  obtain ⟨k, hk, hkS⟩ := List.getElem_of_mem hS
  have hS? : (DensePolyPRS.prs f g)[k]? = some S := by
    rw [List.getElem?_eq_getElem hk, hkS]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have hSg : S = g := by simpa using prs_getElem?_eq_zChain f g 0 S hS?
    subst hSg
    have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hfg; omega
    have hgsz : S.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
    have hda : (toPolynomial₂ f).natDegree = f.size - 1 := by
      rw [natDegree₂_eq_size_sub_one]
    have hdb : (toPolynomial₂ S).natDegree = S.size - 1 := by
      rw [natDegree₂_eq_size_sub_one]
    have hkey := subresultant_deg_ge_normal (toPolynomial₂ f) (toPolynomial₂ S)
      (toPolynomial₂ f).natDegree (toPolynomial₂ S).natDegree
      (toPolynomial₂ S).natDegree le_rfl (by omega) (by omega) le_rfl
    exact ⟨1,
      (toPolynomial₂ f).coeff ((toPolynomial₂ f).natDegree)
          ^ ((toPolynomial₂ S).natDegree - (toPolynomial₂ S).natDegree)
        * (toPolynomial₂ S).coeff ((toPolynomial₂ S).natDegree)
          ^ ((toPolynomial₂ f).natDegree - (toPolynomial₂ S).natDegree - 1),
      one_ne_zero,
      mul_ne_zero
        (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr (toPolynomial₂_ne_zero hf0)))
        (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr (toPolynomial₂_ne_zero hg0))),
      by rw [map_one, one_mul, hkey]⟩
  · exact prs_isSimilar_subresultant f g (le_of_lt hfg) k S hk1 hS?

open DeepWiki.SymbolicIntegration in
/-- **Walk coverage**: if the `i`-th principal subresultant coefficient of the bridged
entry pair is nonzero, the dispatched sequence contains an element of `x`-degree `i` —
the vanishing and defective alternatives would force that coefficient to zero. -/
theorem prs_covers (f g : DensePoly (DensePoly R)) (hfg : g.size ≤ f.size) (hg0 : g ≠ 0)
    (i : ℕ) (hi : i + 1 ≤ g.size)
    (hpsc : (subresultant (toPolynomial₂ f) (toPolynomial₂ g)
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree i).coeff i ≠ 0) :
    ∃ S ∈ DensePolyPRS.prs f g, S.size = i + 1 := by
  suffices H : ∀ n (f g : DensePoly (DensePoly R)), g.size = n → g.size ≤ f.size → g ≠ 0 →
      ∀ i, i + 1 ≤ g.size →
      (subresultant (toPolynomial₂ f) (toPolynomial₂ g)
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree i).coeff i ≠ 0 →
      ∃ S ∈ DensePolyPRS.prs f g, S.size = i + 1 by
    exact H g.size f g rfl hfg hg0 i hi hpsc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f g hgs hfg hg0 i hi hpsc
  have hgsz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hfg; omega
  have hmem_g : g ∈ DensePolyPRS.prs f g := by
    rw [prs_z_eq, if_neg hgsz]
    exact List.mem_cons_self
  rcases eq_or_ne (i + 1) g.size with hieq | hine
  · exact ⟨g, hmem_g, hieq.symm⟩
  have hilt : i + 1 < g.size := by omega
  have hda : (toPolynomial₂ f).natDegree = f.size - 1 := by
    rw [natDegree₂_eq_size_sub_one]
  have hdb : (toPolynomial₂ g).natDegree = g.size - 1 := by
    rw [natDegree₂_eq_size_sub_one]
  -- coefficient-extraction helpers
  have hkill : ∀ (v : Polynomial R) (S P : Polynomial (Polynomial R)),
      v ≠ 0 → Polynomial.C v * S = P → P.coeff i = 0 → S.coeff i = 0 := by
    intro v S P hv hSP hP
    have := congrArg (fun q => Polynomial.coeff q i) hSP
    simp only [Polynomial.coeff_C_mul] at this
    rw [hP] at this
    exact (mul_eq_zero.mp this).resolve_left hv
  have hshape : ∀ (N : ℕ) (u : Polynomial R) (P : Polynomial (Polynomial R)),
      P.coeff i = 0 →
      ((-1 : Polynomial (Polynomial R)) ^ N * (Polynomial.C u * P)).coeff i = 0 := by
    intro N u P hP
    rw [show ((-1 : Polynomial (Polynomial R)) ^ N)
        = Polynomial.C ((-1 : Polynomial R) ^ N) from by rw [map_pow, map_neg, map_one]]
    simp only [Polynomial.coeff_C_mul, hP, mul_zero]
  have hval : ∀ (N n2 : ℕ) (u v : Polynomial R) (P : Polynomial (Polynomial R)),
      ((-1 : Polynomial (Polynomial R)) ^ N
          * ((Polynomial.C u) ^ n2 * (Polynomial.C v * P))).coeff i
        = (-1 : Polynomial R) ^ N * (u ^ n2 * (v * P.coeff i)) := by
    intro N n2 u v P
    rw [show ((-1 : Polynomial (Polynomial R)) ^ N)
        = Polynomial.C ((-1 : Polynomial R) ^ N) from by rw [map_pow, map_neg, map_one],
      show ((Polynomial.C u : Polynomial (Polynomial R)) ^ n2)
        = Polynomial.C (u ^ n2) from (map_pow _ _ _).symm]
    simp only [Polynomial.coeff_C_mul]
  -- the bridged pseudo-division identity and the quotient degree bound
  have hid := walk_step_identity f g hgsz
  set α₀ : Polynomial R := toPolynomial (g.leadingCoeff ^ (f.size + 1 - g.size)) with hα₀def
  have hα₀ : α₀ ≠ 0 :=
    toPolynomial_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero hgsz))
  have hQb := walk_step_Q_deg f g hfg hg0
  rcases eq_or_ne (pseudoMod f g) 0 with hprem | hprem
  · -- terminal step: `C α₀ · f = g · Q`; every strictly lower index has vanishing psc
    exfalso
    have hrel : Polynomial.C α₀ * toPolynomial₂ f
        = Polynomial.C (1 : Polynomial R) * 0
          + toPolynomial₂ g * toPolynomial₂ (pseudoDiv f g) := by
      rw [map_one, one_mul, zero_add]
      rw [hprem, toPolynomial₂_zero, add_zero] at hid
      rw [← hid]
      ring
    rcases eq_or_ne i ((toPolynomial₂ g).natDegree - 1) with htop | hnottop
    · subst htop
      have h := subresultant_prs_step_top (toPolynomial₂ f) (toPolynomial₂ g) 0
        (toPolynomial₂ (pseudoDiv f g)) α₀ 1
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree 0
        one_ne_zero (by rw [hdb]; omega) Polynomial.natDegree_zero le_rfl hQb hrel
      exact hpsc (hkill α₀ _ _ hα₀ h (hshape _ _ _ (by simp)))
    rcases eq_or_ne i 0 with hzero | hpos
    · subst hzero
      have h := subresultant_prs_step_deg (toPolynomial₂ f) (toPolynomial₂ g) 0
        (toPolynomial₂ (pseudoDiv f g)) α₀ 1
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree 0
        one_ne_zero (by rw [hdb]; omega) Polynomial.natDegree_zero le_rfl hQb hrel
      exact hpsc (hkill (α₀ ^ _) _ _ (pow_ne_zero _ hα₀) h (hshape _ _ _ (by simp)))
    · have h := subresultant_prs_step_gap (toPolynomial₂ f) (toPolynomial₂ g) 0
        (toPolynomial₂ (pseudoDiv f g)) α₀ 1
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree 0 i
        hα₀ one_ne_zero (by omega) (by rw [hdb]; omega)
        Polynomial.natDegree_zero le_rfl hQb hrel
      exact hpsc (by rw [h, Polynomial.coeff_zero])
  · -- live step: found, recurse, or vanish
    set r := zStep f g with hr
    have hrne : r ≠ 0 := by
      intro h0
      apply hprem
      have hcz := C_zContent_mul_zPrimitive (pseudoMod f g)
      rw [← hcz, show zPrimitive (pseudoMod f g) = r from rfl, h0, mul_zero]
    have hβ0 : toPolynomial (zContent (pseudoMod f g)) ≠ 0 :=
      toPolynomial_ne_zero (zContent_ne_zero hprem)
    have hrel : Polynomial.C α₀ * toPolynomial₂ f
        = Polynomial.C (toPolynomial (zContent (pseudoMod f g))) * toPolynomial₂ r
          + toPolynomial₂ g * toPolynomial₂ (pseudoDiv f g) := by
      rw [hα₀def, hr]
      exact walk_step_rel f g hgsz
    have hdc : (toPolynomial₂ r).natDegree = r.size - 1 := by
      rw [natDegree₂_eq_size_sub_one]
    have hrsz : r.size ≠ 0 := fun h0 => hrne (eq_zero_of_size_zero h0)
    have hrsize : r.size < g.size := by
      rw [hr, zStep]
      exact lt_of_le_of_lt (zPrimitive_size_le _) (pseudoMod_size_lt hgsz f)
    rcases eq_or_ne (i + 1) r.size with hfound | hne2
    · refine ⟨r, ?_, hfound.symm⟩
      rw [prs_z_eq, if_neg hgsz]
      refine List.mem_cons_of_mem _ ?_
      rw [prs_z_eq, if_neg hrsz]
      exact List.mem_cons_self
    rcases Nat.lt_or_ge (i + 1) r.size with hrec | hvan
    · -- recurse into `(g, r)`: the psc transfers through the step identity
      have hstep := subresultant_prs_step (toPolynomial₂ f) (toPolynomial₂ g)
        (toPolynomial₂ r) (toPolynomial₂ (pseudoDiv f g)) α₀
        (toPolynomial (zContent (pseudoMod f g)))
        (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree (toPolynomial₂ r).natDegree
        i hβ0 (by rw [hdc]; omega) (by rw [hdc, hdb]; omega) rfl le_rfl hQb hrel
      have hcoeffs := congrArg (fun q => Polynomial.coeff q i) hstep
      simp only [Polynomial.coeff_C_mul, hval] at hcoeffs
      have hL : α₀ ^ ((toPolynomial₂ g).natDegree - i)
          * (subresultant (toPolynomial₂ f) (toPolynomial₂ g)
              (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree i).coeff i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hα₀) hpsc
      rw [hcoeffs] at hL
      have hpsc' : (subresultant (toPolynomial₂ g) (toPolynomial₂ r)
          (toPolynomial₂ g).natDegree (toPolynomial₂ r).natDegree i).coeff i ≠ 0 := by
        intro h0
        apply hL
        rw [h0]
        ring
      obtain ⟨S, hSmem, hSsz⟩ := ih r.size (by omega) g r rfl (le_of_lt hrsize) hrne i
        (by omega) hpsc'
      refine ⟨S, ?_, hSsz⟩
      rw [prs_z_eq, if_neg hgsz]
      exact List.mem_cons_of_mem _ hSmem
    · -- vanish: `deg r < i < deg g` — the gap and defective-top indices have zero psc
      exfalso
      have hcltb : (toPolynomial₂ r).natDegree < i := by rw [hdc]; omega
      have hrzero : (Polynomial.C (toPolynomial (zContent (pseudoMod f g)))
          * toPolynomial₂ r).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hcltb)
      rcases eq_or_ne i ((toPolynomial₂ g).natDegree - 1) with htop | hnottop
      · subst htop
        have h := subresultant_prs_step_top (toPolynomial₂ f) (toPolynomial₂ g)
          (toPolynomial₂ r) (toPolynomial₂ (pseudoDiv f g)) α₀
          (toPolynomial (zContent (pseudoMod f g)))
          (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree
          (toPolynomial₂ r).natDegree
          hβ0 (by rw [hdc, hdb]; omega) rfl le_rfl hQb hrel
        exact hpsc (hkill α₀ _ _ hα₀ h (hshape _ _ _ hrzero))
      · have h := subresultant_prs_step_gap (toPolynomial₂ f) (toPolynomial₂ g)
          (toPolynomial₂ r) (toPolynomial₂ (pseudoDiv f g)) α₀
          (toPolynomial (zContent (pseudoMod f g)))
          (toPolynomial₂ f).natDegree (toPolynomial₂ g).natDegree
          (toPolynomial₂ r).natDegree i
          hα₀ hβ0 hcltb (by rw [hdb]; omega) rfl le_rfl hQb hrel
        exact hpsc (by rw [h, Polynomial.coeff_zero])

open DeepWiki.SymbolicIntegration in
/-- The bridged `z`-primitive part has Mathlib content `1` — the dispatched-gcd strip and
the `NormalizedGCDMonoid` content agree up to units. -/
theorem content_toPolynomial₂_zPrimitive {p : DensePoly (DensePoly R)} (hp : p ≠ 0) :
    (toPolynomial₂ (zPrimitive p)).content = 1 := by
  rw [← Polynomial.isPrimitive_iff_content_eq_one]
  intro r hr
  have hcoeff : ∀ i, r ∣ (toPolynomial₂ (zPrimitive p)).coeff i :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr
  have hpull : ∀ i, (equiv (R := R)).symm r ∣ (zPrimitive p).coeff i := by
    intro i
    have h1 := hcoeff i
    rw [toPolynomial₂_coeff] at h1
    have h2 := map_dvd ((equiv (R := R)).symm : Polynomial R →+* DensePoly R) h1
    simpa using h2
  have hunit' : IsUnit ((equiv (R := R)).symm r) :=
    isUnit_of_dvd_unit (dvd_zContent (zPrimitive p) hpull) (zContent_zPrimitive_isUnit hp)
  simpa using hunit'.map (equiv (R := R))

end Chain

section Specialize

variable {R : Type u} [Field R] [DecidableEq R]

open DeepWiki.SymbolicIntegration in
/-- **Similarity specializes through a primitive left side**: if `P` has content `1` and
`IsSimilar P X` over `K[t]`, then wherever the specialized `X` survives, the
specializations are similar over `K`. -/
theorem isSimilar_map_eval_of_content_eq_one {P X : Polynomial (Polynomial R)} (a : R)
    (hP : P.content = 1) (hsim : IsSimilar P X)
    (hXa : X.map (Polynomial.evalRingHom a) ≠ 0) :
    IsSimilar (P.map (Polynomial.evalRingHom a)) (X.map (Polynomial.evalRingHom a)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, heq⟩ := hsim
  have heq2 : Polynomial.C c₁ * P = Polynomial.C (c₂ * X.content) * X.primPart := by
    rw [map_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
    exact heq
  have hcont2 := congrArg Polynomial.content heq2
  rw [Polynomial.content_C_mul, Polynomial.content_C_mul, hP, mul_one,
    Polynomial.content_primPart, mul_one] at hcont2
  have hassoc : Associated c₁ (c₂ * X.content) :=
    normalize_eq_normalize_iff_associated.mp hcont2
  obtain ⟨v, hv⟩ := hassoc
  have hc₁C : (Polynomial.C c₁ : Polynomial (Polynomial R)) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact hc₁
  have hP_eq : P = Polynomial.C (↑v : Polynomial R) * X.primPart := by
    apply mul_left_cancel₀ hc₁C
    rw [heq2, ← hv, map_mul, mul_assoc]
  have hXmap : X.map (Polynomial.evalRingHom a)
      = Polynomial.C (Polynomial.eval a X.content)
        * (X.primPart.map (Polynomial.evalRingHom a)) := by
    conv_lhs => rw [Polynomial.eq_C_content_mul_primPart X]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hPmap : P.map (Polynomial.evalRingHom a)
      = Polynomial.C (Polynomial.eval a (↑v : Polynomial R))
        * (X.primPart.map (Polynomial.evalRingHom a)) := by
    conv_lhs => rw [hP_eq]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  obtain ⟨r, hru, hrC⟩ := Polynomial.isUnit_iff.mp v.isUnit
  have hveval : Polynomial.eval a (↑v : Polynomial R) ≠ 0 := by
    rw [← hrC, Polynomial.eval_C]
    exact hru.ne_zero
  have hweval : Polynomial.eval a X.content ≠ 0 := by
    intro h0
    apply hXa
    rw [hXmap, h0, map_zero, zero_mul]
  exact ⟨Polynomial.eval a X.content, Polynomial.eval a (↑v : Polynomial R),
    hweval, hveval, by rw [hXmap, hPmap]; ring⟩

end Specialize

section Endpoint

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]

omit [DensePolyGcd R] in
open DeepWiki.SymbolicIntegration in
/-- The entry-pair subresultant at any index is the LRT subresultant. -/
theorem entry_subresultant_eq_lrt (b d : DensePoly R) (hd2 : 2 ≤ d.size)
    (hbd : b.size < d.size) (i : ℕ) :
    subresultant (toPolynomial₂ (liftX d))
      (toPolynomial₂ (liftX b - zC * liftX (d′)))
      (toPolynomial₂ (liftX d)).natDegree
      (toPolynomial₂ (liftX b - zC * liftX (d′))).natDegree i
      = lrtSubresultant (toPolynomial b) (toPolynomial d) i := by
  rw [liftX_natDegree₂, operand_natDegree₂ b d hd2 hbd, toPolynomial₂_liftX,
    operand_bridge, lrtSubresultant]

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

/-- Two `GCDMonoid` structures give similar gcds (both are greatest common divisors). -/
private theorem isSimilar_gcd_of_gcd (i₁ i₂ : GCDMonoid (Polynomial R))
    (x y : Polynomial R) :
    DeepWiki.SymbolicIntegration.IsSimilar (@gcd _ _ i₁ x y) (@gcd _ _ i₂ x y) :=
  DeepWiki.SymbolicIntegration.IsSimilar.of_associated (associated_of_dvd_dvd
    (@dvd_gcd _ _ i₂ _ _ _ (@gcd_dvd_left _ _ i₁ x y) (@gcd_dvd_right _ _ i₁ x y))
    (@dvd_gcd _ _ i₁ _ _ _ (@gcd_dvd_left _ _ i₂ x y) (@gcd_dvd_right _ _ i₂ x y)))

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
    exact rootMultiplicity_rtResultant_le (toPolynomial b) (toPolynomial d) hdsep hA a
  have hile' : j + 1 ≤ d.size - 1 := by
    rw [natDegree_toPolynomial_eq_size_sub_one] at hile
    exact hile
  obtain ⟨hsim, hgne, hgdeg⟩ := lazardRiobooTrager_output_spec (toPolynomial b)
    (toPolynomial d) hdsep hA a
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
    obtain ⟨-, hgne, hgdeg⟩ := lazardRiobooTrager_output_spec (toPolynomial b)
      (toPolynomial d) hdsep hA a
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