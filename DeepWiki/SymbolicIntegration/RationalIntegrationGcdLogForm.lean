import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues

/-! # Czichowski's logs are the Rothstein–Trager gcds (Bronstein §2.6 / Czichowski Lemma 2.3)
The integral *connection* behind Czichowski's algorithm: the Gröbner-basis logarithm argument
`S(x,c) = gcd(D, A − c·D')` (Czichowski's Lemma 2.3) is exactly the Rothstein–Trager polynomial
`Gₐ = ∏_{res(α)=a}(X−α)`, so Czichowski's integral `∫ A/D = ∑ c·log(gcd(D, A−c·D'))` is the *same*
logarithmic part as the §2.4/§2.5 Rothstein–Trager / Lazard–Rioboo–Trager result. Stated for split
squarefree `D = Lagrange.nodal s id = ∏_{α∈s}(X−α)`: the gcd of `D` with `A − a·D'` factors as the
product of `(X−α)` over the residue-`a` roots `α` of `D`, hence the §2.5 grouped log sum can be rewritten
with `gcd(D, A−a·D')` inside each `logDeriv`. This is the connection only — no Gröbner-basis structure. -/

open Polynomial

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
/-- **Czichowski's Lemma 2.3 = the Rothstein–Trager gcd** (Bronstein §2.6, p.54): for split squarefree
`D = Lagrange.nodal s id = ∏_{α∈s}(X−α)`, the gcd `gcd(D, A − a·D')` is the product of `(X−α)` over the
roots `α` of `D` whose residue `A(α)/D'(α)` equals `a` — i.e. it is exactly the Rothstein–Trager
polynomial `Gₐ = ∏_{α∈s, res(α)=a}(X−α)`. Czichowski's Gröbner-basis logarithm argument `S(x,c)` coincides
with the §2.4 RT gcd, so his `∫ A/D = ∑ c·log(gcd(D, A−c·D'))` is the same logarithmic part as RT/LRT.
The roots of the gcd are the residue-`a` roots of `D` (`isRoot_gcd_iff_residue`), and the gcd splits as a
monic product of those linear factors. -/
theorem gcd_nodal_eq_prod_residue (s : Finset K) (A : K[X]) (a : K) :
    gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id))
      = ∏ α ∈ s.filter
          (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a), (X - C α) := by
  set D := Lagrange.nodal s id with hD
  set res : K → K := fun α => A.eval α / eval α (derivative D) with hres
  set E := A - C a * derivative D with hE
  -- `D = ∏_{α∈s}(X − α)` (the split form)
  have hDprod : D = ∏ α ∈ s, (X - C α) := by simp [hD, Lagrange.nodal_eq, id]
  -- `D` is separable, hence squarefree, monic, nonzero; its roots are `s`
  have hDsep : D.Separable := by
    rw [hDprod]; exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hDmonic : D.Monic := hD ▸ Lagrange.nodal_monic
  have hD0 : D ≠ 0 := hD ▸ Lagrange.nodal_ne_zero
  have hDroots : D.roots = s.val := by rw [hDprod, roots_prod_X_sub_C]
  -- `D'(α) ≠ 0` at every root of `D`, from separability
  have hd : ∀ {α : K}, D.IsRoot α → (derivative D).eval α ≠ 0 := by
    intro α hα
    have := hDsep.eval₂_derivative_ne_zero (RingHom.id K)
      (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hα)
    simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
  -- `gcd D E` is separable (divides `D`), hence its roots are nodup; it splits and is monic
  have hgsep : (gcd D E).Separable := hDsep.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd D E ≠ 0 := fun h =>
    hD0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left D E))
  have hgmonic : (gcd D E).Monic := normalize_gcd D E ▸ monic_normalize hg0
  have hDsplits : D.Splits := by
    rw [hDprod]; exact Splits.prod fun α _ => Splits.X_sub_C _
  have hgsplits : (gcd D E).Splits := hDsplits.of_dvd hD0 (gcd_dvd_left D E)
  -- the roots of the gcd are exactly the residue-`a` roots of `D`, i.e. `(filter).val`
  have hroots : (gcd D E).roots = (s.filter (fun α => res α = a)).val := by
    refine Multiset.Nodup.ext (nodup_roots hgsep) (s.filter (fun α => res α = a)).nodup |>.mpr
      fun α => ?_
    rw [mem_roots hg0, Finset.mem_val, Finset.mem_filter]
    constructor
    · intro hα
      have hDα : D.IsRoot α := (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left D E)))
      obtain ⟨_, hres'⟩ := (isRoot_gcd_iff_residue A D a α (hd hDα)).mp hα
      have hαs : α ∈ s := by
        have : α ∈ s.val := hDroots ▸ (mem_roots hD0).mpr hDα
        exact this
      exact ⟨hαs, hres'⟩
    · rintro ⟨hαs, hres'⟩
      have hDα : D.IsRoot α := (mem_roots hD0).mp (hDroots ▸ hαs)
      exact (isRoot_gcd_iff_residue A D a α (hd hDα)).mpr ⟨hDα, hres'⟩
  -- conclude: `gcd D E = ∏_{roots}(X − α) = ∏_{α∈filter}(X − α)`
  rw [hgsplits.eq_prod_roots_of_monic hgmonic, hroots, Finset.prod_eq_multiset_prod]

open scoped Classical in
-- Czichowski's Lemma 2.3: `gcd(D, A − a·D') = ∏_{α∈s, res(α)=a}(X−α)`, the Rothstein–Trager `Gₐ`.
example (s : Finset K) (A : K[X]) (a : K) :
    gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id))
      = ∏ α ∈ s.filter
          (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a), (X - C α) :=
  gcd_nodal_eq_prod_residue s A a

open scoped Classical in
/-- **Czichowski's integral in gcd log-form** (Bronstein §2.6, Czichowski part (iii)): for `A` of degree
`< #s` over split squarefree `D = Lagrange.nodal s id = ∏_{α∈s}(X−α)`,
`A/D = ∑_a a · logDeriv(gcd(D, A − a·D'))` in `K(x)`, the sum over the distinct residues `a = A(α)/D'(α)` —
Czichowski's `∫ A/D = ∑ c·log(S(x,c))` with `S(x,c) = gcd(D, A−c·D')`. This is the *same* integral as the
§2.4/§2.5 Rothstein–Trager / LRT result: rewriting the §2.5 grouped log sum `ratFunc_eq_sum_residue_grouped`
(whose argument is `∏_{res(α)=a}(X−α)`) by `gcd_nodal_eq_prod_residue` puts `gcd(D, A − a·D')` inside each
`logDeriv`. -/
theorem ratFunc_eq_sum_residue_gcd (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (gcd (Lagrange.nodal s id)
                  (A - C a * derivative (Lagrange.nodal s id)))) := by
  rw [ratFunc_eq_sum_residue_grouped s A hA]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gcd_nodal_eq_prod_residue]

open scoped Classical in
-- Czichowski part (iii): `∫ A/D = ∑_a a·log(gcd(D, A−a·D'))`, the RT/LRT log sum with the RT gcd.
example (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (gcd (Lagrange.nodal s id)
                  (A - C a * derivative (Lagrange.nodal s id)))) :=
  ratFunc_eq_sum_residue_gcd s A hA

end DeepWiki.SymbolicIntegration
