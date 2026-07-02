import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv

/-! # Generic Bézout/Diophantine helpers

Bézout cofactors (`cbezoutOneWf`), the extended-Euclidean split (`cextendedEuclideanSplitWf`), the
Diophantine solve (`cdiophantineGWf`), and the inner Hermite loop over one squarefree factor
(`cHermiteReduceTowerInnerWf`), built on `cgcdWf`/`cdivmodWf`. The defs are `[CField α]`-only (plus
`[CDiffField α]` for the Hermite loop), so they `native_decide` over noncomputable-`CFieldSpec`
carriers; correctness is proved through `toPolyG` over `K[X]`. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- Bézout cofactors `cbezoutOneWf a b = (u, w)` with `u·a + w·b = 1` for coprime `a, b`: run
`cgcdWf` to get `(g, s, t)` with `s·a + t·b = g` (a nonzero constant, since `a, b` coprime),
then rescale by `g⁻¹`. -/
def cbezoutOneWf (a b : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf a b
  let ginv := CField.inv (cleadG g)
  (cscaleG ginv s, cscaleG ginv t)

/-- Bézout split `cextendedEuclideanSplitWf dₙ dₛ r u w = (b, c)`: with a Bézout pair
`u·dₙ + w·dₛ = 1`, returns `b = (u·r) mod dₛ` and `c = w·r + (u·r div dₛ)·dₙ` via `cdivmodWf`. -/
def cextendedEuclideanSplitWf (dn ds r u w : CPolyG α) : CPolyG α × CPolyG α :=
  let ur := cmulG u r
  let (quo, rem) := cdivmodWf ur ds
  (rem, caddG (cmulG w r) (cmulG quo dn))

/-- Generic Diophantine/Bézout solver `cdiophantineGWf p q rhs = (b, c)` solving `b·p + c·q = rhs`
with `deg b < deg q`, for coprime `p, q`: from `cgcdWf p q = (g, s, t)` with `s·p + t·q = g`
(a nonzero constant), rescale `(s, t)` by `rhs/g`, reduce the first cofactor mod `q`
(`S = quo·q + b` via `cdivmodWf`), and absorb `quo·p` into the second (`c = T + quo·p`). -/
def cdiophantineGWf (p q rhs : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodWf S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

variable [CFieldSpec α]

/-! ### Correctness of the Bézout/Diophantine leaves

The Bézout/Diophantine identities over `K[X]`, from the leaf lemmas `toPolyG_cgcdWf` (Bézout) and
`toPolyG_cdivmodWf` (Euclidean division). -/

/-- `cbezoutOneWf` solves the Bézout identity `u·a + w·b = 1` over `K[X]`: with
`(g, s, t) = cgcdWf a b` and `g` a nonzero constant (the coprime case), the rescaled cofactors
`(u, w) = cbezoutOneWf a b` satisfy `toPolyG u · toPolyG a + toPolyG w · toPolyG b = 1`. -/
theorem toPolyG_cbezoutOneWf (a b : CPolyG α)
    (hgdeg : (toPolyG (cgcdWf a b).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf a b).1 ≠ 0) :
    toPolyG (cbezoutOneWf a b).1 * toPolyG a
        + toPolyG (cbezoutOneWf a b).2 * toPolyG b = 1 := by
  set g := (cgcdWf a b).1 with hg
  set s := (cgcdWf a b).2.1 with hs
  set t := (cgcdWf a b).2.2 with ht
  have hbez : toPolyG s * toPolyG a + toPolyG t * toPolyG b = toPolyG g :=
    toPolyG_cgcdWf a b
  set c := (toPolyG g).leadingCoeff with hc
  have hlead_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  have hgC : toPolyG g = Polynomial.C c := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
    rw [hc, Polynomial.leadingCoeff, hgdeg]
  have hu : toPolyG (cbezoutOneWf a b).1 = Polynomial.C c⁻¹ * toPolyG s := by
    rw [cbezoutOneWf]
    show toPolyG (cscaleG (CField.inv (cleadG g)) s) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  have hw : toPolyG (cbezoutOneWf a b).2 = Polynomial.C c⁻¹ * toPolyG t := by
    rw [cbezoutOneWf]
    show toPolyG (cscaleG (CField.inv (cleadG g)) t) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  rw [hu, hw]
  have hcombine : Polynomial.C c⁻¹ * toPolyG s * toPolyG a
      + Polynomial.C c⁻¹ * toPolyG t * toPolyG b = Polynomial.C c⁻¹ * toPolyG g := by
    rw [← hbez]; ring
  rw [hcombine, hgC, ← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]

/-- `cextendedEuclideanSplitWf` solves `b·dₙ + c·dₛ = r` over `K[X]`: with a Bézout pair
`u·dₙ + w·dₛ = 1` (read through `toPolyG`), `cextendedEuclideanSplitWf dn ds r u w = (b, c)` gives
`toPolyG b · toPolyG dn + toPolyG c · toPolyG ds = toPolyG r`. Requires `dₛ` nonzero
(`cnormG ds ≠ []`). -/
theorem toPolyG_cextendedEuclideanSplitWf (dn ds r u w : CPolyG α)
    (hds0 : cnormG ds ≠ [])
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1) :
    toPolyG (cextendedEuclideanSplitWf dn ds r u w).1 * toPolyG dn
        + toPolyG (cextendedEuclideanSplitWf dn ds r u w).2 * toPolyG ds
      = toPolyG r := by
  set ur := cmulG u r with hur
  -- the fuel-free Euclidean identity `u·r = (u·r div ds)·ds + (u·r mod ds)`.
  have hdivmod : toPolyG ur
      = toPolyG (cdivWf ur ds) * toPolyG ds + toPolyG (cmodWf ur ds) :=
    toPolyG_cmodWf ur ds hds0
  have hb : (cextendedEuclideanSplitWf dn ds r u w).1 = cmodWf ur ds := by
    rw [cextendedEuclideanSplitWf]; simp only [cmodWf, hur]
  have hc : (cextendedEuclideanSplitWf dn ds r u w).2
      = caddG (cmulG w r) (cmulG (cdivWf ur ds) dn) := by
    rw [cextendedEuclideanSplitWf]; simp only [cdivWf, hur]
  rw [hb, hc, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG]
  have hrem : toPolyG (cmodWf ur ds)
      = toPolyG ur - toPolyG (cdivWf ur ds) * toPolyG ds := by
    rw [hdivmod]; ring
  rw [hrem, hur, toPolyG_cmulG]
  have hkey : (toPolyG u * toPolyG r - toPolyG (cdivWf (cmulG u r) ds) * toPolyG ds) * toPolyG dn
      + (toPolyG w * toPolyG r + toPolyG (cdivWf (cmulG u r) ds) * toPolyG dn) * toPolyG ds
      = (toPolyG u * toPolyG dn + toPolyG w * toPolyG ds) * toPolyG r := by ring
  rw [show cmulG u r = ur from rfl] at hkey ⊢
  rw [hkey, hbez, one_mul]

/-- `cextendedEuclideanSplitWf`'s first cofactor is proper (`deg b < deg dₛ`): the first cofactor
`b = (u·r) mod dₛ` is a Euclidean remainder mod `dₛ`. -/
theorem cextendedEuclideanSplitWf_fst_degree_lt (dn ds r u w : CPolyG α)
    (hds : cnormG ds ≠ []) :
    (toPolyG (cextendedEuclideanSplitWf dn ds r u w).1).degree < (toPolyG ds).degree := by
  have hfst : (cextendedEuclideanSplitWf dn ds r u w).1 = cmodWf (cmulG u r) ds := by
    simp [cextendedEuclideanSplitWf, cmodWf]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hds ?_
  show (cnormG (cmodWf (cmulG u r) ds) : List α).length < _
  exact cmodWf_length_lt (cmulG u r) ds hds

/-- `cextendedEuclideanSplitWf`'s second cofactor is proper (`deg c < deg dₙ`): from the Bézout
split, the first-cofactor remainder bound, the denominator split `d = dₛ·dₙ`, and `deg r < deg d`. -/
theorem cextendedEuclideanSplitWf_snd_degree_lt (dn ds r u w d : CPolyG α)
    (hds : cnormG ds ≠ []) (hdn : cnormG dn ≠ [])
    (hsplit : toPolyG d = toPolyG ds * toPolyG dn)
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1)
    (hr : (toPolyG r).degree < (toPolyG d).degree) :
    (toPolyG (cextendedEuclideanSplitWf dn ds r u w).2).degree < (toPolyG dn).degree := by
  set b := toPolyG (cextendedEuclideanSplitWf dn ds r u w).1 with hbdef
  set c := toPolyG (cextendedEuclideanSplitWf dn ds r u w).2 with hcdef
  have hds0 : toPolyG ds ≠ 0 := fun h => hds ((cnormG_eq_nil_iff ds).mpr h)
  have hdn0 : toPolyG dn ≠ 0 := fun h => hdn ((cnormG_eq_nil_iff dn).mpr h)
  have hspec : b * toPolyG dn + c * toPolyG ds = toPolyG r :=
    toPolyG_cextendedEuclideanSplitWf dn ds r u w hds hbez
  have hbdeg : b.degree < (toPolyG ds).degree :=
    cextendedEuclideanSplitWf_fst_degree_lt dn ds r u w hds
  have hbdn : (b * toPolyG dn).degree < (toPolyG d).degree := by
    rw [hsplit, Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hbdeg
  have hcds : c * toPolyG ds = toPolyG r - b * toPolyG dn := by linear_combination hspec
  have hcdsdeg : (c * toPolyG ds).degree < (toPolyG d).degree := by
    rw [hcds]
    calc (toPolyG r - b * toPolyG dn).degree
        ≤ max (toPolyG r).degree (b * toPolyG dn).degree := Polynomial.degree_sub_le _ _
      _ < (toPolyG d).degree := max_lt hr hbdn
  rw [Polynomial.degree_mul, hsplit, Polynomial.degree_mul] at hcdsdeg
  have hdsdeg : (toPolyG ds).degree ≠ ⊥ := by rwa [Ne, Polynomial.degree_eq_bot]
  rw [add_comm (toPolyG ds).degree (toPolyG dn).degree] at hcdsdeg
  exact (WithBot.add_lt_add_iff_right hdsdeg).mp hcdsdeg

/-- `cdiophantineGWf` solves `b·p + c·q = rhs` over `K[X]`: for coprime `p, q` (extended-gcd
`cgcdWf p q = (g, s, t)` with `g` a nonzero constant), the output `(b, c) = cdiophantineGWf p q rhs`
satisfies `toPolyG b · toPolyG p + toPolyG c · toPolyG q = toPolyG rhs`. From the raw Bézout
`toPolyG_cgcdWf` rescaled by `rhs/lc(g)` and the Euclidean division `toPolyG_cdivmodWf`. -/
theorem toPolyG_cdiophantineGWf (p q rhs : CPolyG α)
    (hq0 : cnormG q ≠ [])
    (hgdeg : (toPolyG (cgcdWf p q).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf p q).1 ≠ 0) :
    toPolyG (cdiophantineGWf p q rhs).1 * toPolyG p
        + toPolyG (cdiophantineGWf p q rhs).2 * toPolyG q = toPolyG rhs := by
  set g := (cgcdWf p q).1 with hg
  set s := (cgcdWf p q).2.1 with hs
  set t := (cgcdWf p q).2.2 with ht
  have hbez : toPolyG s * toPolyG p + toPolyG t * toPolyG q = toPolyG g := toPolyG_cgcdWf p q
  set c := (toPolyG g).leadingCoeff with hc
  have hlead_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  have hgC : toPolyG g = Polynomial.C c := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
    rw [hc, Polynomial.leadingCoeff, hgdeg]
  -- the rescaled dividends `S = C(c⁻¹)·rhs·s`, `T = C(c⁻¹)·rhs·t`.
  set S := cscaleG (CField.inv (cleadG g)) (cmulG rhs s) with hSdef
  set T := cscaleG (CField.inv (cleadG g)) (cmulG rhs t) with hTdef
  have hSpoly : toPolyG S = Polynomial.C c⁻¹ * (toPolyG rhs * toPolyG s) := by
    rw [hSdef, toPolyG_cscaleG, toPolyG_cmulG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  have hTpoly : toPolyG T = Polynomial.C c⁻¹ * (toPolyG rhs * toPolyG t) := by
    rw [hTdef, toPolyG_cscaleG, toPolyG_cmulG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  -- the Euclidean division `S = quo·q + b` (fuel-free).
  have hdivmod : toPolyG S
      = toPolyG (cdivmodWf S q).1 * toPolyG q + toPolyG (cdivmodWf S q).2 :=
    toPolyG_cdivmodWf S q hq0
  -- the output components `b = cnormG (cdivmodWf S q).2`, `c = cnormG (T + quo·p)`.
  have hbval : (cdiophantineGWf p q rhs).1 = cnormG (cdivmodWf S q).2 := by
    rw [cdiophantineGWf]
  have hcval : (cdiophantineGWf p q rhs).2
      = cnormG (caddG T (cmulG (cdivmodWf S q).1 p)) := by
    rw [cdiophantineGWf]
  rw [hbval, hcval, toPolyG_cnormG, toPolyG_cnormG, toPolyG_caddG, toPolyG_cmulG]
  -- `b = S − quo·q`, so `b·p + (T + quo·p)·q = S·p + T·q = C(c⁻¹)·rhs·(s·p + t·q) = C(c⁻¹)·rhs·g = rhs`.
  have hbpoly : toPolyG (cdivmodWf S q).2 = toPolyG S - toPolyG (cdivmodWf S q).1 * toPolyG q := by
    rw [hdivmod]; ring
  rw [hbpoly, hSpoly, hTpoly]
  have hkey : (Polynomial.C c⁻¹ * (toPolyG rhs * toPolyG s) - toPolyG (cdivmodWf S q).1 * toPolyG q)
        * toPolyG p
      + (Polynomial.C c⁻¹ * (toPolyG rhs * toPolyG t) + toPolyG (cdivmodWf S q).1 * toPolyG p)
        * toPolyG q
      = Polynomial.C c⁻¹ * toPolyG rhs * (toPolyG s * toPolyG p + toPolyG t * toPolyG q) := by ring
  rw [hkey, hbez, hgC]
  have hCcancel : Polynomial.C c⁻¹ * Polynomial.C c = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]
  calc Polynomial.C c⁻¹ * toPolyG rhs * Polynomial.C c
      = (Polynomial.C c⁻¹ * Polynomial.C c) * toPolyG rhs := by ring
    _ = toPolyG rhs := by rw [hCcancel, one_mul]

/-- `cdiophantineGWf`'s first cofactor is proper: `deg (cdiophantineGWf p q rhs).1 < deg q` for
nonzero `q`. The first cofactor is the normalized `cmodWf` remainder of the rescaled Bézout
dividend. -/
theorem cdiophantineGWf_fst_degree_lt (p q rhs : CPolyG α) (hq : cnormG q ≠ []) :
    (toPolyG (cdiophantineGWf p q rhs).1).degree < (toPolyG q).degree := by
  set g := (cgcdWf p q).1 with hg
  set s := (cgcdWf p q).2.1 with hs
  set S := cscaleG (CField.inv (cleadG g)) (cmulG rhs s) with hS
  have hfst : (cdiophantineGWf p q rhs).1 = cnormG (cmodWf S q) := by
    rw [cdiophantineGWf]
    simp only [← hg, ← hs, ← hS, cmodWf]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hq ?_
  rw [cnormG_idem]
  exact cmodWf_length_lt S q hq

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- Inner Hermite loop over a squarefree factor `v` (multiplicity `i`, `u = d/vⁱ`), driven by the
downward counter `j`: each step solves `b·(u·Dv) + c·v = −a/j` with `cdiophantineGWf`
(`Dv = cmonomialDeriv Dt v` the monomial derivation), accumulates the rational summand `b/vʲ`
into `g`, and updates `a ← −j·c − u·Db`. Structural recursion on `j`. -/
def cHermiteReduceTowerInnerWf (Dt : CPolyG α) (v u : CPolyG α) :
    ℕ → CPolyG α → CPolyG α × CPolyG α → (CPolyG α × CPolyG α) × CPolyG α
  | 0, a, g => (g, a)
  | j + 1, a, g =>
    let jval : α := cnatCastG (j + 1)                                 -- `j` as a field element
    let Dv := cmonomialDeriv Dt v
    let p := cmulG u Dv
    let rhs := cscaleG (CField.neg (CField.inv jval)) a               -- `−a/j`
    let (b, c) := cdiophantineGWf p v rhs
    let Vpow := cpowG v (j + 1)
    let g' := (caddG (cmulG g.1 Vpow) (cmulG b g.2), cmulG g.2 Vpow)  -- `g + b/Vʲ` (cross-multiplied)
    let a' := csubG (cscaleG (CField.neg jval) c) (cmulG u (cmonomialDeriv Dt b))  -- `−j·c − u·Db`
    cHermiteReduceTowerInnerWf Dt v u j a' g'

end CPolyG

end DeepWiki.SymbolicIntegration
