import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Generic Bézout/Diophantine helpers

Bézout cofactors (`cbezoutOneWf`), the extended-Euclidean split (`cextendedEuclideanSplitWf`), the
Diophantine solve (`cdiophantineG`), and the inner Hermite loop over one squarefree factor
(`cHermiteReduceTowerInnerWf`), built on `cgcdWf`/`cdivmodWf`. The defs are `[CField α]`-only (plus
`[CDiffField α]` for the Hermite loop), so they `native_decide` over noncomputable-`CFieldSpec`
carriers; correctness is proved through `toPolyG` over `K[X]`. -/

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-- Bézout cofactors `cbezoutOneWf a b = (u, w)` with `u·a + w·b = 1` for coprime `a, b`. -/
def cbezoutOneWf (a b : CPoly α) : CPoly α × CPoly α :=
  let (g, s, t) := cgcdWf a b
  let ginv := CField.inv (cleadG g)
  (cscaleG ginv s, cscaleG ginv t)

/-- Bézout split `cextendedEuclideanSplitWf dₙ dₛ r u w = (b, c)` along `dₛ`. -/
def cextendedEuclideanSplitWf (dn ds r u w : CPoly α) : CPoly α × CPoly α :=
  let ur := cmulG u r
  let (quo, rem) := cdivmodWf ur ds
  (rem, caddG (cmulG w r) (cmulG quo dn))

/-- Generic Diophantine solver `cdiophantineG p q rhs = (b, c)` for `b·p + c·q = rhs`. -/
def cdiophantineG (p q rhs : CPoly α) : CPoly α × CPoly α :=
  let (g, s, t) := cgcdWf p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodWf S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

variable [CFieldSpec α]

/-! ### Correctness of the Bézout/Diophantine leaves -/

/-- `cbezoutOneWf` solves the normalized Bézout identity over `K[X]` in the coprime case. -/
theorem toPolyG_cbezoutOneWf (a b : CPoly α)
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
    simp only [denote]
    rw [toK_cleadG_eq_leadingCoeff, ← hc]
  have hw : toPolyG (cbezoutOneWf a b).2 = Polynomial.C c⁻¹ * toPolyG t := by
    rw [cbezoutOneWf]
    show toPolyG (cscaleG (CField.inv (cleadG g)) t) = _
    simp only [denote]
    rw [toK_cleadG_eq_leadingCoeff, ← hc]
  rw [hu, hw]
  have hcombine : Polynomial.C c⁻¹ * toPolyG s * toPolyG a
      + Polynomial.C c⁻¹ * toPolyG t * toPolyG b = Polynomial.C c⁻¹ * toPolyG g := by
    rw [← hbez]; ring
  rw [hcombine, hgC, ← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]

/-- `cextendedEuclideanSplitWf` solves the split Bézout equation over `K[X]`. -/
theorem toPolyG_cextendedEuclideanSplitWf (dn ds r u w : CPoly α)
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
  simp only [hb, hc, denote]
  have hrem : toPolyG (cmodWf ur ds)
      = toPolyG ur - toPolyG (cdivWf ur ds) * toPolyG ds := by
    rw [hdivmod]; ring
  rw [hrem, hur]
  simp only [denote]
  have hkey : (toPolyG u * toPolyG r - toPolyG (cdivWf (cmulG u r) ds) * toPolyG ds) * toPolyG dn
      + (toPolyG w * toPolyG r + toPolyG (cdivWf (cmulG u r) ds) * toPolyG dn) * toPolyG ds
      = (toPolyG u * toPolyG dn + toPolyG w * toPolyG ds) * toPolyG r := by ring
  rw [show cmulG u r = ur from rfl] at hkey ⊢
  rw [hkey, hbez, one_mul]

/-- `cextendedEuclideanSplitWf`'s first cofactor is proper: `deg b < deg dₛ`. -/
theorem cextendedEuclideanSplitWf_fst_degree_lt (dn ds r u w : CPoly α)
    (hds : cnormG ds ≠ []) :
    (toPolyG (cextendedEuclideanSplitWf dn ds r u w).1).degree < (toPolyG ds).degree := by
  have hfst : (cextendedEuclideanSplitWf dn ds r u w).1 = cmodWf (cmulG u r) ds := by
    simp [cextendedEuclideanSplitWf, cmodWf]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hds ?_
  show (cnormG (cmodWf (cmulG u r) ds) : List α).length < _
  exact cmodWf_length_lt (cmulG u r) ds hds

/-- `cextendedEuclideanSplitWf`'s second cofactor is proper: `deg c < deg dₙ`. -/
theorem cextendedEuclideanSplitWf_snd_degree_lt (dn ds r u w d : CPoly α)
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

/-- `cdiophantineG` solves the generic Diophantine equation over `K[X]` for coprime inputs. -/
theorem toPolyG_cdiophantineG (p q rhs : CPoly α)
    (hq0 : cnormG q ≠ [])
    (hgdeg : (toPolyG (cgcdWf p q).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf p q).1 ≠ 0) :
    toPolyG (cdiophantineG p q rhs).1 * toPolyG p
        + toPolyG (cdiophantineG p q rhs).2 * toPolyG q = toPolyG rhs := by
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
    rw [hSdef]
    simp only [denote]
    rw [toK_cleadG_eq_leadingCoeff, ← hc]
  have hTpoly : toPolyG T = Polynomial.C c⁻¹ * (toPolyG rhs * toPolyG t) := by
    rw [hTdef]
    simp only [denote]
    rw [toK_cleadG_eq_leadingCoeff, ← hc]
  -- the Euclidean division `S = quo·q + b` (fuel-free).
  have hdivmod : toPolyG S
      = toPolyG (cdivmodWf S q).1 * toPolyG q + toPolyG (cdivmodWf S q).2 :=
    toPolyG_cdivmodWf S q hq0
  -- the output components `b = cnormG (cdivmodWf S q).2`, `c = cnormG (T + quo·p)`.
  have hbval : (cdiophantineG p q rhs).1 = cnormG (cdivmodWf S q).2 := by
    rw [cdiophantineG]
  have hcval : (cdiophantineG p q rhs).2
      = cnormG (caddG T (cmulG (cdivmodWf S q).1 p)) := by
    rw [cdiophantineG]
  simp only [hbval, hcval, denote]
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

/-- `cdiophantineG`'s first cofactor is proper: `deg (cdiophantineG p q rhs).1 < deg q` for nonzero `q`. -/
theorem cdiophantineG_fst_degree_lt (p q rhs : CPoly α) (hq : cnormG q ≠ []) :
    (toPolyG (cdiophantineG p q rhs).1).degree < (toPolyG q).degree := by
  set g := (cgcdWf p q).1 with hg
  set s := (cgcdWf p q).2.1 with hs
  set S := cscaleG (CField.inv (cleadG g)) (cmulG rhs s) with hS
  have hfst : (cdiophantineG p q rhs).1 = cnormG (cmodWf S q) := by
    rw [cdiophantineG]
    simp only [← hg, ← hs, ← hS, cmodWf]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hq ?_
  rw [cnormG_idem]
  exact cmodWf_length_lt S q hq

end CPoly

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α]

/-- Inner Hermite loop over a squarefree factor `v`, driven by a downward multiplicity counter. -/
def cHermiteReduceTowerInnerWf (Dt : CPoly α) (v u : CPoly α) :
    ℕ → CPoly α → CPoly α × CPoly α → (CPoly α × CPoly α) × CPoly α
  | 0, a, g => (g, a)
  | j + 1, a, g =>
    let jval : α := cnatCastG (j + 1)                                 -- `j` as a field element
    let Dv := cmonomialDeriv Dt v
    let p := cmulG u Dv
    let rhs := cscaleG (CField.neg (CField.inv jval)) a               -- `−a/j`
    let (b, c) := cdiophantineG p v rhs
    let Vpow := cpowG v (j + 1)
    let g' := (caddG (cmulG g.1 Vpow) (cmulG b g.2), cmulG g.2 Vpow)  -- `g + b/Vʲ` (cross-multiplied)
    let a' := csubG (cscaleG (CField.neg jval) c) (cmulG u (cmonomialDeriv Dt b))  -- `−j·c − u·Db`
    cHermiteReduceTowerInnerWf Dt v u j a' g'

end CPoly

end DeepWiki.SymbolicIntegration
