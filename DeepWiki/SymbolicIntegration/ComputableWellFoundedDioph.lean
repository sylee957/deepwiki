import DeepWiki.SymbolicIntegration.ComputableWellFounded
import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv

/-! # Fuel-free generic Bézout/Diophantine helpers (`cbezoutOneWf`, `cextendedEuclideanSplitWf`,
`cdiophantineGWf`, `cHermiteReduceTowerInnerWf`)

The fuel-free generic (`[CField α]`-only) Bézout/Diophantine leaves the generic tower integration
engine reuses verbatim. Each substitutes the fuel-free extended-Euclid `cgcdWf` / quotient `cdivmodWf`
(`ComputableWellFounded`) for the fuel'd `cgcdExtG`/`cdivmodG` inside the corresponding fuel'd op:

* **`cbezoutOneWf`** — Bézout cofactors `u·a + w·b = 1` for coprime `a, b` (fuel-free `cbezoutOne`).
* **`cextendedEuclideanSplitWf`** — the Bézout split `(b, c)` from a cofactor pair (fuel-free
  `cextendedEuclideanSplit`).
* **`cdiophantineGWf`** — the full Diophantine solve `b·p + c·q = rhs` with `deg b < deg q` (fuel-free
  `cdiophantineG`).
* **`cHermiteReduceTowerInnerWf`** — the §5.3 inner Hermite loop over one squarefree factor (structural
  on the downward counter `j`, fuel-free `cHermiteReduceTowerInner`), built on `cdiophantineGWf` and the
  monomial derivation `cmonomialDeriv`.

The fuel'd-agreement bridges (`*_eq_of_fuel`, `[CFieldSpec α]`) live alongside; the fuel bounds appear
only in those proofs, the runtime ops carry none. Generic over `[CField α]` (plus `[CDiffField α]` for
the Hermite inner loop), so they native_decide over the noncomputable tower. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Fuel-free Bézout cofactors** `cbezoutOneWf a b = (u, w)` with `u·a + w·b = 1` for coprime `a, b`: the
fuel-free companion of `cbezoutOne`. Runs the **fuel-free** extended-Euclid `cgcdWf` to get `(g, s, t)` with
`s·a + t·b = g` (a nonzero constant, since `a, b` coprime), then rescales by `g⁻¹` — **no fuel at runtime**. -/
def cbezoutOneWf (a b : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf a b
  let ginv := CField.inv (cleadG g)
  (cscaleG ginv s, cscaleG ginv t)

/-- **Fuel-free Bézout split** `cextendedEuclideanSplitWf dₙ dₛ r u w = (b, c)`: the fuel-free companion of
`cextendedEuclideanSplit`. With a Bézout pair `u·dₙ + w·dₛ = 1`, returns `b = (u·r) mod dₛ` and `c = w·r +
(u·r div dₛ)·dₙ` via the **fuel-free** `cdivmodWf` — **no fuel at runtime**. -/
def cextendedEuclideanSplitWf (dn ds r u w : CPolyG α) : CPolyG α × CPolyG α :=
  let ur := cmulG u r
  let (quo, rem) := cdivmodWf ur ds
  (rem, caddG (cmulG w r) (cmulG quo dn))

/-- **Fuel-free generic Diophantine/Bézout solver** `cdiophantineGWf p q rhs = (b, c)` solving
`b·p + c·q = rhs` with `deg b < deg q`, for **coprime** `p, q`: the fuel-free companion of `cdiophantineG`.
From the **fuel-free** extended Euclid `cgcdWf p q = (g, s, t)` with `s·p + t·q = g` (a nonzero constant),
rescale `(s,t)` by `rhs/g`, reduce the first cofactor mod `q` (`S = quo·q + b`, via the **fuel-free**
`cdivmodWf`), and absorb `quo·p` into the second (`c = T + quo·p`) — **no fuel at runtime**. Generic over
`[CField α]`. -/
def cdiophantineGWf (p q rhs : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdWf p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodWf S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

variable [CFieldSpec α]

/-- **`cbezoutOneWf` equals the fuel'd `cbezoutOne` at any sufficient fuel** — with `(cnormG a).length ≤
fuel` and `(cnormG b).length < fuel`, `cbezoutOneWf a b = cbezoutOne fuel a b`, since the only fuel'd
sub-op `cgcdExtG` is bridged by `cgcdWf_eq_of_fuel`. -/
theorem cbezoutOneWf_eq_of_fuel (fuel : ℕ) (a b : CPolyG α)
    (ha : (cnormG a : List α).length ≤ fuel) (hb : (cnormG b : List α).length < fuel) :
    cbezoutOneWf a b = CPolyG.cbezoutOne fuel a b := by
  rw [cbezoutOneWf, CPolyG.cbezoutOne, cgcdWf_eq_of_fuel fuel a b ha hb]

/-- **`cextendedEuclideanSplitWf` equals the fuel'd `cextendedEuclideanSplit` at any sufficient fuel** —
with `(cnormG (cmulG u r)).length ≤ fuel`, `cextendedEuclideanSplitWf dn ds r u w = cextendedEuclideanSplit
fuel dn ds r u w`, since the only fuel'd sub-op `cdivmodG` is bridged by `cdivmodWf_eq_of_fuel`. -/
theorem cextendedEuclideanSplitWf_eq_of_fuel (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hur : (cnormG (cmulG u r) : List α).length ≤ fuel) :
    cextendedEuclideanSplitWf dn ds r u w = CPolyG.cextendedEuclideanSplit fuel dn ds r u w := by
  rw [cextendedEuclideanSplitWf, CPolyG.cextendedEuclideanSplit,
    cdivmodWf_eq_of_fuel fuel (cmulG u r) ds hur]

omit [CFieldSpec α] in
/-- **Bridge — `cdiophantineGWf` equals the fuel'd `cdiophantineG` at any sufficient fuel.** With
`(cnormG p).length ≤ fuel`, `(cnormG q).length < fuel` (for the extended-Euclid descent `cgcdWf`), and the
rescaled-reduced dividend `S = cscaleG (cleadG (cgcdWf p q).1)⁻¹ (cmulG rhs (cgcdWf p q).2.1)` short enough
(`(cnormG S).length ≤ fuel`, for the `cdivmodWf`), `cdiophantineGWf p q rhs = cdiophantineG fuel p q rhs`.
The bounds live only here; `cdiophantineGWf` carries no fuel. The extended Euclid is bridged by
`cgcdWf_eq_of_fuel` and the mod-reduction by `cdivmodWf_eq_of_fuel`. -/
theorem cdiophantineGWf_eq_of_fuel [CFieldSpec α] (fuel : ℕ) (p q rhs : CPolyG α)
    (hp : (cnormG p : List α).length ≤ fuel) (hq : (cnormG q : List α).length < fuel)
    (hS : (cnormG (cscaleG (CField.inv (cleadG (cgcdWf p q).1))
        (cmulG rhs (cgcdWf p q).2.1)) : List α).length ≤ fuel) :
    cdiophantineGWf p q rhs = CPolyG.cdiophantineG fuel p q rhs := by
  rw [cdiophantineGWf, CPolyG.cdiophantineG, cgcdWf_eq_of_fuel fuel p q hp hq]
  rw [cgcdWf_eq_of_fuel fuel p q hp hq] at hS
  rcases hgcd : cgcdExtG fuel p q with ⟨g, s, t⟩
  rw [hgcd] at hS
  simp only at hS ⊢
  rw [cdivmodWf_eq_of_fuel fuel _ q hS]

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Fuel-free inner Hermite loop** over a squarefree factor `v` (multiplicity `i`, `u = d/vⁱ`), driven
by the downward counter `j` (§5.3, quadratic version, p.139): the fuel-free companion of
`cHermiteReduceTowerInner`. Each step solves `b·(u·Dv) + c·v = −a/j` with the **fuel-free** Bézout solver
`cdiophantineGWf` (`Dv = cmonomialDeriv Dt v` the *monomial* derivation), accumulates the rational summand
`b/vʲ` into `g`, and updates `a ← −j·c − u·Db`. The recursion is **structural** on `j` (no fuel measure —
`cmonomialDeriv` carries no fuel, the Bézout solve is fuel-free), so **no fuel at runtime**. -/
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
