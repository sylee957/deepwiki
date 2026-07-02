import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Computing Bronstein Exercise 2.5 with the executable LRT engine, over `ℚ(θ)` (§2.9, p.73)
**Exercise 2.5 ([66]).** Compute, by Lazard–Rioboo–Trager,
`∫ (x⁴+x³+x²+x+1) / (x⁵+x⁴+2x³+2x²−2+4√(−1+√3)) dx`,
and answer: **what happens if the subresultants are not made primitive before evaluating them?**

The denominator's constant term involves the algebraic number `θ = √(−1+√3) = √(√3−1)`, so the integrand
is genuinely over the **field extension** `ℚ(θ)`, not over `ℚ`: `θ² = √3−1`, hence `(θ²+1)² = 3`, i.e.
`θ⁴+2θ²−2 = 0`. So `θ` is a root of the (Eisenstein-at-2, irreducible) `q(y) = y⁴+2y²−2`, and
`K := ℚ(θ) = ℚ[y]/(q)` is a degree-4 field. We therefore build a small **computable extension carrier**:
`ECoeff := CPoly` interpreted **mod `q`** (`ered`), with field arithmetic `eadd`/`emul`/`einv` (inverses
via `cgcdExt`, since `ℚ[y]/(q)` is a field for irreducible `q`). On top of it we re-run the LRT engine of
`SubresultantCompute` one level up: `EPoly := List ECoeff = K[t]`, then `EBPoly := List EPoly = K[t][x]`,
with the same pseudo-division / subresultant-PRS / mod-`R` monic-in-`x` normalization, now over `K[t]`.

`A = x⁴+x³+x²+x+1`, `D = x⁵+x⁴+2x³+2x²+(−2+4θ)`. `D` is squarefree; the LRT Rothstein–Trager resultant
`R(t) = res_x(D, A−t·D') ∈ K[t]` is **degree 5 and squarefree** (five distinct residues), so the LRT
subresultant index is `j = 1`: the per-residue gcd is **linear in `x`**, `S₁ = x + c₀(t)` with
`c₀(t) ∈ K[t]/(R)`. The computed answer is `∫ A/D = ∑_{R(a)=0} a·log(x + c₀(a))`.

**What happens if the subresultants are NOT made primitive (the heart of the exercise, Mulders [66]).**
The *raw* degree-1 subresultant returned by the PRS is, with small integer (over `K`) coefficients,
`S₁ʳᵃʷ = c₁(t)·x + c₀ʳᵃʷ(t)` where the **leading `x`-coefficient `c₁(t)` is NOT `1`** — it is a genuine
**degree-3 polynomial in `t`** (`c₁(t) = 1 + (−2−12θ)t + (−32+104θ)t² + (96−224θ)t³`). So the raw
subresultant is **not monic in `x`** and carries a spurious **`K[t]`-content factor**: it equals
`content(t) · primitive(t,x)` for an explicit non-unit `content(t) ∈ K[t]` of `t`-degree `1`. If one
evaluates this raw subresultant at the residues `R(a)=0` without first making it primitive, the logarithm
argument is multiplied by `content(a)`, i.e. one gets `log(content(a)·S₁(a,x))` instead of the clean
`log(S₁(a,x))` — a spurious extra `log(content(a))` term (and the leading coefficient `c₁(a)` need not be
a unit at every residue, so the argument is not even monic). Making the subresultant **primitive in `x`**
(strip `content(t)`) and **monic in `x` over `K[t]/(R)`** removes this, giving the clean `x + c₀(t)`.

All of this is `native_decide`-pinned (Mathlib `ℚ[X]` is noncomputable; kernel `decide` stalls on the
GMP `ℚ`/`ℚ(θ)` arithmetic, so `native_decide` is used throughout). -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The computable extension field `K = ℚ(θ) = ℚ[y]/(q)`, `q = y⁴+2y²−2` -/

/-- **The minimal polynomial** `q(y) = y⁴+2y²−2` of `θ = √(−1+√3)` as a `CPoly` (in `y`), low→high:
`[-2, 0, 2, 0, 1]`. Eisenstein at `2`, so irreducible over `ℚ`; thus `K := ℚ[y]/(q)` is a field. -/
def ex25_qmin : CPoly := [-2, 0, 2, 0, 1]

/-- **Fuel** for the inner `ℚ[y]` / `K`-arithmetic (`q` has degree 4; a generous bound). -/
abbrev ex25EF : ℕ := 40

/-- **The extension carrier** `ECoeff := CPoly` — a `ℚ[y]`-representative of an element of `K = ℚ(θ)`. -/
abbrev ECoeff := CPoly

/-- **Reduce a representative mod `q`** `ered c = c mod q`: the canonical degree-`< 4` representative of
`c ∈ K`. -/
def ered (c : ECoeff) : ECoeff := cmod ex25EF c ex25_qmin

/-- **`K`-addition** `eadd a b = (a+b) mod q`. -/
def eadd (a b : ECoeff) : ECoeff := ered (cadd a b)

/-- **`K`-negation** `eneg a = (−a) mod q`. -/
def eneg (a : ECoeff) : ECoeff := ered (cneg a)

/-- **`K`-subtraction** `esub a b = (a−b) mod q`. -/
def esub (a b : ECoeff) : ECoeff := ered (csub a b)

/-- **`K`-multiplication** `emul a b = (a·b) mod q`. -/
def emul (a b : ECoeff) : ECoeff := ered (cmul a b)

/-- **`K`-zero test** `eisZero a`: `true` iff `a ≡ 0 (mod q)`. -/
def eisZero (a : ECoeff) : Bool := cisZero (ered a)

/-- **`K`-inverse** `einv a = a⁻¹` in `K = ℚ[y]/(q)` (`q` irreducible ⇒ field): from the Bézout relation
`s·a + ·q = g` (constant `g`), `a⁻¹ ≡ s/g (mod q)`. -/
def einv (a : ECoeff) : ECoeff :=
  let (g, s, _) := cgcdExt ex25EF a ex25_qmin
  ered (cscale (clead g)⁻¹ s)

/-- **`K`-division** `ediv a b = a · b⁻¹` in `K`. -/
def ediv (a b : ECoeff) : ECoeff := emul a (einv b)

/-- **Embed a rational** `eFromQ r = r ∈ K` (reduced). -/
def eFromQ (r : ℚ) : ECoeff := ered (cnorm [r])

/-- **The generator** `etheta = θ = y ∈ K`. -/
def etheta : ECoeff := [0, 1]

/-- **The constant term of `D`** `ecD0 = −2 + 4θ ∈ K` (`= [-2, 4]`). -/
def ecD0 : ECoeff := eadd (eFromQ (-2)) (emul (eFromQ 4) etheta)

/-- **Exercise 2.5: `θ` satisfies `θ⁴ = 2 − 2θ²`** — `y⁴ mod q = 2 − 2y² = [2, 0, -2]`, the defining
relation of `K = ℚ(θ)`. Proved by `native_decide`. -/
theorem ex25_theta_pow4 : ered [0, 0, 0, 0, 1] = [2, 0, -2] := by native_decide

/-- **Exercise 2.5: `K` is a field** — `θ⁻¹ · θ = 1`, witnessing that the computable inverse `einv` is a
genuine `K`-inverse (`q` irreducible). Proved by `native_decide`. -/
theorem ex25_theta_inv : emul (einv etheta) etheta = [1] := by native_decide

/-! ### `EPoly := K[t]` — dense polynomials in `t` with coefficients in `K` -/

/-- **`K[t]` carrier** `EPoly := List ECoeff` (index = `t`-degree, low→high). -/
abbrev EPoly := List ECoeff

/-- **Normalize** a `K[t]`: reduce each coefficient mod `q`, strip trailing `K`-zeros. -/
def epnorm : EPoly → EPoly
  | [] => []
  | a :: as =>
    let a := ered a
    match epnorm as with
    | [] => if eisZero a then [] else [a]
    | r => a :: r

/-- **`K[t]`-addition** (coefficientwise). -/
def epadd : EPoly → EPoly → EPoly
  | [], q => q.map ered
  | p, [] => p.map ered
  | a :: as, b :: bs => eadd a b :: epadd as bs

/-- **`K[t]`-negation** (coefficientwise). -/
def epneg (p : EPoly) : EPoly := p.map eneg

/-- **`K[t]`-subtraction** `epsub p q = p + (−q)`. -/
def epsub (p q : EPoly) : EPoly := epadd p (epneg q)

/-- **`K`-scalar scale** `epscale c p`: multiply every `t`-coefficient by `c ∈ K`. -/
def epscale (c : ECoeff) (p : EPoly) : EPoly := p.map (emul c)

/-- **Shift in `t`** `epshift k p = tᵏ · p`. -/
def epshift : ℕ → EPoly → EPoly
  | 0, p => p
  | n + 1, p => [] :: epshift n p

/-- **`K[t]`-multiplication** (schoolbook convolution). -/
def epmul : EPoly → EPoly → EPoly
  | [], _ => []
  | a :: as, q => epadd (epscale a q) ([] :: epmul as q)

/-- **Leading `t`-coefficient** `eplead p ∈ K` (top nonzero coefficient, `[]` for zero). -/
def eplead (p : EPoly) : ECoeff := (epnorm p).getLast?.getD []

/-- **`K[t]`-zero test**. -/
def episZero (p : EPoly) : Bool := epnorm p == []

/-- **`t`-degree** of a `K[t]` (`(length of epnorm) − 1`, `0` for zero; paired with `episZero`). -/
def epdeg (p : EPoly) : ℕ := (epnorm p).length - 1

/-- **`K[t]` Euclidean division** `epdivmod fuel p q = (quotient, remainder)`, `deg rem < deg q` (over the
field `K`; `q ≠ 0`), fuel-bounded. -/
def epdivmod : ℕ → EPoly → EPoly → EPoly × EPoly
  | 0, p, _ => ([], epnorm p)
  | fuel + 1, p, q =>
    let p := epnorm p
    let q := epnorm q
    if episZero q then ([], [])
    else if p.length < q.length then ([], p)
    else
      let c := ediv (eplead p) (eplead q)
      let k := p.length - q.length
      let term := epshift k [c]
      let p' := epnorm (epsub p (epmul term q))
      let (quo, rem) := epdivmod fuel p' q
      (epadd term quo, rem)

/-- **`K[t]` quotient**. -/
def epquo (fuel : ℕ) (p q : EPoly) : EPoly := (epdivmod fuel p q).1

/-- **`K[t]` remainder**. -/
def epmod (fuel : ℕ) (p q : EPoly) : EPoly := (epdivmod fuel p q).2

/-- **`K[t]` extended gcd** `epgcdExt fuel a b = (g, s, t)` with `s·a + t·b = g` (over the field `K`). -/
def epgcdExt : ℕ → EPoly → EPoly → EPoly × EPoly × EPoly
  | 0, a, _ => (epnorm a, [eFromQ 1], [])
  | fuel + 1, a, b =>
    if episZero b then (epnorm a, [eFromQ 1], [])
    else
      let (q, r) := epdivmod (fuel + 1) a b
      let (g, s, t) := epgcdExt fuel b r
      (g, t, epsub s (epmul t q))

/-- **Make a `K[t]` monic** (lead coefficient `1` in `K`). -/
def epmonic (p : EPoly) : EPoly :=
  let p := epnorm p
  if episZero p then [] else epscale (einv (eplead p)) p

/-- **`K[t]`-derivative** (in `t`) `epderiv [a₀,a₁,…] = [a₁, 2a₂, …]`. -/
def epderiv : EPoly → EPoly
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from `t`-degree `k`, emit `k·a` (as a `K`-scalar) for each coefficient. -/
  go : ℕ → EPoly → EPoly
  | _, [] => []
  | k, a :: as => emul (eFromQ (k : ℚ)) a :: go (k + 1) as

/-! ### The Exercise 2.5 integrand `A/D` over `K` (each `x`-coefficient is a `K`-scalar) -/

/-- **`A = x⁴+x³+x²+x+1`** as an `EPoly` (`x`-coefficients in `K`, all `= 1`), index = `x`-degree. -/
def ex25A : EPoly := [eFromQ 1, eFromQ 1, eFromQ 1, eFromQ 1, eFromQ 1]

/-- **`D = x⁵+x⁴+2x³+2x²+(−2+4θ)`** as an `EPoly` (`x`-coefficients in `K`); the constant term is
`ecD0 = −2+4θ`, the only non-rational coefficient. -/
def ex25D : EPoly := [ecD0, eFromQ 2, eFromQ 2, eFromQ 2, eFromQ 1, eFromQ 1]

/-- **`D' = 5x⁴+4x³+6x²+4x`** (derivative of `D` *in `x`*; reuse `epderiv` since `D`'s `x`-coefficients
sit in `K` and `epderiv` is the dense degree-shift derivative). -/
def ex25Dp : EPoly := epderiv ex25D

/-! ### The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D') ∈ K[t]`, by sampling + interpolation -/

/-- **`K`-power** `epow_K c n = cⁿ ∈ K`. -/
def epow_K (c : ECoeff) : ℕ → ECoeff
  | 0 => eFromQ 1
  | n + 1 => emul c (epow_K c n)

/-- **Univariate resultant over the field `K`** `eresultant fuel p q = res_x(p, q) ∈ K`, via the
Euclidean-PRS identity `res(p,q) = (−1)^(dp·dq)·lc(q)^(dp−dr)·res(q,r)` (`r = p mod q`), bottoming out at
`res(p, c) = c^(deg p)` for constant `c`. The `K[x]` analog of `cresultant`. -/
def eresultant : ℕ → EPoly → EPoly → ECoeff
  | 0, _, _ => eFromQ 0
  | fuel + 1, p, q =>
    let p := epnorm p
    let q := epnorm q
    if episZero q then (if p.length ≤ 1 then eFromQ 1 else eFromQ 0)
    else if q.length ≤ 1 then epow_K (eplead q) (epdeg p)
    else if p.length < q.length then
      let s := epow_K (eneg (eFromQ 1)) (epdeg p * epdeg q)
      emul s (eresultant fuel q p)
    else
      let r := epnorm (epmod (fuel + 1) p q)
      let sign := epow_K (eneg (eFromQ 1)) (epdeg p * epdeg q)
      let lcpow := epow_K (eplead q) (epdeg p - epdeg r)
      emul (emul sign lcpow) (eresultant fuel q r)

/-- **One sample of the RT resultant** `ex25Rsample a = res_x(D, A − a·D') ∈ K` at `a ∈ K`. -/
def ex25Rsample (a : ECoeff) : ECoeff := eresultant 60 ex25D (epsub ex25A (epscale a ex25Dp))

/-- **Lagrange basis numerator over `K`** `∏ (t − xⱼ)`. -/
def elagNum : List ECoeff → EPoly
  | [] => [eFromQ 1]
  | x :: xs => epmul [eneg x, eFromQ 1] (elagNum xs)

/-- **Lagrange interpolation over `K`** `einterpolate pts = R(t) ∈ K[t]` with `R(xₖ) = yₖ` (distinct
abscissas in `K`); the `K`-field inverses make the scalar `1/∏(xₖ−xⱼ)` available. -/
def einterpolate (pts : List (ECoeff × ECoeff)) : EPoly :=
  let xs := pts.map Prod.fst
  let term : ECoeff × ECoeff → EPoly := fun (xk, yk) =>
    let others := xs.filter (fun z => ! (ered z == ered xk))
    let num := elagNum others
    let denom := others.foldl (fun acc xj => emul acc (esub xk xj)) (eFromQ 1)
    epscale (ediv yk denom) num
  epnorm (pts.foldl (fun acc p => epadd acc (term p)) [])

/-- **The Rothstein–Trager resultant** `ex25Rt = R(t) = res_x(D, A − t·D') ∈ K[t]` of Exercise 2.5,
recovered by sampling `R(k)` at `k = 0,…,5` (`deg_t R ≤ deg_x D = 5`) and interpolating over `K`. -/
def ex25Rt : EPoly :=
  einterpolate ((List.range 6).map (fun k => (eFromQ (k : ℚ), ex25Rsample (eFromQ (k : ℚ)))))

/-- **The monic squarefree RT resultant** `ex25Rsqfree = R / gcd(R, R')`, monic over `K`. The residue
ring `K[t]/(R)` over which the LRT log argument is normalized. -/
def ex25Rsqfree : EPoly :=
  let (g, _, _) := epgcdExt 60 ex25Rt (epderiv ex25Rt)
  epmonic (epquo 60 ex25Rt g)

/-- **Exercise 2.5: `R(t)` is degree 5** (five residues): the RT resultant has `6` `t`-coefficients.
Proved by `native_decide`. -/
theorem ex25_resultant_deg : ex25Rt.length = 6 := by native_decide

/-- **Exercise 2.5: `R(t)` is squarefree** — the monic `gcd_t(R, R')` is `1`, so all five residues are
distinct (multiplicity one). Hence no multiplicity splitting; the LRT subresultant index is `j = 1`
(per-residue gcd linear in `x`). Proved by `native_decide`. -/
theorem ex25_resultant_squarefree :
    epmonic (epgcdExt 60 ex25Rt (epderiv ex25Rt)).1 = [[1]] := by native_decide

/-- **Exercise 2.5: the squarefree resultant is degree 5** (monic, `6` coefficients) — confirms the
five distinct residues survive as `K[t]/(R)`. Proved by `native_decide`. -/
theorem ex25_resultant_sqfree_deg : ex25Rsqfree.length = 6 := by native_decide

/-! ### `EBPoly := K[t][x]` — the bivariate subresultant carrier (`x`-poly, `K[t]`-coefficients) -/

/-- **`K[t][x]` carrier** `EBPoly := List EPoly` (index = `x`-degree, coefficients in `K[t]`). -/
abbrev EBPoly := List EPoly

/-- **Normalize** an `EBPoly` (normalize each `K[t]`-coefficient, strip trailing zeros). -/
def ebnorm : EBPoly → EBPoly
  | [] => []
  | a :: as =>
    let a := epnorm a
    match ebnorm as with
    | [] => if episZero a then [] else [a]
    | r => a :: r

/-- **`EBPoly`-addition** in `x` (coefficientwise in `K[t]`). -/
def ebadd : EBPoly → EBPoly → EBPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => epadd a b :: ebadd as bs

/-- **`EBPoly`-negation**. -/
def ebneg (p : EBPoly) : EBPoly := p.map epneg

/-- **`EBPoly`-subtraction**. -/
def ebsub (p q : EBPoly) : EBPoly := ebadd p (ebneg q)

/-- **Scale by a `K[t]` scalar** `ebscaleC c p`. -/
def ebscaleC (c : EPoly) (p : EBPoly) : EBPoly := p.map (epmul c)

/-- **Shift in `x`** `ebshift k p = xᵏ · p`. -/
def ebshift : ℕ → EBPoly → EBPoly
  | 0, p => p
  | n + 1, p => [] :: ebshift n p

/-- **`EBPoly`-multiplication** in `x` (schoolbook). -/
def ebmul : EBPoly → EBPoly → EBPoly
  | [], _ => []
  | a :: as, q => ebadd (ebscaleC a q) ([] :: ebmul as q)

/-- **`EBPoly`-zero test**. -/
def ebisZero (p : EBPoly) : Bool := ebnorm p == []

/-- **`x`-degree** of an `EBPoly`. -/
def ebdeg (p : EBPoly) : ℕ := (ebnorm p).length - 1

/-- **Leading `x`-coefficient** `eblc p ∈ K[t]` (top nonzero `x`-coefficient). -/
def eblc (p : EBPoly) : EPoly := (ebnorm p).getLast?.getD []

/-- **Pseudo-remainder over `K[t]`** `ebpsremainder fuel p q = prem(p, q)` (multiply by `lc(q)` powers, no
`K[t]`-division), `deg_x prem < deg_x q`. -/
def ebpsremainder : ℕ → EBPoly → EBPoly → EBPoly
  | 0, p, _ => ebnorm p
  | fuel + 1, p, q =>
    let p := ebnorm p
    let q := ebnorm q
    if ebisZero q then ebnorm p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := eblc q
      let lcp := eblc p
      let p' := ebnorm (ebsub (ebscaleC lcq p) (ebscaleC lcp (ebshift k q)))
      ebpsremainder fuel p' q

/-- **Exact `K[t]`-scalar division** `ebdivC fuel p c = p / c` (divide every `x`-coefficient by `c ∈ K[t]`,
exact in the subresultant PRS). -/
def ebdivC (fuel : ℕ) (p : EBPoly) (c : EPoly) : EBPoly :=
  ebnorm (p.map (fun a => epquo fuel a c))

/-- **`K[t]`-power** `eppow c n = cⁿ ∈ K[t]`. -/
def eppow (c : EPoly) : ℕ → EPoly
  | 0 => [eFromQ 1]
  | n + 1 => epmul c (eppow c n)

/-- **Subresultant PRS over `K[t]`** `esubresPRS fuel P Q` (Collins–Brown), the LRT log-argument chain in
`x`. Same recurrence as `subresPRS` (`ψ' = (−lc)^δ / ψ^{δ−1}`, `β = −lc·ψ'^δ`, `Rᵢ₊₂ = prem/β`) but with
exact divisions over `K[t]`. -/
def esubresPRS (fuel : ℕ) (P Q : EBPoly) : List EBPoly :=
  let rec go : ℕ → EBPoly → EBPoly → EPoly → ℕ → List EBPoly
    | 0, _, _, _, _ => []
    | fo + 1, Ri_1, Ri, psi, deltaPrev =>
      if ebisZero Ri then []
      else
        let lcRi_1 := eblc Ri_1
        let negLc := epneg lcRi_1
        let psi' := if deltaPrev = 0 then psi
          else epquo fuel (eppow negLc deltaPrev) (eppow psi (deltaPrev - 1))
        let beta := epmul negLc (eppow psi' deltaPrev)
        let pr := ebpsremainder fuel Ri_1 Ri
        let Ri1 := ebdivC fuel pr beta
        let deltaNew := ebdeg Ri - ebdeg Ri1
        Ri :: go fo Ri Ri1 psi' deltaNew
  P :: go fuel P Q [eneg (eFromQ 1)] (ebdeg P - ebdeg Q)

/-- **The `x`-degree-`j` subresultant** `ebsubresultantGcd fuel j P Q` (the element of `esubresPRS` of
`x`-degree `j`), or `[]` if none. -/
def ebsubresultantGcd (fuel j : ℕ) (P Q : EBPoly) : EBPoly :=
  ((esubresPRS fuel P Q).filter (fun R => decide (ebdeg R = j ∧ ¬ ebisZero R))).getLast?.getD []

/-- **`K[t]`-content in `x`** `ebcontentX fuel p = gcd over K[t] of the x-coefficients` — the common
`K[t]`-factor of `p` viewed as a polynomial in `x`. -/
def ebcontentX (fuel : ℕ) (p : EBPoly) : EPoly :=
  (ebnorm p).foldl (fun g c => (epgcdExt fuel g c).1) []

/-- **Primitive part in `x`** `ebprimitivePartX fuel p = p / content_x(p)` (strip the `K[t]`-content). -/
def ebprimitivePartX (fuel : ℕ) (p : EBPoly) : EBPoly :=
  let p := ebnorm p
  let g := ebcontentX fuel p
  if episZero g then p else ebnorm (p.map (fun c => epquo fuel c g))

/-- **Reduce a `K[t]` mod `R`** `credRE fuel R c = c mod R` — representative in `K[t]/(R)`. -/
def credRE (fuel : ℕ) (R c : EPoly) : EPoly := epmod fuel c R

/-- **Inverse of a `K[t]` mod `R`** `einvModR fuel R c = c⁻¹` in `K[t]/(R)` (assumes `gcd(c, R)` constant —
true for a unit, e.g. the leading `x`-coefficient at a residue). -/
def einvModR (fuel : ℕ) (R c : EPoly) : EPoly :=
  let (g, s, _) := epgcdExt fuel c R
  credRE fuel R (epscale (einv (eplead g)) s)

/-- **Make an `EBPoly` monic in `x` over `K[t]/(R)`** `ebmonicXmodR fuel R p`: reduce mod `R`, then scale
every `x`-coefficient by the inverse (mod `R`) of the leading `x`-coefficient (Exercise 2.7's
monic-in-`x` normalization, now over `K[t]/(R)`). -/
def ebmonicXmodR (fuel : ℕ) (R : EPoly) (p : EBPoly) : EBPoly :=
  let p := ebnorm (p.map (fun c => credRE fuel R c))
  if ebisZero p then []
  else
    let inv := einvModR fuel R (eblc p)
    ebnorm (p.map (fun c => credRE fuel R (epmul c inv)))

/-! ### Building `A − t·D'` over `K[t]`, and running the LRT -/

/-- **Lift an `EPoly` (`= K[x]`) into `EBPoly`** `eliftToEB p`: each `x`-coefficient `a ∈ K` becomes the
constant `K[t]`-polynomial `[a]`. -/
def eliftToEB (p : EPoly) : EBPoly := p.map (fun a => [a])

/-- **The variable `t` as a `K[t]`** `etVar = [0, 1]`. -/
def etVar : EPoly := [eFromQ 0, eFromQ 1]

/-- **The LRT second operand** `ex25ArgAmtD' = A − t·D'` as an `EBPoly` (`A` lifted, minus `t·D'`). -/
def ex25ArgAmtD' : EBPoly := ebsub (eliftToEB ex25A) (ebscaleC etVar (eliftToEB ex25Dp))

/-- **The raw degree-1 LRT subresultant** `ex25S1raw = S₁ʳᵃʷ(D, A − t·D') ∈ K[t][x]` of Exercise 2.5,
straight from the subresultant PRS — *before* any primitive/monic normalization. -/
def ex25S1raw : EBPoly := ebsubresultantGcd 60 1 (eliftToEB ex25D) ex25ArgAmtD'

/-- **The `K[t]`-content factor** `ex25content = content_x(S₁ʳᵃʷ)` — the spurious common factor the raw
subresultant carries (the answer to "what if not made primitive"). -/
def ex25content : EPoly := ebcontentX 60 ex25S1raw

/-- **The primitive part** `ex25S1prim = S₁ʳᵃʷ / content` (made primitive in `x`). -/
def ex25S1prim : EBPoly := ebprimitivePartX 60 ex25S1raw

/-- **The normalized LRT log argument** `ex25S1 = S₁(t,x)`: the primitive subresultant reduced mod `R` and
made monic in `x` over `K[t]/(R)` — the clean `x + c₀(t)` that goes inside the logarithms. -/
def ex25S1 : EBPoly := ebmonicXmodR 60 ex25Rsqfree ex25S1prim

/-! ### The "compute" deliverable and the primitivity contrast -/

/-- **Exercise 2.5, the subresultant-PRS `x`-degree chain** is `[5, 4, 3, 1, 0]` — it **drops from `3` to
`1`** (a defective / non-normal PRS, skipping `x`-degree `2`), so the degree-`1` element is the LRT log
argument. Proved by `native_decide`. -/
theorem ex25_prs_degrees :
    (esubresPRS 60 (eliftToEB ex25D) ex25ArgAmtD').map ebdeg = [5, 4, 3, 1, 0] := by native_decide

/-- **Exercise 2.5, the RAW degree-1 subresultant** (the "compute" output *before* normalization):
`S₁ʳᵃʷ = c₁(t)·x + c₀ʳᵃʷ(t)` with, over `K = ℚ(θ)` (`θ = y`),
`c₀ʳᵃʷ(t) = 1 + (−2−12θ)t + (−32+104θ)t² + (96−224θ)t³`,
`c₁(t) = (3−4θ) + (−40+52θ)t + (184−224θ)t² + (−288+320θ)t³`.
Small integer coefficients over `K`, pinned by `native_decide`. (Inner lists are `K`-elements as
`CPoly`-in-`θ`, low→high; outer two entries are the `x⁰`- and `x¹`-coefficients, low→high in `x`.) -/
theorem ex25_raw_subresultant :
    ex25S1raw.map (·.map cnorm) =
      [[[1], [-2, -12], [-32, 104], [96, -224]],
       [[3, -4], [-40, 52], [184, -224], [-288, 320]]] := by native_decide

/-- **Exercise 2.5 — what happens if the subresultants are NOT made primitive (the crux).** The raw
subresultant `S₁ʳᵃʷ` is **not monic in `x`**: its leading `x`-coefficient `c₁(t)` is a genuine **degree-3
polynomial in `t`** (`epdeg = 3`), not the constant `1`. So evaluating the raw subresultant at the
residues `R(a)=0` *without first making it primitive* would put the non-constant `c₁(a)` (and a spurious
`K[t]`-content factor, see `ex25_raw_eq_content_mul_primitive`) inside the logarithm — i.e. a wrong,
non-monic log argument, contributing an extra `log(c₁(a)·…)` rather than the clean `log(x + c₀(a))`.
Both `x`-coefficients are in fact degree-3 in `t`; the leading one `c₁(t) ≠ 1` is the obstruction.
Proved by `native_decide`. -/
theorem ex25_raw_not_monic_in_x : epdeg (eblc ex25S1raw) = 3 := by native_decide

/-- **Exercise 2.5 — the spurious content is a non-unit.** The `K[t]`-content `content_x(S₁ʳᵃʷ)` the raw
subresultant carries has `t`-degree `1` (`epdeg = 1`), i.e. it is a non-constant polynomial in `t` — the
spurious factor that primitivity removes. Proved by `native_decide`. -/
theorem ex25_content_nonunit : epdeg ex25content = 1 := by native_decide

/-- **Exercise 2.5 — the primitivity factorization `S₁ʳᵃʷ = content(t) · primitive(t,x)`.** The raw
subresultant equals its `K[t]`-content times its `x`-primitive part exactly. This **is** "what happens if
not made primitive": the raw log argument is the clean primitive one multiplied by the spurious non-unit
`content(t) ∈ K[t]` (`ex25_content_nonunit`), which would inject a stray `log(content(a))` term at each
residue. Making the subresultant primitive in `x` strips `content(t)`. Proved by `native_decide`. -/
theorem ex25_raw_eq_content_mul_primitive :
    ex25S1raw = ebscaleC ex25content ex25S1prim := by native_decide

/-- **Exercise 2.5, the computed LRT log argument** `S₁(t,x) = x + c₀(t)` — the primitive subresultant made
**monic in `x`** over `K[t]/(R)`: it is **linear in `x`** (two `x`-coefficients) with leading `x`-coefficient
`1`. So the per-residue gcd `gcd(D, A − a·D')` is `x + c₀(a)`, and the integral is
`∫ A/D = ∑_{R(a)=0} a · log(x + c₀(a))` (five complex-log terms, `a` over the degree-5 residue ring
`K[t]/(R)`). The monic normalization is exactly what removes the raw subresultant's spurious leading
coefficient and content. Proved by `native_decide`. -/
theorem ex25_logpart_monic_linear :
    ex25S1.length = 2 ∧ eblc ex25S1 = [[1]] := by native_decide

/-! ### `#eval` prints (the readable answer) -/

-- **`D` over `K`**: `x⁵+x⁴+2x³+2x²+(−2+4θ)` (constant term `[-2, 4] = −2+4θ`).
#eval ex25D.map cnorm

-- **The RT resultant `R(t) ∈ K[t]`** (degree 5; coefficients in `K = ℚ(θ)`, each a `CPoly`-in-`θ`).
#eval ex25Rt.map cnorm

-- **The RAW degree-1 subresultant** (small integers over `K`): leading `x`-coeff is a degree-3
-- `t`-polynomial — NOT monic, the primitivity failure.
#eval ex25S1raw.map (·.map cnorm)

-- **The `K[t]`-content factor** (degree 1 in `t`): the spurious factor stripped by making primitive.
#eval ex25content.map cnorm

-- **The clean LRT log argument** `S₁ = x + c₀(t)` (monic in `x`; `c₀(t)` a degree-4 residue polynomial
-- over `K[t]/(R)`): the answer to `∫ A/D = ∑_{R(a)=0} a·log(x + c₀(a))`.
#eval ex25S1.map (·.map cnorm)

end Compute

end DeepWiki.SymbolicIntegration
