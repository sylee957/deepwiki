import DeepWiki.SymbolicIntegration.Compute.RtResultant

/-! # Computable bivariate subresultant gcd / LRT log argument over `ℚ[t]` (Bronstein §2.5/§2.6)
The Lazard–Rioboo–Trager logarithmic part puts `S(t,x) = gcd_x(D(x), A(x) − t·D'(x))` inside the
logarithms of `∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. This gcd is genuinely **bivariate** (`ℚ[t][x]`): it
is `1` at a generic `t`, so — unlike the univariate Rothstein–Trager resultant `R(t)` of
`RtResultantCompute` — it **cannot** be recovered by evaluation + interpolation. It needs the
**subresultant polynomial-remainder sequence** built from **pseudo-division** over the non-field
coefficient ring `ℚ[t]`.

We give a `#eval`-able rendering on a bivariate carrier `BPoly := List CPoly`: a polynomial in `x`
whose coefficients are `CPoly := List ℚ` (`= ℚ[t]`), index = `x`-degree low→high. `badd`/`bsub`/…/`bmul`
are the `BPoly` algebra (coefficient ops through `RtResultantCompute`/`LogToAtanCompute`'s `CPoly`
arithmetic); `bpsremainder` is the **pseudo-remainder** `prem(p,q)` (multiply by `lc(q)` powers, no
`ℚ[t]` division); `bsubresultantGcd` runs the pseudo-PRS, taking the last nonzero remainder — the
`gcd_x` up to a `ℚ[t]` content factor. On **Example 2.4.1** `A = x⁴−3x²+6, D = x⁶−5x⁴+5x²+4` this
returns the LRT log argument `x³ + 2t·x² − 3x − 4t` (the Czichowski/Gröbner basis element of
Example 2.6.1, `B = {4t²+1, x³+2tx²−3x−4t}`), pinned by `native_decide`. Agreement with the
noncomputable `lrtSubresultant` is **proven** in `SubresultantCorrectness`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The bivariate carrier `BPoly = List CPoly` (`ℚ[t][x]`) -/

/-- **Bivariate dense carrier** `BPoly := List CPoly` = a polynomial in `x` whose coefficients are
`CPoly` (`= ℚ[t]`), index = `x`-degree low→high. So `[[0,-4],[-3],[0,2],[1]]` is
`x³ + 2t·x² − 3x − 4t` (`x⁰`-coeff `−4t`, `x¹`-coeff `−3`, `x²`-coeff `2t`, `x³`-coeff `1`). -/
abbrev BPoly := List CPoly

/-- **Normalize** a `BPoly`: normalize each `CPoly` coefficient, then strip trailing (high-`x`-degree)
zero coefficients, so the zero polynomial becomes `[]`. -/
def bnorm : BPoly → BPoly
  | [] => []
  | a :: as =>
    let a := cnorm a
    match bnorm as with
    | [] => if cisZero a then [] else [a]
    | r => a :: r

/-- **Coefficientwise addition** of two `BPoly`s in `x` (each `x`-coefficient added via `cadd`). -/
def badd : BPoly → BPoly → BPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => cadd a b :: badd as bs

/-- **Negation** of a `BPoly`, each `x`-coefficient negated via `cneg`. -/
def bneg (p : BPoly) : BPoly := p.map cneg

/-- **Subtraction** of `BPoly`s, `p − q := p + (−q)`. -/
def bsub (p q : BPoly) : BPoly := badd p (bneg q)

/-- **Scale by a `CPoly`** (a `ℚ[t]` scalar) `bscaleC c p`: multiply every `x`-coefficient by `c`. -/
def bscaleC (c : CPoly) (p : BPoly) : BPoly := p.map (cmul c)

/-- **Shift in `x`** `bshift k p = xᵏ · p`: prepend `k` zero (`= []`) `x`-coefficients. -/
def bshift : ℕ → BPoly → BPoly
  | 0, p => p
  | n + 1, p => [] :: bshift n p

/-- **Polynomial multiplication** of `BPoly`s in `x` (schoolbook convolution; `x`-coefficient products
use `CPoly`'s `cmul`, sums use `cadd`). -/
def bmul : BPoly → BPoly → BPoly
  | [], _ => []
  | a :: as, q => badd (bscaleC a q) ([] :: bmul as q)

/-- **Zero test** for a `BPoly`: `true` iff it normalizes to `[]`. -/
def bisZero (p : BPoly) : Bool := bnorm p == []

/-- **`x`-degree** of a `BPoly` as a `ℕ`: `(length of bnorm p) − 1`, with `bdeg 0 = 0` (paired with
`bisZero` at call sites). -/
def bdeg (p : BPoly) : ℕ := (bnorm p).length - 1

/-- **Leading `x`-coefficient** `blc p ∈ CPoly` (`= ℚ[t]`): the top nonzero `x`-coefficient, `[]` (zero)
for the zero polynomial. -/
def blc (p : BPoly) : CPoly := (bnorm p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `ℚ[t]` -/

/-- **Pseudo-remainder** `bpsremainder fuel p q = prem(p, q)`: the pseudo-division remainder over the
non-field coefficient ring `ℚ[t]`. Satisfies `lc(q)^(deg p − deg q + 1) · p = s·q + prem` for some `s`,
with `deg prem < deg q`. Standard loop: while `deg p ≥ deg q`, replace `p` by
`lc(q)·p − lc(p)·xᵏ·q` (`k = deg p − deg q`), staying in `BPoly` (no `ℚ[t]` division). Fuel-bounded
(one step per degree drop; `fuel ≥ deg p − deg q + 1` is safe). -/
def bpsremainder : ℕ → BPoly → BPoly → BPoly
  | 0, p, _ => bnorm p
  | fuel + 1, p, q =>
    let p := bnorm p
    let q := bnorm q
    if bisZero q then bnorm p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := blc q
      let lcp := blc p
      -- `lc(q)·p − lc(p)·xᵏ·q`: kills the leading term, stays in `ℚ[t][x]`.
      let p' := bnorm (bsub (bscaleC lcq p) (bscaleC lcp (bshift k q)))
      bpsremainder fuel p' q

/-! ### `ℚ[t]`-content management (so the LRT gcd comes out clean) -/

/-- **`ℚ[t]`-content** of a `BPoly`: the `CPoly`-gcd (over the field `ℚ`, via `cgcdExt`) of all its
`x`-coefficients — the common `ℚ[t]` factor of the polynomial in `x`. -/
def bcontentX (fuel : ℕ) (p : BPoly) : CPoly :=
  (bnorm p).foldl (fun g c => (cgcdExt fuel g c).1) []

/-- **Strip the `ℚ[t]`-content in `x`** `bprimitivePartX fuel p = p / content_x(p)`: divide every
`x`-coefficient by the content (exact `CPoly` division over `ℚ`), giving the `ℚ[t]`-primitive part.
Leaves `[]` unchanged. -/
def bprimitivePartX (fuel : ℕ) (p : BPoly) : BPoly :=
  let p := bnorm p
  let g := bcontentX fuel p
  if cisZero g then p else bnorm (p.map (fun c => cdiv fuel c g))

/-! ### Reduction and inversion modulo a `ℚ[t]` factor `R(t)` (the residue ring `ℚ[t]/(R)`)
The degree-`j` subresultant `Sⱼ(D, A−tD')` is the per-residue gcd `Gₐ` only **modulo** the resultant
factor `Qᵢ(t)` carrying that residue (here `R = 4t²+1`): `Sⱼ mod R` then made **monic in `x`** over the
residue ring `ℚ[t]/(R)` is the book's normalized log argument `S(t,x)` (Exercise 2.7's monic-in-`x`
normalization, the "units in `K[t]/(Qᵢ)`" step). `ℚ[t]/(R)` is a ring; the leading `x`-coefficient is a
**unit** there (Ex 2.7 regularity `sᵢ(a) ≠ 0`), so monic normalization is exact via the extended-Euclidean
inverse. -/

/-- **Reduce a `CPoly` modulo `R`** `credR fuel R c = c mod R` — the representative in `ℚ[t]/(R)`. -/
def credR (fuel : ℕ) (R c : CPoly) : CPoly := cmod fuel c R

/-- **Reduce every `x`-coefficient of a `BPoly` modulo `R`** `bredR fuel R p`: the image of `p` in
`(ℚ[t]/(R))[x]`. -/
def bredR (fuel : ℕ) (R : CPoly) (p : BPoly) : BPoly := bnorm (p.map (credR fuel R))

/-- **Inverse of a `CPoly` modulo `R`** `cinvMod fuel R c = c⁻¹` in `ℚ[t]/(R)` (assumes `gcd(c, R)` is a
nonzero constant — true when `c` is a unit mod `R`, e.g. the leading `x`-coefficient at a residue): from
the Bézout relation `s·c + ·R = g` (constant `g`), `c⁻¹ ≡ s/g (mod R)`. -/
def cinvMod (fuel : ℕ) (R c : CPoly) : CPoly :=
  let (g, s, _) := cgcdExt fuel c R
  credR fuel R (cscale (clead g)⁻¹ s)

/-- **Make a `BPoly` monic in `x` over `ℚ[t]/(R)`** `bmonicXmodR fuel R p`: reduce mod `R`, then multiply
every `x`-coefficient by the inverse (mod `R`) of the leading `x`-coefficient and reduce again — so the
result is monic in `x` with coefficients in `ℚ[t]/(R)`. This is Exercise 2.7's monic-in-`x` log-argument
normalization. -/
def bmonicXmodR (fuel : ℕ) (R : CPoly) (p : BPoly) : BPoly :=
  let p := bredR fuel R p
  if bisZero p then []
  else
    let inv := cinvMod fuel R (blc p)
    bnorm (p.map (fun c => credR fuel R (cmul c inv)))

/-! ### Exact `ℚ[t]`-division of a `BPoly` by a `CPoly`, and `ℚ[t]` powers -/

/-- **Exact `ℚ[t]`-scalar division** `bdivC fuel p c = p / c`: divide every `x`-coefficient of `p` by the
`CPoly` (`= ℚ[t]`) scalar `c` via `cdiv` (the division is exact in the subresultant PRS — `c = βᵢ` always
divides the pseudo-remainder over `ℚ[t]`). -/
def bdivC (fuel : ℕ) (p : BPoly) (c : CPoly) : BPoly := bnorm (p.map (fun a => cdiv fuel a c))

/-- **`ℚ[t]`-power** `cpowP c n = cⁿ` (`CPoly` power, by `ℕ`-recursion via `cmul`). -/
def cpowP (c : CPoly) : ℕ → CPoly
  | 0 => [1]
  | n + 1 => cmul c (cpowP c n)

/-! ### The subresultant PRS (Collins–Brown) — the LRT log-argument chain in `x`

The bare Euclidean pseudo-remainder sequence's last nonzero element is the `gcd_x` *over `ℚ(t)`* — which
is `1` here (the gcd is `1` at generic `t`), so it is **not** the LRT log argument. The LRT log argument
is the **subresultant** `Sⱼ(D, A−tD')` at the index `j` of the last nonzero *specialized* remainder; the
subresultant PRS (Collins 1967 / Brown–Traub) computes the whole chain with **exact `ℚ[t]` divisions**
that strip the pseudo-remainder `lc`-power inflation, so the degree-`j` element comes out as the true
subresultant (here, up to sign, the book's `x³+2tx²−3x−4t`). -/

/-- **Subresultant polynomial-remainder sequence** `subresPRS fuel P Q = [R₁, R₂, R₃, …]` (Collins–Brown),
each `Rᵢ ∈ BPoly` (`= ℚ[t][x]`), with `R₁ = P`, `R₂ = Q` (`deg P ≥ deg Q`). The recurrence uses the
subresultant β-divisors: `δᵢ = deg Rᵢ − deg Rᵢ₊₁`, `ψ` accumulator updated by
`ψ' = (−lc Rᵢ)^δ / ψ^{δ−1}` (exact over `ℚ[t]`), `βᵢ = −lc(Rᵢ)·ψ'^δ`, and `Rᵢ₊₂ = prem(Rᵢ, Rᵢ₊₁)/βᵢ`
(exact). The chain's degree-`j` element is the `j`-th subresultant up to sign. The list is the nonzero
prefix; fuel-bounded. -/
def subresPRS (fuel : ℕ) (P Q : BPoly) : List BPoly :=
  -- `go Ri_1 Ri psi delta_prev fuelOuter`: `delta_prev = δ` of the step that produced `Ri` from `Ri_1`.
  let rec go : ℕ → BPoly → BPoly → CPoly → ℕ → List BPoly
    | 0, _, _, _, _ => []
    | fo + 1, Ri_1, Ri, psi, deltaPrev =>
      if bisZero Ri then []
      else
        let lcRi_1 : CPoly := blc Ri_1
        -- update ψ: ψ' = (−lc Ri_1)^δ / ψ^{δ−1}  (δ = deltaPrev ≥ 1)
        let negLc : CPoly := cneg lcRi_1
        let psi' : CPoly :=
          if deltaPrev = 0 then psi
          else cdiv fuel (cpowP negLc deltaPrev) (cpowP psi (deltaPrev - 1))
        -- β = −lc(Ri_1) · ψ'^δ
        let beta : CPoly := cmul negLc (cpowP psi' deltaPrev)
        let pr : BPoly := bpsremainder fuel Ri_1 Ri
        let Ri1 : BPoly := bdivC fuel pr beta
        let deltaNew : ℕ := bdeg Ri - bdeg Ri1
        Ri :: go fo Ri Ri1 psi' deltaNew
  P :: go fuel P Q [-1] (bdeg P - bdeg Q)

/-- **The LRT subresultant at `x`-degree `j`** `bsubresultantGcd fuel j P Q`: the element of `subresPRS`
whose `x`-degree is `j` (the subresultant `Sⱼ` up to sign), or `[]` if none. For LRT, `j` is the
`x`-degree of the per-residue gcd `Gₐ`; here `j = 3`. -/
def bsubresultantGcd (fuel : ℕ) (j : ℕ) (P Q : BPoly) : BPoly :=
  ((subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R))).getLast?.getD []

/-! ### Lifting `ℚ[x]` (a `CPoly`) into `BPoly`, and building `A − t·D'` -/

/-- **Lift a `CPoly` (`= ℚ[x]`) into `BPoly`** `liftCtoBPoly p`: each `x`-coefficient `aᵢ ∈ ℚ` becomes
the constant `ℚ[t]` polynomial `[aᵢ]` (`cC aᵢ`). So `A, D ∈ ℚ[x]` lift to `BPoly`s with **constant** `t`
coefficients. -/
def liftCtoBPoly (p : CPoly) : BPoly := p.map cC

/-- **The variable `t` as a `CPoly`** `ctVar = [0, 1]` (`= t ∈ ℚ[t]`). -/
def ctVar : CPoly := [0, 1]

/-- **The LRT log argument's second operand** `bArgAmtD' A D = A − t·D'` as a `BPoly`: `A` lifted with
constant `t`-coefficients, minus `t · D'` (`t = ctVar`, `D' = cderiv` applied per `x`-coefficient gives
`liftCtoBPoly (cderiv D)`, scaled by the `ℚ[t]` scalar `t`). The `t`-linear `x`-coefficients live in
`ℚ[t]`. -/
def bArgAmtD' (A D : CPoly) : BPoly :=
  bsub (liftCtoBPoly A) (bscaleC ctVar (liftCtoBPoly (cderiv D)))

/-- **The raw degree-`j` LRT subresultant** `lrtSubresultantCompute fuel j A D = Sⱼ(D, A − t·D') ∈ ℚ[t][x]`:
the bivariate subresultant of `D` (lifted) and `A − t·D'` at `x`-degree `j` (the `x`-degree of the per-
residue gcd `Gₐ`), `ℚ[t]`-primitive in `x`. Over `ℚ(t)` it carries a `ℚ[t]` cofactor; reducing it mod the
resultant factor `R` (`lrtGcdCompute`) gives the book's clean log argument. -/
def lrtSubresultantCompute (fuel : ℕ) (j : ℕ) (A D : CPoly) : BPoly :=
  bprimitivePartX fuel (bsubresultantGcd fuel j (liftCtoBPoly D) (bArgAmtD' A D))

/-- **The computable LRT log argument** `lrtGcdCompute fuel j R A D = S(t,x)`: the degree-`j` LRT
subresultant `Sⱼ(D, A − t·D')` reduced modulo the resultant factor `R(t)` and made **monic in `x`** over
`ℚ[t]/(R)` (Exercise 2.7's normalization). This is the polynomial `S(t,x)` that goes inside the logarithms
of `∫ A/D = ∑_{R(a)=0} a·log(S(a,x))` — the per-residue gcd `Gₐ` expressed once over the residue ring. -/
def lrtGcdCompute (fuel : ℕ) (j : ℕ) (R A D : CPoly) : BPoly :=
  bmonicXmodR fuel R (lrtSubresultantCompute fuel j A D)

/-! ### Example 2.4.1 (§2.4/§2.6, p.48/54): `A = x⁴−3x²+6`, `D = x⁶−5x⁴+5x²+4`,
LRT log argument `S(t,x) = x³ + 2t·x² − 3x − 4t` (Czichowski/Gröbner `B = {4t²+1, x³+2tx²−3x−4t}`). -/

/-- **The Rothstein–Trager resultant factor `R(t) = 4t²+1`** of Example 2.4.1 as a `CPoly`
(`[1, 0, 4]` = `1 + 4t²`); the residues are its roots, and `ℚ[t]/(R)` is the residue ring the LRT log
argument is normalized over. (Up to the leading scalar this is the squarefree part `csqfreePart` of the
full resultant `45796·(4t²+1)³`.) -/
def cR241 : CPoly := [1, 0, 4]

-- **Example 2.4.1, the lifted `A − t·D'`** (sanity print): `A − t·(6x⁵−20x³+10x)`.
#eval bArgAmtD' cA241 cD241

-- **Example 2.4.1, the subresultant PRS `x`-degrees** `[6,5,4,3,2,1,0]` (the degree-0 tail is the
-- resultant `45796·(4t²+1)³`, matching `rtResultant_ex241`).
#eval (subresPRS 30 (liftCtoBPoly cD241) (bArgAmtD' cA241 cD241)).map bdeg

-- **Example 2.4.1, the degree-3 subresultant** `S₃`, `ℚ[t]`-primitive in `x`: the LRT log argument up
-- to a `ℚ[t]` cofactor. Its raw (pre-primitive) form `[[-16,0,792],[0,32,0,-2440],[7,0,-400],
-- [0,-14,0,800]]` satisfies `S₃ ≡ −214t·(x³+2tx²−3x−4t) mod 4t²+1`; `bprimitivePartX` strips a constant.
#eval lrtSubresultantCompute 30 3 cA241 cD241

-- **Example 2.4.1, the normalized LRT log argument** `S(t,x)` = `S₃` mod `4t²+1`, monic in `x`:
-- the book's `x³ + 2t·x² − 3x − 4t = [[0,-4], [-3], [0,2], [1]]`.
#eval lrtGcdCompute 30 3 cR241 cA241 cD241

/-- **Example 2.4.1, the proved LRT log-argument computation** (§2.4/§2.6, p.48/54): the degree-3
bivariate subresultant `S₃(D, A − t·D')` of `D = x⁶−5x⁴+5x²+4` and `A − t·D'` (`A = x⁴−3x²+6`), reduced
modulo the resultant factor `R(t) = 4t²+1` and made monic in `x` over `ℚ[t]/(R)`, evaluates (by
`native_decide`) to `[[0, -4], [-3], [0, 2], [1]]` = `x³ + 2t·x² − 3x − 4t`. This is **exactly** the
book's LRT log argument — the Czichowski/Gröbner basis element `x³+2tx²−3x−4t` of Example 2.6.1
(`B = {4t²+1, x³+2tx²−3x−4t}`), with `4t²+1` the RT resultant `R(t)` of `rtResultant_ex241_sqfree`. The
raw subresultant `S₃` carries the `ℚ[t]` cofactor `−214t` (`S₃ ≡ −214t·(x³+2tx²−3x−4t) mod R`), stripped
by the Exercise 2.7 monic-in-`x` normalization (`bmonicXmodR`). This demonstrates the computable
bivariate LRT log-argument engine actually runs and returns the book's `S(t,x)`. -/
theorem lrtGcd_ex241 :
    lrtGcdCompute 30 3 cR241 cA241 cD241 = [[0, -4], [-3], [0, 2], [1]] := by
  native_decide

/-! ### Bridge back to `ℚ[t][x]` and agreement — PROVEN in `SubresultantCorrectness`
`bsubresultantGcd`/`lrtGcdCompute` agrees (up to a `ℚ[t]` unit, i.e. `IsSimilar`) with the noncomputable
`lrtSubresultant A D` (in `LazardRiobooTragerCorrectness`), the LRT subresultant primitive whose
`t ↦ a` specializations are the per-residue Rothstein–Trager gcds `Gₐ = gcd(D, A − a·D')`. All the
pieces are in place: `lrtGcdCompute_isSimilar_lrtSubresultant` (the residue-ring closure through the
coprime-witness bridge `isSimilar_mapRingHom_of_irreducible`), with the chain matched to the subresultant
PRS via `isSimilar_subresPRS_telescope`/`subresultant_prs_telescope`, the bivariate bridge
`toBPoly : BPoly → ℚ[t][x]` (`toBPoly_bdivC_exact` for the Collins β-divisor exact division), and the
`goState` mirror of the `let rec subresPRS.go`. Concretely `isSimilar_lrtSubresultant_lrtSubresultantCompute_ex241`
is hypothesis-free over `ℚ[t]`, and `lrtGcdCompute_ex241_isSimilar_lrtSubresultant_closed` closes
Example 2.4.1 (`lrtGcd_ex241`) over the residue ring `ℚ[t]/(4t²+1)` with no hypotheses. -/

end Compute

end DeepWiki.SymbolicIntegration
