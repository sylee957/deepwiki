import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # Generic fraction-free gcd over an arbitrary tower level
The recursive fraction-free gcd `CFracGcd`/`cgcdFFGen` over `α[t]` for `α = QFunNZG β = Frac(β[s])`:
clear denominators into `(β[s])[t]`, run a primitive PRS over the GCD-domain `β[s]` (content-gcd
recursing one level down, bottoming at ℚ[x]). Coefficients stay bounded where the Euclidean `cgcdExtG`
swells; `native_decide` witnesses pin the contrast at tower levels 1 and 2. -/

namespace DeepWiki.SymbolicIntegration

open Compute

variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPoly B = List (CPolyG B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPoly B := List (CPolyG B)`: a `t`-polynomial with coefficients in
`CPolyG B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPoly (B : Type*) [CField B] := List (CPolyG B)

namespace GBPoly

/-- Normalize a `GBPoly`: `cnormG` each coefficient, then strip trailing `cisZeroG` coefficients (zero
polynomial becomes `[]`). -/
def gbnorm : GBPoly B → GBPoly B
  | [] => []
  | a :: as =>
    let a := CPolyG.cnormG a
    match gbnorm as with
    | [] => if CPolyG.cisZeroG a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `GBPoly`s in `t` (each `t`-coefficient added via `caddG`). -/
def gbadd : GBPoly B → GBPoly B → GBPoly B
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CPolyG.caddG a b :: gbadd as bs

/-- Negation of a `GBPoly`, each `t`-coefficient negated via `cnegG`. -/
def gbneg (p : GBPoly B) : GBPoly B := p.map CPolyG.cnegG

/-- Subtraction of `GBPoly`s, `p − q := p + (−q)`. -/
def gbsub (p q : GBPoly B) : GBPoly B := gbadd p (gbneg q)

/-- Scale `gbscaleC c p`: multiply every `t`-coefficient by the `B[s]` scalar `c` via `cmulG`. -/
def gbscaleC (c : CPolyG B) (p : GBPoly B) : GBPoly B := p.map (CPolyG.cmulG c)

/-- Shift in `t` `gbshift k p = tᵏ · p`: prepend `k` zero (`= []`) `t`-coefficients. -/
def gbshift : ℕ → GBPoly B → GBPoly B
  | 0, p => p
  | n + 1, p => [] :: gbshift n p

/-- Zero test for a `GBPoly`: `true` iff it normalizes to `[]`. -/
def gbisZero (p : GBPoly B) : Bool := (gbnorm p).isEmpty

/-- `t`-degree of a `GBPoly`: `(gbnorm p).length − 1`, with `gbdeg 0 = 0`. -/
def gbdeg (p : GBPoly B) : ℕ := (gbnorm p).length - 1

/-- Leading `t`-coefficient `gblc p ∈ CPolyG B`: the top nonzero `t`-coefficient, `[]` for zero. -/
def gblc (p : GBPoly B) : CPolyG B := (gbnorm p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `CPolyG B = B[s]` -/

/-- Pseudo-remainder `gbpsremainder fuel p q = prem(p, q)` over `CPolyG B = B[s]`: while `deg p ≥ deg q`,
replace `p` by `lc(q)·p − lc(p)·tᵏ·q` (no `B[s]` division). -/
def gbpsremainder : ℕ → GBPoly B → GBPoly B → GBPoly B
  | 0, p, _ => gbnorm p
  | fuel + 1, p, q =>
    let p := gbnorm p
    let q := gbnorm q
    if gbisZero q then gbnorm p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := gblc q
      let lcp := gblc p
      -- `lc(q)·p − lc(p)·tᵏ·q`: kills the leading term, stays in `B[s][t]`.
      let p' := gbnorm (gbsub (gbscaleC lcq p) (gbscaleC lcp (gbshift k q)))
      gbpsremainder fuel p' q

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in) -/

/-- `B[s]`-content of a `GBPoly` relative to a content-gcd `cgcdB`: fold `cgcdB` over the
`t`-coefficients. -/
def gbcontent (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPoly B) : CPolyG B :=
  (gbnorm p).foldl (fun g c => cgcdB g c) []

/-- Primitive part `gbprimitivePart cgcdB p = p / content_t(p)`: divide every `t`-coefficient by the
content via `cdivWf`. Leaves `[]` unchanged. -/
def gbprimitivePart (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPoly B) : GBPoly B :=
  let p := gbnorm p
  let g := gbcontent cgcdB p
  if CPolyG.cisZeroG g then p else gbnorm (p.map (fun c => CPolyG.cdivWf c g))

end GBPoly

/-! ### The generic fraction-free gcd kernel — the primitive PRS over `CPolyG B = B[s]` -/

/-! ### Clear denominators `CPolyG (QFunNZG β) ↔ GBPoly β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace CPolyG

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qnumCoeffG (c : QFunNZG β) : CPolyG β := c.1.1

/-- The denominator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qdenCoeffG (c : QFunNZG β) : CPolyG β := c.1.2

/-- Clear denominators `cclearDenomsG p ∈ GBPoly β`: multiply `p` over `α = QFunNZG β` by the product of
its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPolyG β`. -/
def cclearDenomsG (p : CPolyG (QFunNZG β)) : GBPoly β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPolyG β) := cs.map qdenCoeffG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPolyG.cmulG acc d) [CField.one]
    CPolyG.cmulG (qnumCoeffG ci) prodOthers)

/-- Lift back `liftGBPolyG p ∈ CPolyG (QFunNZG β)`: read each `CPolyG β` coefficient `c` as the fraction
`c/1`. Inverse of clearing denominators. -/
def liftGBPolyG (p : GBPoly β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG

/-! ### `class CFracGcd α` — the recursive fraction-free gcd over `α[t]` -/

/-! ### Level-1 benchmark inputs over `QFunNZG ℚ ≅ ℚ(x)` -/

namespace BenchG

open CPolyG QFunNZG

/-- Build a `QFunNZG ℚ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`), denominator
nonzero by `decide`. Falls back to `0/1` if the denominator degenerates. -/
def gqc (num den : CPolyG ℚ) (h : CPolyG.cisZeroG den = false := by decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-- The ℚ(x) coefficient `x` as a `QFunNZG ℚ`. -/
def gcX : QFunNZG ℚ := gqc [0, 1] [1]
/-- The ℚ(x) coefficient `1/x` (a genuine denominator). -/
def gcInvX : QFunNZG ℚ := gqc [1] [0, 1]
/-- The ℚ(x) coefficient `x + 1`. -/
def gcXp1 : QFunNZG ℚ := gqc [1, 1] [1]
/-- The ℚ(x) coefficient `1/(x + 1)`. -/
def gcInvXp1 : QFunNZG ℚ := gqc [1] [1, 1]
/-- The ℚ(x) coefficient `x − 1`. -/
def gcXm1 : QFunNZG ℚ := gqc [-1, 1] [1]

/-- `(1 : QFunNZG ℚ)` shorthand for building monic cofactors. -/
def gOne : QFunNZG ℚ := qoneNZG
/-- Negate a `QFunNZG ℚ` coefficient (denominator unchanged). -/
def gNeg (z : QFunNZG ℚ) : QFunNZG ℚ := qnegNZG z

/-- A linear `t`-polynomial `a0 + a1·t` as a `CPolyG (QFunNZG ℚ)` (low→high in `t`). -/
def glin (a0 a1 : QFunNZG ℚ) : CPolyG (QFunNZG ℚ) := [a0, a1]

/-- The fixed gcd target `(t + x)·(t − 1/x)` over `QFunNZG ℚ` — degree 2 in `t`, ℚ(x) coefficients with
genuine denominators. -/
def gCommonFactor : CPolyG (QFunNZG ℚ) :=
  cmulG (glin gcX gOne) (glin (gNeg gcInvX) gOne)

/-- The cofactor-coefficient cycle for `p` (period 5: `x`, `1/x`, `x+1`, `1/(x+1)`, `x−1`). -/
def gcycCoefA : ℕ → QFunNZG ℚ
  | 0 => gcX | 1 => gcInvX | 2 => gcXp1 | 3 => gcInvXp1 | 4 => gcXm1 | n + 5 => gcycCoefA n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `gcycCoefA`). -/
def gcycCoefB : ℕ → QFunNZG ℚ
  | 0 => gcInvXp1 | 1 => gcXm1 | 2 => gcX | 3 => gcInvX | 4 => gcXp1 | n + 5 => gcycCoefB n

/-- The `p`-cofactor `∏_{i<k} (t + gcycCoefA i)`, a `t`-polynomial of degree `k`. -/
def glinProdA : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gcycCoefA n) gOne) (glinProdA n)

/-- The `q`-cofactor `∏_{i<k} (t − gcycCoefB i)`, a `t`-polynomial of degree `k` coprime to
`glinProdA k`. -/
def glinProdB : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gNeg (gcycCoefB n)) gOne) (glinProdB n)

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZG ℚ`, total `t`-degree `k + 2`. -/
def gBenchP (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdA k)

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZG ℚ`, total `t`-degree `k + 2`;
`gcd(gBenchP k, gBenchQ k) = gCommonFactor` (degree 2). -/
def gBenchQ (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdB k)

/-! #### The swell measure over `QFunNZG ℚ` (mirror of `Bench.gcdSizeRaw`) -/

/-- The raw stored size of one `QFunNZG ℚ` coefficient: total numerator/denominator list lengths plus the
sum of `|num| + den` of each ℚ entry. -/
def gCoeffSizeRaw (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)`: `gCoeffSizeRaw` summed over coefficients plus
the `t`-length. -/
def gGcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ :=
  (g : List (QFunNZG ℚ)).foldl (fun a z => a + gCoeffSizeRaw z) g.length

end BenchG

/-! #### The pinned witnesses (`native_decide`) -/

open BenchG in
open BenchG in
/-! ### Level-2 fraction-free gcd inputs over `Lvl2 = ℚ(x)(t₁)` -/

open BenchG in
/-- The `Lvl2 = ℚ(x)(t₁)` scalar unit `(1 : Lvl2)`, for assembling `t₂`-polynomials over the tower. -/
def lvl2One : Lvl2 := CField.one

/-- The `Lvl2` scalar `t₁ = s/1` (numerator `[0, 1] ∈ (QFunNZG ℚ)[s]`, denominator `[1]`). -/
def lvl2T1scalar : Lvl2 :=
  ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The `t₂`-polynomial `(t₂ − t₁)·(t₂ + 1)` over `Lvl2 = ℚ(x)(t₁)` (low→high in `t₂`). -/
def lvl2P : CPolyG Lvl2 :=
  CPolyG.cmulG [CField.neg lvl2T1scalar, lvl2One] [lvl2One, lvl2One]

/-- The `t₂`-polynomial `(t₂ − t₁)·(t₂ − 1)` over `Lvl2`, sharing `(t₂ − t₁)` with `lvl2P`. -/
def lvl2Q : CPolyG Lvl2 :=
  CPolyG.cmulG [CField.neg lvl2T1scalar, lvl2One] [CField.neg lvl2One, lvl2One]

/-! #### A level-2 swell witness over `ℚ(x)(t₁)[t₂]` with genuine `t₁` denominators -/

namespace BenchLvl2

open CPolyG

/-- The `Lvl2 = ℚ(x)(t₁)` scalar `t₁ = s/1` (numerator the monomial `[0,1] ∈ (QFunNZG ℚ)[s]`). -/
def t1 : Lvl2 :=
  ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The `Lvl2` scalar `1/t₁ = 1/s` (numerator `[1]`, denominator `[0,1] = s`), a genuine `t₁`
denominator. -/
def invT1 : Lvl2 :=
  ⟨([CField.one], [(CField.zero : QFunNZG ℚ), CField.one]), by native_decide⟩

/-- The `Lvl2` scalar `t₁ + 1`. -/
def t1p1 : Lvl2 := CField.add t1 CField.one
/-- The `Lvl2` scalar `1/(t₁ + 1)` (a genuine denominator). -/
def invT1p1 : Lvl2 :=
  ⟨([CField.one], [CField.one, CField.one]), by native_decide⟩
/-- The `Lvl2` scalar `t₁ − 1`. -/
def t1m1 : Lvl2 := CField.sub t1 CField.one

/-- A linear `t₂`-polynomial `a0 + a1·t₂` over `Lvl2` (low→high in `t₂`). -/
def lin2 (a0 a1 : Lvl2) : CPolyG Lvl2 := [a0, a1]

/-- The fixed level-2 gcd target `(t₂ + t₁)·(t₂ − 1/t₁)`, degree 2 in `t₂` with a genuine `1/t₁`
denominator. -/
def commonFactor2 : CPolyG Lvl2 :=
  cmulG (lin2 t1 CField.one) (lin2 (CField.neg invT1) CField.one)

/-- The cofactor-coefficient cycle for `p` (period 5 through `t₁`, `1/t₁`, `t₁+1`, `1/(t₁+1)`, `t₁−1`). -/
def cyc2A : ℕ → Lvl2
  | 0 => t1 | 1 => invT1 | 2 => t1p1 | 3 => invT1p1 | 4 => t1m1 | n + 5 => cyc2A n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `cyc2A`). -/
def cyc2B : ℕ → Lvl2
  | 0 => invT1p1 | 1 => t1m1 | 2 => t1 | 3 => invT1 | 4 => t1p1 | n + 5 => cyc2B n

/-- The `p`-cofactor `∏_{i<k} (t₂ + cyc2A i)`, a `t₂`-polynomial of degree `k`. -/
def prod2A : ℕ → CPolyG Lvl2
  | 0 => [CField.one]
  | n + 1 => cmulG (lin2 (cyc2A n) CField.one) (prod2A n)

/-- The `q`-cofactor `∏_{i<k} (t₂ − cyc2B i)`, degree `k`, coprime to `prod2A k`. -/
def prod2B : ℕ → CPolyG Lvl2
  | 0 => [CField.one]
  | n + 1 => cmulG (lin2 (CField.neg (cyc2B n)) CField.one) (prod2B n)

/-- The level-2 benchmark dividend `p = commonFactor2 · prod2A k`, total `t₂`-degree `k + 2`. -/
def benchP2 (k : ℕ) : CPolyG Lvl2 := cmulG commonFactor2 (prod2A k)

/-- The level-2 benchmark divisor `q = commonFactor2 · prod2B k`, total `t₂`-degree `k + 2`;
`gcd(benchP2 k, benchQ2 k) ~ commonFactor2` (degree 2). -/
def benchQ2 (k : ℕ) : CPolyG Lvl2 := cmulG commonFactor2 (prod2B k)

/-- The naive Euclidean gcd `cmonicG (cgcdWf …)` of the level-2 benchmark pair (the swelling kernel). -/
def benchExtGcd2 (k : ℕ) : CPolyG Lvl2 := CPolyG.cmonicG (CPolyG.cgcdWf (benchP2 k) (benchQ2 k)).1

/-! ##### The level-2 swell measure — recursed through both fraction levels -/

/-- The raw stored size of one `QFunNZG ℚ` scalar: list lengths + `Σ(|num|+den)` of the ℚ entries. -/
def sizeLvl1 (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of one `Lvl2 = ℚ(x)(t₁)` scalar: list lengths + `sizeLvl1` over the numerator and
denominator `s`-coefficients. -/
def sizeLvl2 (z : Lvl2) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + sizeLvl1 c) 0) +
    (z.1.2.foldl (fun a c => a + sizeLvl1 c) 0)

/-- The raw stored size of a whole `CPolyG Lvl2`: `sizeLvl2` summed over the `t₂`-coefficients plus the
`t₂`-length. -/
def gcdSize2 (g : CPolyG Lvl2) : ℕ :=
  (g : List Lvl2).foldl (fun a z => a + sizeLvl2 z) g.length

end BenchLvl2

open BenchLvl2 in
open BenchLvl2 in
open BenchLvl2 in
/-! ### Axioms and the remaining gap
The witnesses are `native_decide`-validated. The generic FF gcd is flat at level 1 but not constant at
level 2 (`82 → 103 → 3659` over degrees 3/4/5): the plain primitive PRS bounds the content swell but not
the coprime coefficient degree; a subresultant PRS would flatten level 2. -/


end DeepWiki.SymbolicIntegration
