import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralTorsionLight
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # A light `𝔽_p` point-list Picard group law and individual-class order

A `native_decide`-tractable Picard group law over `𝔽_p` on `y² = ρ(x)`, representing a degree-0 class by
a reduced effective divisor `RedDiv p = List (ZMod p × ZMod p)` (a point list, multiplicity = repetition).
The group law `pdivAdd = pdivReduce ∘ pdivCompose` composes by `++` and reduces via a round-trip through the
Mumford engine (`ptToMum` / `mumToPts`); `picMul` / `picOrder` read an individual class's order. All
arithmetic stays in light `𝔽_p[x]`, cross-validated against the Mumford/Cantor order and the point count. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! ## The reduced-divisor representation `RedDiv p` (a sorted `𝔽_p`-point list) -/

/-- A reduced point divisor over `𝔽_p` `RedDiv p = List (ZMod p × ZMod p)`: an effective affine divisor
`D = Σ Pᵢ` as a list of `𝔽_p`-points (multiplicity = repetition), the positive part of a degree-0 class
`D − (deg D)·∞`. The light analogue of the hyperelliptic Mumford pair — only `ZMod p` pairs, no `𝔽_p[x]`
state. -/
abbrev RedDiv (p : ℕ) : Type := List (ZMod p × ZMod p)

/-- Degree of a point divisor `pdivDeg D = D.length` — affine points counted with multiplicity. The
reduction target is `pdivDeg D ≤ g`. -/
def pdivDeg {p : ℕ} (D : RedDiv p) : ℕ := D.length

/-- `ZMod p × ZMod p` point key `ptKey p P = P.1.val * p + P.2.val : ℕ` — a collision-free `ℕ` code for
an `𝔽_p`-point (both coordinates `< p`), used to sort/compare point divisors canonically. -/
def ptKey (p : ℕ) (P : ZMod p × ZMod p) : ℕ := P.1.val * p + P.2.val

/-- Canonical form of a point divisor `pdivCanon p D` — sort `D` by `ptKey` so two divisors with the
same points-with-multiplicity become the *same* list (the analogue of `cnormG` / `mumfordNormEq`). Sorting
(not set-dedup) preserves multiplicity. -/
def pdivCanon (p : ℕ) (D : RedDiv p) : RedDiv p :=
  D.mergeSort (fun P Q => ptKey p P ≤ ptKey p Q)

/-- Canonical equality of point divisors `pdivEq p D₁ D₂` — `true` iff `pdivCanon`-equal, i.e. the same
multiset of `𝔽_p`-points. The identity-test primitive for `picOrder` (analogue of `mumfordNormEq`). -/
def pdivEq (p : ℕ) (D₁ D₂ : RedDiv p) : Bool := pdivCanon p D₁ == pdivCanon p D₂

/-! ## Light point-extraction: roots of `u(x)` over `𝔽_p` (`rootsWithMult`) -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- Roots with multiplicity `rootsWithMult scan poly` — for each `r` in the scan list (e.g. all of
`𝔽_p` via `zmodGrid`), the multiplicity of `r` as a root of `poly`, found by repeatedly dividing out
`(x − r)` (each exact division by `cdivWf`); emit `r` repeated that many times. The
independent `𝔽_p` point-extraction reading the support out of a reduced `u(x)`. Generic over `[CField α]`. -/
def rootsWithMult (scan : List α) (poly : CPolyG α) : List α :=
  scan.foldr (fun r acc =>
    let rec mult : ℕ → CPolyG α → ℕ
      | 0, _ => 0
      | k + 1, q =>
        if cisZeroG q then 0
        else if CField.isZero (cevalG q r) then 1 + mult k (cdivWf q [CField.neg r, CField.one])
        else 0
    (List.replicate (mult (poly.length + 1) poly) r) ++ acc) []

end CPolyG

/-! ## The point-list ↔ Mumford round-trip (the reduction engine) -/

/-- Point list → reduced Mumford pair `ptToMum ρ g pts`: fold `cantorCompose`/`cantorReduce` over the
single points `mumfordPoint Pᵢ` from `mumfordIdentity`, giving the reduced representative of `Σ (Pᵢ − ∞)`. -/
def ptToMum {α : Type*} [CField α] (ρ : CPolyG α) (g : ℕ) (pts : List (α × α)) :
    MumfordDivisor α :=
  pts.foldl (fun acc P => cantorReduce ρ g (cantorCompose ρ acc (mumfordPoint P.1 P.2)))
    mumfordIdentity

/-- Reduced Mumford pair → point list `mumToPts scan D`: the roots of `D.u` with multiplicity
(`rootsWithMult` over `scan`) each paired with `y = D.v(root)`. -/
def mumToPts {α : Type*} [CField α] (scan : List α) (D : MumfordDivisor α) : List (α × α) :=
  (CPolyG.rootsWithMult scan D.u).map (fun r => (r, cevalG D.v r))

/-! ## The group law: compose (`++`) then reduce (round-trip to Cantor), and `picOrder` -/

/-- Compose two point divisors `pdivCompose D₁ D₂ = D₁ ++ D₂` — add the effective divisors as formal
point sums (analogue of `cantorCompose`). Degree adds; reduction follows. -/
def pdivCompose {p : ℕ} (D₁ D₂ : RedDiv p) : RedDiv p := D₁ ++ D₂

/-- Reduce a point divisor `pdivReduce p ρ g D` — bring an effective divisor on `y² = ρ` to its reduced
representative (`deg ≤ g`) by the round-trip `mumToPts (zmodGrid p) (ptToMum D)` (lift to the reduced
Mumford pair via Cantor compose/reduce, read the support back), then canonicalise. The point-list analogue
of `cantorReduce`; light `𝔽_p[x]` arithmetic on short lists — no HNF. Root extraction uses its own
structural length bound. -/
def pdivReduce (p : ℕ) [CField (ZMod p)] (ρ : CPolyG (ZMod p)) (g : ℕ) (D : RedDiv p) : RedDiv p :=
  pdivCanon p (mumToPts (zmodGrid p) (ptToMum ρ g D))

/-- The Picard group law `pdivAdd p ρ g D₁ D₂ = pdivReduce ρ g (D₁ ++ D₂)` — the sum of two reduced
point divisors as the reduced representative of `[D₁] + [D₂]` in `Pic⁰(C)(𝔽_p)` (compose by `++`, reduce by
the Cantor round-trip). Identity `[]` (the class of `0·∞`); the analogue of `cantorAdd`. -/
def pdivAdd (p : ℕ) [CField (ZMod p)] (ρ : CPolyG (ZMod p)) (g : ℕ) (D₁ D₂ : RedDiv p) : RedDiv p :=
  pdivReduce p ρ g (pdivCompose D₁ D₂)

/-- The scalar multiple `picMul p ρ g n D = n·D` (the `n`-fold Picard sum), `0·D = []` (the identity).
By `ℕ`-recursion `(n+1)·D = D + n·D`. The order of `D` is the least `n ≥ 1` with `picMul … n D ≈ []` — the
analogue of `cantorMul`. -/
def picMul (p : ℕ) [CField (ZMod p)] (ρ : CPolyG (ZMod p)) (g : ℕ) : ℕ → RedDiv p → RedDiv p
  | 0, _ => []
  | n + 1, D => pdivAdd p ρ g D (picMul p ρ g n D)

/-- Order-search loop `picOrderAux fuel p ρ g D acc n`: with `acc = n·D`, test `(n+1)·D = D + acc`
against the identity `[]` (`pdivEq`); on a hit return `some (n+1)`, else recurse. `fuel` bounds the
multiples tried (the finite group order is the ceiling). The analogue of `cantorOrderAux`. -/
def picOrderAux : ℕ → (p : ℕ) → [CField (ZMod p)] → CPolyG (ZMod p) → ℕ → RedDiv p → RedDiv p → ℕ →
    Option ℕ
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, p, _, ρ, g, D, acc, n =>
    let acc := pdivAdd p ρ g D acc
    if pdivEq p acc [] then some (n + 1)
    else picOrderAux fuel p ρ g D acc (n + 1)

/-- The individual-class order `picOrder fuel p ρ g D = some m` — the least `m ≥ 1` with `m·D ≈ []` (the
identity class) in `Pic⁰(C)(𝔽_p)` for `y² = ρ`, searching `1·D, 2·D, …` up to `fuel` multiples (`pdivEq`).
`none` if no `m ≤ fuel` works. The general analogue of `cantorOrder` — reading the order of a *specific*
class on the point-list representation, beyond the genus-1 point-count ceiling. -/
def picOrder (fuel p : ℕ) [CField (ZMod p)] (ρ : CPolyG (ZMod p)) (g : ℕ) (D : RedDiv p) : Option ℕ :=
  picOrderAux fuel p ρ g D [] 0

end DeepWiki.SymbolicIntegration

/-! ## The genus-2 curve `y² = x⁵ + 1` over `𝔽₁₁` (`native_decide`)

On the genus-2 curve `y² = x⁵ + 1` over `𝔽₁₁`, `picOrder` reads the order of `(0,1) − ∞` (= 5) and it
matches the Mumford/Cantor order for the same class. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The genus-2 radicand `ρ = x⁵ + 1 ∈ 𝔽₁₁[x]` (`polyToZMod` of Cantor's `hypRhoX5p1`), the curve
`y² = x⁵ + 1` over `𝔽₁₁`. Genus 2 — `|Pic⁰| ≠ N_p`. -/
def picRhoX5p1Mod11 : CPolyG (ZMod 11) := polyToZMod 11 hypRhoX5p1

/-- The class `(0,1) − ∞` on `y² = x⁵ + 1` over `𝔽₁₁`, as the singleton point divisor `[(0, 1)]`. -/
def picPt01_X5p1 : RedDiv 11 := [((0 : ZMod 11), (1 : ZMod 11))]

/-- `(0,1) + (0,−1)` reduces to the identity `[]` over `𝔽₁₁`: a point plus its opposite is principal
(the inverse law on the point-list representation). -/
theorem pdivAdd_pt01_opp_X5p1 :
    pdivEq 11 (pdivAdd 11 picRhoX5p1Mod11 2 picPt01_X5p1 [((0 : ZMod 11), (-1 : ZMod 11))]) [] = true := by
  native_decide

/-- The double `2·((0,1) − ∞)` is a genuine degree-2 reduced divisor:
`(picMul 11 picRhoX5p1Mod11 2 2 picPt01_X5p1).length = 2`. -/
theorem picMul_two_pt01_X5p1_deg :
    (picMul 11 picRhoX5p1Mod11 2 2 picPt01_X5p1).length = 2 := by native_decide

/-- The order of `(0,1) − ∞` on `y² = x⁵+1` over `𝔽₁₁` is 5:
`picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1 = some 5`. -/
theorem picOrder_pt01_X5p1_eq :
    picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1 = some 5 := by native_decide

/-- The point-list order of `(0,1) − ∞` over `𝔽₁₁` matches the Mumford/Cantor `cantorOrder` for the same
class. -/
theorem picOrder_X5p1_matches_cantor :
    picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1
      = cantorOrder 200 (polyToZMod 11 hypRhoX5p1) 2 (mumfordReduceModP 11 hypG2Pt01) := by
  native_decide

end DeepWiki.SymbolicIntegration

/-! ## Genus-1 cross-check against the point count `N_p` (`native_decide`)

On `y² = x³ + 1` over `𝔽₁₁` (torsion `ℤ/6`), the point-list order of `(2,3) − ∞` (= 6) divides
`N₁₁ = 12` and matches the Cantor order. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The genus-1 radicand `ρ = x³ + 1 ∈ 𝔽₁₁[x]` (`polyToZMod` of Cantor's `hypRhoX3p1`), the curve
`y² = x³ + 1` over `𝔽₁₁`. Torsion `ℤ/6`. -/
def picRhoX3p1Mod11 : CPolyG (ZMod 11) := polyToZMod 11 hypRhoX3p1

/-- The class `(2, 3) − ∞` on `y² = x³ + 1` over `𝔽₁₁`, as `[(2, 3)]`. -/
def picPt23_X3p1 : RedDiv 11 := [((2 : ZMod 11), (3 : ZMod 11))]

/-- The point-list order of `(2,3) − ∞` over `𝔽₁₁` is 6 and divides the point count `N₁₁ = 12`:
`picOrder … = some 6 ∧ npHypOddDeg 11 (hypCurveX3p1 11) % 6 = 0`. -/
theorem picOrder_pt23_X3p1_divides_Np :
    picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1 = some 6
      ∧ npHypOddDeg 11 (hypCurveX3p1 11) % 6 = 0 := by native_decide

/-- The point-list order of `(2,3) − ∞` over `𝔽₁₁` matches the Mumford/Cantor order (both 6). -/
theorem picOrder_X3p1_matches_cantor :
    picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1
      = cantorOrder 60 (polyToZMod 11 hypRhoX3p1) 1 (mumfordReduceModP 11 hypPt23) := by
  native_decide

end DeepWiki.SymbolicIntegration

/-! ## Point-list Picard group law validation (`native_decide`) -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The point-list Picard group law and `picOrder` validate: on genus-2 `y² = x⁵ + 1` over `𝔽₁₁`,
`picOrder` reads the order of `(0,1) − ∞` as 5 matching Cantor, with `2·((0,1)−∞)` a degree-2 divisor and
`(0,1) + (0,−1)` collapsing to `[]`; on genus-1 `y² = x³ + 1`, the order of `(2,3) − ∞` is 6, divides
`N₁₁ = 12`, and matches Cantor. -/
theorem light_picard_group_law_validates :
    -- genus 2 (y² = x⁵+1 / 𝔽₁₁): light group law reads order 5, matches Cantor
    (picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1 = some 5
      ∧ picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1
          = cantorOrder 200 (polyToZMod 11 hypRhoX5p1) 2 (mumfordReduceModP 11 hypG2Pt01)
      ∧ (picMul 11 picRhoX5p1Mod11 2 2 picPt01_X5p1).length = 2
      ∧ pdivEq 11 (pdivAdd 11 picRhoX5p1Mod11 2 picPt01_X5p1
          [((0 : ZMod 11), (-1 : ZMod 11))]) [] = true)
    -- genus 1 (y² = x³+1 / 𝔽₁₁): light order 6 divides N_p and matches Cantor
    ∧ (picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1 = some 6
        ∧ npHypOddDeg 11 (hypCurveX3p1 11) % 6 = 0)
    ∧ picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1
        = cantorOrder 60 (polyToZMod 11 hypRhoX3p1) 1 (mumfordReduceModP 11 hypPt23) := by
  native_decide

/-! ## Representation boundary

The point-list layer supplies the class representation and the individual-order reader; the reduction
engine is reused from the hyperelliptic Cantor `cantorCompose`/`cantorReduce` via the `ptToMum`/`mumToPts`
round-trip. Non-hyperelliptic plane curves use the separate `L(D)` linear-solve representation. -/

end DeepWiki.SymbolicIntegration
