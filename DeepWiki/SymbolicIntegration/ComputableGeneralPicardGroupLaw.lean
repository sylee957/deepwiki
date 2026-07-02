import DeepWiki.SymbolicIntegration.ComputableGeneralTorsionLight
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # A LIGHT, `native_decide`-tractable Picard group law over `𝔽_p` for a GENERAL curve — reading an
INDIVIDUAL divisor class's order beyond the genus-1 ceiling (Trager Ch. 6 / computational AG: a concrete
`𝔽_p` POINT-LIST class representation, NOT the fractional-ideal HNF)

`ComputableGeneralTorsionLight` computes the good-reduction torsion **ceiling** `gcd_p |Pic⁰(C)(𝔽_p)|` by
flat `𝔽_p`-point counting — pure `ZMod p` ring arithmetic, no ideal HNF, every `native_decide` under a
second. That pins the order for **genus 1** (where `Pic⁰` is cyclic of order `N_p`, so the rational torsion
is `gcd_p N_p`), but **not** for higher genus, where `|Pic⁰| ≠ N_p` and an *individual* class's order needs
the actual **group law**. The hyperelliptic Cantor engine (`ComputableCantorComposition` /
`ComputableDivisorOrder`) supplies that group law (`cantorAdd` = compose + reduce, `cantorOrder`) — but
through the **Mumford pair** `(u, v)` of `y² = ρ(x)`.

**This file supplies a LIGHT POINT-LIST class representation + an add-and-reduce group law + the
individual-class order `picOrder`, over `𝔽_p`, in light `𝔽_p[x]` arithmetic (no `QFunNZG`, no `𝔽_p[x]`
HNF — the wall `ComputableGeneralTorsionLight` avoids), and reads an individual divisor class's order on a
GENUS-2 curve, cross-validated against Cantor and against the `N_p` point count.** The keystone framing
(the user's): this is COMPUTATIONAL ALGEBRAIC GEOMETRY (Gröbner/resultant/linear-algebra/interpolation
primitives), so we build the concrete small-`𝔽_p` version.

## The light representation (mirrors Cantor's Mumford pair, but as a point list)

A degree-0 class on the affine curve `C : y² = ρ(x)` (base point `∞`) ↔ an **effective divisor**
`D = Σ Pᵢ` of affine `𝔽_p`-points `Pᵢ = (xᵢ, yᵢ)` (the positive part of `D − (deg D)·∞`), encoded as a
list `RedDiv p = List (ZMod p × ZMod p)` (multiplicity = repetition). Pure `ZMod p` pairs — the lightest
representation, the analogue of the Mumford pair `(u, v)`.

## The group law: add + reduce (mirrors Cantor compose + reduce)

* **`pdivCompose D₁ D₂ = D₁ ++ D₂`** — concatenate the effective parts (the analogue of `cantorCompose`).
* **`pdivReduce`** — reduce to the unique reduced representative `deg ≤ g`. Realized via a faithful
  **round-trip** to the Mumford engine: `ptToMum` builds the Mumford pair from the point list (folding
  `cantorCompose` over the single points `mumfordPoint Pᵢ`, which correctly handles **every** multiplicity —
  the tangent-line doubling included — then `cantorReduce`), and `mumToPts` reads the reduced point list
  back as the roots of the reduced `u` (`rootsWithMult`, an independent `𝔽_p` root scan) paired with
  `y = v(root)`. So the **class representation and the order search live on the light point list**; the
  reduction *engine* is Cantor's proven compose/reduce (the standard, and the only thing that gets all
  multiplicities right). The point-list mirror of `cantorAdd = cantorReduce ∘ cantorCompose`, identity `[]`.
* **`pdivAdd = pdivReduce ∘ pdivCompose`** — the Picard group law on point divisors.

## Individual-class order `picOrder` (mirrors `cantorOrder`)

* **`picMul n D = n·D`** (`ℕ`-fold `pdivAdd`), **`picOrder fuel D`** = least `n ≥ 1` with `n·D ≈ []`,
  `ℕ`-fuel-bounded. The general analogue of `cantorMul` / `cantorOrder` — reading a *specific* class's
  order on the point-list representation, beyond the genus-1 point-count ceiling.

**Proof-of-concept** (`native_decide`, all under a second): on `y² = x⁵ + 1` (genus **2**, where
`|Pic⁰| ≠ N_p` and Cantor's Mumford engine is the only prior group law) `picOrder` reads the order of the
class `(0,1) − ∞` (= 5) on the **point-list** representation, and it **equals the Cantor `cantorOrder`** for
the same class — the individual-class order is now `native_decide`-readable on a NON-genus-1 curve. Plus the
genus-1 cross-check against `ComputableGeneralTorsionLight`'s `N_p` (`y² = x³ + 1`, torsion `ℤ/6`).

Everything is **fuel-bounded total recursion** (no `partial def`), so the axiom set stays
`[propext, Classical.choice, Quot.sound]` + the `native_decide` reduction axiom — no `sorryAx`. -/

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

/-! ## Light point-extraction: roots of `u(x)` over `𝔽_p` (`rootsWithMult`)

To read a reduced Mumford pair `(u, v)` back as a point list, scan `𝔽_p` for the roots of `u` (with
multiplicity) and pair each with `y = v(root)`. Pure short-`𝔽_p[x]` arithmetic (`cevalG`, `cdivWf`), the
same light regime Cantor runs in — NOT the `𝔽_p[x]` HNF wall. -/

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

/-! ## The point-list ↔ Mumford round-trip (the reduction engine)

`ptToMum` lifts a point list to its reduced Mumford pair by folding Cantor composition over the single
points `mumfordPoint Pᵢ` (Cantor's compose handles every multiplicity — including the tangent-line
doubling of a repeated point — correctly, which a naive Lagrange interpolation does not); `mumToPts` reads
a reduced pair back to a point list via `rootsWithMult` + `v`. The reduction *engine* is Cantor's proven
compose/reduce; the *representation* and the order search stay on the light point list. -/

/-- Point list → reduced Mumford pair `ptToMum ρ g pts` — fold Cantor composition over the single
points `mumfordPoint Pᵢ`, reducing at each step (`cantorReduce ρ g`), starting from `mumfordIdentity`. The
result is the unique reduced Mumford representative of the class `Σ (Pᵢ − ∞)`. Cantor's composition gets
**every** multiplicity right (the tangent-line doubling of repeated points), which is why the reduction
round-trips through it. Generic over `[CField α]`. -/
def ptToMum {α : Type*} [CField α] (ρ : CPolyG α) (g : ℕ) (pts : List (α × α)) :
    MumfordDivisor α :=
  pts.foldl (fun acc P => cantorReduce ρ g (cantorCompose ρ acc (mumfordPoint P.1 P.2)))
    mumfordIdentity

/-- Reduced Mumford pair → point list `mumToPts scan D` — read the support of a reduced Mumford
divisor `(u, v)` back out as a point list: the roots of `u` with multiplicity (`rootsWithMult` over `scan`,
e.g. `zmodGrid p`), each paired with `y = v(root)` (`cevalG D.v`). The independent `𝔽_p` point-extraction
half of the round-trip. Generic over `[CField α]`. -/
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

/-! ## Proof-of-concept I: the GENUS-2 curve `y² = x⁵ + 1` over `𝔽₁₁` (`native_decide`)

The hyperelliptic curve `y² = x⁵ + 1` has genus **2** — `|Pic⁰(C)(𝔽_p)| ≠ N_p` (the flat point count alone
does NOT pin an individual class's order), and Cantor's Mumford engine is the only prior group law. Here the
**light point-list group law** `picOrder` reads an individual class's order on the point-list representation,
and we **cross-check it equals the Cantor `cantorOrder`** for the same class — the proof the individual
order is `native_decide`-readable on a NON-genus-1 curve.

`p = 11` (`11 ∤ disc(x⁵+1)`, good reduction). The class `(0,1) − ∞` (`1² = 0⁵ + 1`) has order 5 in
`Pic⁰(C)(𝔽₁₁)`; both engines must agree. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The genus-2 radicand `ρ = x⁵ + 1 ∈ 𝔽₁₁[x]` (`polyToZMod` of Cantor's `hypRhoX5p1`), the curve
`y² = x⁵ + 1` over `𝔽₁₁`. Genus 2 — `|Pic⁰| ≠ N_p`. -/
def picRhoX5p1Mod11 : CPolyG (ZMod 11) := polyToZMod 11 hypRhoX5p1

/-- The class `(0,1) − ∞` on `y² = x⁵ + 1` over `𝔽₁₁`, as the singleton point divisor `[(0, 1)]`. The
light-representation analogue of the Mumford point `(x, 1)`. -/
def picPt01_X5p1 : RedDiv 11 := [((0 : ZMod 11), (1 : ZMod 11))]

/-- `(0,1) + (0,−1)` reduces to the identity over `𝔽₁₁` (`native_decide`): `pdivAdd` of `(0,1)` and
its opposite `(0,−1)` cancels to `[]` — a point plus its hyperelliptic opposite is principal (`P + ιP ~
2·∞`), the inverse law on the light point-list representation (analogue of `cantorSumPoppP`). The reduction
collapsing an opposite pair. -/
theorem pdivAdd_pt01_opp_X5p1 :
    pdivEq 11 (pdivAdd 11 picRhoX5p1Mod11 2 picPt01_X5p1 [((0 : ZMod 11), (-1 : ZMod 11))]) [] = true := by
  native_decide

/-- The double `2·((0,1) − ∞)` is a genuine degree-2 reduced divisor (`native_decide`): `picMul 2`
gives a divisor of length 2 (`deg = g = 2`), NOT a single point — on the genus-2 curve the reduced
representative of `2·((0,1) − ∞)` has degree `g = 2` (on a genus-1 curve the double collapses to one
point). The reduction (via the Cantor tangent-doubling round-trip) producing a real degree-2 reduced
divisor. -/
theorem picMul_two_pt01_X5p1_deg :
    (picMul 11 picRhoX5p1Mod11 2 2 picPt01_X5p1).length = 2 := by native_decide

/-- The order of the class `(0,1) − ∞` on `y² = x⁵+1` over `𝔽₁₁`, via the LIGHT point-list group law, is
5 (`native_decide`): `picOrder 30 11 ρ 2 [(0,1)] = some 5` — the individual-class order read by `pdivAdd`
(compose + Cantor-round-trip reduce) + `picOrder`, on a GENUS-2 curve where the point count `N_p` alone does
NOT pin it. The light `𝔽_p` group law reads the individual order beyond genus 1. -/
theorem picOrder_pt01_X5p1_eq :
    picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1 = some 5 := by native_decide

/-- The light point-list order of `(0,1) − ∞` MATCHES the Cantor `cantorOrder` over `𝔽₁₁`
(`native_decide`) — the individual-class order read on the light **point-list** representation equals the
order the heavy hyperelliptic Mumford/Cantor engine gives, on a GENUS-2 curve. Both compute the order of
`(0,1) − ∞` in `Pic⁰(C)(𝔽₁₁) = Jac(C)(𝔽₁₁)` (`= 5`); they agree — the cross-validation that the light
point-list group law reads the correct individual order on a non-genus-1 curve. -/
theorem picOrder_X5p1_matches_cantor :
    picOrder 30 11 picRhoX5p1Mod11 2 picPt01_X5p1
      = cantorOrder 200 (polyToZMod 11 hypRhoX5p1) 2 (mumfordReduceModP 11 hypG2Pt01) := by
  native_decide

end DeepWiki.SymbolicIntegration

/-! ## Proof-of-concept II: genus-1 cross-check against the point count `N_p` (`native_decide`)

On a **genus-1** curve `Pic⁰(C)(𝔽_p)` is cyclic of order `N_p = |Pic⁰(C)(𝔽_p)|`, so the light group law's
individual-class order must **divide `N_p`**. We cross-check the light `picOrder` against
`ComputableGeneralTorsionLight`'s `npHypOddDeg` on `y² = x³ + 1` (torsion `ℤ/6`): the light group-law order
of `(2,3) − ∞` (= 6) divides `N₁₁ = 12`, and matches the Cantor order. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The genus-1 radicand `ρ = x³ + 1 ∈ 𝔽₁₁[x]` (`polyToZMod` of Cantor's `hypRhoX3p1`), the curve
`y² = x³ + 1` over `𝔽₁₁`. Torsion `ℤ/6`. -/
def picRhoX3p1Mod11 : CPolyG (ZMod 11) := polyToZMod 11 hypRhoX3p1

/-- The class `(2, 3) − ∞` on `y² = x³ + 1` over `𝔽₁₁` (`3² = 9 = 2³ + 1`), as `[(2, 3)]` — the generator
of the full `ℤ/6` torsion (over ℚ); here its order in `Pic⁰(C)(𝔽₁₁)`. -/
def picPt23_X3p1 : RedDiv 11 := [((2 : ZMod 11), (3 : ZMod 11))]

/-- The light group-law order of `(2,3) − ∞` on `y² = x³+1` over `𝔽₁₁` is 6 and DIVIDES the point count
`N₁₁ = 12` (`native_decide`): for the GENUS-1 curve `Pic⁰(C)(𝔽₁₁)` is cyclic of order `N₁₁ = npHypOddDeg
11 (hypCurveX3p1 11)` (the `ComputableGeneralTorsionLight` point count), so any class's order divides `N₁₁`
— the light `picOrder = some 6` is consistent with the flat point count (`12 % 6 = 0`). Cross-validates the
light group law against the torsion-light `N_p`. -/
theorem picOrder_pt23_X3p1_divides_Np :
    picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1 = some 6
      ∧ npHypOddDeg 11 (hypCurveX3p1 11) % 6 = 0 := by native_decide

/-- The light order of `(2,3) − ∞` matches the Cantor order over `𝔽₁₁` (`native_decide`): both the
light point-list group law and the heavy Mumford/Cantor engine give order 6 for `(2,3) − ∞` in
`Pic⁰(C)(𝔽₁₁)` on `y² = x³+1` — the genus-1 cross-check of the light group law against Cantor, complementing
the divides-`N_p` check. -/
theorem picOrder_X3p1_matches_cantor :
    picOrder 30 11 picRhoX3p1Mod11 1 picPt23_X3p1
      = cantorOrder 60 (polyToZMod 11 hypRhoX3p1) 1 (mumfordReduceModP 11 hypPt23) := by
  native_decide

end DeepWiki.SymbolicIntegration

/-! ## The light-general-Picard-group-law milestone (`native_decide`) -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- THE LIGHT `𝔽_p` POINT-LIST PICARD GROUP LAW + INDIVIDUAL-CLASS ORDER `picOrder` READ THE ORDER OF
A SPECIFIC DIVISOR CLASS BEYOND THE GENUS-1 CEILING (Trager Ch. 6 / computational AG, `native_decide`).
Where `ComputableGeneralTorsionLight`'s flat point count pins the order only for genus 1 (cyclic `Pic⁰` of
order `N_p`), the **light point-list group law** — `RedDiv p = List (ZMod p × ZMod p)` (reduced divisor),
`pdivAdd = pdivReduce ∘ pdivCompose` (compose by `++`, reduce by a faithful Cantor compose/reduce
**round-trip** on the point list — `ptToMum` / `mumToPts`, with the independent `𝔽_p` root scan
`rootsWithMult` reading the support back), `picMul` / `picOrder` (the individual-class order) — reads an
**individual class's order** on the point-list representation, in light `𝔽_p[x]` arithmetic on short lists
(no `QFunNZG`, no `𝔽_p[x]` HNF), and `native_decide`-compiles:
* on the **GENUS-2** curve `y² = x⁵ + 1` over `𝔽₁₁` (where `|Pic⁰| ≠ N_p`, Cantor the only prior group law),
  `picOrder` reads the order of `(0,1) − ∞` as **5** and it **matches the Cantor `cantorOrder`** for the
  same class (`picOrder_X5p1_matches_cantor`) — the individual order, `native_decide`-readable on a
  non-genus-1 curve; the double `2·((0,1)−∞)` is a genuine degree-2 reduced divisor
  (`picMul_two_pt01_X5p1_deg`);
* the inverse law holds on the light representation: `(0,1) + (0,−1)` cancels to the identity `[]`
  (`pdivAdd_pt01_opp_X5p1`);
* on the **genus-1** `y² = x³ + 1` over `𝔽₁₁`, the light order of `(2,3) − ∞` is **6**, divides the point
  count `N₁₁ = 12` (`picOrder_pt23_X3p1_divides_Np`) and matches Cantor (`picOrder_X3p1_matches_cantor`) —
  the cross-check against `ComputableGeneralTorsionLight`.
The light `𝔽_p` point-list group law + `picOrder` make the **individual-class order** `native_decide`-
readable on a genuinely non-genus-1 curve — the follow-up the point-count ceiling could not reach. -/
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

/-! ## Verdict & scope

**The light `𝔽_p` Picard group law reads an individual divisor class's order beyond the genus-1 ceiling.**
The reduced-divisor representation is a `𝔽_p`-point list (`RedDiv p`); the group law `pdivAdd` is
compose-by-`++` then reduce (a faithful Cantor compose/reduce **round-trip** on the point list, with the
independent `𝔽_p` root scan `rootsWithMult` reading the support back); the individual-class order is
`picOrder` (the `cantorOrder` analogue). All arithmetic stays light `𝔽_p[x]` on short lists — **no
`QFunNZG`, no `𝔽_p[x]` HNF** (the compilation wall `ComputableGeneralTorsionLight` avoids), every
`native_decide` under a second on the small `𝔽₁₁` examples.

**The proof-of-concept (`picOrder_X5p1_matches_cantor`): on the GENUS-2 curve `y² = x⁵ + 1` over `𝔽₁₁`, the
light `picOrder` reads the order of `(0,1) − ∞` as 5 and it equals the heavy Mumford/Cantor `cantorOrder`
for the same class** — the individual-class order is now `native_decide`-readable on a non-genus-1 curve via
the light point-list representation, cross-validated against Cantor (and, on genus-1 `y² = x³+1`, against
the `ComputableGeneralTorsionLight` point count `N_p`).

**Honest scope (what is reused / what stays heavy).** The class **representation** and the order search are
the new light point-list layer; the **reduction engine** is reused from the proven hyperelliptic Cantor
`cantorCompose`/`cantorReduce` (via the `ptToMum`/`mumToPts` round-trip) — that is what gets every
multiplicity (the tangent-line doubling) right, where a naive Lagrange interpolation on a repeated point
does not. So the light layer is the **point-list class representation + individual-order reader**, faithful
to Cantor's hyperelliptic arithmetic. Two things stay heavy / deferred: (i) a fully *self-contained*
point-list reduction (Hermite/CRT interpolation handling repeated points without the Mumford round-trip);
(ii) the **non-hyperelliptic** general case (a plane curve with no explicit `y²=ρ` involution, e.g. the
Fermat cubic `x³ + y³ = 1`), which needs the general `L((g+1)·∞)` linear solve over a bivariate monomial
basis — both **recorded — not formalized here** — in the `Sources/Doi_10_1007_b138171`
`## NOT YET FORMALIZED` catalog. The milestone delivered: the light point-list group law + `picOrder`,
reading an individual class's order on a genus-2 curve, cross-validated against Cantor and the `N_p` point
count. -/

end DeepWiki.SymbolicIntegration
