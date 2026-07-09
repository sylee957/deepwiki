import DeepWiki.SymbolicIntegration.Engine.Algebraic.ZassenhausDecider.Core.Recombination

/-! # Zassenhaus executable pipeline

Mod-`p` factorization, Hensel lifting, recombination wiring, and the final Boolean decider.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- Lift a `ZMod p` coefficient list to `List ℤ` via `ZMod.val` (representative in `[0, p)`). -/
def liftZMod {p : ℕ} (l : List (ZMod p)) : List ℤ := l.map (fun a => (a.val : ℤ))

/-- Fueled extended Euclidean algorithm over a field: returns `(d, s, t)` with
`s·f + t·g = d = gcd(f, g)`. -/
def xgcdByMonicFuel {R : Type*} [Field R] [DecidableEq R] :
    ℕ → List R → List R → List R × List R × List R
  | 0, f, _ => (f, [1], [])
  | fuel + 1, f, g =>
    if lengthTrim g = 0 then (f, [1], [])
    else
      let lc := (leadL g)⁻¹
      let gm := monicizeL g
      let dg := lengthTrim g - 1
      let qr := divmodByMonic f gm dg
      let q := qr.1
      let r := qr.2
      let res := xgcdByMonicFuel fuel gm r
      -- res = (d, s', t') with s'·gm + t'·r = d.  r = f − gm·q, gm = lc·g.
      -- d = s'·gm + t'·(f − gm·q) = t'·f + (s' − t'·q)·gm = t'·f + (s' − t'·q)·lc·g.
      let d := res.1
      let s' := res.2.1
      let t' := res.2.2
      (d, t', scaleL lc (subL s' (mulL t' q)))

/-- Extended Euclidean gcd with cofactors over a field: `(gcd, s, t)` with `s·f + t·g = gcd`. -/
def xgcdByMonic {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    List R × List R × List R :=
  xgcdByMonicFuel (g.length + 1) f g

/-- The Bézout cofactors `(s, t)` with `s·g + t·h = 1` over `𝔽_p` for a coprime pair `(g, h)`. -/
def bezoutModP {p : ℕ} [Fact p.Prime] (g h : List (ZMod p)) : List (ZMod p) × List (ZMod p) :=
  let res := xgcdByMonic g h
  let c := leadL res.1  -- the gcd is a nonzero constant; its (only) coefficient
  (scaleL c⁻¹ res.2.1, scaleL c⁻¹ res.2.2)

/-- Degree-correct distinct-degree factorization over `𝔽_p`: returns `(d, block)` pairs of the
degree-`d` blocks, advancing through trivial blocks until the cofactor is a constant. -/
def ddfCorrect (p : ℕ) [Fact p.Prime] : ℕ → ℕ → List (ZMod p) → List (ℕ × List (ZMod p))
  | 0, _, _ => []
  | fuel + 1, d, f =>
    if lengthTrim f ≤ 1 then []                       -- cofactor is a constant: done
    else if d + 1 ≥ lengthTrim f then [(lengthTrim f - 1, f)]  -- remainder is itself irreducible
    else
      let df := lengthTrim f - 1
      let sep := subL (xPowModF p d f df) [0, 1]
      let gd := gcdByMonic f sep
      if 1 < lengthTrim gd then
        let gdm := monicizeL gd
        let cof := (divmodByMonic f gdm (lengthTrim gd - 1)).1
        (d, gdm) :: ddfCorrect p fuel (d + 1) cof
      else
        ddfCorrect p fuel (d + 1) f                   -- trivial block: keep going

/-- Full irreducible factorization over `𝔽_p`: distinct-degree blocks each equal-degree-split, flattened. -/
def factorModP (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) : List (List (ZMod p)) :=
  (ddfCorrect p (f.length + 1) 1 f).flatMap (fun b => edfBlock p b.1 (b.2.length + 1) 0 b.2)

/-- The number of Hensel doubling rounds to reach modulus `p^{2^k} > 2·mignotteBound f`. -/
def henselRounds (p : ℕ) (f : List ℤ) : ℕ :=
  let target := 2 * mignotteBound f + 1
  let rec go : ℕ → ℕ → ℕ
    | 0, _ => 0
    | fuel + 1, k => if target ≤ p ^ (2 ^ k) then k else go fuel (k + 1)
  go (mignotteBound f + 1) 0

/-- A degree-stable quadratic Hensel round on `List ℤ` factors: lifts monic `g, h` and cofactors
`s, t` to mod `p^{2m}`, keeping the factor degrees fixed. -/
def henselRoundStable (p : ℕ) (f : List ℤ) (m : ℕ) (g h s t : List ℤ) :
    List ℤ × List ℤ × List ℤ × List ℤ :=
  let n2 := p ^ (2 * m)
  let dg := lengthTrim g - 1
  let dh := lengthTrim h - 1
  let e := subL f (mulL g h)
  -- v = (t·e) mod g, q = (t·e) div g  (g monic of degree dg)
  let te := mulL t e
  let teqr := divmodByMonic te g dg
  let q := teqr.1
  let v := teqr.2
  -- u = s·e + h·q
  let u := addL (mulL s e) (mulL h q)
  let g' := reduceModN n2 (addL g v)
  let h' := reduceModN n2 (addL h u)
  -- reduce cofactors mod the new factors to keep them bounded:
  --   sustain Bézout by re-reducing s mod h', t mod g'
  let s' := reduceModN n2 (modByMonicL s h' dh)
  let t' := reduceModN n2 (modByMonicL t g' dg)
  (g', h', s', t')

/-- Iterate `henselRoundStable` for `k` doubling rounds; returns the lifted factors and cofactors. -/
def henselLiftStable (p : ℕ) (f : List ℤ) :
    ℕ → ℕ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ × List ℤ × List ℤ × List ℤ
  | 0, _, g, h, s, t => (g, h, s, t)
  | k + 1, m, g, h, s, t =>
    let r := henselRoundStable p f m g h s t
    henselLiftStable p f k (2 * m) r.1 r.2.1 r.2.2.1 r.2.2.2

/-- Lift a two-factor mod-`p` split `(g, h)` of `f` to mod `p^{2^k}`, returning `(g', h')` as `List ℤ`. -/
def henselLiftPair {p : ℕ} [Fact p.Prime] (f : List ℤ) (g h : List (ZMod p)) :
    List ℤ × List ℤ :=
  let st := bezoutModP g h
  let k := henselRounds p f
  let r := henselLiftStable p f k 1 (liftZMod g) (liftZMod h) (liftZMod st.1) (liftZMod st.2)
  (r.1, r.2.1)

/-- The product of a list of `ZMod p` factors (`mulL`-fold from `[1]`). -/
def listProdModP {p : ℕ} (fs : List (List (ZMod p))) : List (ZMod p) :=
  fs.foldr (fun a acc => mulL a acc) [1]

/-- Lift a mod-`p` factorization `[g₁, …, gᵣ]` of `f` to mod `p^{2^k}` as `List ℤ` factors, by
repeatedly lifting the head against the product of the tail. -/
def henselLiftMany {p : ℕ} [Fact p.Prime] (f : List ℤ) :
    ℕ → List (List (ZMod p)) → List (List ℤ)
  | _, [] => []
  | _, [g] => [liftZMod g]          -- single factor: lift directly (no Bézout needed)
  | 0, gs => gs.map liftZMod        -- out of fuel: lift each crudely
  | fuel + 1, g :: gs =>
    let h := listProdModP gs        -- product of the rest
    let gh := henselLiftPair f g h
    gh.1 :: henselLiftMany f fuel gs

/-- The complete Zassenhaus decider: `true` iff monic degree-`n` `toPolyZ f` is `ℚ`-irreducible, via
factoring mod `p`, Hensel-lifting, and recombining over the lifted factors. -/
def irreducibleZassenhaus (p : ℕ) [Fact p.Prime] (f : List ℤ) (n : ℕ) : Bool :=
  let facp := factorModP p (reduceCoeffs p f)   -- mod-p irreducible factors (degree-correct)
  -- degree-n guard + a genuine factorization mod p (≥ 1 factor) is required
  if lengthTrim f ≠ n + 1 ∨ facp.length = 0 then false
  -- a single mod-p irreducible factor already proves ℚ-irreducibility (the mod-p test)
  else if facp.length = 1 then true
  else
    let pk := (p : ℤ) ^ (2 ^ henselRounds p f)  -- the lift modulus
    let lifted := henselLiftMany f (facp.length + 1) facp
    let degs := recombine f pk lifted
    -- irreducible iff NO proper ℤ-factor found
    degs.isEmpty

end DeepWiki.SymbolicIntegration
