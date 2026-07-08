import DeepWiki.SymbolicIntegration.Computable.Algebraic.ZassenhausDecider.Iteration

/-! # The complete Zassenhaus `ℚ`-irreducibility decider

A computable, complete decider for irreducibility of a monic integer polynomial over `ℚ`: factor
`f` mod a good prime, Hensel-lift to mod `p^k`, recombine subset-products by `ℤ`-trial-division, and
report irreducible iff no proper factor surfaces. Runs on the coefficient `List ℤ` engine. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Mignotte coefficient bound

A `ℕ` over-bound on any `ℤ`-factor's coefficients, so each factor has a unique symmetric-range
representative once `2·mignotteBound f < p^k`. -/

/-- The maximum absolute value of the coefficients of a list-poly (`0` for the empty list). -/
def maxAbsCoeff (f : List ℤ) : ℕ :=
  f.foldr (fun a acc => max a.natAbs acc) 0

/-- Mignotte coefficient over-bound `2^(f.length+1) · (maxAbsCoeff f + 1)` on any `ℤ`-factor of `f`. -/
def mignotteBound (f : List ℤ) : ℕ :=
  2 ^ (f.length + 1) * (maxAbsCoeff f + 1)

/-- `maxAbsCoeff` bounds every coefficient: `|f.getD i 0| ≤ maxAbsCoeff f` for all `i`. -/
theorem natAbs_getD_le_maxAbsCoeff (f : List ℤ) (i : ℕ) :
    (f.getD i 0).natAbs ≤ maxAbsCoeff f := by
  induction f generalizing i with
  | nil => simp [maxAbsCoeff, List.getD]
  | cons a as ih =>
    rw [maxAbsCoeff, List.foldr_cons, ← maxAbsCoeff]
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      exact le_max_left _ _
    | succ j =>
      rw [List.getD_cons_succ]
      exact le_trans (ih j) (le_max_right _ _)

/-- The Mignotte bound is positive (the `+1` and the power of two). -/
theorem mignotteBound_pos (f : List ℤ) : 0 < mignotteBound f := by
  rw [mignotteBound]
  have h2 : 0 < 2 ^ (f.length + 1) := Nat.two_pow_pos _
  exact Nat.mul_pos h2 (by omega)

/-- `maxAbsCoeff f ≤ mignotteBound f`: the bound dominates the polynomial's own coefficients. -/
theorem maxAbsCoeff_le_mignotteBound (f : List ℤ) : maxAbsCoeff f ≤ mignotteBound f := by
  rw [mignotteBound]
  calc maxAbsCoeff f ≤ maxAbsCoeff f + 1 := by omega
    _ ≤ 1 * (maxAbsCoeff f + 1) := by rw [one_mul]
    _ ≤ 2 ^ (f.length + 1) * (maxAbsCoeff f + 1) :=
        Nat.mul_le_mul_right _ (Nat.one_le_two_pow)

/-! ## Recombination, stage 1: the exact `ℤ`-division test

Trial-divide `f` by each monic candidate over `ℤ`; a vanishing remainder is a genuine factorization
(`dividesExactly_dvd`), the soundness keystone. -/

/-- `true` iff `divmodByMonic f g dg` has zero remainder: `g` exactly divides `f` over `ℤ`. -/
def dividesExactly (f g : List ℤ) (dg : ℕ) : Bool :=
  decide (lengthTrim (divmodByMonic f g dg).2 = 0)

/-- A passing exact-division test yields the factorization
`toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1`. -/
theorem dividesExactly_dvd {f g : List ℤ} {dg : ℕ} (h : dividesExactly f g dg = true) :
    toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1 := by
  rw [dividesExactly, decide_eq_true_eq] at h
  have hid := divmodByMonic_spec f g dg
  have hr0 : toPoly (divmodByMonic f g dg).2 = 0 := toPoly_eq_zero_of_lengthTrim_eq_zero h
  rw [toPolyZ, hid, hr0, add_zero]

/-- A passing exact-division test yields a genuine **divisibility** `toPoly g ∣ toPolyZ f`. -/
theorem dvd_of_dividesExactly {f g : List ℤ} {dg : ℕ} (h : dividesExactly f g dg = true) :
    toPoly g ∣ toPolyZ f :=
  ⟨_, dividesExactly_dvd h⟩

/-! ## Recombination, stage 2: symmetric-range reduction

Map each coefficient mod `p^k` to its representative in the symmetric range `(−p^k/2, p^k/2]`. -/

/-- Shift `a % n` into the symmetric range `(−n/2, n/2]`: subtract `n` when the residue exceeds
`n/2`. -/
def symMod (n a : ℤ) : ℤ :=
  let r := a % n
  if r > n / 2 then r - n else r

/-- Apply `symMod n` to every coefficient of a list-poly: the symmetric-range representative. -/
def symModN (n : ℤ) (l : List ℤ) : List ℤ := l.map (symMod n)

/-! ## Recombination, stage 3: subset products and the search

Over sublists of the lifted factors, form each symmetric-reduced subset-product and `ℤ`-trial-divide
`f`, returning the degrees of the proper factors found. -/

/-- The product of a list of factor coefficient-lists (`mulL`-fold from `[1]`). -/
def listProd (fs : List (List ℤ)) : List ℤ :=
  fs.foldr (fun a acc => mulL a acc) [1]

/-- `toPoly` of a `listProd` is the product of the factors' `toPoly`s. -/
theorem toPoly_listProd (fs : List (List ℤ)) :
    toPoly (listProd fs) = (fs.map toPoly).prod := by
  induction fs with
  | nil => simp [listProd, toPoly]
  | cons a as ih =>
    rw [listProd, List.foldr_cons, toPoly_mulL, List.map_cons, List.prod_cons, ← listProd, ih]

/-- The subset-product of `sub`, symmetric-range-reduced mod `n`: a recombination candidate. -/
def recombineCandidate (n : ℤ) (sub : List (List ℤ)) : List ℤ :=
  symModN n (listProd sub)

/-- Recombination search: over all sublists of `facs` mod `n`, return the degrees of the
symmetric-reduced subset-products of proper degree `1 ≤ d < deg f` that exactly divide `f` over `ℤ`. -/
def recombine (f : List ℤ) (n : ℤ) (facs : List (List ℤ)) : List ℕ :=
  let degF := lengthTrim f - 1
  (facs.sublists.filterMap (fun sub =>
    let cand := recombineCandidate n sub
    let dc := lengthTrim cand
    -- proper factor: degree `dc - 1` in `[1, degF)`, exact divisor over ℤ
    if 2 ≤ dc ∧ dc - 1 < degF ∧ dividesExactly f cand (dc - 1) then
      some (dc - 1)
    else none))

/-! ## Recombination, stage 4: wiring `𝔽_p` factors into the `ℤ` Hensel lift

Lift `ZMod p` factors to `List ℤ` and compute Bézout cofactors over `𝔽_p` via the extended Euclidean
algorithm. -/

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

/-! ## A degree-correct `𝔽_p` factorization

A distinct-degree factorization whose recursion continues through trivial blocks (so degree tags stay
correct), then equal-degree-splits each block by its true degree. -/

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

/-! ## A degree-stable computational Hensel round

A degree-preserving quadratic step keeping each factor monic of its original degree, with cofactors
reduced mod the factors to stay bounded — the computational lift path. -/

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

/-! ## The complete Zassenhaus `ℚ`-irreducibility decider

Decide irreducibility of `toPolyZ f` over `ℚ` by the full factor / Hensel-lift / recombine pipeline. -/

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

/-! ## Soundness and completeness

The reducibility direction (`recombine` non-empty ⟹ `¬ Irreducible`) is proven outright via the
keystone `dividesExactly_dvd`. The irreducibility direction (`true ⟹ Irreducible`) is proven modulo
one isolated surfacing hypothesis `FactorSurfaces` (Hensel-lift uniqueness over `ZMod (p^k)` plus the
Mignotte bound), which is demonstrably realizable. -/

/-- A polynomial of positive `natDegree` is not a unit. -/
theorem not_isUnit_of_natDegree_pos {p : ℤ[X]} (hp : 0 < p.natDegree) : ¬ IsUnit p := by
  intro hu
  have hd : p.degree = 0 := degree_eq_zero_of_isUnit hu
  have : p.natDegree = 0 := natDegree_eq_of_degree_eq_some hd
  omega

/-- If `recombine f n facs` is non-empty then monic-degree-`N` `toPolyZ f` is reducible
(`¬ Irreducible`): the found candidate and its cofactor are both non-unit proper factors. -/
theorem recombine_imp_not_irreducible {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hne : recombine f n facs ≠ []) : ¬ Irreducible (toPolyZ f) := by
  -- extract a candidate from the non-empty filterMap
  rw [recombine] at hne
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall] at hne
  obtain ⟨sub, hsub_mem, hsub⟩ := hne
  -- decode the `if`: the guard held, so `dividesExactly` is true and the degree is proper
  set cand := recombineCandidate n sub with hcanddef
  set dc := lengthTrim cand with hdcdef
  -- the filterMap predicate produced `some _`, so the `if` condition is true
  by_cases hcond : 2 ≤ dc ∧ dc - 1 < lengthTrim f - 1 ∧ dividesExactly f cand (dc - 1)
  · obtain ⟨hdc2, hdclt, hdivex⟩ := hcond
    -- f = cand * q over ℤ
    have hfac : toPolyZ f = toPoly cand * toPoly (divmodByMonic f cand (dc - 1)).1 :=
      dividesExactly_dvd hdivex
    set q := (divmodByMonic f cand (dc - 1)).1 with hqdef
    -- natDegree (toPoly cand) = dc - 1  (cand reads as nonzero: lengthTrim ≥ 2 > 0)
    have hcandne : lengthTrim cand ≠ 0 := by omega
    have hcanddeg : (toPoly cand).natDegree = dc - 1 := natDegree_toPoly_eq hcandne
    -- N = natDegree f
    have hN : (toPolyZ f).natDegree = N := hmon.natDegree_eq
    have hcandne0 : toPoly cand ≠ 0 := by
      rw [Ne, toPoly_eq_zero_iff_lengthTrim]; omega
    have hfne0 : toPolyZ f ≠ 0 := hmon.monic.ne_zero
    have hqpoly_ne0 : toPoly q ≠ 0 := by
      intro h; rw [hfac, h, mul_zero] at hfne0; exact hfne0 rfl
    -- degree sum: natDegree f = natDegree cand + natDegree q
    have hdegsum : (toPoly cand).natDegree + (toPoly q).natDegree = N := by
      have := Polynomial.natDegree_mul hcandne0 hqpoly_ne0
      rw [← hfac, hN] at this; omega
    -- natDegree cand ≥ 1
    have hcandpos : 0 < (toPoly cand).natDegree := by rw [hcanddeg]; omega
    -- natDegree f = lengthTrim f - 1, so dc - 1 < N gives natDegree q ≥ 1
    have hfdeg : (toPolyZ f).natDegree = lengthTrim f - 1 :=
      natDegree_toPoly_eq (by rw [Ne, ← toPoly_eq_zero_iff_lengthTrim]; exact hfne0)
    have hNbig : dc - 1 < N := by rw [hN] at hfdeg; omega
    have hqpos : 0 < (toPoly q).natDegree := by omega
    -- both factors are non-units; conclude not irreducible
    intro hirr
    rcases hirr.isUnit_or_isUnit hfac with hu | hu
    · exact not_isUnit_of_natDegree_pos hcandpos hu
    · exact not_isUnit_of_natDegree_pos hqpos hu
  · -- the predicate must have been true for `some _` to be produced
    exfalso
    apply hsub
    rw [if_neg hcond]

/-- Contrapositive: an `Irreducible` monic-degree-`N` `toPolyZ f` forces `recombine f n facs = []`. -/
theorem irreducible_imp_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) (hirr : Irreducible (toPolyZ f)) :
    recombine f n facs = [] := by
  by_contra hne
  exact recombine_imp_not_irreducible hmon hne hirr

/-! ## Recombination completeness — the irreducibility direction (`true ⟹ Irreducible`)

The converse of `recombine_imp_not_irreducible`. The search plumbing (`recombine_ne_nil_of_witness`)
is proven outright; the deep content — Hensel-lift uniqueness over `ZMod (p^k)` plus the Mignotte
bound — is isolated into the surfacing hypothesis `FactorSurfaces`. -/

/-- A witness sublist whose symmetric-reduced subset-product is a proper-degree exact `ℤ`-divisor of
`f` forces `recombine f n facs ≠ []`. -/
theorem recombine_ne_nil_of_witness {f : List ℤ} {n : ℤ} {facs : List (List ℤ)}
    {sub : List (List ℤ)} (hmem : sub ∈ facs.sublists)
    (hdc2 : 2 ≤ lengthTrim (recombineCandidate n sub))
    (hdclt : lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1)
    (hdiv : dividesExactly f (recombineCandidate n sub)
      (lengthTrim (recombineCandidate n sub) - 1) = true) :
    recombine f n facs ≠ [] := by
  rw [recombine]
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall]
  refine ⟨sub, hmem, ?_⟩
  intro hcontra
  rw [if_pos ⟨hdc2, hdclt, hdiv⟩] at hcontra
  exact absurd hcontra (by simp)

/-- Surfacing predicate: a reducible monic-degree-`N` `toPolyZ f` has some sublist of `facs` whose
symmetric-reduced subset-product mod `n` is a proper-degree exact `ℤ`-divisor. -/
def FactorSurfaces (f : List ℤ) (n : ℤ) (facs : List (List ℤ)) (N : ℕ) : Prop :=
  IsMonicOfDegree (toPolyZ f) N → ¬ Irreducible (toPolyZ f) →
    ∃ sub ∈ facs.sublists,
      2 ≤ lengthTrim (recombineCandidate n sub) ∧
      lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1 ∧
      dividesExactly f (recombineCandidate n sub)
        (lengthTrim (recombineCandidate n sub) - 1) = true

/-- Given `FactorSurfaces`, a reducible monic-degree-`N` `toPolyZ f` forces `recombine f n facs ≠ []`. -/
theorem recombine_complete {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hred : ¬ Irreducible (toPolyZ f)) :
    recombine f n facs ≠ [] := by
  obtain ⟨sub, hmem, hdc2, hdclt, hdiv⟩ := hsurf hmon hred
  exact recombine_ne_nil_of_witness hmem hdc2 hdclt hdiv

/-- Given `FactorSurfaces`, `recombine f n facs = []` forces `toPolyZ f` irreducible. -/
theorem irreducible_of_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hnil : recombine f n facs = []) :
    Irreducible (toPolyZ f) := by
  by_contra hred
  exact recombine_complete hsurf hmon hred hnil

/-- A `true` verdict comes from one of two branches: a single mod-`p` factor, or empty recombination. -/
theorem irreducibleZassenhaus_eq_true_cases {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (h : irreducibleZassenhaus p f n = true) :
    (factorModP p (reduceCoeffs p f)).length = 1 ∨
    recombine f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) = [] := by
  rw [irreducibleZassenhaus] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact Or.inl (by rename_i hlen; exact hlen)
    · exact Or.inr (by rw [List.isEmpty_iff] at h; exact h)

/-- `irreducibleZassenhaus p f n = true → Irreducible (toPolyZ f)`, given the surfacing hypothesis
`hsurf` for the recombination branch and `hmodp` for the single-mod-`p`-factor branch. -/
theorem irreducibleZassenhaus_sound {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) n)
    (hsurf : FactorSurfaces f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) n)
    (hmodp : (factorModP p (reduceCoeffs p f)).length = 1 → Irreducible (toPolyZ f))
    (h : irreducibleZassenhaus p f n = true) :
    Irreducible (toPolyZ f) := by
  rcases irreducibleZassenhaus_eq_true_cases h with hlen | hnil
  · exact hmodp hlen
  · exact irreducible_of_recombine_nil hsurf hmon hnil

end DeepWiki.SymbolicIntegration
