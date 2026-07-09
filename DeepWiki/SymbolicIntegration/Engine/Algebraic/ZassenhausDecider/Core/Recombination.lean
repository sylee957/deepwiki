import DeepWiki.SymbolicIntegration.Engine.Algebraic.ZassenhausDecider.Core.Bounds

/-! # Zassenhaus recombination search

Exact integer division, symmetric representatives, subset products, and the recombination search.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

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

/-- Shift `a % n` into the symmetric range `(−n/2, n/2]`: subtract `n` when the residue exceeds
`n/2`. -/
def symMod (n a : ℤ) : ℤ :=
  let r := a % n
  if r > n / 2 then r - n else r

/-- Apply `symMod n` to every coefficient of a list-poly: the symmetric-range representative. -/
def symModN (n : ℤ) (l : List ℤ) : List ℤ := l.map (symMod n)

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

end DeepWiki.SymbolicIntegration
