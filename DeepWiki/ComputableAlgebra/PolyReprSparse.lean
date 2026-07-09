import DeepWiki.ComputableAlgebra.PolyReprDegree

/-! # A sparse `CPoly` instance — the payoff (Step 5)

`SparsePoly α` wraps a *sparse* association list of `(degree, coefficient)` pairs — a genuinely
different carrier from the dense `List α`. (It is a one-field `structure`, not a `def`-synonym for
`List`, so it inherits nothing and does not collide with the dense `List` instance — the same newtype
discipline as the min-plus carriers.) Giving it a `CPoly` instance means **every** generic op
(`add`/`neg`/`scale`/`mul`, `toPoly`, `cisZero`/`cdeg`/`clead`/`cnorm`) and every correctness square
works on it for free, with the same `native_decide` showcase — proving the abstraction is genuinely
representation-independent. See `docs/representation-independent-poly.md`. -/

namespace DeepWiki.SymbolicIntegration.CPoly

/-- Sparse association-list polynomial: `(degree, coefficient)` pairs (a one-field wrapper). -/
structure SparsePoly (α : Type u) where
  /-- Wrap an association list as a sparse polynomial. -/
  ofList ::
  /-- The underlying `(degree, coefficient)` association list. -/
  toList : List (ℕ × α)

namespace SparsePoly

variable {α : Type u} [CCommRing α]

/-- Recursive coefficient lookup (first matching key, `0` if absent). -/
def scoeff : List (ℕ × α) → ℕ → α
  | [], _ => CCommRing.zero
  | (k, v) :: rest, i => if i = k then v else scoeff rest i

/-- `scoeff` of a `(degree, value)` list built from a coefficient function reads that function on the
key set. -/
theorem scoeff_map_pairs (l : List ℕ) (f : ℕ → α) (j : ℕ) :
    scoeff (l.map (fun i => (i, f i))) j = if j ∈ l then f j else CCommRing.zero := by
  induction l with
  | nil => simp [scoeff]
  | cons a as ih =>
    simp only [List.map_cons, scoeff, List.mem_cons]
    by_cases h : j = a
    · subst h; simp
    · rw [if_neg h, ih]; simp [h]

/-- Coefficients past the max-key bound vanish. -/
theorem scoeff_ge (p : List (ℕ × α)) (i : ℕ)
    (h : p.foldr (fun kv acc => max (kv.1 + 1) acc) 0 ≤ i) : scoeff p i = CCommRing.zero := by
  induction p with
  | nil => simp [scoeff]
  | cons a as ih =>
    obtain ⟨k, v⟩ := a; rw [List.foldr_cons] at h
    simp only [scoeff]; rw [if_neg (by omega), ih (le_trans (le_max_right _ _) h)]

end SparsePoly

/-- The sparse representation is a `CPoly` — the generic engine works on it unchanged. -/
instance instSparse : CPoly SparsePoly where
  coeff p i := SparsePoly.scoeff p.toList i
  degBound p := p.toList.foldr (fun kv acc => max (kv.1 + 1) acc) 0
  ofFn n f := ⟨(List.range n).map (fun i => (i, f i))⟩
  coeff_ofFn n f i := by
    show SparsePoly.scoeff ((List.range n).map (fun i => (i, f i))) i = _
    rw [SparsePoly.scoeff_map_pairs]; simp only [List.mem_range]
  coeff_ge p i h := SparsePoly.scoeff_ge p.toList i h

/-! ### The generic engine works on the sparse representation — same `native_decide` showcase -/

/-- Sparse `cisZero` reduces on an all-zero sparse poly (two stored zero coefficients). -/
example : cisZero (SparsePoly.ofList [(0, 0), (5, 0)] : SparsePoly ℚ) = true := by native_decide
/-- Sparse `cdeg` reduces: a stored `x⁵` term gives honest degree `5` (only two pairs stored). -/
example : cdeg (SparsePoly.ofList [(0, 1), (5, 7)] : SparsePoly ℚ) = 5 := by native_decide
/-- Sparse `clead` reduces: the leading coefficient of `1 + 7x⁵` is `7`. -/
example : clead (SparsePoly.ofList [(0, 1), (5, 7)] : SparsePoly ℚ) = 7 := by native_decide
/-- The generic `cpow` algorithm runs on the **sparse** carrier too: `(1 + x)²` has honest degree `2`
and leading coefficient `1` — the same algorithm, a different representation. -/
example : cdeg (cpow (SparsePoly.ofList [(0, 1), (1, 1)] : SparsePoly ℚ) 2) = 2 := by native_decide
/-- Sparse `(1 + x)²` has leading coefficient `1`. -/
example : clead (cpow (SparsePoly.ofList [(0, 1), (1, 1)] : SparsePoly ℚ) 2) = 1 := by native_decide
/-- Sparse `cderiv`: `d/dx (1 + 3x²) = 6x` has honest degree `1` — same algorithm on the sparse carrier. -/
example : cdeg (cderiv (SparsePoly.ofList [(0, 1), (2, 3)] : SparsePoly ℚ)) = 1 := by native_decide
/-- Sparse `ceval`: `(1 + 2x + 3x²)` at `x = 2` is `17`. -/
example : ceval (2 : ℚ) (SparsePoly.ofList [(0, 1), (1, 2), (2, 3)] : SparsePoly ℚ) = 17 := by
  native_decide

end DeepWiki.SymbolicIntegration.CPoly
