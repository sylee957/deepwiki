import DeepWiki.ComputableAlgebra.PolyReprDegree

/-! # A sparse `CPolyRepr` instance — the payoff (Step 5)

`SparsePoly α` wraps a *sparse* association list of `(degree, coefficient)` pairs — a genuinely
different carrier from the dense `List α`. (It is a one-field `structure`, not a `def`-synonym for
`List`, so it inherits nothing and does not collide with the dense `List` instance — the same newtype
discipline as the min-plus carriers.) Giving it a `CPolyRepr` instance means **every** generic op
(`add`/`neg`/`scale`/`mul`, `toPoly`, `cisZero`/`cdeg`/`clead`/`cnorm`) and every correctness square
works on it for free, with the same `native_decide` showcase — proving the abstraction is genuinely
representation-independent. See `docs/representation-independent-poly.md`. -/

namespace DeepWiki.SymbolicIntegration.CPolyRepr

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

/-- The sparse representation is a `CPolyRepr` — the generic engine works on it unchanged. -/
instance instSparse : CPolyRepr SparsePoly where
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

end DeepWiki.SymbolicIntegration.CPolyRepr
