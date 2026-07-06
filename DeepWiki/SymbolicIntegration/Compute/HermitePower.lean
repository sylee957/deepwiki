import DeepWiki.SymbolicIntegration.Compute.Correctness

/-! # Hermite inner-loop power construction
Reads the concrete `foldl (· * V)` power used by `hermiteInner` as a polynomial power under `toPoly`. -/

namespace DeepWiki.SymbolicIntegration.Compute

/-- `foldl (·* V) init` over `range n` realizes `init · V^n` under `toPoly`. -/
theorem toPoly_foldl_cmul (V : CPoly) (n : ℕ) (init : CPoly) :
    toPoly ((List.range n).foldl (fun acc _ => cmul acc V) init)
      = toPoly init * toPoly V ^ n := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_concat, toPoly_cmul, ih, pow_succ]
    ring

/-- The `hermiteInner` per-step power `Vpow = V^(j+1)` under `toPoly`. -/
theorem toPoly_hermiteInner_Vpow (V : CPoly) (j : ℕ) :
    toPoly ((List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1])
      = toPoly V ^ (j + 1) := by
  rw [toPoly_foldl_cmul]; simp [toPoly_cons]

end DeepWiki.SymbolicIntegration.Compute
