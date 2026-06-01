-- This module serves as the root of the `Leanproofs` library.
import Mathlib.Data.Set.Finite.Basic
import Leanproofs.MinPlusConvolution
import Leanproofs.MinPlus

/-- A first proof: 2 + 2 = 4. -/
theorem two_plus_two : 2 + 2 = 4 := by rfl

/-- Mathlib is available: the natural numbers are infinite. -/
example : Set.Infinite (Set.univ : Set ℕ) := Set.infinite_univ
