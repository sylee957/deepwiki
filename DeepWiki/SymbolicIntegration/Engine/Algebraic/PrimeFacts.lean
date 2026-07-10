import Mathlib.Data.Nat.Prime.Basic

/-! # Concrete prime facts

Shared primality instances for the finite fields used by executable algebraic certificates.
-/

namespace DeepWiki.SymbolicIntegration

/-- `3` is prime. -/
instance factPrime3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- `5` is prime. -/
instance factPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- `7` is prime. -/
instance factPrime7 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `11` is prime. -/
instance factPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

end DeepWiki.SymbolicIntegration
