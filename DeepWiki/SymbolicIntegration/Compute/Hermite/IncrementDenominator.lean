import DeepWiki.SymbolicIntegration.Compute.Hermite.MultifactorIncrements

/-! # Hermite increment denominator support
Shows that each multifactor Hermite increment has denominator supported only on its own factor.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Increment denominators are powers of their factor -/

/-- **`hermiteInner`'s denominator is the seed denominator times a power of `V`**: there is `m` with
`toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 · (toPoly V)^m`. Each loop step `qadd`s
`(B, V^{j+1})`, multiplying the denominator by `V^{j+1}`; so the accumulated denominator is the seed
times a power of `V`. The structural fact that `glocᵢ` has poles only at `Vi`. -/
theorem hermiteInner_den_eq_pow (fuel : ℕ) (V U : DensePoly ℚ) :
    ∀ (j : ℕ) (A : DensePoly ℚ) (g : QFun),
      ∃ m : ℕ, toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 * toPoly V ^ m := by
  intro j
  induction j with
  | zero => intro A g; exact ⟨0, by simp [hermiteInner]⟩
  | succ j ih =>
    intro A g
    rw [hermiteInner]
    rcases hBC : cdiophantine (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A) with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    obtain ⟨m, hm⟩ := ih (csub (cscale (-((j : ℚ) + 1)) C) (cmul U (cderiv B))) (qadd g (B, Vpow))
    refine ⟨m + (j + 1), ?_⟩
    rw [hm]
    show toPoly (qadd g (B, Vpow)).2 * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    show toPoly (cmul g.2 Vpow) * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    have hVpow : DensePoly.toPoly Vpow = DensePoly.toPoly V ^ (j + 1) := by
      simpa only [toPoly_eq_dense] using toPoly_hermiteInner_Vpow V j
    simp only [toPoly_eq_dense]
    rw [DensePoly.toPolyG_cmulG, hVpow, pow_add]
    ring

/-- **`glocIncr`'s denominator is a pure power of `Vi`**: there is `m` with
`toPoly (glocIncr fuel A D Vi).2 = (toPoly Vi.1)^m`. From `hermiteInner_den_eq_pow` at the `qzero`
seed (denominator `1`). So `glocIncr Vi` (and its derivative) has poles only at `Vi` — regular at every
other irreducible factor. -/
theorem glocIncr_den_eq_pow (fuel : ℕ) (A D : DensePoly ℚ) (Vi : DensePoly ℚ × ℕ) :
    ∃ m : ℕ, toPoly (glocIncr fuel A D Vi).2 = toPoly Vi.1 ^ m := by
  obtain ⟨m, hm⟩ := hermiteInner_den_eq_pow fuel Vi.1
    (DensePoly.cdivWf D ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]))
    (Vi.2 - 1) A qzero
  refine ⟨m, ?_⟩
  rw [show (glocIncr fuel A D Vi).2
      = (hermiteInner fuel Vi.1 (DensePoly.cdivWf D
          ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1])) (Vi.2 - 1) A qzero).1.2 from rfl,
    hm]
  simp [qzero, toPoly_eq_dense, DensePoly.toPolyG_cons]

/-- **`glocIncr` is `Vk`-regular for `k ≠ i`**: if `P` is coprime to `Vi`, then `P` does not divide the
denominator of `glocIncr fuel A D Vi` to any positive power beyond what `P ∣ Vi^m` allows — concretely,
`IsRelPrime P (toPoly (glocIncr fuel A D Vi).2)` whenever `IsRelPrime P (toPoly Vi.1)`. The denominator
is `Vi^m` (`glocIncr_den_eq_pow`), coprime to `P`. This is the regularity that localizes `g′`'s pole at
each `Vk` to the single factor `k`. -/
theorem glocIncr_den_isRelPrime (fuel : ℕ) (A D : DensePoly ℚ) (Vi : DensePoly ℚ × ℕ) (P : ℚ[X])
    (hP : IsRelPrime P (toPoly Vi.1)) :
    IsRelPrime P (toPoly (glocIncr fuel A D Vi).2) := by
  obtain ⟨m, hm⟩ := glocIncr_den_eq_pow fuel A D Vi
  rw [hm]
  exact hP.pow_right

end DeepWiki.SymbolicIntegration.Compute
