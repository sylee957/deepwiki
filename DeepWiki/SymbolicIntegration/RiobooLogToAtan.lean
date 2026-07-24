import DeepWiki.SymbolicIntegration.RiobooRealLogarithm

/-! # Rioboo's `LogToAtan`: complex-log to real-arctan conversion
`LogToAtan(A, B)` returns a list of arctangent arguments whose arctan-derivative sum `∑ 2·P'/(1+P²)`
equals `i · d/dx log((A+iB)/(A−iB))`, in a char-`0` differential field with `i² = −1`, with branch
decisions on `K[x]` operands embedded via a derivation-commuting ring hom `φ`. -/

open Polynomial
open scoped Differential
open Classical

namespace DeepWiki.SymbolicIntegration

section AtanDerivSum
variable {R : Type*} [Field R] [Differential R]

/-- **Arctan-derivative sum** of a list of arctan arguments: `atanDerivSum L = ∑_{P∈L} 2·P'/(1+P²)`,
the derivative of `∑_{P∈L} 2·arctan(P)`. -/
def atanDerivSum (L : List R) : R :=
  (L.map fun P => 2 * (P′ / (1 + P ^ 2))).sum

/-- `atanDerivSum [] = 0`. -/
@[simp] theorem atanDerivSum_nil : atanDerivSum ([] : List R) = 0 := by
  simp [atanDerivSum]

/-- `atanDerivSum (P :: L) = 2·P'/(1+P²) + atanDerivSum L`. -/
@[simp] theorem atanDerivSum_cons (P : R) (L : List R) :
    atanDerivSum (P :: L) = 2 * (P′ / (1 + P ^ 2)) + atanDerivSum L := by
  simp [atanDerivSum]

/-- `atanDerivSum [P] = 2·P'/(1+P²)`. -/
theorem atanDerivSum_singleton (P : R) : atanDerivSum [P] = 2 * (P′ / (1 + P ^ 2)) := by
  simp

end AtanDerivSum

section LogToAtan
variable {K : Type*} [Field K]
variable {R : Type*} [Field R] [Differential R] [CharZero R]

/-- Fuel-bounded `LogToAtan` recursion: `logToAtanAux φ fuel A B` returns the list of arctan arguments
in `R` via `φ`, with branches `B ∣ A`, `deg A < deg B`, and the extended-Euclidean cofactor step. -/
noncomputable def logToAtanAux (φ : K[X] →+* R) : ℕ → K[X] → K[X] → List R
  | 0, _, _ => []
  | fuel + 1, A, B =>
    if B ∣ A then
      [φ A / φ B]
    else if A.degree < B.degree then
      logToAtanAux φ fuel (-B) A
    else
      let C := EuclideanDomain.gcdB B (-A)
      let D := EuclideanDomain.gcdA B (-A)
      let G := EuclideanDomain.gcd B (-A)
      (φ A * φ D + φ B * φ C) / φ G :: logToAtanAux φ fuel D C

variable {φ : K[X] →+* R} {i : R}

/-- `imagLog φ i A B := logDeriv((φA + i·φB)/(φA − i·φB))`, the complex-log term via `φ`. -/
noncomputable def imagLog (φ : K[X] →+* R) (i : R) (A B : K[X]) : R :=
  Differential.logDeriv ((φ A + i * φ B) / (φ A - i * φ B))

/-- Base case (`B ∣ A`): with `(φA)²+(φB)² ≠ 0`, `atanDerivSum [φA/φB] = i · imagLog φ i A B`. -/
theorem atanDerivSum_base (hi : i ^ 2 = -1)
    {A B : K[X]} (hB : φ B ≠ 0) (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) :
    atanDerivSum [φ A / φ B] = i * imagLog φ i A B := by
  set u := φ A / φ B with hu
  have huB : u * φ B = φ A := div_mul_cancel₀ _ hB
  -- nonvanishing of `u ± i`
  have hApiB : φ A + i * φ B ≠ 0 := add_imag_ne_zero hi hAB
  have hAmiB : φ A - i * φ B ≠ 0 := sub_imag_ne_zero hi hAB
  have hupi : u + i ≠ 0 := by
    intro h
    apply hApiB
    have : (u + i) * φ B = φ A + i * φ B := by rw [add_mul, huB]
    rw [h, zero_mul] at this; exact this.symm
  have humi : u - i ≠ 0 := by
    intro h
    apply hAmiB
    have : (u - i) * φ B = φ A - i * φ B := by rw [sub_mul, huB]
    rw [h, zero_mul] at this; exact this.symm
  -- `(φA+iφB)/(φA−iφB) = (u+i)/(u−i)`
  have hquot : (φ A + i * φ B) / (φ A - i * φ B) = (u + i) / (u - i) := by
    rw [div_eq_div_iff hAmiB humi, ← huB]; ring
  rw [imagLog, hquot, atanDerivSum_singleton,
    ← logDeriv_imagQuot_eq_arctanDeriv_of_sq hi hupi humi]

/-- Swap step (`deg A < deg B`): `i · imagLog φ i (-B) A = i · imagLog φ i A B`. -/
theorem imagLog_swap (hi : i ^ 2 = -1) (hφneg : ∀ p : K[X], φ (-p) = -φ p)
    {A B : K[X]} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) :
    i * imagLog φ i (-B) A = i * imagLog φ i A B := by
  rw [imagLog, imagLog, hφneg, logDeriv_imagQuot_eq_imagQuot_swap hi hAB]

/-- Recursion step: with `φB·φD − φA·φC = φG`, `φG ≠ 0`, `(φA)²+(φB)² ≠ 0`, `(φC)²+(φD)² ≠ 0`,
`i·imagLog φ i A B = atanDerivSum [(φA·φD + φB·φC)/φG] + i·imagLog φ i D C`. -/
theorem imagLog_step (hi : i ^ 2 = -1)
    {A B C D G : K[X]} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) (hCD : (φ C) ^ 2 + (φ D) ^ 2 ≠ 0)
    (hG : φ B * φ D - φ A * φ C = φ G) (hG0 : φ G ≠ 0) :
    i * imagLog φ i A B
      = atanDerivSum [(φ A * φ D + φ B * φ C) / φ G] + i * imagLog φ i D C := by
  rw [imagLog, imagLog, atanDerivSum_singleton,
    logDeriv_imagQuot_eq_arctan_add_imagQuot hi hAB hCD hG hG0]

/-- Inductive spec of a complete Rioboo `LogToAtan` recursion on `(A, B)` producing the arctan-argument
list `L`, with constructors `base`, `swap`, `step` mirroring the three branches. -/
inductive IsLogToAtanRun (φ : K[X] →+* R) (i : R) : K[X] → K[X] → List R → Prop
  | base {A B : K[X]} (hB : φ B ≠ 0) (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) (hdvd : B ∣ A) :
      IsLogToAtanRun φ i A B [φ A / φ B]
  | swap {A B : K[X]} {L : List R} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0)
      (hrun : IsLogToAtanRun φ i (-B) A L) :
      IsLogToAtanRun φ i A B L
  | step {A B C D G : K[X]} {L : List R} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0)
      (hCD : (φ C) ^ 2 + (φ D) ^ 2 ≠ 0) (hG : φ B * φ D - φ A * φ C = φ G) (hG0 : φ G ≠ 0)
      (hrun : IsLogToAtanRun φ i D C L) :
      IsLogToAtanRun φ i A B ((φ A * φ D + φ B * φ C) / φ G :: L)

/-- For any complete run `IsLogToAtanRun φ i A B L`, `atanDerivSum L = i · imagLog φ i A B`. -/
theorem isLogToAtanRun_correct (hi : i ^ 2 = -1) (hφneg : ∀ p : K[X], φ (-p) = -φ p)
    {A B : K[X]} {L : List R} (hrun : IsLogToAtanRun φ i A B L) :
    atanDerivSum L = i * imagLog φ i A B := by
  induction hrun with
  | base hB hAB _ => exact atanDerivSum_base hi hB hAB
  | swap hAB _ ih => rw [ih, imagLog_swap hi hφneg hAB]
  | step hAB hCD hG hG0 _ ih =>
      rw [atanDerivSum_cons, ← atanDerivSum_singleton, ih, ← imagLog_step hi hAB hCD hG hG0]

omit [Differential R] [CharZero R] in
/-- Fuel base branch: when `B ∣ A`, `logToAtanAux φ (n+1) A B = [φA/φB]`. -/
@[simp] theorem logToAtanAux_base {n : ℕ} {A B : K[X]} (hdvd : B ∣ A) :
    logToAtanAux φ (n + 1) A B = [φ A / φ B] := by
  rw [logToAtanAux]; simp [hdvd]

omit [Differential R] [CharZero R] in
/-- Fuel swap branch: when `¬ B ∣ A` and `deg A < deg B`, `logToAtanAux φ (n+1) A B = logToAtanAux φ n (-B) A`. -/
theorem logToAtanAux_swap {n : ℕ} {A B : K[X]} (hdvd : ¬ B ∣ A) (hlt : A.degree < B.degree) :
    logToAtanAux φ (n + 1) A B = logToAtanAux φ n (-B) A := by
  rw [logToAtanAux]; simp [hdvd, hlt]

omit [Differential R] [CharZero R] in
/-- Fuel step branch: when `¬ B ∣ A` and `deg A ≥ deg B`, the fuel def prepends `(φA·φD + φB·φC)/φG`
(cofactors `C = gcdB(B,−A)`, `D = gcdA(B,−A)`, `G = gcd(B,−A)`) and recurses on `(D, C)`. -/
theorem logToAtanAux_step {n : ℕ} {A B : K[X]} (hdvd : ¬ B ∣ A) (hle : ¬ A.degree < B.degree) :
    logToAtanAux φ (n + 1) A B
      = (φ A * φ (EuclideanDomain.gcdA B (-A)) + φ B * φ (EuclideanDomain.gcdB B (-A)))
          / φ (EuclideanDomain.gcd B (-A))
        :: logToAtanAux φ n (EuclideanDomain.gcdA B (-A)) (EuclideanDomain.gcdB B (-A)) := by
  rw [logToAtanAux]; simp [hdvd, hle]

/-- If `logToAtanAux φ fuel A B` is a complete run, `atanDerivSum (logToAtanAux φ fuel A B) = i · imagLog φ i A B`. -/
theorem logToAtanAux_correct (hi : i ^ 2 = -1) (hφneg : ∀ p : K[X], φ (-p) = -φ p)
    {A B : K[X]} {fuel : ℕ} (hrun : IsLogToAtanRun φ i A B (logToAtanAux φ fuel A B)) :
    atanDerivSum (logToAtanAux φ fuel A B) = i * imagLog φ i A B :=
  isLogToAtanRun_correct hi hφneg hrun

end LogToAtan

end DeepWiki.SymbolicIntegration
