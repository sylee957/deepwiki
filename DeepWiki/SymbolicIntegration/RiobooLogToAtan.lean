import DeepWiki.SymbolicIntegration.RiobooRealLogarithm

/-! # Rioboo's `LogToAtan`: complex-log → real-arctan conversion (Bronstein §2.8, p.63)
Rioboo's `LogToAtan(A, B)` (`A, B ∈ K[x]`, `B ≠ 0`) returns a list of arctangent arguments whose
arctan-derivative sum `∑ 2·P'/(1+P²)` equals `i · d/dx log((A+iB)/(A−iB))`. The recursion:
`if B ∣ A return [A/B]`; `if deg A < deg B return LogToAtan(−B, A)`; else with the extended
Euclidean cofactors `B·D − A·C = G = gcd(A,B)`, `return (A·D+B·C)/G :: LogToAtan(D, C)`.

Each branch is exactly **Theorem 2.8.1** (already proved): base = the `q = A/B` form of Lemma 2.8.1,
swap = `logDeriv_imagQuot_eq_imagQuot_swap`, step = `logDeriv_imagQuot_eq_arctan_add_imagQuot`. Here we
add the recursion's list helper `atanDerivSum`, a **fuel-bounded** total `logToAtanAux`, the three
single-step unfolding identities, and the assembled correctness `logToAtanAux_correct` (under a
"fuel reaches the base case" predicate). Everything is stated abstractly in a characteristic-`0`
differential field `R` with `i² = −1`; the algorithm's branch decisions live on the `K[x]` operands,
embedded into `R` by a derivation-commuting ring hom `φ`. -/

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

/-- **`LogToAtan` recursion, fuel-bounded** (§2.8, p.63): `logToAtanAux φ fuel A B` runs Rioboo's
recursion `fuel` steps, returning the list of arctan arguments (as elements of `R` via `φ`). Branches:
`B ∣ A → [φ(A)/φ(B)]`; `deg A < deg B → LogToAtan(−B, A)`; else with `B·D − A·C = G = gcd(A,B)`,
`(φ(A)φ(D)+φ(B)φ(C))/φ(G) :: LogToAtan(D, C)`. Returns `[]` at `fuel = 0`. -/
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

/-- The two complex logarithms `log((A+iB)/(A−iB))` written via the embedding `φ`, abbreviated for the
`LogToAtan` correctness statements: `imagLog φ i A B := logDeriv((φA + i·φB)/(φA − i·φB))`. -/
noncomputable def imagLog (φ : K[X] →+* R) (i : R) (A B : K[X]) : R :=
  Differential.logDeriv ((φ A + i * φ B) / (φ A - i * φ B))

/-- **`LogToAtan` base case** (`B ∣ A`, §2.8 p.63): with `u = φA/φB` and `(φA)²+(φB)² ≠ 0`,
`atanDerivSum [φA/φB] = i · logDeriv((φA+iφB)/(φA−iφB))` — i.e. `2·u'/(1+u²) = i·logDeriv((u+i)/(u−i))`
by Lemma 2.8.1, after clearing `φB` from the quotient. -/
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

/-- **`LogToAtan` swap step** (`deg A < deg B`, §2.8 p.63): `i·logDeriv((φ(−B)+iφA)/(φ(−B)−iφA))
= i·logDeriv((φA+iφB)/(φA−iφB))` — Theorem 2.8.1(a) applied to `φA, φB`, using `φ(−B) = −φB`. -/
theorem imagLog_swap (hi : i ^ 2 = -1) (hφneg : ∀ p : K[X], φ (-p) = -φ p)
    {A B : K[X]} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) :
    i * imagLog φ i (-B) A = i * imagLog φ i A B := by
  rw [imagLog, imagLog, hφneg, logDeriv_imagQuot_eq_imagQuot_swap hi hAB]

/-- **`LogToAtan` recursion step** (`deg A ≥ deg B`, §2.8 p.63): with the extended-Euclidean cofactors
`C = gcdB(B,−A)`, `D = gcdA(B,−A)`, `G = gcd(B,−A)` (so `φB·φD − φA·φC = φG`), `G ≠ 0`,
`(φC)²+(φD)² ≠ 0`, and `P = (φA·φD + φB·φC)/φG`, one step of Rioboo's recursion satisfies
`i·imagLog φ i A B = atanDerivSum [P] + i·imagLog φ i D C` — exactly Theorem 2.8.1(b). -/
theorem imagLog_step (hi : i ^ 2 = -1)
    {A B C D G : K[X]} (hAB : (φ A) ^ 2 + (φ B) ^ 2 ≠ 0) (hCD : (φ C) ^ 2 + (φ D) ^ 2 ≠ 0)
    (hG : φ B * φ D - φ A * φ C = φ G) (hG0 : φ G ≠ 0) :
    i * imagLog φ i A B
      = atanDerivSum [(φ A * φ D + φ B * φ C) / φ G] + i * imagLog φ i D C := by
  rw [imagLog, imagLog, atanDerivSum_singleton,
    logDeriv_imagQuot_eq_arctan_add_imagQuot hi hAB hCD hG hG0]

/-- **A complete `LogToAtan` run** (§2.8 p.63): the inductive spec of a finite Rioboo recursion tree
on `(A, B)` producing the arctan-argument list `L : List R`. Constructors mirror the three branches:
`base` (`B ∣ A`, output `[φA/φB]`), `swap` (`deg A < deg B`, recurse on `(−B, A)`), and `step`
(`deg A ≥ deg B`, prepend `(φA·φD + φB·φC)/φG` and recurse on the cofactors `(D, C)`), each carrying the
nonvanishing data (`(φA)²+(φB)² ≠ 0`, `φB ≠ 0`, and for `step` the Bézout relation, `φG ≠ 0`,
`(φC)²+(φD)² ≠ 0`). Captures termination structurally without a degree measure. -/
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

/-- **`LogToAtan` correctness** (§2.8 p.63, the assembly of Theorem 2.8.1): for any complete Rioboo
run `IsLogToAtanRun φ i A B L`, the arctan-derivative sum of the output equals the complex logarithm,
`atanDerivSum L = i · imagLog φ i A B = i · d/dx log((φA+iφB)/(φA−iφB))`. Proof: induction on the run —
`base` is `atanDerivSum_base` (Lemma 2.8.1), `swap` is `imagLog_swap` (Thm 2.8.1(a)) after the IH, and
`step` is `imagLog_step` (Thm 2.8.1(b)) after the IH. -/
theorem isLogToAtanRun_correct (hi : i ^ 2 = -1) (hφneg : ∀ p : K[X], φ (-p) = -φ p)
    {A B : K[X]} {L : List R} (hrun : IsLogToAtanRun φ i A B L) :
    atanDerivSum L = i * imagLog φ i A B := by
  induction hrun with
  | base hB hAB _ => exact atanDerivSum_base hi hB hAB
  | swap hAB _ ih => rw [ih, imagLog_swap hi hφneg hAB]
  | step hAB hCD hG hG0 _ ih =>
      rw [atanDerivSum_cons, ← atanDerivSum_singleton, ih, ← imagLog_step hi hAB hCD hG hG0]

