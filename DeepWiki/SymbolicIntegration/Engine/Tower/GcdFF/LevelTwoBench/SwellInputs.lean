import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.LevelOneBench

/-! # Level-2 fraction-free gcd swell benchmark inputs

Recursive benchmark inputs and size measures over `ℚ(x)(t₁)[t₂]` with genuine `t₁` denominators. -/

namespace DeepWiki.SymbolicIntegration

open BenchG

namespace BenchLvl2

open CPoly

/-- The `Lvl2 = ℚ(x)(t₁)` scalar `t₁ = s/1` (numerator the monomial `[0,1] ∈ (CFrac ℚ)[s]`). -/
def t1 : Lvl2 :=
  ⟨([(CField.zero : CFrac ℚ), CField.one], [CField.one]), CFrac.cisZeroG_one_singleton⟩

/-- The `Lvl2` scalar `1/t₁ = 1/s` (numerator `[1]`, denominator `[0,1] = s`), a genuine `t₁`
denominator. -/
def invT1 : Lvl2 :=
  ⟨([CField.one], [(CField.zero : CFrac ℚ), CField.one]), by native_decide⟩

/-- The `Lvl2` scalar `t₁ + 1`. -/
def t1p1 : Lvl2 := CField.add t1 CField.one

/-- The `Lvl2` scalar `1/(t₁ + 1)` (a genuine denominator). -/
def invT1p1 : Lvl2 :=
  ⟨([CField.one], [CField.one, CField.one]), by native_decide⟩

/-- The `Lvl2` scalar `t₁ − 1`. -/
def t1m1 : Lvl2 := CField.sub t1 CField.one

/-- A linear `t₂`-polynomial `a0 + a1·t₂` over `Lvl2` (low→high in `t₂`). -/
def lin2 (a0 a1 : Lvl2) : CPoly Lvl2 := [a0, a1]

/-- The fixed level-2 gcd target `(t₂ + t₁)·(t₂ − 1/t₁)`, degree 2 in `t₂` with a genuine `1/t₁`
denominator. -/
def commonFactor2 : CPoly Lvl2 :=
  cmul (lin2 t1 CField.one) (lin2 (CField.neg invT1) CField.one)

/-- The cofactor-coefficient cycle for `p` (period 5 through `t₁`, `1/t₁`, `t₁+1`, `1/(t₁+1)`, `t₁−1`). -/
def cyc2A : ℕ → Lvl2
  | 0 => t1 | 1 => invT1 | 2 => t1p1 | 3 => invT1p1 | 4 => t1m1 | n + 5 => cyc2A n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `cyc2A`). -/
def cyc2B : ℕ → Lvl2
  | 0 => invT1p1 | 1 => t1m1 | 2 => t1 | 3 => invT1 | 4 => t1p1 | n + 5 => cyc2B n

/-- The `p`-cofactor `∏_{i<k} (t₂ + cyc2A i)`, a `t₂`-polynomial of degree `k`. -/
def prod2A : ℕ → CPoly Lvl2
  | 0 => [CField.one]
  | n + 1 => cmul (lin2 (cyc2A n) CField.one) (prod2A n)

/-- The `q`-cofactor `∏_{i<k} (t₂ − cyc2B i)`, degree `k`, coprime to `prod2A k`. -/
def prod2B : ℕ → CPoly Lvl2
  | 0 => [CField.one]
  | n + 1 => cmul (lin2 (CField.neg (cyc2B n)) CField.one) (prod2B n)

/-- The level-2 benchmark dividend `p = commonFactor2 · prod2A k`, total `t₂`-degree `k + 2`. -/
def benchP2 (k : ℕ) : CPoly Lvl2 := cmul commonFactor2 (prod2A k)

/-- The level-2 benchmark divisor `q = commonFactor2 · prod2B k`, total `t₂`-degree `k + 2`;
`gcd(benchP2 k, benchQ2 k) ~ commonFactor2` (degree 2). -/
def benchQ2 (k : ℕ) : CPoly Lvl2 := cmul commonFactor2 (prod2B k)

/-- The naive Euclidean gcd `cmonic (cgcdWf …)` of the level-2 benchmark pair (the swelling kernel). -/
def benchExtGcd2 (k : ℕ) : CPoly Lvl2 := CPoly.cmonic (CPoly.cgcdWf (benchP2 k) (benchQ2 k)).1

/-- The raw stored size of one `CFrac ℚ` scalar: list lengths + `Σ(|num|+den)` of the ℚ entries. -/
def sizeLvl1 (z : CFrac ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of one `Lvl2 = ℚ(x)(t₁)` scalar: list lengths + `sizeLvl1` over the numerator and
denominator `s`-coefficients. -/
def sizeLvl2 (z : Lvl2) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + sizeLvl1 c) 0) +
    (z.1.2.foldl (fun a c => a + sizeLvl1 c) 0)

/-- The raw stored size of a whole `CPoly Lvl2`: `sizeLvl2` summed over the `t₂`-coefficients plus the
`t₂`-length. -/
def gcdSize2 (g : CPoly Lvl2) : ℕ :=
  (g : List Lvl2).foldl (fun a z => a + sizeLvl2 z) g.length

end BenchLvl2

end DeepWiki.SymbolicIntegration
