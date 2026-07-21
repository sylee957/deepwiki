import DeepWiki.CAlgebra.Poly.Division
import DeepWiki.CAlgebra.Poly.DivisionPseudo

/-! # The descent kernel

One recursion drives every pseudo-remainder-sequence algorithm: `descentTrace` walks the
sequence under a state-threaded `clean` policy, recording each step's divisor and extracted
constant. Every algorithm is a fold over this trace: `gcdDescent` keeps the last element
(the gcd), `prsDescent` the sequence itself (the Lazard–Rioboo–Trager log arguments), and
the resultant fold lives in `DeepWiki/CAlgebra/Resultant/Euclidean`. The gcd universal
property is proven here once, generically over any policy whose extracted constants are
invariantly nonzero — over a field each strip is then a unit `C β`. -/

namespace DeepWiki.CAlgebra

universe u v

namespace DensePoly

section Kernel

variable {S : Type u} [CommRing S] [DecidableEq S]

/-! ### The kernel -/

/-- **The descent kernel** — one recursion for the whole engine: pseudo-divide the pair,
strip the remainder through the state-threaded `clean` policy, recurse on
`(divisor, cleaned)`, recording each step's divisor and extracted constant. Every
projection is a fold over this trace: `resultantDescent` (the constant ledger),
`gcdDescent` (the last element), `prsDescent` (the sequence itself). `hsize` feeds
termination. -/
def descentTrace {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) : List (DensePoly S × S) :=
  if g.size = 0 then []
  else
    (g, (clean st f g (pseudoMod f g)).1) ::
      descentTrace clean hsize (clean st f g (pseudoMod f g)).2.2 g
        (clean st f g (pseudoMod f g)).2.1
  termination_by g.size
  decreasing_by
    rename_i hg0
    have h1 : (pseudoMod f g).size < g.size := pseudoMod_size_lt hg0 f
    have h2 := hsize st f g (pseudoMod f g)
    omega

/-- The kernel stops at an exhausted divisor. -/
theorem descentTrace_of_size_eq_zero {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) (hg0 : g.size = 0) :
    descentTrace clean hsize st f g = [] := by
  rw [descentTrace, if_pos hg0]

/-- One kernel step: record the divisor and the extracted constant, recurse on the cleaned
remainder. -/
theorem descentTrace_of_size_ne_zero {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) (hg0 : g.size ≠ 0) :
    descentTrace clean hsize st f g
      = (g, (clean st f g (pseudoMod f g)).1) ::
          descentTrace clean hsize (clean st f g (pseudoMod f g)).2.2 g
            (clean st f g (pseudoMod f g)).2.1 := by
  rw [descentTrace, if_neg hg0]

/-! ### The projections -/

/-- The sequence projection of the kernel: the cleaned pseudo-remainder sequence itself
from the second entry on — the Lazard–Rioboo–Trager log arguments are read off it. -/
def prsDescent {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) : List (DensePoly S) :=
  (descentTrace clean hsize st f g).map (·.1)

/-- The last divisor of a trace, seeded with the entry element. -/
def lastElem (f : DensePoly S) : List (DensePoly S × S) → DensePoly S
  | [] => f
  | (g, _) :: rest => lastElem g rest

/-- The gcd projection of the kernel: the last nonzero sequence element — no bound or
scalar bookkeeping, which the gcd (needed only up to a unit) never pays for. -/
def gcdDescent {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) : DensePoly S :=
  lastElem f (descentTrace clean hsize st f g)

/-- The gcd projection at an exhausted divisor. -/
theorem gcdDescent_of_size_eq_zero {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) (hg0 : g.size = 0) :
    gcdDescent clean hsize st f g = f := by
  rw [gcdDescent, descentTrace_of_size_eq_zero clean hsize st f g hg0, lastElem]

/-- The gcd projection advances along the kernel step. -/
theorem gcdDescent_of_size_ne_zero {σ : Type v}
    (clean : σ → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (st : σ) (f g : DensePoly S) (hg0 : g.size ≠ 0) :
    gcdDescent clean hsize st f g
      = gcdDescent clean hsize (clean st f g (pseudoMod f g)).2.2 g
          (clean st f g (pseudoMod f g)).2.1 := by
  rw [gcdDescent, gcdDescent, descentTrace_of_size_ne_zero clean hsize st f g hg0, lastElem]

end Kernel

/-! ### The gcd universal property, generically over unit-β policies -/

section GcdUniversal

variable {R : Type u} [Field R] [DecidableEq R]

/-- **The engine's gcd divides both entries**, for any clean policy whose extracted constant
is invariantly nonzero (each `C β` a unit, so pseudo-division steps preserve divisors up to
units); the invariant `I` must reconstruct the strip and persist into the recursive call. -/
theorem gcdDescent_dvd {σ : Type v}
    (clean : σ → DensePoly R → DensePoly R → DensePoly R → R × DensePoly R × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (I : σ → DensePoly R → DensePoly R → Prop)
    (hclean : ∀ st f g, g.size ≠ 0 → I st f g → (clean st f g (pseudoMod f g)).1 ≠ 0 ∧
      C (clean st f g (pseudoMod f g)).1 * (clean st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, g.size ≠ 0 → I st f g →
      I (clean st f g (pseudoMod f g)).2.2 g (clean st f g (pseudoMod f g)).2.1)
    (st : σ) (f g : DensePoly R) (hI : I st f g) :
    gcdDescent clean hsize st f g ∣ f ∧ gcdDescent clean hsize st f g ∣ g := by
  revert hI
  induction st, f, g using descentTrace.induct (clean := clean) (hsize := hsize) with
  | case1 st f g hg0 =>
      intro _
      rw [gcdDescent_of_size_eq_zero clean hsize st f g hg0]
      exact ⟨dvd_refl f, by rw [eq_zero_of_size_zero hg0]; exact dvd_zero f⟩
  | case2 st f g hg0 ih =>
      intro hI
      obtain ⟨hβ, hex⟩ := hclean st f g hg0 hI
      obtain ⟨ih₂, ihrem⟩ := ih (hstep st f g hg0 hI)
      rw [gcdDescent_of_size_ne_zero clean hsize st f g hg0]
      refine ⟨?_, ih₂⟩
      apply dvd_of_dvd_C_mul (pow_ne_zero (f.size + 1 - g.size) (leadingCoeff_ne_zero hg0))
      rw [← pseudoDivMod_spec hg0 f]
      have hcleaned : (clean st f g (pseudoMod f g)).2.1 ∣ pseudoMod f g := by
        conv_rhs => rw [← hex]
        exact dvd_mul_left _ _
      exact dvd_add (ih₂.mul_left _) (ihrem.trans hcleaned)

/-- **Any common divisor divides the engine's gcd**, under the same unit-β invariant (the
descent's strips are cancelled through their units). -/
theorem dvd_gcdDescent {σ : Type v}
    (clean : σ → DensePoly R → DensePoly R → DensePoly R → R × DensePoly R × σ)
    (hsize : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size)
    (I : σ → DensePoly R → DensePoly R → Prop)
    (hclean : ∀ st f g, g.size ≠ 0 → I st f g → (clean st f g (pseudoMod f g)).1 ≠ 0 ∧
      C (clean st f g (pseudoMod f g)).1 * (clean st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, g.size ≠ 0 → I st f g →
      I (clean st f g (pseudoMod f g)).2.2 g (clean st f g (pseudoMod f g)).2.1)
    {d : DensePoly R} (st : σ) (f g : DensePoly R) (hI : I st f g)
    (h₁ : d ∣ f) (h₂ : d ∣ g) : d ∣ gcdDescent clean hsize st f g := by
  revert hI h₁ h₂
  induction st, f, g using descentTrace.induct (clean := clean) (hsize := hsize) with
  | case1 st f g hg0 =>
      intro _ h₁ _
      rw [gcdDescent_of_size_eq_zero clean hsize st f g hg0]
      exact h₁
  | case2 st f g hg0 ih =>
      intro hI h₁ h₂
      obtain ⟨hβ, hex⟩ := hclean st f g hg0 hI
      rw [gcdDescent_of_size_ne_zero clean hsize st f g hg0]
      refine ih (hstep st f g hg0 hI) h₂ ?_
      have hrem : d ∣ pseudoMod f g := by
        rw [pseudoMod_eq_sub hg0]
        exact dvd_sub (h₁.mul_left _) (h₂.mul_left _)
      apply dvd_of_dvd_C_mul hβ
      rw [hex]
      exact hrem

end GcdUniversal

end DensePoly

end DeepWiki.CAlgebra
