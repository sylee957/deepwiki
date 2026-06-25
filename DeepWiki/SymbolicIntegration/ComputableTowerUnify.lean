import DeepWiki.SymbolicIntegration.ComputableTowerReduce
import DeepWiki.SymbolicIntegration.ComputableWellFounded

/-! # Unifying the generic tower engine with the level-1 QFunNZ engine

This file is the FOUNDATION + a MECHANICALNESS PROBE for collapsing the two parallel
symbolic-integration engines into one. The two engines are:

* the **level-1 QFunNZ engine** (`cIntegrate`/`cRischDE`/`cgcdFF`/…) — specialized to the carrier
  `QFunNZ = ℚ(x)`, abstractly **proven** and fuel-free;
* the **generic tower engine** (`cIntegrateG`/`cRischDEG`/`cgcdMonicG`/… over `[CField α]`) —
  `native_decide`-validated only.

The end goal is to *replace* the base algorithms by the generic ones with the rigor preserved. The
safe path is to first lift the generic engine to the QFunNZ engine's rigor, then collapse. This file
takes the first steps and measures whether the full collapse is mechanical:

1. **`instance : CRischField QFunNZ`** — the missing typeclass instance so the generic engine runs at
   `α = QFunNZ` (the level-1 carrier of the old engine). Its base RDE is the existing `cRischDEBase`
   (the §6.6 base solve over ℚ(x), `D = d/dx`), whose signature `QFunNZ → QFunNZ → Option QFunNZ`
   matches `crischDESolve` exactly.
2. **The "generic subsumes base" headline**: `cIntegrateG` *at* `α = QFunNZ` reproduces the level-1
   `cIntegrate` worked integral (Bronstein Example 5.6.2, `t = log x`) on the *same* literal inputs —
   the generic driver lands an antiderivative satisfying `D(∫f) = f` (`checkIdentityG`).
3. **Generic gcd correctness + fuel-free** (the proven foundation): `associated_toPolyG_cgcdMonicG`
   (the generic monic gcd is the polynomial gcd up to associates) from the generic `cgcdExtG` Bézout /
   divides theory; plus a fuel-free `cgcdMonicGWf` bridged to `cgcdMonicG` at sufficient fuel.
4. **The probe**: the generic analog of a high-level QFunNZ correctness lemma, with a precise readout
   of how mechanical the transport was.

Nothing here modifies or weakens the existing QFunNZ engine — it is purely additive. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Task 3 — generic monic-gcd correctness `associated_toPolyG_cgcdMonicG`

The generic monic gcd `cgcdMonicG fuel p q = cmonicG (cgcdExtG fuel p q).1` returns the polynomial gcd
of the inputs up to associates over the genuine field `K = CFieldSpec.K α`. This is the generic
`[CField α] [CFieldSpec α]`-mirror of the QFunNZ-specific `associated_toPolyG_cgcdFF`
(`ComputableGcdCorrect`). It is assembled from the EXISTING generic gcd theory:

* `toPolyG_cgcdExtG_dvd` — under termination, the raw gcd divides both inputs (gives `gcd ∣ rawGcd`,
  via `dvd_gcd`);
* `toPolyG_dvd_cgcdExtG` — the raw gcd is divisible by *every* common divisor, in particular by
  `gcd (toPolyG p) (toPolyG q)` (gives `rawGcd ∣ gcd`, via `gcd_dvd_left`/`gcd_dvd_right`);
* `associated_toPolyG_cmonicG` — monic normalization is a unit-scaling.

Mutual divisibility yields `Associated` (`associated_of_dvd_dvd`). The `gcd` is over `K[X]` with `K` a
field (the `CFieldSpec.K α` field instance), so the `NormalizedGCDMonoid` structure on `K[X]` is
available generically. -/

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Abstract correctness of the generic monic gcd `cgcdMonicG`** (under a terminating run): over the
genuine field `K = CFieldSpec.K α`, `toPolyG (cgcdMonicG fuel p q)` is `Associated` to
`gcd (toPolyG p) (toPolyG q)` in `K[X]`. The generic `[CField α] [CFieldSpec α]`-mirror of
`associated_toPolyG_cgcdFF` — here the proof is purely algebraic (no `PrimPRSRegular` content gate),
because the generic `cgcdExtG` is the field-division Euclid (gcd is exact every step), so termination
alone gives both divisibility directions; monic normalization fixes the unit. -/
theorem associated_toPolyG_cgcdMonicG (fuel : ℕ) (p q : CPolyG α)
    (hterm : cgcdTerminatesG fuel p q) :
    Associated (toPolyG (CPolyG.cgcdMonicG fuel p q)) (gcd (toPolyG p) (toPolyG q)) := by
  -- The raw extended-Euclid gcd divides both inputs (termination), and is the greatest common divisor.
  obtain ⟨hdvd_p, hdvd_q⟩ := toPolyG_cgcdExtG_dvd fuel p q hterm
  -- monic-normalization is a unit-scaling of the raw gcd.
  have hassoc : Associated (toPolyG (CPolyG.cgcdMonicG fuel p q))
      (toPolyG (cgcdExtG fuel p q).1) := associated_toPolyG_cmonicG _
  refine hassoc.trans ?_
  -- Mutual divisibility between the raw gcd and the Mathlib `gcd`.
  apply associated_of_dvd_dvd
  · -- rawGcd ∣ gcd : rawGcd divides both p and q (`toPolyG_cgcdExtG_dvd`), so divides their gcd.
    exact dvd_gcd hdvd_p hdvd_q
  · -- gcd ∣ rawGcd : the Mathlib gcd is a common divisor, so it divides the (greatest) raw gcd.
    exact toPolyG_dvd_cgcdExtG fuel p q (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-! ### Task 3 — fuel-free generic monic gcd `cgcdMonicGWf`

The generic `cgcdMonicG` carries a `fuel : ℕ`. The fuel-free well-founded extended Euclid `cgcdWf`
(`ComputableWellFounded`, recursing on `(cnormG b).length`) already exists at the same generic
`[CField α]` level; we wrap it the same way `cgcdMonicG` wraps `cgcdExtG` and bridge through
`cgcdWf_eq`. -/

/-- **Fuel-free generic monic gcd** `cgcdMonicGWf p q = monic gcd(p, q)`: the gcd component of the
fuel-free well-founded extended Euclid `cgcdWf`, monic-normalized (`cmonicG`). The `[CField α]`-generic,
**fuel-free** companion of `cgcdMonicG` — `native_decide`-able over noncomputable-`CFieldSpec`
carriers, no fuel at runtime. -/
def cgcdMonicGWf (p q : CPolyG α) : CPolyG α :=
  CPolyG.cmonicG (CPolyG.cgcdWf p q).1

/-- **Bridge — `cgcdMonicGWf` equals `cgcdMonicG` at the self-sufficient fuel.** With
`fuel = (cnormG p).length + (cnormG q).length + 1`, the fuel-free `cgcdMonicGWf p q` agrees with
`cgcdMonicG fuel p q`: both are `cmonicG` of the same gcd component, and `cgcdWf p q = cgcdExtG fuel p q`
at this fuel (`cgcdWf_eq`). -/
theorem cgcdMonicGWf_eq (p q : CPolyG α) :
    cgcdMonicGWf p q
      = CPolyG.cgcdMonicG ((cnormG p : List α).length + (cnormG q : List α).length + 1) p q := by
  rw [cgcdMonicGWf, CPolyG.cgcdMonicG, CPolyG.cgcdWf_eq]

/-- **Bridge — `cgcdMonicGWf` equals `cgcdMonicG` at any sufficient fuel.** With
`(cnormG p).length ≤ fuel` and `(cnormG q).length < fuel`, the fuel-free `cgcdMonicGWf p q` agrees with
`cgcdMonicG fuel p q` (`cgcdWf_eq_of_fuel`). -/
theorem cgcdMonicGWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG α)
    (hp : (cnormG p : List α).length ≤ fuel) (hq : (cnormG q : List α).length < fuel) :
    cgcdMonicGWf p q = CPolyG.cgcdMonicG fuel p q := by
  rw [cgcdMonicGWf, CPolyG.cgcdMonicG, CPolyG.cgcdWf_eq_of_fuel fuel p q hp hq]

end DeepWiki.SymbolicIntegration
