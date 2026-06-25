import DeepWiki.SymbolicIntegration.ComputableRischDECorrect
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect

/-! # Discharging the §6.4 `cSPDE` certificate `cSPDECleared` (Bronstein §6.4)

`ComputableRischDECorrect` proves the §6.4 `cSPDE` lifting `cSPDE_cleared_lifting` *gated on*
a per-level certificate predicate `cSPDECleared` — the exact-division witnesses
`(a/g)·g = a, …`, the nonzero-leading `a/g ≠ 0`, and the Bézout `bd·r + ad·z = cd` each SPDE peel
needs. This file **discharges** that certificate from the proven gcd machinery, leaving only
*transparent* per-level preconditions (`cgcdFF` associated to `gcd`, fuel bounds, the Euclidean
gcd termination `cgcdTerminatesG`, and `a ≠ 0`), bundled into a recursive input predicate
`CSPDEClearedInputs` mirroring `cSPDE`'s own recursion.

## The math

Each non-base SPDE level computes `g = cgcdFF fuel a b ~ gcd(a, b)`, the divided
`ad = a/g, bd = b/g, cd = c/g`, and the Bézout cofactors `(r, z) = cdiophantineG fuel bd ad cd`.

* **Exact divisions** `toPolyG ad · toPolyG g = toPolyG a` (and `b, c`): `toPolyG_cdivFF_exact`,
  whose divisibility hypothesis `toPolyG g ∣ toPolyG a` comes from `g ~ gcd(a, b)` (`gcd_dvd_left`)
  and `g ∣ c` is *free* from the `cdvdG fuel g c = true` branch condition the recursion already
  takes (the Euclidean identity `toPolyG_cdivmodG'` with a zero remainder).
* **`ad ≠ 0`**: from `ad·g = a` with `a ≠ 0`.
* **The Bézout certificate**: `toPolyG_cdiophantineG` needs the *internal* `cgcdExtG`-gcd
  `G = (cgcdExtG fuel bd ad).1` to be a **nonzero constant**. Key lemma `cgcdExtG_isUnit_of_divided`:
  `G ∣ ad, G ∣ bd` (`toPolyG_cgcdExtG_dvd` under termination), so `G·g ∣ a, b`, hence
  `G·g ∣ gcd(a, b) ~ g`; cancelling the nonzero `g` makes `G` a unit — a nonzero `C (lc G)`. This is
  exactly the coprimality `ad ⊥ bd` of the divided coefficients, the structure
  `toPolyG_cdiophantineG` certifies. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The internal `cgcdExtG`-gcd of the divided coefficients is a nonzero constant
The Bézout solve `cdiophantineG fuel bd ad cd` runs its own extended Euclidean `cgcdExtG fuel bd ad`;
its gcd `G` is a **unit** of `(RatFunc ℚ)[X]` because `ad, bd` are coprime (they are `a/g, b/g` for
`g = gcd(a, b)`). A unit is a nonzero constant `C (leadingCoeff)`, exactly the
`toPolyG_cdiophantineG` hypotheses. -/

/-- **The divided coefficients' Euclidean gcd is a unit**: if `g ~ gcd(a, b)` (`g ≠ 0`) with
`toPolyG ad · toPolyG g = toPolyG a`, `toPolyG bd · toPolyG g = toPolyG b` the exact divisions, then
under the Euclidean termination `cgcdTerminatesG fuel bd ad` the gcd `G = (cgcdExtG fuel bd ad).1` is
a unit of `(RatFunc ℚ)[X]`. Common divisors `G ∣ ad, G ∣ bd` give `G·g ∣ a, b`, so `G·g ∣ gcd(a, b)`;
since `gcd(a, b) ~ g` and `g ≠ 0`, cancelling `g` makes `G ∣ 1`. -/
theorem cgcdExtG_isUnit_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    IsUnit (toPolyG (cgcdExtG fuel bd ad).1) := by
  -- `G` divides both `bd` and `ad`
  obtain ⟨hGbd, hGad⟩ := toPolyG_cgcdExtG_dvd fuel bd ad hterm
  set G := toPolyG (cgcdExtG fuel bd ad).1 with hGdef
  -- `G·g ∣ a` and `G·g ∣ b`
  have hGg_a : G * toPolyG g ∣ toPolyG a := by
    rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPolyG g ∣ toPolyG b := by
    rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  -- `G·g ∣ gcd(a, b) ~ g`, so `G·g ∣ g`
  have hGg_gcd : G * toPolyG g ∣ gcd (toPolyG a) (toPolyG b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPolyG g ∣ toPolyG g := hGg_gcd.trans hgassoc.symm.dvd
  -- cancel the nonzero `g`: `g = G·g·k = g·(G·k)` ⇒ `1 = G·k` ⇒ `G ∣ 1`
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPolyG g * 1 = toPolyG g * (G * k) := by
    rw [mul_one]; nth_rewrite 1 [hk]; ring
  -- `1 = G·k`, so `G ∣ 1`, hence `G` is a unit
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- **The divided coefficients' Euclidean gcd is the constant `C (leadingCoeff)`**: the unit gcd
`G = (cgcdExtG fuel bd ad).1` of `cgcdExtG_isUnit_of_divided` has degree `0`, so
`toPolyG G = C (toK (cleadG G))`. The first `toPolyG_cdiophantineG` hypothesis. -/
theorem toPolyG_cgcdExtG_eq_C_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    toPolyG (cgcdExtG fuel bd ad).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1)) := by
  have hunit := cgcdExtG_isUnit_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hnd : (toPolyG (cgcdExtG fuel bd ad).1).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
  exact Polynomial.eq_C_of_natDegree_eq_zero hnd

/-- **The divided coefficients' Euclidean gcd has nonzero leading coefficient**: a unit is nonzero,
so `toK (cleadG G) ≠ 0`. The second `toPolyG_cdiophantineG` hypothesis. -/
theorem toK_cleadG_cgcdExtG_ne_zero_of_divided (fuel : ℕ) (a b ad bd g : CPolyG QFunNZ)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1) ≠ 0 := by
  have hunit := cgcdExtG_isUnit_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  rw [toK_cleadG_eq_leadingCoeff]
  exact Polynomial.leadingCoeff_ne_zero.mpr hunit.ne_zero

/-! ### Divisibility from the `cdvdG` branch and the exact-division witnesses
The recursion already branches on `cdvdG fuel g c = true`; `dvd_of_cdvdG` reads that as the honest
`toPolyG g ∣ toPolyG c` (zero remainder + the Euclidean identity). The three exact-division witnesses
the certificate needs then come from `toPolyG_cdivFF_exact` under the divisibilities from `g ~ gcd`
(for `a, b`) and the branch (for `c`). -/

/-- **`cdvdG = true` reads as honest divisibility**: `cdvdG fuel g c = true` and `cnormG g ≠ []` give
`toPolyG g ∣ toPolyG c` (the zero remainder in the Euclidean identity `c = quo·g + rem`). -/
theorem dvd_of_cdvdG {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (g c : CPolyG α)
    (hg0 : cnormG g ≠ []) (hdvd : cdvdG fuel g c = true) :
    toPolyG g ∣ toPolyG c := by
  have hrem0 : toPolyG (cmodG fuel c g) = 0 := (cdvdG_iff fuel g c).mp hdvd
  have hid := toPolyG_cdivmodG' fuel c g hg0
  rw [show (cdivmodG fuel c g).2 = cmodG fuel c g from rfl, hrem0, add_zero] at hid
  rw [hid]
  exact Dvd.intro_left _ rfl

/-- **The `a`-exact-division witness** `toPolyG (cdivFF fuel a g) · toPolyG g = toPolyG a` from
`g ~ gcd(a, b)` (`g ∣ a`), `g ≠ 0`, and the fuel bound. The first `cSPDECleared` clause. -/
theorem cdivFF_a_exact_of_gcd (fuel : ℕ) (a b g : CPolyG QFunNZ)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG a : List QFunNZ).length ≤ fuel)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivFF fuel a g) * toPolyG g = toPolyG a := by
  have hgdvd : toPolyG g ∣ toPolyG a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact (toPolyG_cdivFF_exact fuel a g hg0 hfuel hgdvd).symm

/-- **The `b`-exact-division witness** `toPolyG (cdivFF fuel b g) · toPolyG g = toPolyG b` from
`g ~ gcd(a, b)` (`g ∣ b`). The second `cSPDECleared` clause. -/
theorem cdivFF_b_exact_of_gcd (fuel : ℕ) (a b g : CPolyG QFunNZ)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG b : List QFunNZ).length ≤ fuel)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivFF fuel b g) * toPolyG g = toPolyG b := by
  have hgdvd : toPolyG g ∣ toPolyG b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact (toPolyG_cdivFF_exact fuel b g hg0 hfuel hgdvd).symm

/-- **The `c`-exact-division witness** `toPolyG (cdivFF fuel c g) · toPolyG g = toPolyG c` from the
`cdvdG fuel g c = true` branch (`g ∣ c`). The third `cSPDECleared` clause. -/
theorem cdivFF_c_exact_of_cdvdG (fuel : ℕ) (c g : CPolyG QFunNZ)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG c : List QFunNZ).length ≤ fuel)
    (hdvd : cdvdG fuel g c = true) :
    toPolyG (cdivFF fuel c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdG fuel g c hg0 hdvd
  exact (toPolyG_cdivFF_exact fuel c g hg0 hfuel hgdvd).symm

/-! ### The transparent input predicate `CSPDEClearedInputs` and the `cSPDECleared` discharge
`CSPDEClearedInputs` mirrors `cSPDE`/`cSPDECleared`'s recursion but bundles only *transparent*
per-level facts: each `cgcdFF fuel a b` is `Associated` to `gcd` (the §3.5 headline, gated on
`PrimPRSNodeRegular`); `g ≠ 0`; the fuel bounds the three exact divisions; `a ≠ 0`; and in the
recursion branch the Euclidean termination `cgcdTerminatesG fuel bd ad` so the Bézout gcd is a
constant — recursing on the reduced equation. `cSPDECleared_of_inputs` discharges the full
`cSPDECleared` from it by fuel induction: each exact-division clause via `cdivFF_*_exact`, the
nonzero-`ad` clause via `ad·g = a ≠ 0`, and the Bézout clause via `toPolyG_cdiophantineG` with the
constant-gcd hypotheses supplied by `toPolyG_cgcdExtG_eq_C_of_divided` /
`toK_cleadG_cgcdExtG_ne_zero_of_divided`. -/

/-- **Transparent per-level input predicate for the `cSPDECleared` discharge**, mirroring `cSPDE`'s
recursion. At each non-base level (`n ≥ 0`, `cdvdG fuel g c`), with `g = cgcdFF fuel a b`,
`ad = a/g`, `bd = b/g`, `cd = c/g`: the gcd is nonzero (`cnormG g ≠ []`) and `Associated` to
`gcd(toPolyG a, toPolyG b)`, the fuel bounds each exact division (`(cnormG a).length ≤ fuel`, …), and
`a ≠ 0`. In the recursion branch (`cdegG ad ≠ 0`) additionally the Euclidean termination
`cgcdTerminatesG fuel bd ad` (so the Bézout gcd is constant) and `CSPDEClearedInputs` on the reduced
equation. Each clause is a transparent degree/fuel/termination fact a real `cSPDE` run satisfies. -/
def CSPDEClearedInputs (Dt : CPolyG QFunNZ) : ℕ → (a b c : CPolyG QFunNZ) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := cgcdFF fuel a b
      if cdvdG fuel g c then
        let ad := cdivFF fuel a g
        let bd := cdivFF fuel b g
        (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
          ∧ ((cnormG a : List QFunNZ).length ≤ fuel)
          ∧ ((cnormG b : List QFunNZ).length ≤ fuel)
          ∧ ((cnormG c : List QFunNZ).length ≤ fuel)
          ∧ (cnormG a ≠ [])
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad (cdivFF fuel c g)
               cgcdTerminatesG fuel bd ad
                 ∧ CSPDEClearedInputs Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

/-- **`cSPDECleared` discharged from transparent inputs**: `CSPDEClearedInputs Dt fuel a b c n`
implies the per-level certificate `cSPDECleared Dt fuel a b c n`. By fuel induction mirroring both
recursions: the three exact-division witnesses come from `cdivFF_a/b/c_exact_*`, the nonzero-`ad`
clause from `ad·g = a` with `a ≠ 0`, and (recursion branch) the Bézout clause from
`toPolyG_cdiophantineG` with the divided-coefficient gcd shown constant by
`toPolyG_cgcdExtG_eq_C_of_divided`, recursing through the IH on the reduced equation. This turns the
§6.4 `cSPDE_cleared_lifting` gate into transparent degree/fuel/termination preconditions. -/
theorem cSPDECleared_of_inputs (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ),
      CSPDEClearedInputs Dt fuel a b c n → cSPDECleared Dt fuel a b c n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n _
    rw [cSPDECleared]; trivial
  | succ fuel ih =>
    intro a b c n hin
    rw [cSPDECleared]
    rw [CSPDEClearedInputs] at hin
    by_cases hn : n < 0
    · rw [if_pos hn]; trivial
    · rw [if_neg hn] at hin ⊢
      set g := cgcdFF fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hin ⊢
        set ad := cdivFF fuel a g with had
        set bd := cdivFF fuel b g with hbd
        obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrest⟩ := hin
        -- the three exact-division witnesses
        have hdiva : toPolyG ad * toPolyG g = toPolyG a :=
          cdivFF_a_exact_of_gcd fuel a b g hg0 hfa hgassoc
        have hdivb : toPolyG bd * toPolyG g = toPolyG b :=
          cdivFF_b_exact_of_gcd fuel a b g hg0 hfb hgassoc
        have hdivc : toPolyG (cdivFF fuel c g) * toPolyG g = toPolyG c :=
          cdivFF_c_exact_of_cdvdG fuel c g hg0 hfc hdvd
        -- `a ≠ 0`, so `ad ≠ 0` (since `ad·g = a`)
        have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
        have hadne : toPolyG ad ≠ 0 := by
          intro h; apply hane; rw [← hdiva, h, zero_mul]
        have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
        refine ⟨hdiva, hdivb, hdivc, hadne, ?_⟩
        by_cases hdeg : cdegG ad = 0
        · rw [if_pos hdeg] at hrest ⊢; trivial
        · rw [if_neg hdeg] at hrest ⊢
          obtain ⟨hterm, hrec⟩ := hrest
          -- the Bézout certificate from `toPolyG_cdiophantineG` (divided gcd is a nonzero constant)
          have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
          have hgC := toPolyG_cgcdExtG_eq_C_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
          have hgCne := toK_cleadG_cgcdExtG_ne_zero_of_divided fuel a b ad bd g hgne hgassoc hdiva
            hdivb hterm
          have hbez := toPolyG_cdiophantineG fuel bd ad (cdivFF fuel c g) hadnil hgC hgCne
          refine ⟨?_, ih ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG (cdiophantineG fuel bd ad (cdivFF fuel c g)).2
              (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivFF fuel c g)).1))
            (n - (cdegG ad : ℤ)) hrec⟩
          -- `bd·r + ad·z = cd` (commuted from `r·bd + z·ad = cd`)
          linear_combination hbez
      · rw [if_neg (by simpa using hdvd : ¬ cdvdG fuel g c = true)] at hin ⊢; trivial

-- `CSPDEClearedInputs` discharges the per-level certificate `cSPDECleared`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (hin : CSPDEClearedInputs Dt fuel a b c n) : cSPDECleared Dt fuel a b c n :=
  cSPDECleared_of_inputs Dt fuel a b c n hin

/-! ### The re-gated §6.4 headlines — `cSPDE` lifting under transparent inputs only
Composing `cSPDECleared_of_inputs` into the §6.4 lifting (`cSPDE_cleared_lifting`) and the §6.4-§6.5
composition (`cSPDE_polyRischDENoCancel_cleared`) replaces their abstract `cSPDECleared` gate with the
transparent `CSPDEClearedInputs` — the §6.4 SPDE spine now rests only on degree/fuel/termination
preconditions (the §3.5/cgcdFF-headline shape), no per-level exact-division/Bézout assumptions. -/

/-- **The §6.4 `cSPDE` cleared lifting under transparent inputs**: if `cSPDE Dt fuel a b c n =
some (b̄, c̄, m, α, β)` and the transparent `CSPDEClearedInputs Dt fuel a b c n` holds, then for every
`h` solving the reduced `D(h) + b̄·h = c̄`, the reconstruction `q = α·h + β` solves the original
`a·D(q) + b·q = c` over `(RatFunc ℚ)[X]` (`D = implicitDeriv (toPolyG Dt)`). `cSPDE_cleared_lifting`
with its `cSPDECleared` gate discharged by `cSPDECleared_of_inputs`. -/
theorem cSPDE_cleared_lifting_of_inputs (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ)
    (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel a b c n) (h : CPolyG QFunNZ)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
        + toPolyG b * toPolyG (caddG (cmulG α h) β)
      = toPolyG c :=
  cSPDE_cleared_lifting Dt fuel a b c n bbar cbar m α β hspde
    (cSPDECleared_of_inputs Dt fuel a b c n hin) h hh

-- The §6.4 lifting under transparent inputs only: reduced solution lifts to the original equation.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel a b c n) (h : CPolyG QFunNZ)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
        + toPolyG b * toPolyG (caddG (cmulG α h) β)
      = toPolyG c :=
  cSPDE_cleared_lifting_of_inputs Dt fuel a b c n bbar cbar m α β hspde hin h hh

/-- **The §6.4-§6.5 polynomial-stage spine under transparent inputs**: if `cSPDE Dt fuel a b c n =
some (b̄, c̄, m, α, β)` (under transparent `CSPDEClearedInputs`) and `cPolyRischDENoCancel Dt fuel b̄
c̄ m = some v`, then `q = α·v + β` solves the original `a·D(q) + b·q = c`. The `cSPDE →
cPolyRischDENoCancel` composition with the §6.4 certificate gate replaced by transparent
degree/fuel/termination preconditions. Axiom-clean (no `native_decide`). -/
theorem cSPDE_polyRischDENoCancel_cleared_of_inputs (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (a b c : CPolyG QFunNZ) (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel a b c n)
    (hpoly : cPolyRischDENoCancel Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α v) β))
        + toPolyG b * toPolyG (caddG (cmulG α v) β)
      = toPolyG c :=
  cSPDE_polyRischDENoCancel_cleared Dt fuel a b c n bbar cbar m α β v hspde
    (cSPDECleared_of_inputs Dt fuel a b c n hin) hpoly

-- The §6.4-§6.5 spine under transparent inputs: `q = α·v + β` solves `a·D(q)+b·q=c` (cleared).
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel a b c n)
    (hpoly : cPolyRischDENoCancel Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α v) β))
        + toPolyG b * toPolyG (caddG (cmulG α v) β)
      = toPolyG c :=
  cSPDE_polyRischDENoCancel_cleared_of_inputs Dt fuel a b c n bbar cbar m α β v hspde hin hpoly

#print axioms cgcdExtG_isUnit_of_divided
#print axioms dvd_of_cdvdG
#print axioms cdivFF_a_exact_of_gcd
#print axioms cSPDECleared_of_inputs
#print axioms cSPDE_cleared_lifting_of_inputs
#print axioms cSPDE_polyRischDENoCancel_cleared_of_inputs

end DeepWiki.SymbolicIntegration
