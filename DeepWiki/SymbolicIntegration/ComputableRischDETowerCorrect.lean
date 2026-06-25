import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableRischDEPipelineCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Abstract correctness of the GENERIC tower Risch-DE oracle `cRischDEG` at the level-1 carrier ℚ(x)
The generic tower §6 oracle `cRischDEG` (`ComputableTowerRischDE`) assembles the Risch differential
equation pipeline `Dy + f·y = g` on the `[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic
ops — §6.2 normal/special denominators (`cRdeNormalDenominatorG`/`cRdeSpecialDenominatorG`), the §6.3
degree bound (`cRdeBoundDegreeG`), the §6.4 SPDE (`cSPDEG`), and the §6.5/§6.6 PolyRischDE dispatch
(`cPolyRischDEG`) — recursing into the base solve `CRischField.crischDESolve`. It is `native_decide`-validated
only (the level-2 `towerRdeLvl2_solves_*` headlines).

This file gives the generic RDE oracle the abstract cleared-identity `Dy + f·y = g` it lacked — at the
level-1 carrier `α = QFunNZ` the engine collapse instantiates, where `cgcdFFCore` reads through `toPolyG`
to the SAME gcd as `cgcdFF` up to associates (the nucleus `ComputableSplitFactorTowerCorrect` filled the
§3.5 piece; the §5 transport `ComputableIntegrateTowerCorrect` is the template).

**The route (mirroring the §5 transport).** The generic stages at `α = QFunNZ` differ from the QFunNZ
`cRischDE` stages only in the gcd (`cgcdFFCore` vs `cgcdFF`, inside the §6.2 denominator/§6.4 SPDE steps)
and `cdivG` vs `cdivFF` (definitionally equal, `cdivFF := cdivG`). The §6 cleared-identity machinery is
mostly **gcd-free**:

* The **§6.5 non-cancellation** loop (`cPolyRischDENoCancelG`) has the **identical body** to
  `cPolyRischDENoCancel` (no gcd: only `cdegG`/`cleadG`/`cmonomialDeriv`/`cshiftG`/`csub/mul/addG`), so its
  cleared identity transports **verbatim** (`cPolyRischDENoCancelG_cleared_identity`).
* The **§6.4 SPDE** (`cSPDEG`) differs from `cSPDE` only at `let g := cgcdFFCore …`; its lifting
  (`cSPDEG_cleared_lifting`) is the same `gcd`-peel induction gated on a per-level certificate
  `cSPDEGCleared`, and the certificate discharge `cSPDEGCleared_of_inputs` is where the gcd actually
  enters — bridged through the §5 nucleus `associated_toPolyG_cgcdFFCore_node` (the certificate's
  `Associated (toPolyG g) (gcd …)` clause), exactly as the §5 split-factor transport.
* The **§6.2 normal denominator** glue (`rdeNormalDenominator_glue`) is a commutative-ring `Derivation`
  identity — already engine-agnostic and **reused directly** from `ComputableRischDEPipelineCorrect`.

The deliverable:

* **`cPolyRischDENoCancelG_cleared_identity`** — the §6.5 non-cancellation cleared identity for the generic
  loop (verbatim transport).
* **`cSPDEGCleared` / `cSPDEG_cleared_lifting` / `CSPDEGClearedInputs` / `cSPDEGCleared_of_inputs`** — the
  §6.4 SPDE generic certificate, lifting, transparent inputs, and discharge (the `cgcdFF ⤳ cgcdFFCore`
  bridge enters only in the discharge).
* **`cSPDEG_polyRischDENoCancel_cleared_of_inputs`** — the §6.4+§6.5 polynomial-stage spine.
* **`cRdeNormalDenominatorG_cleared_lift`** — the §6.2 normal-denominator cleared lifting (generic).
* **`cRdeSpecialDenominatorG_primitive_eq`** — the §6.2 special denominator is the identity in the
  primitive regime.
* **★ `cRischDEG_rdeCleared`** — the generic RDE oracle's cleared identity `Dy + f·y = g`: in the primitive
  regime, `cRischDEG` returns a `(ynum, yden)` whose `y = ynum/yden` solves the cleared Risch-DE
  `gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(RatFunc ℚ)[X]`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §6.5 — the generic non-cancellation cleared identity `D(q) + b·q = c` (verbatim transport)

`cPolyRischDENoCancelG Dt fuel b c n` (`ComputableTowerRischDE`) has the **identical body** to
`cPolyRischDENoCancel` (`ComputableRischDE`): both peel `p = (lc(c)/lc(b))·tᵐ`, recurse on
`c' = c − D(p) − b·p`, glue `q ← p + (recursive q)` — no gcd anywhere (only
`cdegG`/`cleadG`/`cmonomialDeriv`/`cshiftG`/`csub/mul/addG`). So the QFunNZ proof
`cPolyRischDENoCancel_cleared_identity` transports **verbatim** (the only change is the function name). -/

/-- **`cPolyRischDENoCancelG` satisfies the cleared RDE identity `D(q) + b·q = c`** (abstract, ALL inputs)
over the field ℚ(x), whenever the generic non-cancellation solve **succeeds**. If
`cPolyRischDENoCancelG Dt fuel b c n = some q` then, with `D = cmonomialDeriv Dt` (`= implicitDeriv
(toPolyG Dt)` through `toPolyG`), `implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q =
toPolyG c` in `(RatFunc ℚ)[X]`. The generic mirror of `cPolyRischDENoCancel_cleared_identity`, transported
verbatim (the loop body is identical — `cPolyRischDENoCancelG` has no gcd). Proved by induction on `fuel`:
each pass peels `p = (lc(c)/lc(b))·tᵐ`, recurses on `c' = c − D(p) − b·p`, and the additivity of
`implicitDeriv` glues `D(p+q) + b·(p+q) = D(p) + b·p + (D(q) + b·q) = D(p) + b·p + c' = c`. -/
theorem cPolyRischDENoCancelG_cleared_identity (Dt b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ) (q : CPolyG QFunNZ),
      cPolyRischDENoCancelG Dt fuel b c n = some q →
        Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hq
    -- `cPolyRischDENoCancelG Dt 0 _ _ _ = none`, contradiction
    rw [cPolyRischDENoCancelG] at hq
    exact absurd hq (by simp)
  | succ fuel ih =>
    intro c n q hq
    rw [cPolyRischDENoCancelG] at hq
    by_cases hc : cisZeroG c = true
    · -- base case: `c = 0`, returns `[]`, so `D(0) + b·0 = 0 = c`
      rw [if_pos hc, Option.some.injEq] at hq
      subst hq
      have hc0 : toPolyG c = 0 := (cisZeroG_iff c).mp hc
      rw [toPolyG_nil, map_zero, mul_zero, add_zero, hc0]
    · -- recursion branch
      rw [if_neg hc] at hq
      set m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ) with hm
      by_cases hguard : n < 0 ∨ m < 0 ∨ m > n
      · rw [if_pos hguard] at hq
        exact absurd hq (by simp)
      · rw [if_neg hguard] at hq
        simp only at hq
        set coeff := CField.div (cleadG c) (cleadG b) with hcoeff
        set p := cshiftG m.toNat [coeff] with hp
        set c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p) with hc'
        -- destructure the recursive call
        rcases hrec : cPolyRischDENoCancelG Dt fuel b c' (m - 1) with _ | qrec
        · rw [hrec] at hq; exact absurd hq (by simp)
        · rw [hrec, Option.some.injEq] at hq
          -- the recursive identity on `c'`
          have ihrec := ih c' (m - 1) qrec hrec
          -- `q = p + qrec`
          subst hq
          rw [toPolyG_caddG, map_add, mul_add]
          -- expand `c' = c − D(p) − b·p` through `toPolyG`
          have hc'eq : toPolyG c' = toPolyG c
              - Differential.implicitDeriv (toPolyG Dt) (toPolyG p) - toPolyG b * toPolyG p := by
            rw [hc', toPolyG_csubG, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cmulG]
          rw [hc'eq] at ihrec
          -- glue: `D(p) + D(qrec) + (b·p + b·qrec) = D(p) + b·p + (D(qrec) + b·qrec) = c`
          linear_combination ihrec

-- The §6.5 generic non-cancellation cleared identity, restated. When `cPolyRischDENoCancelG Dt fuel b c n
-- = some q`, the output `q` solves `D(q) + b·q = c` over ℚ(x)[t].
example (Dt b c : CPolyG QFunNZ) (fuel : ℕ) (n : ℤ) (q : CPolyG QFunNZ)
    (hq : cPolyRischDENoCancelG Dt fuel b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c :=
  cPolyRischDENoCancelG_cleared_identity Dt b fuel c n q hq

#print axioms cPolyRischDENoCancelG_cleared_identity

/-! ### §6.4 — the generic SPDE per-level certificate `cSPDEGCleared`

`cSPDEG Dt fuel a b c n` (`ComputableTowerRischDE`) is the generic mirror of `cSPDE`: the same `gcd(a,b)`
peel, but `g = cgcdFFCore fuel a b` (vs `cgcdFF`) and the three divisions `cdivG` (vs `cdivFF`,
definitionally equal). We mirror the QFunNZ certificate `cSPDECleared` verbatim with `cgcdFF → cgcdFFCore`,
`cdivFF → cdivG`: the recursively-bundled `toPolyG`-level facts that the `gcd`-peel divisions are exact and
the Bézout solve is correct, matching `cSPDEG`'s own recursion. -/

/-- **Per-level certificate predicate for `cSPDEG`** `cSPDEGCleared Dt fuel a b c n`: the generic mirror of
`cSPDECleared`, with `g = cgcdFFCore fuel a b` and the divided coefficients `ad = a/g`, `bd = b/g`,
`cd = c/g` via `cdivG`. At each non-base level (`n ≥ 0`, `g ∣ c`, `deg(ad) > 0`) it asserts the three
exact-division witnesses `toPolyG ad·toPolyG g = toPolyG a` (and `b`, `c`), the nonzero-leading
`toPolyG ad ≠ 0`, and the Bézout `toPolyG bd·toPolyG r + toPolyG ad·toPolyG z = toPolyG cd`, then recurses
on the reduced equation. Designed so that `cSPDEG = some (…)` together with `cSPDEGCleared` discharges the
full lifting by induction. -/
def cSPDEGCleared (Dt : CPolyG QFunNZ) : ℕ → (a b c : CPolyG QFunNZ) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let ad := cdivG fuel a g
        let bd := cdivG fuel b g
        let cd := cdivG fuel c g
        -- the three exact-division witnesses (so `toPolyG` of divided · gcd = original)
        (toPolyG ad * toPolyG g = toPolyG a) ∧ (toPolyG bd * toPolyG g = toPolyG b)
          ∧ (toPolyG cd * toPolyG g = toPolyG c)
          -- `a` (hence the divided `ad`) is nonzero (the SPDE input invariant `a ≠ 0`)
          ∧ (toPolyG ad ≠ 0)
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad cd
               -- the Bézout certificate `bd·r + ad·z = cd`
               (toPolyG bd * toPolyG rz.1 + toPolyG ad * toPolyG rz.2 = toPolyG cd)
                 ∧ cSPDEGCleared Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

/-- **The full recursive `cSPDEG` cleared lifting**: under the certificate `cSPDEGCleared`, if
`cSPDEG Dt fuel a b c n = some (b̄, c̄, m, α, β)` then for every `h` solving the reduced
`D(h) + b̄·h = c̄` (`D = implicitDeriv (toPolyG Dt)`), the reconstruction `q = α·h + β` solves the
**original** `a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`. The generic mirror of `cSPDE_cleared_lifting`,
transported `cgcdFF → cgcdFFCore`/`cdivFF → cdivG` (the gcd is `set`-abstracted as `g` and only read
through the certificate, so the `gcd`-peel induction is otherwise identical — the helpers `spde_const_base`,
`cSPDE_peel_cleared` are engine-agnostic and reused directly). -/
theorem cSPDEG_cleared_lifting (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ)
      (α β : CPolyG QFunNZ),
      cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α, β) →
      cSPDEGCleared Dt fuel a b c n →
      ∀ h : CPolyG QFunNZ,
        Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h = toPolyG cbar →
        toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
            + toPolyG b * toPolyG (caddG (cmulG α h) β)
          = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n bbar cbar m α β hspde _ h _
    rw [cSPDEG] at hspde
    exact absurd hspde (by simp)
  | succ fuel ih =>
    intro a b c n bbar cbar m α β hspde hcert h hh
    rw [cSPDEG] at hspde
    by_cases hn : n < 0
    · -- base case `n < 0`: `c = 0` ⇒ `(b̄,c̄,m,α,β) = ([],[],0,[],[])`, `q = 0`, divided = original
      rw [if_pos hn] at hspde
      by_cases hc0 : cisZeroG c = true
      · rw [if_pos hc0, Option.some.injEq] at hspde
        simp only [Prod.mk.injEq] at hspde
        obtain ⟨_hbbar, _hcbar, _, hα, hβ⟩ := hspde
        -- `q = α·h + β = 0·h + 0 = 0`, and `c = 0`
        subst hα; subst hβ
        have hcc : toPolyG c = 0 := (cisZeroG_iff c).mp hc0
        rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, zero_mul, add_zero, map_zero, mul_zero,
          mul_zero, add_zero, hcc]
      · rw [if_neg hc0] at hspde
        exact absurd hspde (by simp)
    · -- recursion / constant-base
      rw [if_neg hn] at hspde
      -- unfold the certificate
      rw [cSPDEGCleared] at hcert
      simp only [if_neg hn] at hcert
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hspde hcert
        set ad := cdivG fuel a g with had
        set bd := cdivG fuel b g with hbd
        set cd := cdivG fuel c g with hcd
        obtain ⟨hdiva, hdivb, hdivc, hadne, hcertrest⟩ := hcert
        by_cases hdeg : cdegG ad = 0
        · -- constant-`a` base case: `cSPDEG` returns `(ainv·bd, ainv·cd, n, [1], [])`, `q = h`
          rw [if_pos hdeg, Option.some.injEq] at hspde
          simp only [Prod.mk.injEq] at hspde
          obtain ⟨hbbar, hcbar, _, hα, hβ⟩ := hspde
          -- `α = [1]`, `β = []`, so `q = 1·h + 0 = h`
          subst hα; subst hβ
          rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, add_zero]
          have hone : toPolyG ([CField.one] : CPolyG QFunNZ) = 1 := by
            rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
          rw [hone, one_mul]
          -- the constant scalar `a0 = lc(ad) = leadingCoeff(toPolyG ad) ≠ 0`
          set a0 : RatFunc ℚ := CFieldSpec.toK (cleadG ad) with ha0def
          have ha0ne : a0 ≠ 0 := by
            rw [ha0def, toK_cleadG_eq_leadingCoeff]
            exact Polynomial.leadingCoeff_ne_zero.mpr hadne
          -- `toPolyG ad = C a0` (degree 0 ⇒ constant polynomial)
          have hadC : toPolyG ad = Polynomial.C a0 := by
            have hnd : (toPolyG ad).natDegree = 0 := by rw [← cdegG_eq_natDegree, hdeg]
            rw [ha0def, toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
            conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
          -- read `hh` as the reduced equation `D(h) + (C a0⁻¹·bd)·h = C a0⁻¹·cd`
          rw [← hbbar, ← hcbar, toPolyG_cscaleG, toPolyG_cscaleG, CFieldSpec.toK_inv,
            ← ha0def] at hh
          -- the divided identity `ad·D(h) + bd·h = cd` from `spde_const_base`
          have hdivided : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
              + toPolyG bd * toPolyG h = toPolyG cd := by
            rw [hadC]
            exact spde_const_base (Differential.implicitDeriv (toPolyG Dt)) a0 (toPolyG bd) (toPolyG cd)
              (toPolyG h) ha0ne hh
          -- multiply by `toPolyG g`: `a·D(h) + b·h = g·(ad·D(h) + bd·h) = g·cd = c`
          rw [← hdiva, ← hdivb, ← hdivc]
          linear_combination toPolyG g * hdivided
        · -- recursion peel: `q = ad·h' + r`, `h'` from the recursive solve
          rw [if_neg hdeg] at hspde
          rw [if_neg hdeg] at hcertrest
          -- destructure the Bézout cofactors `(r, z) = cdiophantineG bd ad cd`
          rcases hrz : cdiophantineG fuel bd ad cd with ⟨r, z⟩
          rw [hrz] at hspde hcertrest
          simp only at hspde hcertrest
          obtain ⟨hbez', hcertrec⟩ := hcertrest
          rcases hrec : cSPDEG Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
            with _ | ⟨bbar', cbar', m', α', β'⟩
          · rw [hrec] at hspde; exact absurd hspde (by simp)
          · rw [hrec, Option.some.injEq] at hspde
            simp only [Prod.mk.injEq] at hspde
            obtain ⟨hbbar, hcbar, _hm, hα, hβ⟩ := hspde
            -- `α = ad·α'`, `β = ad·β' + r`, `bbar = bbar'`, `cbar = cbar'`
            rw [← hbbar] at hh; rw [← hcbar] at hh
            -- IH gives the recursive call's ORIGINAL equation
            --   `ad·D(h') + (bd + D(ad))·h' = z − D(r)`,  `h' = α'·h + β'`
            have hihrec := ih ad (caddG bd (cmonomialDeriv Dt ad))
              (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
              bbar' cbar' m' α' β' hrec hcertrec h hh
            -- expand `hihrec` into the `cSPDE_peel_cleared`-`hred` shape, with `h' = α'·h + β'`
            have hred : toPolyG ad
                  * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β'))
                + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad))
                    * toPolyG (caddG (cmulG α' h) β')
                = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r) := by
              simp only [toPolyG_caddG, toPolyG_cmonomialDeriv, toPolyG_csubG] at hihrec ⊢
              linear_combination hihrec
            subst hα; subst hβ
            -- divided peel identity from `cSPDE_peel_cleared` (reconstruction `ad·(α'·h + β') + r`)
            have hpeel := cSPDE_peel_cleared Dt ad bd cd r z (caddG (cmulG α' h) β') hbez' hred
            -- the goal's `q = (ad·α')·h + (ad·β' + r)` equals `ad·(α'·h+β') + r` as a polynomial
            have hqeq : toPolyG (caddG (cmulG (cmulG ad α') h) (caddG (cmulG ad β') r))
                = toPolyG (caddG (cmulG ad (caddG (cmulG α' h) β')) r) := by
              simp only [toPolyG_caddG, toPolyG_cmulG]; ring
            -- rewrite the goal's `q`-image to the peel shape, then multiply the peel by `g`
            rw [hqeq, ← hdiva, ← hdivb, ← hdivc]
            linear_combination toPolyG g * hpeel
      · rw [if_neg hdvd] at hspde
        exact absurd hspde (by simp)

-- Full recursive `cSPDEG` lifting: under `cSPDEGCleared`, a reduced solution lifts to the original eqn.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β : CPolyG QFunNZ)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hcert : cSPDEGCleared Dt fuel a b c n) (h : CPolyG QFunNZ)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
        + toPolyG b * toPolyG (caddG (cmulG α h) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting Dt fuel a b c n bbar cbar m α β hspde hcert h hh

#print axioms cSPDEG_cleared_lifting

/-! ### §6.4 — the transparent input predicate `CSPDEGClearedInputs` and the `cSPDEGCleared` discharge

`CSPDEGClearedInputs` mirrors `CSPDEClearedInputs` (`cgcdFF → cgcdFFCore`, `cdivFF → cdivG`): the
transparent per-level facts a real `cSPDEG` run satisfies — each `cgcdFFCore fuel a b` is `Associated` to
`gcd` (the §3.5 headline, here bundled directly as a clause), `g ≠ 0`, the fuel bounds, `a ≠ 0`, and (in
the recursion branch) the Euclidean termination `cgcdTerminatesG fuel bd ad`. `cSPDEGCleared_of_inputs`
discharges the certificate by fuel induction — verbatim from `cSPDECleared_of_inputs`, with the divided
exact-divisions via `cdivFF_*_exact_*` (`cdivFF := cdivG`), the Bézout via `toPolyG_cdiophantineG` with the
constant divided-gcd supplied by `toPolyG_cgcdExtG_eq_C_of_divided` (all of which take `g` abstractly, so
they are reused directly). The only difference from `CSPDEClearedInputs` is `g = cgcdFFCore`. -/

/-- **Transparent per-level input predicate for the `cSPDEGCleared` discharge**, mirroring `cSPDEG`'s
recursion. At each non-base level (`n ≥ 0`, `cdvdG fuel g c`), with `g = cgcdFFCore fuel a b`,
`ad = a/g`, `bd = b/g`: the gcd is nonzero (`cnormG g ≠ []`) and `Associated` to
`gcd(toPolyG a, toPolyG b)`, the fuel bounds each exact division, and `a ≠ 0`. In the recursion branch
(`cdegG ad ≠ 0`) additionally the Euclidean termination `cgcdTerminatesG fuel bd ad` and
`CSPDEGClearedInputs` on the reduced equation. The generic mirror of `CSPDEClearedInputs` (only
`g = cgcdFFCore`). -/
def CSPDEGClearedInputs (Dt : CPolyG QFunNZ) : ℕ → (a b c : CPolyG QFunNZ) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let ad := cdivG fuel a g
        let bd := cdivG fuel b g
        (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
          ∧ ((cnormG a : List QFunNZ).length ≤ fuel)
          ∧ ((cnormG b : List QFunNZ).length ≤ fuel)
          ∧ ((cnormG c : List QFunNZ).length ≤ fuel)
          ∧ (cnormG a ≠ [])
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad (cdivG fuel c g)
               cgcdTerminatesG fuel bd ad
                 ∧ CSPDEGClearedInputs Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

/-- **`cSPDEGCleared` discharged from transparent inputs**: `CSPDEGClearedInputs Dt fuel a b c n`
implies the per-level certificate `cSPDEGCleared Dt fuel a b c n`. By fuel induction mirroring
`cSPDECleared_of_inputs`: the three exact-division witnesses come from `cdivFF_a/b/c_exact_*` (with
`cdivFF := cdivG`), the nonzero-`ad` clause from `ad·g = a` with `a ≠ 0`, and (recursion branch) the
Bézout clause from `toPolyG_cdiophantineG` with the divided-coefficient gcd shown constant by
`toPolyG_cgcdExtG_eq_C_of_divided`. The supporting lemmas take `g` abstractly (with the `Associated` and
exact-division hypotheses), so the only change from `cSPDECleared_of_inputs` is `g = cgcdFFCore`. -/
theorem cSPDEGCleared_of_inputs (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ),
      CSPDEGClearedInputs Dt fuel a b c n → cSPDEGCleared Dt fuel a b c n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n _
    rw [cSPDEGCleared]; trivial
  | succ fuel ih =>
    intro a b c n hin
    rw [cSPDEGCleared]
    rw [CSPDEGClearedInputs] at hin
    by_cases hn : n < 0
    · rw [if_pos hn]; trivial
    · rw [if_neg hn] at hin ⊢
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hin ⊢
        set ad := cdivG fuel a g with had
        set bd := cdivG fuel b g with hbd
        obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrest⟩ := hin
        -- the three exact-division witnesses (`cdivFF := cdivG`, so the `cdivFF`-helpers apply)
        have hdiva : toPolyG ad * toPolyG g = toPolyG a :=
          cdivFF_a_exact_of_gcd fuel a b g hg0 hfa hgassoc
        have hdivb : toPolyG bd * toPolyG g = toPolyG b :=
          cdivFF_b_exact_of_gcd fuel a b g hg0 hfb hgassoc
        have hdivc : toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c :=
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
          have hbez := toPolyG_cdiophantineG fuel bd ad (cdivG fuel c g) hadnil hgC hgCne
          refine ⟨?_, ih ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
              (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivG fuel c g)).1))
            (n - (cdegG ad : ℤ)) hrec⟩
          -- `bd·r + ad·z = cd` (commuted from `r·bd + z·ad = cd`)
          linear_combination hbez
      · rw [if_neg (by simpa using hdvd : ¬ cdvdG fuel g c = true)] at hin ⊢; trivial

-- `CSPDEGClearedInputs` discharges the per-level certificate `cSPDEGCleared`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (hin : CSPDEGClearedInputs Dt fuel a b c n) : cSPDEGCleared Dt fuel a b c n :=
  cSPDEGCleared_of_inputs Dt fuel a b c n hin

#print axioms cSPDEGCleared_of_inputs

/-! ### §6.4-§6.5 — the generic polynomial-stage spine under transparent inputs

Composing `cSPDEGCleared_of_inputs` into the generic SPDE lifting and feeding the §6.5 generic
non-cancellation solution `v` (which satisfies `D(v) + b̄·v = c̄` by `cPolyRischDENoCancelG_cleared_identity`)
as the reduced solution `h` gives the polynomial-stage spine: under transparent inputs, the reconstruction
`q = α·v + β` solves the original `a·D(q) + b·q = c`. The generic mirror of
`cSPDE_polyRischDENoCancel_cleared_of_inputs`. -/

/-- **The generic §6.4 `cSPDEG` cleared lifting under transparent inputs**: if `cSPDEG Dt fuel a b c n =
some (b̄, c̄, m, α, β)` and the transparent `CSPDEGClearedInputs Dt fuel a b c n` holds, then for every `h`
solving the reduced `D(h) + b̄·h = c̄`, the reconstruction `q = α·h + β` solves the original
`a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`. `cSPDEG_cleared_lifting` with its `cSPDEGCleared` gate discharged
by `cSPDEGCleared_of_inputs`. The generic mirror of `cSPDE_cleared_lifting_of_inputs`. -/
theorem cSPDEG_cleared_lifting_of_inputs (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ)
    (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β : CPolyG QFunNZ)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEGClearedInputs Dt fuel a b c n) (h : CPolyG QFunNZ)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
        + toPolyG b * toPolyG (caddG (cmulG α h) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting Dt fuel a b c n bbar cbar m α β hspde
    (cSPDEGCleared_of_inputs Dt fuel a b c n hin) h hh

/-- **The generic §6.4-§6.5 polynomial-stage spine under transparent inputs**: if `cSPDEG Dt fuel a b c n =
some (b̄, c̄, m, α, β)` (under transparent `CSPDEGClearedInputs`) and `cPolyRischDENoCancelG Dt fuel b̄ c̄ m
= some v`, then `q = α·v + β` solves the original `a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`. The `cSPDEG →
cPolyRischDENoCancelG` composition with the §6.4 certificate replaced by transparent
degree/fuel/termination preconditions. Axiom-clean (no `native_decide`). The generic mirror of
`cSPDE_polyRischDENoCancel_cleared_of_inputs`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_of_inputs (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (a b c : CPolyG QFunNZ) (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEGClearedInputs Dt fuel a b c n)
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α v) β))
        + toPolyG b * toPolyG (caddG (cmulG α v) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting_of_inputs Dt fuel a b c n bbar cbar m α β hspde hin v
    (cPolyRischDENoCancelG_cleared_identity Dt bbar fuel cbar m v hpoly)

-- The generic §6.4-§6.5 spine under transparent inputs: `q = α·v + β` solves `a·D(q)+b·q=c` (cleared).
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hin : CSPDEGClearedInputs Dt fuel a b c n)
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α v) β))
        + toPolyG b * toPolyG (caddG (cmulG α v) β)
      = toPolyG c :=
  cSPDEG_polyRischDENoCancel_cleared_of_inputs Dt fuel a b c n bbar cbar m α β v hspde hin hpoly

#print axioms cSPDEG_polyRischDENoCancel_cleared_of_inputs

end DeepWiki.SymbolicIntegration
