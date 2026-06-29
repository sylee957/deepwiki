import DeepWiki.SymbolicIntegration.ComputableFieldGcd

/-! # Fuel-free (well-founded) generic Euclidean division and gcd

The engine ops `cdivmodG`/`cmodG`/`cgcdExtG` (`GenericPolyEngine`) take an explicit `fuel : ℕ`
and need a fuel-sufficiency side condition (`cgcdTerminatesG`) for their correctness. This file
gives **true fuel-free** companions, `cdivmodWf`/`cmodWf`/`cgcdWf`, by structural well-founded
recursion on the normalized list length (`decreasing_by` discharged from the proven one-step length
drops `stepG_length_lt`/`cmodWf_length_lt`). No fuel is computed or passed at runtime.

The ~200 existing correctness theorems are **transported, not re-proven**: each WF op equals its
fuel'd version at *any* sufficient fuel (`cdivmodWf_eq_of_fuel`/`cgcdWf_eq_of_fuel`), so the bound
appears only inside the bridge proof, never at runtime. The Euclidean identity, Bézout relation,
and gcd-divisibility then follow for the WF ops — the last **unconditionally** (a WF def always
terminates, so no `cgcdTerminatesG` hypothesis survives). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Step A — the leaf `cdivmodWf` (fuel-free Euclidean division)

`cdivmodWf p q` runs the same remainder loop as `cdivmodG`'s `fuel+1` branch, but recurses with no
fuel: termination is by `(cnormG p).length`, strictly dropped each step by `stepG_length_lt`. The
recursion-case shape mirrors `cdivmodG` exactly (normalize `p`, `q`; the leading-term match
`c = clead p / clead q`; the `csub`-`cmul`-`cshift` reduce step) so the fuel bridge is a clean
induction. -/

/-- **One reduce step** of generic Euclidean division: replace `p` by the leading-term-cancelled
`cnormG (p − (clead p/clead q)·xᵏ·q)`. The recursion driver of `cdivmodWf` (split out so the
well-founded recursion's decreasing argument is exactly `stepG_length_lt`). -/
def reduceStepWf (p q : CPolyG α) : CPolyG α :=
  cnormG (csubG (cnormG p)
    (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
      [CField.div (cleadG p) (cleadG q)]) (cnormG q)))

/-- **Fuel-free generic Euclidean division** of `CPolyG`s, `[CField α]`-only: `cdivmodWf p q =
(quotient, remainder)` with `p = quotient · q + remainder` over `K` (`q ≠ 0`). True well-founded
recursion on `(cnormG p).length` — **no fuel is computed or passed at runtime**. Termination is
structural: the reduce step `p' = reduceStepWf p q` is taken only when the *guard*
`(cnormG p').length < (cnormG p).length` holds, so the `decreasing_by` is the guard itself (no field
axiom needed, hence `[CField α]`-only and `native_decide`-able over noncomputable-`CFieldSpec`
carriers like `QFunNZG ℚ`). Over a genuine field the leading term always cancels (`stepG_length_lt`), so
the guard never fails and `cdivmodWf` agrees with `cdivmodG` (the bridge `cdivmodWf_eq_cdivmodG`). -/
def cdivmodWf (p q : CPolyG α) : CPolyG α × CPolyG α :=
  let pn := cnormG p
  let qn := cnormG q
  if cisZeroG qn then ([], [])
  else if (pn : List α).length < (qn : List α).length then ([], pn)
  else
    let c := CField.div (cleadG pn) (cleadG qn)
    let k := (pn : List α).length - (qn : List α).length
    let term := cshiftG k [c]
    let p' := reduceStepWf p q
    if (cnormG p' : List α).length < (cnormG p : List α).length then
      let (quo, rem) := cdivmodWf p' q
      (caddG term quo, rem)
    else (term, p')   -- unreachable over a genuine field (`stepG_length_lt`)
termination_by (cnormG p).length
decreasing_by assumption

/-- **Fuel-free remainder** of generic Euclidean division (`cdivmodWf`'s second component). -/
def cmodWf (p q : CPolyG α) : CPolyG α := (cdivmodWf p q).2

/-- **Fuel-free quotient** of generic Euclidean division (`cdivmodWf`'s first component). -/
def cdivWf (p q : CPolyG α) : CPolyG α := (cdivmodWf p q).1

/-! ### Step B — fuel-free extended Euclidean algorithm `cgcdWf`

`cgcdWf a b = (g, s, t)` with `s·a + t·b = g`, `g = gcd(a,b)` over `K`. True well-founded recursion on
`(cnormG b).length` — no fuel at runtime. Mirrors `cgcdExtG`'s body with `cdivWf`/`cmodWf`; the
recursion `cgcdWf b (cmodWf a b)` is taken only under the *structural guard*
`(cnormG (cmodWf a b)).length < (cnormG b).length`, so the def stays `[CField α]`-only. Over a genuine
field the remainder always shortens (`cmodG_length_lt`), so the guard never fails and `cgcdWf` agrees
with `cgcdExtG` (`cgcdWf_eq`). -/

/-- **Fuel-free extended Euclidean algorithm** on `CPolyG`s, `[CField α]`-only: `cgcdWf a b = (g, s, t)`
with the Bézout relation `s·a + t·b = g` and `g = gcd(a, b)` over `K`. Well-founded on
`(cnormG b).length` with the structural guard `(cnormG (cmodWf a b)).length < (cnormG b).length`; no
fuel at runtime. `native_decide`-able over noncomputable-`CFieldSpec` carriers (`QFunNZG ℚ`). -/
def cgcdWf (a b : CPolyG α) : CPolyG α × CPolyG α × CPolyG α :=
  if cisZeroG b then (cnormG a, [CField.one], [])
  else
    let q := cdivWf a b
    let r := cmodWf a b
    if (cnormG r : List α).length < (cnormG b : List α).length then
      let (g, s, t) := cgcdWf b r
      (g, t, csubG s (cmulG t q))
    else (cnormG a, [CField.one], [])   -- unreachable over a genuine field (`cmodG_length_lt`)
termination_by (cnormG b).length
decreasing_by assumption

/-- **Fuel-free gcd** (`cgcdWf`'s first component). -/
def cgcdWfGcd (a b : CPolyG α) : CPolyG α := (cgcdWf a b).1

/-! ### Bridge to the fuel'd `cdivmodG` and transported correctness

Over a genuine field (`[CFieldSpec α]`) the leading term always cancels, so `cdivmodWf`'s structural
guard never fails and the WF def coincides with `cdivmodG fuel` for **any** sufficient fuel
(`cdivmodWf_eq_of_fuel`). The bound `(cnormG p).length ≤ fuel` lives only in this proof; the runtime
`cdivmodWf` carries no fuel. The Euclidean identity is then transported from `toPolyG_cdivmodG`
unconditionally (`toPolyG_cdivmodWf`). -/

variable [CFieldSpec α]

/-- **The reduce step strictly shortens** the normalized list (over `[CFieldSpec α]`): discharges
`cdivmodWf`'s structural guard, so over a genuine field the reducing branch is always taken. -/
theorem reduceStepWf_length_lt (p q : CPolyG α) (hcz : cisZeroG (cnormG q) = false)
    (hlen : ¬ (cnormG p : List α).length < (cnormG q : List α).length) :
    (cnormG (reduceStepWf p q) : List α).length < (cnormG p : List α).length := by
  have hq : cnormG q ≠ [] := by
    simpa [cisZeroG, List.isEmpty_iff] using hcz
  have hle : (cnormG q : List α).length ≤ (cnormG p : List α).length := Nat.le_of_not_lt hlen
  have hpn : cnormG p ≠ [] := by
    intro h
    rw [h, List.length_nil, Nat.le_zero] at hle
    exact hq (List.length_eq_zero_iff.mp hle)
  have hstep := stepG_length_lt (cnormG p) (cnormG q)
    (by simpa using hpn) (by simpa using hq) (by simpa using hle)
  rw [reduceStepWf]
  simpa only [cnormG_idem, cleadG_cnormG] using hstep

omit [CFieldSpec α] in
/-- **`cdivmodG`'s reducing branch is driven by `reduceStepWf`**: in the non-base branch
`cdivmodG (fuel+1) p q = (term + (cdivmodG fuel (reduceStepWf p q) q).1, (cdivmodG fuel … ).2)`. The
recursive divisor is normalized to `cnormG q` by `cdivmodG`, re-folded with `cdivmodG_cnormG_right`. -/
theorem cdivmodG_succ_reducing (fuel : ℕ) (p q : CPolyG α) (hcz : cisZeroG (cnormG q) = false)
    (hlen : ¬ (cnormG p : List α).length < (cnormG q : List α).length) :
    cdivmodG (fuel + 1) p q =
      ((cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
            [CField.div (cleadG p) (cleadG q)]).caddG (cdivmodG fuel (reduceStepWf p q) q).1,
        (cdivmodG fuel (reduceStepWf p q) q).2) := by
  rw [cdivmodG]
  rw [if_neg (by rw [← cisZeroG_cnormG]; simpa using hcz), if_neg (by simpa using hlen)]
  simp only [cleadG_cnormG]
  rw [show cnormG (csubG (cnormG p)
        (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
          [CField.div (cleadG p) (cleadG q)]) (cnormG q))) = reduceStepWf p q from rfl,
    ← cdivmodG_cnormG_right]

/-- **Bridge — `cdivmodWf` equals `cdivmodG` at any sufficient fuel.** For `fuel ≥ (cnormG p).length`,
`cdivmodWf p q = cdivmodG fuel p q`. The fuel bound appears only here; `cdivmodWf` carries none. By
strong induction on `fuel`. -/
theorem cdivmodWf_eq_of_fuel : ∀ (fuel : ℕ) (p q : CPolyG α),
    (cnormG p : List α).length ≤ fuel → cdivmodWf p q = cdivmodG fuel p q := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
    intro p q hfuel
    rw [cdivmodWf.eq_def]
    by_cases hcz : cisZeroG (cnormG q) = true
    · -- divisor zero: both return `([], [])`
      simp only [hcz, if_true]
      cases fuel with
      | zero =>
        simp only [Nat.le_zero] at hfuel
        have hp0 : cnormG p = [] := List.length_eq_zero_iff.mp hfuel
        rw [cdivmodG]; rw [hp0]
      | succ fuel =>
        rw [cdivmodG]
        rw [if_pos (by rw [← cisZeroG_cnormG]; simpa using hcz)]
    · have hcz' : cisZeroG (cnormG q) = false := by simpa using hcz
      by_cases hlen : (cnormG p : List α).length < (cnormG q : List α).length
      · -- deg p < deg q: both return `([], cnormG p)`
        simp only [hcz', Bool.false_eq_true, if_false, hlen, if_true]
        cases fuel with
        | zero =>
          -- `cdivmodG 0 p q = ([], cnormG p)`
          rw [cdivmodG]
        | succ fuel =>
          rw [cdivmodG]
          rw [if_neg (by rw [← cisZeroG_cnormG]; simpa using hcz), if_pos (by simpa using hlen)]
      · -- reducing branch
        have hdec := reduceStepWf_length_lt p q hcz' hlen
        have hpne : cnormG p ≠ [] := by
          intro h; rw [h, List.length_nil] at hdec; exact absurd hdec (by simp)
        have hpos : 0 < (cnormG p : List α).length := List.length_pos_iff.mpr hpne
        obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hfuel' : (cnormG (reduceStepWf p q) : List α).length ≤ fuel' := by omega
        have ihstep := ihf fuel' (by omega) (reduceStepWf p q) q hfuel'
        rw [cdivmodG_succ_reducing fuel' p q hcz' hlen]
        simp only [hcz', Bool.false_eq_true, if_false, hlen, if_pos hdec, ihstep, cleadG_cnormG]

/-- **Bridge at the self-sufficient fuel**: `cdivmodWf p q = cdivmodG (cnormG p).length p q`. -/
theorem cdivmodWf_eq (p q : CPolyG α) :
    cdivmodWf p q = cdivmodG (cnormG p : List α).length p q :=
  cdivmodWf_eq_of_fuel _ p q le_rfl

/-- **Euclidean-division identity through `toPolyG`** for the fuel-free `cdivmodWf` (nonzero divisor,
**no fuel hypothesis**): `toPolyG p = toPolyG (quotient) · toPolyG q + toPolyG (remainder)`. -/
theorem toPolyG_cdivmodWf (p q : CPolyG α) (hq0 : cnormG q ≠ []) :
    toPolyG p
      = toPolyG (cdivmodWf p q).1 * toPolyG q + toPolyG (cdivmodWf p q).2 := by
  -- Direct well-founded induction on `cdivmodWf`'s own recursion: the four branches are the divisor-zero
  -- contradiction, the `deg p < deg q` base, the reduce step (IH on `p'`), and the unreachable branch.
  induction p using cdivmodWf.induct (q := q) with
  | case1 p =>
    -- divisor zero contradicts `cnormG q ≠ []`
    rename_i hcz
    have hcz' : cisZeroG (cnormG q) = true := hcz
    exact absurd (by simpa [cisZeroG, List.isEmpty_iff] using hcz') hq0
  | case2 p =>
    -- `deg p < deg q`: `cdivmodWf p q = ([], cnormG p)`
    rename_i hcz hlen
    have hcz' : cisZeroG (cnormG q) = false := by simpa using hcz
    have hlen' : (cnormG p : List α).length < (cnormG q : List α).length := hlen
    have hval : cdivmodWf p q = ([], cnormG p) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_pos hlen']
    rw [hval]
    simp [toPolyG_cnormG]
  | case3 p =>
    -- reducing branch: `p = term·q + p'`, then IH `p' = quo·q + rem`
    rename_i pn qn hcz hlen p' hdec quo rem hqr ih
    have hcz' : cisZeroG (cnormG q) = false := by simpa using hcz
    have hlen' : ¬ (cnormG p : List α).length < (cnormG q : List α).length := hlen
    set term := cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
      [CField.div (cleadG p) (cleadG q)] with hterm
    have hval : cdivmodWf p q = (caddG term quo, rem) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_neg hlen', if_pos hdec]
      simp only [cleadG_cnormG, hterm]
      rw [show (p.reduceStepWf q).cdivmodWf q = (quo, rem) from hqr]
    rw [hval]
    have hstep : toPolyG (reduceStepWf p q) = toPolyG p - toPolyG term * toPolyG q := by
      rw [reduceStepWf, toPolyG_cnormG, toPolyG_csubG, toPolyG_cnormG, toPolyG_cmulG,
        toPolyG_cnormG, hterm]
    have hih : toPolyG (reduceStepWf p q)
        = toPolyG quo * toPolyG q + toPolyG rem := by
      rw [ih, hqr]
    simp only [toPolyG_caddG]
    rw [hstep] at hih
    linear_combination hih
  | case4 p =>
    -- unreachable over a genuine field (`reduceStepWf_length_lt`)
    rename_i pn qn hcz hlen p' hdec
    have hcz' : cisZeroG (cnormG q) = false := by simpa using hcz
    have hlen' : ¬ (cnormG p : List α).length < (cnormG q : List α).length := hlen
    exact absurd (reduceStepWf_length_lt p q hcz' hlen') hdec

/-- **Remainder identity through `toPolyG`** for `cmodWf` (no fuel hypothesis). -/
theorem toPolyG_cmodWf (p q : CPolyG α) (hq0 : cnormG q ≠ []) :
    toPolyG p = toPolyG (cdivWf p q) * toPolyG q + toPolyG (cmodWf p q) := by
  rw [cdivWf, cmodWf]; exact toPolyG_cdivmodWf p q hq0

/-! ### Bridge of `cgcdWf` to the fuel'd `cgcdExtG`, and transported correctness

`cgcdWf_eq_of_fuel` is the gcd analogue of `cdivmodWf_eq_of_fuel`: over `[CFieldSpec α]` the remainder
descent always strictly shortens (`cmodG_length_lt`), so `cgcdWf`'s structural guard never fails and
`cgcdWf` coincides with `cgcdExtG fuel` whenever `fuel` covers the descent (`(cnormG a).length ≤ fuel`
and `(cnormG b).length < fuel`, the `cgcdTerminates_of_fuel` accounting). Bézout and gcd-divisibility
then transport **unconditionally** (`cgcdWf` always terminates: no `cgcdTerminatesG` survives). -/

/-- `cdivWf`/`cmodWf` agree with the fuel'd `cdivG`/`cmodG` at any sufficient fuel. -/
theorem cmodWf_eq_cmodG_succ (fuel : ℕ) (a b : CPolyG α)
    (hfuel : (cnormG a : List α).length ≤ fuel + 1) :
    cmodWf a b = cmodG (fuel + 1) a b := by
  rw [cmodWf, cmodG, cdivmodWf_eq_of_fuel (fuel + 1) a b hfuel]

/-- `cdivWf` agrees with the fuel'd `cdivG` (= `(cdivmodG …).1`) at any sufficient fuel. -/
theorem cdivWf_eq_cdivmodG_succ (fuel : ℕ) (a b : CPolyG α)
    (hfuel : (cnormG a : List α).length ≤ fuel + 1) :
    cdivWf a b = (cdivmodG (fuel + 1) a b).1 := by
  rw [cdivWf, cdivmodWf_eq_of_fuel (fuel + 1) a b hfuel]

/-- **The remainder strictly shortens** below `(cnormG b).length` for a nonzero divisor: discharges
`cgcdWf`'s structural guard, so over a genuine field the recursing branch is always taken. -/
theorem cmodWf_length_lt (a b : CPolyG α) (hb : cnormG b ≠ []) :
    (cnormG (cmodWf a b) : List α).length < (cnormG b : List α).length := by
  rw [cmodWf_eq_cmodG_succ ((cnormG a : List α).length) a b (by omega)]
  exact cmodG_length_lt _ a b hb (by omega)

/-- **Generic `cgcdExtG` descent terminates for sufficient fuel** (the generic analogue of
`cgcdTerminates_of_fuel`): if `fuel` bounds `(cnormG a).length` and *strictly* bounds
`(cnormG b).length`, the remainder descent reaches a zero remainder within `fuel`. Each step replaces
`(a, b)` by `(b, cmodG (fuel+1) a b)` and `cmodG_length_lt` shortens the remainder strictly below
`(cnormG b).length`, preserving the asymmetric strict bound. -/
theorem cgcdTerminatesG_of_fuel : ∀ (fuel : ℕ) (a b : CPolyG α),
    (cnormG a : List α).length ≤ fuel → (cnormG b : List α).length < fuel →
      cgcdTerminatesG fuel a b := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hb; omega
  | succ fuel ih =>
    intro a b ha hb
    rw [cgcdTerminatesG]
    by_cases hbz : cisZeroG b = true
    · exact Or.inl hbz
    · refine Or.inr ?_
      have hbne : cnormG b ≠ [] := by
        rw [cisZeroG] at hbz; simpa using List.isEmpty_eq_false_iff.mp (by simpa using hbz)
      have hlt : (cnormG (cmodG (fuel + 1) a b) : List α).length < (cnormG b : List α).length :=
        cmodG_length_lt (fuel + 1) a b hbne ha
      exact ih b (cmodG (fuel + 1) a b) (by omega) (by omega)

/-- **Bridge — `cgcdWf` equals `cgcdExtG` at any sufficient fuel.** With `(cnormG a).length ≤ fuel`
and `(cnormG b).length < fuel`, `cgcdWf a b = cgcdExtG fuel a b`. The bounds appear only here; `cgcdWf`
carries no fuel. By strong induction on `fuel`, preserving the asymmetric `< fuel`-on-`b` invariant
exactly as `cgcdTerminates_of_fuel`. -/
theorem cgcdWf_eq_of_fuel : ∀ (fuel : ℕ) (a b : CPolyG α),
    (cnormG a : List α).length ≤ fuel → (cnormG b : List α).length < fuel →
      cgcdWf a b = cgcdExtG fuel a b := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
    intro a b ha hb
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [cgcdWf.eq_def, cgcdExtG]
      by_cases hbz : cisZeroG b = true
      · simp only [hbz, if_true]
      · have hbz' : cisZeroG b = false := by simpa using hbz
        have hbne : cnormG b ≠ [] := by
          rw [cisZeroG] at hbz'; simpa using List.isEmpty_eq_false_iff.mp hbz'
        have hdec := cmodWf_length_lt a b hbne
        -- the divmod cofactor and remainder match the fuel'd versions
        have hmod : cmodWf a b = cmodG (fuel + 1) a b := cmodWf_eq_cmodG_succ fuel a b ha
        have hdiv : cdivWf a b = (cdivmodG (fuel + 1) a b).1 :=
          cdivWf_eq_cdivmodG_succ fuel a b ha
        -- recurse: new first slot ≤ fuel, new second slot < fuel
        have ha' : (cnormG b : List α).length ≤ fuel := by omega
        have hb' : (cnormG (cmodWf a b) : List α).length < fuel := by omega
        have ihstep := ihf fuel (by omega) b (cmodWf a b) ha' hb'
        rw [hmod] at ihstep hdec
        simp only [hbz', Bool.false_eq_true, if_false, hmod, if_pos hdec, hdiv, ihstep]

/-- **Bridge at the self-sufficient fuel**: `cgcdWf a b = cgcdExtG (max+1) a b` with
`max = (cnormG a).length + (cnormG b).length`. -/
theorem cgcdWf_eq (a b : CPolyG α) :
    cgcdWf a b
      = cgcdExtG ((cnormG a : List α).length + (cnormG b : List α).length + 1) a b :=
  cgcdWf_eq_of_fuel _ a b (by omega) (by omega)

/-- **Bézout identity through `toPolyG`** for the fuel-free `cgcdWf` (no fuel hypothesis): with
`(g, s, t) = cgcdWf a b`, `toPolyG s · toPolyG a + toPolyG t · toPolyG b = toPolyG g`. Proven by
**direct well-founded induction on `cgcdWf`'s own recursion** — the base branch is `Bézout 1·a + 0·b =
a` (`cisZeroG b`), the recursing branch substitutes the Euclidean identity `a = q·b + r` into the IH
`s·b + t·r = g`, and the unreachable branch is closed by `cmodWf_length_lt`. References no fuel symbol. -/
theorem toPolyG_cgcdWf (a b : CPolyG α) :
    toPolyG (cgcdWf a b).2.1 * toPolyG a + toPolyG (cgcdWf a b).2.2 * toPolyG b
      = toPolyG (cgcdWf a b).1 := by
  induction a, b using cgcdWf.induct with
  | case1 a b =>
    -- `cisZeroG b`: `cgcdWf a b = (cnormG a, [1], [])`, Bézout `1·a + 0·b = a`
    rename_i hcz
    have hb0 : toPolyG b = 0 := (cisZeroG_iff b).mp hcz
    have hval : cgcdWf a b = (cnormG a, [CField.one], []) := by
      rw [cgcdWf.eq_def, if_pos hcz]
    rw [hval]
    simp [toPolyG_cnormG, toPolyG_cons, CFieldSpec.toK_one, hb0]
  | case2 a b =>
    -- recursing branch: `cgcdWf a b = (g, t, csubG s (cmulG t q))` with `(g,s,t) = cgcdWf b r`,
    -- `r = cmodWf a b`, `q = cdivWf a b`. IH: `s·b + t·r = g`. Euclid: `a = q·b + r`.
    -- the `have rr := a.cmodWf b` let-binder is auto-introduced between `hcz` and `hdec`; recover all.
    rename_i hcz rr hdec g s t hgst ih
    have hbne : cnormG b ≠ [] := by
      intro h; rw [cisZeroG] at hcz; simp [h] at hcz
    have hval : cgcdWf a b = (g, t, csubG s (cmulG t (cdivWf a b))) := by
      rw [cgcdWf.eq_def, if_neg hcz, if_pos hdec]
      show (let (g, s, t) := cgcdWf b (cmodWf a b); (g, t, csubG s (cmulG t (cdivWf a b)))) = _
      rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst]
    have heuclid : toPolyG a = toPolyG (cdivWf a b) * toPolyG b + toPolyG (cmodWf a b) :=
      toPolyG_cmodWf a b hbne
    -- IH at the recursive pair `(b, cmodWf a b)`: `s·b + t·r = g`
    rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst] at ih
    rw [hval]
    rw [toPolyG_csubG, toPolyG_cmulG]
    simp only at ih
    linear_combination ih + toPolyG t * heuclid
  | case3 a b =>
    -- unreachable over a genuine field (`cmodWf_length_lt`)
    rename_i hcz rr hdec
    have hbne : cnormG b ≠ [] := by
      intro h; rw [cisZeroG] at hcz; simp [h] at hcz
    exact absurd (cmodWf_length_lt a b hbne) hdec

/-- **`cgcdWf`'s gcd is greatest among common divisors** (no fuel hypothesis): any `d` dividing both
`toPolyG a` and `toPolyG b` divides `toPolyG (cgcdWf a b).1`. Immediate from Bézout. -/
theorem toPolyG_dvd_cgcdWf {d : (CFieldSpec.K α)[X]} (a b : CPolyG α)
    (ha : d ∣ toPolyG a) (hb : d ∣ toPolyG b) :
    d ∣ toPolyG (cgcdWf a b).1 := by
  rw [← toPolyG_cgcdWf a b]
  exact dvd_add (ha.mul_left _) (hb.mul_left _)

/-- **`cgcdWf`'s gcd divides both inputs — UNCONDITIONALLY** (the WF def always terminates, so no
`cgcdTerminatesG` hypothesis is needed): `toPolyG (cgcdWf a b).1` divides `toPolyG a` and `toPolyG b`.
With `toPolyG_dvd_cgcdWf` and Bézout this characterizes `g` as an honest gcd in `K[X]`. Proven by
**direct well-founded induction on `cgcdWf`'s own recursion**: the base branch gives `g = cnormG a ∣ a`
(reflexive) and `g ∣ b = 0`; the recursing branch reads off `g ∣ b ∧ g ∣ r` from the IH and combines
them through the Euclidean identity `a = q·b + r` to get `g ∣ a`. The WF recursion always reaches the
true base, so divisibility needs **no fuel-termination hypothesis** — references no fuel symbol. -/
theorem toPolyG_cgcdWf_dvd (a b : CPolyG α) :
    toPolyG (cgcdWf a b).1 ∣ toPolyG a ∧ toPolyG (cgcdWf a b).1 ∣ toPolyG b := by
  induction a, b using cgcdWf.induct with
  | case1 a b =>
    -- `cisZeroG b`: `cgcdWf a b = (cnormG a, ...)`, so `g = cnormG a ∣ a` (refl) and `g ∣ b = 0`
    rename_i hcz
    have hb0 : toPolyG b = 0 := (cisZeroG_iff b).mp hcz
    have hval : (cgcdWf a b).1 = cnormG a := by rw [cgcdWf.eq_def, if_pos hcz]
    rw [hval, toPolyG_cnormG]
    exact ⟨dvd_refl _, by rw [hb0]; exact dvd_zero _⟩
  | case2 a b =>
    -- recursing branch: `(cgcdWf a b).1 = (cgcdWf b r).1 = g`, IH `g ∣ b ∧ g ∣ r`, Euclid `a = q·b + r`
    rename_i hcz rr hdec g s t hgst ih
    have hbne : cnormG b ≠ [] := by
      intro h; rw [cisZeroG] at hcz; simp [h] at hcz
    have hgfst : (cgcdWf a b).1 = g := by
      rw [cgcdWf.eq_def, if_neg hcz, if_pos hdec]
      show (let (g, s, t) := cgcdWf b (cmodWf a b); (g, t, csubG s (cmulG t (cdivWf a b)))).1 = g
      rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst]
    rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst] at ih
    simp only at ih
    obtain ⟨hgb, hgr⟩ := ih
    have heuclid : toPolyG a = toPolyG (cdivWf a b) * toPolyG b + toPolyG (cmodWf a b) :=
      toPolyG_cmodWf a b hbne
    rw [hgfst]
    refine ⟨?_, hgb⟩
    rw [heuclid]
    exact dvd_add (hgb.mul_left _) hgr
  | case3 a b =>
    -- unreachable over a genuine field (`cmodWf_length_lt`)
    rename_i hcz rr hdec
    have hbne : cnormG b ≠ [] := by
      intro h; rw [cisZeroG] at hcz; simp [h] at hcz
    exact absurd (cmodWf_length_lt a b hbne) hdec

/-! ### `native_decide` smoke tests — the WF def reduces in compiled code

`cdivmodWf` is `[CField α]`-only, so it reduces in native code; the well-founded structure carries no
fuel and no noncomputable bridge into the compiled body. -/

/-- `cdivmodWf` over `ℚ`: `(1 + x²) mod (1 + x) = 2`. -/
example : (CPolyG.cdivmodWf [(1 : ℚ), 0, 1] [(1 : ℚ), 1]).2 = [2] := by native_decide

/-- `cgcdWf` over `ℚ`: `gcd(x² − 1, x − 1)` is degree-1 (a `x − 1` associate, normalized length 2). -/
example :
    ((CPolyG.cgcdWf [(-1 : ℚ), 0, 1] [(-1 : ℚ), 1]).1 : List ℚ).length = 2 := by native_decide

/-- **Fuel-free divisibility test** `cdvdGWf q p = cisZeroG (cmodWf p q)`: the fuel-free companion of
`cdvdG`, deciding `q ∣ p` (remainder of `p` by `q` is zero) with the leaf fuel-free remainder `cmodWf`
(true well-founded recursion, no fuel at runtime). Generic over `[CField α]`. -/
def cdvdGWf (q p : CPolyG α) : Bool := cisZeroG (cmodWf p q)

/-- **`cdvdGWf` equals the fuel'd `cdvdG` at any sufficient fuel**: for `(cnormG p).length ≤ fuel`,
`cdvdGWf q p = cdvdG fuel q p`. Both test the zero-ness of the Euclidean remainder; the leaf bridge
`cdivmodWf_eq_of_fuel` supplies the agreement. -/
theorem cdvdGWf_eq_of_fuel (fuel : ℕ) (q p : CPolyG α)
    (hfuel : (cnormG p : List α).length ≤ fuel) :
    cdvdGWf q p = CPolyG.cdvdG fuel q p := by
  rw [cdvdGWf, CPolyG.cdvdG, cmodWf, cmodG, cdivmodWf_eq_of_fuel fuel p q hfuel]

/-- **`cdvdGWf` reads as remainder-zero — DIRECTLY** (no fuel hypothesis): `cdvdGWf q p = true ↔
toPolyG (cmodWf p q) = 0`. Immediate from the definition `cdvdGWf q p = cisZeroG (cmodWf p q)` and
`cisZeroG_iff`; the fuel-free remainder `cmodWf` carries the Euclidean identity `toPolyG_cmodWf`, so a
true `cdvdGWf q p` certifies `q ∣ p` in `K[X]`. The fuel-free analogue of `cdvdG_iff`, referencing no
fuel symbol. -/
theorem cdvdGWf_iff (q p : CPolyG α) :
    cdvdGWf q p = true ↔ toPolyG (cmodWf p q) = 0 := by
  rw [cdvdGWf, cisZeroG_iff]

/-- **A true `cdvdGWf q p` certifies polynomial divisibility** `toPolyG q ∣ toPolyG p` (no fuel
hypothesis, nonzero divisor `cnormG q ≠ []`): from `cdvdGWf_iff` the remainder `toPolyG (cmodWf p q) = 0`,
and the Euclidean identity `toPolyG_cmodWf` then makes `toPolyG p = toPolyG (cdivWf p q) · toPolyG q`. The
fuel-free divisibility certificate. -/
theorem dvd_of_cdvdGWf (q p : CPolyG α) (hq : cnormG q ≠ []) (h : cdvdGWf q p = true) :
    toPolyG q ∣ toPolyG p := by
  have hrem : toPolyG (cmodWf p q) = 0 := (cdvdGWf_iff q p).mp h
  have heuclid : toPolyG p = toPolyG (cdivWf p q) * toPolyG q + toPolyG (cmodWf p q) :=
    toPolyG_cmodWf p q hq
  rw [hrem, add_zero] at heuclid
  exact ⟨toPolyG (cdivWf p q), by rw [heuclid]; ring⟩

end CPolyG

end DeepWiki.SymbolicIntegration
