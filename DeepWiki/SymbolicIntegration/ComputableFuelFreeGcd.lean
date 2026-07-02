import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import Mathlib.RingTheory.Polynomial.Content

/-! # Fuel-free (well-founded) generic Euclidean division and gcd

The engine ops `cdivmodG`/`cmodG`/`cgcdExtG` (`GenericPolyEngine`) take an explicit `fuel : ℕ`
and need a fuel-sufficiency side condition (`cgcdTerminatesG`) for their correctness. This file
gives **true fuel-free** companions, `cdivmodWf`/`cmodWf`/`cgcdWf`/`cgcdMonicWf`, by structural
well-founded recursion on the normalized list length (`decreasing_by` discharged from the proven
one-step length drops `stepG_length_lt`/`cmodWf_length_lt`). No fuel is computed or passed at runtime.

The fuel-free correctness API is proved directly over the WF recursions, by well-founded induction on
each def's own recursion: Euclidean division, Bézout, and gcd-divisibility carry no fuel hypothesis and
reference no fuel'd symbol. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Step A — the leaf `cdivmodWf` (fuel-free Euclidean division)

`cdivmodWf p q` runs the same remainder loop as `cdivmodG`'s `fuel+1` branch, but recurses with no
fuel: termination is by `(cnormG p).length`, strictly dropped each step by `stepG_length_lt`. The
recursion-case shape mirrors `cdivmodG` exactly (normalize `p`, `q`; the leading-term match
`c = clead p / clead q`; the `csub`-`cmul`-`cshift` reduce step). -/

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
carriers like `QFunNZG ℚ`). Over a genuine field the leading term always cancels (`stepG_length_lt`). -/
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
field the remainder always shortens (`cmodWf_length_lt`). -/

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

/-- **Fuel-free generic monic gcd**: monic-normalize the gcd component of `cgcdWf`. -/
def cgcdMonicWf (p q : CPolyG α) : CPolyG α :=
  cmonicG (cgcdWf p q).1

/-! ### The reduce step strictly shortens

The per-step length drop that discharges `cdivmodWf`'s own structural termination guard. -/

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
      simp [reduceStepWf, hterm]
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

/-! ### Remainder shortening and direct gcd correctness

Over `[CFieldSpec α]`, the fuel-free remainder strictly shortens below a nonzero divisor. The Bézout and
gcd-divisibility theorems below are proved directly by well-founded induction on `cgcdWf`, so no
`cgcdTerminatesG` or fuel bound survives in the Wf API. -/

/-- **The remainder strictly shortens** below `(cnormG b).length` for a nonzero divisor: discharges
`cgcdWf`'s structural guard, so over a genuine field the recursing branch is always taken. Proven by
**direct well-founded induction on `cdivmodWf`'s own recursion** (mirroring `toPolyG_cdivmodWf`), no
fuel symbol referenced. -/
theorem cmodWf_length_lt (a b : CPolyG α) (hb : cnormG b ≠ []) :
    (cnormG (cmodWf a b) : List α).length < (cnormG b : List α).length := by
  rw [cmodWf]
  induction a using cdivmodWf.induct (q := b) with
  | case1 a =>
    rename_i hcz
    have hcz' : cisZeroG (cnormG b) = true := hcz
    exact absurd (by simpa [cisZeroG, List.isEmpty_iff] using hcz') hb
  | case2 a =>
    rename_i hcz hlen
    have hcz' : cisZeroG (cnormG b) = false := by simpa using hcz
    have hlen' : (cnormG a : List α).length < (cnormG b : List α).length := hlen
    have hval : cdivmodWf a b = ([], cnormG a) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_pos hlen']
    rw [hval, cnormG_idem]
    exact hlen'
  | case3 a =>
    rename_i pn qn hcz hlen a' hdec quo rem hqr ih
    have hcz' : cisZeroG (cnormG b) = false := by simpa using hcz
    have hlen' : ¬ (cnormG a : List α).length < (cnormG b : List α).length := hlen
    set term := cshiftG ((cnormG a : List α).length - (cnormG b : List α).length)
      [CField.div (cleadG a) (cleadG b)] with hterm
    have hval : cdivmodWf a b = (caddG term quo, rem) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_neg hlen', if_pos hdec]
      simp only [cleadG_cnormG, hterm]
      rw [show (a.reduceStepWf b).cdivmodWf b = (quo, rem) from hqr]
    rw [hval]
    rw [hqr] at ih
    exact ih
  | case4 a =>
    rename_i pn qn hcz hlen a' hdec
    have hcz' : cisZeroG (cnormG b) = false := by simpa using hcz
    have hlen' : ¬ (cnormG a : List α).length < (cnormG b : List α).length := hlen
    exact absurd (reduceStepWf_length_lt a b hcz' hlen') hdec

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

/-! ### Exact division through `toPolyG`

When a polynomial divides another through the semantic bridge `toPolyG`, Euclidean division has zero
remainder. -/

/-- **The fuel-free Euclidean remainder vanishes when the divisor divides the dividend** (through
`toPolyG`). -/
theorem toPolyG_cmodWf_eq_zero_of_dvd (p q : CPolyG α) (hq0 : cnormG q ≠ [])
    (hdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cmodWf p q) = 0 := by
  have hid : toPolyG p = toPolyG (cdivWf p q) * toPolyG q + toPolyG (cmodWf p q) :=
    toPolyG_cmodWf p q hq0
  have hdvdrem : toPolyG q ∣ toPolyG (cmodWf p q) := by
    have : toPolyG (cmodWf p q)
        = toPolyG p - toPolyG (cdivWf p q) * toPolyG q := by
      rw [hid]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have hlen : (cnormG (cmodWf p q) : List α).length < (cnormG q : List α).length :=
    cmodWf_length_lt p q hq0
  by_contra hne
  have hdeg : (toPolyG q).natDegree ≤ (toPolyG (cmodWf p q)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdrem hne
  have hrn : cnormG (cmodWf p q) ≠ [] := fun h => hne ((cnormG_eq_nil_iff _).mp h)
  rw [length_cnormG_of_ne _ hrn, length_cnormG_of_ne q hq0] at hlen
  omega

/-- **Fuel-free exact division through `toPolyG`**: if `toPolyG q ∣ toPolyG p`, then the fuel-free
Euclidean quotient times the divisor recovers the dividend. -/
theorem toPolyG_cdivWf_exact (p q : CPolyG α) (hq0 : cnormG q ≠ [])
    (hdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivWf p q) * toPolyG q = toPolyG p := by
  have hid : toPolyG p = toPolyG (cdivWf p q) * toPolyG q + toPolyG (cmodWf p q) :=
    toPolyG_cmodWf p q hq0
  have hrem0 : toPolyG (cmodWf p q) = 0 :=
    toPolyG_cmodWf_eq_zero_of_dvd p q hq0 hdvd
  rw [hid, hrem0, add_zero]

/-! ### The fuel-free monic gcd divides both inputs (through `toPolyG`) -/

/-- **The fuel-free monic gcd divides both inputs** (through `toPolyG`), with no termination or fuel
hypothesis. -/
theorem toPolyG_cgcdMonicWf_dvd (p q : CPolyG α) :
    toPolyG (cgcdMonicWf p q) ∣ toPolyG p ∧ toPolyG (cgcdMonicWf p q) ∣ toPolyG q := by
  obtain ⟨hp, hq⟩ := toPolyG_cgcdWf_dvd p q
  have hassoc : Associated (toPolyG (cgcdMonicWf p q)) (toPolyG (cgcdWf p q).1) := by
    rw [cgcdMonicWf]
    exact associated_toPolyG_cmonicG _
  exact ⟨hassoc.dvd.trans hp, hassoc.dvd.trans hq⟩

end CPolyG

open CPolyG

/-- **Abstract correctness of the fuel-free generic monic gcd `CPolyG.cgcdMonicWf`**: over the genuine
field `K = CFieldSpec.K α`, `toPolyG (CPolyG.cgcdMonicWf p q)` is associated to
`gcd (toPolyG p) (toPolyG q)` in `K[X]`. This is the fuel-free analogue of
`associated_toPolyG_cgcdExtG`, with no termination or fuel hypothesis. -/
theorem associated_toPolyG_cgcdMonicWf {α : Type*} [CField α] [CFieldSpec α] (p q : CPolyG α) :
    Associated (toPolyG (CPolyG.cgcdMonicWf p q)) (gcd (toPolyG p) (toPolyG q)) := by
  obtain ⟨hdvd_p, hdvd_q⟩ := CPolyG.toPolyG_cgcdWf_dvd p q
  have hassoc : Associated (toPolyG (CPolyG.cgcdMonicWf p q)) (toPolyG (CPolyG.cgcdWf p q).1) := by
    rw [CPolyG.cgcdMonicWf]
    exact associated_toPolyG_cmonicG _
  refine hassoc.trans ?_
  apply associated_of_dvd_dvd
  · exact dvd_gcd hdvd_p hdvd_q
  · exact CPolyG.toPolyG_dvd_cgcdWf p q (gcd_dvd_left _ _) (gcd_dvd_right _ _)

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

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

/-- **A false `cdvdGWf q p` refutes polynomial divisibility** `¬ toPolyG q ∣ toPolyG p` (no fuel
hypothesis, nonzero divisor `cnormG q ≠ []`). This is the fuel-free converse used by Wf valuation
sharpness: if semantic divisibility held, the fuel-free exact-remainder theorem would force
`cdvdGWf q p = true`. -/
theorem not_dvd_of_cdvdGWf_false (q p : CPolyG α) (hq : cnormG q ≠ [])
    (h : cdvdGWf q p = false) : ¬ toPolyG q ∣ toPolyG p := by
  intro hdvd
  have hrem : toPolyG (cmodWf p q) = 0 := toPolyG_cmodWf_eq_zero_of_dvd p q hq hdvd
  have htrue : cdvdGWf q p = true := (cdvdGWf_iff q p).mpr hrem
  rw [htrue] at h
  exact Bool.noConfusion h

end CPolyG

end DeepWiki.SymbolicIntegration
