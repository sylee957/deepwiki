import DeepWiki.NetworkCalculus.TM2Trace

/-!
# Connecting a Mathlib polytime Boolean verifier to `AcceptsWithin`

For a verifier `verify : α → Bool` realized by a Mathlib
`Turing.TM2ComputableInPolyTime ea Computability.encodeBool verify`, we bridge
"the verifier returns `true`" to "the verifier TM halts with the encoded `true`
output within its polynomial time bound" (`AcceptsWithin` of `TM2Trace`).

The genuine work is halt-uniqueness: `tm2Trace` is a deterministic function and
`traceFrom_halt` makes a halt configuration permanent, so the trace can reach a
halt configuration only once, at a unique step.  Combined with injectivity of
`haltList` on the output stack this pins the halting output uniquely, giving the
full `verify a = true ↔ AcceptsWithin …` equivalence.

Scope: this file covers ONLY the verifier ⟺ acceptance connection.  Deferred
(see the cookLevin development): the `IsInNP_TM` separable refinement, the
initialization-free certificate variant, plugging into
`tableauFormula_sat_iff_halt`, and the Cook and Levin discharge.
-/

open StateTransition Turing

namespace DeepWiki

section HaltUniqueness

variable {σ : Type*} {f : σ → Option σ} {c₀ : σ}

/-- A trace can hit a halt configuration (`f c = none`) at most once: two halt
hits of the deterministic trace agree. -/
theorem traceFrom_halt_unique {k₁ k₂ : ℕ} {c₁ c₂ : σ}
    (h₁ : traceFrom f c₀ k₁ = some c₁) (hc₁ : f c₁ = none)
    (h₂ : traceFrom f c₀ k₂ = some c₂) (hc₂ : f c₂ = none) :
    c₁ = c₂ := by
  -- Symmetric: from a halt at `i`, every later step is `none`, so the other halt
  -- step cannot exceed `i`.
  have key : ∀ {i j : ℕ} {a b : σ}, traceFrom f c₀ i = some a → f a = none →
      traceFrom f c₀ j = some b → j ≤ i := by
    intro i j a b hi ha hj
    rcases le_or_gt j i with hle | hlt
    · exact hle
    · -- `hlt : i < j` is `i + 1 ≤ j`, the hypothesis `traceFrom_none_of_le` needs.
      have : traceFrom f c₀ j = none :=
        traceFrom_none_of_le (traceFrom_halt hi ha) j hlt
      rw [hj] at this
      exact absurd this (Option.some_ne_none b)
  have le₁ : k₂ ≤ k₁ := key h₁ hc₁ h₂
  have le₂ : k₁ ≤ k₂ := key h₂ hc₂ h₁
  have : k₁ = k₂ := Nat.le_antisymm le₂ le₁
  subst this
  exact Option.some.inj (h₁.symm.trans h₂)

end HaltUniqueness

section HaltList

variable {tm : FinTM2}

/-- A halt configuration's halting label is `none`. -/
@[simp]
theorem haltList_l (s : List (tm.Γ tm.k₁)) : (haltList tm s).l = none := rfl

/-- The step function halts immediately on a halt configuration. -/
theorem step_haltList (s : List (tm.Γ tm.k₁)) : tm.step (haltList tm s) = none := rfl

/-- Reading the output stack of a halt configuration recovers the output list. -/
theorem haltList_stk_k₁ (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s := by
  show (@dite (List (tm.Γ tm.k₁)) (tm.k₁ = tm.k₁) (tm.kDecidableEq tm.k₁ tm.k₁)
      (fun h => by rw [h]; exact s) fun _ => []) = s
  rw [dif_pos rfl]
  rfl

/-- `haltList tm` is injective on the output stack. -/
theorem haltList_injective : Function.Injective (haltList tm) := by
  intro s s' h
  have := congrArg (fun c => c.stk tm.k₁) h
  simpa only [haltList_stk_k₁] using this

end HaltList

section Verifier

variable {α : Type} {αΓ : Type} {ea : α → List αΓ} {verify : α → Bool}
  (h : TM2ComputableInPolyTime ea Computability.encodeBool verify)

/-- The verifier TM's encoded input stack for `a`. -/
def verifierInput (a : α) : List (h.tm.Γ h.tm.k₀) := List.map h.inputAlphabet.invFun (ea a)

/-- The verifier TM's encoded output stack for a Boolean result `b`. -/
def verifierOut (b : Bool) : List (h.tm.Γ h.tm.k₁) :=
  List.map h.outputAlphabet.invFun (Computability.encodeBool b)

/-- The verifier TM's polynomial time budget on input `a`. -/
def verifierTime (a : α) : ℕ := h.time.eval (ea a).length

/-- `verifierOut` is injective in the Boolean argument. -/
theorem verifierOut_injective : Function.Injective (verifierOut h) := by
  intro b b' hb
  have hmap : List.map h.outputAlphabet.invFun (Computability.encodeBool b)
      = List.map h.outputAlphabet.invFun (Computability.encodeBool b') := hb
  have : Computability.encodeBool b = Computability.encodeBool b' :=
    List.map_injective_iff.mpr h.outputAlphabet.symm.injective hmap
  simpa only [Computability.encodeBool, pure, List.cons.injEq, and_true] using this

/-- Forward: the verifier TM halts on input `a` with output `verifierOut (verify a)`
within its polynomial time budget. -/
theorem verify_imp_acceptsOut (a : α) :
    AcceptsWithin h.tm (verifierInput h a) (some (verifierOut h (verify a)))
      (verifierTime h a) :=
  acceptsWithin_iff.mpr ⟨h.outputsFun a⟩

/-- Halt-uniqueness for the verifier: any halting output the TM can reach on input
`a` equals `verifierOut (verify a)`. -/
theorem acceptsWithin_out_inj (a : α) {O : List (h.tm.Γ h.tm.k₁)} {m : ℕ}
    (hO : AcceptsWithin h.tm (verifierInput h a) (some O) m) :
    O = verifierOut h (verify a) := by
  -- Both `hO` and the forward acceptance reach a halt configuration of the trace.
  obtain ⟨k₁, _, hk₁⟩ := hO
  obtain ⟨k₂, _, hk₂⟩ := verify_imp_acceptsOut h a
  rw [Option.map_some] at hk₁ hk₂
  -- The two halt configurations agree by halt-uniqueness of the deterministic trace.
  have heq : haltList h.tm O = haltList h.tm (verifierOut h (verify a)) :=
    traceFrom_halt_unique hk₁ (step_haltList O) hk₂ (step_haltList (verifierOut h (verify a)))
  exact haltList_injective heq

/-- The verifier returns `true` iff the TM halts within budget with the encoded
`true` output. -/
theorem verify_iff_acceptsTrue (a : α) :
    verify a = true ↔
      AcceptsWithin h.tm (verifierInput h a) (some (verifierOut h true)) (verifierTime h a) := by
  constructor
  · intro hv
    have := verify_imp_acceptsOut h a
    rwa [hv] at this
  · intro hacc
    have hout : verifierOut h true = verifierOut h (verify a) :=
      acceptsWithin_out_inj h a hacc
    exact (verifierOut_injective h hout).symm

end Verifier

section Restatements

-- Each theorem restated against its expected type ("it compiled" ≠ "it says the right thing").

variable {σ : Type*} {f : σ → Option σ} {c₀ : σ}

example {k₁ k₂ : ℕ} {c₁ c₂ : σ}
    (h₁ : traceFrom f c₀ k₁ = some c₁) (hc₁ : f c₁ = none)
    (h₂ : traceFrom f c₀ k₂ = some c₂) (hc₂ : f c₂ = none) : c₁ = c₂ :=
  traceFrom_halt_unique h₁ hc₁ h₂ hc₂

example {tm : FinTM2} (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s :=
  haltList_stk_k₁ s

example {tm : FinTM2} : Function.Injective (haltList (tm := tm)) := haltList_injective

example {α αΓ : Type} {ea : α → List αΓ} {verify : α → Bool}
    (h : TM2ComputableInPolyTime ea Computability.encodeBool verify) (a : α) :
    AcceptsWithin h.tm (verifierInput h a) (some (verifierOut h (verify a))) (verifierTime h a) :=
  verify_imp_acceptsOut h a

example {α αΓ : Type} {ea : α → List αΓ} {verify : α → Bool}
    (h : TM2ComputableInPolyTime ea Computability.encodeBool verify) (a : α) :
    verify a = true ↔
      AcceptsWithin h.tm (verifierInput h a) (some (verifierOut h true)) (verifierTime h a) :=
  verify_iff_acceptsTrue h a

end Restatements

end DeepWiki
