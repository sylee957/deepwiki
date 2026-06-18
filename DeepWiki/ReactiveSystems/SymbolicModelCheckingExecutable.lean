import DeepWiki.ReactiveSystems.TimedAutomataFinite
import DeepWiki.ReactiveSystems.TimedRegionCode
import DeepWiki.ReactiveSystems.SymbolicModelChecking
import DeepWiki.ReactiveSystems.TimedHmlIntervalDelay

/-! # Executable timed model checking (delay-free fragment)
The executable decision procedure `SymSatCode` mirrors symbolic satisfaction `SymSat`
on a region *code* (`RegionCode`) rather than a real valuation, so it is `#eval`-able.
This file establishes the supporting pieces: the delay-free fragment of `Mt`
(`Mt.DelayFree`), the boundedness transport along clock renamings
(`boundedBy_mapClock`), and the all-zero initial region code `RegionCode.initial` with
its agreement to `regionFingerprint` of the zero valuation — the computable starting
point of a model-checking run. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ## The delay-free fragment -/

variable {Act D : Type*}

/-- The **delay-free fragment** of `Mt`: no `∃∃`/`∀∀` delay quantifiers (whose decision
needs the region time-successor graph). Everything else is allowed. -/
def Mt.DelayFree : Mt Act D → Prop
  | .tt => True
  | .ff => True
  | .and F G => F.DelayFree ∧ G.DelayFree
  | .or F G => F.DelayFree ∧ G.DelayFree
  | .dia _ F => F.DelayFree
  | .box _ F => F.DelayFree
  | .existsDelay _ => False
  | .forallDelay _ => False
  | .reset _ F => F.DelayFree
  | .guard _ => True

/-! ## Boundedness transports along a clock renaming -/

/-- A renamed constraint is bounded by `cmax'` exactly when the original is bounded by
the pulled-back clamp `cmax' ∘ f`. -/
theorem ClockConstraint.boundedBy_mapClock {C C' : Type*} (f : C → C') (cmax' : C' → ℕ) :
    ∀ {g : ClockConstraint C}, (g.mapClock f).BoundedBy cmax' ↔ g.BoundedBy (cmax' ∘ f) := by
  intro g
  induction g with
  | true_ => exact Iff.rfl
  | atom x c n => exact Iff.rfl
  | and g₁ g₂ ih₁ ih₂ => exact and_congr ih₁ ih₂

/-! ## The all-zero initial region code -/

variable {C : Type*}

/-- The region code of the all-zero valuation: every clamped floor `0`, every clock
frac-zero, every frac-order bit set. A computable constant. -/
def RegionCode.initial (cmax : C → ℕ) : RegionCode cmax :=
  (fun _ => ⟨0, by omega⟩, fun _ => true, fun _ _ => true)

open Classical in
/-- **Initial-code agreement.** The fingerprint of the all-zero valuation is the
computable `RegionCode.initial` — so a model-checking run starts from a constant code
without ever evaluating the `noncomputable` `regionFingerprint`. -/
theorem initial_fingerprint {cmax : C → ℕ} :
    regionFingerprint cmax (fun _ => (0 : ℝ≥0)) = RegionCode.initial cmax := by
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · apply Fin.ext
    rw [regionFingerprint_floor]
    show regionFloor cmax (fun _ => (0 : ℝ≥0)) x = 0
    unfold regionFloor; simp
  · rw [regionFingerprint_fracZero]
    exact decide_eq_true_iff.mpr ⟨zero_le', fracPart_zero⟩
  · rw [regionFingerprint_fracOrder]
    exact decide_eq_true_iff.mpr ⟨zero_le', zero_le', le_refl _⟩

end DeepWiki.ReactiveSystems
