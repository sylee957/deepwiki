import Book.CompleteDioids
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

/-! # Scalar dioid carriers

One-field newtype `structure`s wrapping numeric types as
(min,plus) / (max,plus) dioids, with `ofVal`/`toVal` and
attached lattice + dioid instances.
-/

namespace DeepWiki

open scoped Algebra.Bridge
open scoped ENNReal NNReal Classical

/-- (min,plus) dioid carrier over `WithTop ℝ`. -/
structure MinPlus where ofVal ::
  toVal : WithTop ℝ

/-- (min,plus) dioid carrier over `WithTop (WithBot ℝ)`. -/
structure MinPlusExt where ofVal ::
  toVal : WithTop (WithBot ℝ)

/-- (min,plus) dioid carrier over `ℝ≥0∞`. -/
structure MinPlusNN where ofVal ::
  toVal : ℝ≥0∞

/-- (max,plus) dioid carrier over `WithBot ℝ≥0∞`. -/
structure MaxPlusNN where ofVal ::
  toVal : WithBot ℝ≥0∞

/-- (max,plus) dioid carrier over `WithBot (WithTop ℝ)`. -/
structure MaxPlusExt where ofVal ::
  toVal : WithBot (WithTop ℝ)

namespace MinPlus
/-- Coercion `MinPlus → WithTop ℝ` via `toVal`. -/
instance : Coe MinPlus (WithTop ℝ) := ⟨toVal⟩
/-- Extensionality: equal `toVal` implies equal `MinPlus`. -/
@[ext] theorem ext {a b : MinPlus}
    (h : (a : WithTop ℝ) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlus

namespace MinPlusExt
/-- Coercion `MinPlusExt → WithTop (WithBot ℝ)` via `toVal`. -/
instance : Coe MinPlusExt (WithTop (WithBot ℝ)) := ⟨toVal⟩
/-- Extensionality: equal `toVal` implies equal `MinPlusExt`. -/
@[ext] theorem ext {a b : MinPlusExt}
    (h : (a : WithTop (WithBot ℝ)) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlusExt

namespace MinPlusNN
/-- Coercion `MinPlusNN → ℝ≥0∞` via `toVal`. -/
instance : Coe MinPlusNN ℝ≥0∞ := ⟨toVal⟩
/-- Extensionality: equal `toVal` implies equal `MinPlusNN`. -/
@[ext] theorem ext {a b : MinPlusNN}
    (h : (a : ℝ≥0∞) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MinPlusNN

namespace MaxPlusNN
/-- Coercion `MaxPlusNN → WithBot ℝ≥0∞` via `toVal`. -/
instance : Coe MaxPlusNN (WithBot ℝ≥0∞) := ⟨toVal⟩
/-- Extensionality: equal `toVal` implies equal `MaxPlusNN`. -/
@[ext] theorem ext {a b : MaxPlusNN}
    (h : (a : WithBot ℝ≥0∞) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MaxPlusNN

namespace MaxPlusExt
/-- Coercion `MaxPlusExt → WithBot (WithTop ℝ)` via `toVal`. -/
instance : Coe MaxPlusExt (WithBot (WithTop ℝ)) := ⟨toVal⟩
/-- Extensionality: equal `toVal` implies equal `MaxPlusExt`. -/
@[ext] theorem ext {a b : MaxPlusExt}
    (h : (a : WithBot (WithTop ℝ)) = b) : a = b := by
  cases a; cases b; exact congrArg ofVal h
end MaxPlusExt

namespace MinPlusAux

/-- `+` left-distributes over `min` on `WithTop ℝ`. -/
theorem add_min (a b c : WithTop ℝ) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

/-- `+` right-distributes over `min` on `WithTop ℝ`. -/
theorem min_add (a b c : WithTop ℝ) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

end MinPlusAux

namespace MinPlus
open Algebra

/-- `MinPlus` dioid: `⊕ = min`, `⊗ = +`, `𝟘 = ⊤`, `𝟙 = 0`. -/
instance : Algebra.Dioid MinPlus where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MinPlusAux.add_min _ _ _)
  right_distrib _ _ _ := ext (MinPlusAux.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)

end MinPlus

namespace MinPlus

/-- Dioid order `≼ₒ` is the reverse numeric order on `MinPlus`. -/
theorem le_iff (a b : MinPlus) :
    a ≼ₒ b ↔ (b : WithTop ℝ) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlus) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : WithTop ℝ) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)

end MinPlus

namespace MinPlus
open Algebra

example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : MinPlus) ⊕ₒ ⟨y⟩ = ⟨z⟩ :=
  ⟨min x y, rfl⟩

example (a : MinPlus) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a

example (x y : ℝ) :
    ∃ z : ℝ, (⟨x⟩ : MinPlus) ⊗ₒ ⟨y⟩ = ⟨z⟩ :=
  ⟨x + y, rfl⟩

example (a : MinPlus) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlus

example (a : MinPlus) :
    a ≼ₒ a :=
  le_rfl

namespace RbarX

/-- Order iso `x ↦ r + x` on `WithTop (WithBot ℝ)`. -/
noncomputable def shift (r : ℝ) :
    WithTop (WithBot ℝ) ≃o WithTop (WithBot ℝ) :=
  ((OrderIso.addLeft r).withBotCongr).withTopCongr

/-- `shift r` acts as left-addition by `r`. -/
theorem shift_eq (r : ℝ) (x : WithTop (WithBot ℝ)) :
    shift r x
      = (((r : WithBot ℝ) : WithTop (WithBot ℝ)))
        + x := by
  induction x using WithTop.recTopCoe with
  | top => simp [shift]
  | coe d =>
    induction d using WithBot.recBotCoe with
    | bot =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.withBotCongr_apply,
        WithBot.map_bot]
      rw [show ((⊥ : WithBot ℝ)
            : WithTop (WithBot ℝ))
          = ((↑r : WithBot ℝ)
              : WithTop (WithBot ℝ))
            + ((⊥ : WithBot ℝ)
                : WithTop (WithBot ℝ)) from ?_]
      · rfl
      · rw [← WithTop.coe_add, WithBot.add_bot]
    | coe s =>
      simp only [shift, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.addLeft_apply]
      rw [← WithTop.coe_add, ← WithBot.coe_add]

/-- `+` distributes over `⨅` on `WithTop (WithBot ℝ)`. -/
theorem add_iInf {ι : Sort*} (a : WithTop (WithBot ℝ))
    (f : ι → WithTop (WithBot ℝ)) :
    (a + ⨅ i, f i) = ⨅ i, a + f i := by
  refine le_antisymm
    (le_iInf fun i => by gcongr; exact iInf_le _ i) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [iInf_of_empty]
  · induction a using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      induction b using WithBot.recBotCoe with
      | coe r =>
        have hmap : (shift r) (⨅ i, f i)
            = ⨅ i, (shift r) (f i) :=
          OrderIso.map_iInf _ _
        simp only [shift_eq] at hmap
        exact hmap.ge
      | bot =>
        by_cases htop : (⨅ i, f i) = ⊤
        · have hall : ∀ i, f i = ⊤ := fun i =>
            top_le_iff.mp (htop ▸ iInf_le f i)
          simp only [hall, WithTop.add_top,
            ciInf_const, le_refl]
        · obtain ⟨c, hc⟩ :=
            Option.ne_none_iff_exists'.mp htop
          rw [show (⨅ i, f i)
              = (c : WithTop (WithBot ℝ)) from hc,
            ← WithTop.coe_add]
          have hex : ∃ j, f j ≠ ⊤ := by
            by_contra h; push Not at h
            exact htop (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊥ : WithBot ℝ) + c : WithBot ℝ)
              = ⊥ from WithBot.bot_add c]
          refine iInf_le_of_le j ?_
          obtain ⟨d, hd⟩ :=
            Option.ne_none_iff_exists'.mp hj
          rw [show f j
              = (d : WithTop (WithBot ℝ)) from hd,
            ← WithTop.coe_add, WithBot.bot_add]

/-- `+` left-distributes over `min` on `WithTop (WithBot ℝ)`. -/
theorem add_min (a b c : WithTop (WithBot ℝ)) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

/-- `+` right-distributes over `min` on `WithTop (WithBot ℝ)`. -/
theorem min_add (a b c : WithTop (WithBot ℝ)) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

end RbarX

namespace MinPlusExt

/-- `MinPlusExt` dioid: `⊕ = min`, `⊗ = +`, `𝟘 = ⊤`, `𝟙 = 0`. -/
instance : Algebra.Dioid MinPlusExt where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (RbarX.add_min _ _ _)
  right_distrib _ _ _ := ext (RbarX.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)

/-- Dioid order `≼ₒ` is the reverse numeric order on `MinPlusExt`. -/
theorem le_iff (a b : MinPlusExt) :
    a ≼ₒ b ↔ (b : WithTop (WithBot ℝ)) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlusExt) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : WithTop (WithBot ℝ)) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)

/-- `MinPlusExt` complete dioid: `⨆ = ⨅` numerically. -/
noncomputable instance :
    Algebra.CompleteDioid MinPlusExt where
  iSup f := ⟨⨅ i, ↑(f i)⟩
  le_iSup f i := (le_iff _ _).mpr (iInf_le _ i)
  iSup_le f b hb := (le_iff _ _).mpr (le_iInf (by
    intro i
    exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithTop (WithBot ℝ)) + ⨅ i, ↑(f i)
       = ⨅ i, ((↑a : WithTop (WithBot ℝ)) + ↑(f i))
    exact RbarX.add_iInf _ _

end MinPlusExt

namespace MinPlusExt
open Algebra

example (x y : ℝ) :
    ∃ z : ℝ, (⟨↑↑x⟩ : MinPlusExt) ⊕ₒ ⟨↑↑y⟩
      = ⟨↑↑z⟩ :=
  ⟨min x y, by
    refine ext ?_
    show min (↑↑x : WithTop (WithBot ℝ)) ↑↑y
        = ↑↑(min x y)
    rw [WithBot.coe_min, WithTop.coe_min]⟩

example (a : MinPlusExt) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a

example (x y : ℝ) :
    ∃ z : ℝ, (⟨↑↑x⟩ : MinPlusExt) ⊗ₒ ⟨↑↑y⟩
      = ⟨↑↑z⟩ :=
  ⟨x + y, by
    refine ext ?_
    show (↑↑x : WithTop (WithBot ℝ)) + ↑↑y
        = ↑↑(x + y)
    rw [WithBot.coe_add, WithTop.coe_add]⟩

example (a : MinPlusExt) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlusExt

namespace RplusX

/-- `+` left-distributes over `min` on `ℝ≥0∞`. -/
theorem add_min (a b c : ℝ≥0∞) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by gcongr)]
  · rw [min_eq_right h, min_eq_right (by gcongr)]

/-- `+` right-distributes over `min` on `ℝ≥0∞`. -/
theorem min_add (a b c : ℝ≥0∞) :
    min a b + c = min (a + c) (b + c) := by
  rw [add_comm, add_min, add_comm a c, add_comm b c]

/-- `+` distributes over `⨅` on `ℝ≥0∞`. -/
theorem add_iInf {ι : Sort*} (a : ℝ≥0∞) (f : ι → ℝ≥0∞) :
    a + ⨅ i, f i = ⨅ i, a + f i := ENNReal.add_iInf

end RplusX

namespace MinPlusNN

/-- `MinPlusNN` dioid: `⊕ = min`, `⊗ = +`, `𝟘 = ⊤`, `𝟙 = 0`. -/
instance : Algebra.Dioid MinPlusNN where
  add a b := ⟨min ↑a ↑b⟩
  zero := ⟨⊤⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (min_assoc _ _ _)
  eps_oplus _ := ext (min_eq_right le_top)
  oplus_eps _ := ext (min_eq_left le_top)
  oplus_comm _ _ := ext (min_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (RplusX.add_min _ _ _)
  right_distrib _ _ _ := ext (RplusX.min_add _ _ _)
  eps_otimes _ := ext (WithTop.top_add _)
  otimes_eps _ := ext (WithTop.add_top _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (min_self _)

/-- Dioid order `≼ₒ` is the reverse numeric order on `MinPlusNN`. -/
theorem le_iff (a b : MinPlusNN) :
    a ≼ₒ b ↔ (b : ℝ≥0∞) ≤ a := by
  have h1 : a ≼ₒ b
      ↔ (⟨min ↑a ↑b⟩ : MinPlusNN) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : min (↑a : ℝ≥0∞) ↑b = ↑b := congrArg toVal h
    rw [← this]; exact min_le_left _ _
  · intro h; exact ext (min_eq_right h)

/-- `MinPlusNN` complete dioid: `⨆ = ⨅` numerically. -/
noncomputable instance :
    Algebra.CompleteDioid MinPlusNN where
  iSup f := ⟨⨅ i, ↑(f i)⟩
  le_iSup f i := (le_iff _ _).mpr (iInf_le _ i)
  iSup_le f b hb := (le_iff _ _).mpr (le_iInf (by
    intro i
    exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : ℝ≥0∞) + ⨅ i, ↑(f i)
       = ⨅ i, ((↑a : ℝ≥0∞) + ↑(f i))
    exact RplusX.add_iInf _ _

end MinPlusNN

namespace MinPlusNN
open Algebra

example (x y : ℝ≥0) :
    ∃ z : ℝ≥0, (⟨↑x⟩ : MinPlusNN) ⊕ₒ ⟨↑y⟩
      = ⟨↑z⟩ :=
  ⟨min x y, by
    refine ext ?_
    show min (↑x : ℝ≥0∞) ↑y = ↑(min x y)
    rw [ENNReal.coe_min]⟩

example (a : MinPlusNN) :
    a ⊕ₒ ⟨⊤⟩ = a := add_zero a

example (x y : ℝ≥0) :
    ∃ z : ℝ≥0, (⟨↑x⟩ : MinPlusNN) ⊗ₒ ⟨↑y⟩
      = ⟨↑z⟩ :=
  ⟨x + y, by
    refine ext ?_
    show (↑x : ℝ≥0∞) + ↑y = ↑(x + y)
    rw [ENNReal.coe_add]⟩

example (a : MinPlusNN) :
    a ⊗ₒ ⟨⊤⟩ = ⟨⊤⟩ := mul_zero a

end MinPlusNN

namespace MaxX

/-- For `x ≠ ⊥`, coercing `x.unbotD 0` recovers `x`. -/
theorem coe_unbotD_eq {x : WithBot ℝ≥0∞} (h : x ≠ ⊥) :
    ((x.unbotD 0 : ℝ≥0∞) : WithBot ℝ≥0∞) = x := by
  obtain ⟨d, rfl⟩ := (WithBot.ne_bot_iff_exists).mp h
  rw [WithBot.unbotD_coe]

/-- `⨆` on `WithBot ℝ≥0∞` equals the coerced `ℝ≥0∞` `⨆`. -/
theorem bridge {ι : Sort*} (f : ι → WithBot ℝ≥0∞)
    (j : ι) (hj : f j ≠ ⊥) :
    (⨆ i, f i)
      = ((⨆ i, (f i).unbotD 0 : ℝ≥0∞)
          : WithBot ℝ≥0∞) := by
  have : Nonempty ι := ⟨j⟩
  rw [WithBot.coe_iSup (OrderTop.bddAbove
    (Set.range fun i => (f i).unbotD 0))]
  refine le_antisymm (iSup_le fun i => ?_)
    (iSup_le fun i => ?_)
  · rcases eq_or_ne (f i) ⊥ with h0 | h0
    · exact h0 ▸ bot_le
    · exact le_iSup_of_le i (by rw [coe_unbotD_eq h0])
  · rcases eq_or_ne (f i) ⊥ with h0 | h0
    · rw [h0]; refine le_iSup_of_le j ?_
      obtain ⟨d, hd⟩ := (WithBot.ne_bot_iff_exists).mp hj
      rw [← hd, WithBot.unbotD_bot, WithBot.coe_le_coe]
      exact bot_le
    · exact le_iSup_of_le i (by rw [coe_unbotD_eq h0])

/-- `+` distributes over `⨆` on `WithBot ℝ≥0∞`. -/
theorem add_iSup {ι : Sort*} (a : WithBot ℝ≥0∞)
    (f : ι → WithBot ℝ≥0∞) :
    a + ⨆ i, f i = ⨆ i, a + f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · induction a using WithBot.recBotCoe with
    | bot => simp
    | coe e =>
      by_cases hb : ∃ j, f j ≠ ⊥
      · obtain ⟨j, hj⟩ := hb
        have hgj : (e : WithBot ℝ≥0∞) + f j ≠ ⊥ := by
          obtain ⟨d, hd⟩ :=
            (WithBot.ne_bot_iff_exists).mp hj
          rw [← hd, ← WithBot.coe_add]
          exact WithBot.coe_ne_bot
        have hv : ∀ i,
            ((e : WithBot ℝ≥0∞) + f i).unbotD 0
            = if f i = ⊥ then 0
              else e + (f i).unbotD 0 := by
          intro i
          rcases eq_or_ne (f i) ⊥ with h0 | h0
          · simp [h0]
          · obtain ⟨d, hd⟩ :=
              (WithBot.ne_bot_iff_exists).mp h0
            simp [← hd, ← WithBot.coe_add]
        rw [bridge f j hj,
          bridge (fun i => (e : WithBot ℝ≥0∞) + f i)
            j hgj,
          ← WithBot.coe_add, ENNReal.add_iSup]
        congr 1
        refine le_antisymm (iSup_le fun i => ?_)
          (iSup_le fun i => ?_)
        · rcases eq_or_ne (f i) ⊥ with h0 | h0
          · refine le_iSup_of_le j ?_
            rw [hv j, if_neg hj, h0,
              WithBot.unbotD_bot, add_zero]
            exact le_self_add
          · exact le_iSup_of_le i
              (by rw [hv i, if_neg h0])
        · rw [hv i]
          rcases eq_or_ne (f i) ⊥ with h0 | h0
          · simp [h0]
          · rw [if_neg h0]
            exact le_iSup_of_le i (le_refl _)
      · push Not at hb; simp [hb]

/-- `+` left-distributes over `max` on `WithBot ℝ≥0∞`. -/
theorem add_max (a b c : WithBot ℝ≥0∞) :
    a + max b c = max (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (by gcongr)]
  · rw [max_eq_left h, max_eq_left (by gcongr)]

/-- `+` right-distributes over `max` on `WithBot ℝ≥0∞`. -/
theorem max_add (a b c : WithBot ℝ≥0∞) :
    max a b + c = max (a + c) (b + c) := by
  rw [add_comm, add_max, add_comm a c, add_comm b c]

end MaxX

namespace MaxPlusNN

/-- `MaxPlusNN` dioid: `⊕ = max`, `⊗ = +`, `𝟘 = ⊥`, `𝟙 = 0`. -/
instance : Algebra.Dioid MaxPlusNN where
  add a b := ⟨max ↑a ↑b⟩
  zero := ⟨⊥⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (max_assoc _ _ _)
  eps_oplus _ := ext (max_eq_right bot_le)
  oplus_eps _ := ext (max_eq_left bot_le)
  oplus_comm _ _ := ext (max_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MaxX.add_max _ _ _)
  right_distrib _ _ _ := ext (MaxX.max_add _ _ _)
  eps_otimes _ := ext (WithBot.bot_add _)
  otimes_eps _ := ext (WithBot.add_bot _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (max_self _)

/-- Dioid order `≼ₒ` agrees with the numeric order on `MaxPlusNN`. -/
theorem le_iff (a b : MaxPlusNN) :
    a ≼ₒ b ↔ (a : WithBot ℝ≥0∞) ≤ b := by
  have h1 : a ≼ₒ b
      ↔ (⟨max ↑a ↑b⟩ : MaxPlusNN) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : max (↑a : WithBot ℝ≥0∞) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact le_max_left _ _
  · intro h; exact ext (max_eq_right h)

/-- `MaxPlusNN` complete dioid: `⨆` is the numeric `⨆`. -/
noncomputable instance :
    Algebra.CompleteDioid MaxPlusNN where
  iSup f := ⟨⨆ i, ↑(f i)⟩
  le_iSup f i :=
    (le_iff _ _).mpr
      (le_iSup (fun i => (f i : WithBot ℝ≥0∞)) i)
  iSup_le f b hb := (le_iff _ _).mpr (iSup_le (by
    intro i; exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithBot ℝ≥0∞) + ⨆ i, ↑(f i)
       = ⨆ i, ((↑a : WithBot ℝ≥0∞) + ↑(f i))
    exact MaxX.add_iSup _ _

end MaxPlusNN

namespace MaxPlusExtAux

/-- Order iso `x ↦ r + x` on `WithBot (WithTop ℝ)`. -/
noncomputable def shift (r : ℝ) :
    WithBot (WithTop ℝ) ≃o WithBot (WithTop ℝ) :=
  ((OrderIso.addLeft r).withTopCongr).withBotCongr

/-- `shift r` acts as left-addition by `r`. -/
theorem shift_eq (r : ℝ) (x : WithBot (WithTop ℝ)) :
    shift r x
      = (((r : WithTop ℝ) : WithBot (WithTop ℝ)))
        + x := by
  induction x using WithBot.recBotCoe with
  | bot => simp [shift]
  | coe d =>
    induction d using WithTop.recTopCoe with
    | top =>
      simp only [shift, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.withTopCongr_apply,
        WithTop.map_top]
      rw [show ((⊤ : WithTop ℝ)
            : WithBot (WithTop ℝ))
          = ((↑r : WithTop ℝ)
              : WithBot (WithTop ℝ))
            + ((⊤ : WithTop ℝ)
                : WithBot (WithTop ℝ)) from ?_]
      · rfl
      · rw [← WithBot.coe_add, WithTop.add_top]
    | coe s =>
      simp only [shift, OrderIso.withBotCongr_apply,
        WithBot.map_coe, OrderIso.withTopCongr_apply,
        WithTop.map_coe, OrderIso.addLeft_apply]
      rw [← WithBot.coe_add, ← WithTop.coe_add]

/-- `+` distributes over `⨆` on `WithBot (WithTop ℝ)`. -/
theorem add_iSup {ι : Sort*} (a : WithBot (WithTop ℝ))
    (f : ι → WithBot (WithTop ℝ)) :
    (a + ⨆ i, f i) = ⨆ i, a + f i := by
  refine le_antisymm ?_
    (iSup_le fun i => by gcongr; exact le_iSup _ i)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · induction a using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      induction b using WithTop.recTopCoe with
      | coe r =>
        have hmap : (shift r) (⨆ i, f i)
            = ⨆ i, (shift r) (f i) :=
          OrderIso.map_iSup _ _
        simp only [shift_eq] at hmap
        exact hmap.le
      | top =>
        by_cases hbot : (⨆ i, f i) = ⊥
        · have hall : ∀ i, f i = ⊥ := fun i =>
            le_bot_iff.mp (hbot ▸ le_iSup f i)
          simp only [hall, WithBot.add_bot,
            ciSup_const, le_refl]
        · obtain ⟨c, hc⟩ :=
            Option.ne_none_iff_exists'.mp hbot
          rw [show (⨆ i, f i)
              = (c : WithBot (WithTop ℝ)) from hc,
            ← WithBot.coe_add]
          have hex : ∃ j, f j ≠ ⊥ := by
            by_contra h; push Not at h
            exact hbot (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊤ : WithTop ℝ) + c : WithTop ℝ)
              = ⊤ from WithTop.top_add c]
          refine le_iSup_of_le j ?_
          obtain ⟨d, hd⟩ :=
            Option.ne_none_iff_exists'.mp hj
          rw [show f j
              = (d : WithBot (WithTop ℝ)) from hd,
            ← WithBot.coe_add, WithTop.top_add]

/-- `+` left-distributes over `max` on `WithBot (WithTop ℝ)`. -/
theorem add_max (a b c : WithBot (WithTop ℝ)) :
    a + max b c = max (a + b) (a + c) := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (by gcongr)]
  · rw [max_eq_left h, max_eq_left (by gcongr)]

/-- `+` right-distributes over `max` on `WithBot (WithTop ℝ)`. -/
theorem max_add (a b c : WithBot (WithTop ℝ)) :
    max a b + c = max (a + c) (b + c) := by
  rw [add_comm, add_max, add_comm a c, add_comm b c]

end MaxPlusExtAux

namespace MaxPlusExt

/-- `MaxPlusExt` dioid: `⊕ = max`, `⊗ = +`, `𝟘 = ⊥`, `𝟙 = 0`. -/
instance : Algebra.Dioid MaxPlusExt where
  add a b := ⟨max ↑a ↑b⟩
  zero := ⟨⊥⟩
  mul a b := ⟨↑a + ↑b⟩
  one := ⟨0⟩
  oplus_assoc _ _ _ := ext (max_assoc _ _ _)
  eps_oplus _ := ext (max_eq_right bot_le)
  oplus_eps _ := ext (max_eq_left bot_le)
  oplus_comm _ _ := ext (max_comm _ _)
  otimes_assoc _ _ _ := ext (add_assoc _ _ _)
  one_otimes _ := ext (zero_add _)
  otimes_one _ := ext (add_zero _)
  left_distrib _ _ _ := ext (MaxPlusExtAux.add_max _ _ _)
  right_distrib _ _ _ := ext (MaxPlusExtAux.max_add _ _ _)
  eps_otimes _ := ext (WithBot.bot_add _)
  otimes_eps _ := ext (WithBot.add_bot _)
  otimes_comm _ _ := ext (add_comm _ _)
  oplus_idem _ := ext (max_self _)

/-- Dioid order `≼ₒ` agrees with the numeric order on `MaxPlusExt`. -/
theorem le_iff (a b : MaxPlusExt) :
    a ≼ₒ b ↔ (a : WithBot (WithTop ℝ)) ≤ b := by
  have h1 : a ≼ₒ b
      ↔ (⟨max ↑a ↑b⟩ : MaxPlusExt) = b := Iff.rfl
  rw [h1]
  constructor
  · intro h
    have : max (↑a : WithBot (WithTop ℝ)) ↑b = ↑b :=
      congrArg toVal h
    rw [← this]; exact le_max_left _ _
  · intro h; exact ext (max_eq_right h)

/-- `MaxPlusExt` complete dioid: `⨆` is the numeric `⨆`. -/
noncomputable instance :
    Algebra.CompleteDioid MaxPlusExt where
  iSup f := ⟨⨆ i, ↑(f i)⟩
  le_iSup f i :=
    (le_iff _ _).mpr
      (le_iSup (fun i => (f i : WithBot (WithTop ℝ))) i)
  iSup_le f b hb := (le_iff _ _).mpr (iSup_le (by
    intro i; exact (le_iff _ _).mp (hb i)))
  mul_iSup a f := by
    refine ext ?_
    show (↑a : WithBot (WithTop ℝ)) + ⨆ i, ↑(f i)
       = ⨆ i, ((↑a : WithBot (WithTop ℝ)) + ↑(f i))
    exact MaxPlusExtAux.add_iSup _ _

end MaxPlusExt

end DeepWiki
