import DeepWiki.ReactiveSystems.HennessyMilner
import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # Weak (observational) Hennessy–Milner satisfaction
The *weak* reading of HML: the modalities `⟨a⟩` / `[a]` range over *weak*
transitions `=a⇒` (silent steps absorbed) rather than concrete ones. This is the
satisfaction relevant to testing (§7.3): for example `[a]ff` holds of exactly the
processes that afford no `=a⇒` transition. We record the inductive definition,
its `simp` unfoldings, and that a `τ`-free state has only the trivial weak path
(used to compute the weak transitions of small processes). -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- **Weak satisfaction** `p ⊨w F`: like `Sat`, but `⟨a⟩`/`[a]` quantify over weak
transitions `=a⇒[τ]` instead of concrete `a`-steps. -/
def WSat (L : LTS Proc Act) (tau : Act) (p : Proc) : HML Act → Prop
  | .tt => True
  | .ff => False
  | .and F G => WSat L tau p F ∧ WSat L tau p G
  | .or F G => WSat L tau p F ∨ WSat L tau p G
  | .dia a F => ∃ p', WeakStep L tau p a p' ∧ WSat L tau p' F
  | .box a F => ∀ p', WeakStep L tau p a p' → WSat L tau p' F

variable {L : LTS Proc Act} {tau : Act}

@[simp] theorem wsat_tt (p : Proc) : WSat L tau p HML.tt ↔ True := Iff.rfl
@[simp] theorem wsat_ff (p : Proc) : WSat L tau p HML.ff ↔ False := Iff.rfl
@[simp] theorem wsat_and (p : Proc) (F G : HML Act) :
    WSat L tau p (F.and G) ↔ WSat L tau p F ∧ WSat L tau p G := Iff.rfl
@[simp] theorem wsat_or (p : Proc) (F G : HML Act) :
    WSat L tau p (F.or G) ↔ WSat L tau p F ∨ WSat L tau p G := Iff.rfl
@[simp] theorem wsat_dia (p : Proc) (a : Act) (F : HML Act) :
    WSat L tau p (HML.dia a F) ↔ ∃ p', WeakStep L tau p a p' ∧ WSat L tau p' F := Iff.rfl
@[simp] theorem wsat_box (p : Proc) (a : Act) (F : HML Act) :
    WSat L tau p (HML.box a F) ↔ ∀ p', WeakStep L tau p a p' → WSat L tau p' F := Iff.rfl

/-- `⟨a⟩tt` holds weakly iff the state affords a weak `a`-transition. -/
@[simp] theorem wsat_dia_tt (p : Proc) (a : Act) :
    WSat L tau p (HML.dia a HML.tt) ↔ ∃ p', WeakStep L tau p a p' := by
  simp [WSat]

/-- `[a]ff` holds weakly iff the state affords *no* weak `a`-transition. -/
@[simp] theorem wsat_box_ff (p : Proc) (a : Act) :
    WSat L tau p (HML.box a HML.ff) ↔ ∀ p', ¬ WeakStep L tau p a p' := by
  simp [WSat]

/-- A state with no silent move admits only the trivial silent path: `tauStar`
from it reaches only itself. -/
theorem tauStar_eq_of_no_tau {p p' : Proc} (hp : ∀ q, ¬ L.step p tau q)
    (h : tauStar L tau p p') : p' = p := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, _⟩
  · rfl
  · exact absurd hc (hp c)

end LTS

end DeepWiki.ReactiveSystems
