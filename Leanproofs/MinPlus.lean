import Leanproofs.MinPlus.Dioid
import Leanproofs.MinPlus.CompleteDioid
import Leanproofs.MinPlus.Builder
import Leanproofs.MinPlus.RminInstance
import Leanproofs.MinPlus.RplusMinInstance
import Leanproofs.MinPlus.RbarInstance
import Leanproofs.MinPlus.Convolution
import Leanproofs.MinPlus.FunctionDioid
import Leanproofs.MinPlus.FunctionClasses
import Leanproofs.MinPlus.SubDioid
import Leanproofs.MinPlus.FunctionClassDioids

/-!
# Chapter 2 — The (min,plus) Functions Semi-ring

Umbrella module for the formalization of Chapter 2 of Bouillard, Boyer and Le Corronc,
*Deterministic Network Calculus*. Currently re-exports:

* `Leanproofs.MinPlus.Dioid` — idempotent dioids and Theorem 2.1 (§2.1.1);
* `Leanproofs.MinPlus.CompleteDioid` — the complete dioid of scalars (§2.1.1);
* `Leanproofs.MinPlus.Builder` — the reusable `(·)ᵒᵈ` (min,plus) dioid construction;
* `Leanproofs.MinPlus.RminInstance` — `Rmin = ℝ ∪ {+∞}` is a dioid (Theorem 2.2);
* `Leanproofs.MinPlus.RplusMinInstance` — `R⁺min = ℝ≥0 ∪ {+∞}` is a complete dioid (Prop. 2.2);
* `Leanproofs.MinPlus.RbarInstance` — `R̄min = ℝ ∪ {±∞}` is a complete dioid (Prop. 2.1);
* `Leanproofs.MinPlus.Convolution` — the (min,plus) functions `F` and convolution (Def. 2.6–2.7);
* `Leanproofs.MinPlus.FunctionDioid` — `(F, ∧, ∗)` is a complete commutative dioid (Prop. 2.3);
* `Leanproofs.MinPlus.FunctionClasses` — the subsets `F⁺, F₀, F↑, F↑₀` (Def. 2.8) and their
  stability under `∧`/`∗` (Lemma 2.3);
* `Leanproofs.MinPlus.SubDioid` — the generic sub-complete-dioid builder (`SubCompleteDioid`):
  closure data over a `CompleteDioid` yields the restricted complete dioid with adjusted top
  `sSup carrier`;
* `Leanproofs.MinPlus.FunctionClassDioids` — `F⁺` and `F↑` are complete dioids with the adjusted
  top `const0` (the constant-`0` function), built via `SubDioid`; and `F₀`, `F↑₀` are not dioids
  (they lack `ε`).
-/
