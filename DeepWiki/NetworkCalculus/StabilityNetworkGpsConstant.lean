import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-! # GPS networks with constant rates: the peelable critical flow (Lemma 12.5)
In a network of GPS servers where each flow `j` keeps one weight `φⱼ > 0` along its
path and is offered the share `φⱼ / ∑_{k∈Fl(h)} φₖ` of each crossed server `h`'s rate
`R^(h)`, aggregate local stability `∑_{j∈Fl(h)} rⱼ < R^(h)` at every server forces the
existence of a *single* flow `i` — the one minimizing `rⱼ/φⱼ` — whose rate stays
below its GPS share `φᵢ R^(h)/∑_{k∈Fl(h)} φₖ` at *every* server it crosses. This is
the flow that can be peeled off in the induction proving local ⟹ global stability
(Theorem 12.5). The statement is purely arithmetic over the flow/server incidence. -/

namespace DeepWiki

open scoped BigOperators

/-- **Lemma 12.5** (GPS with constant rates): with flows `ι`, servers `σ`, positive
weights `φ`, per-server rates `R`, and flow sets `Fl h` (`i ∈ Fl h ⇔ flow `i` crosses
server `h`), aggregate local stability `∑_{j∈Fl h} r j < R h` at every server yields a
flow `i` below its GPS share `φ i · R h / ∑_{j∈Fl h} φ j` at every server it crosses.
The witness is the flow minimizing `r j / φ j`. -/
theorem exists_flow_below_gps_share {ι σ : Type*} [Fintype ι] [Nonempty ι]
    (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j) (R : σ → ℝ) (Fl : σ → Finset ι)
    (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i, ∀ h, i ∈ Fl h → r i < φ i * R h / (∑ j ∈ Fl h, φ j) := by
  obtain ⟨i, -, himin⟩ :=
    Finset.exists_min_image Finset.univ (fun j => r j / φ j) Finset.univ_nonempty
  refine ⟨i, fun h hi => ?_⟩
  have hsumφ : 0 < ∑ j ∈ Fl h, φ j := Finset.sum_pos (fun j _ => hφ j) ⟨i, hi⟩
  -- the minimality `r i / φ i ≤ r j / φ j` cross-multiplies to `r i · φ j ≤ r j · φ i`
  have hcross : ∀ j, r i * φ j ≤ r j * φ i := fun j =>
    (div_le_div_iff₀ (hφ i) (hφ j)).mp (himin j (Finset.mem_univ j))
  rw [lt_div_iff₀ hsumφ]
  calc r i * ∑ j ∈ Fl h, φ j
      = ∑ j ∈ Fl h, r i * φ j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Fl h, φ i * r j :=
        Finset.sum_le_sum fun j _ => (hcross j).trans_eq (mul_comm _ _)
    _ = φ i * ∑ j ∈ Fl h, r j := by rw [← Finset.mul_sum]
    _ < φ i * R h := mul_lt_mul_of_pos_left (hstab h) (hφ i)

end DeepWiki
