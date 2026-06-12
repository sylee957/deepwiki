import Book.ServersResidual

/-! # GPS residual service
A generalized-processor-sharing server guarantees each backlogged flow
its weighted share of the service: `φⱼ·ΔDᵢ ≥ φᵢ·ΔDⱼ` on flow-`i`
backlogged periods. Summing the shares over any subset `J` whose
aggregate is served at a strict `β_J` leaves flow `i ∈ J` the strict
proportion `(φᵢ/∑_{j∈J} φⱼ)·β_J` — the book's subset lemma, whose
`J = univ` instance is the GPS residual theorem. The improved residual
(truncating the higher-share flows at their crossing times) is
deferred. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **GPS server family**: on every backlogged period of flow `i` the
served amounts respect the proportional shares,
`φᵢ·(Dⱼ(t)−Dⱼ(s)) ≤ φⱼ·(Dᵢ(t)−Dᵢ(s))`. -/
def IsGps {ι : Type*} (φ : ι → ℝ≥0) (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i j, ∀ s t : ℝ≥0, s ≤ t → IsBacklogged (A i) (D i) (Set.Ioc s t) →
    φ i * (D j t - D j s) ≤ φ j * (D i t - D i s)

/-- **GPS `n`-server**: every served family respects the proportional
shares. -/
def IsGpsServerN {ι : Type*} (φ : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds → IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- **GPS share against any aggregate**: on a backlogged period of
flow `i`, the total weight of `J` times flow `i`'s increment
dominates `φ i` times the `J`-aggregate increment. -/
theorem mul_sum_le_sum_mul_of_isGps {ι : Type*} {φ : ι → ℝ≥0}
    {As Ds : ι → Curve} {J : Finset ι}
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    φ i * ((∑ j ∈ J, (Ds j) t) - ∑ j ∈ J, (Ds j) s)
      ≤ (∑ j ∈ J, φ j) * ((Ds i) t - (Ds i) s) := by
  calc φ i * ((∑ j ∈ J, (Ds j) t) - ∑ j ∈ J, (Ds j) s)
      = φ i * ∑ j ∈ J, ((Ds j) t - (Ds j) s) := by
        congr 1
        exact (Finset.sum_tsub_distrib J fun j _ =>
          ((Ds j).mono hst : (Ds j) s ≤ (Ds j) t)).symm
    _ = ∑ j ∈ J, φ i * ((Ds j) t - (Ds j) s) := Finset.mul_sum ..
    _ ≤ ∑ j ∈ J, φ j * ((Ds i) t - (Ds i) s) :=
        Finset.sum_le_sum fun j _ => hgps i j s t hst hbl
    _ = (∑ j ∈ J, φ j) * ((Ds i) t - (Ds i) s) := (Finset.sum_mul ..).symm

/-- **GPS proportional share over a subset** (product form): if the
aggregate of the flows in `J` is served at a strict `β_J`, each flow
`i ∈ J` keeps its share on its own backlogged periods:
`φᵢ·β_J(t−s) ≤ (∑_{j∈J} φⱼ)·(Dᵢ(t)−Dᵢ(s))`. -/
theorem mul_le_sum_mul_of_isGps {ι : Type*} {φ : ι → ℝ≥0}
    {As Ds : ι → Curve} {J : Finset ι} {βJ : ℝ≥0 → ℝ≥0}
    (hc : ∀ j ∈ J, Ds j ≤ As j)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j ∈ J, (As j) x) (fun x => ∑ j ∈ J, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j ∈ J, (Ds j) s) + βJ (t - s) ≤ ∑ j ∈ J, (Ds j) t)
    {i : ι} (hi : i ∈ J) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    φ i * βJ (t - s) ≤ (∑ j ∈ J, φ j) * ((Ds i) t - (Ds i) s) := by
  have hstr := hstrict s t hst
    (isBacklogged_sum_of_isBacklogged (fun j hj x => hc j hj x) hi hbl)
  have hβle : βJ (t - s) ≤ (∑ j ∈ J, (Ds j) t) - ∑ j ∈ J, (Ds j) s :=
    le_tsub_of_add_le_left hstr
  exact le_trans (mul_le_mul_right hβle (φ i))
    (mul_sum_le_sum_mul_of_isGps hgps hst hbl)

/-- **GPS residual service over a subset** (the book's subset lemma, in
strict-service form): with positive total weight on `J`, flow `i ∈ J`
obeys the strict inequality for `(φᵢ/∑_{j∈J} φⱼ)·β_J`. -/
theorem add_div_mul_le_of_isGps {ι : Type*} {φ : ι → ℝ≥0}
    {As Ds : ι → Curve} {J : Finset ι} {βJ : ℝ≥0 → ℝ≥0}
    (hc : ∀ j ∈ J, Ds j ≤ As j)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j ∈ J, (As j) x) (fun x => ∑ j ∈ J, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j ∈ J, (Ds j) s) + βJ (t - s) ≤ ∑ j ∈ J, (Ds j) t)
    {i : ι} (hi : i ∈ J) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + (φ i / ∑ j ∈ J, φ j) * βJ (t - s) ≤ (Ds i) t := by
  rcases eq_zero_or_pos (∑ j ∈ J, φ j) with hΦ | hΦ
  · rw [hΦ, div_zero, zero_mul, add_zero]
    exact (Ds i).mono hst
  have hkey : (φ i / ∑ j ∈ J, φ j) * βJ (t - s)
      ≤ (Ds i) t - (Ds i) s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hΦ, mul_comm ((Ds i) t - (Ds i) s)]
    exact mul_le_sum_mul_of_isGps hc hgps hstrict hi hst hbl
  calc (Ds i) s + (φ i / ∑ j ∈ J, φ j) * βJ (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hkey
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

/-- Relation form: a GPS `n`-server with positive total weight and a
strict aggregate service curve `β` offers `(φᵢ/∑ φⱼ)·β` as a strict
service curve to the residual server of flow `i`. -/
theorem isStrictMinimalServiceCurve_residualServer_of_isGps {ι : Type*}
    [Fintype ι] {S : (ι → Curve) → (ι → Curve) → Prop}
    {φ : ι → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S) :
    IsStrictMinimalServiceCurve (fun v => (φ i / ∑ j, φ j) * β v)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  refine add_div_mul_le_of_isGps (fun j _ => hcaus As Ds hp j)
    (hgps As Ds hp) ?_ (Finset.mem_univ i) hst hbl
  exact hβ.sum_strict hp

/-! ## Book restatement (GPS residual service)
A GPS `n`-server offering a strict service curve `β` with non-null
weights `φ₁,…,φₙ` (the formal theorem needs no positivity at all — null
total weight degenerates the curve to `0`): flow `i` receives
`(φᵢ/∑ⱼ φⱼ)·β` as a strict service curve — independent of the cross-traffic intensity (and accordingly
loose: the improvement that lets saturated higher-share flows release
their share is the book's follow-up theorem, deferred). -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop}
    {φ : ι → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S) :
    IsStrictMinimalServiceCurve (fun v => (φ i / ∑ j, φ j) * β v)
      (residualServer S i) :=
  isStrictMinimalServiceCurve_residualServer_of_isGps hSrv.1 hβ hgps

end DeepWiki
