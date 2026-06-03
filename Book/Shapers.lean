import VersoManual
import Book.Servers
import Book.SubadditiveClosure
import Book.RealConvolution

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Shapers" =>
A _shaper_ is a server whose output is constrained by an arrival
curve. Building on the curves and servers of the previous chapter, this
chapter defines arrival curves, the shaper servers that enforce them,
the sub-additive closure's effect, and the greedy shaper.

```lean
namespace VerifiedWiki

open Algebra Set Topology Filter
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Convolution monotonicity

The convolution is isotone in each argument: increasing a curve can
only increase the convolution. This is the one fact about the
convolution that the service- and arrival-curve results share.

*Theorem:* $`\sigma \le_n \sigma' \implies D \ast \sigma \le_n D \ast \sigma'`

```lean
theorem conv_natLe_right (D : F) {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    conv D sigma ≤ₙ conv D sigma' := by
  rw [natLe_iff]
  intro t
  rw [conv_apply]
  refine CompleteDioid.sSup_le _ _ ?_
  rintro x ⟨u, s, hus, rfl⟩
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨u, s, hus, rfl⟩)
  exact mul_le_mul_left
    ((natLe_iff sigma sigma').mp h s) (D u)
```

# Min-plus minimal service curves

A _minimal service curve_ bounds a server's output from _below_: the
server `S` offers the min-plus minimal service curve `beta` when every
output is at least the convolution of its input with `beta`,
$`D \ge A \ast \beta`, stated directly on the real values.

*Definition:* `S` offers the min-plus service curve `beta`

```lean
def OffersMinPlusService (beta : ℝ≥0 → ℝ≥0) (S : Server) :
    Prop :=
  ∀ A D : Curve, (A, D) ∈ S → infConvR A beta ≤ D
```

A server `S` _is_ a min-plus server for `beta` when it offers `beta` —
the server (causal and left-total by construction) together with the
service guarantee. We take this as a predicate on a `Server`.

*Definition:* `S` is a min-plus server for `beta`

```lean
def IsMinPlusServer (beta : ℝ≥0 → ℝ≥0) (S : Server) :
    Prop :=
  OffersMinPlusService beta S
```

The _largest_ min-plus server for `beta` is the set of all causal pairs
meeting the service bound — pairs with $`A \ge D \ge A \ast \beta`.
Causality ($`D \le A`, the first conjunct) and the service bound make
up the relation; assembling it into a `Server` needs left-totality,
supplied as `htot`.

*Definition:* $`S_{\mathrm{mp}}(\beta) = \{\,(A, D) \mid A \ge D \ge A \ast \beta\,\}`

```lean
def minPlusServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧ infConvR p.1 beta ≤ p.2 }

theorem mem_minPlusServiceRel_iff
    {beta : ℝ≥0 → ℝ≥0} {p : Curve × Curve} :
    p ∈ minPlusServiceRel beta ↔
      p.2 ≤ p.1 ∧ infConvR p.1 beta ≤ p.2 :=
  Iff.rfl

def minPlusServer (beta : ℝ≥0 → ℝ≥0)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ minPlusServiceRel beta) :
    Server where
  rel := minPlusServiceRel beta
  causal _A _D hp := hp.1
  leftTotal A := htot A
```

A server lies inside the largest min-plus server for `beta` exactly
when it offers `beta` — the causality conjunct is automatic, since a
server is causal by construction.

*Theorem:* $`S \subseteq S_{\mathrm{mp}}(\beta) \iff S` offers $`\beta`

```lean
theorem subset_minPlusServiceRel_iff
    {S : Server} {beta : ℝ≥0 → ℝ≥0} :
    (∀ p ∈ S, p ∈ minPlusServiceRel beta) ↔
      OffersMinPlusService beta S := by
  constructor
  · intro h A D hp
    exact (h (A, D) hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p.1 p.2 hp⟩
```

Monotony of the service guarantee: if `S` offers the larger `beta'`, it
also offers any smaller `beta`. Since `beta ≤ beta'` gives
$`A \ast \beta \le A \ast \beta' \le D`, the smaller curve is still a
valid lower bound.

*Theorem:* $`\beta \le \beta' \;\wedge\; S \text{ offers } \beta' \implies S \text{ offers } \beta`

```lean
theorem OffersMinPlusService.mono
    {S : Server} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta ≤ beta') (hS : OffersMinPlusService beta' S) :
    OffersMinPlusService beta S :=
  fun A D hp =>
    le_trans (infConvR_mono_right A h) (hS A D hp)
```

The weakest service curve is the constant $`\beta_0 = 0`.

*Definition:* the zero service curve $`\beta_0(t) = 0`

```lean
def β₀ : ℝ≥0 → ℝ≥0 := fun _ => 0
```

Every server offers $`\beta_0`: then $`(A \ast \beta_0)(t) \le A(0) + 0
= 0` (using $`A(0) = 0`), so it lies below every output. This is the
weakest possible guarantee.

*Theorem:* every server offers the zero service curve $`\beta_0`

```lean
theorem offersMinPlusService_β₀ (S : Server) :
    OffersMinPlusService β₀ S := by
  intro A D _ t
  rw [infConvR_eq]
  refine le_trans
    (ciInf_le (OrderBot.bddBelow _) ⟨(0, t), by simp⟩) ?_
  show A 0 + β₀ t ≤ D t
  rw [A.zero]
  show (0 : ℝ≥0) + (0 : ℝ≥0) ≤ D t
  simp
```

# Backlogged periods

The second main service curve — the _strict_ service curve — is stated
over _backlogged periods_: intervals during which the system is never
empty, i.e. the arrival stays strictly above the departure. (Causality
gives $`A \ge D`; backlogged means the inequality is strict.)

*Definition:* `I` is a backlogged period for `(A, D)` — $`\forall t \in I,\ D(t) < A(t)`

```lean
def IsBacklogged (A D : Curve) (I : Set ℝ≥0) : Prop :=
  ∀ t ∈ I, D t < A t
```

The _start_ of the backlogged period of a time `t` is the last instant
up to `t` at which the system was empty ($`A = D`): the supremum of
those instants.

*Definition:* $`\mathrm{Start}_{A,D}(t) = \sup\,\{\, u \le t \mid A(u) = D(u) \,\}`

```lean
noncomputable def Start (A D : Curve) (t : ℝ≥0) : ℝ≥0 :=
  sSup { u | u ≤ t ∧ A u = D u }
```

The defining set is nonempty (the origin, where both curves vanish) and
bounded above by `t`, so the supremum is well-behaved; in particular
`Start t ≤ t`, and `Start` is monotone.

*Theorem:* basic facts: the defining set is nonempty, $`\mathrm{Start}\,t \le t`, and $`\mathrm{Start}` is monotone

```lean
theorem start_set_nonempty (A D : Curve) (t : ℝ≥0) :
    { u | u ≤ t ∧ A u = D u }.Nonempty :=
  ⟨0, by simp, by rw [A.zero, D.zero]⟩

theorem start_le (A D : Curve) (t : ℝ≥0) :
    Start A D t ≤ t :=
  csSup_le (start_set_nonempty A D t) (fun _ hx => hx.1)

theorem start_mono (A D : Curve) {t t' : ℝ≥0}
    (h : t ≤ t') : Start A D t ≤ Start A D t' :=
  csSup_le (start_set_nonempty A D t)
    (fun x hx =>
      le_csSup ⟨t', fun y hy => hy.1⟩
        ⟨le_trans hx.1 h, hx.2⟩)
```

_Property 1._ Any sub-interval of a backlogged period is backlogged —
immediate from the definition.

*Theorem:* a sub-interval of a backlogged period is backlogged

```lean
theorem IsBacklogged.subset {A D : Curve}
    {I I' : Set ℝ≥0} (h : IsBacklogged A D I)
    (hsub : I' ⊆ I) : IsBacklogged A D I' :=
  fun t ht => h t (hsub ht)
```

_Property 2._ For a causal pair, $`(\mathrm{Start}\,t, t]` is itself a
backlogged period: every instant after the start (and up to `t`) has
$`A > D`, since otherwise it would be an emptiness instant beyond the
supremum.

*Theorem:* $`(\mathrm{Start}\,t, t]` is a backlogged period

```lean
theorem isBacklogged_Ioc_start (A D : Curve)
    (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    IsBacklogged A D (Set.Ioc (Start A D t) t) := by
  intro u hu
  have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
    ⟨t, fun x hx => hx.1⟩
  rcases (hc u).lt_or_eq with h | h
  · exact h
  · exact absurd (le_csSup hbdd ⟨hu.2, h.symm⟩)
      (not_le.mpr hu.1)
```

_Property 3._ At the start of a backlogged period the system is empty,
$`A(\mathrm{Start}\,t) = D(\mathrm{Start}\,t)`. This rests on the
_left-continuity_ of the curves: if $`A > D` at the start, both stay so
just to its left, so emptiness instants could not accumulate there —
contradicting the supremum.

*Theorem:* $`A(\mathrm{Start}\,t) = D(\mathrm{Start}\,t)`

```lean
theorem A_start_eq_D_start (A D : Curve)
    (hc : ∀ x, D x ≤ A x) (t : ℝ≥0) :
    A (Start A D t) = D (Start A D t) := by
  set s := Start A D t with hs
  rcases (hc s).lt_or_eq with hlt | heq
  · exfalso
    have hbdd : BddAbove { u | u ≤ t ∧ A u = D u } :=
      ⟨t, fun x hx => hx.1⟩
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h | h
      · rw [h, A.zero, D.zero] at hlt
        exact absurd hlt (lt_irrefl 0)
      · exact h
    have hev : ∀ᶠ u in 𝓝[<] s, D u < A u :=
      (D.leftCont s).eventually_lt (A.leftCont s) hlt
    have hbasis :
        (𝓝[<] s).HasBasis (· < s) (Ioo · s) :=
      nhdsLT_basis_of_exists_lt ⟨0, hs0⟩
    rw [hbasis.eventually_iff] at hev
    obtain ⟨l, hls, hl⟩ := hev
    have hub : ∀ x ∈ { u | u ≤ t ∧ A u = D u },
        x ≤ l := by
      intro x hx
      by_contra hxl
      rw [not_le] at hxl
      rcases (le_csSup hbdd hx).lt_or_eq with hxlt | hxeq
      · have := hl ⟨hxl, hxlt⟩
        rw [hx.2] at this; exact absurd this (lt_irrefl _)
      · -- x = sSup = s with A x = D x, vs D s < A s
        subst hxeq
        exact absurd hx.2 (ne_of_gt hlt)
    exact absurd
      (csSup_le (start_set_nonempty A D t) hub)
      (not_le.mpr hls)
  · exact heq.symm
```

_Property 4._ The start is _constant_ on a backlogged period: any two
instants of the same (interval) period share a start. If two starts
differed, the larger would lie inside $`(\mathrm{Start}, t]`, a
backlogged period — yet by Property 3 the system is empty there, a
contradiction.

*Theorem:* $`\mathrm{Start}` is constant on a backlogged period

```lean
theorem start_const_of_backlogged (A D : Curve)
    (hc : ∀ x, D x ≤ A x)
    {I : Set ℝ≥0} (hI : IsBacklogged A D I)
    (hoc : I.OrdConnected)
    {t t' : ℝ≥0} (ht : t ∈ I) (ht' : t' ∈ I) :
    Start A D t = Start A D t' := by
  wlog hle : t ≤ t' generalizing t t'
  · exact (this ht' ht (not_le.mp hle).le).symm
  refine le_antisymm (start_mono A D hle) ?_
  have hst : Start A D t' ≤ t := by
    by_contra h
    rw [not_le] at h
    have hmem : Start A D t' ∈ I :=
      hoc.out ht ht' ⟨h.le, start_le A D t'⟩
    have := hI _ hmem
    rw [A_start_eq_D_start A D hc t'] at this
    exact absurd this (lt_irrefl _)
  exact le_csSup ⟨t, fun y hy => hy.1⟩
    ⟨hst, A_start_eq_D_start A D hc t'⟩
```

# Strict service curves

The _strict_ minimal service curve is the second main service notion.
It demands the service bound on _every backlogged period_: over a
backlogged $`(s, t]`, the departure grows by at least $`\beta(t - s)`.

*Definition:* `S` offers a strict service curve `beta` — $`\forall (s,t] \text{ backlogged},\ D(t) - D(s) \ge \beta(t - s)`

```lean
def OffersStrictService (beta : ℝ≥0 → ℝ≥0)
    (S : Server) : Prop :=
  ∀ A D : Curve, (A, D) ∈ S →
    ∀ s t, s ≤ t →
      IsBacklogged A D (Set.Ioc s t) →
        D s + beta (t - s) ≤ D t
```

The largest server offering a strict service curve `beta` is the set
of causal pairs meeting the bound on every backlogged period.

*Definition:* $`S_{\mathrm{strict}}(\beta) = \{\,(A, D) \mid A \ge D,\ \forall (s,t] \text{ backlogged},\ D(t) - D(s) \ge \beta(t-s)\,\}`

```lean
def strictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧
      ∀ s t, s ≤ t →
        IsBacklogged p.1 p.2 (Set.Ioc s t) →
          p.2 s + beta (t - s) ≤ p.2 t }

theorem subset_strictServiceRel_iff
    {S : Server} {beta : ℝ≥0 → ℝ≥0} :
    (∀ p ∈ S, p ∈ strictServiceRel beta) ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp
    exact (h (A, D) hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p.1 p.2 hp⟩
```

The zero curve $`\beta_0 = 0` is a strict service curve for every
server (departures are non-decreasing).

*Theorem:* every server offers the strict service curve $`\beta_0`

```lean
theorem offersStrictService_β₀ (S : Server) :
    OffersStrictService β₀ S := by
  intro A D _ s t hst _
  show D s + β₀ (t - s) ≤ D t
  show D s + (0 : ℝ≥0) ≤ D t
  rw [add_zero]
  exact D.mono hst
```

Monotony (the analogue of Proposition 5.6, point 3): a smaller strict
service curve is offered by at least as many servers.

*Theorem:* $`\beta' \le \beta \implies S_{\mathrm{strict}}(\beta) \subseteq S_{\mathrm{strict}}(\beta')`

```lean
theorem strictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    strictServiceRel beta ⊆ strictServiceRel beta' := by
  intro p hp
  refine ⟨hp.1, fun s t hst hbl => ?_⟩
  refine le_trans ?_ (hp.2 s t hst hbl)
  gcongr
  exact h _
```

The join (Proposition 5.6, point 1): offering two strict service
curves means offering their pointwise maximum.

*Theorem:* $`S \text{ offers } \beta \text{ and } \beta' \implies S \text{ offers } \beta \vee \beta'`

```lean
theorem offersStrictService_sup
    {S : Server} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : OffersStrictService beta S)
    (h' : OffersStrictService beta' S) :
    OffersStrictService
      (fun u => max (beta u) (beta' u)) S := by
  intro A D hp s t hst hbl
  show D s + max (beta (t-s)) (beta' (t-s)) ≤ D t
  rcases le_total (beta (t-s)) (beta' (t-s)) with hle | hle
  · rw [max_eq_right hle]; exact h' A D hp s t hst hbl
  · rw [max_eq_left hle]; exact h A D hp s t hst hbl
```

The output bound (equation 5.13): from $`(\mathrm{Start}\,t, t]` being
a backlogged period and $`A(\mathrm{Start}\,t) = D(\mathrm{Start}\,t)`,
the departure satisfies $`D(t) \ge A(\mathrm{Start}\,t) + \beta(t - \mathrm{Start}\,t)`.

*Theorem:* $`D(t) \ge A(\mathrm{Start}\,t) + \beta(t - \mathrm{Start}\,t)`

```lean
theorem strictService_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve) (hp : (A, D) ∈ strictServiceRel beta)
    (t : ℝ≥0) :
    A (Start A D t) + beta (t - Start A D t) ≤ D t := by
  have hc : ∀ x, D x ≤ A x := fun x => hp.1 x
  have hbl := isBacklogged_Ioc_start A D hc t
  have hbound := hp.2 (Start A D t) t (start_le A D t) hbl
  rw [A_start_eq_D_start A D hc t]
  exact hbound
```

# The strict service curve and its closure

Strict service curves carry a closure phenomenon (Proposition 5.6,
point 2): a strict service curve can be replaced by a _larger_ one, for
free. The mechanism is _concatenation_ — a backlogged period splits at
any interior point into two backlogged sub-periods, and the two service
bounds compose.

*Theorem:* concatenation — $`D(s) + \bigl(\beta(r - s) + \beta(t - r)\bigr) \le D(t)` over a backlogged $`(s,t]`

```lean
theorem strict_concat (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S)
    (A D : Curve) (hp : (A, D) ∈ S)
    {s r t : ℝ≥0} (hsr : s ≤ r) (hrt : r ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) :
    D s + (beta (r - s) + beta (t - r)) ≤ D t := by
  have b1 : D s + beta (r - s) ≤ D r :=
    hβ A D hp s r hsr
      (hbl.subset (Set.Ioc_subset_Ioc_right hrt))
  have b2 : D r + beta (t - r) ≤ D t :=
    hβ A D hp r t hrt
      (hbl.subset (Set.Ioc_subset_Ioc_left hsr))
  calc D s + (beta (r - s) + beta (t - r))
      = (D s + beta (r - s)) + beta (t - r) := by
        ring
    _ ≤ D r + beta (t - r) := by gcongr
    _ ≤ D t := b2
```

The closure of interest (Proposition 5.6, point 2) is the
_non-decreasing closure_ $`\beta_{\uparrow}(t) = \sup_{u \le t} \beta(u)`
of the chapter `Real convolutions of curves` — the least non-decreasing
curve above `beta`. The point is that a strict service curve can always
be replaced by its non-decreasing closure for free:
$`S_{\mathrm{strict}}(\beta) = S_{\mathrm{strict}}(\beta_{\uparrow})`.
The supremum-absorption lemma `add_ciSup_le` from that chapter is the
workhorse.

The closure upgrade: a server offering the strict service curve `beta`
automatically offers its non-decreasing closure. For each $`u \le t-s`,
the sub-period $`(s, s+u]` is backlogged, so $`D(s) + \beta(u) \le
D(s+u) \le D(t)`; taking the supremum over `u` absorbs into the bound.

*Theorem:* $`S \text{ offers } \beta \implies S \text{ offers } \beta_{\uparrow}`

```lean
theorem offersStrictService_ndClosure
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (ndClosure beta) S := by
  intro A D hp s t hst hbl
  show D s + ndClosure beta (t - s) ≤ D t
  unfold ndClosure
  refine add_ciSup_le _ _ _ (fun q => ?_)
  obtain ⟨u, (hu : u ≤ t - s)⟩ := q
  have hsu : s + u ≤ t := by
    have : s + u ≤ s + (t - s) := by gcongr
    rwa [add_tsub_cancel_of_le hst] at this
  have hb := hβ A D hp s (s + u) le_self_add
    (hbl.subset (Set.Ioc_subset_Ioc_right hsu))
  rw [show (s + u) - s = u by
      rw [add_comm]; exact add_tsub_cancel_right u s] at hb
  exact le_trans hb (D.mono hsu)
```

The reverse inclusion is monotony: `beta` lies below its closure (it is
the $`u = t` term), so offering $`\beta_{\uparrow}` offers `beta`. This
needs `beta` bounded on each initial interval, so that the supremum is
genuine. Together the two give the equality
$`S_{\mathrm{strict}}(\beta) = S_{\mathrm{strict}}(\beta_{\uparrow})`.

*Theorem:* $`S \text{ offers } \beta \iff S \text{ offers } \beta_{\uparrow}`

```lean
theorem offersStrictService_ndClosure_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    OffersStrictService (ndClosure beta) S ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_ndClosure beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact offersStrictService_ndClosure beta
```

# The super-additive closure of a strict service curve

The other closure of Proposition 5.6, point 2 is the _super-additive
closure_ $`\bar\beta^{*}`, built from the _super-convolution_ `superConv`
and its iterates `superPow` — both from the chapter `Real convolutions
of curves`. The first step already upgrades for free: each split
$`a + b = t - s` gives the interior point $`r = s + a`, where
concatenation supplies the two-term bound, and the supremum over splits
is absorbed.

*Theorem:* $`S \text{ offers } \beta \implies S \text{ offers } \beta \boxplus \beta`

```lean
theorem offersStrictService_superConv
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (superConv beta) S := by
  intro A D hp s t hst hbl
  show D s + superConv beta (t - s) ≤ D t
  refine add_superConv_le _ _ _ _ (fun q => ?_)
  obtain ⟨⟨a, b⟩, (hab : a + b = t - s)⟩ := q
  have hsum : s + (a + b) = t := by
    rw [hab, add_tsub_cancel_of_le hst]
  have hsa : s + a ≤ t :=
    le_trans (by gcongr; exact le_self_add) hsum.le
  have hrs : (s + a) - s = a := by
    rw [add_comm]; exact add_tsub_cancel_right a s
  have htr : t - (s + a) = b := by
    rw [← hsum,
      show s + (a + b) = (s + a) + b by ring,
      add_tsub_cancel_left]
  have hcc :=
    strict_concat beta hβ A D hp le_self_add hsa hbl
  rw [hrs, htr] at hcc
  exact hcc
```

Offering `beta` is preserved by every iterate, by induction on the
two-step upgrade; the supremum over `n` is then absorbed, so a server
offering `beta` offers the whole super-additive closure.

*Theorem:* $`S \text{ offers } \beta \implies S \text{ offers } \beta^{(n)}` and $`S \text{ offers } \bar\beta^{*}`

```lean
theorem offers_superPow (beta : ℝ≥0 → ℝ≥0)
    {S : Server} (hβ : OffersStrictService beta S)
    (n : ℕ) :
    OffersStrictService (superPow beta n) S := by
  induction n with
  | zero => exact hβ
  | succ n ih => exact offersStrictService_superConv _ ih

theorem offersStrictService_saClosure
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (saClosure beta) S := by
  intro A D hp s t hst hbl
  show D s + saClosure beta (t - s) ≤ D t
  unfold saClosure
  refine add_ciSup_le _ _ _ (fun n => ?_)
  exact offers_superPow beta hβ n A D hp s t hst hbl
```

The reverse inclusion is monotony: `beta` is the $`n = 0` iterate, so
it lies below $`\bar\beta^{*}`, and offering $`\bar\beta^{*}` offers
`beta`. As with the non-decreasing closure, this needs the iterates
bounded on each initial point, giving the equality
$`S_{\mathrm{strict}}(\beta) = S_{\mathrm{strict}}(\bar\beta^{*})`.

*Theorem:* $`S \text{ offers } \beta \iff S \text{ offers } \bar\beta^{*}`

```lean
theorem offersStrictService_saClosure_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hbdd : ∀ t,
      BddAbove (Set.range (fun n => superPow beta n t))) :
    OffersStrictService (saClosure beta) S ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_saClosure beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact offersStrictService_saClosure beta
```

# Arrival curves

An output cumulative function allows `sigma` as an arrival curve when
it lies below its convolution with `sigma`.

*Definition:* `D` allows `sigma` as an arrival curve

```lean
def AllowsArrivalCurve (D sigma : F) : Prop :=
  D ≤ₙ conv D sigma
```

The defining inequality is equivalent to a kernel inequality for every
split `u + s = t`. This form is the workhorse for the closure result.

*Theorem:* $`D \text{ allows } \sigma \iff \forall\, u+s=t,\ D(u) \otimes \sigma(s) \preceq D(t)`

```lean
theorem allowsArrivalCurve_iff_kernel
    (D sigma : F) :
    AllowsArrivalCurve D sigma ↔
      ∀ u s t, u + s = t →
        D u ⊗ₒ sigma s ≼ₒ D t := by
  constructor
  · intro h u s t hus
    have hc : conv D sigma t ≼ₒ D t :=
      (natLe_iff D (conv D sigma)).mp h t
    have hterm :
        D u ⊗ₒ sigma s ≼ₒ conv D sigma t := by
      rw [conv_apply]
      exact CompleteDioid.le_sSup _ _
        ⟨u, s, hus, rfl⟩
    exact le_trans hterm hc
  · intro h
    unfold AllowsArrivalCurve
    rw [natLe_iff]
    intro t
    rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    exact h u s t hus
```

# Shapers

A _shaper_ is a server whose every output allows `sigma` as an arrival
curve.

*Definition:* `S` is a `sigma`-shaper

```lean
def IsShaper (S : Server) (sigma : F) : Prop :=
  ∀ p ∈ S, AllowsArrivalCurve (↑p.2 : F) sigma
```

The largest causal server satisfying the shaper constraint is the set
of all pairs whose output is below the input and whose output allows
`sigma` as an arrival curve.

*Definition:* the largest `sigma`-shaper relation and server

The shaper _relation_ is the set of all causal pairs whose output
allows `sigma`. It carries the causality proof on its own; assembling
it into a `Server` additionally needs left-totality, supplied as a
hypothesis `htot` — exactly the obligation that the curve class be
closed under the shaping construction.

```lean
def shaperRel (sigma : F) : Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧
      AllowsArrivalCurve (↑p.2 : F) sigma }

theorem mem_shaperRel_iff
    {sigma : F} {p : Curve × Curve} :
    p ∈ shaperRel sigma ↔
      p.2 ≤ p.1 ∧
        AllowsArrivalCurve (↑p.2 : F) sigma :=
  Iff.rfl

def shaperServer (sigma : F)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ shaperRel sigma) :
    Server where
  rel := shaperRel sigma
  causal := fun _A _D hp => hp.1
  leftTotal A := htot A
```

A server lies inside the largest `sigma`-shaper exactly when it is a
`sigma`-shaper — the causality conjunct is automatic, since a server is
causal by construction.

*Theorem:* $`S \subseteq S_{\mathrm{sh}}(\sigma) \iff S` is a $`\sigma`-shaper

```lean
theorem subset_shaperRel_iff
    {S : Server} {sigma : F} :
    (∀ p ∈ S, p ∈ shaperRel sigma) ↔
      IsShaper S sigma := by
  constructor
  · intro h p hp
    exact (h p hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p hp⟩
```

# Shaping closure

The _sub-additive closure_ $`\sigma^{\star}`, its convolution powers
`convPow`, and the Kleene-star theory were developed in the chapter
`The sub-additive closure`. Here we relate the closure to the shaper
constructions through the natural order and the arrival-curve kernel.

The closure is below the original curve in the natural order because
the original curve is one of the powers.

*Theorem:* $`\sigma^\star \le_n \sigma`

```lean
theorem subadditiveClosure_natLe_self
    (sigma : F) : sigma⋆ ≤ₙ sigma := by
  intro t
  have h :
      sigma t ≼ₒ subadditiveClosure sigma t := by
    dsimp [subadditiveClosure]
    have h1 :
        convPow sigma 1 t ≼ₒ
          CompleteDioid.iSup
            (fun n : ℕ => convPow sigma n t) :=
      CompleteDioid.le_iSup
        (fun n : ℕ => convPow sigma n t) 1
    simpa [convPow_one] using h1
  exact (RplusMin.le_iff (sigma t)
    (subadditiveClosure sigma t)).mp h
```

The kernel inequality propagates along every convolution power.

*Theorem:* if $`D` allows $`\sigma`, then $`\forall\, u+s=t,\ D(u) \otimes \sigma^{\ast n}(s) \preceq D(t)`

```lean
theorem kernel_convUnit (D : F) :
    ∀ u s t, u + s = t →
      D u ⊗ₒ convUnit s ≼ₒ D t := by
  intro u s t hus
  by_cases hs : s = 0
  · have hu : u = t := by
      rw [← hus, hs, add_zero]
    rw [convUnit, if_pos hs, hu]
    exact le_of_eq
      (Algebra.MulMonoid.otimes_one (D t))
  · rw [convUnit, if_neg hs]
    rw [Algebra.Semiring.otimes_eps]
    exact bot_le

theorem kernel_convPow_of_allows
    {D sigma : F}
    (hD : AllowsArrivalCurve D sigma) :
    ∀ n u s t, u + s = t →
      D u ⊗ₒ convPow sigma n s ≼ₒ D t := by
  have hsigma :=
    (allowsArrivalCurve_iff_kernel D sigma).mp hD
  intro n
  induction n with
  | zero =>
      exact kernel_convUnit D
  | succ n ih =>
      intro u s t hus
      rw [convPow, conv_apply,
        CompleteDioid.mul_sSup]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨y, ⟨a, b, hab, rfl⟩, rfl⟩
      change D u ⊗ₒ
          (convPow sigma n a ⊗ₒ sigma b) ≼ₒ D t
      rw [← Algebra.MulMonoid.otimes_assoc]
      have hleft :
          (D u ⊗ₒ convPow sigma n a) ⊗ₒ
              sigma b ≼ₒ
            D (u + a) ⊗ₒ sigma b :=
        mul_le_mul_right (ih u a (u + a) rfl)
          (sigma b)
      have hsum : (u + a) + b = t := by
        rw [add_assoc, hab, hus]
      exact le_trans hleft
        (hsigma (u + a) b t hsum)
```

Therefore allowing `sigma` and allowing its closure are equivalent.

*Theorem:* $`D \text{ allows } \sigma^\star \iff D \text{ allows } \sigma`

```lean
theorem allowsArrivalCurve_closure_iff
    (D sigma : F) :
    AllowsArrivalCurve D sigma⋆ ↔
      AllowsArrivalCurve D sigma := by
  constructor
  · intro h
    exact NatLe.trans h
      (conv_natLe_right D
        (subadditiveClosure_natLe_self sigma))
  · intro h
    rw [allowsArrivalCurve_iff_kernel]
    intro u s t hus
    rw [subadditiveClosure,
      CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ ?_
    intro n
    exact kernel_convPow_of_allows h n u s t hus
```

# Properties of shapers

The largest `sigma`-shaper is unchanged by replacing `sigma` with its
closure.

*Theorem:* $`S_{\mathrm{sh}}(\sigma) = S_{\mathrm{sh}}(\sigma^\star)`

```lean
theorem shaperRel_closure
    (sigma : F) :
    shaperRel sigma = shaperRel sigma⋆ := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : F) sigma).2 hp.2⟩
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : F) sigma).1 hp.2⟩

theorem IsShaper.closure
    {S : Server} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ := by
  intro p hp
  exact (allowsArrivalCurve_closure_iff
    (↑p.2 : F) sigma).2 (hS p hp)

example
    (sigma : F) :
    shaperRel sigma = shaperRel sigma⋆ :=
  shaperRel_closure sigma

example
    {S : Server} {sigma : F}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ :=
  IsShaper.closure hS
```

Larger arrival curves preserve the shaper property, and their largest
servers contain the smaller-curve largest server.

*Theorem:* if $`\sigma \le_n \sigma'`, then $`S_{\mathrm{sh}}(\sigma) \subseteq S_{\mathrm{sh}}(\sigma')`

```lean
theorem IsShaper.of_natLe
    {S : Server}
    {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' := by
  intro p hp
  exact NatLe.trans (hS p hp)
    (conv_natLe_right (↑p.2 : F) h)

theorem shaperRel_mono
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    shaperRel sigma ⊆ shaperRel sigma' := by
  intro p hp
  exact ⟨hp.1,
    NatLe.trans hp.2
      (conv_natLe_right (↑p.2 : F) h)⟩

example
    {sigma sigma' : F}
    (h : sigma ≤ₙ sigma') :
    shaperRel sigma ⊆ shaperRel sigma' :=
  shaperRel_mono h

example
    {S : Server} {sigma sigma' : F}
    (hS : IsShaper S sigma)
    (h : sigma ≤ₙ sigma') :
    IsShaper S sigma' :=
  IsShaper.of_natLe hS h
```

# The greedy shaper

A _shaper_ constrains its output to allow `sigma` as an arrival curve.
A _greedy_ shaper does more: it shapes the output as tightly as
possible, fixing it to be exactly the convolution of the input with
`sigma`. Each output is then `sigma`-constrained by construction, and
the shaper is _greedy_ in that it delays the input no more than
forced.

The relation itself places no constraint on `sigma`: a server is a
`sigma`-greedy shaper when every admissible pair has output exactly the
convolution of the input with `sigma`. The regularity of `sigma` —
sub-additivity, left-continuity, nullity at the origin — enters only
where it is needed: to make the greedy shaper a well-defined _server_
(its output causal and a valid cumulative function).

A server is a `sigma`-greedy shaper when every admissible pair has
output exactly the convolution of the input with `sigma`.

*Definition:* $`S \text{ is a } \sigma\text{-greedy shaper} \iff \forall (A, D) \in S,\ D = A \ast \sigma`

```lean
def IsGreedyShaper
    (S : Server) (sigma : F) : Prop :=
  ∀ p ∈ S, (↑p.2 : F) = conv (↑p.1 : F) sigma
```

To form the greedy shaper _as a server_, its output must be causal —
the departure below the arrival, $`A \ast \sigma \le_n A`. This holds
exactly when `sigma` is null at the origin: the split $`t = t + 0`
contributes the term $`A(t) \otimes \sigma(0) = A(t)`, so the
convolution never exceeds `A`. Sub-additivity and left-continuity are
not needed for causality; nullity at the origin is.

*Theorem:* if $`\sigma(0) = e` then $`A \ast \sigma \le_n A`

```lean
theorem conv_natLe_self_of_zeroAtOrigin
    (A sigma : F) (h0 : sigma 0 = eₒ) :
    conv A sigma ≤ₙ A := by
  rw [natLe_iff]
  intro t
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨t, 0, add_zero t, rfl⟩)
  show A t ≼ₒ A t ⊗ₒ sigma 0
  rw [h0]
  exact le_of_eq (MulMonoid.otimes_one (A t)).symm
```

The greedy _relation_ is the set of all pairs whose departure is the
convolution of the arrival with `sigma`. It is causal when `sigma` is
null at the origin (by the lemma above); assembling it into a `Server`
additionally needs left-totality, supplied as a hypothesis `htot`.

*Definition:* $`S_{\mathrm{gsh}}(\sigma) = \{\,(A, D) \mid D = A \ast \sigma\,\}`

```lean
def greedyRel (sigma : F) : Set (Curve × Curve) :=
  { p | (↑p.2 : F) = conv (↑p.1 : F) sigma }

theorem mem_greedyRel_iff
    {sigma : F} {p : Curve × Curve} :
    p ∈ greedyRel sigma ↔
      (↑p.2 : F) = conv (↑p.1 : F) sigma :=
  Iff.rfl

def greedyShaper
    (sigma : F) (h0 : sigma 0 = eₒ)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ greedyRel sigma) :
    Server where
  rel := greedyRel sigma
  causal A D hp := by
    rw [Curve.le_iff_natLe]
    rw [(hp : (↑D : F) = conv (↑A : F) sigma)]
    exact conv_natLe_self_of_zeroAtOrigin (↑A) sigma h0
  leftTotal A := htot A
```

A `sigma`-greedy shaper is a server whose every member equals its own
convolution; the greedy relation is the largest such set.

*Theorem:* $`S \text{ greedy} \iff S \subseteq S_{\mathrm{gsh}}(\sigma)`

```lean
theorem isGreedyShaper_iff_subset
    {S : Server} {sigma : F} :
    IsGreedyShaper S sigma ↔
      ∀ p ∈ S, p ∈ greedyRel sigma :=
  Iff.rfl
```

# The greedy shaper is a sigma-shaper

A sub-additive curve allows itself as an arrival curve: the kernel
inequality $`\sigma(u) \otimes \sigma(s) \preceq \sigma(u + s)` is
exactly the condition for $`\sigma` to allow $`\sigma`.

*Definition:* dioid sub-additivity of a curve, $`\sigma(u) \otimes \sigma(s) \preceq \sigma(u + s)`

```lean
def IsSubadditiveF (sigma : F) : Prop :=
  ∀ u s : ℝ≥0, sigma u ⊗ₒ sigma s ≼ₒ sigma (u + s)
```

*Theorem:* a sub-additive curve allows itself

```lean
theorem allowsArrivalCurve_self_of_subadd
    {sigma : F} (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve sigma sigma := by
  rw [allowsArrivalCurve_iff_kernel]
  intro u s t hus
  rw [← hus]
  exact hsub u s
```

The point of the construction is that the output is `sigma`-shaped.
Under sub-additivity the convolution `A ∗ sigma` allows `sigma`:
shifting the constraint through associativity and monotonicity,
$`A \ast \sigma \le_n A \ast (\sigma \ast \sigma) = (A \ast \sigma) \ast \sigma`.

*Theorem:* if $`\sigma` is sub-additive then $`A \ast \sigma` allows $`\sigma`

```lean
theorem allowsArrivalCurve_conv_of_subadd
    (A : F) {sigma : F} (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve (conv A sigma) sigma := by
  have h : conv A sigma ≤ₙ conv A (conv sigma sigma) :=
    conv_natLe_right A
      (allowsArrivalCurve_self_of_subadd hsub)
  rw [← conv_assoc] at h
  exact h
```

Hence every output of a greedy shaper over a sub-additive curve is a
`sigma`-shaper output.

*Theorem:* a greedy shaper over a sub-additive curve is a $`\sigma`-shaper

```lean
theorem IsGreedyShaper.isShaper
    {S : Server} {sigma : F}
    (hsub : IsSubadditiveF sigma)
    (hS : IsGreedyShaper S sigma) :
    IsShaper S sigma := by
  intro p hp
  rw [hS p hp]
  exact allowsArrivalCurve_conv_of_subadd (↑p.1) hsub
```

```lean
end VerifiedWiki
```
