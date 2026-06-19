import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Ultimately pseudo-periodic functions (UPP)
The function class that makes (min,plus) operators *computable*: a function is **ultimately
pseudo-periodic** when beyond a rank `T` it repeats with period `d` up to a constant increment `c`
(`f (t + d) = f t + c` for `t ≥ T`). Together with piecewise-linearity on `[0, T+d)` this means `f`
is determined by *finite* data — the basis of the finite (quadruplet) representation of §4.3.2 and
the algorithmic min-plus calculus.

This file is the semantic layer: the property `IsUPPWith`/`IsUPP` and the **stability** results
(the heart of Theorem 4.3) — the class is closed under `+`, `-`, `⊓`, `⊔` (Lemmas 4.2, 4.3). The
concrete finite data structure + executable operators build on top of this. -/

namespace DeepWiki

open scoped NNReal

variable {V : Type*}

/-- `f` is **ultimately pseudo-periodic with rank `T`, period `d`, increment `c`**: beyond `T`,
advancing time by `d` raises the value by `c` — `∀ t ≥ T, f (t + d) = f t + c`. The finite data
`(T, d, c)` plus the values on `[0, T+d)` then determine `f` everywhere. -/
def IsUPPWith [Add V] (f : ℝ≥0 → V) (T d : ℝ≥0) (c : V) : Prop :=
  0 < d ∧ ∀ t, T ≤ t → f (t + d) = f t + c

/-- `f` is **ultimately pseudo-periodic** (UPP): it admits some rank, period and increment. -/
def IsUPP [Add V] (f : ℝ≥0 → V) : Prop := ∃ T d c, IsUPPWith f T d c

/-- The period of a pseudo-periodic function is positive. -/
theorem IsUPPWith.period_pos [Add V] {f : ℝ≥0 → V} {T d c} (h : IsUPPWith f T d c) : 0 < d := h.1

/-- The pseudo-period step (elimination): `f (t + d) = f t + c` past the rank. -/
theorem IsUPPWith.step [Add V] {f : ℝ≥0 → V} {T d c} (h : IsUPPWith f T d c)
    {t : ℝ≥0} (ht : T ≤ t) : f (t + d) = f t + c := h.2 t ht

/-- An `IsUPPWith` witness gives `IsUPP`. -/
theorem IsUPPWith.isUPP [Add V] {f : ℝ≥0 → V} {T d c} (h : IsUPPWith f T d c) : IsUPP f :=
  ⟨T, d, c, h⟩

/-- The rank can be raised: pseudo-periodicity past `T` holds past any larger `T'`. -/
theorem IsUPPWith.mono_rank [Add V] {f : ℝ≥0 → V} {T T' d c} (h : IsUPPWith f T d c)
    (hT : T ≤ T') : IsUPPWith f T' d c :=
  ⟨h.1, fun t ht => h.2 t (hT.trans ht)⟩

/-- Iterating the pseudo-period: `f (t + n • d) = f t + n • c` past the rank, for every `n`. -/
theorem IsUPPWith.iterate [AddMonoid V] {f : ℝ≥0 → V} {T d c} (h : IsUPPWith f T d c)
    (n : ℕ) {t : ℝ≥0} (ht : T ≤ t) : f (t + n • d) = f t + n • c := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : T ≤ t + k • d := ht.trans le_self_add
    calc f (t + (k + 1) • d) = f (t + k • d + d) := by rw [succ_nsmul, ← add_assoc]
      _ = f (t + k • d) + c := h.2 _ hk
      _ = f t + k • c + c := by rw [ih]
      _ = f t + (k + 1) • c := by rw [succ_nsmul, add_assoc]

/-- The period may be scaled by any positive natural: `n • d` is also a period (increment `n • c`).
This is the rescaling that lets functions with commensurable periods be put on a common period. -/
theorem IsUPPWith.nsmul_period [AddMonoid V] {f : ℝ≥0 → V} {T d c} (h : IsUPPWith f T d c)
    {n : ℕ} (hn : n ≠ 0) : IsUPPWith f T (n • d) (n • c) :=
  ⟨nsmul_pos h.1 hn, fun _ ht => h.iterate n ht⟩

/-- **Lemma 4.2** (addition), common-period form. The sum of two pseudo-periodic functions sharing
a period `d` is pseudo-periodic with period `d`, rank `max T₁ T₂` and increment `c₁ + c₂`. -/
theorem IsUPPWith.add [AddCommMonoid V] {f g : ℝ≥0 → V} {T₁ T₂ d c₁ c₂}
    (hf : IsUPPWith f T₁ d c₁) (hg : IsUPPWith g T₂ d c₂) :
    IsUPPWith (fun t => f t + g t) (max T₁ T₂) d (c₁ + c₂) := by
  refine ⟨hf.1, fun t ht => ?_⟩
  have h1 := hf.2 t ((le_max_left _ _).trans ht)
  have h2 := hg.2 t ((le_max_right _ _).trans ht)
  simp only [h1, h2]; abel

/-- **Lemma 4.3** (minimum), equal-increment form. The pointwise minimum of two pseudo-periodic
functions sharing a period `d` and increment `c` is pseudo-periodic with period `d`, increment `c`
and rank `max T₁ T₂` — the book's case `d_g c_f = d_f c_g`. -/
theorem IsUPPWith.min [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    {f g : ℝ≥0 → V} {T₁ T₂ d c}
    (hf : IsUPPWith f T₁ d c) (hg : IsUPPWith g T₂ d c) :
    IsUPPWith (fun t => min (f t) (g t)) (max T₁ T₂) d c := by
  refine ⟨hf.1, fun t ht => ?_⟩
  have h1 := hf.2 t ((le_max_left _ _).trans ht)
  have h2 := hg.2 t ((le_max_right _ _).trans ht)
  simp only [h1, h2]
  rcases le_total (f t) (g t) with h | h
  · rw [min_eq_left h, min_eq_left (add_le_add_left h c)]
  · rw [min_eq_right h, min_eq_right (add_le_add_left h c)]

/-- **Lemma 4.3** (maximum), equal-increment form. The pointwise maximum of two pseudo-periodic
functions sharing a period `d` and increment `c` is pseudo-periodic with period `d` and
increment `c`. -/
theorem IsUPPWith.max [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    {f g : ℝ≥0 → V} {T₁ T₂ d c}
    (hf : IsUPPWith f T₁ d c) (hg : IsUPPWith g T₂ d c) :
    IsUPPWith (fun t => max (f t) (g t)) (max T₁ T₂) d c := by
  refine ⟨hf.1, fun t ht => ?_⟩
  have h1 := hf.2 t ((le_max_left _ _).trans ht)
  have h2 := hg.2 t ((le_max_right _ _).trans ht)
  simp only [h1, h2]
  rcases le_total (f t) (g t) with h | h
  · rw [max_eq_right h, max_eq_right (add_le_add_left h c)]
  · rw [max_eq_left h, max_eq_left (add_le_add_left h c)]

end DeepWiki
