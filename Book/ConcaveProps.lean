import Book.Concave
import Book.Additivity
import Book.ClosureEReal
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Closure properties of concave curves
Stability of `IsConcaveEReal` curves `ℝ≥0 → EReal` under the curve operations
(pointwise sum, `min`, sub-additivity, the convolution decomposition, the
sub-additive closure). `EReal` addition is monotone via Mathlib's `add_le_add`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Pointwise `min` (`EReal` `⊓`) of two concave curves is concave: each scaled
chord summand of `f ⊓ g` is below the corresponding summand of `f` and of `g`,
and `EReal` addition is monotone, so the combined chord lies below both `f`'s
and `g`'s chord, hence below their `min`. -/
theorem IsConcaveEReal.inf (f g : ℝ≥0 → EReal) (hf : IsConcaveEReal f) (hg : IsConcaveEReal g) :
    IsConcaveEReal (f ⊓ g) := by
  intro s t p hp
  simp only [Pi.inf_apply]
  refine le_inf ?_ ?_
  · refine le_trans ?_ (hf s t p hp)
    exact add_le_add
      (mul_le_mul_of_nonneg_left inf_le_left (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left inf_le_left (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))
  · refine le_trans ?_ (hg s t p hp)
    exact add_le_add
      (mul_le_mul_of_nonneg_left inf_le_right (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left inf_le_right (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))

/-- Pointwise sum of two concave curves is concave. The chord weights enter as
finite, nonneg `ℝ→EReal` coercions, so `EReal` left-distributivity expands each
weighted sum unconditionally; the four scaled summands then regroup by the
`AddCommMonoid` law `add_add_add_comm`, and `EReal` addition is monotone — so
no finiteness side condition (and hence no `(+∞)+(−∞)` exclusion) is required. -/
theorem IsConcaveEReal.add (f g : ℝ≥0 → EReal) (hf : IsConcaveEReal f) (hg : IsConcaveEReal g) :
    IsConcaveEReal (f + g) := by
  intro s t p hp
  have hp0 : (0 : EReal) ≤ ((p : ℝ) : EReal) := by exact_mod_cast p.coe_nonneg
  have hq0 : (0 : EReal) ≤ (((1 - p : ℝ≥0) : ℝ) : EReal) := by
    exact_mod_cast (1 - p : ℝ≥0).coe_nonneg
  have hptop : ((p : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hqtop : (((1 - p : ℝ≥0) : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hchf := hf s t p hp
  have hchg := hg s t p hp
  show ((p : ℝ) : EReal) * (f s + g s)
      + (((1 - p : ℝ≥0) : ℝ) : EReal) * (f t + g t)
      ≤ f (p * s + (1 - p) * t) + g (p * s + (1 - p) * t)
  rw [EReal.left_distrib_of_nonneg_of_ne_top hp0 hptop,
      EReal.left_distrib_of_nonneg_of_ne_top hq0 hqtop,
      add_add_add_comm]
  exact add_le_add hchf hchg

/-- A concave curve with `0 ≤ f 0` is subadditive: `f (u + s) ≤ f u + f s`.
The chord argument places `u`, `s` as convex combinations of `u + s` and `0`,
then drops the nonneg `f 0` terms. -/
theorem IsConcaveEReal.isSubadditive
    (f : ℝ≥0 → EReal) (hf : IsConcaveEReal f) (h0 : (0 : EReal) ≤ f 0) :
    IsSubadditive f := by
  intro u s
  obtain hT0 | hT := eq_or_ne (u + s) 0
  · -- `u + s = 0` forces `u = s = 0`, so the claim is `f 0 ≤ f 0 + f 0`,
    -- which follows from `0 ≤ f 0` (drop a nonneg `f 0` on the right).
    obtain ⟨rfl, rfl⟩ := add_eq_zero.1 hT0
    have : f 0 + (0 : EReal) ≤ f 0 + f 0 :=
      add_le_add (le_refl _) h0
    simpa using this
  · set T : ℝ≥0 := u + s with hTdef
    have hTpos : 0 < T := pos_iff_ne_zero.2 hT
    -- chord weights `p = u/T`, `q = s/T`
    set p : ℝ≥0 := u / T with hpdef
    set q : ℝ≥0 := s / T with hqdef
    have hpq : p + q = 1 := by
      rw [← NNReal.coe_inj]
      rw [NNReal.coe_add, hpdef, hqdef, NNReal.coe_div, NNReal.coe_div,
        ← add_div, ← NNReal.coe_add, ← hTdef, NNReal.coe_one,
        div_self (by exact_mod_cast hT)]
    have hp1 : p ≤ 1 := by rw [← hpq]; exact le_self_add
    have hq1 : q ≤ 1 := by rw [← hpq]; exact le_add_self
    have h1p : (1 : ℝ≥0) - p = q := by
      rw [← hpq]; simp
    have h1q : (1 : ℝ≥0) - q = p := by
      rw [← hpq]; simp
    -- domain points: `p*T = u`, `q*T = s`
    have hpT : p * T = u := by
      rw [hpdef, div_mul_cancel₀]; exact hT
    have hqT : q * T = s := by
      rw [hqdef, div_mul_cancel₀]; exact hT
    -- the two chord inequalities at points `T, 0`
    have hc1 := hf T 0 p hp1
    have hc2 := hf T 0 q hq1
    rw [h1p, mul_zero, add_zero, hpT] at hc1
    rw [h1q, mul_zero, add_zero, hqT] at hc2
    -- now `hc1 : ↑p*f T + ↑q*f 0 ≤ f u`, `hc2 : ↑q*f T + ↑p*f 0 ≤ f s`
    -- nonneg finite coercions of the weights into `EReal`
    have hpc : (0 : EReal) ≤ ((p : ℝ) : EReal) := by exact_mod_cast p.coe_nonneg
    have hqc : (0 : EReal) ≤ ((q : ℝ) : EReal) := by exact_mod_cast q.coe_nonneg
    -- `↑p + ↑q = 1` in `EReal`
    have hpqE : ((p : ℝ) : EReal) + ((q : ℝ) : EReal) = 1 := by
      rw [← EReal.coe_add]
      have : (p : ℝ) + (q : ℝ) = ((p + q : ℝ≥0) : ℝ) := by push_cast; ring
      rw [this, hpq]; simp
    -- `f T = ↑p*f T + ↑q*f T` and `f 0 = ↑q*f 0 + ↑p*f 0`
    have hsplitT : f (u + s) = ((p : ℝ) : EReal) * f T + ((q : ℝ) : EReal) * f T := by
      rw [← EReal.right_distrib_of_nonneg hpc hqc, hpqE, one_mul, ← hTdef]
    have hsplit0 : f 0 = ((q : ℝ) : EReal) * f 0 + ((p : ℝ) : EReal) * f 0 := by
      rw [← EReal.right_distrib_of_nonneg hqc hpc, add_comm ((q : ℝ) : EReal), hpqE,
        one_mul]
    -- regroup `f(u+s) + f 0` into the two chord left-hand sides
    have hregroup : f (u + s) + f 0
        = (((p : ℝ) : EReal) * f T + ((q : ℝ) : EReal) * f 0)
            + (((q : ℝ) : EReal) * f T + ((p : ℝ) : EReal) * f 0) := by
      conv_lhs => rw [hsplitT, hsplit0]
      rw [add_add_add_comm]
    -- `f 0` terms are nonneg, so `f(u+s) ≤ f(u+s) + f 0 ≤ f u + f s`
    calc f (u + s)
        = f (u + s) + 0 := (add_zero _).symm
      _ ≤ f (u + s) + f 0 := add_le_add (le_refl _) h0
      _ = (((p : ℝ) : EReal) * f T + ((q : ℝ) : EReal) * f 0)
            + (((q : ℝ) : EReal) * f T + ((p : ℝ) : EReal) * f 0) := hregroup
      _ ≤ f u + f s := add_le_add hc1 hc2

/-- Adding a finite real constant commutes with an `EReal` infimum:
`(⨅ i, u i) + ↑c = ⨅ i, (u i + ↑c)`. The `≤` direction uses that `↑c` is
`AddLECancellable` (so `· − ↑c` undoes `· + ↑c` even at `±∞`). -/
theorem iInf_add_coe {ι : Type*} [Nonempty ι] (u : ι → EReal) (c : ℝ) :
    (⨅ i, u i) + (c : EReal) = ⨅ i, (u i + (c : EReal)) := by
  apply le_antisymm
  · exact le_iInf fun i => add_le_add (iInf_le u i) (le_refl _)
  · have hle : (⨅ i, (u i + (c:EReal))) - (c:EReal) ≤ ⨅ i, u i := by
      refine le_iInf fun i => ?_
      calc (⨅ j, (u j + (c:EReal))) - (c:EReal)
          ≤ (u i + (c:EReal)) - (c:EReal) := EReal.sub_le_sub (iInf_le _ i) (le_refl _)
        _ = u i := EReal.add_sub_cancel_right
    calc (⨅ i, (u i + (c:EReal)))
        = ((⨅ i, (u i + (c:EReal))) - (c:EReal)) + (c:EReal) := EReal.sub_add_cancel.symm
      _ ≤ (⨅ i, u i) + (c:EReal) := add_le_add hle (le_refl _)

/-- A finite-constant curve `Function.const _ ↑c` is concave: its chord weights
sum to `1`, so every chord equals `↑c` (concavity holds with equality). -/
theorem isIsConcaveERealReal_const (c : ℝ) : IsConcaveEReal (Function.const ℝ≥0 (c : EReal)) := by
  intro s t p hp
  show ((p : ℝ) : EReal) * (c:EReal) + (((1 - p : ℝ≥0) : ℝ) : EReal) * (c:EReal) ≤ (c:EReal)
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  apply le_of_eq
  congr 1
  have hsum : (p:ℝ) + ((1-p:ℝ≥0):ℝ) = 1 := by
    rw [NNReal.coe_sub hp, NNReal.coe_one]; ring
  have : (p:ℝ)*c + ((1-p:ℝ≥0):ℝ)*c = ((p:ℝ)+((1-p:ℝ≥0):ℝ))*c := by ring
  rw [this, hsum, one_mul]

/-- Subtracting a finite real constant preserves concavity: `f − const ↑a`
is concave when `f` is (it is `f` plus the concave constant `const ↑(−a)`). -/
theorem IsIsConcaveERealReal.sub_const (f : ℝ≥0 → EReal) (hf : IsConcaveEReal f) (a : ℝ) :
    IsConcaveEReal (f - Function.const ℝ≥0 (a:EReal)) := by
  have : (f - Function.const ℝ≥0 (a:EReal))
      = f + Function.const ℝ≥0 ((-a:ℝ):EReal) := by
    funext x; show f x - (a:EReal) = f x + ((-a:ℝ):EReal); rw [EReal.coe_neg]; rfl
  rw [this]
  exact IsConcaveEReal.add f (Function.const ℝ≥0 ((-a:ℝ):EReal)) hf (isIsConcaveERealReal_const (-a))

/-- Subtracting a finite real constant preserves finiteness on the positive
ray: `f − const ↑a` is `FiniteOnPos` when `f` is. -/
theorem FiniteOnPos_sub_const (f : ℝ≥0 → EReal) (hf : FiniteOnPos f) (a : ℝ) :
    FiniteOnPos (f - Function.const ℝ≥0 (a:EReal)) := by
  intro x hx
  show f x - (a:EReal) ≠ ⊤ ∧ f x - (a:EReal) ≠ ⊥
  rw [← hf.coe_toReal hx, ← EReal.coe_sub]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- Convolution decomposition with finite values at the origin. With `a = f 0`,
`b = g 0` real (finite), `f − a` and `g − b` are the genuine `EReal` shifts, and
`minConv f g = ((f − a) ⊓ (g − b)) + a + b` pointwise. Only finiteness of the
origin values `a, b` is needed (it makes the `EReal` shift well-behaved); no
finiteness on the positive ray. -/
theorem minConv_eq_inf_sub_add
    (f g : ℝ≥0 → EReal) (a b : ℝ) (ha : f 0 = (a : EReal)) (hb : g 0 = (b : EReal))
    (hf : IsConcaveEReal f) (hg : IsConcaveEReal g) :
    minConv f g
      = (f - Function.const ℝ≥0 (a : EReal)) ⊓ (g - Function.const ℝ≥0 (b : EReal))
          + Function.const ℝ≥0 ((a : EReal) + (b : EReal)) := by
  set f' : ℝ≥0 → EReal := fun x => f x - (a:EReal) with hf'def
  set g' : ℝ≥0 → EReal := fun x => g x - (b:EReal) with hg'def
  -- the shifts vanish at the origin: `f' 0 = a − a = 0`, likewise `g'`
  have hf'0 : f' 0 = 0 := by
    show f 0 - (a:EReal) = 0
    rw [ha, EReal.sub_self (EReal.coe_ne_top a) (EReal.coe_ne_bot a)]
  have hg'0 : g' 0 = 0 := by
    show g 0 - (b:EReal) = 0
    rw [hb, EReal.sub_self (EReal.coe_ne_top b) (EReal.coe_ne_bot b)]
  -- the meet of the concave shifts is concave and null at 0, hence subadditive
  have hm0 : f' 0 ⊓ g' 0 = 0 := by rw [hf'0, hg'0, inf_idem]
  have hsub : IsSubadditive (fun x => f' x ⊓ g' x) :=
    IsConcaveEReal.isSubadditive _
      (IsConcaveEReal.inf f' g' (IsIsConcaveERealReal.sub_const f hf a) (IsIsConcaveERealReal.sub_const g hg b))
      (le_of_eq hm0.symm)
  -- per split: `f u + g s = (f' u + g' s) + (a + b)`, finite constants pulled out
  have hsummand : ∀ u s : ℝ≥0, f u + g s = (f' u + g' s) + ((a:EReal) + (b:EReal)) := by
    intro u s
    have e1 : f u = f' u + (a:EReal) := by
      show f u = (f u - (a:EReal)) + (a:EReal); rw [EReal.sub_add_cancel]
    have e2 : g s = g' s + (b:EReal) := by
      show g s = (g s - (b:EReal)) + (b:EReal); rw [EReal.sub_add_cancel]
    rw [e1, e2]; abel
  funext t
  show minConv f g t = (f' t ⊓ g' t) + ((a:EReal) + (b:EReal))
  apply le_antisymm
  · -- bound the convolution by the two extreme splits `t + 0` and `0 + t`
    rw [← min_add_add_right]
    refine le_inf ?_ ?_
    · refine le_trans (minConv_le_add f g (add_zero t)) ?_
      rw [hsummand t 0, hg'0, add_zero]
    · refine le_trans (minConv_le_add f g (zero_add t)) ?_
      rw [hsummand 0 t, hf'0, zero_add]
  · -- the subadditive meet undercuts every split
    refine le_minConv fun u s hus => ?_
    rw [hsummand u s]
    refine add_le_add ?_ le_rfl
    calc f' t ⊓ g' t = f' (u + s) ⊓ g' (u + s) := by rw [hus]
      _ ≤ (f' u ⊓ g' u) + (f' s ⊓ g' s) := hsub u s
      _ ≤ f' u + g' s := add_le_add inf_le_left inf_le_right

/-- Corollary: if both curves vanish at the origin, `minConv f g = f ⊓ g`. -/
theorem minConv_eq_inf_of_null
    (f g : ℝ≥0 → EReal) (hf : IsConcaveEReal f) (hg : IsConcaveEReal g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    minConv f g = f ⊓ g := by
  have hmain := minConv_eq_inf_sub_add f g 0 0
    (by rw [hf0]; rfl) (by rw [hg0]; rfl) hf hg
  rw [hmain]
  funext t
  show (f t - ((0:ℝ):EReal)) ⊓ (g t - ((0:ℝ):EReal)) + (((0:ℝ):EReal) + ((0:ℝ):EReal))
      = f t ⊓ g t
  simp [EReal.coe_zero]

/-- A concave `EReal` curve that never takes `−∞` and vanishes at the origin is
its own sub-additive closure: concavity with `g 0 = 0` gives subadditivity, and
`subadditiveClosureEReal_eq_self` closes the fixed point. -/
theorem subadditiveClosureEReal_eq_self_of_concaveE
    (g : ℝ≥0 → EReal) (hg : NeverBot g) (h0 : g 0 = 0) (hconc : IsConcaveEReal g) :
    subadditiveClosureEReal g = g :=
  subadditiveClosureEReal_eq_self g hg
    (IsConcaveEReal.isSubadditive g hconc (le_of_eq h0.symm)) h0

end DeepWiki
