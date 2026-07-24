import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit

/-! # Rioboo's `LogToReal`: the σ-orbit root partition and full correctness
Partitioning the roots of `R` over `K̄` into real roots (`b = 0`) and conjugate pairs `a ± i·b`
(`b > 0`) via a conjugation `σ` (`σ ∘ σ = id`, `σ i = −i`, `i² = −1`) with ordered fixed field `K`,
`roots_partition` constructs the certified partition that `logToReal_correct_of_partition` consumes,
giving `logToReal_correct`: the complex-log sum's derivative equals `LogToReal`'s real output's. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Recursion
variable {R : Type*} [Field R] [Differential R]

omit [Field R] [Differential R] in
/-- `pairs.bind (fun p => {aPlus p, aMinus p}) = pairs.map aPlus + pairs.map aMinus`. -/
theorem bind_pair_eq_map_add_map {σ : Type*} (pairs : Multiset σ) (aPlus aMinus : σ → R) :
    (pairs.bind fun p => ({aPlus p, aMinus p} : Multiset R)) = pairs.map aPlus + pairs.map aMinus := by
  rw [show (fun p => ({aPlus p, aMinus p} : Multiset R)) = (fun p => aPlus p ::ₘ {aMinus p}) from rfl,
    Multiset.bind_cons, Multiset.bind_singleton]

omit [Differential R] in
/-- Given `roots = reals + map aPlus pairs + map aMinus pairs`, the root-sum splits as
`(roots.map g).sum = (reals.map g).sum + (pairs.map (fun p => g (aPlus p) + g (aMinus p))).sum`. -/
theorem logToReal_rootSum_split {σ : Type*} (roots reals : Multiset R) (pairs : Multiset σ)
    (aPlus aMinus : σ → R) (g : R → R)
    (hpart : roots = reals + pairs.map aPlus + pairs.map aMinus) :
    (roots.map g).sum
      = (reals.map g).sum + (pairs.map (fun p => g (aPlus p) + g (aMinus p))).sum := by
  rw [hpart, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
    add_assoc, Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_add]
  rfl

/-- Given the certified partition `roots = reals + map (a·+i·b·) pairs + map (a·−i·b·) pairs` and each
pair's split `S(a p ± i·b p) = A p ± i·B p` (`(A p)²+(B p)² ≠ 0`), the complex-log sum
`∑ α·logDeriv(S α)` equals `∑_{reals} α·logDeriv(S α) + ∑_{pairs} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]`. -/
theorem logToReal_correct_of_partition {σ : Type*}
    (S : R → R) (reals : Multiset R) (pairs : Multiset σ)
    (a b A B : σ → R) {i : R} (hi : i ^ 2 = -1)
    (roots : Multiset R)
    (hpart : roots = reals + pairs.map (fun p => a p + i * b p)
        + pairs.map (fun p => a p - i * b p))
    (hSplus : ∀ p ∈ pairs, S (a p + i * b p) = A p + i * B p)
    (hSminus : ∀ p ∈ pairs, S (a p - i * b p) = A p - i * B p)
    (hAB : ∀ p ∈ pairs, (A p) ^ 2 + (B p) ^ 2 ≠ 0) :
    (roots.map (fun α => α * Differential.logDeriv (S α))).sum
      = (reals.map (fun α => α * Differential.logDeriv (S α))).sum
        + (pairs.map (fun p => a p * Differential.logDeriv ((A p) ^ 2 + (B p) ^ 2)
            + b p * (i * Differential.logDeriv ((A p + i * B p) / (A p - i * B p))))).sum := by
  -- Split the original root-sum into real-root part + conjugate-pair part.
  rw [logToReal_rootSum_split roots reals pairs (fun p => a p + i * b p) (fun p => a p - i * b p)
    (fun α => α * Differential.logDeriv (S α)) hpart]
  -- The conjugate-pair part folds, term by term, into the real form via the split lemma.
  refine congrArg _ (congrArg _ (Multiset.map_congr rfl fun p hp => ?_))
  exact logToReal_conjugate_pair_of_split hi (hAB p hp) (hSplus p hp) (hSminus p hp)

end Recursion

section Conjugation
variable {L : Type*} [Field L]

/-- If a field automorphism `σ` fixes `R`'s coefficients (`R.map σ = R`) and `R` is split, then
`σ` permutes the roots: `R.roots.map σ = R.roots`. -/
theorem roots_map_self_of_map_eq {σ : L ≃+* L} {R : L[X]}
    (hmap : R.map (σ : L →+* L) = R) (hsplit : Multiset.card R.roots = R.natDegree) :
    R.roots.map (σ : L →+* L) = R.roots := by
  have := roots_map_of_injective_of_card_eq_natDegree
    (f := (σ : L →+* L)) (EquivLike.injective σ) hsplit
  rw [hmap] at this
  exact this

/-- With `R.map σ = R` and `R` split, each root and its conjugate share multiplicity:
`R.roots.count α = R.roots.count (σ α)`. -/
theorem count_roots_conj_eq [DecidableEq L] {σ : L ≃+* L} {R : L[X]}
    (hmap : R.map (σ : L →+* L) = R) (hsplit : Multiset.card R.roots = R.natDegree) (α : L) :
    R.roots.count α = R.roots.count (σ α) := by
  have hinj : Function.Injective (σ : L →+* L) := EquivLike.injective σ
  conv_rhs => rw [← roots_map_self_of_map_eq hmap hsplit]
  rw [show σ α = (σ : L →+* L) α from rfl,
    Multiset.count_map_eq_count' (σ : L →+* L) R.roots hinj]

end Conjugation

section RealImagPart
variable {L : Type*} [Field L] [CharZero L]

/-- Real part of a root under conjugation `σ`: `realPart σ α := (α + σ α)/2`. -/
def realPart (σ : L ≃+* L) (α : L) : L := (α + σ α) / 2

/-- Imaginary part of a root under conjugation `σ` with `i² = −1`: `imagPart σ i α := (α − σ α)/(2·i)`. -/
def imagPart (σ : L ≃+* L) (i : L) (α : L) : L := (α - σ α) / (2 * i)

variable {σ : L ≃+* L} {i : L}

/-- `α = realPart σ α + i·imagPart σ i α`, with `i² = −1`. -/
theorem eq_realPart_add_imagPart (hi : i ^ 2 = -1) (α : L) :
    α = realPart σ α + i * imagPart σ i α := by
  have hi0 : (i : L) ≠ 0 := by rintro rfl; norm_num at hi
  rw [realPart, imagPart]
  field_simp
  ring

/-- `σ α = realPart σ α − i·imagPart σ i α`, with `i² = −1`. -/
theorem conj_eq_realPart_sub_imagPart (hi : i ^ 2 = -1) (α : L) :
    σ α = realPart σ α - i * imagPart σ i α := by
  have hi0 : (i : L) ≠ 0 := by rintro rfl; norm_num at hi
  rw [realPart, imagPart]
  field_simp
  ring

/-- For `σ` an involution with `σ i = −i`, `σ (imagPart σ i α) = imagPart σ i α`. -/
theorem imagPart_fixed (hinv : ∀ x, σ (σ x) = x) (hσi : σ i = -i) (α : L) :
    σ (imagPart σ i α) = imagPart σ i α := by
  simp only [imagPart, map_div₀, map_sub, map_mul, hinv, hσi, map_ofNat, mul_neg, div_neg]
  rw [← neg_div, neg_sub]

/-- For `σ` an involution, `σ (realPart σ α) = realPart σ α`. -/
theorem realPart_fixed (hinv : ∀ x, σ (σ x) = x) (α : L) :
    σ (realPart σ α) = realPart σ α := by
  rw [realPart, map_div₀, map_add, hinv, map_ofNat, add_comm]

omit [CharZero L] in
/-- For `σ` an involution, `imagPart σ i (σ α) = −imagPart σ i α`. -/
theorem imagPart_conj (hinv : ∀ x, σ (σ x) = x) (α : L) :
    imagPart σ i (σ α) = -imagPart σ i α := by
  rw [imagPart, imagPart, hinv, ← neg_div, neg_sub]

/-- With `i² = −1`, `imagPart σ i α = 0 ↔ σ α = α`. -/
theorem imagPart_eq_zero_iff (hi : i ^ 2 = -1) (α : L) :
    imagPart σ i α = 0 ↔ σ α = α := by
  have hi0 : (i : L) ≠ 0 := by rintro rfl; norm_num at hi
  have h2i : (2 * i : L) ≠ 0 := mul_ne_zero two_ne_zero hi0
  rw [imagPart, div_eq_zero_iff, sub_eq_zero, or_iff_left h2i, eq_comm]

end RealImagPart

section Partition
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra K L]

omit [DecidableEq L] in
/-- If `algebraMap K L (b α) = imagPart σ i α`, then `b (σ α) = −b α`. -/
theorem realImagPartK_conj {σ : L ≃+* L} {i : L} {b : L → K}
    (hinv : ∀ x, σ (σ x) = x)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α) (α : L) :
    b (σ α) = -b α := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  apply hinj
  rw [hb, map_neg, hb, imagPart_conj hinv]

omit [DecidableEq L] [LinearOrder K] [IsStrictOrderedRing K] in
/-- If `algebraMap K L (b α) = imagPart σ i α` and `i² = −1`, then `b α = 0 ↔ σ α = α`. -/
theorem realImagPartK_eq_zero_iff {σ : L ≃+* L} {i : L} {b : L → K} (hi : i ^ 2 = -1)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α) (α : L) :
    b α = 0 ↔ σ α = α := by
  rw [← imagPart_eq_zero_iff hi α, ← hb α, map_eq_zero]

/-- With `σ` an involution (`σ i = −i`) fixing `R`'s coefficients (`R.map σ = R`), `R` split, `i² = −1`,
and `algebraMap K L (b α) = imagPart σ i α`, the roots partition as
`R.roots = filter (b·=0) + (filter (0<b·)).map (a·+i·b·) + (filter (0<b·)).map (a·−i·b·)`. -/
theorem roots_partition {σ : L ≃+* L} {i : L} {R : L[X]} {b : L → K}
    (hi : i ^ 2 = -1) (hinv : ∀ x, σ (σ x) = x)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α)
    (hmap : R.map (σ : L →+* L) = R) (hsplit : Multiset.card R.roots = R.natDegree) :
    R.roots
      = R.roots.filter (fun α => b α = 0)
        + (R.roots.filter (fun α => 0 < b α)).map
            (fun α => realPart σ α + i * imagPart σ i α)
        + (R.roots.filter (fun α => 0 < b α)).map
            (fun α => realPart σ α - i * imagPart σ i α) := by
  -- The two pair-maps are `id` and `σ` on the roots (`α = a+ib`, `σα = a−ib`).
  have hmapId : (R.roots.filter (fun α => 0 < b α)).map
        (fun α => realPart σ α + i * imagPart σ i α)
      = R.roots.filter (fun α => 0 < b α) := by
    rw [show (fun α => realPart σ α + i * imagPart σ i α) = id from
      funext fun α => (eq_realPart_add_imagPart hi α).symm, Multiset.map_id]
  have hmapσ : (R.roots.filter (fun α => 0 < b α)).map
        (fun α => realPart σ α - i * imagPart σ i α)
      = (R.roots.filter (fun α => 0 < b α)).map (σ : L →+* L) :=
    Multiset.map_congr rfl fun α _ => (conj_eq_realPart_sub_imagPart hi α).symm
  rw [hmapId, hmapσ]
  -- `σ` maps `filter (b>0)` onto `filter (b<0)` count-preservingly.
  have hbij : (R.roots.filter (fun α => 0 < b α)).map (σ : L →+* L)
      = R.roots.filter (fun α => b α < 0) := by
    have hinj : Function.Injective (σ : L →+* L) := EquivLike.injective σ
    refine Multiset.ext.mpr fun x => ?_
    -- `count x (map σ s) = count (σ x) s`, via `count_map_eq_count'` at `σ x` (σ involution).
    have hcm : ((R.roots.filter (fun α => 0 < b α)).map (σ : L →+* L)).count x
        = (R.roots.filter (fun α => 0 < b α)).count (σ x) := by
      have := Multiset.count_map_eq_count' (σ : L →+* L)
        (R.roots.filter (fun α => 0 < b α)) hinj (σ x)
      rwa [show (σ : L →+* L) (σ x) = x from hinv x] at this
    rw [hcm, Multiset.count_filter, Multiset.count_filter,
      show b (σ x) = -b x from realImagPartK_conj hinv hb x]
    simp only [neg_pos]
    rw [← count_roots_conj_eq hmap hsplit x]
  -- Trichotomy: `filter (b≠0) = filter (b>0) + filter (b<0)`.
  have htri : R.roots.filter (fun α => ¬ b α = 0)
      = R.roots.filter (fun α => 0 < b α) + R.roots.filter (fun α => b α < 0) := by
    refine Multiset.ext.mpr fun x => ?_
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter, Multiset.count_filter]
    rcases lt_trichotomy (b x) 0 with hlt | heq | hgt
    · rw [if_neg (asymm hlt), if_pos hlt, zero_add, if_pos (ne_of_lt hlt)]
    · simp only [heq, lt_irrefl, not_true, if_false, add_zero]
    · rw [if_pos hgt, if_neg (asymm hgt), add_zero, if_pos (ne_of_gt hgt)]
  -- Assemble: roots = filter(b=0) + filter(b≠0) = reals + pairs + filter(b<0); rewrite filter(b<0).
  conv_lhs => rw [← Multiset.filter_add_not (fun α => b α = 0) R.roots]
  rw [htri, hbij, ← add_assoc]

end Partition

section Correct
variable {L : Type*} [Field L] [Differential L] [CharZero L] [DecidableEq L]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra K L]

/-- Full `LogToReal` correctness: in a differential field `L` with `i² = −1`, conjugation `σ`
(involution, `σ i = −i`), `R.map σ = R` split, and `algebraMap K L (b α) = imagPart σ i α`, given each
pair's split `S(a±i·b) = A ± i·B` (`A²+B² ≠ 0`), the complex-log sum `∑ α·logDeriv(S α)` equals
`∑_{b·=0} α·logDeriv(S α) + ∑_{0<b·} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]`. -/
theorem logToReal_correct {σ : L ≃+* L} {i : L} {R : L[X]} {b : L → K}
    (S A B : L → L)
    (hi : i ^ 2 = -1) (hinv : ∀ x, σ (σ x) = x)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α)
    (hmap : R.map (σ : L →+* L) = R) (hsplit : Multiset.card R.roots = R.natDegree)
    (hSplus : ∀ p ∈ R.roots.filter (fun α => 0 < b α),
      S (realPart σ p + i * imagPart σ i p) = A p + i * B p)
    (hSminus : ∀ p ∈ R.roots.filter (fun α => 0 < b α),
      S (realPart σ p - i * imagPart σ i p) = A p - i * B p)
    (hAB : ∀ p ∈ R.roots.filter (fun α => 0 < b α), (A p) ^ 2 + (B p) ^ 2 ≠ 0) :
    (R.roots.map (fun α => α * Differential.logDeriv (S α))).sum
      = ((R.roots.filter (fun α => b α = 0)).map
          (fun α => α * Differential.logDeriv (S α))).sum
        + ((R.roots.filter (fun α => 0 < b α)).map
            (fun p => realPart σ p * Differential.logDeriv ((A p) ^ 2 + (B p) ^ 2)
              + imagPart σ i p
                * (i * Differential.logDeriv ((A p + i * B p) / (A p - i * B p))))).sum :=
  logToReal_correct_of_partition S _ (R.roots.filter (fun α => 0 < b α))
    (realPart σ) (imagPart σ i) A B hi R.roots
    (roots_partition hi hinv hb hmap hsplit) hSplus hSminus hAB

end Correct
