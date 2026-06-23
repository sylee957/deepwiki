import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit

/-! # Rioboo's `LogToReal`: the σ-orbit root partition and full correctness (Bronstein §2.8, p.66–69)
`LogToReal(R, S)` rewrites the complex-log sum `g = ∑_{α | R(α)=0} α·log(S(α, x))` as a real function
by partitioning the roots of `R` over `K̄` into **real roots** (`α = a ∈ K`, i.e. `b = 0`) and
**conjugate pairs** `a ± i·b` with `b > 0`, each pair contributing both `a+i·b` and `a−i·b` (book
(2.25), p.66). The per-pair contribution is the real function `a·log(A²+B²) + b·LogToAtan(A, B)`
(`logToReal_conjugate_pair`), so the output (p.69) is
`∑_{pairs} [a·log(A²+B²) + b·LogToAtan(A,B)] + ∑_{real roots} a·log(S(a, x))`.

**Stage A — assembly given the partition.** Taking the root partition
`R.roots = reals + map a₊ pairs + map a₋ pairs` (each conjugate pair `p` supplying both
`a₊ p = a p + i·b p` and `a₋ p = a p − i·b p`) as a **certified `Multiset` hypothesis**, the original
root-sum `∑_{α ∈ R.roots} α·logDeriv(S α)` splits as `∑_{reals} + ∑_{pairs} [pair contribution]`
(`logToReal_rootSum_split`), and by `logToReal_conjugate_pair` the pair part equals the real form
`∑_{pairs} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]` — so **`LogToReal`'s output derivative
equals the original complex log-sum's derivative, given the partition** (`logToReal_correct_of_partition`).

**Stage B — the partition CONSTRUCTION (now complete).** Over a field-with-involution `(L, σ)`
(`σ ∘ σ = id`, `σ i = −i`, `i² = −1`) with the ordered fixed field `K ↪ L` (`[Field K] [LinearOrder K]
[IsStrictOrderedRing K]`), the real/imaginary parts `realPart σ α = (α+σα)/2`,
`imagPart σ i α = (α−σα)/(2i)` are `σ`-fixed (`realPart_fixed`/`imagPart_fixed`), reconstruct
`α = a + i·b`, `σα = a − i·b` (`eq_realPart_add_imagPart`/`conj_eq_realPart_sub_imagPart`), and
`σ` flips `b` (`imagPart_conj`/`realImagPartK_conj`: `b(σα) = −b(α)`), with `b = 0 ⟺ σα = α`
(`realImagPartK_eq_zero_iff`). Selecting `reals = R.roots.filter (b·=0)`,
`pairs = R.roots.filter (0<b·)` (the `b>0` rep via `K`'s order), the σ-stable root multiset partitions
`R.roots = reals + pairs.map(a+ib) + pairs.map(a−ib)` (`roots_partition`): the `b<0` block is the
`σ`-image of the `b>0` block, count-preservingly (`count_roots_conj_eq` + `b(σα)=−b(α)`, a
`Multiset.count`/`Multiset.ext` σ-bijection — no Mathlib orbit lemma needed), and the trichotomy
`b≠0 = (0<b) ⊎ (b<0)` splits the moved part. Feeding this into `logToReal_correct_of_partition` gives
**the full `LogToReal` correctness over `R`'s roots, with NO partition hypothesis**
(`logToReal_correct`) — closing the §2.8 `LogToReal` root-partition/recursion. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Recursion
variable {R : Type*} [Field R] [Differential R]

omit [Field R] [Differential R] in
/-- **Conjugate-pair root partition of a `Multiset`** (§2.8, p.66, book (2.25), the `bind`-of-`{a₊, a₋}`
form): for `pairs : Multiset σ` of conjugate-pair data and conjugate-root maps `a₊, a₋ : σ → R`, the
roots contributed by the pairs are `pairs.bind (fun p => {a₊ p, a₋ p})`, and this equals
`map a₊ pairs + map a₋ pairs` — each pair `p` supplies exactly its two conjugate roots. The flat
`map a₊ pairs + map a₋ pairs` is the form used by the root-sum split. -/
theorem bind_pair_eq_map_add_map {σ : Type*} (pairs : Multiset σ) (aPlus aMinus : σ → R) :
    (pairs.bind fun p => ({aPlus p, aMinus p} : Multiset R)) = pairs.map aPlus + pairs.map aMinus := by
  rw [show (fun p => ({aPlus p, aMinus p} : Multiset R)) = (fun p => aPlus p ::ₘ {aMinus p}) from rfl,
    Multiset.bind_cons, Multiset.bind_singleton]

omit [Differential R] in
/-- **`LogToReal` root-sum split over the partition** (§2.8, p.66, book (2.22)→(2.25)): given the root
partition `roots = reals + map a₊ pairs + map a₋ pairs` (`reals : Multiset R` the real roots, `pairs`
the conjugate-pair data, `a₊ p`/`a₋ p` the two conjugate roots of pair `p`) and a per-root weight-times-
log-derivative term `g`, the original complex log-sum `∑_{α ∈ roots} g α = (roots.map g).sum` splits as
the real-root part `∑_{reals} g a` plus the conjugate-pair part `∑_{pairs} [g (a₊ p) + g (a₋ p)]`. Pure
`Multiset.sum`/`map` bookkeeping (`Multiset.sum_map_add`). -/
theorem logToReal_rootSum_split {σ : Type*} (roots reals : Multiset R) (pairs : Multiset σ)
    (aPlus aMinus : σ → R) (g : R → R)
    (hpart : roots = reals + pairs.map aPlus + pairs.map aMinus) :
    (roots.map g).sum
      = (reals.map g).sum + (pairs.map (fun p => g (aPlus p) + g (aMinus p))).sum := by
  rw [hpart, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
    add_assoc, Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_add]
  rfl

/-- **`LogToReal` correctness given the partition** (§2.8, p.66–69, the assembly heart of the full
algorithm): suppose the roots of `S`'s associated `R` partition as `roots = reals +
map (a·+i·b·) pairs + map (a·−i·b·) pairs` (`a p, b p ∈ K` the real/imaginary parts of a conjugate
pair, `i² = −1`), and each pair has the real/imaginary split `S(a p + i·b p, x) = A p + i·B p`,
`S(a p − i·b p, x) = A p − i·B p` (from `exists_realImag_split`) with `(A p)² + (B p)² ≠ 0`. Then the
original complex log-sum's derivative `∑_{α ∈ roots} α·logDeriv(S α)` equals
`∑_{reals} a·logDeriv(S a) + ∑_{pairs} [a·logDeriv((A p)²+(B p)²) + b·(i·logDeriv((A+iB)/(A−iB)))]` —
i.e. the derivative of `LogToReal`'s real output `∑_{pairs} [a·log(A²+B²) + b·LogToAtan(A,B)] +
∑_{reals} a·log(S(a, x))`. The conjugate-pair part is folded from `logToReal_conjugate_pair_of_split`
by `Multiset.map_congr`; the split into real/pair parts is `logToReal_rootSum_split`. The partition is
taken as a certified hypothesis (the σ-orbit construction is the §2.8 residual). -/
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

/-- Restatement of **`LogToReal`'s correctness given the partition** against the book wording
(§2.8, p.66–69): the original complex log-sum `g = ∑_{α | R(α)=0} α·log(S(α, x))` has derivative equal
to the derivative of `LogToReal`'s real output — the conjugate-pair sum `∑_{a,b∈K, b>0, P(a,b)=Q(a,b)=0}
[a·log(A²+B²) + b·LogToAtan(A,B)]` plus the real-root sum `∑_{a∈K, R(a)=0} a·log(S(a,x))` — given that
`R`'s roots partition as real roots ⊎ conjugate pairs `a±i·b`. -/
example {σ : Type*} (S : R → R) (reals : Multiset R) (pairs : Multiset σ)
    (a b A B : σ → R) {i : R} (hi : i ^ 2 = -1) (roots : Multiset R)
    (hpart : roots = reals + pairs.map (fun p => a p + i * b p)
        + pairs.map (fun p => a p - i * b p))
    (hSplus : ∀ p ∈ pairs, S (a p + i * b p) = A p + i * B p)
    (hSminus : ∀ p ∈ pairs, S (a p - i * b p) = A p - i * B p)
    (hAB : ∀ p ∈ pairs, (A p) ^ 2 + (B p) ^ 2 ≠ 0) :
    (roots.map (fun α => α * Differential.logDeriv (S α))).sum
      = (reals.map (fun α => α * Differential.logDeriv (S α))).sum
        + (pairs.map (fun p => a p * Differential.logDeriv ((A p) ^ 2 + (B p) ^ 2)
            + b p * (i * Differential.logDeriv ((A p + i * B p) / (A p - i * B p))))).sum :=
  logToReal_correct_of_partition S reals pairs a b A B hi roots hpart hSplus hSminus hAB

end Recursion

section Conjugation
variable {L : Type*} [Field L]

/-- **σ-conjugation permutes `R`'s roots** (§2.8, p.66, the start of the partition construction): let
`σ : L ≃+* L` be a field automorphism (the conjugation, `σ i = −i`) fixing `R`'s coefficients
(`R.map σ = R`, so `R ∈ K[t]` over the fixed field `K`), with `R` split over `L`
(`card R.roots = R.natDegree`). Then `σ` maps the root multiset to itself, `R.roots.map σ = R.roots`
— so `σ` acts as a permutation of `R`'s roots. This is the bijection-of-roots fact
(`roots_map_of_injective_of_card_eq_natDegree`, `σ` injective) composed with `R.map σ = R`. It is the
input to the orbit partition: σ-fixed roots are the real roots (`α = a`), 2-element orbits `{α, σα}` the
conjugate pairs `a ± i·b`. -/
theorem roots_map_self_of_map_eq {σ : L ≃+* L} {R : L[X]}
    (hmap : R.map (σ : L →+* L) = R) (hsplit : Multiset.card R.roots = R.natDegree) :
    R.roots.map (σ : L →+* L) = R.roots := by
  have := roots_map_of_injective_of_card_eq_natDegree
    (f := (σ : L →+* L)) (EquivLike.injective σ) hsplit
  rw [hmap] at this
  exact this

/-- **σ-conjugation preserves root multiplicities** (§2.8, p.66, the orbit-stability behind the
partition): with the same hypotheses (`R.map σ = R`, `R` split), each root and its conjugate occur with
the same multiplicity, `(R.roots).count α = (R.roots).count (σ α)` for `σ` injective — so conjugate
roots pair up evenly and the 2-element σ-orbits `{α, σα}` carry equal counts. Immediate from
`roots_map_self_of_map_eq` and `Multiset.count_map_eq_count'`. -/
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

/-- **Real part of a root** (§2.8, p.66, `a = (α + σ α)/2`): for the conjugation `σ` (`σ i = −i`,
fixed field the reals) and a root `α = a + i·b`, the real part is `realPart σ α = (α + σ α)/2`. With
`σ α = a − i·b` this recovers `a`, the common real part of the conjugate pair `α, σ α`. -/
def realPart (σ : L ≃+* L) (α : L) : L := (α + σ α) / 2

/-- **Imaginary part of a root** (§2.8, p.66, `b = (α − σ α)/(2 i)`): for the conjugation `σ`
(`σ i = −i`) and `i` with `i² = −1`, the imaginary part is `imagPart σ i α = (α − σ α)/(2 i)`. With
`σ α = a − i·b` this recovers `b`; `b = 0 ⟺ σ α = α` (real root), and `b(σ α) = −b(α)`. -/
def imagPart (σ : L ≃+* L) (i : L) (α : L) : L := (α - σ α) / (2 * i)

variable {σ : L ≃+* L} {i : L}

/-- `α = realPart σ α + i·imagPart σ i α` (§2.8, p.66): a root reconstructs from its real and
imaginary parts, with `i² = −1`. -/
theorem eq_realPart_add_imagPart (hi : i ^ 2 = -1) (α : L) :
    α = realPart σ α + i * imagPart σ i α := by
  have hi0 : (i : L) ≠ 0 := by rintro rfl; norm_num at hi
  rw [realPart, imagPart]
  field_simp
  ring

/-- `σ α = realPart σ α − i·imagPart σ i α` (§2.8, p.66): the conjugate root is the real part minus
`i` times the imaginary part. -/
theorem conj_eq_realPart_sub_imagPart (hi : i ^ 2 = -1) (α : L) :
    σ α = realPart σ α - i * imagPart σ i α := by
  have hi0 : (i : L) ≠ 0 := by rintro rfl; norm_num at hi
  rw [realPart, imagPart]
  field_simp
  ring

/-- **`imagPart` is `σ`-fixed** (§2.8, p.66): with `σ` an involution (`σ (σ α) = α`) and `σ i = −i`,
the imaginary part lies in the fixed field, `σ (imagPart σ i α) = imagPart σ i α`. Computation:
`σ b = (σ α − α)/(2·σ i) = (σ α − α)/(−2 i) = (α − σ α)/(2 i) = b`. -/
theorem imagPart_fixed (hinv : ∀ x, σ (σ x) = x) (hσi : σ i = -i) (α : L) :
    σ (imagPart σ i α) = imagPart σ i α := by
  simp only [imagPart, map_div₀, map_sub, map_mul, hinv, hσi, map_ofNat, mul_neg, div_neg]
  rw [← neg_div, neg_sub]

/-- **`realPart` is `σ`-fixed** (§2.8, p.66): with `σ` an involution, the real part lies in the fixed
field, `σ (realPart σ α) = realPart σ α`. -/
theorem realPart_fixed (hinv : ∀ x, σ (σ x) = x) (α : L) :
    σ (realPart σ α) = realPart σ α := by
  rw [realPart, map_div₀, map_add, hinv, map_ofNat, add_comm]

omit [CharZero L] in
/-- **`σ` flips the imaginary part** (§2.8, p.66, `b(σ α) = −b(α)`): with `σ` an involution,
`imagPart σ i (σ α) = −imagPart σ i α` — conjugation negates the imaginary part, so it bijects the
`b > 0` roots with the `b < 0` roots. -/
theorem imagPart_conj (hinv : ∀ x, σ (σ x) = x) (α : L) :
    imagPart σ i (σ α) = -imagPart σ i α := by
  rw [imagPart, imagPart, hinv, ← neg_div, neg_sub]

/-- **Real root ⟺ `imagPart = 0`** (§2.8, p.66): with `i ≠ 0`, a root is `σ`-fixed (real,
`σ α = α`) iff its imaginary part vanishes, `imagPart σ i α = 0 ↔ σ α = α`. -/
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
/-- **`K`-valued imaginary part flips under `σ`** (§2.8, p.66): if the ordered fixed field `K` reads
the imaginary part (`algebraMap K L (b α) = imagPart σ i α`), then `b (σ α) = −b α` — the sign-flip
transported to the ordered field `K` (via `imagPart_conj` and injectivity of `algebraMap K L`). -/
theorem realImagPartK_conj {σ : L ≃+* L} {i : L} {b : L → K}
    (hinv : ∀ x, σ (σ x) = x)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α) (α : L) :
    b (σ α) = -b α := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  apply hinj
  rw [hb, map_neg, hb, imagPart_conj hinv]

omit [DecidableEq L] [LinearOrder K] [IsStrictOrderedRing K] in
/-- **`K`-valued imaginary part is `0` ⟺ real root** (§2.8, p.66): if `algebraMap K L (b α) =
imagPart σ i α` and `i² = −1`, then `b α = 0 ↔ σ α = α` — the ordered-field criterion picking out the
real roots. -/
theorem realImagPartK_eq_zero_iff {σ : L ≃+* L} {i : L} {b : L → K} (hi : i ^ 2 = -1)
    (hb : ∀ α, algebraMap K L (b α) = imagPart σ i α) (α : L) :
    b α = 0 ↔ σ α = α := by
  rw [← imagPart_eq_zero_iff hi α, ← hb α, map_eq_zero]

/-- **Conjugate-pair root partition from the conjugation** (§2.8, p.66, book (2.25), the σ-orbit
construction): let `σ : L ≃+* L` be the conjugation (an involution `σ ∘ σ = id`, `σ i = −i`) fixing
`R`'s coefficients (`R.map σ = R`, so `R ∈ K[t]`), `R` split (`card R.roots = deg R`), `i² = −1`, and
let the ordered fixed field `K` read each imaginary part `b α = imagPart σ i α` (`algebraMap K L (b α)
= imagPart σ i α`). Selecting `reals := R.roots.filter (b · = 0)` (the real roots, `b = 0`) and
`pairs := R.roots.filter (0 < b ·)` (one representative per conjugate pair, the `b > 0` selection via
`K`'s order), the root multiset partitions as
`R.roots = reals + pairs.map (a·+i·b·) + pairs.map (a·−i·b·)` with `a = realPart`. The moved part
`filter (b·≠0)` splits by trichotomy (`K` linear) into `filter (0<b·) + filter (b·<0)`, and the `b<0`
block is the `σ`-image of the `b>0` block (`σ` bijects them count-preservingly, via `count_roots_conj_eq`
and `realImagPartK_conj`'s `b(σα)=−b(α)`); the `a+ib`/`a−ib` maps are `id`/`σ` on the roots
(`eq_realPart_add_imagPart`, `conj_eq_realPart_sub_imagPart`). This constructs the certified partition
hypothesis of `logToReal_correct_of_partition`. -/
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

/-- **`LogToReal` correctness over `R`'s roots** (§2.8, p.66–69, book (2.22)→(2.26), CLOSING the
algorithm): in a differential field `L` carrying `√−1` (`i² = −1`) and a conjugation `σ`
(an involution `σ ∘ σ = id`, `σ i = −i`) with `R ∈ K[t]` lifted `σ`-fixed (`R.map σ = R`) and split
over `L` (`card R.roots = deg R`), reading each imaginary part into the ordered fixed field `K`
(`algebraMap K L (b α) = imagPart σ i α`), the σ-orbit partition `roots_partition` discharges the
partition hypothesis of `logToReal_correct_of_partition` **without assuming it**: given each root's
real/imaginary split `S(a+i·b, x) = A + i·B`, `S(a−i·b, x) = A − i·B` (`A²+B² ≠ 0`, from
`exists_realImag_split_bivariate`), the original complex log-sum's derivative
`∑_{α|R(α)=0} α·logDeriv(S(α,x))` equals `LogToReal`'s real output's derivative
`∑_{reals} a·logDeriv(S a) + ∑_{pairs} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]` —
`a·log(A²+B²) + b·LogToAtan(A,B)` per conjugate pair. `reals = R.roots.filter (b·=0)` the real roots,
`pairs = R.roots.filter (0 < b·)` the `b>0` representatives. This is the full §2.8 `LogToReal`. -/
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

/-- Restatement of **`LogToReal`'s full correctness** against the book wording (§2.8, p.66–69):
the complex-log sum `g = ∑_{α|R(α)=0} α·log(S(α,x))` has derivative equal to `LogToReal`'s real
output's derivative — `∑_{a,b∈K, b>0, P(a,b)=Q(a,b)=0} [a·log(A²+B²) + b·LogToAtan(A,B)] +
∑_{a∈K, R(a)=0} a·log(S(a,x))` — with the conjugate-pair partition CONSTRUCTED from the conjugation
(no partition hypothesis). -/
example {σ : L ≃+* L} {i : L} {R : L[X]} {b : L → K} (S A B : L → L)
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
  logToReal_correct S A B hi hinv hb hmap hsplit hSplus hSminus hAB

end Correct
