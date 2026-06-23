import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit

/-! # Rioboo's `LogToReal`: the recursion over `R`'s roots, given the partition (Bronstein §2.8, p.66–69)
`LogToReal(R, S)` rewrites the complex-log sum `g = ∑_{α | R(α)=0} α·log(S(α, x))` as a real function
by partitioning the roots of `R` over `K̄` into **real roots** (`α = a ∈ K`, i.e. `b = 0`) and
**conjugate pairs** `a ± i·b` with `b > 0`, each pair contributing both `a+i·b` and `a−i·b` (book
(2.25), p.66). The per-pair contribution is the real function `a·log(A²+B²) + b·LogToAtan(A, B)`
(`logToReal_conjugate_pair`), so the output (p.69) is
`∑_{pairs} [a·log(A²+B²) + b·LogToAtan(A,B)] + ∑_{real roots} a·log(S(a, x))`.

This file closes the **assembly given the partition** (the reachable substance, mirroring how
Thm 2.8.4 / `rioboo_coprime` took the LRT cofactors as hypotheses): taking the root partition
`R.roots = reals + map a₊ pairs + map a₋ pairs` (each conjugate pair `p` supplying both
`a₊ p = a p + i·b p` and `a₋ p = a p − i·b p`) as a **certified `Multiset` hypothesis**, the original
root-sum `∑_{α ∈ R.roots} α·logDeriv(S α)` splits as `∑_{reals} + ∑_{pairs} [pair contribution]`
(`logToReal_rootSum_split`), and by `logToReal_conjugate_pair` the pair part equals the real form
`∑_{pairs} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]` — so **`LogToReal`'s output derivative
equals the original complex log-sum's derivative, given the partition** (`logToReal_correct_of_partition`).
The friction is purely `Multiset.sum`/`map`/`bind` bookkeeping (`Multiset.sum_map_add`,
`Multiset.bind_cons`/`bind_singleton`), folded against the per-pair lemma.

The **partition construction** itself — that the σ-conjugation (`σ i = −i`, fixed field the reals)
permutes `R.roots` as σ-fixed roots (real) ⊎ 2-element σ-orbits `{α, σα}` (conjugate pairs), with the
`b > 0` representative selected via an ordering on the fixed field — needs field-with-involution +
ordered-fixed-field orbit machinery (a `LinearOrderedField` complexification / abstract `(L, σ, <)`
with σ-orbit decomposition of a root `Multiset`) not yet in Mathlib, and is the precisely-stated §2.8
residual. -/

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

/-! ## NOT YET FORMALIZED (§2.8 partition-construction residual)

The **Stage A** assembly (`logToReal_correct_of_partition`) is complete: given the root partition as a
certified `Multiset` hypothesis, `LogToReal`'s output derivative equals the original complex log-sum's
derivative. **Stage B's** start is here — the conjugation `σ` permutes `R`'s roots
(`roots_map_self_of_map_eq`) preserving multiplicities (`count_roots_conj_eq`). What remains is the
**orbit decomposition with the `b > 0` selection**, the genuine §2.8 infra:

* [infra] Partition the σ-stable root `Multiset` `R.roots` into the σ-fixed sub-multiset
  `{α | σ α = α}` (the real roots, `b = 0`) and a `Multiset` of 2-element σ-orbits `{α, σ α}` with
  `σ α ≠ α` (the conjugate pairs). This is a `Multiset`-level orbit quotient under the order-2
  involution `σ` — choosing one representative per 2-orbit, which needs a section of the orbit map
  (an orbit-representative `Multiset`-fold under an involution), not currently in Mathlib.
* [infra] The `b > 0` representative selection: with `α = a + i·b` and `σ α = a − i·b`, recover
  `a = (α + σ α)/2` and `b = (α − σ α)/(2 i)` in the fixed field `K`, and select the representative with
  `b > 0` via a `LinearOrderedField` order on `K` (the "real closure" `K̄ = K(i)` ordered-fixed-field
  setup). Requires a field-with-involution `(L, σ)` whose fixed field carries a `LinearOrder` compatible
  with `i² = −1` (a complexification `L = K(i)` over an ordered `K`), not yet built.

Once both are in place, feeding the resulting `reals`/`pairs` multisets into
`logToReal_correct_of_partition` discharges the full `LogToReal` correctness over `R`'s roots. -/

end DeepWiki.SymbolicIntegration
