import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Min-plus matrices — foundation for the sub-additive-closure cyclicity theorem
The min-plus semiring `(ℤ ∪ {+∞}, min, +)` is Mathlib's `Tropical (WithTop ℤ)`: addition is `min`,
multiplication is `+`, `𝟘 = +∞ = ⊤`, `𝟙 = (0 : ℤ)`. Matrices over it inherit the (non-commutative)
semiring product `(A * B)ᵢⱼ = ⨁ₖ Aᵢₖ ⊗ Bₖⱼ = ⨅ₖ (Aᵢₖ + Bₖⱼ)` and powers `Aᵏ` from Mathlib.

This is the first step toward the **cyclicity theorem** (`Aᵏ⁺ᵈ = Aᵏ + λd` past a finite rank, BCOQ
"Synchronization and Linearity" Thm 3.112), which computes the sub-additive closure `f* = ⨅ₘ f^⊗ᵐ`
(the closure is *not* a finite truncation of `f^⊗ᵐ` — see `DeepWiki.UppSeq` — but a matrix power that
genuinely stabilizes). A research-scale arc; this file builds the algebraic substrate. -/

namespace DeepWiki.MinPlusMatrix

open Matrix

/-- The **min-plus semiring** `(ℤ ∪ {+∞}, min, +)` — Mathlib's tropical semiring on `WithTop ℤ`:
`⊕ = min`, `⊗ = +`, `𝟘 = ⊤ = +∞`, `𝟙 = (0 : ℤ)`. -/
abbrev MP := Tropical (WithTop ℤ)

/-- The additive identity (`⊕`-zero) of the min-plus semiring is `+∞`. -/
theorem mp_zero : (0 : MP) = Tropical.trop ⊤ := rfl

/-- The multiplicative identity (`⊗`-unit) of the min-plus semiring is `0`. -/
theorem mp_one : (1 : MP) = Tropical.trop (0 : WithTop ℤ) := rfl

/-- `⊕` is `min` on the underlying values. -/
theorem mp_add (a b : MP) : (a + b).untrop = min a.untrop b.untrop := rfl

/-- `⊗` is `+` on the underlying values. -/
theorem mp_mul (a b : MP) : (a * b).untrop = a.untrop + b.untrop := rfl

/-- Min-plus matrices form a semiring (from Mathlib), so the product
`(A * B)ᵢⱼ = ⨅ₖ (Aᵢₖ + Bₖⱼ)` and powers `Aᵏ` are available. -/
example (A : Matrix (Fin 2) (Fin 2) MP) (k : ℕ) : Matrix (Fin 2) (Fin 2) MP := A ^ k

/-- A concrete 2×2 min-plus matrix (entries `0,1,2,0`), for sanity checks. -/
def exA : Matrix (Fin 2) (Fin 2) MP :=
  !![Tropical.trop 0, Tropical.trop 1; Tropical.trop 2, Tropical.trop 0]

/-- Sanity (gate-verified): the min-plus matrix square computes `(A²)₀₀ = min(0+0, 1+2) = 0`,
confirming `Matrix` over `Tropical (WithTop ℤ)` is the min-plus matrix product. -/
example : (exA ^ 2) 0 0 = Tropical.trop 0 := by native_decide

/-- Sanity (gate-verified): `(A²)₀₁ = min(0+1, 1+0) = 1`. -/
example : (exA ^ 2) 0 1 = Tropical.trop 1 := by native_decide

/-- **Min-plus matrix power recursion, last edge**: `(Aᵐ⁺¹)ᵢⱼ = ⨅ₖ ((Aᵐ)ᵢₖ + Aₖⱼ)` on the underlying
`WithTop ℤ` values — relax over the *last* edge `k → j` (matrix product `∑ = ⨅`, `⊗ = +`, via
`A^(m+1) = Aᵐ * A`). A basic tool for the walk/circuit analysis underlying the cyclicity theorem. -/
theorem untrop_pow_succ_apply_last {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (m : ℕ) (i j : Fin n) :
    ((A ^ (m + 1)) i j).untrop
      = Finset.univ.inf (fun k => ((A ^ m) i k).untrop + (A k j).untrop) := by
  rw [pow_succ, Matrix.mul_apply, Finset.untrop_sum']
  rfl

/-- **Min-plus matrix power recursion, first edge**: `(Aᵐ⁺¹)ᵢⱼ = ⨅ₖ (Aᵢₖ + (Aᵐ)ₖⱼ)` — the dual,
relaxing over the *first* edge `i → k` (via `A^(m+1) = A * Aᵐ`). This is the form that splits a walk
at its head, used to construct an optimal walk vertex by vertex. -/
theorem untrop_pow_succ_apply_first {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (m : ℕ) (i j : Fin n) :
    ((A ^ (m + 1)) i j).untrop
      = Finset.univ.inf (fun k => (A i k).untrop + ((A ^ m) k j).untrop) := by
  rw [pow_succ', Matrix.mul_apply, Finset.untrop_sum']
  rfl

/-- **Concatenation bound**: splitting a length-`p+q` walk `i ⤳ j` through any *fixed* intermediate
vertex `k` (as `i ⤳ k` of length `p`, then `k ⤳ j` of length `q`) over-estimates the optimum:
`(Aᵖ⁺ᵠ)ᵢⱼ ≤ (Aᵖ)ᵢₖ + (Aᵠ)ₖⱼ` on underlying values. Immediate from `A^(p+q) = A^p * A^q` (`pow_add`)
and `inf ≤ term`. The workhorse for the super- and sub-additivity arguments behind the eigenvalue. -/
theorem untrop_pow_add_le {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (p q : ℕ) (i j k : Fin n) :
    ((A ^ (p + q)) i j).untrop ≤ ((A ^ p) i k).untrop + ((A ^ q) k j).untrop := by
  rw [pow_add, Matrix.mul_apply, Finset.untrop_sum']
  exact Finset.inf_le (Finset.mem_univ k)

/-- **Diagonal subadditivity** (Fekete-ready): the underlying diagonal weights `aₘ := (Aᵐ)ᵢᵢ` are
subadditive, `aₚ₊ᵩ ≤ aₚ + aᵩ` — concatenating a length-`p` circuit at `i` with a length-`q` circuit
at `i` yields a length-`p+q` circuit at `i`. By Fekete's lemma `infₘ aₘ/m` then exists; it is the
min mean circuit weight through `i`, i.e. the min-plus eigenvalue. -/
theorem untrop_pow_add_le_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (p q : ℕ) (i : Fin n) :
    ((A ^ (p + q)) i i).untrop ≤ ((A ^ p) i i).untrop + ((A ^ q) i i).untrop :=
  untrop_pow_add_le A p q i i i

/-- **Weight of a walk** starting at `i` and visiting the vertices of `l` in order: `l` lists the
vertices *after* the start, so the walk has `l.length` edges and ends at `l`'s last element (or at
`i` when `l = []`). The weight is the sum of the traversed edge weights on the underlying values. -/
def walkWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n) : List (Fin n) → WithTop ℤ
  | [] => 0
  | j :: rest => (A i j).untrop + walkWeight A j rest

/-- The empty walk has weight `0` (the multiplicative unit). -/
@[simp] theorem walkWeight_nil {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n) :
    walkWeight A i [] = 0 := rfl

/-- Peeling the first edge: `walkWeight A i (j :: rest) = Aᵢⱼ + walkWeight A j rest`. -/
@[simp] theorem walkWeight_cons {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i j : Fin n)
    (rest : List (Fin n)) :
    walkWeight A i (j :: rest) = (A i j).untrop + walkWeight A j rest := rfl

/-- **Walk interpretation, upper half**: the matrix-power entry `(Aᵐ)ᵢⱼ` lower-bounds the weight of
*every* explicit length-`m` walk `i ⤳ j` — the optimum is at least as good as any concrete walk.
By induction on the vertex list, peeling the first edge (`A^(m+1) = A * Aᵐ`) and relaxing the
leading `inf` to the chosen next vertex. The matching attainment (some walk meets it) is the
converse half. -/
theorem untrop_pow_le_walkWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) MP)
    (i : Fin n) (l : List (Fin n)) :
    ((A ^ l.length) i (l.getLastD i)).untrop ≤ walkWeight A i l := by
  induction l generalizing i with
  | nil => simp [Matrix.one_apply_eq]
  | cons j rest ih =>
    rw [List.getLastD_cons, List.length_cons, pow_succ', Matrix.mul_apply, Finset.untrop_sum']
    refine le_trans (Finset.inf_le (Finset.mem_univ j)) ?_
    show (A i j).untrop + ((A ^ rest.length) j (rest.getLastD j)).untrop
        ≤ (A i j).untrop + walkWeight A j rest
    gcongr
    exact ih j

/-- **Walk interpretation, attainment half**: whenever `(Aᵐ)ᵢⱼ` is finite (`≠ +∞`, i.e. some walk
exists) the optimum is *attained* — there is an explicit length-`m` walk `i ⤳ j` whose weight equals
`(Aᵐ)ᵢⱼ`. Built vertex by vertex: the first-edge recursion's leading `inf` is attained at some `k₀`
(finite linear order), whose tail entry stays finite, so the induction supplies the rest of the walk.
Together with `untrop_pow_le_walkWeight` this says `(Aᵐ)ᵢⱼ` *is* the minimum walk weight. -/
theorem exists_walkWeight_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) :
    ∀ (m : ℕ) (i j : Fin n), ((A ^ m) i j).untrop ≠ ⊤ →
      ∃ l : List (Fin n), l.length = m ∧ l.getLastD i = j ∧
        walkWeight A i l = ((A ^ m) i j).untrop := by
  intro m
  induction m with
  | zero =>
    intro i j h
    by_cases hij : i = j
    · subst hij
      exact ⟨[], rfl, rfl, by simp [walkWeight, Matrix.one_apply_eq]⟩
    · exact absurd (by rw [pow_zero, Matrix.one_apply_ne hij]; rfl) h
  | succ m ih =>
    intro i j h
    haveI : Nonempty (Fin n) := ⟨i⟩
    have heq := untrop_pow_succ_apply_first A m i j
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k => (A i k).untrop + ((A ^ m) k j).untrop)
    rw [Finset.inf'_eq_inf, ← heq] at hk₀
    have hfin : ((A ^ m) k₀ j).untrop ≠ ⊤ := fun htop => h (by rw [hk₀, htop, WithTop.add_top])
    obtain ⟨l', hlen', hend', hw'⟩ := ih k₀ j hfin
    refine ⟨k₀ :: l', by simp [hlen'], ?_, ?_⟩
    · rw [List.getLastD_cons]; exact hend'
    · rw [walkWeight_cons, hw', ← hk₀]

/-- The **precedence graph** of a min-plus matrix: an edge `i → j` exists iff the entry is finite
(`≠ 𝟘 = +∞`). Its circuits carry the spectral theory (eigenvalue = min mean circuit, cyclicity). -/
def HasEdge {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i j : Fin n) : Prop := A i j ≠ 0

/-! ### Cyclicity: the predicate, a general case, and concrete witnesses
The cyclicity theorem (BCOQ Thm 3.112) states that an irreducible min-plus matrix's powers become
*pseudo-periodic*: `Aᵏ⁺ᶜ = (c·λ) ⊗ Aᵏ` past a finite rank, with cyclicity `c` and eigenvalue `λ`.
We record this conclusion as `IsPseudoPeriodicPow`, prove the **idempotent case in full generality**
(`exA`, `λ = 0`, `c = 1`), and pin the **nontrivial** shape (`λ = 1`, `c = 2`) with gate-verified
witnesses on the 2-cycle below — there the eigenvalue increment is genuinely exercised. -/

/-- **Ultimate pseudo-periodicity of the powers** — the conclusion of the cyclicity theorem (BCOQ
Thm 3.112) as a predicate: past rank `K`, advancing by `c` multiplies each entry by the eigenvalue
increment, `(Aᵏ⁺ᶜ)ᵢⱼ = (Aᵏ)ᵢⱼ ⊗ trop(c·λ)` (tropical `⊗ = +`). The general theorem asserts such
`c, K, λ` exist for any irreducible `A`; we record the predicate and prove the instances we can. -/
def IsPseudoPeriodicPow {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (c K : ℕ) (lam : ℤ) : Prop :=
  0 < c ∧ ∀ k, K ≤ k → ∀ i j,
    (A ^ (k + c)) i j = (A ^ k) i j * Tropical.trop (((c : ℤ) * lam : ℤ) : WithTop ℤ)

/-- `exA` is multiplicatively idempotent (`exA ⊗ exA = exA`): its `0`-weight self-loops make it a
closure operator. -/
theorem exA_mul_self : exA * exA = exA := by native_decide

/-- Powers of the idempotent `exA` collapse: `exAᵏ⁺¹ = exA` for every `k`. -/
theorem exA_pow_succ (k : ℕ) : exA ^ (k + 1) = exA := by
  induction k with
  | zero => rw [pow_one]
  | succ k ih => rw [pow_succ, ih, exA_mul_self]

/-- **First general (∀ k) cyclicity result**: the idempotent `exA` is pseudo-periodic with cyclicity
`c = 1`, rank `K = 1`, eigenvalue `λ = 0` — `exAᵏ⁺¹ = exAᵏ` for every `k ≥ 1` (both equal `exA`). The
idempotent case is exactly the sub-additive-closure case already computed closed-form in
`DeepWiki.UppSeq`; this is its matrix face. -/
theorem isPseudoPeriodicPow_exA : IsPseudoPeriodicPow exA 1 1 0 := by
  refine ⟨one_pos, ?_⟩
  rintro (_ | m) hk i j
  · simp at hk
  · rw [exA_pow_succ (m + 1), exA_pow_succ m]
    norm_num

/-- A 2-state min-plus matrix realizing a nontrivial cyclicity: the bidirectional edge `0 ↔ 1` of
weight `1`, diagonal `+∞ = 𝟘`. Its only circuit `0→1→0` has weight `2` over length `2`, so the
min-plus eigenvalue is `λ = 1` and the cyclicity is `c = 2`. -/
def twoCycleMP : Matrix (Fin 2) (Fin 2) MP :=
  !![0, Tropical.trop 1; Tropical.trop 1, 0]

/-- Sanity (gate-verified): `twoCycleMP² = diag 2` — the length-2 circuit weight lands on the
diagonal, off-diagonal is `+∞` (no length-2 walk between the two distinct vertices). -/
example : twoCycleMP ^ 2 = !![Tropical.trop 2, 0; 0, Tropical.trop 2] := by native_decide

/-- **Cyclicity witnessed** at rank 1 (BCOQ Thm 3.112, concrete): `A³ᵢⱼ = A¹ᵢⱼ ⊗ trop 2`, i.e.
`Aᵏ⁺ᶜ = (c·λ) ⊗ Aᵏ` with `c = 2`, `λ = 1` — every finite entry grows by `c·λ = 2` per period
(tropical `⊗ = +`; `+∞` stays `+∞`). -/
theorem twoCycleMP_cyclicity_at_one :
    ∀ i j, (twoCycleMP ^ 3) i j = twoCycleMP i j * Tropical.trop 2 := by native_decide

/-- **Cyclicity witnessed** at rank 2: `A⁴ᵢⱼ = A²ᵢⱼ ⊗ trop 2` — the same period-2, increment-2
relation one step on, confirming it is the steady pseudo-periodic regime, not a coincidence at `k=1`. -/
theorem twoCycleMP_cyclicity_at_two :
    ∀ i j, (twoCycleMP ^ 4) i j = (twoCycleMP ^ 2) i j * Tropical.trop 2 := by native_decide

end DeepWiki.MinPlusMatrix
