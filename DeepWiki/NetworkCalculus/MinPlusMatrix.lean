import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pigeonhole

/-! # Min-plus matrices — spectral theory toward the sub-additive-closure cyclicity theorem
The min-plus semiring `(ℤ ∪ {+∞}, min, +)` is Mathlib's `Tropical (WithTop ℤ)`: addition is `min`,
multiplication is `+`, `𝟘 = +∞ = ⊤`, `𝟙 = (0 : ℤ)`. Matrices over it inherit the (non-commutative)
semiring product `(A * B)ᵢⱼ = ⨁ₖ Aᵢₖ ⊗ Bₖⱼ = ⨅ₖ (Aᵢₖ + Bₖⱼ)` and powers `Aᵏ` from Mathlib (`WithTop ℤ`
has no `InfSet`, so the product `⨅` is spelled with `Finset.inf` via `Finset.untrop_sum'`).

Built here, toward BCOQ "Synchronization and Linearity" Thm 3.112:
* **Walk interpretation** — `(Aᵐ)ᵢⱼ` is the minimum weight of a length-`m` walk `i ⤳ j`
  (`untrop_pow_le_walkWeight` and `exists_walkWeight_eq`), with finiteness `untrop_pow_ne_top_iff`.
* **Eigenvalue bounds** — upper `untrop_pow_mul_le_nsmul_walkWeight` (iterating a circuit) and lower
  `walkWeight_ge_of_short` / `untrop_pow_diag_ge` (an integer rate valid on short circuits propagates,
  via circuit extraction `exists_circuit_extraction(_proper)`); they meet on a tight circuit, where the
  rate is exactly attained, `untrop_pow_mul_eq_of_tight` (`(Aᵏᵖ)ᵢᵢ = μ·kp`).
* **Closure termination** — with nonnegative circuits, walks collapse to length `< n`
  (`walkWeight_reduce_of_nonneg`), so the Kleene star is the finite truncation `⨁_{k<n} Aᵏ`
  (`exists_lt_untrop_pow_le`): the sub-additive closure `f* = ⨁ₘ f^⊗ᵐ` stabilizes at rank `n`.
* **Linear growth** — the deflated generalization to any rate `μ` (`walkWeight_reduce_of_rate`,
  `exists_le_untrop_pow_deflate`): `(Aᵏ)ᵢⱼ ≥ μ·k + C`, the eigenvalue's lower linear envelope.
* **Cyclicity predicate** — `IsPseudoPeriodicPow` (`Aᵏ⁺ᶜ = Aᵏ ⊗ trop(c·λ)`) with the stabilizing-powers
  case, eigenvalue uniqueness, closure under multiples, and concrete witnesses.

Remaining (research-scale): a canonical ℚ-valued eigenvalue, the upper linear envelope (needs
irreducibility), and the full cyclicity period (critical graph + spectral projector). -/

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

/-- **Weight is additive over concatenation**: a walk `i ⤳ (end of l₁) ⤳ (end of l₂)` splits into its
two legs, `walkWeight A i (l₁ ++ l₂) = walkWeight A i l₁ + walkWeight A (l₁.getLastD i) l₂`. The
algebraic backbone of every walk-decomposition argument (toward the eigenvalue lower bound). -/
theorem walkWeight_append {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n)
    (l₁ l₂ : List (Fin n)) :
    walkWeight A i (l₁ ++ l₂) = walkWeight A i l₁ + walkWeight A (l₁.getLastD i) l₂ := by
  induction l₁ generalizing i with
  | nil => simp [walkWeight]
  | cons a t ih =>
    simp only [List.cons_append, walkWeight_cons, List.getLastD_cons]
    rw [ih, add_assoc]

/-- **Repeating a circuit scales its weight**: traversing a circuit `l` at `i` (`l.getLastD i = i`)
`k` times is the walk `(replicate k l).flatten`, of weight `k • walkWeight A i l`. The explicit walk
witnessing the diagonal bound `untrop_pow_mul_le_nsmul_walkWeight`. -/
theorem walkWeight_replicate_circuit {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n)
    (l : List (Fin n)) (hl : l.getLastD i = i) (k : ℕ) :
    walkWeight A i (List.replicate k l).flatten = k • walkWeight A i l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, walkWeight_append, hl, ih, succ_nsmul, add_comm]

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

/-- **Reachability = finiteness** (both walk-interpretation halves at once): the entry `(Aᵐ)ᵢⱼ` is
finite (`≠ +∞`) iff some length-`m` walk `i ⤳ j` has finite weight. Forward by `exists_walkWeight_eq`
(the optimum is a concrete finite walk); backward by `untrop_pow_le_walkWeight` (the entry is `≤` that
walk, hence finite). A `0/∞` reachability test for matrix powers via explicit walks. -/
theorem untrop_pow_ne_top_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (m : ℕ) (i j : Fin n) :
    ((A ^ m) i j).untrop ≠ ⊤ ↔
      ∃ l : List (Fin n), l.length = m ∧ l.getLastD i = j ∧ walkWeight A i l ≠ ⊤ := by
  constructor
  · intro h
    obtain ⟨l, hlen, hend, hw⟩ := exists_walkWeight_eq A m i j h
    exact ⟨l, hlen, hend, by rw [hw]; exact h⟩
  · rintro ⟨l, hlen, hend, hw⟩
    have hle := untrop_pow_le_walkWeight A i l
    rw [hlen, hend] at hle
    exact ne_top_of_le_ne_top hw hle

/-- **Diagonal grows at most linearly** (the subadditive Fekete estimate, integer form): iterating a
length-`p` loop at `i` `k` times bounds the diagonal, `(Aᵏᵖ)ᵢᵢ ≤ k • (Aᵖ)ᵢᵢ`. By induction on `k`
from `untrop_pow_add_le_diag`. No analysis needed — the `•` is `ℕ`-scaling on `WithTop ℤ`. -/
theorem untrop_pow_mul_le_nsmul {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (p : ℕ) (i : Fin n) (k : ℕ) :
    ((A ^ (k * p)) i i).untrop ≤ k • ((A ^ p) i i).untrop := by
  induction k with
  | zero => simp [Matrix.one_apply_eq]
  | succ k ih =>
    rw [Nat.succ_mul, succ_nsmul]
    exact le_trans (untrop_pow_add_le_diag A (k * p) p i) (by gcongr)

/-- **Eigenvalue upper bound via an explicit circuit**: any circuit `l` at `i` (length `p`, returning
to `i`, weight `w`) caps the diagonal growth — `(Aᵏᵖ)ᵢᵢ ≤ k • w` (traverse the circuit `k` times).
So the min-plus eigenvalue `λ = limₖ (Aᵏᵖ)ᵢᵢ / (kp)` is `≤ w / p`, the circuit's mean weight: every
circuit's mean is an upper bound for `λ`. Combines `untrop_pow_mul_le_nsmul` with the walk bound. -/
theorem untrop_pow_mul_le_nsmul_walkWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) MP)
    (i : Fin n) (l : List (Fin n)) (hl : l.getLastD i = i) (k : ℕ) :
    ((A ^ (k * l.length)) i i).untrop ≤ k • walkWeight A i l := by
  have hc : ((A ^ l.length) i i).untrop ≤ walkWeight A i l := by
    have h := untrop_pow_le_walkWeight A i l
    rwa [hl] at h
  calc ((A ^ (k * l.length)) i i).untrop
      ≤ k • ((A ^ l.length) i i).untrop := untrop_pow_mul_le_nsmul A l.length i k
    _ ≤ k • walkWeight A i l := by gcongr

/-! ### Toward the eigenvalue lower bound: circuit extraction
The lower bound `(Aᵐ)ᵢᵢ ≥ m·λ` rests on decomposing a long walk into a short path plus circuits. The
two pieces below are its scaffolding: a *pigeonhole* (a walk longer than the vertex count repeats a
vertex) and the *weight bookkeeping* (a `prefix ++ circuit ++ suffix` split decomposes additively into
the shortened walk plus the circuit). Assembling these into the full extraction is the next step. -/

/-- **Pigeonhole on walk vertices**: a walk `i ⤳ …` whose vertex count `l.length + 1` exceeds `n`
repeats a vertex — there are positions `a < b` in the vertex list `i :: l` with the same vertex. The
gap `[a, b]` is the circuit the lower-bound argument extracts. -/
theorem exists_lt_repeated_vertex {n : ℕ} (i : Fin n) (l : List (Fin n)) (h : n ≤ l.length) :
    ∃ a b : Fin (i :: l).length, a < b ∧ (i :: l).get a = (i :: l).get b := by
  obtain ⟨a, b, hab, hval⟩ := Fintype.exists_ne_map_eq_of_card_lt (i :: l).get
    (by simp only [Fintype.card_fin, List.length_cons]; omega)
  rcases lt_or_gt_of_ne hab with h1 | h1
  · exact ⟨a, b, h1, hval⟩
  · exact ⟨b, a, h1, hval.symm⟩

/-- **Circuit extraction, weight bookkeeping**: if a walk splits as `prefix ++ circuit ++ suffix` with
the prefix ending at `v` (`lp.getLastD i = v`) and the circuit returning to `v` (`lc.getLastD v = v`),
its weight is the shortened walk `prefix ++ suffix` plus the circuit weight. Pure `walkWeight_append`
algebra — the additive core of removing a circuit from a walk. -/
theorem walkWeight_circuit_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i v : Fin n)
    (lp lc ls : List (Fin n)) (hpv : lp.getLastD i = v) (hcv : lc.getLastD v = v) :
    walkWeight A i (lp ++ lc ++ ls) = walkWeight A i (lp ++ ls) + walkWeight A v lc := by
  rw [List.append_assoc, walkWeight_append, hpv, walkWeight_append, hcv, walkWeight_append, hpv,
    add_comm (walkWeight A v lc) (walkWeight A v ls), ← add_assoc]

/-- **List helper**: the last vertex of a length-`a` prefix of the walk `i :: l` is its `a`-th vertex,
`(l.take a).getLastD i = (i :: l)[a]` (as `getElem?`-with-default). Turns the pigeonhole's index `a`
into the endpoint condition `prefix.getLastD i = vᵃ` that `walkWeight_circuit_decomp` consumes. -/
theorem getLastD_take {α : Type*} (i : α) (l : List α) (a : ℕ) (ha : a ≤ l.length) :
    (l.take a).getLastD i = ((i :: l)[a]?).getD i := by
  induction a generalizing i l with
  | zero => simp
  | succ a ih =>
    cases l with
    | nil => simp at ha
    | cons x l' =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at ha
      simp only [List.take_succ_cons, List.getLastD_cons, List.getElem?_cons_succ]
      rw [ih x l' ha, List.getElem?_eq_getElem (show a < (x :: l').length by
        simp only [List.length_cons]; omega)]
      rfl

/-- **List helper**: the `prefix ++ circuit ++ suffix` split of a walk's tail at indices `a ≤ b`
reassembles to the whole, `l.take a ++ (l.drop a).take (b - a) ++ l.drop b = l`. The structural side of
circuit extraction (the weight side is `walkWeight_circuit_decomp`). -/
theorem take_take_drop_drop {α : Type*} (l : List α) (a b : ℕ) (hab : a ≤ b) :
    l.take a ++ (l.drop a).take (b - a) ++ l.drop b = l := by
  rw [List.append_assoc,
    show l.drop b = (l.drop a).drop (b - a) from by rw [List.drop_drop]; congr 1; omega,
    List.take_append_drop, List.take_append_drop]

/-- **List helper**: the last element of `l₁ ++ l₂` is `l₂`'s last, falling back through `l₁`'s last
to the default — `(l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d)`. Lets circuit extraction keep
the walk's endpoint (`prefix ++ suffix` ends where `prefix ++ circuit ++ suffix` does). -/
theorem getLastD_append {α : Type*} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d) := by
  induction l₁ generalizing d with
  | nil => simp
  | cons a t ih => rw [List.cons_append, List.getLastD_cons, ih, List.getLastD_cons]

/-- **List helper**: the last vertex of the circuit segment `(l.drop A).take (B - A)` (for `A < B ≤
length`) is the `B`-th walk vertex `(i :: l)[B]`, independent of the default — the segment is nonempty
so `getLastD` returns its genuine last element. Supplies the circuit's return-vertex condition. -/
theorem getLastD_drop_take {α : Type*} (i x : α) (l : List α) (A B : ℕ)
    (hAB : A < B) (hB : B ≤ l.length) :
    ((l.drop A).take (B - A)).getLastD x = (i :: l)[B]?.getD x := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have key : (x :: l.drop A)[k + 1 - A]? = (i :: l)[k + 1]? := by
    rw [show k + 1 - A = (k - A) + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop,
        List.getElem?_cons_succ, show A + (k - A) = k by omega]
  rw [getLastD_take x (l.drop A) (k + 1 - A) (by rw [List.length_drop]; omega), key]

/-- **Circuit extraction core** (index form): given a repeated vertex at positions `a < b` of the
walk `i :: l` (`(i::l)[a]? = (i::l)[b]?`), split the tail as `prefix ++ circuit ++ suffix` with the
prefix `= l.take a` ending at the repeated vertex `v` and the circuit nonempty and returning to `v`.
Assembles the pigeonhole-free pieces; exposing `lp = l.take a` lets callers force `lp ≠ []` via `a`. -/
theorem circuit_extraction_core {n : ℕ} (i : Fin n) (l : List (Fin n)) (a b : ℕ)
    (hab : a < b) (hb : b ≤ l.length) (hval : (i :: l)[a]? = (i :: l)[b]?) :
    ∃ (lp lc ls : List (Fin n)) (v : Fin n),
      l = lp ++ lc ++ ls ∧ lp = l.take a ∧ lc ≠ [] ∧ lp.getLastD i = v ∧ lc.getLastD v = v := by
  refine ⟨l.take a, (l.drop a).take (b - a), l.drop b, ((i :: l)[a]?).getD i,
    (take_take_drop_drop l a b (le_of_lt hab)).symm, rfl, ?_, ?_, ?_⟩
  · have : 0 < ((l.drop a).take (b - a)).length := by
      rw [List.length_take, List.length_drop]; omega
    exact List.ne_nil_of_length_pos this
  · rw [getLastD_take i l a (by omega)]
  · have ha : a < (i :: l).length := by simp only [List.length_cons]; omega
    rw [getLastD_drop_take i (((i :: l)[a]?).getD i) l a b hab hb, ← hval,
        List.getElem?_eq_getElem ha]
    rfl

/-- **Single-circuit extraction**: any walk `i ⤳ …` with at least `n` edges (so `> n` vertices)
splits as `prefix ++ circuit ++ suffix`, where the prefix ends at some vertex `v`, and the circuit is
nonempty and returns to `v`. The pigeonhole supplies the repeated vertex; `circuit_extraction_core`
does the bookkeeping. With `walkWeight_circuit_decomp` this peels a circuit off a long walk. -/
theorem exists_circuit_extraction {n : ℕ} (i : Fin n) (l : List (Fin n)) (hl : n ≤ l.length) :
    ∃ (lp lc ls : List (Fin n)) (v : Fin n),
      l = lp ++ lc ++ ls ∧ lc ≠ [] ∧ lp.getLastD i = v ∧ lc.getLastD v = v := by
  obtain ⟨a, b, hab, hval⟩ := exists_lt_repeated_vertex i l hl
  have hve : (i :: l)[a.val]? = (i :: l)[b.val]? := by
    rw [List.getElem?_eq_getElem a.isLt, List.getElem?_eq_getElem b.isLt]
    exact congrArg some hval
  obtain ⟨lp, lc, ls, v, hsplit, _, hlc, hpv, hcv⟩ :=
    circuit_extraction_core i l a.val b.val hab
      (by have := b.isLt; simp only [List.length_cons] at this; omega) hve
  exact ⟨lp, lc, ls, v, hsplit, hlc, hpv, hcv⟩

/-- **Proper circuit extraction** (nonempty prefix): for `l` *longer* than the vertex count
(`n < l.length`), pigeonholing the interior vertices yields a split where **both** the prefix and the
circuit are nonempty. Hence the shortened walk `prefix ++ suffix` *and* the circuit are each strictly
shorter than `l` — the version that lets the lower-bound strong induction recurse on both pieces
(avoiding the degenerate closed-walk split where the circuit is the whole walk). -/
theorem exists_circuit_extraction_proper {n : ℕ} (i : Fin n) (l : List (Fin n)) (hl : n < l.length) :
    ∃ (lp lc ls : List (Fin n)) (v : Fin n),
      l = lp ++ lc ++ ls ∧ lp ≠ [] ∧ lc ≠ [] ∧ lp.getLastD i = v ∧ lc.getLastD v = v := by
  obtain ⟨a, b, hab, hval⟩ := Fintype.exists_ne_map_eq_of_card_lt l.get (by simpa using hl)
  have hve : ∀ p q : Fin l.length, l.get p = l.get q →
      (i :: l)[p.val + 1]? = (i :: l)[q.val + 1]? := by
    intro p q hpq
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_eq_getElem p.isLt, List.getElem?_eq_getElem q.isLt]
    exact congrArg some hpq
  rcases lt_or_gt_of_ne (show a.val ≠ b.val from fun h => hab (Fin.ext h)) with h | h
  · obtain ⟨lp, lc, ls, v, hsplit, hlp, hlc, hpv, hcv⟩ :=
      circuit_extraction_core i l (a.val + 1) (b.val + 1) (by omega) (by omega) (hve a b hval)
    refine ⟨lp, lc, ls, v, hsplit, ?_, hlc, hpv, hcv⟩
    rw [hlp]
    exact List.ne_nil_of_length_pos (by rw [List.length_take]; have := a.isLt; omega)
  · obtain ⟨lp, lc, ls, v, hsplit, hlp, hlc, hpv, hcv⟩ :=
      circuit_extraction_core i l (b.val + 1) (a.val + 1) (by omega) (by omega) (hve b a hval.symm)
    refine ⟨lp, lc, ls, v, hsplit, ?_, hlc, hpv, hcv⟩
    rw [hlp]
    exact List.ne_nil_of_length_pos (by rw [List.length_take]; have := b.isLt; omega)

/-- **Extraction, weight form** (the lower-bound recursion step): a walk `i ⤳ …` with at least `n`
edges has a *strictly shorter* walk `l'` with the **same endpoint** (`l'.getLastD i = l.getLastD i`)
plus a nonempty circuit `lc` at some `v`, decomposing the weight additively: `walkWeight A i l =
walkWeight A i l' + walkWeight A v lc`. Strong induction on this peels a walk down to a simple path
plus circuits — each circuit's weight bounded below by `λ·(length)` gives `(Aᵐ)ᵢᵢ ≥ m·λ`. -/
theorem exists_walkWeight_shorter {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n)
    (l : List (Fin n)) (hl : n ≤ l.length) :
    ∃ (l' lc : List (Fin n)) (v : Fin n),
      l'.length < l.length ∧ l'.getLastD i = l.getLastD i ∧ lc ≠ [] ∧ lc.getLastD v = v ∧
      walkWeight A i l = walkWeight A i l' + walkWeight A v lc := by
  obtain ⟨lp, lc, ls, v, hsplit, hlc, hpv, hcv⟩ := exists_circuit_extraction i l hl
  refine ⟨lp ++ ls, lc, v, ?_, ?_, hlc, hcv, ?_⟩
  · have : 0 < lc.length := List.length_pos_of_ne_nil hlc
    rw [hsplit]; simp only [List.length_append]; omega
  · rw [hsplit, getLastD_append, getLastD_append, getLastD_append, hpv, hcv]
  · rw [hsplit]; exact walkWeight_circuit_decomp A i v lp lc ls hpv hcv

/-- **Proper extraction, weight form**: for `l` longer than the vertex count, the split gives a
shorter walk `l'` *and* a circuit `lc` that are **both** strictly shorter than `l` (lengths summing to
`l.length`), with `l'` keeping the endpoint and the additive weight decomposition. The version the
strong induction recurses on — both pieces shrink, so it terminates. -/
theorem exists_walkWeight_shorter_proper {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (i : Fin n)
    (l : List (Fin n)) (hl : n < l.length) :
    ∃ (l' lc : List (Fin n)) (v : Fin n),
      l'.length < l.length ∧ lc.length < l.length ∧ l'.getLastD i = l.getLastD i ∧
      lc.getLastD v = v ∧ l'.length + lc.length = l.length ∧
      walkWeight A i l = walkWeight A i l' + walkWeight A v lc := by
  obtain ⟨lp, lc, ls, v, hsplit, hlp, hlc, hpv, hcv⟩ := exists_circuit_extraction_proper i l hl
  have hlcpos : 0 < lc.length := List.length_pos_of_ne_nil hlc
  have hlppos : 0 < lp.length := List.length_pos_of_ne_nil hlp
  refine ⟨lp ++ ls, lc, v, ?_, ?_, ?_, hcv, ?_, ?_⟩
  · rw [hsplit]; simp only [List.length_append]; omega
  · rw [hsplit]; simp only [List.length_append]; omega
  · rw [hsplit, getLastD_append, getLastD_append, getLastD_append, hpv, hcv]
  · rw [hsplit]; simp only [List.length_append]; omega
  · rw [hsplit]; exact walkWeight_circuit_decomp A i v lp lc ls hpv hcv

/-- **Eigenvalue lower bound** (closed-walk form, division-free): if every *short* closed walk
(length `≤ n`) has weight at least `μ · length` for an integer rate `μ`, then **every** closed walk
does — `μ · l.length ≤ walkWeight A i l`. Strong induction on length via `exists_walkWeight_shorter_proper`:
a long closed walk splits into a shorter closed walk plus a closed circuit, both bounded by the IH,
and the rate adds. Taking `μ` to be the min mean over short circuits gives `(Aᵐ)ᵢᵢ ≥ m · λ` — the
lower half of the cyclicity eigenvalue, with no rationals or limits. -/
theorem walkWeight_ge_of_short {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (μ : ℤ)
    (hshort : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (↑(μ * l₀.length) : WithTop ℤ) ≤ walkWeight A v l₀) :
    ∀ (i : Fin n) (l : List (Fin n)), l.getLastD i = i →
      (↑(μ * l.length) : WithTop ℤ) ≤ walkWeight A i l := by
  suffices H : ∀ N (i : Fin n) (l : List (Fin n)), l.length = N → l.getLastD i = i →
      (↑(μ * l.length) : WithTop ℤ) ≤ walkWeight A i l by
    intro i l hcl; exact H l.length i l rfl hcl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i l hN hcl
    by_cases hle : l.length ≤ n
    · exact hshort i l hcl hle
    · rw [not_le] at hle
      obtain ⟨l', lc, v, hl'len, hlclen, hl'end, hcv, hsum, hwt⟩ :=
        exists_walkWeight_shorter_proper A i l hle
      have hcl' : l'.getLastD i = i := by rw [hl'end]; exact hcl
      have ih1 := ih l'.length (by omega) i l' rfl hcl'
      have ih2 := ih lc.length (by omega) v lc rfl hcv
      have hsum' : μ * (l.length : ℤ) = μ * l'.length + μ * lc.length := by
        have : (l.length : ℤ) = l'.length + lc.length := by exact_mod_cast hsum.symm
        rw [this]; ring
      rw [hwt]
      calc (↑(μ * l.length) : WithTop ℤ)
          = ↑(μ * l'.length) + ↑(μ * lc.length) := by rw [← WithTop.coe_add]; exact_mod_cast hsum'
        _ ≤ walkWeight A i l' + walkWeight A v lc := add_le_add ih1 ih2

/-- **Eigenvalue lower bound, matrix form**: with a rate `μ` valid on all short closed walks, the
diagonal power entry is bounded below linearly, `μ · m ≤ (Aᵐ)ᵢᵢ`. The `+∞` entry is bounded trivially;
a finite entry is the weight of a length-`m` closed walk (`exists_walkWeight_eq` at `j = i`), which
`walkWeight_ge_of_short` bounds. Paired with `untrop_pow_mul_le_nsmul_walkWeight` (the upper bound,
`(Aᵏᵖ)ᵢᵢ ≤ k·weight`), this pins the diagonal growth rate — the min-plus eigenvalue. -/
theorem untrop_pow_diag_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (μ : ℤ)
    (hshort : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (↑(μ * l₀.length) : WithTop ℤ) ≤ walkWeight A v l₀)
    (i : Fin n) (m : ℕ) :
    (↑(μ * m) : WithTop ℤ) ≤ ((A ^ m) i i).untrop := by
  by_cases htop : ((A ^ m) i i).untrop = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨l, hlen, hend, hw⟩ := exists_walkWeight_eq A m i i htop
    have hge := walkWeight_ge_of_short A μ hshort i l hend
    rw [hlen] at hge
    rw [hw] at hge
    exact hge

/-- **Nonnegative circuits collapse walks to simple ones** — the route to closure termination. If
every short closed walk has nonnegative weight (so, by `walkWeight_ge_of_short`, *every* circuit does),
then any walk `i ⤳ j` has a walk of length `< n` with the **same endpoints** and weight `≤` it: a
circuit can always be deleted without raising the weight (`le_add_of_nonneg_right`), and deletion
shrinks length. Hence the min-weight `i ⤳ j` walk is attained at length `< n` — the (min,plus) Kleene
star `⨁ₖ Aᵏ` is the finite truncation `⨁_{k<n} Aᵏ`, i.e. the sub-additive closure terminates. -/
theorem walkWeight_reduce_of_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) MP)
    (hnn : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (0 : WithTop ℤ) ≤ walkWeight A v l₀) :
    ∀ (i : Fin n) (l : List (Fin n)),
      ∃ l', l'.length < n ∧ l'.getLastD i = l.getLastD i ∧ walkWeight A i l' ≤ walkWeight A i l := by
  have hall : ∀ (w : Fin n) (lc : List (Fin n)), lc.getLastD w = w →
      (0 : WithTop ℤ) ≤ walkWeight A w lc := by
    intro w lc hcl
    have := walkWeight_ge_of_short A 0 (fun v l₀ h1 h2 => by simpa using hnn v l₀ h1 h2) w lc hcl
    simpa using this
  suffices H : ∀ N (i : Fin n) (l : List (Fin n)), l.length = N →
      ∃ l', l'.length < n ∧ l'.getLastD i = l.getLastD i ∧ walkWeight A i l' ≤ walkWeight A i l by
    intro i l; exact H l.length i l rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i l hN
    by_cases hlt : l.length < n
    · exact ⟨l, hlt, rfl, le_refl _⟩
    · rw [not_lt] at hlt
      obtain ⟨l₁, lc, v, hl1len, hl1end, hlcne, hcv, hwt⟩ := exists_walkWeight_shorter A i l hlt
      obtain ⟨l', hl'len, hl'end, hl'wt⟩ := ih l₁.length (by omega) i l₁ rfl
      refine ⟨l', hl'len, by rw [hl'end, hl1end], ?_⟩
      calc walkWeight A i l' ≤ walkWeight A i l₁ := hl'wt
        _ ≤ walkWeight A i l := by rw [hwt]; exact le_add_of_nonneg_right (hall v lc hcv)

/-- **Kleene-star finiteness** (matrix form of closure termination): with nonnegative circuits, for
every power `k` some power `m < n` is entrywise at least as good, `(Aᵐ)ᵢⱼ ≤ (Aᵏ)ᵢⱼ`. So the (min,plus)
star `⨁ₖ Aᵏ = ⨁_{m<n} Aᵏ` is reached by powers below `n` — the sub-additive closure stabilizes at rank
`n`. The `+∞` entry takes `m = 0`; a finite entry's optimal length-`k` walk reduces (by
`walkWeight_reduce_of_nonneg`) to a length-`< n` walk of no greater weight, which `(Aᵐ)ᵢⱼ` underbids. -/
theorem exists_lt_untrop_pow_le {n : ℕ} (A : Matrix (Fin n) (Fin n) MP)
    (hnn : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (0 : WithTop ℤ) ≤ walkWeight A v l₀)
    (i j : Fin n) (k : ℕ) :
    ∃ m, m < n ∧ ((A ^ m) i j).untrop ≤ ((A ^ k) i j).untrop := by
  by_cases htop : ((A ^ k) i j).untrop = ⊤
  · exact ⟨0, i.pos, by rw [htop]; exact le_top⟩
  · obtain ⟨l, hlen, hend, hw⟩ := exists_walkWeight_eq A k i j htop
    obtain ⟨l', hl'len, hl'end, hl'wt⟩ := walkWeight_reduce_of_nonneg A hnn i l
    refine ⟨l'.length, hl'len, ?_⟩
    have hle := untrop_pow_le_walkWeight A i l'
    rw [hl'end, hend] at hle
    calc ((A ^ l'.length) i j).untrop ≤ walkWeight A i l' := hle
      _ ≤ walkWeight A i l := hl'wt
      _ = ((A ^ k) i j).untrop := hw

/-- **Rate-`μ` reduction** (general growth, the deflation generalizing `walkWeight_reduce_of_nonneg`):
for *any* integer rate `μ` valid on short circuits (`μ ≤ min mean`), every walk has one of length `≤ n`
with the same endpoints whose `μ`-*deflated* weight is no larger — stated subtraction-free as
`walkWeight l' + μ·|l| ≤ walkWeight l + μ·|l'|` (i.e. `weight l' − μ·|l'| ≤ weight l − μ·|l|`). Deleting a
circuit drops the deflated weight (its weight is `≥ μ·length`), and deflated weight is non-increasing. -/
theorem walkWeight_reduce_of_rate {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (μ : ℤ)
    (hμ : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (↑(μ * l₀.length) : WithTop ℤ) ≤ walkWeight A v l₀) :
    ∀ (i : Fin n) (l : List (Fin n)),
      ∃ l', l'.length ≤ n ∧ l'.getLastD i = l.getLastD i ∧
        walkWeight A i l' + (↑(μ * (l.length : ℤ)) : WithTop ℤ)
          ≤ walkWeight A i l + (↑(μ * (l'.length : ℤ)) : WithTop ℤ) := by
  have hall := walkWeight_ge_of_short A μ hμ
  suffices H : ∀ N (i : Fin n) (l : List (Fin n)), l.length = N →
      ∃ l', l'.length ≤ n ∧ l'.getLastD i = l.getLastD i ∧
        walkWeight A i l' + (↑(μ * (l.length : ℤ)) : WithTop ℤ)
          ≤ walkWeight A i l + (↑(μ * (l'.length : ℤ)) : WithTop ℤ) by
    intro i l; exact H l.length i l rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i l hN
    by_cases hle : l.length ≤ n
    · exact ⟨l, hle, rfl, le_refl _⟩
    · rw [not_le] at hle
      obtain ⟨l₁, lc, v, hl1len, hlclen, hl1end, hcv, hsum, hwt⟩ :=
        exists_walkWeight_shorter_proper A i l hle
      obtain ⟨l', hl'len, hl'end, hl'inv⟩ := ih l₁.length (by omega) i l₁ rfl
      refine ⟨l', hl'len, by rw [hl'end, hl1end], ?_⟩
      have hcoe : (↑(μ * (l₁.length : ℤ)) : WithTop ℤ) + ↑(μ * (lc.length : ℤ))
          = ↑(μ * (l.length : ℤ)) := by
        rw [← WithTop.coe_add]; congr 1
        have : (l.length : ℤ) = l₁.length + lc.length := by exact_mod_cast hsum.symm
        rw [this]; ring
      have step1 : walkWeight A i l₁ + (↑(μ * (lc.length : ℤ)) : WithTop ℤ) ≤ walkWeight A i l := by
        rw [hwt]; gcongr; exact hall v lc hcv
      calc walkWeight A i l' + (↑(μ * (l.length : ℤ)) : WithTop ℤ)
          = walkWeight A i l' + ↑(μ * (l₁.length : ℤ)) + ↑(μ * (lc.length : ℤ)) := by
            rw [add_assoc, hcoe]
        _ ≤ walkWeight A i l₁ + ↑(μ * (l'.length : ℤ)) + ↑(μ * (lc.length : ℤ)) := by gcongr
        _ = walkWeight A i l₁ + ↑(μ * (lc.length : ℤ)) + ↑(μ * (l'.length : ℤ)) := by
            rw [add_right_comm]
        _ ≤ walkWeight A i l + ↑(μ * (l'.length : ℤ)) := by gcongr

/-- **Rate-`μ` Kleene finiteness** (matrix form of the general growth bound): with rate `μ` valid on
short circuits, for every power `k` some power `m ≤ n` deflation-beats it,
`(Aᵐ)ᵢⱼ − μ·m ≤ (Aᵏ)ᵢⱼ − μ·k` (subtraction-free: `(Aᵐ)ᵢⱼ + μ·k ≤ (Aᵏ)ᵢⱼ + μ·m`). So `(Aᵏ)ᵢⱼ ≥ μ·k + C`
for a constant `C` (the min deflated power below `n`): the powers grow at least linearly at rate `μ`.
Taking `μ` the min mean circuit, this is the min-plus eigenvalue's linear-growth lower envelope. -/
theorem exists_le_untrop_pow_deflate {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (μ : ℤ)
    (hμ : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (↑(μ * l₀.length) : WithTop ℤ) ≤ walkWeight A v l₀)
    (i j : Fin n) (k : ℕ) :
    ∃ m, m ≤ n ∧ ((A ^ m) i j).untrop + (↑(μ * (k : ℤ)) : WithTop ℤ)
      ≤ ((A ^ k) i j).untrop + (↑(μ * (m : ℤ)) : WithTop ℤ) := by
  by_cases htop : ((A ^ k) i j).untrop = ⊤
  · exact ⟨0, Nat.zero_le n, by rw [htop, top_add]; exact le_top⟩
  · obtain ⟨l, hlen, hend, hw⟩ := exists_walkWeight_eq A k i j htop
    obtain ⟨l', hl'len, hl'end, hl'inv⟩ := walkWeight_reduce_of_rate A μ hμ i l
    refine ⟨l'.length, hl'len, ?_⟩
    have hle := untrop_pow_le_walkWeight A i l'
    rw [hl'end, hend] at hle
    calc ((A ^ l'.length) i j).untrop + (↑(μ * (k : ℤ)) : WithTop ℤ)
        ≤ walkWeight A i l' + ↑(μ * (k : ℤ)) := by gcongr
      _ = walkWeight A i l' + ↑(μ * (l.length : ℤ)) := by rw [hlen]
      _ ≤ walkWeight A i l + ↑(μ * (l'.length : ℤ)) := hl'inv
      _ = ((A ^ k) i j).untrop + ↑(μ * (l'.length : ℤ)) := by rw [hw]

/-- **The eigenvalue is attained on a tight circuit** (upper meets lower): if some length-`p` circuit
at `i` is *tight* for the rate `μ` (`(Aᵖ)ᵢᵢ = μ·p`, i.e. its mean is exactly `μ`), then along its
multiples the diagonal is exactly linear, `(Aᵏᵖ)ᵢᵢ = μ·kp`. The `≤` repeats the tight circuit
(`untrop_pow_mul_le_nsmul`); the `≥` is the lower bound (`untrop_pow_diag_ge`). So when `μ` is the min
mean circuit, the growth rate `μ` is genuinely achieved — the min-plus eigenvalue, exactly. -/
theorem untrop_pow_mul_eq_of_tight {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (μ : ℤ)
    (hμ : ∀ (v : Fin n) (l₀ : List (Fin n)), l₀.getLastD v = v → l₀.length ≤ n →
      (↑(μ * l₀.length) : WithTop ℤ) ≤ walkWeight A v l₀)
    (i : Fin n) (p : ℕ) (htight : ((A ^ p) i i).untrop = (↑(μ * (p : ℤ)) : WithTop ℤ)) (k : ℕ) :
    ((A ^ (k * p)) i i).untrop = (↑(μ * ((k * p : ℕ) : ℤ)) : WithTop ℤ) := by
  apply le_antisymm
  · have h := untrop_pow_mul_le_nsmul A p i k
    rw [htight] at h
    refine h.trans (le_of_eq ?_)
    rw [← WithTop.coe_nsmul, nsmul_eq_mul]
    congr 1; push_cast; ring
  · exact untrop_pow_diag_ge A μ hμ i (k * p)

/-! ### The min-plus eigenvalue, as the minimum mean cycle
The growth rate `λ` characterized abstractly by the bounds above is, concretely, the minimum mean over
circuits. By the reduction `walkWeight_reduce_of_nonneg`/`exists_lt_untrop_pow_le`, only circuits of
length `≤ n` matter, so the minimum is over a finite set and lands in `WithTop ℚ` (`⊤` iff the matrix
is acyclic). -/

/-- Mean weight of the minimum-weight length-`p` circuit at `v`, in `WithTop ℚ` (`⊤` when there is no
length-`p` circuit at `v`, i.e. `(Aᵖ)ᵥᵥ = +∞`): the diagonal entry divided by the length. -/
def cycleMean {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (v : Fin n) (p : ℕ) : WithTop ℚ :=
  WithTop.map (fun z : ℤ => (z : ℚ) / (p : ℚ)) ((A ^ p) v v).untrop

/-- The **min-plus eigenvalue** `λ(A)`: the minimum mean over short circuits (lengths `1..n`), in
`WithTop ℚ`. Only short circuits are needed — longer ones never beat them (`exists_lt_untrop_pow_le`).
`λ = ⊤` exactly when `A` is acyclic. -/
def minMeanCycle {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) : WithTop ℚ :=
  (Finset.univ ×ˢ Finset.Icc 1 n).inf (fun vp => cycleMean A vp.1 vp.2)

/-- `λ(A)` is a lower bound for every short circuit's mean (it is their minimum). -/
theorem minMeanCycle_le {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (v : Fin n) (p : ℕ)
    (hp1 : 1 ≤ p) (hpn : p ≤ n) : minMeanCycle A ≤ cycleMean A v p := by
  unfold minMeanCycle
  have hmem : ((v, p) : Fin n × ℕ) ∈ Finset.univ ×ˢ Finset.Icc 1 n := by
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]; exact ⟨hp1, hpn⟩
  exact Finset.inf_le hmem

/-- **`λ(A)` is attained** by a short circuit (`n ≥ 1`): some `v` and length `1 ≤ p ≤ n` have
`λ(A) = cycleMean A v p` — the argmin of the finite circuit-mean set. With `minMeanCycle_le` this is
the textbook characterization: `λ(A)` is the minimum mean over circuits, achieved. -/
theorem minMeanCycle_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) MP) (hn : 1 ≤ n) :
    ∃ v p, 1 ≤ p ∧ p ≤ n ∧ minMeanCycle A = cycleMean A v p := by
  have hne : (Finset.univ ×ˢ Finset.Icc 1 n : Finset (Fin n × ℕ)).Nonempty := by
    refine ⟨(⟨0, hn⟩, 1), ?_⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and]
    exact ⟨le_refl 1, hn⟩
  obtain ⟨⟨v, p⟩, hmem, heq⟩ := Finset.exists_mem_eq_inf' hne (fun vp => cycleMean A vp.1 vp.2)
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and] at hmem
  refine ⟨v, p, hmem.1, hmem.2, ?_⟩
  rw [minMeanCycle, ← Finset.inf'_eq_inf hne]
  exact heq

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

/-- **Stabilizing powers are pseudo-periodic** (the trivial-eigenvalue cyclicity, in full generality):
if the powers stabilize at rank `K` (`Aᴷ⁺¹ = Aᴷ`) then `A` is pseudo-periodic with cyclicity `c = 1`,
rank `K`, eigenvalue `λ = 0`. Once one step stabilizes, all do (`Nat.le_induction`), and `λ = 0` means
the increment `trop(1·0) = 𝟙` is trivial. This is the general face of the idempotent case below. -/
theorem isPseudoPeriodicPow_of_pow_succ_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) MP} {K : ℕ}
    (h : A ^ (K + 1) = A ^ K) : IsPseudoPeriodicPow A 1 K 0 := by
  refine ⟨one_pos, ?_⟩
  have key : ∀ k, K ≤ k → A ^ (k + 1) = A ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k hk ih =>
      calc A ^ (k + 1 + 1) = A ^ (k + 1) * A := pow_succ A (k + 1)
        _ = A ^ k * A := by rw [ih]
        _ = A ^ (k + 1) := (pow_succ A k).symm
  intro k hk i j
  rw [key k hk]
  norm_num

/-- **The eigenvalue is well-defined**: for a fixed cyclicity `c`, the eigenvalue `λ` is unique —
any two pseudo-periodic descriptions `IsPseudoPeriodicPow A c K λ₁/λ₂` agree on `λ` as soon as some
diagonal entry `(Aᴷ)ᵢᵢ` is finite (a genuine circuit through `i` exists). At that entry both give
`(Aᴷ⁺ᶜ)ᵢᵢ = (Aᴷ)ᵢᵢ ⊗ trop(c·λ)`; cancelling the finite `(Aᴷ)ᵢᵢ` and the positive `c` pins `λ`. -/
theorem IsPseudoPeriodicPow.lam_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) MP} {c K : ℕ}
    {lam₁ lam₂ : ℤ} (h₁ : IsPseudoPeriodicPow A c K lam₁) (h₂ : IsPseudoPeriodicPow A c K lam₂)
    {i : Fin n} (hi : (A ^ K) i i ≠ 0) : lam₁ = lam₂ := by
  have e : (A ^ K) i i * Tropical.trop (((c : ℤ) * lam₁ : ℤ) : WithTop ℤ)
         = (A ^ K) i i * Tropical.trop (((c : ℤ) * lam₂ : ℤ) : WithTop ℤ) :=
    (h₁.2 K le_rfl i i).symm.trans (h₂.2 K le_rfl i i)
  have hu : ((A ^ K) i i).untrop ≠ ⊤ :=
    fun ht => hi (Tropical.untrop_injective (by rw [ht]; rfl))
  have e2 : (((c : ℤ) * lam₁ : ℤ) : WithTop ℤ) = (((c : ℤ) * lam₂ : ℤ) : WithTop ℤ) := by
    apply WithTop.add_left_cancel hu
    have huntrop := congrArg Tropical.untrop e
    simpa [Tropical.untrop_mul, Tropical.untrop_trop] using huntrop
  have e3 : (c : ℤ) * lam₁ = (c : ℤ) * lam₂ := by exact_mod_cast e2
  exact mul_left_cancel₀ (by exact_mod_cast h₁.1.ne') e3

/-- **Cyclicity is closed under positive multiples**: if `A` is pseudo-periodic with cyclicity `c`
(rank `K`, eigenvalue `λ`) then it is also pseudo-periodic with cyclicity `m·c` for any `m ≥ 1` — the
same eigenvalue, the increment scaling to `(m·c)·λ`. Proved by applying the `c`-step relation `m`
times (`Nat.le_induction`, tropical `trop a · trop b = trop (a+b)`). The cyclicity is *a* period, not
the minimal one; this records that any multiple works. -/
theorem IsPseudoPeriodicPow.mul_left {n : ℕ} {A : Matrix (Fin n) (Fin n) MP} {c K : ℕ}
    {lam : ℤ} (h : IsPseudoPeriodicPow A c K lam) :
    ∀ m, 0 < m → IsPseudoPeriodicPow A (m * c) K lam := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rw [Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; exact h
  | succ m hm ih =>
    refine ⟨Nat.mul_pos (Nat.succ_pos m) h.1, fun k hk i j => ?_⟩
    have hstep := h.2 (k + m * c) (le_trans hk (Nat.le_add_right k (m * c))) i j
    have hih := ih.2 k hk i j
    have hcast : (((m * c : ℕ) : ℤ) * lam : WithTop ℤ) + (((c : ℕ) : ℤ) * lam : WithTop ℤ)
               = ((((m + 1) * c : ℕ) : ℤ) * lam : WithTop ℤ) := by
      rw [← WithTop.coe_add]; congr 1; push_cast; ring
    calc (A ^ (k + (m + 1) * c)) i j
        = (A ^ (k + m * c + c)) i j := by rw [show k + (m + 1) * c = k + m * c + c by ring]
      _ = (A ^ (k + m * c)) i j * Tropical.trop (((c : ℤ) * lam : ℤ) : WithTop ℤ) := hstep
      _ = (A ^ k) i j * Tropical.trop ((((m * c : ℕ) : ℤ) * lam : ℤ) : WithTop ℤ)
            * Tropical.trop (((c : ℤ) * lam : ℤ) : WithTop ℤ) := by rw [hih]
      _ = (A ^ k) i j * (Tropical.trop ((((m * c : ℕ) : ℤ) * lam : ℤ) : WithTop ℤ)
            * Tropical.trop (((c : ℤ) * lam : ℤ) : WithTop ℤ)) := by rw [mul_assoc]
      _ = (A ^ k) i j * Tropical.trop (((((m * c : ℕ) : ℤ) * lam : ℤ) : WithTop ℤ)
            + (((c : ℤ) * lam : ℤ) : WithTop ℤ)) := by rw [← Tropical.trop_add]
      _ = (A ^ k) i j * Tropical.trop (((((m + 1) * c : ℕ) : ℤ) * lam : ℤ) : WithTop ℤ) := by
            rw [hcast]

/-- `exA` is multiplicatively idempotent (`exA ⊗ exA = exA`): its `0`-weight self-loops make it a
closure operator. -/
theorem exA_mul_self : exA * exA = exA := by native_decide

/-- Powers of the idempotent `exA` collapse: `exAᵏ⁺¹ = exA` for every `k`. -/
theorem exA_pow_succ (k : ℕ) : exA ^ (k + 1) = exA := by
  induction k with
  | zero => rw [pow_one]
  | succ k ih => rw [pow_succ, ih, exA_mul_self]

/-- **A concrete cyclicity instance**: the idempotent `exA` is pseudo-periodic with cyclicity `c = 1`,
rank `K = 1`, eigenvalue `λ = 0` — a corollary of `isPseudoPeriodicPow_of_pow_succ_eq` (its powers
stabilize: `exA² = exA¹`). The idempotent case is exactly the sub-additive-closure case already
computed closed-form in `DeepWiki.UppSeq`; this is its matrix face. -/
theorem isPseudoPeriodicPow_exA : IsPseudoPeriodicPow exA 1 1 0 :=
  isPseudoPeriodicPow_of_pow_succ_eq (by simp [exA_pow_succ])

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
