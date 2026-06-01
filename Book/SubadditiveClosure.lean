import VersoManual
import Book.FunctionClasses

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Sub-additive closure" =>
In a complete dioid the _sub-additive closure_, or _Kleene star_, of an
element collects all of its powers into a single sum. Working over an
arbitrary complete dioid `α`, with $`\oplus = {+}` the dioid sum
$`\bigsqcup`, $`\otimes = {*}` the product, neutrals $`\mathbf{1} = e`
and $`\mathbf{0} = \varepsilon`, and the canonical order $`\preceq`, this
chapter defines the star and its strict variant, establishes their
basic algebraic identities and monotonicity, and proves that the star
delivers the least solution of an affine fixed-point equation.

```lean
namespace NetworkCalculus

open scoped Computability
```

# The Kleene star
The _Kleene star_ $`a^{\star}` is the sum of all non-negative powers of
$`a`, where $`a^0 = e = \mathbf{1}` and $`a^{i+1} = a \otimes a^i`:

$$`a^{\star} = \bigoplus_{i \ge 0} a^i.`

The _strict closure_ $`a^+` is the same sum restricted to the strictly
positive powers:

$$`a^+ = \bigoplus_{i \ge 1} a^i.`

In Lean the powers are the monoid `npow` of the semiring, and the sum
is the indexed least upper bound `⨆`.

```lean
/-- The Kleene star `a★ = ⊕_{i ≥ 0} aⁱ`. -/
noncomputable def kstar {α : Type*} [CompleteDioid α]
    (a : α) : α :=
  ⨆ i : ℕ, a ^ i

/-- The strict closure `a⁺ = ⊕_{i ≥ 1} aⁱ`. -/
noncomputable def kplus {α : Type*} [CompleteDioid α]
    (a : α) : α :=
  ⨆ i : ℕ, a ^ (i + 1)
```

Splitting the star sum into its $`i = 0` term $`a^0 = e` and the
remaining terms gives $`a^{\star} = e \oplus a^+`. The $`\le` direction
cases on whether the index is $`0` or a successor; the $`\ge`
direction uses $`e \preceq a^{\star}` (the $`i = 0` term) and
$`a^+ \preceq a^{\star}` (a sub-sum), recalling $`\oplus = \sqcup`.

```lean
theorem kstar_eq_one_add_kplus
    {α : Type*} [CompleteDioid α] (a : α) :
    kstar a = 1 + kplus a := by
  rw [add_eq_sup]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i with
    | zero => simp
    | succ n =>
        refine le_trans ?_ le_sup_right
        exact le_iSup (fun j => a ^ (j + 1)) n
  · refine sup_le ?_ ?_
    · exact le_iSup_of_le 0 (by simp)
    · exact iSup_le fun i =>
        le_iSup (fun j => a ^ j) (i + 1)
```

*Proof.* By antisymmetry, splitting the $`i=0` term: $`\bigsqcup_i a^i = a^0 \sqcup \bigsqcup_{n} a^{n+1} = e \sqcup a^+`. $`\quad\blacksquare`

Factoring $`a` out of the strict closure gives
$`a^+ = a \otimes a^{\star}`: since $`\otimes` distributes over the
arbitrary sum (lower semi-continuity),
$`a \otimes \bigoplus_i a^i = \bigoplus_i a \otimes a^i = \bigoplus_i a^{i+1}`.

```lean
theorem kplus_eq_mul_kstar
    {α : Type*} [CompleteDioid α] (a : α) :
    kplus a = a * kstar a := by
  rw [kstar, CompleteDioid.mul_iSup]
  refine iSup_congr fun i => ?_
  rw [← pow_succ']
```

*Proof.* By lower semi-continuity and $`a \otimes a^i = a^{i+1}`: $`a \otimes \bigoplus_i a^i = \bigoplus_i a^{i+1} = a^+`. $`\quad\blacksquare`

# Properties
The star is _monotone_ for the canonical order. The key step is that
each power is monotone, $`a \preceq b \Rightarrow a^i \preceq b^i`,
proved by induction on $`i`; the star is then a monotone sum.

```lean
theorem pow_le_pow' {α : Type*} [CompleteDioid α]
    {a b : α} (h : a ≤ b) :
    ∀ i, a ^ i ≤ b ^ i
  | 0 => by simp
  | (i+1) => by
      rw [pow_succ, pow_succ]
      exact le_trans
        (Dioid.mul_le_mul_right' (pow_le_pow' h i) a)
        (Dioid.mul_le_mul_left' h _)
```

*Proof.* Induction on $`i`: $`a^0 = e = b^0`; and $`a^{n+1} = a^n \otimes a \preceq b^n \otimes a \preceq b^n \otimes b = b^{n+1}` (isotony, induction hypothesis, $`a \preceq b`). $`\quad\blacksquare`

```lean
theorem kstar_mono {α : Type*} [CompleteDioid α]
    {a b : α} (h : a ≤ b) :
    kstar a ≤ kstar b :=
  iSup_mono fun i => pow_le_pow' h i
```

*Proof.* Termwise from `pow_le_pow'`: $`\bigoplus_i a^i \preceq \bigoplus_i b^i`. $`\quad\blacksquare`

Two sub-sum bounds: $`a \preceq a^+` (the $`i = 1` term) and
$`a^+ \preceq a^{\star}` (more terms), so $`a \preceq a^+ \preceq
a^{\star}`. Likewise $`e \preceq a^{\star}` and each power is below
the star.

```lean
theorem le_kplus {α : Type*} [CompleteDioid α]
    (a : α) : a ≤ kplus a :=
  le_iSup_of_le 0 (by simp)
```

*Proof.* $`a = a^{0+1}` is the $`i=0` term of $`a^+`, so $`a \preceq a^+`. $`\quad\blacksquare`

```lean
theorem kplus_le_kstar {α : Type*} [CompleteDioid α]
    (a : α) :
    kplus a ≤ kstar a :=
  iSup_le fun i => le_iSup (fun j => a ^ j) (i + 1)
```

*Proof.* Each $`a^{i+1}` is a term of $`a^{\star} = \bigoplus_j a^j`, so $`a^+ \preceq a^{\star}`. $`\quad\blacksquare`

```lean
theorem one_le_kstar {α : Type*} [CompleteDioid α]
    (a : α) : 1 ≤ kstar a :=
  le_iSup_of_le 0 (by simp)
```

*Proof.* $`e = a^0` is the $`i=0` term of $`a^{\star}`, so $`e \preceq a^{\star}`. $`\quad\blacksquare`

```lean
theorem le_kstar {α : Type*} [CompleteDioid α]
    (a : α) : a ≤ kstar a :=
  (le_kplus a).trans (kplus_le_kstar a)
```

*Proof.* $`a \preceq a^+ \preceq a^{\star}` (`le_kplus`, `kplus_le_kstar`). $`\quad\blacksquare`

```lean
theorem pow_le_kstar {α : Type*} [CompleteDioid α]
    (a : α) (i : ℕ) :
    a ^ i ≤ kstar a :=
  le_iSup (fun j => a ^ j) i
```

*Proof.* $`a^i` is the $`i`-th term of $`a^{\star} = \bigoplus_j a^j`. $`\quad\blacksquare`

The star is _multiplicatively idempotent_,
$`a^{\star} \otimes a^{\star} = a^{\star}`: distributing the product
over both sums collapses $`a^i \otimes a^j = a^{i+j}`, which is again a
power below $`a^{\star}`; conversely $`e \preceq a^{\star}` gives the
reverse bound.

```lean
theorem kstar_mul_kstar
    {α : Type*} [CompleteDioid α] (a : α) :
    kstar a * kstar a = kstar a := by
  rw [kstar, CompleteDioid.iSup_mul]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [CompleteDioid.mul_iSup]
    refine iSup_le fun j => ?_
    rw [← pow_add]
    exact pow_le_kstar a (i + j)
  · refine iSup_le fun i => ?_
    refine le_iSup_of_le i ?_
    calc a ^ i = a ^ i * 1 := (mul_one _).symm
      _ ≤ a ^ i * kstar a :=
          Dioid.mul_le_mul_left' (one_le_kstar a) _
```

*Proof.* Distribute over both sums. $`\preceq`: $`a^i \otimes a^j = a^{i+j} \preceq a^{\star}` (`pow_le_kstar`). $`\succeq`: $`a^i = a^i \otimes e \preceq a^i \otimes a^{\star}` (`one_le_kstar`). $`\quad\blacksquare`

The star is a _closure operator_: applying it twice changes nothing,
$`(a^{\star})^{\star} = a^{\star}`. The $`\ge` direction is
$`a^{\star} \preceq (a^{\star})^{\star}`; the $`\le` direction bounds
each power $`(a^{\star})^i \preceq a^{\star}` by induction, using
multiplicative idempotence.

```lean
theorem kstar_idem {α : Type*} [CompleteDioid α]
    (a : α) :
    kstar (kstar a) = kstar a := by
  apply le_antisymm
  · rw [kstar]
    refine iSup_le fun i => ?_
    induction i with
    | zero => simpa using one_le_kstar a
    | succ n ih =>
        rw [pow_succ]
        calc kstar a ^ n * kstar a
            ≤ kstar a * kstar a :=
              Dioid.mul_le_mul_right' ih _
          _ = kstar a := kstar_mul_kstar a
  · exact le_kstar (kstar a)
```

*Proof.* By antisymmetry. $`\succeq`: $`a^{\star} \preceq (a^{\star})^{\star}` (`le_kstar`). $`\preceq`: by induction $`(a^{\star})^{i} \preceq a^{\star}`, using $`(a^{\star})^{n+1} = (a^{\star})^n \otimes a^{\star} \preceq a^{\star} \otimes a^{\star} = a^{\star}` (`kstar_mul_kstar`). $`\quad\blacksquare`

Adjoining the unit to $`a` leaves the star unchanged,
$`(a \oplus e)^{\star} = a^{\star}`. One direction is monotonicity,
since $`a \preceq a \oplus e`; the other bounds each power
$`(a \oplus e)^i \preceq a^{\star}` by induction, using
$`a^{\star} \otimes a \preceq a^{\star}` (which is
$`a^+ \preceq a^{\star}` after commuting) and
$`a^{\star} \otimes e = a^{\star}`.

```lean
theorem add_one_kstar {α : Type*} [CompleteDioid α]
    (a : α) :
    kstar (a + 1) = kstar a := by
  apply le_antisymm
  · rw [kstar]
    refine iSup_le fun i => ?_
    induction i with
    | zero => simpa using one_le_kstar a
    | succ n ih =>
        rw [pow_succ]
        calc (a + 1) ^ n * (a + 1)
            ≤ kstar a * (a + 1) :=
              Dioid.mul_le_mul_right' ih _
          _ = kstar a * a + kstar a * 1 :=
              mul_add _ _ _
          _ ≤ kstar a := by
              rw [mul_one, add_eq_sup]
              refine sup_le ?_ le_rfl
              rw [mul_comm, ← kplus_eq_mul_kstar]
              exact kplus_le_kstar a
  · refine kstar_mono ?_
    rw [add_eq_sup]; exact le_sup_left
```

*Proof.* By antisymmetry. $`\succeq`: $`a \preceq a \oplus e` gives $`a^{\star} \preceq (a \oplus e)^{\star}` (`kstar_mono`). $`\preceq`: by induction $`(a\oplus e)^{i} \preceq a^{\star}`, using $`(a\oplus e)^{n+1} \preceq a^{\star}\otimes(a\oplus e) = a^{\star}\otimes a \oplus a^{\star} \preceq a^{\star}` (since $`a^{\star}\otimes a = a^+ \preceq a^{\star}`). $`\quad\blacksquare`

# The Kleene star theorem
The central result is that $`a^{\star} \otimes b` is the _least_
solution of the affine fixed-point equation

$$`x = a \otimes x \oplus b.`

Two small order helpers make each summand a lower bound of a sum,
$`d \preceq c \oplus d` and $`c \preceq c \oplus d` (recall
$`\oplus = \sqcup`):

```lean
theorem self_le_add {α : Type*} [CompleteDioid α]
    (c d : α) : d ≤ c + d := by
  rw [add_eq_sup]; exact le_sup_right

theorem le_add_self' {α : Type*} [CompleteDioid α]
    (c d : α) : c ≤ c + d := by
  rw [add_eq_sup]; exact le_sup_left
```

First, $`a^{\star} \otimes b` _is_ a solution. Computing the
right-hand side:
$`a \otimes (a^{\star} \otimes b) = (a \otimes a^{\star}) \otimes b = a^+ \otimes b`,
and then
$`a^+ \otimes b \oplus b = (e \oplus a^+) \otimes b = a^{\star} \otimes b`
by distributivity and $`a^{\star} = e \oplus a^+`.

```lean
theorem kstar_mul_is_solution
    {α : Type*} [CompleteDioid α] (a b : α) :
    a * (kstar a * b) + b = kstar a * b := by
  rw [← mul_assoc, ← kplus_eq_mul_kstar,
    kstar_eq_one_add_kplus, add_mul, one_mul,
    add_comm (kplus a * b) b]
```

*Proof.* $`a \otimes (a^{\star}\otimes b) \oplus b = a^+\otimes b \oplus b = (e \oplus a^+)\otimes b = a^{\star}\otimes b` (`kplus_eq_mul_kstar`, `kstar_eq_one_add_kplus`, distributivity). $`\quad\blacksquare`

Second, it is the _least_ solution: any $`x` with
$`x = a \otimes x \oplus b` dominates $`a^{\star} \otimes b`. From the
equation, $`b \preceq x` and $`a \otimes x \preceq x`, so by induction
$`a^k \otimes b \preceq x` for every $`k` (apply $`a \otimes -` and
descend through $`a \otimes x \preceq x`). Distributing the product
over the star sum,
$`a^{\star} \otimes b = \bigl(\bigoplus_k a^k\bigr) \otimes b = \bigoplus_k a^k \otimes b \preceq x`.

```lean
theorem kstar_mul_le_of_solution
    {α : Type*} [CompleteDioid α] {a b x : α}
    (h : a * x + b = x) : kstar a * b ≤ x := by
  have hb : b ≤ x :=
    (self_le_add (a * x) b).trans_eq h
  have hax : a * x ≤ x :=
    (le_add_self' (a * x) b).trans_eq h
  have key : ∀ k, a ^ k * b ≤ x := by
    intro k
    induction k with
    | zero => simpa using hb
    | succ n ih =>
        rw [pow_succ', mul_assoc]
        calc a * (a ^ n * b)
            ≤ a * x := Dioid.mul_le_mul_left' ih a
          _ ≤ x := hax
  rw [kstar, CompleteDioid.iSup_mul]
  exact iSup_le key

end NetworkCalculus
```

*Proof.* From $`a \otimes x \oplus b = x`: $`b \preceq x` and $`a \otimes x \preceq x`. Induction gives $`a^k \otimes b \preceq x` (since $`a^{n+1}\otimes b = a\otimes(a^n\otimes b) \preceq a\otimes x \preceq x`). Then $`a^{\star}\otimes b = \bigoplus_k a^k\otimes b \preceq x`. $`\quad\blacksquare`

Together these say $`a^{\star} \otimes b` solves $`x = a \otimes x
\oplus b` and lies below every solution: it is the least fixed point.
