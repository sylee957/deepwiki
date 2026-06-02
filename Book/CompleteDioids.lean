import VersoManual
import Book.Order
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Complete dioids" =>
A _complete dioid_ adds suprema of arbitrary indexed families to the
dioid order, with the product lower semi-continuous. This chapter
defines it, bridges its supremum to `Mathlib`'s, derives lower
semi-continuity as an equality, and develops the top element and the
agreement of the algebraic and lattice orders.

```lean
namespace NetworkCalculus

namespace Algebra

open scoped Bridge
```

# A complete dioid from scratch

A dioid is _complete_ when every _indexed family_ has a least upper
bound for the canonical order $`\preceq`, and the product is _lower
semi-continuous_: it commutes with these suprema. We take the supremum
$`\bigsqcup_i f(i)` over a family $`f : \iota \to T` as the field
`iSup`, with the two least-upper-bound laws and lower semi-continuity.

*Definition:* a _complete dioid_ adds $`\bigsqcup : (\iota \to T) \to T` with
$$`f(i) \preceq \textstyle\bigsqcup_j f(j), \qquad (\forall i,\ f(i) \preceq b) \Rightarrow \textstyle\bigsqcup_i f(i) \preceq b,`
$$`a \otimes \textstyle\bigsqcup_i f(i) \preceq \textstyle\bigsqcup_i a \otimes f(i).`

Lower semi-continuity is stated as a single inequality `mul_iSup_le`:
the product is _below_ the supremum of the products. The reverse
inequality is free — each $`a \otimes f(i)` is below $`a \otimes
\bigsqcup f` by isotony, so their supremum is too — so the full
equality is a theorem, not an axiom.

```lean
class CompleteDioid (T : Type u) extends Dioid T where
  iSup : {ι : Type u} → (ι → T) → T
  le_iSup : ∀ {ι : Type u} (f : ι → T) (i : ι),
    f i ≼ₒ iSup f
  iSup_le : ∀ {ι : Type u} (f : ι → T) (b : T),
    (∀ i, f i ≼ₒ b) → iSup f ≼ₒ b
  mul_iSup_le : ∀ {ι : Type u} (a : T) (f : ι → T),
    a ⊗ₒ iSup f ≼ₒ iSup (fun i => a ⊗ₒ f i)
```

The supremum is taken over an _indexed family_ $`\bigsqcup_i f(i)`.
The supremum of a _set_ is the special case indexing by the set's own
elements; it is `Mathlib`'s `sSup`, and we derive it together with its
two least-upper-bound laws, matching the `sSup` API the order and
convolution proofs use.

*Definition:* $`\bigsqcup s = \bigsqcup_{x \in s} x`

```lean
namespace CompleteDioid

def sSup {T : Type*} [CompleteDioid T] (s : Set T) : T :=
  CompleteDioid.iSup (fun x : s => x.val)
```

*Theorem:* $`a \in s \Rightarrow a \preceq \bigsqcup s`

```lean
theorem le_sSup {T : Type*} [CompleteDioid T]
    (s : Set T) (a : T) (h : a ∈ s) : a ≼ₒ sSup s :=
  CompleteDioid.le_iSup (fun x : s => x.val) ⟨a, h⟩
```

*Theorem:* $`(\forall a \in s,\ a \preceq b) \Rightarrow \bigsqcup s \preceq b`

```lean
theorem sSup_le {T : Type*} [CompleteDioid T]
    (s : Set T) (b : T) (h : ∀ a ∈ s, a ≼ₒ b) :
    sSup s ≼ₒ b :=
  CompleteDioid.iSup_le _ b (fun x => h x.val x.2)
```

*Theorem:* $`a \otimes \bigsqcup s \preceq \bigsqcup\,\{\,a \otimes b \mid b \in s\,\}`

```lean
theorem mul_sSup_le {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    a ⊗ₒ sSup s ≼ₒ sSup ((fun b => a ⊗ₒ b) '' s) := by
  refine le_trans
    (CompleteDioid.mul_iSup_le a (fun x : s => x.val)) ?_
  apply CompleteDioid.iSup_le
  intro x
  exact CompleteDioid.le_sSup _ _ ⟨x.val, x.2, rfl⟩

end CompleteDioid
```

The supremum and its two least-upper-bound laws are exactly a
`Mathlib` `CompleteSemilatticeSup`: the `sSup` is `Mathlib`'s `⨆`, and
`le_sSup`/`sSup_le` package into `IsLUB`. A `scoped` bridge records
this, reusing the partial order from the dioid, so `Mathlib`'s
supremum API applies once `open scoped …Bridge`.

```lean
namespace Bridge

scoped instance instSupSet
    {T : Type*} [CompleteDioid T] : SupSet T where
  sSup := CompleteDioid.sSup

scoped instance instCompleteSemilatticeSup
    {T : Type*} [CompleteDioid T] :
    CompleteSemilatticeSup T where
  toPartialOrder := instPartialOrder
  toSupSet := instSupSet
  isLUB_sSup s :=
    ⟨fun a ha => CompleteDioid.le_sSup s a ha,
     fun b hb => CompleteDioid.sSup_le s b hb⟩

end Bridge
```

With the bridge open, $`\bigsqcup s` is `Mathlib`'s least upper bound
of $`s`.

*Theorem:* $`\bigsqcup s` is the least upper bound of $`s`

```lean
example {T : Type*} [CompleteDioid T] (s : Set T) :
    IsLUB s (CompleteDioid.sSup s) := isLUB_sSup s
```

The full lower-semi-continuity _equality_ now follows: the axiom gives
one inequality, and the other is free from the least-upper-bound laws
and isotony of the product.

*Theorem:* $`a \otimes \bigsqcup_{b \in s} b = \bigsqcup_{b \in s} a \otimes b`

```lean
theorem CompleteDioid.mul_sSup {T : Type*}
    [CompleteDioid T] (a : T) (s : Set T) :
    a ⊗ₒ CompleteDioid.sSup s
      = CompleteDioid.sSup ((fun b => a ⊗ₒ b) '' s) := by
  apply le_antisymm
  · exact CompleteDioid.mul_sSup_le a s
  · refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨b, hb, rfl⟩
    exact mul_le_mul_left (CompleteDioid.le_sSup s b hb) a
```

Lower semi-continuity holds on the right as well, by commutativity of
the product.

*Theorem:* $`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = \bigsqcup_{b \in s} b \otimes a`

```lean
theorem sSup_mul {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    (CompleteDioid.sSup s) ⊗ₒ a
      = CompleteDioid.sSup ((fun b => b ⊗ₒ a) '' s) := by
  rw [mul_comm, CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, mul_comm y a⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, mul_comm a y⟩
```

The binary join is the supremum of a two-element set, and the product
distributes over it — the finite shadow of lower semi-continuity.

*Definition:* $`a \sqcup b := \bigsqcup \{a, b\}`

```lean
def sup {T : Type*} [CompleteDioid T] (a b : T) : T :=
  CompleteDioid.sSup {a, b}
```

*Theorem:* $`a \otimes (b \sqcup c) = (a \otimes b) \sqcup (a \otimes c)`

```lean
theorem mul_sup {T : Type*} [CompleteDioid T]
    (a b c : T) :
    a ⊗ₒ sup b c = sup (a ⊗ₒ b) (a ⊗ₒ c) := by
  unfold sup
  rw [CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨b, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr rfl, rfl⟩
```

# The top element

A complete dioid has a _greatest element_ $`\top`, the sum of all the
elements of the carrier:
$$`\top = \bigsqcup_{x} x.`
We take it as the supremum of the universal set, written `⊤ₒ[T]`.

*Definition:* $`\top = \bigsqcup_{x \in T} x`

```lean
def top (T : Type*) [CompleteDioid T] : T :=
  CompleteDioid.sSup Set.univ

scoped notation:max "⊤ₒ[" T "]" => top T
```

Being the supremum of everything, $`\top` lies above every element.

*Theorem:* $`a \preceq \top`

```lean
theorem le_top {T : Type*} [CompleteDioid T] (a : T) :
    a ≼ₒ ⊤ₒ[T] :=
  CompleteDioid.le_sSup Set.univ a (Set.mem_univ a)
```

Hence $`\top` is _absorbing for the sum_: adding anything to it changes
nothing.

*Theorem:* $`\top \oplus a = \top`

```lean
theorem top_oplus {T : Type*} [CompleteDioid T] (a : T) :
    ⊤ₒ[T] ⊕ₒ a = ⊤ₒ[T] := by
  have h : a ⊕ₒ ⊤ₒ[T] = ⊤ₒ[T] := le_top a
  rw [add_comm, h]
```

Since the zero $`\varepsilon` is absorbing for the product, multiplying
$`\top` by $`\varepsilon` on either side collapses to $`\varepsilon`.

*Theorem:* $`\varepsilon \otimes \top = \top \otimes \varepsilon = \varepsilon`

```lean
theorem eps_otimes_top {T : Type*} [CompleteDioid T] :
    εₒ ⊗ₒ ⊤ₒ[T] = εₒ :=
  zero_mul (top T)

theorem top_otimes_eps {T : Type*} [CompleteDioid T] :
    ⊤ₒ[T] ⊗ₒ εₒ = εₒ :=
  mul_zero (top T)
```

# The two orders agree

A complete dioid now carries _two_ ways to compare elements. The
_algebraic_ order $`\preceq` comes from the sum, $`a \preceq b \iff a
\oplus b = b`. The _lattice_ order comes from the supremum: $`a` is
below $`b` when the least upper bound of $`\{a, b\}` is $`b`. These must
coincide for the structure to be consistent, and they do — a direct
consequence of the least-upper-bound laws.

First, the supremum of a pair _is_ the binary sum: adjoining the two
upper-bound facts to idempotency pins $`\bigsqcup\{a, b\} = a \oplus b`.

*Theorem:* $`\bigsqcup \{a, b\} = a \oplus b`

```lean
theorem sSup_pair {T : Type*} [CompleteDioid T]
    (a b : T) : CompleteDioid.sSup {a, b} = a ⊕ₒ b := by
  apply le_antisymm
  · refine CompleteDioid.sSup_le _ _ ?_
    intro x hx
    rcases hx with hx | hx
    · show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, ← add_assoc, Dioid.oplus_idem]
    · rw [Set.mem_singleton_iff] at hx
      show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, add_comm a b,
        ← add_assoc, Dioid.oplus_idem]
  · have ha := CompleteDioid.le_sSup ({a, b} : Set T) a
      (by simp)
    have hb := CompleteDioid.le_sSup ({a, b} : Set T) b
      (by simp)
    show (a ⊕ₒ b) ⊕ₒ CompleteDioid.sSup {a, b}
      = CompleteDioid.sSup {a, b}
    rw [add_assoc, hb, ha]
```

Hence the lattice order — $`\bigsqcup\{a, b\} = b` — is exactly the
algebraic order $`a \preceq b`.

*Theorem:* $`a \preceq b \iff \bigsqcup \{a, b\} = b`

```lean
theorem le_iff_sSup_pair {T : Type*} [CompleteDioid T]
    {a b : T} :
    a ≼ₒ b ↔ CompleteDioid.sSup {a, b} = b := by
  rw [sSup_pair]; rfl
```

```lean
end Algebra
```

```lean
end NetworkCalculus
```
