import VersoManual
import Book.Signatures
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Dioids and complete dioids" =>
Building on the operation signatures and the additive monoid of the
previous chapter, this chapter completes the algebra of _dioids_: the
remaining layers of the type-class tower, the _canonical order_ they
induce, the order properties and isotony, the _complete dioid_ that
adds completeness and lower semi-continuity, and its top element. The
concrete number-system models that realize the tower are built in the
next chapter.

All declarations continue in the `NetworkCalculus` namespace, extending
the tower started in the previous chapter.

```lean
namespace NetworkCalculus

namespace Algebra

open scoped Bridge
```

# Completing the tower

On top of the signatures, monoids, and semi-rings of the previous
chapter, the idempotency that distinguishes a dioid is added as a
single field on top of a commutative semi-ring, so no inheritance
diamond arises.

*Theorem:* $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`

```lean
theorem quaternary_distrib {T : Type*} [Semiring T]
    (a b c d : T) :
    (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = a ⊗ₒ c ⊕ₒ b ⊗ₒ c ⊕ₒ a ⊗ₒ d ⊕ₒ b ⊗ₒ d := by
  have hexp : (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = (a ⊗ₒ c ⊕ₒ a ⊗ₒ d) ⊕ₒ (b ⊗ₒ c ⊕ₒ b ⊗ₒ d) := by
    rw [Semiring.right_distrib, Semiring.left_distrib,
      Semiring.left_distrib]
  rw [hexp,
    AddMonoid.oplus_assoc (a ⊗ₒ c) (b ⊗ₒ c) (a ⊗ₒ d),
    AddMonoid.oplus_assoc (a ⊗ₒ c)
      (b ⊗ₒ c ⊕ₒ a ⊗ₒ d) (b ⊗ₒ d),
    AddMonoid.oplus_assoc (a ⊗ₒ c) (a ⊗ₒ d)
      (b ⊗ₒ c ⊕ₒ b ⊗ₒ d)]
  congr 1
  rw [AddCommMonoid.oplus_comm (b ⊗ₒ c) (a ⊗ₒ d),
    AddMonoid.oplus_assoc (a ⊗ₒ d) (b ⊗ₒ c) (b ⊗ₒ d)]
```

## A complete dioid from scratch

A dioid is _complete_ when every subset of the carrier has a least
upper bound for the canonical order $`\preceq`, and the product is
_lower semi-continuous_: it commutes with these suprema. We add the
supremum $`\bigsqcup` as a field `sSup`, the two laws making it a least
upper bound, and lower semi-continuity
$$`a \otimes \bigsqcup_{b \in s} b = \bigsqcup_{b \in s} a \otimes b.`

*Definition:* a _complete dioid_ adds $`\bigsqcup : \mathcal{P}(T) \to T` with
$$`a \in s \Rightarrow a \preceq \textstyle\bigsqcup s, \qquad (\forall a \in s,\ a \preceq b) \Rightarrow \textstyle\bigsqcup s \preceq b,`
$$`a \otimes \textstyle\bigsqcup s = \textstyle\bigsqcup\,\{\,a \otimes b \mid b \in s\,\}.`

```lean
class CompleteDioid (T : Type*) extends Dioid T where
  sSup : Set T → T
  le_sSup : ∀ (s : Set T) (a : T), a ∈ s →
    a ≼ₒ sSup s
  sSup_le : ∀ (s : Set T) (b : T),
    (∀ a ∈ s, a ≼ₒ b) → sSup s ≼ₒ b
  mul_sSup : ∀ (a : T) (s : Set T),
    a ⊗ₒ sSup s = sSup ((fun b => a ⊗ₒ b) '' s)
```

Lower semi-continuity holds on the right as well, by commutativity of
the product.

*Theorem:* $`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = \bigsqcup_{b \in s} b \otimes a`

```lean
theorem sSup_mul {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    (CompleteDioid.sSup s) ⊗ₒ a
      = CompleteDioid.sSup ((fun b => b ⊗ₒ a) '' s) := by
  rw [CommSemiring.otimes_comm, CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, CommSemiring.otimes_comm y a⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, CommSemiring.otimes_comm a y⟩
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

## The top element

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
  rw [AddCommMonoid.oplus_comm, h]
```

Since the zero $`\varepsilon` is absorbing for the product, multiplying
$`\top` by $`\varepsilon` on either side collapses to $`\varepsilon`.

*Theorem:* $`\varepsilon \otimes \top = \top \otimes \varepsilon = \varepsilon`

```lean
theorem eps_otimes_top {T : Type*} [CompleteDioid T] :
    εₒ ⊗ₒ ⊤ₒ[T] = εₒ :=
  Semiring.eps_otimes (top T)

theorem top_otimes_eps {T : Type*} [CompleteDioid T] :
    ⊤ₒ[T] ⊗ₒ εₒ = εₒ :=
  Semiring.otimes_eps (top T)
```

## The two orders agree

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
  apply _root_.le_antisymm
  · refine CompleteDioid.sSup_le _ _ ?_
    intro x hx
    rcases hx with hx | hx
    · show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, ← AddMonoid.oplus_assoc, Dioid.oplus_idem]
    · rw [Set.mem_singleton_iff] at hx
      show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, AddCommMonoid.oplus_comm a b,
        ← AddMonoid.oplus_assoc, Dioid.oplus_idem]
  · have ha := CompleteDioid.le_sSup ({a, b} : Set T) a
      (by simp)
    have hb := CompleteDioid.le_sSup ({a, b} : Set T) b
      (by simp)
    show (a ⊕ₒ b) ⊕ₒ CompleteDioid.sSup {a, b}
      = CompleteDioid.sSup {a, b}
    rw [AddMonoid.oplus_assoc, hb, ha]
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
