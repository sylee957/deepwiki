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
namespace VerifiedWiki

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
$$`a \otimes \textstyle\bigsqcup_i f(i) = \textstyle\bigsqcup_i a \otimes f(i).`

Lower semi-continuity is the equality `mul_iSup`: the product commutes
with the supremum of a family.

```lean
class CompleteDioid (T : Type u) extends Dioid T where
  iSup : {ι : Type u} → (ι → T) → T
  le_iSup : ∀ {ι : Type u} (f : ι → T) (i : ι),
    f i ≼ₒ iSup f
  iSup_le : ∀ {ι : Type u} (f : ι → T) (b : T),
    (∀ i, f i ≼ₒ b) → iSup f ≼ₒ b
  mul_iSup : ∀ {ι : Type u} (a : T) (f : ι → T),
    a ⊗ₒ iSup f = iSup (fun i => a ⊗ₒ f i)
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
  rw [show a ⊗ₒ sSup s
      = CompleteDioid.iSup (fun x : s => a ⊗ₒ x.val) from
    CompleteDioid.mul_iSup a _]
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

Lower semi-continuity in _set_ form follows, transferring the
indexed-family equality to a supremum over a set.

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

# Residuation

In a field every nonzero element has an inverse, so division is the
inverse of multiplication. A dioid has no inverses — but a complete
dioid has suprema, and that is enough to define the _greatest solution_
of an inequality. The right-multiplication map $`R_a : x \mapsto x
\otimes a` is lower semi-continuous (`sSup_mul`), so it is _residuated_:
its _residual_ $`R_a^{\sharp}` sends $`b` to the greatest $`x` with
$`x \otimes a \preceq b`. We write that greatest solution $`b \oslash
a`, the _residuation_ (or _right-quotient_) of $`b` by $`a`.

*Definition:* $`b \oslash a = \bigsqcup\,\{\, x \mid x \otimes a \preceq b \,\}`

```lean
def resid {T : Type*} [CompleteDioid T] (b a : T) : T :=
  CompleteDioid.sSup { x | x ⊗ₒ a ≼ₒ b }

scoped notation:70 b:70 " ⊘ₒ " a:71 => resid b a
```

The residuation is itself a solution: $`(b \oslash a) \otimes a \preceq
b`. Pushing $`\otimes a` through the supremum (right lower
semi-continuity), each term $`x \otimes a` with $`x` in the set is
$`\preceq b` by construction, so their supremum is too.

*Theorem:* $`(b \oslash a) \otimes a \preceq b`

```lean
theorem resid_mul_le {T : Type*} [CompleteDioid T]
    (b a : T) : (b ⊘ₒ a) ⊗ₒ a ≼ₒ b := by
  rw [resid, sSup_mul]
  refine CompleteDioid.sSup_le _ _ ?_
  rintro y ⟨x, hx, rfl⟩
  exact hx
```

It is moreover the _greatest_ solution: the central equivalence is the
Galois connection $`x \otimes a \preceq b \iff x \preceq b \oslash a`.
Left to right is membership in the defining set; right to left raises
$`x \otimes a` to $`(b \oslash a) \otimes a` by isotony, then applies
`resid_mul_le`.

*Theorem:* $`x \otimes a \preceq b \iff x \preceq b \oslash a`

```lean
theorem mul_le_iff_le_resid {T : Type*}
    [CompleteDioid T] (x a b : T) :
    x ⊗ₒ a ≼ₒ b ↔ x ≼ₒ b ⊘ₒ a := by
  constructor
  · intro h
    exact CompleteDioid.le_sSup _ x h
  · intro h
    exact le_trans (mul_le_mul_right h a)
      (resid_mul_le b a)
```

The other round-trip is the residual after the map: $`x \preceq (x
\otimes a) \oslash a`. It is the right-to-left direction applied to
$`x \otimes a \preceq x \otimes a`.

*Theorem:* $`x \preceq (x \otimes a) \oslash a`

```lean
theorem le_resid_mul {T : Type*} [CompleteDioid T]
    (x a : T) : x ≼ₒ (x ⊗ₒ a) ⊘ₒ a :=
  (mul_le_iff_le_resid x a (x ⊗ₒ a)).mp (le_refl _)
```

Residuation is _isotone_ in the dividend: a larger $`b` admits more
solutions, so a larger quotient.

*Theorem:* $`b \preceq b' \implies b \oslash a \preceq b' \oslash a`

```lean
theorem resid_mono {T : Type*} [CompleteDioid T]
    {b b' : T} (a : T) (h : b ≼ₒ b') :
    b ⊘ₒ a ≼ₒ b' ⊘ₒ a := by
  rw [← mul_le_iff_le_resid]
  exact le_trans (resid_mul_le b a) h
```

Residuation is _antitone_ in the divisor: a larger $`a` makes $`x
\otimes a` larger, so fewer $`x` solve the inequality, so a smaller
quotient.

*Theorem:* $`a \preceq a' \implies b \oslash a' \preceq b \oslash a`

```lean
theorem resid_antitone {T : Type*} [CompleteDioid T]
    (b : T) {a a' : T} (h : a ≼ₒ a') :
    b ⊘ₒ a' ≼ₒ b ⊘ₒ a := by
  rw [← mul_le_iff_le_resid]
  exact le_trans (mul_le_mul_left h (b ⊘ₒ a'))
    (resid_mul_le b a')
```

# Sub-complete-dioids

A subset of a complete dioid that is closed under the operations is
itself a complete dioid. Concretely, given a predicate $`P` on the
carrier closed under the sum $`\oplus`, the product $`\otimes`, the two
neutrals $`\varepsilon` and $`e`, and arbitrary suprema, the subtype
$`\{x \mid P(x)\}` inherits the whole structure: every law transports
from the ambient dioid through the first projection, since the
operations act on the underlying values. We package the five closure
conditions and build the instance.

As with `Mathlib`'s `Subsemiring`, we bundle the substructure as a
_set_ together with its closure proofs: a `SubCompleteDioid` is a subset
of the carrier closed under the sum, the product, the two neutrals, and
arbitrary suprema.

*Definition:* a sub-complete-dioid: a subset closed under the operations

```lean
structure SubCompleteDioid (T : Type u)
    [CompleteDioid T] where
  carrier : Set T
  add_mem' : ∀ {a b}, a ∈ carrier → b ∈ carrier →
    a ⊕ₒ b ∈ carrier
  mul_mem' : ∀ {a b}, a ∈ carrier → b ∈ carrier →
    a ⊗ₒ b ∈ carrier
  eps_mem' : εₒ ∈ carrier
  one_mem' : eₒ ∈ carrier
  iSup_mem' : ∀ {ι : Type u} (f : ι → T),
    (∀ i, f i ∈ carrier) →
    CompleteDioid.iSup f ∈ carrier
```

An element of `T` is a _member_ of a substructure when it lies in the
carrier, and the substructure coerces to a _type_ — its members paired
with their membership proof.

```lean
namespace SubCompleteDioid
variable {T : Type u} [CompleteDioid T]

instance : Membership T (SubCompleteDioid T) :=
  ⟨fun S a => a ∈ S.carrier⟩

instance : CoeSort (SubCompleteDioid T) (Type u) :=
  ⟨fun S => {a : T // a ∈ S.carrier}⟩

theorem add_mem (S : SubCompleteDioid T) {a b : T}
    (ha : a ∈ S) (hb : b ∈ S) : a ⊕ₒ b ∈ S :=
  S.add_mem' ha hb

theorem mul_mem (S : SubCompleteDioid T) {a b : T}
    (ha : a ∈ S) (hb : b ∈ S) : a ⊗ₒ b ∈ S :=
  S.mul_mem' ha hb
```

The operations on the substructure act on the underlying values,
carrying the closure proofs; the laws are those of $`T` lifted by
`Subtype.ext`. This gives the inherited complete dioid, found by
instance resolution on the coercion-to-type $`\uparrow S`.

*Definition:* the inherited `CompleteDioid` on $`\uparrow S`

```lean
noncomputable instance (S : SubCompleteDioid T) :
    CompleteDioid S where
  add a b := ⟨a.1 ⊕ₒ b.1, S.add_mem' a.2 b.2⟩
  zero := ⟨εₒ, S.eps_mem'⟩
  mul a b := ⟨a.1 ⊗ₒ b.1, S.mul_mem' a.2 b.2⟩
  one := ⟨eₒ, S.one_mem'⟩
  oplus_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  eps_oplus _ := Subtype.ext (zero_add _)
  oplus_eps _ := Subtype.ext (add_zero _)
  oplus_comm _ _ := Subtype.ext (add_comm _ _)
  otimes_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)
  one_otimes _ := Subtype.ext (one_mul _)
  otimes_one _ := Subtype.ext (mul_one _)
  left_distrib _ _ _ := Subtype.ext (mul_add _ _ _)
  right_distrib _ _ _ := Subtype.ext (add_mul _ _ _)
  eps_otimes _ := Subtype.ext (zero_mul _)
  otimes_eps _ := Subtype.ext (mul_zero _)
  otimes_comm _ _ := Subtype.ext (mul_comm _ _)
  oplus_idem _ := Subtype.ext (Dioid.oplus_idem _)
  iSup f := ⟨CompleteDioid.iSup (fun i => (f i).1),
    S.iSup_mem' _ (fun i => (f i).2)⟩
  le_iSup f i := Subtype.ext (by
    show (f i).1 ⊕ₒ CompleteDioid.iSup _
        = CompleteDioid.iSup _
    exact CompleteDioid.le_iSup (fun i => (f i).1) i)
  iSup_le f b hb := Subtype.ext (by
    show CompleteDioid.iSup _ ⊕ₒ b.1 = b.1
    exact CompleteDioid.iSup_le (fun i => (f i).1) b.1
      (fun i => congrArg Subtype.val (hb i)))
  mul_iSup a f := Subtype.ext (by
    show a.1 ⊗ₒ CompleteDioid.iSup _
        = CompleteDioid.iSup _
    exact CompleteDioid.mul_iSup a.1 (fun i => (f i).1))
```

The substructure is _compatible_ with the ambient one: its operations
are those of $`T` restricted, so the inclusion $`\uparrow S \to T` is a
complete-dioid homomorphism — it commutes with the sum, the product,
both neutrals, and arbitrary suprema. Each equation holds by
definition.

*Theorem:* the inclusion preserves the operations

```lean
theorem coe_add (S : SubCompleteDioid T) (a b : S) :
    ((a ⊕ₒ b : S) : T) = (a : T) ⊕ₒ (b : T) :=
  rfl

theorem coe_mul (S : SubCompleteDioid T) (a b : S) :
    ((a ⊗ₒ b : S) : T) = (a : T) ⊗ₒ (b : T) :=
  rfl

theorem coe_eps (S : SubCompleteDioid T) :
    ((εₒ : S) : T) = εₒ :=
  rfl

theorem coe_one (S : SubCompleteDioid T) :
    ((eₒ : S) : T) = eₒ :=
  rfl

theorem coe_iSup (S : SubCompleteDioid T)
    {ι : Type u} (f : ι → S) :
    ((CompleteDioid.iSup f : S) : T)
      = CompleteDioid.iSup (fun i => (f i : T)) :=
  rfl

end SubCompleteDioid
```

```lean
end Algebra
```

```lean
end VerifiedWiki
```
