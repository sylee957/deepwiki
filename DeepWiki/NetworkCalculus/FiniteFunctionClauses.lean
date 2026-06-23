import DeepWiki.NetworkCalculus.BooleanConstraints
import Mathlib.Data.Fintype.Prod

/-! # Finite-function → CNF gadget (the Cook–Levin transition encoder)

A reusable encoder turning an arbitrary function `f : A → B` (and a binary `g : A → B → C`)
over `Fintype`s into clauses that, on **one-hot-encoded** inputs, force the one-hot-encoded
output to equal `f` of the input. The gadget asserts only the input→output *functional link*;
one-hotness of inputs and outputs is the caller's responsibility (`exactlyOne`), and combining
the two pins the output VALUE to `f` of the input value (`funClauses_out_eq`).

This is the gadget the Cook–Levin transition clauses use to encode `TM2`'s `Stmt` functions
(`push`'s `σ → Γ k`, `load`'s `σ → σ`, `branch`'s `σ → Bool`, `goto`'s `σ → Λ`, `peek`/`pop`'s
`σ → Option (Γ k) → σ`). Everything is generic over the variable count `n` and the carrier
`Fintype`s.
-/

namespace DeepWiki.BooleanConstraints

open CnfFormula

/-! ## A literal-satisfaction shorthand: `litSat assign (v, true) = true ↔ assign v = true` -/

/-- A positive literal `(v, true)` is satisfied iff its variable is assigned `true`. -/
theorem litSat_true_iff {n : ℕ} (assign : Fin n → Bool) (v : Fin n) :
    litSat assign (v, true) = true ↔ assign v = true := by
  simp [litSat]

/-! ## (1) Unary gadget: one implication clause per input value -/

/-- The clauses encoding `f : A → B`: for each `a`, "if `inVar a` then `outVar (f a)`". -/
noncomputable def funClauses {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n)
    (outVar : B → Fin n) (f : A → B) : List (Clause n) :=
  (Finset.univ : Finset A).toList.map (fun a => implies (inVar a, true) (outVar (f a), true))

/-- A clause is in `funClauses` iff it is the implication clause for some input value `a`. -/
theorem mem_funClauses {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n) (outVar : B → Fin n)
    (f : A → B) (c : Clause n) :
    c ∈ funClauses inVar outVar f ↔
      ∃ a : A, c = implies (inVar a, true) (outVar (f a), true) := by
  simp only [funClauses, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, eq_comm]

/-- **Forward spec.** If `assign` satisfies the gadget and the input `inVar a₀` is `true`, then
the output `outVar (f a₀)` is `true`. -/
theorem funClauses_spec {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n) (outVar : B → Fin n)
    (f : A → B) (assign : Fin n → Bool)
    (h : satisfiesAll assign (funClauses inVar outVar f)) (a₀ : A)
    (hin : assign (inVar a₀) = true) : assign (outVar (f a₀)) = true := by
  have hc : implies (inVar a₀, true) (outVar (f a₀), true) ∈ funClauses inVar outVar f :=
    (mem_funClauses inVar outVar f _).2 ⟨a₀, rfl⟩
  have := (implies_sat_iff assign (inVar a₀, true) (outVar (f a₀), true)).1 (h _ hc)
  rw [litSat_true_iff, litSat_true_iff] at this
  exact this hin

/-- **Converse (encode).** If `assign` is functional-consistent — each input `true` forces its
output `true` — then it satisfies the gadget. -/
theorem funClauses_satisfies {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n)
    (outVar : B → Fin n) (f : A → B) (assign : Fin n → Bool)
    (hcons : ∀ a : A, assign (inVar a) = true → assign (outVar (f a)) = true) :
    satisfiesAll assign (funClauses inVar outVar f) := by
  intro c hc
  obtain ⟨a, rfl⟩ := (mem_funClauses inVar outVar f c).1 hc
  rw [implies_sat_iff, litSat_true_iff, litSat_true_iff]
  exact hcons a

/-- **Output determination.** Under the forward spec's conclusion plus output one-hotness, any
`b` with `outVar b` true equals `f a₀`: the gadget pins the output value to `f` of the input. -/
theorem funClauses_out_eq {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n) (outVar : B → Fin n)
    (f : A → B) (assign : Fin n → Bool)
    (h : satisfiesAll assign (funClauses inVar outVar f)) (a₀ : A)
    (hin : assign (inVar a₀) = true)
    (hOut : ∀ b b' : B, assign (outVar b) = true → assign (outVar b') = true → b = b')
    (b : B) (hb : assign (outVar b) = true) : b = f a₀ :=
  hOut b (f a₀) hb (funClauses_spec inVar outVar f assign h a₀ hin)

/-! ## (2) Binary gadget: one 3-literal clause per input pair -/

/-- A negated literal `(v, !s)` is satisfied iff the positive literal `(v, s)` is not. -/
theorem litSat_neg {n : ℕ} (assign : Fin n → Bool) (v : Fin n) (s : Bool) :
    litSat assign (v, !s) = !(litSat assign (v, s)) := by
  simp only [litSat]
  cases assign v <;> cases s <;> rfl

/-- The 3-literal clause `inA a ∧ inB b → outVar (g a b)`, i.e. `¬inA a ∨ ¬inB b ∨ out`. -/
def implies₂ {n : ℕ} (a b c : Literal n) : Clause n := [(a.1, !a.2), (b.1, !b.2), c]

/-- **`implies₂` semantics.** `¬a ∨ ¬b ∨ c` is satisfied iff `a`, `b` both satisfied implies `c`. -/
theorem implies₂_sat_iff {n : ℕ} (assign : Fin n → Bool) (a b c : Literal n) :
    clauseSat assign (implies₂ a b c) = true ↔
      (litSat assign a = true → litSat assign b = true → litSat assign c = true) := by
  simp only [implies₂, clauseSat, List.any_cons, List.any_nil, Bool.or_false]
  -- rewrite the two negated literals to negations of the positive ones
  have e1 : litSat assign (a.1, !a.2) = !(litSat assign a) := litSat_neg assign a.1 a.2
  have e2 : litSat assign (b.1, !b.2) = !(litSat assign b) := litSat_neg assign b.1 b.2
  rw [e1, e2]
  cases hca : litSat assign a <;> cases hcb : litSat assign b <;>
    cases hcc : litSat assign c <;> simp

/-- The clauses encoding `g : A → B → C`: for each `(a, b)`, "if `inA a ∧ inB b` then
`outVar (g a b)`". -/
noncomputable def funClauses₂ {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) : List (Clause n) :=
  (Finset.univ : Finset (A × B)).toList.map
    (fun p => implies₂ (inA p.1, true) (inB p.2, true) (outVar (g p.1 p.2), true))

/-- A clause is in `funClauses₂` iff it is the implication clause for some input pair `(a, b)`. -/
theorem mem_funClauses₂ {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) (c : Clause n) :
    c ∈ funClauses₂ inA inB outVar g ↔
      ∃ (a : A) (b : B),
        c = implies₂ (inA a, true) (inB b, true) (outVar (g a b), true) := by
  simp only [funClauses₂, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨⟨a, b⟩, -, rfl⟩; exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), Finset.mem_univ _, rfl⟩


/-- **Forward spec.** If `assign` satisfies the binary gadget and both inputs `inA a₀`, `inB b₀`
are `true`, then the output `outVar (g a₀ b₀)` is `true`. -/
theorem funClauses₂_spec {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) (assign : Fin n → Bool)
    (h : satisfiesAll assign (funClauses₂ inA inB outVar g)) (a₀ : A) (b₀ : B)
    (hinA : assign (inA a₀) = true) (hinB : assign (inB b₀) = true) :
    assign (outVar (g a₀ b₀)) = true := by
  have hc : implies₂ (inA a₀, true) (inB b₀, true) (outVar (g a₀ b₀), true)
      ∈ funClauses₂ inA inB outVar g :=
    (mem_funClauses₂ inA inB outVar g _).2 ⟨a₀, b₀, rfl⟩
  have := (implies₂_sat_iff assign (inA a₀, true) (inB b₀, true) (outVar (g a₀ b₀), true)).1
    (h _ hc)
  rw [litSat_true_iff, litSat_true_iff, litSat_true_iff] at this
  exact this hinA hinB

/-- **Converse (encode).** If `assign` is functional-consistent for `g` — both inputs `true`
forces the output `true` — then it satisfies the binary gadget. -/
theorem funClauses₂_satisfies {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) (assign : Fin n → Bool)
    (hcons : ∀ (a : A) (b : B),
      assign (inA a) = true → assign (inB b) = true → assign (outVar (g a b)) = true) :
    satisfiesAll assign (funClauses₂ inA inB outVar g) := by
  intro c hc
  obtain ⟨a, b, rfl⟩ := (mem_funClauses₂ inA inB outVar g c).1 hc
  rw [implies₂_sat_iff, litSat_true_iff, litSat_true_iff, litSat_true_iff]
  exact hcons a b

/-- **Output determination (binary).** Under the forward spec's conclusion plus output
one-hotness, any `c` with `outVar c` true equals `g a₀ b₀`. -/
theorem funClauses₂_out_eq {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) (assign : Fin n → Bool)
    (h : satisfiesAll assign (funClauses₂ inA inB outVar g)) (a₀ : A) (b₀ : B)
    (hinA : assign (inA a₀) = true) (hinB : assign (inB b₀) = true)
    (hOut : ∀ c c' : C, assign (outVar c) = true → assign (outVar c') = true → c = c')
    (c : C) (hc : assign (outVar c) = true) : c = g a₀ b₀ :=
  hOut c (g a₀ b₀) hc (funClauses₂_spec inA inB outVar g assign h a₀ b₀ hinA hinB)

/-! ## Restatements: the load-bearing forward specs against their intended wording -/

-- `funClauses_spec`: gadget satisfied + input known ⟹ output known.
example {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n) (outVar : B → Fin n) (f : A → B)
    (assign : Fin n → Bool) (h : satisfiesAll assign (funClauses inVar outVar f)) (a₀ : A)
    (hin : assign (inVar a₀) = true) : assign (outVar (f a₀)) = true :=
  funClauses_spec inVar outVar f assign h a₀ hin

-- `funClauses₂_spec`: binary gadget satisfied + both inputs known ⟹ output known.
example {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n) (inB : B → Fin n)
    (outVar : C → Fin n) (g : A → B → C) (assign : Fin n → Bool)
    (h : satisfiesAll assign (funClauses₂ inA inB outVar g)) (a₀ : A) (b₀ : B)
    (hinA : assign (inA a₀) = true) (hinB : assign (inB b₀) = true) :
    assign (outVar (g a₀ b₀)) = true :=
  funClauses₂_spec inA inB outVar g assign h a₀ b₀ hinA hinB

end DeepWiki.BooleanConstraints
