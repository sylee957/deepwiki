import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Inclusion dependencies
An inclusion dependency `[A₁,…,Aₖ] ⊆ [B₁,…,Bₖ]` holds in a row set when every row `t` is matched
on the `A`-attributes by some row `t'` on the `B`-attributes (Def 3.15). Unlike functional,
multivalued and join dependencies, inclusion dependencies are genuinely semantic (about the
contents) and the order of the attribute sequences matters. Two of the standard inference rules
— reflexivity and transitivity — are proved sound at the row-set level. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A row set satisfies the *inclusion dependency* `[A₁,…,Aₖ] ⊆ [B₁,…,Bₖ]` (Def 3.15): every row
`t` of `r` has a row `t'` of `r` with `t(Aᵢ) = t'(Bᵢ)` for every `i`. The attributes are given as
sequences (their order matters). -/
def SatisfiesInd {k : ℕ} (r : Table Ω Val) (A B : Fin k → {x // x ∈ Ω}) : Prop :=
  ∀ t ∈ r, ∃ t' ∈ r, ∀ i, t (A i) = t' (B i)

variable {k : ℕ} {r : Table Ω Val} {A B C : Fin k → {x // x ∈ Ω}}

/-- Inclusion dependencies are reflexive: `[A] ⊆ [A]`. -/
theorem satisfiesInd_refl : SatisfiesInd r A A :=
  fun t ht => ⟨t, ht, fun _ => rfl⟩

/-- Inclusion dependencies are transitive: `[A] ⊆ [B]` and `[B] ⊆ [C]` give `[A] ⊆ [C]`. -/
theorem satisfiesInd_trans (hAB : SatisfiesInd r A B) (hBC : SatisfiesInd r B C) :
    SatisfiesInd r A C := by
  intro t ht
  obtain ⟨t', ht', h1⟩ := hAB t ht
  obtain ⟨t'', ht'', h2⟩ := hBC t' ht'
  exact ⟨t'', ht'', fun i => (h1 i).trans (h2 i)⟩

end DeepWiki
