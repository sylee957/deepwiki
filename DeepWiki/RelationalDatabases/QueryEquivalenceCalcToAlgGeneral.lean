import DeepWiki.RelationalDatabases.QueryEquivalenceCalcToAlg

/-! # Reduction of the tuple calculus to the algebra (§2.4): the general case via position tagging
The disjoint-context reduction (`QueryEquivalenceCalcToAlg`) assumes the variable schemes do not
clash. The book's general method (§2.4.1, Step 2) removes that assumption by *tagging* each
attribute with its tuple variable's position. We tag by **co-depth** (distance from the outermost
variable) rather than de Bruijn depth: co-depth is stable when the existential adds a fresh innermost
variable, so the tagged tail is left unchanged and the existential becomes a plain projection (no
attribute renaming on the algebra side is needed). A variable of co-depth `k` over scheme `Ω`
contributes tags `{(k, a) | a ∈ Ω}`; different variables get different `k`, so the product scheme is
clash-free even when two variables range over the same database relation.

The tagged environment-flattening, lookup bridge, translation (where an agreement atom becomes a
genuine equality constraint between tagged copies, not the vacuous condition of the disjoint case)
and correctness are layered on this. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- *Position-tagged attributes* (§2.4.1, Step 2): attribute `a` at position `i` is `(i, a)`. -/
abbrev TagAtt (Att : Type u) : Type u := ℕ × Att

/-- Tag an attribute with a fixed position `n`. -/
def tagAt (n : ℕ) : Att ↪ TagAtt Att := ⟨fun a => (n, a), fun _ _ h => by simpa using h⟩

/-- The *tagged product scheme* of a context: the head variable (outermost co-depth `Γ.length`)
tagged with `Γ.length`, the rest keeping their (stable) co-depth tags. -/
def flattenTagged : Ctx Att → Finset (TagAtt Att)
  | [] => ∅
  | Ω :: Γ => Ω.map (tagAt Γ.length) ∪ flattenTagged Γ

@[simp] theorem flattenTagged_nil : flattenTagged ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenTagged_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenTagged (Ω :: Γ) = Ω.map (tagAt Γ.length) ∪ flattenTagged Γ := rfl

/-- Every tag of the product scheme has position below the context length (so co-depth tags of a
context never reach `Γ.length`). -/
theorem flattenTagged_lt : {Γ : Ctx Att} → {p : TagAtt Att} → p ∈ flattenTagged Γ → p.1 < Γ.length
  | [], p, h => absurd h (Finset.notMem_empty p)
  | Ω :: Γ, p, h => by
      rw [flattenTagged_cons, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨a, _, hap⟩ := Finset.mem_map.mp h
        rw [tagAt, Function.Embedding.coeFn_mk] at hap
        rw [← hap]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (flattenTagged_lt h)

/-- A top-position (`= Γ.length`) tag of `flattenTagged (Ω :: Γ)` comes from the head variable. -/
theorem mem_flattenTagged_head {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (h0 : p.1 = Γ.length) : p.2 ∈ Ω := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, ha, hap⟩ := Finset.mem_map.mp hp
    rw [tagAt, Function.Embedding.coeFn_mk] at hap
    rw [← hap]; exact ha
  · exact absurd h0 (Nat.ne_of_lt (flattenTagged_lt hp))

/-- A below-top tag of `flattenTagged (Ω :: Γ)` belongs (unchanged) to the tail. -/
theorem mem_flattenTagged_tail {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (hn : p.1 ≠ Γ.length) : p ∈ flattenTagged Γ := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, _, hap⟩ := Finset.mem_map.mp hp
    rw [tagAt, Function.Embedding.coeFn_mk] at hap
    exact absurd (by rw [← hap]) hn
  · exact hp

/-- Glue an environment into a flat row over the tagged product scheme: the tag `(k, a)` reads
attribute `a` from the variable of co-depth `k`. -/
def envToTupleTagged : {Γ : Ctx Att} → Env Val Γ → Tuple (flattenTagged Γ) Val
  | [], _ => fun p => absurd p.property (Finset.notMem_empty p.val)
  | _ :: Γ, (t, e) => fun p =>
      if h : p.val.1 = Γ.length then t ⟨p.val.2, mem_flattenTagged_head p.property h⟩
      else (envToTupleTagged e) ⟨p.val, mem_flattenTagged_tail p.property h⟩

/-- The co-depth of a variable — its position tag in the product scheme (distance from outermost). -/
def Var.cotag : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → ℕ
  | (_ :: Γ'), _, .here => Γ'.length
  | _, _, .there v' => v'.cotag

/-- A variable's attribute, tagged with the variable's co-depth, lies in the product scheme. -/
theorem tag_mem_flattenTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) → {a : Att} →
    a ∈ Ω → (v.cotag, a) ∈ flattenTagged Γ
  | _, _, .here, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inl (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  | _, _, .there v, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inr (tag_mem_flattenTagged v ha)

/-- **Tagged lookup bridge**: reading a variable equals the tagged flat row at the variable's
co-depth tags — needing *no* disjointness, since co-depth tags are unique. -/
theorem lookup_eq_envToTupleTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) →
    (e : Env Val Γ) → {a : Att} → (ha : a ∈ Ω) → (hflat : (v.cotag, a) ∈ flattenTagged Γ) →
    lookup v e ⟨a, ha⟩ = envToTupleTagged e ⟨(v.cotag, a), hflat⟩
  | _ :: Γ', _, .here, (_, _), a, ha, _ => by
      simp only [lookup, envToTupleTagged, Var.cotag, dif_pos]
  | _ :: Γ', _, .there v', (_, e'), a, ha, _ => by
      have hne : v'.cotag ≠ Γ'.length := Nat.ne_of_lt (flattenTagged_lt (tag_mem_flattenTagged v' ha))
      simp only [lookup, envToTupleTagged, Var.cotag, dif_neg hne]
      exact lookup_eq_envToTupleTagged v' e' ha _

end DeepWiki
