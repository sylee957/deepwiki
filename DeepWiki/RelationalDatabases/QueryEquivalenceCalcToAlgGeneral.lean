import DeepWiki.RelationalDatabases.QueryEquivalenceCalcToAlg

/-! # Reduction of the tuple calculus to the algebra (§2.4): the general case via position tagging
The disjoint-context reduction (`QueryEquivalenceCalcToAlg`) assumes the variable schemes do not
clash. The book's general method (§2.4.1, Step 2) removes that assumption by *tagging* each
attribute with its tuple-variable's index: attribute `a` of the i-th context variable becomes
`(i, a)`. The product scheme is then clash-free by construction — different positions get different
tags — so two variables sharing a database scheme (e.g. both ranging over the same relation) no
longer collide, and an agreement atom becomes a genuine equality constraint between two tagged
copies (rather than the vacuous condition of the disjoint case).

This file builds the tagged product scheme; the tagged environment-flattening, lookup bridge,
translation and correctness are layered on it (mirroring the disjoint development). -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- *Position-tagged attributes* (§2.4.1, Step 2): attribute `a` of the i-th context variable is
`(i, a)`. Tagging makes the product scheme clash-free without assuming disjoint input schemes. -/
abbrev TagAtt (Att : Type u) : Type u := ℕ × Att

/-- Tag an attribute with position `0` (the innermost variable). -/
def tag0 : Att ↪ TagAtt Att := ⟨fun a => (0, a), fun _ _ h => by simpa using h⟩

/-- Shift every tag's position up by one (moving one variable deeper into the context). -/
def shiftTag : TagAtt Att ↪ TagAtt Att :=
  ⟨Prod.map Nat.succ id, fun _ _ h => by simpa [Prod.ext_iff, Nat.succ_inj] using h⟩

/-- The *tagged product scheme* of a context: the head variable's attributes tagged with `0`, the
rest shifted one position deeper. -/
def flattenTagged : Ctx Att → Finset (TagAtt Att)
  | [] => ∅
  | Ω :: Γ => Ω.map tag0 ∪ (flattenTagged Γ).map shiftTag

@[simp] theorem flattenTagged_nil : flattenTagged ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenTagged_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenTagged (Ω :: Γ) = Ω.map tag0 ∪ (flattenTagged Γ).map shiftTag := rfl

/-- The head variable's tags (position `0`) are disjoint from the deeper variables' tags (positions
`≥ 1`): the product scheme is clash-free by construction. -/
theorem flattenTagged_disjoint_head (Ω : Finset Att) (Γ : Ctx Att) :
    Disjoint (Ω.map tag0) ((flattenTagged Γ).map shiftTag) := by
  rw [Finset.disjoint_left]
  rintro p hp hq
  simp only [Finset.mem_map, tag0, shiftTag, Function.Embedding.coeFn_mk] at hp hq
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨q', _, hq'⟩ := hq
  simp [Prod.ext_iff] at hq'

/-- A position-`0` tag of the product scheme comes from the head variable. -/
theorem mem_flattenTagged_zero {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (h0 : p.1 = 0) : p.2 ∈ Ω := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, ha, hap⟩ := Finset.mem_map.mp hp
    rw [tag0, Function.Embedding.coeFn_mk] at hap
    rw [← hap]; exact ha
  · obtain ⟨q, _, hqp⟩ := Finset.mem_map.mp hp
    rw [shiftTag, Function.Embedding.coeFn_mk] at hqp
    rw [← hqp] at h0; simp at h0

/-- A positive-position tag of the product scheme comes (shifted) from a deeper variable. -/
theorem mem_flattenTagged_succ {p : TagAtt Att} {Ω : Finset Att} {Γ : Ctx Att}
    (hp : p ∈ flattenTagged (Ω :: Γ)) (hn : p.1 ≠ 0) : (p.1 - 1, p.2) ∈ flattenTagged Γ := by
  rw [flattenTagged_cons, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨a, _, hap⟩ := Finset.mem_map.mp hp
    rw [tag0, Function.Embedding.coeFn_mk] at hap
    exact absurd (by rw [← hap]) hn
  · obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    rw [shiftTag, Function.Embedding.coeFn_mk] at hqp
    have h1 : (p.1 - 1, p.2) = q := by rw [← hqp]; simp
    rw [h1]; exact hq

/-- Glue an environment into a single flat row over the *tagged* product scheme: the tag `(i, a)`
reads attribute `a` from the i-th context variable. -/
def envToTupleTagged : {Γ : Ctx Att} → Env Val Γ → Tuple (flattenTagged Γ) Val
  | [], _ => fun p => absurd p.property (Finset.notMem_empty p.val)
  | _ :: _, (t, e) => fun p =>
      if h : p.val.1 = 0 then t ⟨p.val.2, mem_flattenTagged_zero p.property h⟩
      else (envToTupleTagged e) ⟨(p.val.1 - 1, p.val.2), mem_flattenTagged_succ p.property h⟩

/-- The de Bruijn depth of a variable — its position tag in the product scheme. -/
def Var.depth : {Γ : Ctx Att} → {Ω : Finset Att} → Var Γ Ω → ℕ
  | _, _, .here => 0
  | _, _, .there v => v.depth + 1

/-- A variable's attribute, tagged with the variable's depth, lies in the tagged product scheme. -/
theorem tag_mem_flattenTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) → {a : Att} →
    a ∈ Ω → (v.depth, a) ∈ flattenTagged Γ
  | _, _, .here, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inl (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  | _, _, .there v, a, ha => by
      rw [flattenTagged_cons, Finset.mem_union]
      exact Or.inr (Finset.mem_map.mpr ⟨(v.depth, a), tag_mem_flattenTagged v ha, rfl⟩)

/-- **Tagged lookup bridge**: reading a variable equals the tagged flat row at the variable's
depth-tags — and (unlike the untagged case) this needs *no* disjointness, since tags are unique. -/
theorem lookup_eq_envToTupleTagged : {Γ : Ctx Att} → {Ω : Finset Att} → (v : Var Γ Ω) →
    (e : Env Val Γ) → {a : Att} → (ha : a ∈ Ω) → (hflat : (v.depth, a) ∈ flattenTagged Γ) →
    lookup v e ⟨a, ha⟩ = envToTupleTagged e ⟨(v.depth, a), hflat⟩
  | _, _, .here, (_, _), a, ha, _ => by
      simp only [lookup, envToTupleTagged, Var.depth, dif_pos]
  | _, _, .there v', (_, e'), a, ha, _ => by
      simp only [lookup, envToTupleTagged, Var.depth]
      exact lookup_eq_envToTupleTagged v' e' ha _

end DeepWiki
