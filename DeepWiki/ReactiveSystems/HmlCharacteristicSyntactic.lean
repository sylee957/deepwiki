import DeepWiki.ReactiveSystems.HmlRecursionSystems
import DeepWiki.ReactiveSystems.HmlCharacteristic

/-! # The syntactic characteristic formula (§6.6)
For a *finite* LTS, the strong-bisimilarity class of each state is characterised
by a single Hennessy–Milner formula with recursion: the characteristic equation
system `charSys` assigns to each state `p` (a variable `X_p`) the formula
`(⋀_a ⋀_{p'∈Der a p} ⟨a⟩ X_{p'}) ∧ (⋀_a [a] ⋁_{p'∈Der a p} X_{p'})` — "every move
of `p` is matchable" and "no `a`-move leaves `p`'s `a`-successors". Its greatest
solution `sysMax (charSys)` equals the semantic characteristic property
`charProp`, hence the bisimilarity class: `q ⊨ X_p` iff `p ~ q`. This realises
the semantic `charProp`/Theorem 6.4 as an explicit recursive formula. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- Finite conjunction over `HMLV`, folding over a `Finset`'s `toList`. -/
noncomputable def bigAndV {V Act ι : Type*} (s : Finset ι) (f : ι → HMLV V Act) : HMLV V Act :=
  (s.toList.map f).foldr HMLV.and HMLV.tt

/-- Finite disjunction over `HMLV`, folding over a `Finset`'s `toList`. -/
noncomputable def bigOrV {V Act ι : Type*} (s : Finset ι) (f : ι → HMLV V Act) : HMLV V Act :=
  (s.toList.map f).foldr HMLV.or HMLV.ff

variable {V : Type*}

/-- List-version of the conjunction denotation. -/
theorem denotV_foldr_and (L : LTS Proc Act) (ρ : V → Set Proc) {ι} (l : List ι)
    (f : ι → HMLV V Act) :
    denotV L ρ ((l.map f).foldr HMLV.and HMLV.tt) = ⋂ i ∈ l, denotV L ρ (f i) := by
  induction l with
  | nil => simp [denotV]
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, denotV, ih, List.mem_cons,
      Set.iInter_iInter_eq_or_left]

/-- List-version of the disjunction denotation. -/
theorem denotV_foldr_or (L : LTS Proc Act) (ρ : V → Set Proc) {ι} (l : List ι)
    (f : ι → HMLV V Act) :
    denotV L ρ ((l.map f).foldr HMLV.or HMLV.ff) = ⋃ i ∈ l, denotV L ρ (f i) := by
  induction l with
  | nil => simp [denotV]
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, denotV, ih, List.mem_cons,
      Set.iUnion_iUnion_eq_or_left]

/-- `⟦⋀_{i∈s} f i⟧ = ⋂_{i∈s} ⟦f i⟧`. -/
theorem denotV_bigAndV (L : LTS Proc Act) (ρ : V → Set Proc) {ι} (s : Finset ι)
    (f : ι → HMLV V Act) :
    denotV L ρ (bigAndV s f) = ⋂ i ∈ s, denotV L ρ (f i) := by
  rw [bigAndV, denotV_foldr_and]
  apply Set.ext
  intro p
  simp [Finset.mem_toList]

/-- `⟦⋁_{i∈s} f i⟧ = ⋃_{i∈s} ⟦f i⟧`. -/
theorem denotV_bigOrV (L : LTS Proc Act) (ρ : V → Set Proc) {ι} (s : Finset ι)
    (f : ι → HMLV V Act) :
    denotV L ρ (bigOrV s f) = ⋃ i ∈ s, denotV L ρ (f i) := by
  rw [bigOrV, denotV_foldr_or]
  apply Set.ext
  intro p
  simp [Finset.mem_toList]

/-- The `a`-successors of `p` as a `Finset`. -/
def Der (L : LTS Proc Act) [Fintype Proc] [∀ p a p', Decidable (L.step p a p')]
    (a : Act) (p : Proc) : Finset Proc :=
  Finset.univ.filter (fun p' => L.step p a p')

@[simp] theorem mem_Der (L : LTS Proc Act) [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')]
    {a : Act} {p p' : Proc} :
    p' ∈ Der L a p ↔ L.step p a p' := by
  simp [Der]

/-- The characteristic equation system of a finite LTS (Equation 6.15, §6.6):
each state `p` gets a variable (`V := Proc`) whose formula says "every move of `p`
is matchable into the named successor" (`⋀_a ⋀_{p'∈Der a p} ⟨a⟩ p'`) and "every
`a`-move lands among `p`'s `a`-successors" (`⋀_a [a] ⋁_{p'∈Der a p} p'`). -/
noncomputable def charSys (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] : Proc → HMLV Proc Act :=
  fun p =>
    (bigAndV (Finset.univ : Finset Act)
        (fun a => bigAndV (Der L a p) (fun p' => HMLV.dia a (HMLV.var p')))).and
    (bigAndV (Finset.univ : Finset Act)
        (fun a => HMLV.box a (bigOrV (Der L a p) (fun p' => HMLV.var p'))))

/-- The semantic functional of the characteristic equation system is exactly the
characteristic-property functional `charFun`. -/
theorem sysFun_charSys_eq (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] (ρ : Proc → Set Proc) :
    sysFun L (charSys L) ρ = charFun L ρ := by
  funext p
  show denotV L ρ (charSys L p) = charFun L ρ p
  rw [charSys]
  simp only [denotV, denotV_bigAndV, denotV_bigOrV, mem_Der, Finset.mem_univ,
    Set.iInter_true]
  apply Set.ext
  intro q
  simp only [charFun, OrderHom.coe_mk, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_iUnion, exists_prop]

/-- The semantic functionals coincide as order homomorphisms. -/
theorem sysFun_charSys_eq_orderHom (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] : sysFun L (charSys L) = charFun L :=
  OrderHom.ext _ _ (funext (sysFun_charSys_eq L))

/-- The largest solution of the characteristic equation system equals the
characteristic property (the greatest fixed point of `charFun`). -/
theorem sysMax_charSys_eq_charProp (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] : sysMax L (charSys L) = charProp L := by
  rw [sysMax, charProp, sysFun_charSys_eq_orderHom]

/-- **Theorem 6.4 / Eq. 6.15** (§6.6). The largest solution of the syntactic
characteristic equation system of a finite LTS is the strong-bisimilarity class:
`q ∈ ⟦charSys p⟧` iff `p ~ q`. -/
theorem charSys_characterizes (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] (p q : Proc) :
    q ∈ sysMax L (charSys L) p ↔ Bisimilar L p q := by
  rw [sysMax_charSys_eq_charProp]
  exact charProp_eq_bisimilar L p q

end LTS

end DeepWiki.ReactiveSystems
