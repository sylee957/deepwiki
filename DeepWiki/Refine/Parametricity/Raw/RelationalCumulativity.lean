import DeepWiki.Refine.Parametricity.Raw.Conversion

/-! # Relational cumulativity for raw parametricity

Ordinary `CCω` cumulative conversion preserves every substituted raw relation fiber.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

/-- Raising the result universe raises the beta-normal element-relation type. -/
theorem elementRelationType_cumulative (term : Term n) {lower upper : Nat}
    (levelOrder : lower ≤ upper) :
    Cumulative (elementRelationType term lower) (elementRelationType term upper) := by
  unfold elementRelationType
  exact .pi (.refl _) (.pi (.refl _) (.sort levelOrder))

/-- The related-term interpretation of universes is monotone in the universe level. -/
theorem relatedTermType_sort_cumulative (term : Term n) {lower upper : Nat}
    (levelOrder : lower ≤ upper) :
    Cumulative (relatedTermType term (.sort lower))
      (relatedTermType term (.sort upper)) := by
  exact .trans (.conversion (relatedTermType_sort_beta term lower))
    (.trans (elementRelationType_cumulative term levelOrder)
      (.conversion (relatedTermType_sort_beta term upper).symm))

/-- Apply a weakened function to the newest source variable. -/
private def fiberApplication (function : Term n) : Term (n + 1) :=
  .app (function.rename Renaming.shift) (.var 0)

/-- The related type of `fiberApplication` is the output in a product-relation fiber. -/
private theorem relatedTermType_fiberApplication (function : Term n)
    (codomain : Term (n + 1)) :
    relatedTermType (fiberApplication function) codomain =
      applicationRelationBody function codomain := by
  unfold fiberApplication relatedTermType applicationRelationBody
  simp only [original, primed, Term.rename]
  rw [show
    Term.rename (originalRenaming (n + 1)) (Term.rename Renaming.shift function) =
      weakenBy (original function) 3 by
        exact (original_rename_shift function).trans
          (weakenBy_three_eq_rename_translatedShift (original function)).symm]
  rw [show
    Term.rename (primedRenaming (n + 1)) (Term.rename Renaming.shift function) =
      weakenBy (primed function) 3 by
        exact (primed_rename_shift function).trans
          (weakenBy_three_eq_rename_translatedShift (primed function)).symm]
  rfl

/-- Fiberwise codomain cumulativity and convertible domains lift through products. -/
theorem relatedTermType_pi_cumulative (term : Term n)
    {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainEqual : Convertible domain domain')
    (codomainCumulative : ∀ output : Term (n + 1),
      Cumulative (relatedTermType output codomain)
        (relatedTermType output codomain')) :
    Cumulative (relatedTermType term (.pi domain codomain))
      (relatedTermType term (.pi domain' codomain')) := by
  have outputCumulative := codomainCumulative (fiberApplication term)
  rw [relatedTermType_fiberApplication term codomain,
    relatedTermType_fiberApplication term codomain'] at outputCumulative
  have originalDomainEqual := original_convertible domainEqual
  have primedDomainEqual := Convertible.weakenBy (primed_convertible domainEqual) 1
  have relationDomainEqual : Convertible
      (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
      (.app (.app (weakenBy (translate domain') 2) (.var 1)) (.var 0)) :=
    Convertible.app_both
      (Convertible.app_both
        (Convertible.weakenBy (translate_convertible domainEqual) 2) (.refl _))
      (.refl _)
  have normalCumulative :
      Cumulative (piRelationFiberNormal domain codomain term)
        (piRelationFiberNormal domain' codomain' term) := by
    unfold piRelationFiberNormal
    exact .pi originalDomainEqual
      (.pi primedDomainEqual
        (.pi relationDomainEqual outputCumulative))
  have sourceBeta := relatedTermType_pi_beta term domain codomain
  rw [piRelationFiber_eq_normal] at sourceBeta
  have targetBeta := relatedTermType_pi_beta term domain' codomain'
  rw [piRelationFiber_eq_normal] at targetBeta
  exact .trans (.conversion sourceBeta)
    (.trans normalCumulative (.conversion targetBeta.symm))

/-- `IsRelationallyCumulative left right` compares every substituted binary relation fiber. -/
def IsRelationallyCumulative (left right : Term n) : Prop :=
  ∀ {target : Nat} (mapping : Substitution n target) (term : Term target),
    Cumulative (relatedTermType term (left.substitute mapping))
      (relatedTermType term (right.substitute mapping))

namespace IsRelationallyCumulative

/-- Definitional conversion induces relational-fiber cumulativity. -/
theorem of_convertible {left right : Term n} (conversion : Convertible left right) :
    IsRelationallyCumulative left right := fun mapping _ =>
  .conversion (relatedTermType_convertible (conversion.substitute mapping))

/-- Universe-level order induces relational-fiber cumulativity. -/
theorem sort {lower upper : Nat} (levelOrder : lower ≤ upper) :
    IsRelationallyCumulative (.sort lower : Term n) (.sort upper) := fun _ term =>
  relatedTermType_sort_cumulative term levelOrder

/-- Relational-fiber cumulativity is transitive. -/
theorem trans {first second third : Term n}
    (firstSecond : IsRelationallyCumulative first second)
    (secondThird : IsRelationallyCumulative second third) :
    IsRelationallyCumulative first third := fun mapping term =>
  (firstSecond mapping term).trans (secondThird mapping term)

/-- Convertible domains and fiberwise cumulative codomains induce cumulative product fibers. -/
theorem pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainEqual : Convertible domain domain')
    (codomainCumulative : IsRelationallyCumulative codomain codomain') :
    IsRelationallyCumulative (.pi domain codomain) (.pi domain' codomain') :=
  fun mapping term => relatedTermType_pi_cumulative term (domainEqual.substitute mapping)
    (codomainCumulative (Substitution.lift mapping))

/-- Relational cumulativity specializes to the original scope. -/
theorem apply {left right : Term n} (subtype : IsRelationallyCumulative left right)
    (term : Term n) :
    Cumulative (relatedTermType term left) (relatedTermType term right) := by
  simpa only [Term.substitute_identity] using subtype Substitution.identity term

/-- Relational cumulativity is stable under simultaneous substitution. -/
theorem substitute {left right : Term source}
    (subtype : IsRelationallyCumulative left right)
    (mapping : Substitution source target) :
    IsRelationallyCumulative (left.substitute mapping) (right.substitute mapping) := by
  intro final outer term
  simpa only [Term.substitute_comp] using
    subtype (Substitution.comp outer mapping) term

/-- Relational cumulativity is stable under a change of free-variable scope. -/
theorem rename {left right : Term source}
    (subtype : IsRelationallyCumulative left right)
    (mapping : Renaming source target) :
    IsRelationallyCumulative (left.rename mapping) (right.rename mapping) := by
  intro final outer term
  simpa only [Term.substitute_rename] using
    subtype (fun index => outer (mapping index)) term

end IsRelationallyCumulative

/-- Every ordinary cumulative conversion preserves all substituted raw relation fibers. -/
theorem isRelationallyCumulative_of_cumulative {left right : Term n}
    (subtype : Cumulative left right) :
    IsRelationallyCumulative left right := by
  induction subtype with
  | conversion equal => exact IsRelationallyCumulative.of_convertible equal
  | sort level => exact IsRelationallyCumulative.sort level
  | pi domainEqual _ codomainInduction =>
      exact IsRelationallyCumulative.pi domainEqual codomainInduction
  | trans _ _ firstInduction secondInduction =>
      exact IsRelationallyCumulative.trans firstInduction secondInduction

end DeepWiki.Refine.DependentCalculus.RawParametricity
