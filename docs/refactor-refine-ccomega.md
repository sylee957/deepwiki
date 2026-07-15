# Refine CCω module reorganization

The scoped calculus currently uses a flat `DependentCalculus*` file family, while its readable
surface notation lives inside an examples module. Group the calculus core, metatheory, and surface
elaboration under `DeepWiki/Refine/CCOmega/` without changing declaration namespaces or theorem
statements.

## Boundary

Move these modules in dependency order:

1. `DependentCalculusSyntax` → `CCOmega/Syntax`
2. `DependentCalculusTyping` → `CCOmega/Typing`
3. `DependentCalculusConfluence` → `CCOmega/Confluence`
4. `DependentCalculusRegularity` → `CCOmega/Regularity`
5. `DependentCalculusPrincipalTyping` → `CCOmega/PrincipalTyping`
6. `DependentCalculusCumulativeInversion` → `CCOmega/CumulativeInversion`
7. `DependentCalculusSubjectReduction` → `CCOmega/SubjectReduction`
8. Extract the named `ccω!{...}` notation into `CCOmega/SurfaceSyntax`.

Keep `DeepWiki.Refine.DependentCalculus` as the declaration namespace. Raw, univalent, and annotated
parametricity remain separate consumers because they are translations or extensions of the
calculus, not part of its core definition.

## Compatibility and gates

- Add `DeepWiki/Refine/CCOmega.lean` as the area aggregator.
- Update every repository import to the new module paths; do not leave forwarding shims.
- Keep the examples module focused on tutorial declarations rather than macro implementation.
- Gate `DeepWiki.Refine.CCOmega.SurfaceSyntax`, the parametricity tutorial, `DeepWiki.Refine`, and
  finally the complete repository serially.
