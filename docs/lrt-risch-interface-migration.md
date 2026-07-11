# LRT Risch interface migration

The algebraic-residue recursive solver currently places executable hooks and
denotation proofs in `LawfulRischLevelLrt`.  This violates the engine-wide
`C…` / `LawfulC…` boundary and prevents a recursive LRT level from being used
as a composable operation.

## Target

1. Introduce `CRischLevelLrt` as the Prop-free operation interface containing
   the monomial hook and optional single-`w` coefficient hook.
2. Make `LawfulCRischLevelLrt C` contain only the special and algebraic-residue
   soundness laws for a supplied `C`.
3. Move assembled LRT operations and their theorems under `CRischLevelLrt`,
   parameterized by `C`; migrate primitive and tower realizers to paired
   operation/lawful instances.
4. Keep Liouville descent as a separate relative-completeness frontier.  A
   later pass will package the resulting decision theorem as the LRT-level
   completeness contract once its domain and output certificate are generic.
5. Delete the old mixed class and update all imports, documentation, and
   grounding results.  Gate the LRT modules, their immediate consumers, and
   the strict full build before committing.
