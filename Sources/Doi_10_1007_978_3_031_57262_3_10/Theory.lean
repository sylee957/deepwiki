import DeepWiki.Refine.FunctionalRelation
import Sources.Doi_10_1007_978_3_031_57262_3_10.Source

/-! # Trocq theory — coverage catalog

Coverage map for the mathematical definitions and metatheorems in the ESOP 2024 paper. The
section-specific catalogs point to the source-neutral equivalence, relation, annotation, weakening,
and core-parametricity modules.

## NOT YET FORMALIZED

- Theorem 1 (raw-parametricity abstraction theorem), p. 7 — [infra] the theorem is proved for the
  intrinsic function fragment; the exact result still needs all dependent `CCω` typing judgments.
- Theorem 2 (univalent-parametricity abstraction theorem), p. 9 — [infra] the theorem and universe
  case are proved for the intrinsic fragment; the exact result still needs full `CCω` syntax.
- Lemma 2 (equivalence as a relation functional in both directions), p. 10 — [infra] depends on
  univalence to identify an arbitrary functional relation family with an equality graph; the
  carrier- and existence-level directions are formalized.
- Lemma 3 (functions are equivalent to functional relations), p. 10 — [infra] depends on
  univalence for the equality of relation families; both structure-level conversion maps are
  formalized.
- Theorem 3 (symmetric characterization of type equivalence), p. 11 — [infra] its exact equivalence
  of structure types needs univalence; the carrier and inhabitedness characterizations are proved.
- Lemma 5 (functionality of raw parametricity translation), p. 15 — [infra] needs raw-parametricity
  syntax and judgments.
- Definition 8 (admissible parametricity context), p. 16 — [infra] needs translated contexts and
  typing judgments.
- Theorem 4 (raw-parametricity abstraction theorem in sequent form), p. 16 — [infra] depends on
  Definition 8.
- Theorem 5 (univalent abstraction theorem in sequent form), p. 17 — [infra] needs the univalent
  universe interpretation.
- Definition 9 (weakening of map classes and parametricity witnesses), p. 18 — [deferred] adjacent
  and generic indexed map-class weakening compile, as does recursive weakening for the documented
  intrinsic core; the full dependent `CCω⁺` syntax remains.
- Theorem 6 (Trocq abstraction theorem), p. 19 — [infra] the intrinsic core abstraction theorem is
  proved, while the exact theorem needs a full intrinsically typed model of annotated `CCω⁺`.
-/

namespace DeepWiki.Ccm

/-- **Definition 5, p. 12:** the bidirectional six-level hierarchy of structured relations. -/
abbrev def_5 := @DeepWiki.Refine.RelationClass

/-- **Definition 6, p. 12:** forward/backward annotations with the componentwise partial order. -/
abbrev def_6 := DeepWiki.Refine.Annotation

/-- **Definition 3, p. 10:** functionality as contractibility of every relation fiber. -/
abbrev def_3 := @DeepWiki.Refine.IsFun

/-- **Definition 4, p. 10:** a relation equipped with a coherent represented map. -/
abbrev def_4 := @DeepWiki.Refine.IsUmap

/-- **Lemma 4, p. 11:** functional relations and coherent represented maps are equivalent. -/
abbrev lemma_4 := @DeepWiki.Refine.isFunEquivIsUmap

/-- **Definition 7, p. 13:** the admissible pairs of universe-translation annotations. -/
abbrev def_7 := DeepWiki.Refine.AdmissibleUniverseTranslation

end DeepWiki.Ccm
