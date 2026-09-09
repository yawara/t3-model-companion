/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Identities
public import T3.GroupTheory.AssociatedGraded
public import T3.GroupTheory.AssociatedGraded.Lie
public import T3.GroupTheory.AssociatedGraded.Generation
public import T3.GroupTheory.AssociatedGraded.Product
public import T3.GroupTheory.CentralSeries
public import T3.GroupTheory.ConjugateWidth
public import T3.GroupTheory.Coproduct.Basic
public import T3.GroupTheory.Coproduct.Graded
public import T3.GroupTheory.Coproduct.GradedEquiv
public import T3.GroupTheory.Coproduct.BlockBracket
public import T3.GroupTheory.Coproduct.Strict
public import T3.GroupTheory.Coproduct.CentralSeries
public import T3.GroupTheory.Coproduct.Presentation
public import T3.GroupTheory.Coproduct.Relations
public import T3.GroupTheory.Free.Examples
public import T3.GroupTheory.Free.ExteriorLie
public import T3.GroupTheory.Free.ExteriorNaturality
public import T3.GroupTheory.Free.Graded
public import T3.GroupTheory.Free.InfiniteNormalForm
public import T3.GroupTheory.Free.NormalForm
public import T3.GroupTheory.GradedNormalClosure
public import T3.GroupTheory.GradedQuotient
public import T3.GroupTheory.GeneratorRank
public import T3.GroupTheory.Presentation
public import T3.GroupTheory.Roots.Commutator
public import T3.GroupTheory.Roots.CommutatorRelations
public import T3.GroupTheory.Roots.Triple
public import T3.GroupTheory.Support
public import T3.LinearAlgebra.BlockDecomposition
public import T3.LinearAlgebra.ExteriorSum
public import T3.LinearAlgebra.ExteriorTensor
public import T3.LinearAlgebra.ExteriorLowDegree
public import T3.LinearAlgebra.TruncatedExterior
public import T3.ModelTheory.Inductive
public import T3.ModelTheory.LocallyFinite
public import T3.ModelTheory.ModelCompanion
public import T3.ModelTheory.ModelCompanionCriterion
public import T3.ModelTheory.ModelCompleteness
public import T3.ModelTheory.UniformLocalFiniteness
public import T3.ModelTheory.BoundedAmalgamationCriterion
public import T3.ModelTheory.ExponentThree
public import T3.ModelTheory.ExistentiallyClosedGroups

/-!
# Guide to the paper

This library follows *Existence of a Model Companion for Groups of Exponent 3*,
by Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi, in `T3_modelcompanion_v4.tex`.

The source revision and the status of each paper item are recorded in
`docs/paper-map.toml`; `docs/paper-map.md` is its generated reading index.
Declarations carry a `Paper-ID` and, when available, the original TeX label.

## Section 2: Preliminaries

* `T3.GroupTheory.Basic`: the exponent-three condition, including the trivial group.
* `T3.GroupTheory.Identities`: elementary group identities from Fact 2.15,
  `fact:elementary equations`.
* `T3.GroupTheory.Free.Examples`: the noncommutative second center in Fact 2.15(3).
* `T3.GroupTheory.Free.Basic`: the free exponent-three group and its universal property.
* `T3.GroupTheory.Free.NormalForm`: the finite normal form and exact order in Fact 2.27,
  `fact:Levi and van der Waerden`; the function `T3.freeOrderExponent` is defined here.
* `T3.GroupTheory.Free.InfiniteNormalForm`: the unique finitely supported normal word
  in arbitrary rank, Remark 2.28, `remark:infinite dim`.
* `T3.GroupTheory.CentralSeries`: general central-series properties and the strictness
  consequence of internal coincidence, Definitions 2.12, 2.23, 2.25 and Lemma 2.26.
* `T3.GroupTheory.AssociatedGraded`: the degree quotients, their vector spaces and maps,
  and ambient graded images.
* `T3.GroupTheory.AssociatedGraded.Lie`: the commutator bracket, graded Lie structure,
  triple identities and induced Lie maps, including Proposition 2.24.
* `T3.GroupTheory.AssociatedGraded.Generation`: generation by the degree-one component,
  as asserted in Lemma 2.19(3).
* `T3.GroupTheory.AssociatedGraded.Product`: the lower central terms and canonical layer
  equivalences for direct products, Example 2.21(2).
* `T3.LinearAlgebra.TruncatedExterior`: the actual exterior powers, signed bracket and
  graded Lie algebra in Example 2.9, without dimension assumptions.
* `T3.LinearAlgebra.BlockDecomposition`: block homogeneity and the canonical direct sum of
  block quotients in Definition 2.10 and Proposition 2.11, with arbitrary index sets.
* `T3.GroupTheory.Free.Graded`: the actual degree quotients of the free group identified
  with finitely supported coordinates in arbitrary rank.
* `T3.GroupTheory.Free.ExteriorLie`: the paper's maps `σ₁`, `σ₂`, and `σ₃`, assembled into
  the graded Lie isomorphism of Proposition 2.29 and Remark 2.30 in arbitrary rank.
* `T3.GroupTheory.GradedQuotient`: the natural quotient-layer isomorphism of Lemma 2.31.
* `T3.GroupTheory.Coproduct.Basic`: coproducts, free groups on disjoint unions, and factor
  embeddings, as in Notation 2.1(8), Fact 2.16, and Lemma 2.17.
* `T3.ModelTheory.ModelCompanion`: companion, syntactic model completeness, and
  existential closedness from Definition 2.2(1–4).
* `T3.ModelTheory.Inductive`: the Pi-two condition in Definition 2.2(5) and equality of the
  model-companion class with the original theory's existentially closed models.
* `T3.ModelTheory.ModelCompanionCriterion`: both directions of Fact 2.3 for general Pi-two
  theories, using existentially closed extensions and the syntactic Robinson test.
* `T3.ModelTheory.ModelCompleteness`: the equivalence of syntactic model completeness with
  elementary preservation by embeddings, proved using finite diagrams and compactness.
* `T3.ModelTheory.FiniteDiagram`: finite function and relation tables, tuple diagrams,
  and existentially closed transfer fixing a finite common substructure.
* `T3.ModelTheory.LocallyFinite`: local finiteness and the representation of a full tuple's
  quantifier-free diagram by a finite conjunction in a finite language.
* `T3.ModelTheory.UniformLocalFiniteness`: the uniform bound of Fact 2.5 and finitely many
  quantifier-free formulas up to theory equivalence, completing Definition 2.2(6).
* `T3.ModelTheory.BoundedAmalgamationCriterion`: both directions of Fact 2.6 in a finite
  language, with Pi-two and local-finiteness hypotheses. The obstruction bound counts all
  generators, and the finite structures need not themselves be models of the theory.
* `T3.ModelTheory.ExponentThree`: the actual group language and theory `T₃`, its Pi-two
  axiomatization and local finiteness, including the trivial group.

The index records exactly which parts have been proved and checked against the paper.
The companion, existential-closedness and local-finiteness predicates use the documented
canonical semantic universe; bridges to arbitrary model universes remain separate work.
The group-theoretic bound needed to apply the criterion to `T₃` is not yet proved.

## Section 3: Main results

`T3.GroupTheory.ConjugateWidth` proves Proposition 3.1: every element of a principal normal
closure is a product of at most three positive conjugates, including the trivial case.
`T3.GroupTheory.Support` proves Lemma 3.2 with the generator bound `3(m+1)n` and a certificate
inside the actual subgroup `H₀ = ⟨C,B,Δ⟩`. Proposition A, the bounded-witness theorem, and the
model-companion corollary are planned.

## Section 4: Structural analysis

* `T3.GroupTheory.Presentation`: Proposition 4.1 for any specified basis and representatives.
  The two group-generation inclusions are in `T3.GroupTheory.Generation`.
* `T3.GroupTheory.GradedNormalClosure`: all three statements of Lemma 4.2 for an arbitrary
  subgroup of the derived subgroup, including nonhomogeneous relations.
* `T3.GroupTheory.Roots.Triple`: the concrete simultaneous quotient construction and base
  embedding of Lemma 4.8 using `G × Free (Fin (3 * n))`.
* `T3.LinearAlgebra.ExteriorSum`: direct decomposition into exterior-basis blocks, supporting
  the proof of Proposition 4.3.
* `T3.LinearAlgebra.ExteriorTensor`: exterior powers of a direct sum as complementary tensor
  powers, with inverse given by the actual ordered exterior product, in arbitrary rank.
* `T3.GroupTheory.Free.ExteriorNaturality`: the free factor maps agree with the standard
  exterior-power inclusions in degrees one, two, and three.
* `T3.GroupTheory.Coproduct.Presentation`: the canonical free quotient presentation of the
  coproduct and componentwise intersections of its factor relations with the central terms.
* `T3.GroupTheory.Coproduct.Relations`: the graded relation images and absorption of pure
  commutator relations, as used in the proof of Proposition 4.3.
* `T3.GroupTheory.Coproduct.Graded`: the canonical degree-one isomorphism and degree-two/three
  maps, including their tensor formulas and naturality.
* `T3.GroupTheory.Coproduct.GradedEquiv`: the actual degree-two/three isomorphisms, obtained
  from free presentations, the signed exterior decomposition, and quotient kernel transport.
  All groups and free ranks are arbitrary.
* `T3.GroupTheory.Coproduct.BlockBracket`: the paper's block bracket inclusions and the
  signed mixed bracket formulas, completing Proposition 4.3.
* `T3.GroupTheory.Coproduct.Strict`: preservation of injectivity by coproduct along a strict
  inclusion, Lemma 4.4, using the natural graded isomorphisms.
* `T3.GroupTheory.Coproduct.CentralSeries`: Lemma 4.5 for arbitrary nontrivial `G` and `F₂`.
  The two graded separation claims follow the paper's component calculations.
* `T3.GroupTheory.Roots.Commutator`: the simultaneous quotient by all commutator-root relations,
  with injective base map and root equations, Lemma 4.6. The proof follows Claims A, B, and C.
* `T3.GroupTheory.GeneratorRank`: the first two graded dimensions are bounded by the number
  of generators and its second binomial coefficient, for the proofs of Lemmas 4.7 and 4.9.
  Finite dimensionality is proved; the strictification constructions remain unfinished.
* `T3.ModelTheory.ExistentiallyClosedGroups`: all three conclusions of Proposition 4.11.
  Finite diagrams transfer witnesses from the concrete root quotients and free-two coproduct,
  preserving all designated parameters. Nontriviality follows from existential closedness.

Strictification and Proposition 4.12 remain to be implemented before the main results.
-/
