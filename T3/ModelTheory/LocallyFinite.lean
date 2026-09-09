/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.FiniteDiagram

/-!
# Locally finite theories and finite tuple diagrams

Local finiteness means that every finite set in a model generates a finite substructure.
As in the companion and existential-closedness definitions, models in this predicate use
the canonical semantic universe `max u v`. The finite-diagram conclusion itself holds in
target structures of arbitrary universes.

For a finite language, `IsLocallyFinite.exists_finite_tupleQfDiagram` represents the full
quantifier-free diagram of a finite tuple by a finite subset of that diagram. The proof
uses the actual finite generated substructure and its function and relation tables.
It makes no assertion that the full syntactic diagram is finite.

Paper-ID: model_theory.local_finiteness
TeX: T3_modelcompanion_v4.tex, Definition 2.4, lines 203–206; no label.
The finite-diagram consequence is Definition 2.2, item 6, lines 192–193.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} (T : L.Theory)

/-- A theory is locally finite if every finite subset of each of its models generates a
finite substructure. Models here lie in the canonical semantic universe `max u v`.

Paper-ID: model_theory.local_finiteness
TeX: T3_modelcompanion_v4.tex, Definition 2.4, lines 203–206; no label.
-/
def IsLocallyFinite : Prop :=
  ∀ (M : T.ModelType.{u, v, max u v}) (s : Set M),
    s.Finite → Finite (Substructure.closure L s)

variable {T}

/-- A finite tuple in a model of a locally finite theory generates a finite substructure.

Paper-ID: model_theory.local_finiteness
TeX: T3_modelcompanion_v4.tex, Definition 2.4; no label.
-/
theorem IsLocallyFinite.finite_closure_range (hT : T.IsLocallyFinite)
    (M : T.ModelType.{u, v, max u v}) {α : Type w} [Finite α] (a : α → M) :
    Finite (Substructure.closure L (Set.range a)) :=
  hT M _ (Set.finite_range a)

/-- In a finite language and a locally finite theory, the full quantifier-free diagram of
a finite tuple is equivalent to a finite subset. The equivalence holds in every target
structure, so in particular it holds modulo the theory. This does not claim that the set
of all true quantifier-free formulas is itself finite.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 192–193; no label.
-/
theorem IsLocallyFinite.exists_finite_tupleQfDiagram [Finite L.Symbols]
    (hT : T.IsLocallyFinite) (M : T.ModelType.{u, v, max u v})
    {α : Type w} [Finite α] (a : α → M) :
    ∃ Δ : Finset (L.Formula α), (Δ : Set (L.Formula α)) ⊆ tupleQfDiagram (L := L) a ∧
      ∀ (N : Type w') [L.Structure N] (b : α → N),
        (∀ φ ∈ Δ, φ.Realize b) ↔ ∀ φ ∈ tupleQfDiagram (L := L) a, φ.Realize b := by
  classical
  letI := hT.finite_closure_range M a
  refine ⟨{finiteGeneratedDiagram (L := L) a}, ?_, ?_⟩
  · intro φ hφ
    obtain rfl := Finset.mem_singleton.mp hφ
    exact finiteGeneratedDiagram_mem_tupleQfDiagram a
  · intro N _ b
    simpa only [Finset.mem_singleton, forall_eq] using
      realize_finiteGeneratedDiagram_iff_tupleQfDiagram a b

end FirstOrder.Language.Theory
