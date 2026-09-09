/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelEmbeddings
public import T3.ModelTheory.LocallyFinite

/-!
# Local finiteness in arbitrary universes

A small elementary hull containing a finite parameter set allows local finiteness to pass
from the canonical semantic universe to every nonempty model of the theory.

Paper-ID: model_theory.local_finiteness
TeX: T3_modelcompanion_v4.tex, Definition 2.4, lines 203–206; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' x

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T : L.Theory}

/-- Local finiteness in the canonical semantic universe implies that finite parameter sets
generate finite substructures in every nonempty model, without a cardinality hypothesis.

Paper-ID: model_theory.local_finiteness
TeX: T3_modelcompanion_v4.tex, Definition 2.4, lines 203–206; no label.
-/
theorem IsLocallyFinite.finite_closure (hT : T.IsLocallyFinite) (M : Type w)
    [L.Structure M] [Nonempty M] [M ⊨ T] (s : Set M) (hs : s.Finite) :
    Finite (Substructure.closure L s) := by
  classical
  obtain ⟨S, hS, hsmall⟩ :=
    exists_small_elementarySubstructure_containing_finset (L := L) M hs.toFinset
  letI := hsmall
  let N : T.ModelType.{u, v, max u v} := (ModelType.of T S).shrink
  let e : S ≃[L] N := (equivShrink S).inducedStructureEquiv
  let j : N ↪[L] M := S.subtype.toEmbedding.comp e.symm.toEmbedding
  have hsrange : s ⊆ Set.range j := by
    intro a ha
    let a' : S := ⟨a, hS (hs.mem_toFinset.mpr ha)⟩
    exact ⟨e a', by simp [j, a', Embedding.comp_apply, Equiv.coe_toEmbedding]⟩
  let t : Set N := j ⁻¹' s
  have ht : t.Finite := hs.preimage j.injective.injOn
  have himage : j '' t = s := Set.image_preimage_eq_of_subset hsrange
  letI := hT N t ht
  have hfinite : Set.Finite (Substructure.closure L s : Set M) := by
    rw [← himage, ← Embedding.coe_toHom (f := j), Substructure.closure_image j.toHom]
    exact (Set.toFinite (Substructure.closure L t : Set N)).image j
  exact hfinite.to_subtype

/-- A finite tuple in an arbitrary model of a locally finite theory has a finite
quantifier-free diagram basis. Its equivalence is valid in arbitrary target structures.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 192–193; no label.
-/
theorem IsLocallyFinite.exists_finite_tupleQfDiagram_of_model [Finite L.Symbols]
    (hT : T.IsLocallyFinite) (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T]
    {α : Type x} [Finite α] (a : α → M) :
    ∃ Δ : Finset (L.Formula α), (Δ : Set (L.Formula α)) ⊆ tupleQfDiagram (L := L) a ∧
      ∀ (N : Type w') [L.Structure N] (b : α → N),
        (∀ φ ∈ Δ, φ.Realize b) ↔ ∀ φ ∈ tupleQfDiagram (L := L) a, φ.Realize b := by
  classical
  letI := hT.finite_closure M (Set.range a) (Set.finite_range a)
  refine ⟨{finiteGeneratedDiagram (L := L) a}, ?_, ?_⟩
  · intro φ hφ
    obtain rfl := Finset.mem_singleton.mp hφ
    exact finiteGeneratedDiagram_mem_tupleQfDiagram a
  · intro N _ b
    simpa only [Finset.mem_singleton, forall_eq] using
      realize_finiteGeneratedDiagram_iff_tupleQfDiagram a b

end FirstOrder.Language.Theory
