/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelCompleteness
public import Mathlib.ModelTheory.Skolem

/-!
# Model embeddings in arbitrary universes

Compactness transfers the model-embedding condition from the canonical semantic universe to
arbitrary nonempty models. Each finite part of the quantifier-free diagram lives in a small
Skolem hull, to which the original embedding hypothesis applies.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.2, item 1, line 180; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w x

namespace FirstOrder.Language

open Structure

variable {L : Language.{u, v}}

/-- Every finite parameter set is contained in an elementary substructure in the language's
canonical semantic universe, up to equivalence.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 1; no label.
-/
theorem exists_small_elementarySubstructure_containing_finset (M : Type w)
    [L.Structure M] [Nonempty M] (s : Finset M) :
    ∃ S : L.ElementarySubstructure M, (s : Set M) ⊆ S ∧ Small.{max u v} S := by
  let S := (Substructure.closure (L.sum L.skolem₁) (s : Set M)).elementarySkolem₁Reduct
  refine ⟨S, Substructure.subset_closure, ?_⟩
  change Small.{max u v} (Substructure.closure (L.sum L.skolem₁) (s : Set M))
  infer_instance

namespace Theory

variable {T T' : L.Theory}

/-- Every finite family of quantifier-free facts from an arbitrary model can be realized
simultaneously in a canonical-universe model of the target theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 1; no label.
-/
theorem ModelsEmbedInto.exists_finite_assignment (h : T.ModelsEmbedInto T')
    (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T]
    {ι : Type x} [Finite ι] (n : ι → ℕ) (φ : ∀ i, L.Formula (Fin (n i)))
    (a : ∀ i, Fin (n i) → M) (hφ : ∀ i, (φ i).IsQF)
    (ha : ∀ i, (φ i).Realize (a i)) :
    ∃ N : T'.ModelType.{u, v, max u v}, ∃ b : M → N,
      ∀ i, (φ i).Realize (b ∘ a i) := by
  classical
  letI := Fintype.ofFinite ι
  let s : Finset M := Finset.univ.biUnion fun i => Finset.univ.image (a i)
  obtain ⟨S, hs, hsmall⟩ := exists_small_elementarySubstructure_containing_finset (L := L) M s
  letI := hsmall
  let S' : T.ModelType.{u, v, max u v} := (ModelType.of T S).shrink
  let e : S ≃[L] S' := (equivShrink S).inducedStructureEquiv
  obtain ⟨N, ⟨f⟩⟩ := h S'
  let b : M → N := Function.extend (Subtype.val : S → M) (f ∘ e)
    (fun _ => Classical.choice (inferInstance : Nonempty N))
  have hmem (i : ι) (j : Fin (n i)) : a i j ∈ S := by
    apply hs
    simp only [s, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
      true_and]
    exact ⟨i, j, rfl⟩
  refine ⟨N, b, fun i => ?_⟩
  let a' : Fin (n i) → S := fun j => ⟨a i j, hmem i j⟩
  have ha' : (φ i).Realize a' := (S.subtype.map_formula (φ i) a').mp (ha i)
  have hb : b ∘ a i = f ∘ e ∘ a' := by
    funext j
    simpa only [b, a', Function.comp_def] using
      Subtype.val_injective.extend_apply (f ∘ e)
        (fun _ => Classical.choice (inferInstance : Nonempty N)) (a' j)
  rw [hb]
  simpa only [Formula.Realize, Unique.eq_default (f.comp e.toEmbedding ∘ default),
    Function.comp_def, Embedding.comp_apply, Equiv.coe_toEmbedding] using
    (hφ i).isExistential.realize_embedding (f.comp e.toEmbedding) ha'

/-- A model in any universe embeds into a model of the target theory when the embedding
condition holds in the canonical semantic universe. The target lies in the maximum of the
language and source universes.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 1, line 180; no label.
-/
theorem ModelsEmbedInto.exists_embedding (h : T.ModelsEmbedInto T')
    (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T] :
    ∃ N : T'.ModelType.{u, v, max u v w}, Nonempty (M ↪[L] N) := by
  classical
  have hsat : ((L.lhomWithConstants M).onTheory T' ∪ L.qfDiagram M).IsSatisfiable := by
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro Θ hΘ
    have hdata : ∀ θ : {θ : L[[M]].Sentence // θ ∈ Θ.filter (· ∈ L.qfDiagram M)},
        ∃ (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
          φ.IsQF ∧ φ.Realize a ∧ (θ : L[[M]].Sentence) =
            Formula.equivSentence (φ.relabel a) :=
      fun θ => (Finset.mem_filter.mp θ.2).2
    choose n φ a hφ ha heq using hdata
    obtain ⟨N, b, hb⟩ := h.exists_finite_assignment M n φ a hφ ha
    letI : (constantsOn M).Structure N := constantsOn.structure b
    haveI : N ⊨ (Θ : L[[M]].Theory) := by
      rw [model_iff]
      intro θ hθ
      rcases hΘ hθ with hT' | hdiag
      · have hN : N ⊨ (L.lhomWithConstants M).onTheory T' :=
          (LHom.onTheory_model _ _).mpr N.is_model
        exact hN.realize_of_mem θ hT'
      · have hθ' : θ ∈ Θ.filter (· ∈ L.qfDiagram M) :=
          Finset.mem_filter.mpr ⟨hθ, hdiag⟩
        have heq' : θ = Formula.equivSentence
            ((φ ⟨θ, hθ'⟩).relabel (a ⟨θ, hθ'⟩)) := heq ⟨θ, hθ'⟩
        rw [heq', realize_equivSentence_relabel]
        exact hb ⟨θ, hθ'⟩
    exact Model.isSatisfiable N
  obtain ⟨N⟩ := hsat
  letI : L.Structure N := (L.lhomWithConstants M).reduct N
  haveI : N ⊨ T' := (LHom.onTheory_model _ _).mp
    (N.is_model.mono Set.subset_union_left)
  haveI : N ⊨ L.qfDiagram M := N.is_model.mono Set.subset_union_right
  exact ⟨ModelType.of T' N, ⟨Embedding.ofModelsQfDiagram L M N⟩⟩

end Theory

end FirstOrder.Language
