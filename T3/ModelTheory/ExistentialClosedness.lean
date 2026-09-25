/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ElementaryReflection
public import T3.ModelTheory.Inductive
public import T3.ModelTheory.FiniteDiagram

/-!
# Existentially closed models in arbitrary universes

Existential closedness can be tested using targets in the maximum of the source and language
universes. A Skolem hull containing the whole embedded source shows that this test reflects
existential formulas from targets in every universe. In the canonical universe it is exactly
the original predicate. For a Pi-two theory, the models of a model companion are precisely
the existentially closed models in every universe.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, item 4, line 277; no label.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, Fact 2.3, lines 289–295; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T T' : L.Theory}

/-- Existential closedness for a model in its own universe. Targets in the maximum of that
universe and the language universes suffice, as `reflects_of_model` proves.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, item 4, line 277; no label.
-/
def IsExistentiallyClosedAt (T : L.Theory) (M : Type w) [L.Structure M] : Prop :=
  Nonempty M ∧ M ⊨ T ∧
    ∀ (N : T.ModelType.{u, v, max u v w}) (f : M ↪[L] N)
      {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M),
      φ.IsExistential → φ.Realize (f ∘ x) → φ.Realize x

/-- In the canonical semantic universe the general predicate is the original one.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, item 4; no label.
-/
theorem isExistentiallyClosedAt_iff (M : Type (max u v)) [L.Structure M] :
    T.IsExistentiallyClosedAt M ↔ T.IsExistentiallyClosed M := Iff.rfl

/-- Existential formulas reflect from extension models in any universe. The elementary
Skolem hull contains the entire image of the source, without assuming that the source is small.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, item 4; no label.
-/
theorem IsExistentiallyClosedAt.reflects_of_model {M : Type w} [L.Structure M]
    (hM : T.IsExistentiallyClosedAt M) (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M)
    (hφ : φ.IsExistential) (hN : φ.Realize (f ∘ x)) : φ.Realize x := by
  classical
  let S := (Substructure.closure (L.sum L.skolem₁) (Set.range f)).elementarySkolem₁Reduct
  have : Small.{max u v w} S := by
    change Small.{max u v w} (Substructure.closure (L.sum L.skolem₁) (Set.range f))
    rw [← SetLike.coe_sort_coe, Substructure.coe_closure_eq_range_term_realize]
    have : Small.{max u v w} ((L.sum L.skolem₁).Term (Set.range f)) :=
      small_of_injective (Term.relabelEquiv (equivShrink.{max u v w} (Set.range f))).injective
    exact small_range _
  let S' : T.ModelType.{u, v, max u v w} := (ModelType.of T S).shrink
  let e : S ≃[L] S' := (equivShrink S).inducedStructureEquiv
  let fS : M ↪[L] S := f.codRestrict S.toSubstructure
    (fun a => Substructure.subset_closure (Set.mem_range_self a))
  have hS : φ.Realize (fS ∘ x) := (S.subtype.map_formula φ (fS ∘ x)).mp hN
  apply hM.2.2 S' (e.toEmbedding.comp fS) φ x hφ
  simpa only [Formula.Realize, Unique.eq_default (e ∘ default), Function.comp_def,
    Embedding.comp_apply, Equiv.coe_toEmbedding] using
    hφ.realize_embedding e.toEmbedding hS

/-- In any universe, a model of a model companion of a Pi-two theory models the original theory.
The two companion embeddings have elementary composite, which reflects the Pi-two axioms.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, Fact 2.3, lines 289–295; no label.
-/
theorem IsModelCompanionOf.models_of_isPiTwo_in_universe (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T'] :
    M ⊨ T := by
  obtain ⟨S, hS, hTS, hST⟩ := hT
  obtain ⟨N, ⟨f⟩⟩ := h.isCompanion.1.exists_embedding M
  obtain ⟨P, ⟨g⟩⟩ := h.isCompanion.2.exists_embedding N
  let e : M ↪ₑ[L] P := ⟨g.comp f, fun _ φ x =>
    IsModelComplete.realize_embedding_iff h.isModelComplete (g.comp f) φ x⟩
  have hM : M ⊨ S := S.model_iff.mpr fun φ hφ => by
    have hN : N ⊨ φ := (hTS φ hφ).realize_sentence N
    apply (hS φ hφ).realize_of_comp_elementary f g e rfl
    simpa only [Sentence.Realize, Formula.Realize, Unique.eq_default (f ∘ default)] using hN
  exact (model_iff_of_mutual_consequence hTS hST M).mpr hM

/-- A companion model which also models the original theory is existentially closed in
arbitrary universes. No Pi-two hypothesis is needed when the latter model assumption is given.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, items 3 and 4; no label.
-/
theorem IsModelCompanionOf.isExistentiallyClosedAt_of_models
    (h : T'.IsModelCompanionOf T) (M : Type w) [L.Structure M] [Nonempty M]
    [M ⊨ T'] [M ⊨ T] : T.IsExistentiallyClosedAt M := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro N f n φ x hφ hN
  obtain ⟨P, ⟨g⟩⟩ := h.isCompanion.2.exists_embedding N
  apply (IsModelComplete.realize_embedding_iff h.isModelComplete (g.comp f) φ x).mp
  simpa only [Formula.Realize, Unique.eq_default (g ∘ default), Function.comp_def,
    Embedding.comp_apply] using hφ.realize_embedding g hN

/-- For a Pi-two theory with a model companion, its existentially closed models in every
universe are precisely the models of the companion.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, Fact 2.3, lines 289–295; no label.
-/
theorem IsModelCompanionOf.models_iff_isExistentiallyClosedAt (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) (M : Type w) [L.Structure M] [Nonempty M] :
    M ⊨ T' ↔ T.IsExistentiallyClosedAt M := by
  constructor
  · intro hM
    let : M ⊨ T := h.models_of_isPiTwo_in_universe hT M
    exact h.isExistentiallyClosedAt_of_models M
  · intro hM
    let : M ⊨ T := hM.2.1
    obtain ⟨N, ⟨f⟩⟩ := h.isCompanion.2.exists_embedding M
    let : N ⊨ T := h.models_of_isPiTwo_in_universe hT N
    obtain ⟨e, _⟩ := IsModelComplete.exists_elementaryEmbedding_of_reflects_existential
      h.isModelComplete N f (fun φ x hφ hN => hM.reflects_of_model N f φ x hφ hN)
    exact (e.theory_model_iff T').mpr N.is_model

/-- Reflection applies to formulas indexed by any finite parameter type, independently of
the universes of the parameters, the original model, and the extension model.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, item 4; no label.
-/
theorem IsExistentiallyClosedAt.realize_of_finite {M : Type w} [L.Structure M]
    (hM : T.IsExistentiallyClosedAt M) (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) {α : Type*} [Finite α] (φ : L.Formula α) (a : α → M)
    (hφ : φ.IsExistential) (hN : φ.Realize (f ∘ a)) : φ.Realize a := by
  let := Fintype.ofFinite α
  let e := Fintype.equivFin α
  let ψ : L.Formula (Fin (Fintype.card α)) := φ.relabel e
  have hψ : ψ.IsExistential := hφ.relabel _
  have ha : (a ∘ e.symm) ∘ e = a :=
    funext fun i => congrArg a (e.symm_apply_apply i)
  have hfa : (f ∘ (a ∘ e.symm)) ∘ e = f ∘ a :=
    funext fun i => congrArg (fun j => f (a j)) (e.symm_apply_apply i)
  have hNψ : ψ.Realize (f ∘ (a ∘ e.symm)) := by
    change (φ.relabel e).Realize _
    rw [Formula.realize_relabel, hfa]
    exact hN
  have h := hM.reflects_of_model N f ψ (a ∘ e.symm) hψ hNψ
  change (φ.relabel e).Realize _ at h
  rwa [Formula.realize_relabel, ha] at h

/-- A finite structure in an extension has a copy in the existentially closed model fixing
a prescribed finite tuple. The finite structure itself need not model the theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2(6) and Proposition 4.13,
`proposition:bdd LCS`, final finite-diagram transfer.
-/
theorem IsExistentiallyClosedAt.exists_embedding_over_tuple [Finite L.Symbols]
    {M : Type w} [L.Structure M] (hM : T.IsExistentiallyClosedAt M)
    (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T] (f : M ↪[L] N)
    {A : Type*} [L.Structure A] [Finite A] {α : Type*} [Finite α]
    (a : α → A) (b : α → M) (g : A ↪[L] N) (hcompat : (g : A → N) ∘ a = f ∘ b) :
    ∃ h : A ↪[L] M, (h : A → M) ∘ a = b := by
  apply (realize_exists_embeddingExtensionDiagram_iff a b).mp
  apply hM.realize_of_finite N f _ b
  · exact (embeddingExtensionDiagram_isQF a).isExistential_iExs
  · exact (realize_exists_embeddingExtensionDiagram_iff a (f ∘ b)).mpr ⟨g, hcompat⟩

end FirstOrder.Language.Theory
