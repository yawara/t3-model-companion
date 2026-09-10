/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelCompleteness

/-!
# Pi-two theories and existentially closed models of model companions

`FirstOrder.Language.Theory.IsPiTwo` follows Definition 2.2(5): the theory admits an equivalent
axiomatization by universal-existential sentences. It does not require the given axioms to have
that syntactic form. Equivalence is expressed using mathlib's semantic consequence, which also
gives equivalence on nonempty models in arbitrary universes.

For a Pi-two theory with a model companion, the models of the companion are exactly the
existentially closed models of the original theory. This proves the model-companion-to-model-class
implication of Fact 2.3. The reverse implication is not asserted here. As in
`T3.ModelTheory.ModelCompanion`, companions and existentially closed models use the canonical
semantic universe.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.2, item 5, line 184; no label.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.3, lines 195–201; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' w'' u'

namespace FirstOrder.Language

variable {L : Language.{u, v}}

namespace BoundedFormula

variable {α : Type u'} {n : ℕ}

/-- A universal-existential formula consists of a finite universal prefix followed by an
existential formula, whose matrix is quantifier free. Either prefix may be empty.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 5, line 184; no label.
-/
inductive IsUniversalExistential : ∀ {n}, L.BoundedFormula α n → Prop
  /-- An existential formula has an empty universal prefix. -/
  | of_isExistential {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsExistential) :
      IsUniversalExistential φ
  /-- Adding a universal quantifier preserves a universal-existential prefix. -/
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversalExistential φ) :
      IsUniversalExistential φ.all

/-- A universal formula is universal-existential, with an empty existential prefix.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 5; no label.
-/
theorem IsUniversal.isUniversalExistential {φ : L.BoundedFormula α n} (h : φ.IsUniversal) :
    φ.IsUniversalExistential := by
  induction h with
  | of_isQF h => exact .of_isExistential h.isExistential
  | all _ ih => exact .all ih

/-- If two embeddings compose to an elementary embedding, universal-existential formulas true
in the intermediate structure reflect to the source on source parameters.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem IsUniversalExistential.realize_of_comp_elementary
    {M : Type w} {N : Type w'} {P : Type w''}
    [L.Structure M] [L.Structure N] [L.Structure P]
    (f : M ↪[L] N) (g : N ↪[L] P) (e : M ↪ₑ[L] P)
    (he : e.toEmbedding = g.comp f) {φ : L.BoundedFormula α n}
    (hφ : φ.IsUniversalExistential) {x : α → M} {xs : Fin n → M}
    (hN : φ.Realize (f ∘ x) (f ∘ xs)) : φ.Realize x xs := by
  have heval (a : M) : e a = g (f a) := by
    have h := congrArg (fun k : M ↪[L] P => k a) he
    exact h
  induction hφ with
  | of_isExistential hφ =>
    apply (e.map_boundedFormula _ x xs).mp
    simpa only [Function.comp_def, heval] using hφ.realize_embedding g hN
  | all _ ih =>
    rw [realize_all] at hN ⊢
    intro a
    apply ih
    rw [Fin.comp_snoc]
    exact hN (f a)

end BoundedFormula

namespace Theory

variable {T T' : L.Theory}

/-- A Pi-two theory admits an equivalent axiomatization by universal-existential sentences.
The two consequence conditions express equivalence of theories, not equality of axiom sets.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.2, item 5, line 184; no label.
-/
def IsPiTwo (T : L.Theory) : Prop :=
  ∃ S : L.Theory, (∀ φ ∈ S, φ.IsUniversalExistential) ∧
    (∀ φ ∈ S, T ⊨ᵇ φ) ∧ (∀ φ ∈ T, S ⊨ᵇ φ)

/-- Mutual consequence gives equivalence of model classes in any universe.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 5; no label.
-/
theorem model_iff_of_mutual_consequence
    (hTT' : ∀ φ ∈ T', T ⊨ᵇ φ) (hT'T : ∀ φ ∈ T, T' ⊨ᵇ φ)
    (M : Type w) [L.Structure M] [Nonempty M] : M ⊨ T ↔ M ⊨ T' := by
  constructor
  · intro hM
    exact T'.model_iff.mpr fun φ hφ => (hTT' φ hφ).realize_sentence M
  · intro hM
    exact T.model_iff.mpr fun φ hφ => (hT'T φ hφ).realize_sentence M

/-- A theory already axiomatized by universal-existential sentences is Pi-two.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 5; no label.
-/
theorem isPiTwo_of_forall_isUniversalExistential
    (h : ∀ φ ∈ T, φ.IsUniversalExistential) : T.IsPiTwo :=
  ⟨T, h, fun _ hφ => models_sentence_of_mem hφ, fun _ hφ => models_sentence_of_mem hφ⟩

/-- Every universal theory is Pi-two. The definition of Pi-two also permits equivalent
axiomatizations and genuine existential witnesses.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 5; no label.
-/
theorem IsUniversal.isPiTwo [h : T.IsUniversal] : T.IsPiTwo :=
  isPiTwo_of_forall_isUniversalExistential fun _ hφ =>
    (h.isUniversal_of_mem hφ).isUniversalExistential

/-- For a Pi-two theory, every model of its model companion satisfies the original theory.
Embed it into a model of the original theory and then back into a model of the companion;
model completeness makes the composite elementary and reflects the Pi-two axioms.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, part of Fact 2.3, lines 195–201; no label.
-/
theorem IsModelCompanionOf.models_of_isPiTwo (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) (M : T'.ModelType.{u, v, max u v}) : M ⊨ T := by
  obtain ⟨S, hS, hTS, hST⟩ := hT
  obtain ⟨N, ⟨f⟩⟩ := h.isCompanion.1 M
  obtain ⟨P, ⟨g⟩⟩ := h.isCompanion.2 N
  obtain ⟨e, he⟩ := IsModelComplete.allEmbeddingsElementary h.isModelComplete M P (g.comp f)
  have hM : M ⊨ S := S.model_iff.mpr fun φ hφ => by
    have hN : N ⊨ φ := (hTS φ hφ).realize_sentence N
    apply (hS φ hφ).realize_of_comp_elementary f g e he
    simpa only [Sentence.Realize, Formula.Realize, Unique.eq_default (f ∘ default)] using hN
  exact (model_iff_of_mutual_consequence hTS hST M).mpr hM

/-- Every model of a model companion of a Pi-two theory is existentially closed for that theory.
This is the companion-model inclusion in the equality of classes of Fact 2.3.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, one inclusion in Fact 2.3, lines 195–201; no label.
-/
theorem IsModelCompanionOf.isExistentiallyClosed_of_isPiTwo (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) (M : T'.ModelType.{u, v, max u v}) :
    T.IsExistentiallyClosed M := by
  let : M ⊨ T := h.models_of_isPiTwo hT M
  exact h.isExistentiallyClosed_of_models M

/-- An existentially closed model of a Pi-two theory satisfies every axiom of its model
companion. Its embedding into a companion model reflects existential formulas and is elementary
by the Tarski-Vaught criterion for a model-complete target.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, converse class inclusion in Fact 2.3, lines 195–201; no label.
-/
theorem IsExistentiallyClosed.models_of_isModelCompanionOf (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) {M : Type (max u v)} [L.Structure M]
    (hM : T.IsExistentiallyClosed M) : M ⊨ T' := by
  let : Nonempty M := hM.1
  let : M ⊨ T := hM.2.1
  obtain ⟨N, ⟨f⟩⟩ := h.isCompanion.2 (ModelType.of T M)
  let : N ⊨ T := h.models_of_isPiTwo hT N
  obtain ⟨e, _⟩ := IsModelComplete.exists_elementaryEmbedding_of_existential_reflection
    h.isModelComplete N f (fun φ a hφ hN => hM.2.2 (ModelType.of T N) f φ a hφ hN)
  exact (e.theory_model_iff T').mpr N.is_model

/-- For a Pi-two theory with a model companion, the nonempty models of that companion are
exactly the existentially closed models of the original theory. This proves the forward
implication of Fact 2.3, in the canonical semantic universe.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, forward implication of Fact 2.3, lines 195–201; no label.
-/
theorem IsModelCompanionOf.models_iff_isExistentiallyClosed (hT : T.IsPiTwo)
    (h : T'.IsModelCompanionOf T) (M : Type (max u v)) [L.Structure M] [Nonempty M] :
    M ⊨ T' ↔ T.IsExistentiallyClosed M := by
  constructor
  · intro hM
    exact h.isExistentiallyClosed_of_isPiTwo hT (ModelType.of T' M)
  · exact IsExistentiallyClosed.models_of_isModelCompanionOf hT h

end Theory

end FirstOrder.Language
