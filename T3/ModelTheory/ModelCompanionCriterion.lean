/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ExistentiallyClosedExtension
public import T3.ModelTheory.RobinsonTest

/-!
# Model companions and existentially closed models

For an arbitrary Pi-two theory, a theory is its model companion if and only if it axiomatizes
its existentially closed models. The forward implication is proved in `Inductive`. For the
reverse implication, existentially closed extensions supply the necessary embeddings, and
Robinson's test supplies syntactic model completeness.

This is Fact 2.3 with the repository's explicit canonical semantic universe `Type (max u v)`.
No finite-language, local-finiteness, or universality assumption is imposed.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, Fact 2.3, lines 195–201; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T Tstar : L.Theory}

/-- A theory axiomatizing the existentially closed models of a Pi-two theory is a model
companion of that theory. In particular, model completeness has its syntactic meaning from
Definition 2.2(2).

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, reverse implication of Fact 2.3, lines 195–201; no label.
-/
theorem isModelCompanionOf_of_isExistentiallyClosed_iff (hT : T.IsPiTwo)
    (h₁ : ∀ M : Tstar.ModelType.{u, v, max u v}, T.IsExistentiallyClosed M)
    (h₂ : ∀ M : T.ModelType.{u, v, max u v}, T.IsExistentiallyClosed M → M ⊨ Tstar) :
    Tstar.IsModelCompanionOf T := by
  have hcomp : Tstar.IsCompanion T := by
    constructor
    · intro M
      letI : M ⊨ T := (h₁ M).2.1
      exact ⟨ModelType.of T M, ⟨Embedding.refl L M⟩⟩
    · exact modelsEmbedInto_of_isExistentiallyClosed_models hT h₂
  refine ⟨hcomp, isModelComplete_of_isExistentiallyClosedInModels ?_⟩
  intro M N f n φ x hφ hN
  letI : N ⊨ T := (h₁ N).2.1
  exact (h₁ M).2.2 (ModelType.of T N) f φ x hφ hN

/-- **Fact 2.3.** For a Pi-two theory, model companionship is equivalent to equality of the
companion's model class and the class of existentially closed models of the original theory.
The model-class quantifiers range over nonempty structures in the canonical semantic universe.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, Fact 2.3, lines 195–201; no label.
-/
theorem isModelCompanionOf_iff_models_iff_isExistentiallyClosed (hT : T.IsPiTwo) :
    Tstar.IsModelCompanionOf T ↔
      ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M],
        M ⊨ Tstar ↔ T.IsExistentiallyClosed M := by
  constructor
  · intro h M _ _
    exact h.models_iff_isExistentiallyClosed hT M
  · intro h
    exact isModelCompanionOf_of_isExistentiallyClosed_iff hT
      (fun M => (h M).mp M.is_model) (fun M hM => (h M).mpr hM)

end FirstOrder.Language.Theory
