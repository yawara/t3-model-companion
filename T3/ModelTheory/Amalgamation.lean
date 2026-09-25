/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.FiniteDiagram

/-!
# Amalgamation in a theory

Two structures over a common base amalgamate in `T` when they embed compatibly into a model
of `T`. The structures and base need not themselves satisfy `T`, and may be empty. No condition
on the intersection of the two images is imposed. The target models use the canonical semantic
universe from the model-companion definitions; the three input universes are arbitrary.

For an existentially closed model, amalgamability with a finite extension of a finite base is
equivalent to the existence of a copy of that extension over the base inside the model. The
finite-diagram API expresses this by a single existential formula.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 314–356.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' w'' w'''

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- The existential formula asserting an embedding of a finite structure extending a given
assignment of finitely many parameters.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, line 325.
-/
noncomputable def extensionFormula [Finite L.Symbols] {A : Type w} [Finite A]
    {B : Type w'} [L.Structure B] [Finite B] (i : A → B) : L.Formula A :=
  (embeddingExtensionDiagram (L := L) i).iExs B

/-- The finite extension formula is existential, with the finite diagram as its matrix.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 325–328.
-/
theorem extensionFormula_isExistential [Finite L.Symbols] {A : Type w} [Finite A]
    {B : Type w'} [L.Structure B] [Finite B] (i : A → B) :
    (extensionFormula (L := L) i).IsExistential :=
  (embeddingExtensionDiagram_isQF i).isExistential_iExs

/-- A realization of the finite extension formula is exactly an embedding over the given
parameter assignment. No model assumption is made on the finite structure.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, line 325.
-/
theorem realize_extensionFormula_iff [Finite L.Symbols] {A : Type w} [Finite A]
    {B : Type w'} [L.Structure B] [Finite B] (i : A → B)
    {N : Type w''} [L.Structure N] (a : A → N) :
    (extensionFormula (L := L) i).Realize a ↔ ∃ f : B ↪[L] N, f ∘ i = a :=
  realize_exists_embeddingExtensionDiagram_iff i a

namespace Theory

/-- A structure embeds into a nonempty model of the theory in the canonical semantic universe.
The structure itself may be empty and need not satisfy the theory.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 314, 332.
-/
def Embeddable (T : L.Theory) (C : Type w) [L.Structure C] : Prop :=
  ∃ N : T.ModelType.{u, v, max u v}, Nonempty (C ↪[L] N)

/-- An amalgam over the base is a pair of embeddings into one model of the theory which agree
on the base. There is no restriction on the intersection of their images.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 316–319.
-/
def AmalgamableOver (T : L.Theory)
    {A : Type w} {B : Type w'} {C : Type w''}
    [L.Structure A] [L.Structure B] [L.Structure C] (i : A ↪[L] B) (j : A ↪[L] C) : Prop :=
  ∃ (N : T.ModelType.{u, v, max u v}) (f : B ↪[L] N) (g : C ↪[L] N), f.comp i = g.comp j

variable {T : L.Theory} {A : Type w} {B : Type w'} {C : Type w''} {D : Type w'''}
  [L.Structure A] [L.Structure B] [L.Structure C] [L.Structure D]

/-- Amalgamation is symmetric in the two extensions.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, amalgamation over A.
-/
theorem AmalgamableOver.symm {i : A ↪[L] B} {j : A ↪[L] C}
    (h : T.AmalgamableOver i j) : T.AmalgamableOver j i := by
  obtain ⟨N, f, g, heq⟩ := h
  exact ⟨N, g, f, heq.symm⟩

/-- Restricting an amalgam along an embedding on its right side gives an amalgam.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 354–356.
-/
theorem AmalgamableOver.of_comp_right {i : A ↪[L] B} {j : A ↪[L] C}
    (e : C ↪[L] D) (h : T.AmalgamableOver i (e.comp j)) : T.AmalgamableOver i j := by
  obtain ⟨N, f, g, heq⟩ := h
  exact ⟨N, f, g.comp e, heq⟩

/-- For an existentially closed model, amalgamation with a finite extension is equivalent to
an embedding of that extension back into the model over the finite base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 332, 341.
-/
theorem IsExistentiallyClosed.amalgamableOver_iff_exists_embedding [Finite L.Symbols]
    [Finite A] [Finite B] {M : Type (max u v)} [L.Structure M]
    (hM : T.IsExistentiallyClosed M) (i : A ↪[L] B) (j : A ↪[L] M) :
    T.AmalgamableOver i j ↔ ∃ f : B ↪[L] M, f.comp i = j := by
  constructor
  · rintro ⟨N, f, g, heq⟩
    obtain ⟨e, he⟩ := hM.exists_embedding_over_tuple N g i j f
      (congrArg DFunLike.coe heq)
    exact ⟨e, Embedding.ext (congrFun he)⟩
  · rintro ⟨f, heq⟩
    let : Nonempty M := hM.1
    let : M ⊨ T := hM.2.1
    exact ⟨ModelType.of T M, f, Embedding.refl L M, heq⟩

/-- The finite extension formula expresses amalgamation with an existentially closed model.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 332, 341.
-/
theorem IsExistentiallyClosed.amalgamableOver_iff_realize_extensionFormula [Finite L.Symbols]
    [Finite A] [Finite B] {M : Type (max u v)} [L.Structure M]
    (hM : T.IsExistentiallyClosed M) (i : A ↪[L] B) (j : A ↪[L] M) :
    T.AmalgamableOver i j ↔ (extensionFormula (L := L) (i : A → B)).Realize j := by
  rw [hM.amalgamableOver_iff_exists_embedding i j, realize_extensionFormula_iff]
  exact exists_congr fun f => ⟨fun h => congrArg DFunLike.coe h,
    fun h => Embedding.ext (congrFun h)⟩

end Theory

end FirstOrder.Language
