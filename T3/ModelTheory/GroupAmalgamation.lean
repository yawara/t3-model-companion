/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Amalgamation
public import T3.ModelTheory.ExponentThree

/-!
# Group amalgams and model-theoretic amalgams

An amalgam of compatible groups in the exponent-three variety is exactly an amalgam of their
group-language embeddings in `T₃`. In one direction, the algebraic target receives its
compatible language structure. In the other, the target model supplies its actual group
operations. The commuting diagrams are preserved element by element.

The two factors use the canonical semantic universe `Type`; the base may have any universe.
Neither the base nor either factor is assumed to model `T₃`, and no finiteness or condition
on the intersection of the two factor images is imposed.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v7.tex, `thm:main`, lines 781–823, and
`fact:locally finiteness and model companion`, the amalgamation criterion.
-/

@[expose] public section

open scoped FirstOrder

namespace T3

namespace Amalgamation

/-- Ordinary group amalgamation is symmetric in its factors, in arbitrary universes.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v7.tex, `thm:main`, the symmetric witness cases.
-/
theorem AmalgamableOver.symm {A G H : Type*} [Group A] [Group G] [Group H]
    {f : A →* G} {g : A →* H} (h : AmalgamableOver f g) : AmalgamableOver g f := by
  obtain ⟨K, hK, hpow, i, j, hi, hj, hij⟩ := h
  exact ⟨K, hK, hpow, j, i, hj, hi, hij.symm⟩

/-- Interchanging the two factors does not change group amalgamability.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v7.tex, `thm:main`, the symmetric witness cases.
-/
theorem amalgamableOver_comm {A G H : Type*} [Group A] [Group G] [Group H]
    (f : A →* G) (g : A →* H) : AmalgamableOver f g ↔ AmalgamableOver g f :=
  ⟨AmalgamableOver.symm, AmalgamableOver.symm⟩

end Amalgamation

namespace GroupAmalgamation

open FirstOrder FirstOrder.Language FirstOrder.Group

variable {A : Type*} {G H : Type} [Group A] [Group G] [Group H]
  [CompatibleGroup A] [CompatibleGroup G] [CompatibleGroup H]

/-- The concrete group amalgam and the first-order amalgam of the corresponding embeddings
are equivalent. Only the target is required to have exponent three.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v7.tex, `thm:main`, and the deduction from the amalgamation criterion.
-/
theorem amalgamableOver_iff (f : A →* G) (g : A →* H)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Amalgamation.AmalgamableOver f g ↔ exponentThreeTheory.AmalgamableOver
      (embeddingOfInjectiveMonoidHom f hf) (embeddingOfInjectiveMonoidHom g hg) := by
  constructor
  · rintro ⟨K, hK, hpow, i, j, hi, hj, hij⟩
    let : Group K := hK
    let : CompatibleGroup K := compatibleGroupOfGroup K
    let : K ⊨ exponentThreeTheory := exponentThreeTheory_model_iff.mpr hpow
    let i' : G ↪[Language.group] K := embeddingOfInjectiveMonoidHom i hi
    let j' : H ↪[Language.group] K := embeddingOfInjectiveMonoidHom j hj
    refine ⟨Theory.ModelType.of exponentThreeTheory K,
      i', j', ?_⟩
    apply Embedding.ext
    intro a
    exact DFunLike.congr_fun hij a
  · rintro ⟨N, i, j, hij⟩
    let : N ⊨ Theory.group := (inferInstance : N ⊨ exponentThreeTheory).mono
      (fun _ h => Set.mem_insert_of_mem _ h)
    let : Group N := groupOfModelGroup N
    let : CompatibleGroup N := compatibleGroupOfGroupStructure N
    refine ⟨N, inferInstance, exponentThreeTheory_model_iff.mp inferInstance,
      embeddingToMonoidHom i, embeddingToMonoidHom j, i.injective, j.injective, ?_⟩
    apply MonoidHom.ext
    intro a
    exact DFunLike.congr_fun hij a

/-- The amalgamation bridge expressed directly in terms of group-language embeddings.
The base need not satisfy `T₃` or any finiteness hypothesis.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v7.tex, `thm:main`, and the deduction from the amalgamation criterion.
-/
theorem amalgamableOver_embeddings_iff (f : A ↪[Language.group] G)
    (g : A ↪[Language.group] H) :
    exponentThreeTheory.AmalgamableOver f g ↔
      Amalgamation.AmalgamableOver (embeddingToMonoidHom f) (embeddingToMonoidHom g) := by
  simpa only [embeddingOfInjectiveMonoidHom_embeddingToMonoidHom] using
    (amalgamableOver_iff (embeddingToMonoidHom f) (embeddingToMonoidHom g)
      f.injective g.injective).symm

/-- The bridge with the factors reversed, matching the finite-extension-first convention
of the general model-companion criterion.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v7.tex, `thm:main`, applying the amalgamation criterion.
-/
theorem amalgamableOver_embeddings_swap_iff (f : A ↪[Language.group] G)
    (g : A ↪[Language.group] H) :
    exponentThreeTheory.AmalgamableOver f g ↔
      Amalgamation.AmalgamableOver (embeddingToMonoidHom g) (embeddingToMonoidHom f) :=
  (amalgamableOver_embeddings_iff f g).trans (Amalgamation.amalgamableOver_comm _ _)

end GroupAmalgamation

end T3
