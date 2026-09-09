/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.Amalgamation
public import T3.ModelTheory.ExistentialClosedness

/-!
# Amalgamation in arbitrary universes

Ordinary amalgams can be realized in the maximum of the language and extension universes.
Skolem hulls of the two images show that the choice of target universe does not restrict the
mathematical amalgamation problem. When both sides are small, this agrees with the original
canonical-universe predicate.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 220–262.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' w'' w''' z

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T : L.Theory}

/-- An ordinary amalgam in the maximum of the language and the two extension universes.
No condition is imposed on the intersection of the two images.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 222–225.
-/
def AmalgamableOverAt (T : L.Theory)
    {A : Type w} {B : Type w'} {C : Type w''}
    [L.Structure A] [L.Structure B] [L.Structure C] (i : A ↪[L] B) (j : A ↪[L] C) : Prop :=
  ∃ (N : T.ModelType.{u, v, max u v w' w''}) (f : B ↪[L] N) (g : C ↪[L] N),
    f.comp i = g.comp j

variable {A : Type w} {B : Type w'} {C : Type w''}
  [L.Structure A] [L.Structure B] [L.Structure C]

/-- An amalgam can be chosen in any universe containing small copies of both sides and
all language symbols. Only the images of the two sides are placed in the Skolem hull.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, supporting `fact:locally finiteness and model companion`.
-/
theorem exists_amalgam_of_small [Small.{max u v z} B] [Small.{max u v z} C]
    {i : A ↪[L] B} {j : A ↪[L] C} (N : Type w''')
    [L.Structure N] [Nonempty N] [N ⊨ T] (f : B ↪[L] N) (g : C ↪[L] N)
    (heq : f.comp i = g.comp j) :
    ∃ (P : T.ModelType.{u, v, max u v z}) (f' : B ↪[L] P) (g' : C ↪[L] P),
      f'.comp i = g'.comp j := by
  classical
  let s : Set N := Set.range (Sum.elim f g)
  let S := (Substructure.closure (L.sum L.skolem₁) s).elementarySkolem₁Reduct
  haveI : Small.{max u v z} S := by
    change Small.{max u v z} (Substructure.closure (L.sum L.skolem₁) s)
    rw [← SetLike.coe_sort_coe, Substructure.coe_closure_eq_range_term_realize]
    haveI : Small.{max u v z} ((L.sum L.skolem₁).Term s) :=
      small_of_injective (Term.relabelEquiv (equivShrink.{max u v z} s)).injective
    exact small_range _
  let P : T.ModelType.{u, v, max u v z} := (ModelType.of T S).shrink
  let e : S ≃[L] P := (equivShrink S).inducedStructureEquiv
  let fS : B ↪[L] S := f.codRestrict S.toSubstructure
    (fun b => Substructure.subset_closure ⟨Sum.inl b, rfl⟩)
  let gS : C ↪[L] S := g.codRestrict S.toSubstructure
    (fun c => Substructure.subset_closure ⟨Sum.inr c, rfl⟩)
  refine ⟨P, e.toEmbedding.comp fS, e.toEmbedding.comp gS, ?_⟩
  apply Embedding.ext
  intro a
  apply congrArg e.toEmbedding
  apply Subtype.ext
  exact DFunLike.congr_fun heq a

/-- An amalgam in any target universe gives the standard universe-sized amalgam.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, supporting `fact:locally finiteness and model companion`.
-/
theorem AmalgamableOverAt.of_amalgam {i : A ↪[L] B} {j : A ↪[L] C}
    (N : Type w''') [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : B ↪[L] N) (g : C ↪[L] N) (heq : f.comp i = g.comp j) :
    T.AmalgamableOverAt i j :=
  exists_amalgam_of_small.{u, v, w, w', w'', w''', max w' w''} N f g heq

/-- For canonically small sides, amalgamation is equivalent to the original predicate.
In particular, this applies to finite structures in arbitrary universes.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, supporting `fact:locally finiteness and model companion`.
-/
theorem amalgamableOverAt_iff [Small.{max u v} B] [Small.{max u v} C]
    {i : A ↪[L] B} {j : A ↪[L] C} :
    T.AmalgamableOverAt i j ↔ T.AmalgamableOver i j := by
  constructor
  · rintro ⟨N, f, g, heq⟩
    exact exists_amalgam_of_small.{u, v, w, w', w'', max u v w' w'', 0} N f g heq
  · rintro ⟨N, f, g, heq⟩
    exact AmalgamableOverAt.of_amalgam N f g heq

/-- Ordinary amalgamation is symmetric in the two extensions.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`.
-/
theorem AmalgamableOverAt.symm {i : A ↪[L] B} {j : A ↪[L] C}
    (h : T.AmalgamableOverAt i j) : T.AmalgamableOverAt j i := by
  obtain ⟨N, f, g, heq⟩ := h
  exact ⟨N, g, f, heq.symm⟩

/-- Restricting one side of an ordinary amalgam preserves amalgamability, even when the
restriction changes its universe.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 260–262.
-/
theorem AmalgamableOverAt.of_comp_right {D : Type w'''} [L.Structure D]
    {i : A ↪[L] B} {j : A ↪[L] C} (e : C ↪[L] D)
    (h : T.AmalgamableOverAt i (e.comp j)) : T.AmalgamableOverAt i j := by
  obtain ⟨N, f, g, heq⟩ := h
  exact AmalgamableOverAt.of_amalgam N f (g.comp e) heq

/-- Over a finite base, an arbitrary existentially closed model amalgamates with a finite
extension exactly when that extension embeds back into the model over the base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 238, 257.
-/
theorem IsExistentiallyClosedAt.amalgamableOverAt_iff_exists_embedding [Finite L.Symbols]
    [Finite A] [Finite B] {M : Type w''} [L.Structure M]
    (hM : T.IsExistentiallyClosedAt M) (i : A ↪[L] B) (j : A ↪[L] M) :
    T.AmalgamableOverAt i j ↔ ∃ f : B ↪[L] M, f.comp i = j := by
  constructor
  · rintro ⟨N, f, g, heq⟩
    obtain ⟨e, he⟩ := hM.exists_embedding_over_tuple N g i j f
      (congrArg DFunLike.coe heq)
    exact ⟨e, Embedding.ext (congrFun he)⟩
  · rintro ⟨f, heq⟩
    letI : Nonempty M := hM.1
    letI : M ⊨ T := hM.2.1
    exact AmalgamableOverAt.of_amalgam M f (Embedding.refl L M) heq

/-- The same finite extension formula expresses amalgamation with an existentially closed
model in every universe.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 238, 257.
-/
theorem IsExistentiallyClosedAt.amalgamableOverAt_iff_realize_extensionFormula
    [Finite L.Symbols] [Finite A] [Finite B] {M : Type w''} [L.Structure M]
    (hM : T.IsExistentiallyClosedAt M) (i : A ↪[L] B) (j : A ↪[L] M) :
    T.AmalgamableOverAt i j ↔ (extensionFormula (L := L) (i : A → B)).Realize j := by
  rw [hM.amalgamableOverAt_iff_exists_embedding i j, realize_extensionFormula_iff]
  exact exists_congr fun f => ⟨fun h => congrArg DFunLike.coe h,
    fun h => Embedding.ext (congrFun h)⟩

end FirstOrder.Language.Theory
