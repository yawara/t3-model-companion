/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.Amalgamation.Universes
public import T3.ModelTheory.BoundedAmalgamationCriterion
public import T3.ModelTheory.LocallyFinite.Universes

/-!
# Bounded amalgamation obstructions in arbitrary models

The same existential rewriting of the negated finite extension formula supplies a fixed
bound for obstructions in existentially closed models of every universe. The witnesses and
the original bound are unchanged; actual amalgams can live in any universe.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 214–243.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' z

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T Tstar : L.Theory}

private theorem isExistentiallyClosedAt_equiv {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (hM : T.IsExistentiallyClosedAt M) (e : M ≃[L] N) :
    T.IsExistentiallyClosedAt N := by
  let : Nonempty M := hM.1
  let : Nonempty N := e.toEquiv.symm.nonempty
  let : M ⊨ T := hM.2.1
  have : N ⊨ T := (e.toElementaryEmbedding.theory_model_iff T).mp hM.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro P f n φ x hφ hP
  have hPx : φ.Realize ((f.comp e.toEmbedding) ∘ (e.symm ∘ x)) := by
    simpa only [Function.comp_def, Embedding.comp_apply, Equiv.coe_toEmbedding,
      Equiv.apply_symm_apply] using hP
  have hMx := hM.reflects_of_model P (f.comp e.toEmbedding) φ (e.symm ∘ x) hφ hPx
  have heφ := e.toElementaryEmbedding.map_formula φ (e.symm ∘ x)
  simpa only [Equiv.coe_toElementaryEmbedding, Function.comp_def, Equiv.apply_symm_apply]
    using heφ.mpr hMx

/-- A model companion gives one generator bound for every fixed finite inclusion. The bound
is the existential witness bound of the negated extension formula plus the size of the base.
Local finiteness is not needed for this generator bound; it makes the resulting obstruction
finite in the subsequent corollary.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 233–243.
-/
theorem IsModelCompanionOf.exists_bounded_nonamalgamation_obstruction_in_universe [Finite L.Symbols]
    (hPi : T.IsPiTwo) (hMC : Tstar.IsModelCompanionOf T)
    {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B] [Finite A] [Finite B]
    (i : A ↪[L] B) :
    ∃ n : ℕ, ∀ (M : Type z) [L.Structure M], T.IsExistentiallyClosedAt M →
      ∀ j : A ↪[L] M, ¬ T.AmalgamableOverAt i j →
        ∃ (C : L.Substructure M) (hj : ∀ a, j a ∈ C), C.GeneratedByAtMost n ∧
          ¬ T.AmalgamableOverAt i (j.codRestrict C hj) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let a := Fintype.card A
  let eA : A ≃ Fin a := Fintype.equivFin A
  let δ : L.Formula (Fin a) := (extensionFormula (L := L) (i : A → B)).relabel eA
  obtain ⟨ψ, hψ, hiff⟩ := hMC.isModelComplete δ.not
  obtain ⟨k, hk⟩ := hψ.exists_bounded_finite_witnesses_formula
  refine ⟨k + a, ?_⟩
  intro M _ hM j hbad
  let : Nonempty M := hM.1
  let : M ⊨ T := hM.2.1
  let : M ⊨ Tstar := (hMC.models_iff_isExistentiallyClosedAt hPi M).mpr hM
  let vA : Fin a → M := j ∘ eA.symm
  have hvA : vA ∘ eA = j := by
    funext x
    exact congrArg j (eA.symm_apply_apply x)
  have hnotδ : ¬ δ.Realize vA := by
    intro hδ
    change ((extensionFormula (L := L) (i : A → B)).relabel eA).Realize vA at hδ
    rw [Formula.realize_relabel, hvA] at hδ
    exact hbad ((hM.amalgamableOverAt_iff_realize_extensionFormula i j).mpr hδ)
  have hψM : ψ.Realize vA := hiff.realize_iff.mp (Formula.realize_not.mpr hnotδ)
  obtain ⟨s, hs, htransfer⟩ := hk M vA hψM
  let t : Finset M := s ∪ Finset.univ.image j
  let C : L.Substructure M := Substructure.closure L (t : Set M)
  have hj : ∀ x, j x ∈ C := fun x =>
    Substructure.subset_closure (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ x)))
  refine ⟨C, hj, ⟨t, ?_, rfl⟩, ?_⟩
  · exact (Finset.card_union_le _ _).trans (add_le_add hs
      (Finset.card_image_le.trans (by simp [a])))
  · intro hbadC
    obtain ⟨N₀, f, g, hcomm⟩ := hbadC
    obtain ⟨N, ⟨e⟩⟩ := hMC.isCompanion.2.exists_embedding N₀
    let vC : Fin a → C := j.codRestrict C hj ∘ eA.symm
    have hvC : vC ∘ eA = j.codRestrict C hj := by
      funext x
      exact congrArg (j.codRestrict C hj) (eA.symm_apply_apply x)
    have hsC : (s : Set M) ⊆ Set.range C.subtype := fun x hx =>
      ⟨⟨x, Substructure.subset_closure (Finset.mem_union_left _ hx)⟩, rfl⟩
    have hψC : ψ.Realize vC := htransfer C C.subtype hsC vC rfl
    have hψN : ψ.Realize ((e.comp g) ∘ vC) :=
      hψ.realize_formula_embedding (e.comp g) hψC
    have hδN : δ.Realize ((e.comp g) ∘ vC) := by
      change ((extensionFormula (L := L) (i : A → B)).relabel eA).Realize _
      rw [Formula.realize_relabel, Function.comp_assoc, hvC]
      apply (realize_extensionFormula_iff _ _).mpr
      refine ⟨e.comp f, ?_⟩
      funext x
      exact congrArg e (DFunLike.congr_fun hcomm x)
    exact (Formula.realize_not.mp (hiff.realize_iff.mpr hψN)) hδN


/-- The canonical bounded-obstruction condition yields the same all-model conclusion through
the model companion supplied by the sufficient direction of the criterion. The hypotheses
are exactly the finite-language, locally finite, Pi-two hypotheses of Fact 2.6.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 214–263.
-/
theorem BoundedAmalgamationObstructions.exists_bounded_obstruction_in_universe
    [Finite L.Symbols] (hbound : T.BoundedAmalgamationObstructions)
    (hPi : T.IsPiTwo) (hLF : T.IsLocallyFinite)
    {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B] [Finite A] [Finite B]
    (i : A ↪[L] B) :
    ∃ n : ℕ, ∀ (M : Type z) [L.Structure M], T.IsExistentiallyClosedAt M →
      ∀ j : A ↪[L] M, ¬ T.AmalgamableOverAt i j →
        ∃ (C : L.Substructure M) (hj : ∀ a, j a ∈ C), C.GeneratedByAtMost n ∧
          ¬ T.AmalgamableOverAt i (j.codRestrict C hj) := by
  obtain ⟨Tstar, hMC⟩ := hasModelCompanion_of_boundedAmalgamationObstructions hPi hLF hbound
  exact hMC.exists_bounded_nonamalgamation_obstruction_in_universe hPi i

/-- In a locally finite theory, the uniformly generated obstruction inside an arbitrary
existentially closed model is finite. The finite obstruction need not itself model the theory.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 220–243.
-/
theorem HasModelCompanion.exists_finite_bounded_obstruction_in_universe
    [Finite L.Symbols] (h : T.HasModelCompanion) (hPi : T.IsPiTwo)
    (hLF : T.IsLocallyFinite) {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] [Finite A] [Finite B] (i : A ↪[L] B) :
    ∃ n : ℕ, ∀ (M : Type z) [L.Structure M], T.IsExistentiallyClosedAt M →
      ∀ j : A ↪[L] M, ¬ T.AmalgamableOverAt i j →
        ∃ (C : L.Substructure M) (hj : ∀ a, j a ∈ C), Finite C ∧ C.GeneratedByAtMost n ∧
          ¬ T.AmalgamableOverAt i (j.codRestrict C hj) := by
  obtain ⟨Tstar, hMC⟩ := h
  obtain ⟨n, hn⟩ :=
    IsModelCompanionOf.exists_bounded_nonamalgamation_obstruction_in_universe.{u, v, w, w', z}
      hPi hMC i
  refine ⟨n, ?_⟩
  intro M _ hM j hbad
  let : Nonempty M := hM.1
  let : M ⊨ T := hM.2.1
  obtain ⟨C, hj, hgen, hbadC⟩ := hn M hM j hbad
  refine ⟨C, hj, ?_, hgen, hbadC⟩
  obtain ⟨s, _, heq⟩ := hgen
  rw [← heq]
  exact hLF.finite_closure M (s : Set M) s.finite_toSet

/-- Each finite inclusion has one generator bound for obstructions in all existentially
closed models of a universe containing the language's canonical semantic universe.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, item 2.
-/
def BoundedAmalgamationObstructionsAt (T : L.Theory) : Prop :=
  ∀ d : FiniteInclusion T, ∃ n : ℕ,
    ∀ (M : Type (max u v z)) [L.Structure M], T.IsExistentiallyClosedAt M →
      ∀ j : d.base ↪[L] M, ¬ T.AmalgamableOverAt d.incl j →
        ∃ (C : L.Substructure M) (hj : ∀ a, j a ∈ C), C.GeneratedByAtMost n ∧
          ¬ T.AmalgamableOverAt d.incl (j.codRestrict C hj)

/-- The larger-universe condition restricts to the canonical condition. Lifting a model
preserves existential closedness, and mapping the obstruction back preserves its generators.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, supporting `fact:locally finiteness and model companion`.
-/
theorem BoundedAmalgamationObstructionsAt.to_canonical
    (h : BoundedAmalgamationObstructionsAt.{u, v, z} T) :
    T.BoundedAmalgamationObstructions := by
  classical
  intro d
  obtain ⟨n, hn⟩ := h d
  refine ⟨n, ?_⟩
  intro M hM j hbad
  let N : T.ModelType.{u, v, max u v z} := M.ulift
  let e : M ≃[L] N := Equiv.inducedStructureEquiv _
  have hN : T.IsExistentiallyClosedAt N := isExistentiallyClosedAt_equiv hM e
  let jN : d.base ↪[L] N := e.toEmbedding.comp j
  have hbadN : ¬ T.AmalgamableOverAt d.incl jN := by
    intro hN
    exact hbad (amalgamableOverAt_iff.mp (hN.of_comp_right e.toEmbedding))
  obtain ⟨C, hj, hgen, hbadC⟩ := hn N hN jN hbadN
  let D : L.Substructure M := C.map e.symm.toHom
  have hjD : ∀ a, j a ∈ D := by
    intro a
    refine ⟨e (j a), hj a, ?_⟩
    exact e.symm_apply_apply (j a)
  have hgenD : D.GeneratedByAtMost n := by
    obtain ⟨s, hs, heq⟩ := hgen
    refine ⟨s.image e.symm, Finset.card_image_le.trans hs, ?_⟩
    rw [Finset.coe_image, ← Equiv.coe_toHom (f := e.symm),
      ← Substructure.map_closure, heq]
  let q : C ↪[L] D := (e.symm.toEmbedding.comp C.subtype).codRestrict D
    (fun c => ⟨c, c.property, rfl⟩)
  have hmark : q.comp (jN.codRestrict C hj) = j.codRestrict D hjD := by
    apply Embedding.ext
    intro a
    apply Subtype.ext
    exact e.symm_apply_apply (j a)
  refine ⟨D, hjD, hgenD, ?_⟩
  rintro ⟨P, f, g, heq⟩
  apply hbadC
  apply AmalgamableOverAt.of_comp_right q
  rw [hmark]
  exact AmalgamableOverAt.of_amalgam P f g heq

/-- The complete criterion supplies the bounded obstruction condition in every larger
semantic universe, with no cardinality condition on the existentially closed model.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 214–263.
-/
theorem BoundedAmalgamationObstructions.to_universe [Finite L.Symbols]
    (hbound : T.BoundedAmalgamationObstructions) (hPi : T.IsPiTwo)
    (hLF : T.IsLocallyFinite) : BoundedAmalgamationObstructionsAt.{u, v, z} T := by
  intro d
  exact hbound.exists_bounded_obstruction_in_universe hPi hLF d.incl

/-- **Fact 2.6 in arbitrary model universes.** For a locally finite Pi-two theory in a
finite language, the model-companion criterion holds in every semantic universe containing
the language's canonical universe. The amalgamation relation permits targets of any size.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 214–263.
-/
theorem hasModelCompanion_iff_boundedAmalgamationObstructionsAt [Finite L.Symbols]
    (hPi : T.IsPiTwo) (hLF : T.IsLocallyFinite) :
    T.HasModelCompanion ↔ BoundedAmalgamationObstructionsAt.{u, v, z} T := by
  constructor
  · rintro ⟨Tstar, hMC⟩ d
    exact hMC.exists_bounded_nonamalgamation_obstruction_in_universe hPi d.incl
  · intro hbound
    exact hasModelCompanion_of_boundedAmalgamationObstructions hPi hLF hbound.to_canonical

end FirstOrder.Language.Theory
