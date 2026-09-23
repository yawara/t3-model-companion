/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.BlockBracket
public import T3.GroupTheory.Coproduct.CentralSeriesCriterion
public import T3.GroupTheory.Coproduct.FreeTwo
public import T3.GroupTheory.Coproduct.GradedEquiv
public import T3.LinearAlgebra.TensorProduct

/-!
# Graded separation in a coproduct with the two-generator free group

The two claims in the proof of Lemma 4.6 are proved by the paper's component calculations.
In degree one we separate the left and right components. In degree two we expand the mixed
tensor against the two free generators and inspect the left pure coefficient, the two mixed
coefficients, and the right pure coefficient in that order. The mixed brackets have the
paper's signs, and their nonvanishing is read through the canonical degree-three equivalence.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v8.tex, `lemma:coincidence of central series`, Claims A and B.
-/

@[expose] public section

open scoped TensorProduct

namespace T3.Coproduct.FreeTwoSeparation

open AssociatedGraded

variable {G : Type*} [Group G] [Fact (HasExponentThree G)]

omit [Fact (HasExponentThree G)] in
private theorem bracket_inr_inr (β : Layer (Free (Fin 2)) 2)
    (w : Layer (Free (Fin 2)) 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mapLayer (inr (G := G)) 2 β) (mapLayer inr 1 w) = 0 := by
  rw [← mapLayer_bracketLayer (i := 2) (j := 1)]
  have h : bracketLayer (by decide) (by decide) β w = 0 :=
    FreeTwo.layerThree_subsingleton.elim _ _
  rw [h, map_zero]

private theorem bracket_inr_inl (β : Layer (Free (Fin 2)) 2) (g : Layer G 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mapLayer inr 2 β) (mapLayer inl 1 g) =
      -mixedMap (i := 1) (j := 2) (by decide) (by decide) (g ⊗ₜ[ZMod 3] β) := by
  rw [mixedMap_tmul, bracketLayer_one_two, neg_neg]

private theorem mixed_one_two_tmul_ne_zero {g : Layer G 1}
    {β : Layer (Free (Fin 2)) 2} (hg : g ≠ 0) (hβ : β ≠ 0) :
    mixedMap (i := 1) (j := 2) (by decide) (by decide) (g ⊗ₜ[ZMod 3] β) ≠ 0 := by
  intro h
  have he := congrArg (fun z : Layer (Coproduct G (Free (Fin 2))) 3 =>
    ((layerThreeEquiv (G := G) (H := Free (Fin 2))).symm z).2.2.1) h
  exact TensorProduct.tmul_ne_zero hg hβ (by simpa using he)

private theorem triple_sum_inr_inr (α : Layer G 1) (β u v : Layer (Free (Fin 2)) 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (bracketLayer (i := 1) (j := 1) (by decide) (by decide)
        (mapLayer inl 1 α + mapLayer inr 1 β) (mapLayer inr 1 u)) (mapLayer inr 1 v) =
      -mixedMap (i := 1) (j := 2) (by decide) (by decide)
        (α ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) u v) := by
  rw [map_add, LinearMap.add_apply, ← mixedMap_tmul (i := 1) (j := 1),
    ← mapLayer_bracketLayer (i := 1) (j := 1), map_add, LinearMap.add_apply,
    bracket_mixedMap_tmul_inr, bracket_inr_inr, add_zero]

private theorem triple_inr_inl_inr (β w : Layer (Free (Fin 2)) 1) (g : Layer G 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (bracketLayer (i := 1) (j := 1) (by decide) (by decide)
        (mapLayer inr 1 β) (mapLayer inl 1 g)) (mapLayer inr 1 w) =
      mixedMap (i := 1) (j := 2) (by decide) (by decide)
        (g ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) β w) := by
  rw [bracketLayer_one_swap, ← mixedMap_tmul (i := 1) (j := 1), map_neg,
    LinearMap.neg_apply, bracket_mixedMap_tmul_inr, neg_neg]

/-- Every nonzero first-layer vector of `G ∐ F₂` is detected by a triple bracket.
The two cases are the paper's nonzero left component and nonzero right component.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v8.tex, `lemma:coincidence of central series`, Claim A, lines 1060–1073.
-/
theorem exists_triple_bracket_ne_zero [Nontrivial G]
    (a : Layer (Coproduct G (Free (Fin 2))) 1) (ha : a ≠ 0) :
    ∃ b c : Layer (Coproduct G (Free (Fin 2))) 1,
      bracketLayer (by decide) (by decide)
        (bracketLayer (by decide) (by decide) a b) c ≠ 0 := by
  obtain ⟨⟨α, β⟩, rfl⟩ := (layerOneEquiv (G := G) (H := Free (Fin 2))).surjective a
  simp only [layerOneEquiv_apply] at ha ⊢
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := by
      intro hβ
      exact ha (by simp [hα, hβ])
    obtain ⟨g, hg⟩ := exists_nonzero_layerOne (G := G)
    obtain ⟨w, _, hw⟩ := FreeTwo.exists_bracket_ne_zero β hβ
    refine ⟨mapLayer inl 1 g, mapLayer inr 1 w, ?_⟩
    simp only [hα, map_zero, zero_add]
    rw [triple_inr_inl_inr β w g]
    exact mixed_one_two_tmul_ne_zero hg hw
  · refine ⟨mapLayer inr 1 FreeTwo.x, mapLayer inr 1 FreeTwo.y, ?_⟩
    rw [triple_sum_inr_inr, neg_ne_zero]
    exact mixed_one_two_tmul_ne_zero hα FreeTwo.q_ne_zero

private theorem bracket_two_inr (α₂ : Layer G 2) (α₁ α₁' : Layer G 1)
    (β₂ : Layer (Free (Fin 2)) 2) (w : Layer (Free (Fin 2)) 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (layerTwoEquiv (α₂, α₁ ⊗ₜ[ZMod 3] FreeTwo.x + α₁' ⊗ₜ[ZMod 3] FreeTwo.y, β₂))
      (mapLayer inr 1 w) =
      mixedMap (i := 2) (j := 1) (by decide) (by decide) (α₂ ⊗ₜ[ZMod 3] w) +
        (-mixedMap (i := 1) (j := 2) (by decide) (by decide)
          (α₁ ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) FreeTwo.x w) +
        -mixedMap (i := 1) (j := 2) (by decide) (by decide)
          (α₁' ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) FreeTwo.y w)) := by
  simp only [layerTwoEquiv_apply, layerTwoMap_apply, map_add, LinearMap.add_apply]
  rw [← mixedMap_tmul (i := 2) (j := 1), bracket_mixedMap_tmul_inr,
    bracket_mixedMap_tmul_inr, bracket_inr_inr, add_zero]

/-- Every nonzero second-layer vector of `G ∐ F₂` has a nonzero bracket with the first layer.
The proof follows the paper's four coefficients `α₂`, `α₁`, `α₁'`, and `β₂`.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v8.tex, `lemma:coincidence of central series`, Claim B, lines 1074–1087.
-/
theorem exists_bracket_ne_zero [Nontrivial G]
    (a : Layer (Coproduct G (Free (Fin 2))) 2) (ha : a ≠ 0) :
    ∃ b : Layer (Coproduct G (Free (Fin 2))) 1,
      bracketLayer (by decide) (by decide) a b ≠ 0 := by
  obtain ⟨⟨α₂, t, β₂⟩, rfl⟩ := (layerTwoEquiv (G := G) (H := Free (Fin 2))).surjective a
  obtain ⟨α₁, α₁', rfl⟩ := FreeTwo.exists_tensor_eq t
  by_cases hα₂ : α₂ = 0
  · by_cases hα₁ : α₁ = 0
    · by_cases hα₁' : α₁' = 0
      · have hβ₂ : β₂ ≠ 0 := by
          intro hβ₂
          apply ha
          simp [hα₂, hα₁, hα₁', hβ₂, layerTwoMap_apply]
        obtain ⟨g, hg⟩ := exists_nonzero_layerOne (G := G)
        refine ⟨mapLayer inl 1 g, ?_⟩
        simp only [hα₂, hα₁, hα₁', TensorProduct.zero_tmul, add_zero,
          layerTwoEquiv_apply, layerTwoMap_apply, map_zero, zero_add]
        rw [bracket_inr_inl, neg_ne_zero]
        exact mixed_one_two_tmul_ne_zero hg hβ₂
      · refine ⟨mapLayer inr 1 FreeTwo.x, ?_⟩
        rw [bracket_two_inr]
        simp only [hα₂, hα₁, TensorProduct.zero_tmul, map_zero, neg_zero, zero_add]
        rw [bracketLayer_one_swap FreeTwo.y FreeTwo.x, TensorProduct.tmul_neg,
          map_neg, neg_neg]
        exact mixed_one_two_tmul_ne_zero hα₁' FreeTwo.q_ne_zero
    · refine ⟨mapLayer inr 1 FreeTwo.y, ?_⟩
      rw [bracket_two_inr]
      simp only [hα₂, TensorProduct.zero_tmul, map_zero, zero_add, bracketLayer_one_self,
        TensorProduct.tmul_zero, neg_zero, add_zero, neg_ne_zero]
      exact mixed_one_two_tmul_ne_zero hα₁ FreeTwo.q_ne_zero
  · refine ⟨mapLayer inr 1 FreeTwo.x, ?_⟩
    rw [bracket_two_inr]
    intro h
    have he := congrArg (fun z : Layer (Coproduct G (Free (Fin 2))) 3 =>
      ((layerThreeEquiv (G := G) (H := Free (Fin 2))).symm z).2.1) h
    exact TensorProduct.tmul_ne_zero hα₂ FreeTwo.x_ne_zero (by simpa using he)

end T3.Coproduct.FreeTwoSeparation
