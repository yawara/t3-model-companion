/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.ExteriorBracket
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The graded linear calculations for the two-generator free group

The two free generators give a basis of the actual first lower-central quotient. Their bracket
is nonzero, while the third quotient vanishes. Every nonzero first-layer vector has a nonzero
bracket with one of the two basis vectors. Tensors with this first layer have the paper's two-term
expansion, for arbitrary coefficient modules without a dimension or cardinality restriction.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, proof, lines 973–1001.
-/

@[expose] public section

open scoped TensorProduct
open Module T3.AssociatedGraded

namespace T3.Coproduct.FreeTwo

/-- The initial form of the first free generator.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the vector `x`.
-/
noncomputable def x : Layer (Free (Fin 2)) 1 := Free.layerOneBasis 0

/-- The initial form of the second free generator.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the vector `y`.
-/
noncomputable def y : Layer (Free (Fin 2)) 1 := Free.layerOneBasis 1

/-- The bracket of the two generator classes, corresponding to `x ∧ y`.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the two-form `x ∧ y`.
-/
noncomputable def q : Layer (Free (Fin 2)) 2 := bracketLayer (by decide) (by decide) x y

/-- The first generator class is nonzero.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the basis `{x,y}`.
-/
theorem x_ne_zero : x ≠ 0 := Free.layerOneBasis.ne_zero 0

/-- The second generator class is nonzero.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the basis `{x,y}`.
-/
theorem y_ne_zero : y ≠ 0 := Free.layerOneBasis.ne_zero 1

/-- The bracket of the two generator classes is the increasing-commutator basis vector.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, `x ∧ y ≠ 0`.
-/
theorem q_eq_basis : q = Free.layerTwoBasis (⟨0, 1, by decide⟩ : IncreasingPair (Fin 2)) :=
  (Free.layerTwoBasis_eq_bracket ⟨0, 1, by decide⟩).symm

/-- The wedge of the two generator classes is nonzero in the actual second layer.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, `x ∧ y ≠ 0`.
-/
theorem q_ne_zero : q ≠ 0 := by
  rw [q_eq_basis]
  exact Free.layerTwoBasis.ne_zero _

/-- The third layer of the two-generator free group is trivial.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, `β₂ ∧ y = 0`.
-/
theorem layerThree_subsingleton : Subsingleton (Layer (Free (Fin 2)) 3) := by
  let : IsEmpty (IncreasingTriple (Fin 2)) := ⟨fun t => by
    have h₁ := t.first_lt_second
    have h₂ := t.second_lt_third
    have h₃ := t.third.isLt
    simp only [Fin.lt_def] at h₁ h₂
    omega⟩
  exact ⟨fun a b => Free.layerThreeEquiv.injective (Subsingleton.elim _ _)⟩

/-- Every first-layer vector is the sum of its two generator coordinates.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the basis `{x,y}`.
-/
theorem eq_repr_smul (β : Layer (Free (Fin 2)) 1) :
    β = Free.layerOneBasis.repr β 0 • x + Free.layerOneBasis.repr β 1 • y := by
  simpa only [Fin.sum_univ_two, x, y] using (Free.layerOneBasis.sum_repr β).symm

/-- Bracketing a first-layer vector with the second generator extracts its first coordinate.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, choice of `w`.
-/
theorem bracket_y (β : Layer (Free (Fin 2)) 1) :
    bracketLayer (by decide) (by decide) β y = Free.layerOneBasis.repr β 0 • q := by
  nth_rw 1 [eq_repr_smul β]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    bracketLayer_one_self, smul_zero, add_zero, q]

/-- Bracketing a first-layer vector with the first generator extracts the negative second
coordinate.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, choice of `w`.
-/
theorem bracket_x (β : Layer (Free (Fin 2)) 1) :
    bracketLayer (by decide) (by decide) β x = - (Free.layerOneBasis.repr β 1 • q) := by
  nth_rw 1 [eq_repr_smul β]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    bracketLayer_one_self, smul_zero, zero_add]
  rw [bracketLayer_one_swap y x]
  simp only [q, smul_neg]

/-- A nonzero first-layer vector has a nonzero bracket with one of the free generators.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, line 983.
-/
theorem exists_bracket_ne_zero (β : Layer (Free (Fin 2)) 1) (hβ : β ≠ 0) :
    ∃ w : Layer (Free (Fin 2)) 1, (w = x ∨ w = y) ∧
      bracketLayer (by decide) (by decide) β w ≠ 0 := by
  by_cases h₀ : Free.layerOneBasis.repr β 0 = 0
  · have h₁ : Free.layerOneBasis.repr β 1 ≠ 0 := by
      intro h₁
      apply hβ
      rw [eq_repr_smul β, h₀, h₁, zero_smul, zero_smul, add_zero]
    refine ⟨x, Or.inl rfl, ?_⟩
    rw [bracket_x, neg_ne_zero]
    exact smul_ne_zero h₁ q_ne_zero
  · refine ⟨y, Or.inr rfl, ?_⟩
    rw [bracket_y]
    exact smul_ne_zero h₀ q_ne_zero

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

/-- Every tensor with the first layer of `F₂` has the paper's two-term generator expansion.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, lines 992–993.
-/
theorem exists_tensor_eq (t : V ⊗[ZMod 3] Layer (Free (Fin 2)) 1) :
    ∃ α α' : V, t = α ⊗ₜ[ZMod 3] x + α' ⊗ₜ[ZMod 3] y := by
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) (Free.layerOneBasis (I := Fin 2))
  refine ⟨e t 0, e t 1, ?_⟩
  have h := e.symm_apply_apply t
  change e.symm (e t) = t at h
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    Finsupp.sum_fintype (e t) _ (fun i =>
      TensorProduct.zero_tmul V (Free.layerOneBasis i)), Fin.sum_univ_two] at h
  exact h.symm

end T3.Coproduct.FreeTwo
