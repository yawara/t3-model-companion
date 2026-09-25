/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Kernels of tensor maps and nonzero pure tensors

The kernel of the tensor product of two surjections is the sum of their tensor relation
subspaces. This gives the tensor quotients in the graded coproduct decomposition.

Taking coordinates in any basis of the right factor shows that a pure tensor of two nonzero
vectors is nonzero. No finite-dimensionality assumption is used. This is the tensor
nonvanishing step in both central-series claims for a coproduct with the free group of rank two.

Paper-ID: structure.graded_coproduct, structure.free_two_stabilization
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, lines 1012–1022, and
`lemma:coincidence of central series`, lines 1077–1097.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

section Quotient

variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- Tensoring two quotient maps kills exactly the sum of the two tensor relation subspaces.
No finite-dimensionality or flatness hypothesis is required.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, tensor quotients, lines 1012–1022.
-/
theorem map_ker_eq_map₂ (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (map f g).ker = Submodule.map₂ (mk R A B) f.ker ⊤ ⊔
      Submodule.map₂ (mk R A B) ⊤ g.ker := by
  rw [map_ker f.exact_subtype_ker_map hf g.exact_subtype_ker_map hg]
  simp only [LinearMap.lTensor, LinearMap.rTensor, range_map,
    LinearMap.range_id, Submodule.range_subtype]
  exact sup_comm _ _

end Quotient

section Nonvanishing

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A pure tensor of two nonzero vectors over a field is nonzero, in arbitrary dimensions.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v9.tex, `lemma:coincidence of central series`, tensor nonvanishing.
-/
theorem tmul_ne_zero {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[K] w ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K W
  intro h
  apply hw
  apply b.repr.injective
  ext i
  have hi := congrArg (fun t : V ⊗[K] W => equivFinsuppOfBasisRight b t i) h
  rw [equivFinsuppOfBasisRight_apply_tmul_apply, map_zero, Finsupp.zero_apply] at hi
  simpa only [map_zero, Finsupp.zero_apply] using (smul_eq_zero.mp hi).resolve_right hv

end Nonvanishing

end TensorProduct
