/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Nonzero pure tensors over a field

Taking coordinates in any basis of the right factor shows that a pure tensor of two nonzero
vectors is nonzero. No finite-dimensionality assumption is used. This is the tensor
nonvanishing step in both central-series claims for a coproduct with the free group of rank two.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, lines 981–1001.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A pure tensor of two nonzero vectors over a field is nonzero, in arbitrary dimensions.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, tensor nonvanishing.
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

end TensorProduct
