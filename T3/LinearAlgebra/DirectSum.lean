/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decomposition into the canonical summands of a direct sum

The ranges of the canonical inclusions `DirectSum.lof` form a `DirectSum.Decomposition` of the
external direct sum. The decomposition sends each coordinate to its canonical inclusion,
regarded as an element of that inclusion's range.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, supporting the direct-sum grading in Definition 2.18.
-/

@[expose] public section

open scoped DirectSum

namespace DirectSum

variable (R : Type*) [Semiring R] (ι : Type*) [DecidableEq ι]
  (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The canonical homogeneous submodules decompose the external direct sum.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, supporting the direct-sum grading in Definition 2.18.
-/
instance rangeLofDecomposition :
    Decomposition (fun i => LinearMap.range (lof R ι M i)) := by
  apply Decomposition.ofLinearMap _ (lmap fun i => (lof R ι M i).rangeRestrict)
  · apply linearMap_ext
    intro i
    ext x
    simp
  · apply linearMap_ext
    intro i
    ext x
    obtain ⟨m, hm⟩ := x.property
    have hx : x = (lof R ι M i).rangeRestrict m := Subtype.ext hm.symm
    rw [hx]
    simp

/-- The `i`-th homogeneous component is the canonical inclusion of the `i`-th coordinate.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, supporting the direct-sum grading in Definition 2.18.
-/
@[simp]
theorem coe_decompose_range_lof (x : ⨁ i, M i) (i : ι) :
    (decompose (fun i => LinearMap.range (lof R ι M i)) x i : ⨁ i, M i) =
      lof R ι M i (x i) := rfl

end DirectSum
