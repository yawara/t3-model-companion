/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Exterior
public import T3.GroupTheory.Free.ExteriorBracket
public import T3.GroupTheory.AssociatedGraded.Truncation
public import T3.LinearAlgebra.TruncatedExterior

/-!
# The exterior description of the associated graded of a free exponent-three group

The three basis isomorphisms are assembled into the paper's direct-sum map. The source is
the associated graded of the actual free group; the target is the truncated exterior algebra
of any vector space with the specified basis. The construction works in arbitrary rank.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/

@[expose] public section

open scoped ExteriorAlgebra DirectSum
open Module T3.AssociatedGraded

namespace T3.Free

variable {I V : Type*} [LinearOrder I] [AddCommGroup V] [Module (ZMod 3) V]
  (b : Basis I (ZMod 3) V)

/-- The direct sum `σ₁ ⊕ σ₂ ⊕ σ₃`, as a linear equivalence with the truncated exterior algebra.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/
noncomputable def exteriorLinearEquiv : GradedModule (Free I) ≃ₗ[ZMod 3] TruncatedExterior V :=
  (truncationEquiv (Free I)).trans
    ((sigmaOne b).prodCongr ((sigmaTwo b).prodCongr (sigmaThree b)))

/-- The first component of the direct-sum comparison is `σ₁`.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_one (x : GradedModule (Free I)) :
    TruncatedExterior.one (exteriorLinearEquiv b x) = sigmaOne b (x 1) := rfl

/-- The second component of the direct-sum comparison is `σ₂`.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_two (x : GradedModule (Free I)) :
    TruncatedExterior.two (exteriorLinearEquiv b x) = sigmaTwo b (x 2) := rfl

/-- The third component of the direct-sum comparison is `σ₃`.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_three (x : GradedModule (Free I)) :
    TruncatedExterior.three (exteriorLinearEquiv b x) = sigmaThree b (x 3) := rfl

/-- The comparison inserts `σ₁` into the first homogeneous exterior summand.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_lof_one (x : Layer (Free I) 1) :
    exteriorLinearEquiv b (DirectSum.lof (ZMod 3) ℕ (Layer (Free I)) 1 x) =
      TruncatedExterior.ofOne (sigmaOne b x) := by
  apply TruncatedExterior.ext <;>
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

/-- The comparison inserts `σ₂` into the second homogeneous exterior summand.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_lof_two (x : Layer (Free I) 2) :
    exteriorLinearEquiv b (DirectSum.lof (ZMod 3) ℕ (Layer (Free I)) 2 x) =
      TruncatedExterior.ofTwo (sigmaTwo b x) := by
  apply TruncatedExterior.ext <;>
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

/-- The comparison inserts `σ₃` into the third homogeneous exterior summand.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLinearEquiv_lof_three (x : Layer (Free I) 3) :
    exteriorLinearEquiv b (DirectSum.lof (ZMod 3) ℕ (Layer (Free I)) 3 x) =
      TruncatedExterior.ofThree (sigmaThree b x) := by
  apply TruncatedExterior.ext <;>
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

/-- The comparison identifies each homogeneous subspace with the corresponding exterior degree.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/
theorem exteriorLinearEquiv_mem_grade_iff (n : ℕ) (x : GradedModule (Free I)) :
    exteriorLinearEquiv b x ∈ TruncatedExterior.grade V n ↔ x ∈ grade (Free I) n := by
  constructor
  · intro hx
    refine ⟨x n, ?_⟩
    apply (exteriorLinearEquiv b).injective
    apply TruncatedExterior.ext
    · by_cases h : n = 1
      · subst n
        simp
      · rw [hx.1 h]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, Ne.symm h]
    · by_cases h : n = 2
      · subst n
        simp
      · rw [hx.2.1 h]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, Ne.symm h]
    · by_cases h : n = 3
      · subst n
        simp
      · rw [hx.2.2 h]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, Ne.symm h]
  · rintro ⟨y, rfl⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, Ne.symm h]

/-- The direct sum of the three exterior identifications preserves the paper's signed bracket.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/
theorem exteriorLinearEquiv_map_bracket (x y : GradedModule (Free I)) :
    exteriorLinearEquiv b ⁅x, y⁆ = ⁅exteriorLinearEquiv b x, exteriorLinearEquiv b y⁆ := by
  apply TruncatedExterior.ext
  · rw [exteriorLinearEquiv_one, bracket_one, map_zero, TruncatedExterior.one_lie]
  · rw [exteriorLinearEquiv_two, bracket_two, sigmaTwo_bracketLayer, TruncatedExterior.two_lie,
      exteriorLinearEquiv_one, exteriorLinearEquiv_one]
  · rw [exteriorLinearEquiv_three, bracket_three, map_sub, sigmaThree_bracketLayer,
      sigmaThree_bracketLayer, TruncatedExterior.three_lie, exteriorLinearEquiv_two,
      exteriorLinearEquiv_one, exteriorLinearEquiv_two, exteriorLinearEquiv_one]

/-- The paper's Lie algebra isomorphism from the free group's actual associated graded to
the truncated exterior algebra of a vector space with the prescribed basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30. No finite-rank assumption is used.
-/
noncomputable def exteriorLieEquiv : GradedModule (Free I) ≃ₗ⁅ZMod 3⁆ TruncatedExterior V :=
  { exteriorLinearEquiv b with map_lie' := fun {x y} => exteriorLinearEquiv_map_bracket b x y }

/-- The Lie isomorphism is the direct sum of the three specified maps `σ₁`, `σ₂`, and `σ₃`.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem exteriorLieEquiv_apply (x : GradedModule (Free I)) :
    exteriorLieEquiv b x = exteriorLinearEquiv b x := rfl

/-- The exterior Lie isomorphism preserves and reflects the homogeneous degree.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/
theorem exteriorLieEquiv_mem_grade_iff (n : ℕ) (x : GradedModule (Free I)) :
    exteriorLieEquiv b x ∈ TruncatedExterior.grade V n ↔ x ∈ grade (Free I) n :=
  exteriorLinearEquiv_mem_grade_iff b n x

/-- The exterior Lie isomorphism maps each entire homogeneous subspace onto its counterpart.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`, and Remark 2.30.
-/
theorem exteriorLieEquiv_grade (n : ℕ) :
    (grade (Free I) n).map (exteriorLieEquiv b).toLinearEquiv.toLinearMap =
      TruncatedExterior.grade V n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (exteriorLieEquiv_mem_grade_iff b n x).mpr hx
  · intro hy
    refine ⟨(exteriorLieEquiv b).symm y, ?_, (exteriorLieEquiv b).apply_symm_apply y⟩
    apply (exteriorLieEquiv_mem_grade_iff b n _).mp
    simpa only [LieEquiv.apply_symm_apply] using hy

end T3.Free
