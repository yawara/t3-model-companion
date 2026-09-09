/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded.Lie

/-!
# Truncating the associated graded at degree three

For a group of exponent three, only degrees one, two and three contribute to the associated
graded. This file gives the canonical linear equivalence from the direct sum of the actual
central quotients to the finite product of those three quotients. It is used to assemble
the three maps in the paper's exterior description of a free group's associated graded.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.19(1) and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.
-/

@[expose] public section

open scoped DirectSum

namespace T3.AssociatedGraded

variable (G : Type*) [Group G] [Fact (HasExponentThree G)]

/-- The associated graded is the product of its three possibly nonzero components.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.19(1) and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.
-/
def truncationEquiv : GradedModule G ≃ₗ[ZMod 3] Layer G 1 × Layer G 2 × Layer G 3 where
  toFun x := (x 1, x 2, x 3)
  invFun x := DirectSum.lof (ZMod 3) ℕ (Layer G) 1 x.1 +
    DirectSum.lof (ZMod 3) ℕ (Layer G) 2 x.2.1 + DirectSum.lof (ZMod 3) ℕ (Layer G) 3 x.2.2
  left_inv x := by
    apply DFinsupp.ext
    intro n
    by_cases h₁ : n = 1
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    by_cases h₂ : n = 2
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    by_cases h₃ : n = 3
    · subst n
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subsingleton.elim _ _
    · haveI := layer_subsingleton_of_four_le (G := G) Fact.out (show 4 ≤ n by omega)
      exact Subsingleton.elim _ _
  right_inv x := by
    apply Prod.ext
    · simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    · apply Prod.ext <;> simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Truncation reads the three homogeneous coordinates.

Paper-ID: preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v4.tex, v4 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem truncationEquiv_apply (x : GradedModule G) : truncationEquiv G x = (x 1, x 2, x 3) := rfl

/-- The inverse truncation inserts the three homogeneous coordinates into the direct sum.

Paper-ID: preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v4.tex, v4 Proposition 2.29, `proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem truncationEquiv_symm_apply (x : Layer G 1 × Layer G 2 × Layer G 3) :
    (truncationEquiv G).symm x = DirectSum.lof (ZMod 3) ℕ (Layer G) 1 x.1 +
      DirectSum.lof (ZMod 3) ℕ (Layer G) 2 x.2.1 + DirectSum.lof (ZMod 3) ℕ (Layer G) 3 x.2.2 := rfl

/-- The degree-three coordinate of a bracket is the sum of its two mixed-degree terms.

Paper-ID: preliminaries.associated_graded_properties, preliminaries.free_graded_equiv
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.19 and Proposition 2.29,
`proposition:gr(F) is Grassmann algebra`.
-/
@[simp]
theorem bracket_three (x y : GradedModule G) :
    ⁅x, y⁆ 3 = bracketLayer (by decide) (by decide) (x 2) (y 1) -
      bracketLayer (by decide) (by decide) (y 2) (x 1) := by
  simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

end T3.AssociatedGraded
