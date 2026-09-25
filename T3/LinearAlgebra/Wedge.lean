/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Wedge multiplication between exterior powers

The truncated exterior Lie algebra in the paper uses the two bilinear maps

`V × V → ⋀²V`  and  `⋀²V × V → ⋀³V`.

mathlib defines `⋀[R]^n M` as a submodule of the exterior algebra rather than as a quotient, and
`Mathlib/LinearAlgebra/ExteriorAlgebra/Grading.lean` shows those submodules form a graded monoid.
So both maps come from the algebra product together with `SetLike.mul_mem_graded`; no alternating
map has to be built by hand.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v9.tex, `example:Grassmann algebra`, v9 Example 2.9.

## Main definitions

* `gradedMul`: the product of an element of `⋀[R]^i M` and one of `⋀[R]^j M`, in `⋀[R]^(i + j) M`;
* `wedgeVV`: `V × V → ⋀²V`;
* `wedgeQV`: `⋀²V × V → ⋀³V`.
-/

@[expose] public section

namespace T3

open scoped ExteriorAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The product of an element of `⋀[R]^i M` and one of `⋀[R]^j M`, landing in `⋀[R]^(i + j) M`. -/
def gradedMul {i j : ℕ} (a : ⋀[R]^i M) (b : ⋀[R]^j M) : ⋀[R]^(i + j) M :=
  ⟨(a : ExteriorAlgebra R M) * (b : ExteriorAlgebra R M), SetLike.mul_mem_graded a.2 b.2⟩

@[simp]
theorem gradedMul_coe {i j : ℕ} (a : ⋀[R]^i M) (b : ⋀[R]^j M) :
    (gradedMul a b : ExteriorAlgebra R M) = (a : ExteriorAlgebra R M) * b :=
  rfl

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The exterior-power functor is the restriction of the induced exterior-algebra map. -/
theorem exteriorPower_map_coe (f : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^n M) :
    (exteriorPower.map n f x : ExteriorAlgebra R N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra R M) := by
  let a := (⋀[R]^n N).subtype.comp (exteriorPower.map n f)
  let b := (ExteriorAlgebra.map f).toLinearMap.comp (⋀[R]^n M).subtype
  have hab : a = b := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (exteriorPower.map n f (exteriorPower.ιMulti R n v) : ExteriorAlgebra R N) =
      ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti R n v)
    simp only [exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.map_apply_ιMulti]
  exact DFunLike.congr_fun hab x

/-- Exterior multiplication commutes with the maps induced by a linear map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, natural exterior decomposition.
-/
theorem exteriorPower_map_gradedMul (f : M →ₗ[R] N) {i j : ℕ}
    (a : ⋀[R]^i M) (b : ⋀[R]^j M) :
    exteriorPower.map (i + j) f (gradedMul a b) =
      gradedMul (exteriorPower.map i f a) (exteriorPower.map j f b) := by
  apply Subtype.ext
  simp only [exteriorPower_map_coe, gradedMul_coe, map_mul]

/-- The degree-one exterior identification commutes with every linear map. -/
theorem exteriorPower_map_oneEquiv_symm (f : M →ₗ[R] N) (v : M) :
    exteriorPower.map 1 f ((exteriorPower.oneEquiv R M).symm v) =
      (exteriorPower.oneEquiv R N).symm (f v) := by
  apply (exteriorPower.oneEquiv R N).injective
  have h := DFunLike.congr_fun (exteriorPower.oneEquiv_naturality f)
    ((exteriorPower.oneEquiv R M).symm v)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h

theorem gradedMul_add_left {i j : ℕ} (a a' : ⋀[R]^i M) (b : ⋀[R]^j M) :
    gradedMul (a + a') b = gradedMul a b + gradedMul a' b :=
  Subtype.ext (by simp [add_mul])

theorem gradedMul_add_right {i j : ℕ} (a : ⋀[R]^i M) (b b' : ⋀[R]^j M) :
    gradedMul a (b + b') = gradedMul a b + gradedMul a b' :=
  Subtype.ext (by simp [mul_add])

theorem gradedMul_smul_left {i j : ℕ} (r : R) (a : ⋀[R]^i M) (b : ⋀[R]^j M) :
    gradedMul (r • a) b = r • gradedMul a b :=
  Subtype.ext (by simp)

theorem gradedMul_smul_right {i j : ℕ} (r : R) (a : ⋀[R]^i M) (b : ⋀[R]^j M) :
    gradedMul a (r • b) = r • gradedMul a b :=
  Subtype.ext (by simp)

variable (R M) in
/-- The bilinear map `M × M → ⋀[R]^2 M`. -/
noncomputable def wedgeVV : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun u v => gradedMul ((exteriorPower.oneEquiv R M).symm u)
      ((exteriorPower.oneEquiv R M).symm v))
    (fun u u' v => by rw [map_add, gradedMul_add_left])
    (fun r u v => by rw [map_smul, gradedMul_smul_left])
    (fun u v v' => by rw [map_add, gradedMul_add_right])
    (fun r u v => by rw [map_smul, gradedMul_smul_right])

variable (R M) in
/-- The bilinear map `⋀[R]^2 M × M → ⋀[R]^3 M`. -/
noncomputable def wedgeQV : ⋀[R]^2 M →ₗ[R] M →ₗ[R] ⋀[R]^3 M :=
  LinearMap.mk₂ R (fun q v => gradedMul q ((exteriorPower.oneEquiv R M).symm v))
    (fun q q' v => gradedMul_add_left q q' _)
    (fun r q v => gradedMul_smul_left r q _)
    (fun q v v' => by rw [map_add, gradedMul_add_right])
    (fun r q v => by rw [map_smul, gradedMul_smul_right])

/-- The coercion of `(oneEquiv R M).symm m` into the exterior algebra is `ι R m`. -/
theorem oneEquiv_symm_coe (m : M) :
    (((exteriorPower.oneEquiv R M).symm m : ⋀[R]^1 M) : ExteriorAlgebra R M)
      = ExteriorAlgebra.ι R m := by
  simp [exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply]

@[simp]
theorem wedgeVV_self (v : M) : wedgeVV R M v v = 0 := by
  refine Subtype.ext ?_
  simp only [wedgeVV, LinearMap.mk₂_apply, gradedMul_coe, oneEquiv_symm_coe,
    ExteriorAlgebra.ι_sq_zero]
  rfl

/--
The triple wedge is invariant under cyclic permutation. In characteristic three, this
identity yields the Jacobi identity for the truncated exterior Lie bracket.
-/
theorem wedgeQV_wedgeVV_cyclic (u v w : M) :
    wedgeQV R M (wedgeVV R M u v) w = wedgeQV R M (wedgeVV R M v w) u := by
  refine Subtype.ext ?_
  simp only [wedgeQV, wedgeVV, LinearMap.mk₂_apply, gradedMul_coe, oneEquiv_symm_coe]
  have h1 : ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u
      = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w) := by
    exact eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap (R := R) u w)
  have h2 : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u
      = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) := by
    exact eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap (R := R) u v)
  calc ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w
      = -(-(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) * ExteriorAlgebra.ι R w) := by
        rw [neg_mul, neg_neg]
    _ = -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w) := by rw [h2]
    _ = -(ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w)) := by
        rw [mul_assoc]
    _ = ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u) := by
        rw [h1, mul_neg]
    _ = ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u := by rw [mul_assoc]

/-- Multiplication by a zero exterior form vanishes. -/
@[simp]
theorem gradedMul_zero_left {i j : ℕ} (b : ⋀[R]^j M) :
    gradedMul (0 : ⋀[R]^i M) b = 0 := Subtype.ext (by simp)

/-- Multiplication with a zero exterior form vanishes. -/
@[simp]
theorem gradedMul_zero_right {i j : ℕ} (a : ⋀[R]^i M) :
    gradedMul a (0 : ⋀[R]^j M) = 0 := Subtype.ext (by simp)

/-- A degree-one exterior form has square zero. -/
@[simp]
theorem gradedMul_one_self (a : ⋀[R]^1 M) : gradedMul a a = 0 := by
  obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective a
  exact wedgeVV_self v

/-- Triple products of degree-one exterior forms are invariant under cyclic permutation. -/
theorem gradedMul_one_cyclic (a b c : ⋀[R]^1 M) :
    gradedMul (gradedMul a b) c = gradedMul (gradedMul b c) a := by
  obtain ⟨u, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective a
  obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective b
  obtain ⟨w, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective c
  exact wedgeQV_wedgeVV_cyclic u v w

/-- A triple exterior product with its last two arguments equal vanishes. -/
@[simp]
theorem gradedMul_one_repeat (a b : ⋀[R]^1 M) :
    gradedMul (gradedMul a b) b = 0 := by
  rw [gradedMul_one_cyclic, gradedMul_one_self, gradedMul_zero_left]

/-- Degree-one exterior forms anticommute. -/
theorem gradedMul_one_swap (a b : ⋀[R]^1 M) : gradedMul a b = -gradedMul b a := by
  have h := gradedMul_one_self (a + b)
  rw [gradedMul_add_left, gradedMul_add_right, gradedMul_add_right,
    gradedMul_one_self, gradedMul_one_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Degree-one and degree-two exterior forms commute. -/
theorem gradedMul_one_two_comm (a : ⋀[R]^1 M) (q : ⋀[R]^2 M) :
    gradedMul a q = gradedMul q a := by
  have hq : q ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨f, rfl⟩ := hq
    obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective a
    apply Subtype.ext
    simp only [gradedMul_coe, oneEquiv_symm_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, mul_one]
    have h (x y : M) : ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y =
        -(ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R x) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) x y)
    rw [← mul_assoc, h v (f 0), neg_mul, mul_assoc, h v (f (Fin.succ 0)), mul_neg, neg_neg]
    rw [mul_assoc]
  | zero => simp
  | add q r _ _ hq hr => rw [gradedMul_add_right, gradedMul_add_left, hq, hr]
  | smul r q _ hq => rw [gradedMul_smul_right, gradedMul_smul_left, hq]

end T3
