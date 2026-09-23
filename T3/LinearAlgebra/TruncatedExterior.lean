/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.LinearAlgebra.Wedge
public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Data.ZMod.Basic

/-!
# The truncated exterior Lie algebra in characteristic three

The underlying vector space is the product of the actual exterior powers in degrees one, two,
and three. Its bracket is the bilinear extension of exterior multiplication, with a minus sign
for the product of degree one with degree two. No dimension or basis is assumed.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9.
-/

@[expose] public section

namespace T3

open scoped ExteriorAlgebra DirectSum

variable (V : Type*) [AddCommGroup V] [Module (ZMod 3) V]

/-- The vector space `Λ¹V ⊕ Λ²V ⊕ Λ³V`, represented as a finite product.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
def TruncatedExterior := (⋀[ZMod 3]^1 V) × (⋀[ZMod 3]^2 V) × (⋀[ZMod 3]^3 V)

namespace TruncatedExterior

instance : AddCommGroup (TruncatedExterior V) :=
  inferInstanceAs (AddCommGroup ((⋀[ZMod 3]^1 V) × (⋀[ZMod 3]^2 V) × (⋀[ZMod 3]^3 V)))

instance : Module (ZMod 3) (TruncatedExterior V) :=
  inferInstanceAs (Module (ZMod 3) ((⋀[ZMod 3]^1 V) × (⋀[ZMod 3]^2 V) × (⋀[ZMod 3]^3 V)))

variable {V}

/-- The degree-one coordinate. -/
def one (x : TruncatedExterior V) : ⋀[ZMod 3]^1 V := x.1

/-- The degree-two coordinate. -/
def two (x : TruncatedExterior V) : ⋀[ZMod 3]^2 V := x.2.1

/-- The degree-three coordinate. -/
def three (x : TruncatedExterior V) : ⋀[ZMod 3]^3 V := x.2.2

@[simp]
theorem one_zero : one (0 : TruncatedExterior V) = 0 := rfl

@[simp]
theorem two_zero : two (0 : TruncatedExterior V) = 0 := rfl

@[simp]
theorem three_zero : three (0 : TruncatedExterior V) = 0 := rfl

@[simp]
theorem one_add (x y : TruncatedExterior V) : one (x + y) = one x + one y := rfl

@[simp]
theorem two_add (x y : TruncatedExterior V) : two (x + y) = two x + two y := rfl

@[simp]
theorem three_add (x y : TruncatedExterior V) : three (x + y) = three x + three y := rfl

@[simp]
theorem one_smul (r : ZMod 3) (x : TruncatedExterior V) : one (r • x) = r • one x := rfl

@[simp]
theorem two_smul (r : ZMod 3) (x : TruncatedExterior V) : two (r • x) = r • two x := rfl

@[simp]
theorem three_smul (r : ZMod 3) (x : TruncatedExterior V) : three (r • x) = r • three x := rfl

@[simp]
theorem one_neg (x : TruncatedExterior V) : one (-x) = -one x := rfl

@[simp]
theorem one_sub (x y : TruncatedExterior V) :
    one (x - y) = one x - one y := rfl

@[simp]
theorem two_neg (x : TruncatedExterior V) : two (-x) = -two x := rfl

@[simp]
theorem two_sub (x y : TruncatedExterior V) :
    two (x - y) = two x - two y := rfl

@[simp]
theorem three_neg (x : TruncatedExterior V) : three (-x) = -three x := rfl

@[simp]
theorem three_sub (x y : TruncatedExterior V) :
    three (x - y) = three x - three y := rfl

instance : Bracket (TruncatedExterior V) (TruncatedExterior V) where
  bracket x y := (0, gradedMul (one x) (one y),
    gradedMul (two x) (one y) - gradedMul (two y) (one x))

@[ext]
theorem ext {x y : TruncatedExterior V}
    (h₁ : one x = one y) (h₂ : two x = two y) (h₃ : three x = three y) : x = y :=
  Prod.ext h₁ (Prod.ext h₂ h₃)

@[simp]
theorem one_lie (x y : TruncatedExterior V) : one ⁅x, y⁆ = 0 := rfl

@[simp]
theorem two_lie (x y : TruncatedExterior V) : two ⁅x, y⁆ =
    gradedMul (one x) (one y) := rfl

@[simp]
theorem three_lie (x y : TruncatedExterior V) : three ⁅x, y⁆ =
    gradedMul (two x) (one y) - gradedMul (two y) (one x) := rfl

private theorem add_add_self (z : ⋀[ZMod 3]^3 V) : z + z + z = 0 := by
  have h : (1 + 1 + 1 : ZMod 3) = 0 := rfl
  have := congrArg (· • z) h
  simpa only [add_smul, _root_.one_smul, zero_smul] using this

/-- The paper's signed exterior bracket satisfies the Lie axioms.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
instance instLieRing : LieRing (TruncatedExterior V) where
  add_lie x y z := by
    apply ext <;> simp only [one_lie, two_lie, three_lie, one_add, two_add, three_add,
      gradedMul_add_left, gradedMul_add_right, add_zero]
    abel
  lie_add x y z := by
    apply ext <;> simp only [one_lie, two_lie, three_lie, one_add, two_add, three_add,
      gradedMul_add_left, gradedMul_add_right, add_zero]
    abel
  lie_self x := by
    apply ext <;> simp
  leibniz_lie x y z := by
    apply ext <;> simp only [one_lie, two_lie, three_lie, one_add, two_add, three_add,
      gradedMul_zero_left, gradedMul_zero_right, zero_sub, sub_zero, add_zero]
    rw [gradedMul_one_cyclic (one x) (one z) (one y), gradedMul_one_swap (one z) (one y)]
    have hneg : gradedMul (-gradedMul (one y) (one z)) (one x) =
        -gradedMul (gradedMul (one y) (one z)) (one x) := by
      apply Subtype.ext
      simp [neg_mul]
    rw [hneg, neg_neg, gradedMul_one_cyclic (one x) (one y) (one z)]
    have h := add_add_self (gradedMul (gradedMul (one y) (one z)) (one x))
    exact neg_eq_iff_add_eq_zero.mpr (by simpa [add_assoc] using h)

/-- The signed exterior bracket is bilinear over `𝔽₃`.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
instance instLieAlgebra : LieAlgebra (ZMod 3) (TruncatedExterior V) where
  lie_smul r x y := by
    apply ext <;> simp [gradedMul_smul_left, gradedMul_smul_right, smul_sub]

/-- The inclusion of the degree-one exterior power. -/
def ofOne : (⋀[ZMod 3]^1 V) →ₗ[ZMod 3] TruncatedExterior V where
  toFun a := (a, 0, 0)
  map_add' _ _ := ext rfl (zero_add _).symm (zero_add _).symm
  map_smul' r _ := ext rfl (smul_zero r).symm (smul_zero r).symm

/-- The inclusion of the degree-two exterior power. -/
def ofTwo : (⋀[ZMod 3]^2 V) →ₗ[ZMod 3] TruncatedExterior V where
  toFun a := (0, a, 0)
  map_add' _ _ := ext (zero_add _).symm rfl (zero_add _).symm
  map_smul' r _ := ext (smul_zero r).symm rfl (smul_zero r).symm

/-- The inclusion of the degree-three exterior power. -/
def ofThree : (⋀[ZMod 3]^3 V) →ₗ[ZMod 3] TruncatedExterior V where
  toFun a := (0, 0, a)
  map_add' _ _ := ext (zero_add _).symm (zero_add _).symm rfl
  map_smul' r _ := ext (smul_zero r).symm (smul_zero r).symm rfl

@[simp]
theorem one_ofOne (a : ⋀[ZMod 3]^1 V) : one (ofOne a) = a := rfl

@[simp]
theorem two_ofOne (a : ⋀[ZMod 3]^1 V) : two (ofOne a) = 0 := rfl

@[simp]
theorem three_ofOne (a : ⋀[ZMod 3]^1 V) : three (ofOne a) = 0 := rfl

@[simp]
theorem one_ofTwo (a : ⋀[ZMod 3]^2 V) : one (ofTwo a) = 0 := rfl

@[simp]
theorem two_ofTwo (a : ⋀[ZMod 3]^2 V) : two (ofTwo a) = a := rfl

@[simp]
theorem three_ofTwo (a : ⋀[ZMod 3]^2 V) : three (ofTwo a) = 0 := rfl

@[simp]
theorem one_ofThree (a : ⋀[ZMod 3]^3 V) : one (ofThree a) = 0 := rfl

@[simp]
theorem two_ofThree (a : ⋀[ZMod 3]^3 V) : two (ofThree a) = 0 := rfl

@[simp]
theorem three_ofThree (a : ⋀[ZMod 3]^3 V) : three (ofThree a) = a := rfl

/-- The bracket of degree-one elements is their exterior product.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
@[simp]
theorem ofOne_lie_ofOne (a b : ⋀[ZMod 3]^1 V) :
    ⁅ofOne a, ofOne b⁆ = ofTwo (gradedMul a b) := by ext <;> simp

/-- The bracket in degrees two and one is their exterior product.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
@[simp]
theorem ofTwo_lie_ofOne (q : ⋀[ZMod 3]^2 V) (a : ⋀[ZMod 3]^1 V) :
    ⁅ofTwo q, ofOne a⁆ = ofThree (gradedMul q a) := by ext <;> simp

/-- The bracket in degrees one and two is the negative exterior product.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
@[simp]
theorem ofOne_lie_ofTwo (a : ⋀[ZMod 3]^1 V) (q : ⋀[ZMod 3]^2 V) :
    ⁅ofOne a, ofTwo q⁆ = ofThree (-gradedMul a q) := by
  apply ext <;> simp [gradedMul_one_two_comm]

/-- Degree-three elements have zero bracket with every element. -/
@[simp]
theorem ofThree_lie (a : ⋀[ZMod 3]^3 V) (x : TruncatedExterior V) :
    ⁅ofThree a, x⁆ = 0 := by ext <;> simp

/-- Every element has zero bracket with degree-three elements. -/
@[simp]
theorem lie_ofThree (x : TruncatedExterior V) (a : ⋀[ZMod 3]^3 V) :
    ⁅x, ofThree a⁆ = 0 := by ext <;> simp

/-- Two degree-two elements have zero bracket. -/
@[simp]
theorem ofTwo_lie_ofTwo (a b : ⋀[ZMod 3]^2 V) :
    ⁅ofTwo a, ofTwo b⁆ = 0 := by ext <;> simp

/-- A triple bracket is the triple exterior product of the degree-one coordinates.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
theorem triple_lie (x y z : TruncatedExterior V) :
    ⁅⁅x, y⁆, z⁆ = ofThree (gradedMul (gradedMul (one x) (one y)) (one z)) := by
  apply ext <;> simp only [one_lie, two_lie, three_lie, one_ofThree, two_ofThree,
    three_ofThree, gradedMul_zero_left, gradedMul_zero_right, sub_zero]

/-- Triple brackets are invariant under cyclic permutation.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
theorem triple_lie_cyclic (x y z : TruncatedExterior V) : ⁅⁅x, y⁆, z⁆ = ⁅⁅y, z⁆, x⁆ := by
  rw [triple_lie, triple_lie, gradedMul_one_cyclic]

/-- A triple bracket with its last two arguments equal vanishes.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
theorem triple_lie_repeat (x y : TruncatedExterior V) : ⁅⁅x, y⁆, y⁆ = 0 := by
  rw [triple_lie, gradedMul_one_repeat, map_zero]

/-- Every bracket of length four vanishes.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
theorem quadruple_lie (x y z w : TruncatedExterior V) : ⁅⁅⁅x, y⁆, z⁆, w⁆ = 0 := by
  rw [triple_lie x y z, ofThree_lie]

/-- Every element is the sum of its three homogeneous components. -/
theorem ofOne_add_ofTwo_add_ofThree (x : TruncatedExterior V) :
    ofOne (one x) + ofTwo (two x) + ofThree (three x) = x := by ext <;> simp

variable (V)

/-- The homogeneous submodule of degree `n`, zero outside degrees one, two, and three.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
def grade (n : ℕ) : Submodule (ZMod 3) (TruncatedExterior V) where
  carrier := {x | (n ≠ 1 → one x = 0) ∧ (n ≠ 2 → two x = 0) ∧ (n ≠ 3 → three x = 0)}
  zero_mem' := by simp
  add_mem' hx hy := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp [hx.1 h, hy.1 h]
    · simp [hx.2.1 h, hy.2.1 h]
    · simp [hx.2.2 h, hy.2.2 h]
  smul_mem' r _ hx := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp [hx.1 h]
    · simp [hx.2.1 h]
    · simp [hx.2.2 h]

variable {V}

/-- Membership in a homogeneous component means that all other coordinates vanish. -/
theorem mem_grade {n : ℕ} {x : TruncatedExterior V} : x ∈ grade V n ↔
    (n ≠ 1 → one x = 0) ∧ (n ≠ 2 → two x = 0) ∧ (n ≠ 3 → three x = 0) := Iff.rfl

/-- The degree-one component has zero degree-two and degree-three coordinates. -/
@[simp]
theorem mem_grade_one {x : TruncatedExterior V} :
    x ∈ grade V 1 ↔ two x = 0 ∧ three x = 0 := by simp [mem_grade]

/-- The degree-two component has zero degree-one and degree-three coordinates. -/
@[simp]
theorem mem_grade_two {x : TruncatedExterior V} :
    x ∈ grade V 2 ↔ one x = 0 ∧ three x = 0 := by simp [mem_grade]

/-- The degree-three component has zero degree-one and degree-two coordinates. -/
@[simp]
theorem mem_grade_three {x : TruncatedExterior V} :
    x ∈ grade V 3 ↔ one x = 0 ∧ two x = 0 := by simp [mem_grade]

/-- The homogeneous component is zero outside degrees one, two, and three. -/
@[simp]
theorem grade_eq_bot {n : ℕ} (h₁ : n ≠ 1) (h₂ : n ≠ 2) (h₃ : n ≠ 3) :
    grade V n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  exact ext (hx.1 h₁) (hx.2.1 h₂) (hx.2.2 h₃)

/-- The signed exterior bracket respects the homogeneous degrees. -/
instance instGradedBracket : SetLike.GradedBracket (grade V) (grade V) where
  bracket_mem {i j} {x y} hx hy := by
    change ⁅x, y⁆ ∈ grade V (i + j)
    refine ⟨fun _ => one_lie x y, fun h => ?_, fun h => ?_⟩
    · by_cases hi : i = 1
      · have hj : j ≠ 1 := by omega
        simp [hy.1 hj]
      · simp [hx.1 hi]
    · have h₁ : gradedMul (two x) (one y) = 0 := by
        by_cases hi : i = 2
        · have hj : j ≠ 1 := by omega
          simp [hy.1 hj]
        · simp [hx.2.1 hi]
      have h₂ : gradedMul (two y) (one x) = 0 := by
        by_cases hj : j = 2
        · have hi : i ≠ 1 := by omega
          simp [hx.1 hi]
        · simp [hy.2.1 hj]
      simp [h₁, h₂]

/-- The degree-one component, with its membership in the homogeneous submodule. -/
def componentOne : TruncatedExterior V →ₗ[ZMod 3] grade V 1 where
  toFun x := ⟨ofOne (one x), by simp⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- The degree-two component, with its membership in the homogeneous submodule. -/
def componentTwo : TruncatedExterior V →ₗ[ZMod 3] grade V 2 where
  toFun x := ⟨ofTwo (two x), by simp⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- The degree-three component, with its membership in the homogeneous submodule. -/
def componentThree : TruncatedExterior V →ₗ[ZMod 3] grade V 3 where
  toFun x := ⟨ofThree (three x), by simp⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- The explicit decomposition into the three homogeneous components. -/
def decompositionMap : TruncatedExterior V →ₗ[ZMod 3] ⨁ n : ℕ, grade V n :=
  (DirectSum.lof (ZMod 3) ℕ (fun n => grade V n) 1).comp componentOne +
    (DirectSum.lof (ZMod 3) ℕ (fun n => grade V n) 2).comp componentTwo +
    (DirectSum.lof (ZMod 3) ℕ (fun n => grade V n) 3).comp componentThree

private theorem decompositionMap_left_inv :
    DirectSum.coeLinearMap (grade V) ∘ₗ decompositionMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simpa [decompositionMap, componentOne, componentTwo, componentThree] using
    ofOne_add_ofTwo_add_ofThree x

private theorem decompositionMap_coe (n : ℕ) (x : grade V n) :
    decompositionMap (x : TruncatedExterior V) =
      DirectSum.lof (ZMod 3) ℕ (fun n => grade V n) n x := by
  have hz (i : ℕ) (h : (0 : TruncatedExterior V) ∈ grade V i) :
      (⟨0, h⟩ : grade V i) = 0 := rfl
  by_cases h₁ : n = 1
  · subst n
    obtain ⟨h₂, h₃⟩ := mem_grade_one.mp x.property
    have hx : ofOne (one (x : TruncatedExterior V)) = (x : TruncatedExterior V) := by
      apply ext <;> simp [h₂, h₃]
    simp [decompositionMap, componentOne, componentTwo, componentThree, h₂, h₃, hx, hz]
  by_cases h₂ : n = 2
  · subst n
    obtain ⟨h₁, h₃⟩ := mem_grade_two.mp x.property
    have hx : ofTwo (two (x : TruncatedExterior V)) = (x : TruncatedExterior V) := by
      apply ext <;> simp [h₁, h₃]
    simp [decompositionMap, componentOne, componentTwo, componentThree, h₁, h₃, hx, hz]
  by_cases h₃ : n = 3
  · subst n
    obtain ⟨h₁, h₂⟩ := mem_grade_three.mp x.property
    have hx : ofThree (three (x : TruncatedExterior V)) = (x : TruncatedExterior V) := by
      apply ext <;> simp [h₁, h₂]
    simp [decompositionMap, componentOne, componentTwo, componentThree, h₁, h₂, hx, hz]
  have hx : x = 0 := Subtype.ext (ext (x.property.1 h₁)
    (x.property.2.1 h₂) (x.property.2.2 h₃))
  rw [hx]
  simp

private theorem decompositionMap_right_inv :
    decompositionMap ∘ₗ DirectSum.coeLinearMap (grade V) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp [decompositionMap_coe]

/-- The homogeneous components form an internal direct sum. -/
instance instDecomposition : DirectSum.Decomposition (grade V) := by
  exact DirectSum.Decomposition.ofLinearMap (grade V) decompositionMap
    (by exact decompositionMap_left_inv) (by exact decompositionMap_right_inv)

/-- The paper's truncated exterior algebra is an internally graded Lie algebra over `𝔽₃`.

Paper-ID: linear_algebra.truncated_exterior
TeX: T3_modelcompanion_v8.tex, `example:Grassmann algebra`, v8 Example 2.9. -/
instance instGradedLieAlgebra : GradedLieAlgebra (grade V) where

end TruncatedExterior

end T3
