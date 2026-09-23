/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.LinearAlgebra.ExteriorTensor
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The exterior sum decomposition in degrees two and three

The finite direct sum of exterior tensor blocks is identified with the right-associated
products appearing in the paper. Exterior degrees zero and one are identified with the
coefficient ring and the original module. Recomposition uses the pure inclusions and ordinary
exterior multiplication on each mixed tensor block. In particular, both mixed blocks in degree
three have positive signs here; the sign in the degree-one by degree-two Lie bracket is separate.

The bases may have arbitrary cardinality, and the coefficient ring is any commutative ring.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, lines 969–973.
-/

@[expose] public section

open scoped ExteriorAlgebra DirectSum TensorProduct
open Module

namespace T3.ExteriorLowDegree

variable {R V W I J : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- List three dependent components in decreasing order of their indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, degree two blocks.
-/
def piThreeEquiv (M : Fin 3 → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] : (∀ i, M i) ≃ₗ[R] M 2 × M 1 × M 0 where
  toFun f := (f 2, f 1, f 0)
  invFun z := Fin.cases z.2.2 (Fin.cases z.2.1 (Fin.cases z.1 (fun i => Fin.elim0 i)))
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- List four dependent components in decreasing order of their indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, degree three blocks.
-/
def piFourEquiv (M : Fin 4 → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] : (∀ i, M i) ≃ₗ[R] M 3 × M 2 × M 1 × M 0 where
  toFun f := (f 3, f 2, f 1, f 0)
  invFun z := Fin.cases z.2.2.2 (Fin.cases z.2.2.1 (Fin.cases z.2.1
    (Fin.cases z.1 (fun i => Fin.elim0 i))))
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Remove the exterior degree-zero factor on the left of a tensor product.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, pure exterior blocks.
-/
noncomputable def zeroLeftEquiv (n : ℕ) :
    ((⋀[R]^0 V) ⊗[R] (⋀[R]^n W)) ≃ₗ[R] ⋀[R]^n W :=
  (TensorProduct.congr (exteriorPower.zeroEquiv R V) (LinearEquiv.refl R _)).trans
    (TensorProduct.lid R _)

/-- Remove the exterior degree-zero factor on the right of a tensor product.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, pure exterior blocks.
-/
noncomputable def zeroRightEquiv (n : ℕ) :
    ((⋀[R]^n V) ⊗[R] (⋀[R]^0 W)) ≃ₗ[R] ⋀[R]^n V :=
  (TensorProduct.congr (LinearEquiv.refl R _) (exteriorPower.zeroEquiv R W)).trans
    (TensorProduct.rid R _)

private theorem zeroEquiv_symm_one_coe (M : Type*) [AddCommGroup M] [Module R M] :
    ((exteriorPower.zeroEquiv R M).symm 1 : ExteriorAlgebra R M) = 1 := by
  simp [exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe]

private theorem dsThree_symm (M : Fin 3 → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (z : M 2 × M 1 × M 0) :
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm ((piThreeEquiv (R := R) M).symm z) =
      DirectSum.lof R _ M 2 z.1 + DirectSum.lof R _ M 1 z.2.1 +
        DirectSum.lof R _ M 0 z.2.2 := by
  apply DFinsupp.ext
  intro i
  fin_cases i <;>
    simp [piThreeEquiv, DFinsupp.equivFunOnFintype, DirectSum.lof_eq_of, DirectSum.of_apply] <;> rfl

private theorem dsFour_symm (M : Fin 4 → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (z : M 3 × M 2 × M 1 × M 0) :
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm ((piFourEquiv (R := R) M).symm z) =
      DirectSum.lof R _ M 3 z.1 + DirectSum.lof R _ M 2 z.2.1 +
        DirectSum.lof R _ M 1 z.2.2.1 + DirectSum.lof R _ M 0 z.2.2.2 := by
  apply DFinsupp.ext
  intro i
  fin_cases i <;>
    simp [piFourEquiv, DFinsupp.equivFunOnFintype, DirectSum.lof_eq_of, DirectSum.of_apply] <;> rfl

private theorem tensorEquiv_symm_lof [LinearOrder I] [LinearOrder J]
    (b : Basis I R V) (c : Basis J R W) (n : ℕ) (k : Fin (n + 1))
    (z : ExteriorTensor.TensorBlock R V W n k) :
    (ExteriorTensor.tensorEquiv b c n).symm (DirectSum.lof R _ _ k z) =
      ExteriorTensor.wedgeMap R V W n k z :=
  DFunLike.congr_fun (ExteriorTensor.tensorEquiv_symm_comp_lof b c n k) z

private theorem wedgeMap_zero (n : ℕ) (q : ⋀[R]^n W) :
    ExteriorTensor.wedgeMap R V W n 0 ((zeroLeftEquiv (V := V) n).symm q) =
      exteriorPower.map n (LinearMap.inr R V W) q := by
  apply Subtype.ext
  change (exteriorPower.map 0 (LinearMap.inl R V W)
    ((exteriorPower.zeroEquiv R V).symm 1) : ExteriorAlgebra R (V × W)) *
    (exteriorPower.map n (LinearMap.inr R V W) q : ExteriorAlgebra R (V × W)) = _
  simp only [exteriorPower_map_coe, zeroEquiv_symm_one_coe, map_one, one_mul]

private theorem wedgeMap_last_two (q : ⋀[R]^2 V) :
    ExteriorTensor.wedgeMap R V W 2 2 ((zeroRightEquiv (W := W) 2).symm q) =
      exteriorPower.map 2 (LinearMap.inl R V W) q := by
  apply Subtype.ext
  change (exteriorPower.map 2 (LinearMap.inl R V W) q : ExteriorAlgebra R (V × W)) *
    (exteriorPower.map 0 (LinearMap.inr R V W)
      ((exteriorPower.zeroEquiv R W).symm 1) : ExteriorAlgebra R (V × W)) = _
  simp only [exteriorPower_map_coe, zeroEquiv_symm_one_coe, map_one, mul_one]

private theorem wedgeMap_last_three (q : ⋀[R]^3 V) :
    ExteriorTensor.wedgeMap R V W 3 3 ((zeroRightEquiv (W := W) 3).symm q) =
      exteriorPower.map 3 (LinearMap.inl R V W) q := by
  apply Subtype.ext
  change (exteriorPower.map 3 (LinearMap.inl R V W) q : ExteriorAlgebra R (V × W)) *
    (exteriorPower.map 0 (LinearMap.inr R V W)
      ((exteriorPower.zeroEquiv R W).symm 1) : ExteriorAlgebra R (V × W)) = _
  simp only [exteriorPower_map_coe, zeroEquiv_symm_one_coe, map_one, mul_one]

variable (R V W) in
/-- Include a tensor of vectors by exterior multiplication, with the left factor first.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree two decomposition.
-/
noncomputable def mixedTwoMap : V ⊗[R] W →ₗ[R] ⋀[R]^2 (V × W) :=
  (ExteriorTensor.wedgeMap R V W 2 1).comp
    (TensorProduct.congr (exteriorPower.oneEquiv R V).symm
      (exteriorPower.oneEquiv R W).symm).toLinearMap

variable (R V W) in
/-- Include the mixed tensor of a left two-form and a right vector by exterior multiplication.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
noncomputable def mixedTwoOneMap : (⋀[R]^2 V) ⊗[R] W →ₗ[R] ⋀[R]^3 (V × W) :=
  (ExteriorTensor.wedgeMap R V W 3 2).comp
    (TensorProduct.congr (LinearEquiv.refl R _) (exteriorPower.oneEquiv R W).symm).toLinearMap

variable (R V W) in
/-- Include the mixed tensor of a left vector and a right two-form by exterior multiplication.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
noncomputable def mixedOneTwoMap : V ⊗[R] (⋀[R]^2 W) →ₗ[R] ⋀[R]^3 (V × W) :=
  (ExteriorTensor.wedgeMap R V W 3 1).comp
    (TensorProduct.congr (exteriorPower.oneEquiv R V).symm (LinearEquiv.refl R _)).toLinearMap

/-- On a pure tensor the mixed degree-two map is the usual wedge of the included vectors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree two decomposition.
-/
theorem mixedTwoMap_tmul (v : V) (w : W) :
    mixedTwoMap R V W (v ⊗ₜ[R] w) =
      gradedMul (exteriorPower.map 1 (LinearMap.inl R V W)
        ((exteriorPower.oneEquiv R V).symm v))
        (exteriorPower.map 1 (LinearMap.inr R V W)
          ((exteriorPower.oneEquiv R W).symm w)) := rfl

/-- On a pure tensor the left degree-two mixed map is the usual wedge, with positive sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
theorem mixedTwoOneMap_tmul (q : ⋀[R]^2 V) (w : W) :
    mixedTwoOneMap R V W (q ⊗ₜ[R] w) =
      gradedMul (exteriorPower.map 2 (LinearMap.inl R V W) q)
        (exteriorPower.map 1 (LinearMap.inr R V W)
          ((exteriorPower.oneEquiv R W).symm w)) := rfl

/-- On a pure tensor the right degree-two mixed map is the usual wedge, with positive sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
theorem mixedOneTwoMap_tmul (v : V) (q : ⋀[R]^2 W) :
    mixedOneTwoMap R V W (v ⊗ₜ[R] q) =
      gradedMul (exteriorPower.map 1 (LinearMap.inl R V W)
        ((exteriorPower.oneEquiv R V).symm v))
        (exteriorPower.map 2 (LinearMap.inr R V W) q) := rfl

variable (R V W) in
/-- Recompose the three degree-two components by the pure inclusions and the mixed wedge map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree two decomposition.
-/
noncomputable def twoMap :
    (⋀[R]^2 V) × (V ⊗[R] W) × (⋀[R]^2 W) →ₗ[R] ⋀[R]^2 (V × W) :=
  (exteriorPower.map 2 (LinearMap.inl R V W)).coprod
    ((mixedTwoMap R V W).coprod (exteriorPower.map 2 (LinearMap.inr R V W)))

variable (R V W) in
/-- Recompose the four degree-three components by the pure inclusions and the mixed wedge maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
noncomputable def threeMap :
    (⋀[R]^3 V) × ((⋀[R]^2 V) ⊗[R] W) × (V ⊗[R] (⋀[R]^2 W)) × (⋀[R]^3 W) →ₗ[R]
      ⋀[R]^3 (V × W) :=
  (exteriorPower.map 3 (LinearMap.inl R V W)).coprod
    ((mixedTwoOneMap R V W).coprod
      ((mixedOneTwoMap R V W).coprod (exteriorPower.map 3 (LinearMap.inr R V W))))

/-- Simplify and reorder the three exterior tensor blocks in degree two.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, degree two blocks.
-/
noncomputable def twoBlocksEquiv :
    (⨁ k : Fin 3, ExteriorTensor.TensorBlock R V W 2 k) ≃ₗ[R]
      (⋀[R]^2 V) × (V ⊗[R] W) × (⋀[R]^2 W) :=
  (DFinsupp.linearEquivFunOnFintype (R := R)).trans <|
    (piThreeEquiv (R := R) (ExteriorTensor.TensorBlock R V W 2)).trans <|
    (zeroRightEquiv 2).prodCongr
      ((TensorProduct.congr (exteriorPower.oneEquiv R V)
        (exteriorPower.oneEquiv R W)).prodCongr (zeroLeftEquiv 2))

/-- Simplify and reorder the four exterior tensor blocks in degree three.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, supporting `proposition:gr of free product`, degree three blocks.
-/
noncomputable def threeBlocksEquiv :
    (⨁ k : Fin 4, ExteriorTensor.TensorBlock R V W 3 k) ≃ₗ[R]
      (⋀[R]^3 V) × ((⋀[R]^2 V) ⊗[R] W) × (V ⊗[R] (⋀[R]^2 W)) × (⋀[R]^3 W) :=
  (DFinsupp.linearEquivFunOnFintype (R := R)).trans <|
    (piFourEquiv (R := R) (ExteriorTensor.TensorBlock R V W 3)).trans <|
    (zeroRightEquiv 3).prodCongr
      ((TensorProduct.congr (LinearEquiv.refl R _) (exteriorPower.oneEquiv R W)).prodCongr
        ((TensorProduct.congr (exteriorPower.oneEquiv R V) (LinearEquiv.refl R _)).prodCongr
          (zeroLeftEquiv 3)))

variable [LinearOrder I] [LinearOrder J] (b : Basis I R V) (c : Basis J R W)

/-- The degree-two exterior sum decomposition, with the paper's right-associated product.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, lines 969–973.
-/
noncomputable def twoEquiv :
    ((⋀[R]^2 V) × (V ⊗[R] W) × (⋀[R]^2 W)) ≃ₗ[R] ⋀[R]^2 (V × W) :=
  (twoBlocksEquiv (R := R) (V := V) (W := W)).symm.trans
    (ExteriorTensor.tensorEquiv b c 2).symm

/-- The degree-three exterior sum decomposition, with both mixed wedge components positive.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, lines 969–973.
-/
noncomputable def threeEquiv :
    ((⋀[R]^3 V) × ((⋀[R]^2 V) ⊗[R] W) × (V ⊗[R] (⋀[R]^2 W)) × (⋀[R]^3 W)) ≃ₗ[R]
      ⋀[R]^3 (V × W) :=
  (threeBlocksEquiv (R := R) (V := V) (W := W)).symm.trans
    (ExteriorTensor.tensorEquiv b c 3).symm

/-- Degree-two recomposition is the sum of the two pure inclusions and the mixed wedge.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree two decomposition.
-/
theorem twoEquiv_apply (q : ⋀[R]^2 V) (t : V ⊗[R] W) (r : ⋀[R]^2 W) :
    twoEquiv b c (q, t, r) = exteriorPower.map 2 (LinearMap.inl R V W) q +
      mixedTwoMap R V W t + exteriorPower.map 2 (LinearMap.inr R V W) r := by
  change (ExteriorTensor.tensorEquiv b c 2).symm
    ((DFinsupp.linearEquivFunOnFintype (R := R)).symm
      ((piThreeEquiv (R := R) _).symm
        ((zeroRightEquiv 2).symm q,
          (TensorProduct.congr (exteriorPower.oneEquiv R V)
            (exteriorPower.oneEquiv R W)).symm t,
          (zeroLeftEquiv 2).symm r))) = _
  erw [dsThree_symm (R := R)]
  simp only [map_add, tensorEquiv_symm_lof]
  erw [wedgeMap_zero (V := V) 2 r, wedgeMap_last_two (W := W) q]
  rfl

/-- Degree-three recomposition is the sum of the pure inclusions and the two positive wedges.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
theorem threeEquiv_apply (q : ⋀[R]^3 V) (t : (⋀[R]^2 V) ⊗[R] W)
    (u : V ⊗[R] (⋀[R]^2 W)) (r : ⋀[R]^3 W) :
    threeEquiv b c (q, t, u, r) = exteriorPower.map 3 (LinearMap.inl R V W) q +
      mixedTwoOneMap R V W t + mixedOneTwoMap R V W u +
        exteriorPower.map 3 (LinearMap.inr R V W) r := by
  change (ExteriorTensor.tensorEquiv b c 3).symm
    ((DFinsupp.linearEquivFunOnFintype (R := R)).symm
      ((piFourEquiv (R := R) _).symm
        ((zeroRightEquiv 3).symm q,
          (TensorProduct.congr (LinearEquiv.refl R _) (exteriorPower.oneEquiv R W)).symm t,
          (TensorProduct.congr (exteriorPower.oneEquiv R V) (LinearEquiv.refl R _)).symm u,
          (zeroLeftEquiv 3).symm r))) = _
  erw [dsFour_symm (R := R)]
  simp only [map_add, tensorEquiv_symm_lof]
  erw [wedgeMap_zero (V := V) 3 r, wedgeMap_last_three (W := W) q]
  rfl

/-- The degree-two equivalence has the canonical, basis-independent recomposition map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree two decomposition.
-/
theorem twoEquiv_toLinearMap : (twoEquiv b c).toLinearMap = twoMap R V W := by
  apply LinearMap.ext
  rintro ⟨q, t, r⟩
  simpa only [twoMap, LinearMap.coprod_apply, LinearEquiv.coe_coe, add_assoc] using
    twoEquiv_apply b c q t r

/-- The degree-three equivalence has the canonical, basis-independent recomposition map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, degree three decomposition.
-/
theorem threeEquiv_toLinearMap : (threeEquiv b c).toLinearMap = threeMap R V W := by
  apply LinearMap.ext
  rintro ⟨q, t, u, r⟩
  simpa only [threeMap, LinearMap.coprod_apply, LinearEquiv.coe_coe, add_assoc] using
    threeEquiv_apply b c q t u r

end T3.ExteriorLowDegree
