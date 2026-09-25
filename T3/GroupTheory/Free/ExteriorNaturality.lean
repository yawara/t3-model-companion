/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.ExteriorBracket
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Naturality of the free-group exterior identifications

If a homomorphism between free exponent-three groups agrees in degree one with a specified
linear map between their basis spaces, it agrees in degrees two and three with the induced
exterior-power maps. The proof uses the increasing commutator bases and preservation of the
actual graded bracket. This identifies the factor maps in the coproduct presentation with
the canonical inclusions in the exterior algebra.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof, lines 966–1016.
-/

@[expose] public section

open scoped ExteriorAlgebra
open Module

namespace T3.Free

open AssociatedGraded

variable {I J V W : Type*} [LinearOrder I] [LinearOrder J]
  [AddCommGroup V] [Module (ZMod 3) V] [AddCommGroup W] [Module (ZMod 3) W]
  (b : Basis I (ZMod 3) V) (c : Basis J (ZMod 3) W)
  (φ : Free I →* Free J) (f : V →ₗ[ZMod 3] W)

/-- Agreement on the free generator classes implies agreement on the entire first layer.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, identification of factor maps.
-/
theorem sigmaOne_mapLayer_of_basis
    (h : ∀ i, sigmaOne c (mapLayer φ 1 (layerOneBasis i)) =
      (exteriorPower.oneEquiv (ZMod 3) W).symm (f (b i)))
    (x : Layer (Free I) 1) :
    sigmaOne c (mapLayer φ 1 x) = exteriorPower.map 1 f (sigmaOne b x) := by
  have he : (sigmaOne c).toLinearMap.comp (mapLayer φ 1) =
      (exteriorPower.map 1 f).comp (sigmaOne b).toLinearMap := by
    apply (layerOneBasis (I := I)).ext
    intro i
    change sigmaOne c (mapLayer φ 1 (layerOneBasis i)) =
      exteriorPower.map 1 f (sigmaOne b (layerOneBasis i))
    rw [h, layerOneBasis_apply, sigmaOne_of, exteriorPower_map_oneEquiv_symm]
  exact DFunLike.congr_fun he x

/-- Agreement of the first layers forces agreement of the second layers with the exterior map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, identification of degree-two maps.
-/
theorem sigmaTwo_mapLayer
    (h : ∀ x, sigmaOne c (mapLayer φ 1 x) = exteriorPower.map 1 f (sigmaOne b x))
    (x : Layer (Free I) 2) :
    sigmaTwo c (mapLayer φ 2 x) = exteriorPower.map 2 f (sigmaTwo b x) := by
  have he : (sigmaTwo c).toLinearMap.comp (mapLayer φ 2) =
      (exteriorPower.map 2 f).comp (sigmaTwo b).toLinearMap := by
    apply (layerTwoBasis (I := I)).ext
    intro p
    change sigmaTwo c (mapLayer φ 2 (layerTwoBasis p)) =
      exteriorPower.map 2 f (sigmaTwo b (layerTwoBasis p))
    rw [layerTwoBasis_eq_bracket, mapLayer_bracketLayer (i := 1) (j := 1),
      sigmaTwo_bracketLayer, sigmaTwo_bracketLayer, h, h,
      exteriorPower_map_gradedMul (i := 1) (j := 1)]
  exact DFunLike.congr_fun he x

/-- Agreement of the first layers forces agreement of the third layers with the exterior map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, degree-three maps.
-/
theorem sigmaThree_mapLayer
    (h : ∀ x, sigmaOne c (mapLayer φ 1 x) = exteriorPower.map 1 f (sigmaOne b x))
    (x : Layer (Free I) 3) :
    sigmaThree c (mapLayer φ 3 x) = exteriorPower.map 3 f (sigmaThree b x) := by
  let e : Basis (IncreasingTriple I) (ZMod 3) (Layer (Free I) 3) := Basis.ofRepr layerThreeEquiv
  have hb (t : IncreasingTriple I) : e t = bracketLayer (by decide) (by decide)
      (bracketLayer (by decide) (by decide) (layerOneBasis t.first) (layerOneBasis t.second))
      (layerOneBasis t.third) := by
    apply layerThreeEquiv.injective
    rw [layerOneBasis_apply, layerOneBasis_apply, layerOneBasis_apply, bracketLayer_mk,
      bracketLayer_mk]
    change layerThreeEquiv (layerThreeEquiv.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (layerThreeEquiv_tripleCommutator t).symm
  have he : (sigmaThree c).toLinearMap.comp (mapLayer φ 3) =
      (exteriorPower.map 3 f).comp (sigmaThree b).toLinearMap := by
    apply e.ext
    intro t
    change sigmaThree c (mapLayer φ 3 (e t)) = exteriorPower.map 3 f (sigmaThree b (e t))
    rw [hb, mapLayer_bracketLayer (i := 2) (j := 1), sigmaThree_bracketLayer,
      sigmaThree_bracketLayer, sigmaTwo_mapLayer b c φ f h, h,
      exteriorPower_map_gradedMul (i := 2) (j := 1)]
  exact DFunLike.congr_fun he x

section Sum

variable [LinearOrder (I ⊕ J)]

omit [LinearOrder J] in
/-- The left free factor in degree one corresponds to the canonical vector-space inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, left factor identification.
-/
theorem sigmaOne_map_inl (x : Layer (Free I) 1) :
    sigmaOne (b.prod c) (mapLayer (map (Sum.inl : I → I ⊕ J)) 1 x) =
      exteriorPower.map 1 (LinearMap.inl (ZMod 3) V W) (sigmaOne b x) := by
  apply sigmaOne_mapLayer_of_basis
  intro i
  rw [layerOneBasis_apply, mapLayer_mk]
  change sigmaOne (b.prod c) (mk (Free (I ⊕ J)) 1 ⟨map Sum.inl (of i), _⟩) = _
  rw [map_of, sigmaOne_of, Basis.prod_apply]
  rfl

omit [LinearOrder I] in
/-- The right free factor in degree one corresponds to the canonical vector-space inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, right factor identification.
-/
theorem sigmaOne_map_inr (x : Layer (Free J) 1) :
    sigmaOne (b.prod c) (mapLayer (map (Sum.inr : J → I ⊕ J)) 1 x) =
      exteriorPower.map 1 (LinearMap.inr (ZMod 3) V W) (sigmaOne c x) := by
  apply sigmaOne_mapLayer_of_basis
  intro j
  rw [layerOneBasis_apply, mapLayer_mk]
  change sigmaOne (b.prod c) (mk (Free (I ⊕ J)) 1 ⟨map Sum.inr (of j), _⟩) = _
  rw [map_of, sigmaOne_of, Basis.prod_apply]
  rfl

omit [LinearOrder J] in
/-- The second graded map of the left free inclusion is its exterior-square inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, left degree-two factor.
-/
theorem sigmaTwo_map_inl (x : Layer (Free I) 2) :
    sigmaTwo (b.prod c) (mapLayer (map (Sum.inl : I → I ⊕ J)) 2 x) =
      exteriorPower.map 2 (LinearMap.inl (ZMod 3) V W) (sigmaTwo b x) :=
  sigmaTwo_mapLayer b (b.prod c) _ _ (sigmaOne_map_inl b c) x

omit [LinearOrder I] in
/-- The second graded map of the right free inclusion is its exterior-square inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, right degree-two factor.
-/
theorem sigmaTwo_map_inr (x : Layer (Free J) 2) :
    sigmaTwo (b.prod c) (mapLayer (map (Sum.inr : J → I ⊕ J)) 2 x) =
      exteriorPower.map 2 (LinearMap.inr (ZMod 3) V W) (sigmaTwo c x) :=
  sigmaTwo_mapLayer c (b.prod c) _ _ (sigmaOne_map_inr b c) x

omit [LinearOrder J] in
/-- The third graded map of the left free inclusion is its exterior-cube inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, left degree-three factor.
-/
theorem sigmaThree_map_inl (x : Layer (Free I) 3) :
    sigmaThree (b.prod c) (mapLayer (map (Sum.inl : I → I ⊕ J)) 3 x) =
      exteriorPower.map 3 (LinearMap.inl (ZMod 3) V W) (sigmaThree b x) :=
  sigmaThree_mapLayer b (b.prod c) _ _ (sigmaOne_map_inl b c) x

omit [LinearOrder I] in
/-- The third graded map of the right free inclusion is its exterior-cube inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, right degree-three factor.
-/
theorem sigmaThree_map_inr (x : Layer (Free J) 3) :
    sigmaThree (b.prod c) (mapLayer (map (Sum.inr : J → I ⊕ J)) 3 x) =
      exteriorPower.map 3 (LinearMap.inr (ZMod 3) V W) (sigmaThree c x) :=
  sigmaThree_mapLayer c (b.prod c) _ _ (sigmaOne_map_inr b c) x

/-- The mixed bracket in degree two is the product of the two exterior factor inclusions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, the `(1,1)` component.
-/
theorem sigmaTwo_bracket_factors (x : Layer (Free I) 1) (y : Layer (Free J) 1) :
    sigmaTwo (b.prod c) (bracketLayer (by decide) (by decide)
      (mapLayer (map (Sum.inl : I → I ⊕ J)) 1 x) (mapLayer (map Sum.inr) 1 y)) =
      gradedMul (exteriorPower.map 1 (LinearMap.inl (ZMod 3) V W) (sigmaOne b x))
        (exteriorPower.map 1 (LinearMap.inr (ZMod 3) V W) (sigmaOne c y)) := by
  rw [sigmaTwo_bracketLayer, sigmaOne_map_inl, sigmaOne_map_inr]

/-- The `(2,1)` mixed bracket is the ordered exterior product, with positive sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, the `(2,1)` component.
-/
theorem sigmaThree_bracket_factors_two_one (q : Layer (Free I) 2) (y : Layer (Free J) 1) :
    sigmaThree (b.prod c) (bracketLayer (by decide) (by decide)
      (mapLayer (map (Sum.inl : I → I ⊕ J)) 2 q) (mapLayer (map Sum.inr) 1 y)) =
      gradedMul (exteriorPower.map 2 (LinearMap.inl (ZMod 3) V W) (sigmaTwo b q))
        (exteriorPower.map 1 (LinearMap.inr (ZMod 3) V W) (sigmaOne c y)) := by
  rw [sigmaThree_bracketLayer, sigmaTwo_map_inl, sigmaOne_map_inr]

/-- The `(1,2)` mixed bracket is the negative of the left-before-right exterior product.
This is the sign needed when identifying the paper's `η₃` with its exterior tensor blocks.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, the `(1,2)` component.
-/
theorem sigmaThree_bracket_factors_one_two (x : Layer (Free I) 1) (q : Layer (Free J) 2) :
    sigmaThree (b.prod c) (bracketLayer (by decide) (by decide)
      (mapLayer (map (Sum.inl : I → I ⊕ J)) 1 x) (mapLayer (map Sum.inr) 2 q)) =
      -gradedMul (exteriorPower.map 1 (LinearMap.inl (ZMod 3) V W) (sigmaOne b x))
        (exteriorPower.map 2 (LinearMap.inr (ZMod 3) V W) (sigmaTwo c q)) := by
  rw [bracketLayer_one_two, map_neg, sigmaThree_bracketLayer,
    sigmaTwo_map_inr, sigmaOne_map_inl, gradedMul_one_two_comm]

end Sum

end T3.Free
