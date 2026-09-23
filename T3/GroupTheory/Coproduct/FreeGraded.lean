/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Graded
public import T3.GroupTheory.Free.ExteriorNaturality
public import T3.LinearAlgebra.ExteriorLowDegree

/-!
# The canonical graded coproduct maps for free factors

The free coproduct is identified with the free group on the disjoint union of its generators.
The free-group exterior identifications turn the canonical mixed brackets into ordered exterior
products. In degree three the right mixed bracket has a minus sign, as prescribed by the
paper's Lie bracket; this sign is retained in the comparison of linear maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, proof lines 961–973.
-/

@[expose] public section

open scoped ExteriorAlgebra TensorProduct
open Module

namespace T3.Coproduct

open AssociatedGraded

variable {I J : Type*}

/-- The free coproduct and the free group on the disjoint union have canonically equal layers.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, identification of `F`.
-/
def freeSumLayerEquiv (n : ℕ) :
    Layer (Coproduct (Free I) (Free J)) n ≃ₗ[ZMod 3] Layer (Free (I ⊕ J)) n :=
  { mapLayer Free.coproductToSum n with
    invFun := mapLayer Free.sumToCoproduct n
    left_inv := mapLayer_leftInverse _ _ (by
      apply MonoidHom.ext
      intro x
      exact Free.sumEquivCoproduct.apply_symm_apply x) n
    right_inv := mapLayer_leftInverse _ _ (by
      apply MonoidHom.ext
      intro x
      exact Free.sumEquivCoproduct.symm_apply_apply x) n }

/-- The layer equivalence is induced by the specified free-coproduct homomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, identification of `F`.
-/
theorem freeSumLayerEquiv_apply (n : ℕ) (x : Layer (Coproduct (Free I) (Free J)) n) :
    freeSumLayerEquiv n x = mapLayer Free.coproductToSum n x := rfl

/-- The free-coproduct identification preserves the entire left factor in each degree.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, canonical left factor.
-/
@[simp]
theorem freeSumLayerEquiv_inl (n : ℕ) (x : Layer (Free I) n) :
    freeSumLayerEquiv n (mapLayer (inl (H := Free J)) n x) =
      mapLayer (Free.map (Sum.inl : I → I ⊕ J)) n x := by
  have h : Free.coproductToSum.comp (inl (G := Free I) (H := Free J)) =
      Free.map (Sum.inl : I → I ⊕ J) := rfl
  rw [freeSumLayerEquiv_apply, ← LinearMap.comp_apply, ← mapLayer_comp]
  rw [h]

/-- The free-coproduct identification preserves the entire right factor in each degree.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, canonical right factor.
-/
@[simp]
theorem freeSumLayerEquiv_inr (n : ℕ) (x : Layer (Free J) n) :
    freeSumLayerEquiv n (mapLayer (inr (G := Free I)) n x) =
      mapLayer (Free.map (Sum.inr : J → I ⊕ J)) n x := by
  have h : Free.coproductToSum.comp (inr (G := Free I) (H := Free J)) =
      Free.map (Sum.inr : J → I ⊕ J) := rfl
  rw [freeSumLayerEquiv_apply, ← LinearMap.comp_apply, ← mapLayer_comp]
  rw [h]

/-- The free-coproduct identification preserves the mixed bracket in its printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, canonical mixed factors.
-/
theorem freeSumLayerEquiv_mixedMap_tmul {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : Layer (Free I) i) (y : Layer (Free J) j) :
    freeSumLayerEquiv (i + j) (mixedMap hi hj (x ⊗ₜ[ZMod 3] y)) =
      bracketLayer hi hj (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) i x)
        (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) j y) := by
  rw [mixedMap_tmul, freeSumLayerEquiv_apply, mapLayer_bracketLayer]
  change bracketLayer hi hj (freeSumLayerEquiv i (mapLayer inl i x))
    (freeSumLayerEquiv j (mapLayer inr j y)) = _
  rw [freeSumLayerEquiv_inl, freeSumLayerEquiv_inr]

/-- The paper's second-degree map with target the free group on the disjoint union.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free presentation of `η₂`.
-/
def freeSumLayerTwoMap :
    LayerTwoBlocks (G := Free I) (H := Free J) →ₗ[ZMod 3] Layer (Free (I ⊕ J)) 2 :=
  (freeSumLayerEquiv 2).toLinearMap.comp layerTwoMap

/-- The paper's third-degree map with target the free group on the disjoint union.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free presentation of `η₃`.
-/
def freeSumLayerThreeMap :
    LayerThreeBlocks (G := Free I) (H := Free J) →ₗ[ZMod 3] Layer (Free (I ⊕ J)) 3 :=
  (freeSumLayerEquiv 3).toLinearMap.comp layerThreeMap

/-- The free presentation of `η₂` retains its three canonical components.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free presentation of `η₂`.
-/
theorem freeSumLayerTwoMap_apply (x : LayerTwoBlocks (G := Free I) (H := Free J)) :
    freeSumLayerTwoMap x = mapLayer (Free.map Sum.inl) 2 x.1 +
      (freeSumLayerEquiv 2 (mixedMap (by decide) (by decide) x.2.1) +
        mapLayer (Free.map Sum.inr) 2 x.2.2) := by
  simp [freeSumLayerTwoMap, layerTwoMap_apply]

/-- The free presentation of `η₃` retains both mixed brackets in their printed order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free presentation of `η₃`.
-/
theorem freeSumLayerThreeMap_apply (x : LayerThreeBlocks (G := Free I) (H := Free J)) :
    freeSumLayerThreeMap x = mapLayer (Free.map Sum.inl) 3 x.1 +
      (freeSumLayerEquiv 3 (mixedMap (by decide) (by decide) x.2.1) +
        (freeSumLayerEquiv 3 (mixedMap (by decide) (by decide) x.2.2.1) +
          mapLayer (Free.map Sum.inr) 3 x.2.2.2)) := by
  simp [freeSumLayerThreeMap, layerThreeMap_apply]

section Bases

variable {V W : Type*} [LinearOrder I] [LinearOrder J]
  [AddCommGroup V] [Module (ZMod 3) V] [AddCommGroup W] [Module (ZMod 3) W]
  (b : Basis I (ZMod 3) V) (c : Basis J (ZMod 3) W)

/-- The first layer of a free group identifies with the specified space of its generators.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free basis spaces `V₀, V₁`.
-/
noncomputable def freeFirstEquiv : Layer (Free I) 1 ≃ₗ[ZMod 3] V :=
  (Free.sigmaOne b).trans (exteriorPower.oneEquiv (ZMod 3) V)

/-- Converting the generator space back to the first exterior power recovers `σ₁`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, first exterior factor.
-/
@[simp]
theorem oneEquiv_symm_freeFirstEquiv (x : Layer (Free I) 1) :
    (exteriorPower.oneEquiv (ZMod 3) V).symm (freeFirstEquiv b x) = Free.sigmaOne b x :=
  (exteriorPower.oneEquiv (ZMod 3) V).symm_apply_apply _

/-- The second-degree domain in exterior coordinates, retaining all canonical factor maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-two blocks.
-/
noncomputable def freeTwoBlocksEquiv : LayerTwoBlocks (G := Free I) (H := Free J) ≃ₗ[ZMod 3]
    (⋀[ZMod 3]^2 V) × (V ⊗[ZMod 3] W) × (⋀[ZMod 3]^2 W) :=
  (Free.sigmaTwo b).prodCongr
    ((TensorProduct.congr (freeFirstEquiv b) (freeFirstEquiv c)).prodCongr (Free.sigmaTwo c))

/-- The third-degree domain in exterior coordinates, with the negative sign on the `(1,2)`
tensor component dictated by the canonical Lie bracket.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-three blocks.
-/
noncomputable def freeThreeBlocksEquiv :
    LayerThreeBlocks (G := Free I) (H := Free J) ≃ₗ[ZMod 3]
      (⋀[ZMod 3]^3 V) × ((⋀[ZMod 3]^2 V) ⊗[ZMod 3] W) ×
        (V ⊗[ZMod 3] (⋀[ZMod 3]^2 W)) × (⋀[ZMod 3]^3 W) :=
  (Free.sigmaThree b).prodCongr
    ((TensorProduct.congr (Free.sigmaTwo b) (freeFirstEquiv c)).prodCongr
      (((TensorProduct.congr (freeFirstEquiv b) (Free.sigmaTwo c)).trans
        (LinearEquiv.neg (ZMod 3))).prodCongr (Free.sigmaThree c)))

/-- The second-degree change of coordinates on an arbitrary block vector.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-two blocks.
-/
theorem freeTwoBlocksEquiv_apply (x : LayerTwoBlocks (G := Free I) (H := Free J)) :
    freeTwoBlocksEquiv b c x =
      (Free.sigmaTwo b x.1, TensorProduct.congr (freeFirstEquiv b) (freeFirstEquiv c) x.2.1,
        Free.sigmaTwo c x.2.2) := rfl

/-- The third-degree change of coordinates records the sign of the right mixed component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-three blocks.
-/
theorem freeThreeBlocksEquiv_apply (x : LayerThreeBlocks (G := Free I) (H := Free J)) :
    freeThreeBlocksEquiv b c x =
      (Free.sigmaThree b x.1,
        TensorProduct.congr (Free.sigmaTwo b) (freeFirstEquiv c) x.2.1,
        -TensorProduct.congr (freeFirstEquiv b) (Free.sigmaTwo c) x.2.2.1,
        Free.sigmaThree c x.2.2.2) := rfl

variable [LinearOrder (I ⊕ J)]

/-- The entire `(1,1)` tensor component agrees with the canonical exterior tensor map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free mixed degree two.
-/
theorem sigmaTwo_freeSum_mixedMap (z : Layer (Free I) 1 ⊗[ZMod 3] Layer (Free J) 1) :
    Free.sigmaTwo (b.prod c)
      (freeSumLayerEquiv 2 (mixedMap (by decide) (by decide) z)) =
      ExteriorLowDegree.mixedTwoMap (ZMod 3) V W
        (TensorProduct.congr (freeFirstEquiv b) (freeFirstEquiv c) z) := by
  have h : (Free.sigmaTwo (b.prod c)).toLinearMap.comp
      ((freeSumLayerEquiv 2).toLinearMap.comp
        (mixedMap (i := 1) (j := 1) (by decide) (by decide))) =
        (ExteriorLowDegree.mixedTwoMap (ZMod 3) V W).comp
          (TensorProduct.congr (freeFirstEquiv b) (freeFirstEquiv c)).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      freeSumLayerEquiv_mixedMap_tmul (i := 1) (j := 1),
      Free.sigmaTwo_bracket_factors, TensorProduct.congr_tmul,
      ExteriorLowDegree.mixedTwoMap_tmul, oneEquiv_symm_freeFirstEquiv]
  exact DFunLike.congr_fun h z

/-- The entire `(2,1)` tensor component agrees with exterior multiplication with positive sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free mixed degree three.
-/
theorem sigmaThree_freeSum_mixedMap_two_one
    (z : Layer (Free I) 2 ⊗[ZMod 3] Layer (Free J) 1) :
    Free.sigmaThree (b.prod c)
      (freeSumLayerEquiv 3 (mixedMap (by decide) (by decide) z)) =
      ExteriorLowDegree.mixedTwoOneMap (ZMod 3) V W
        (TensorProduct.congr (Free.sigmaTwo b) (freeFirstEquiv c) z) := by
  have h : (Free.sigmaThree (b.prod c)).toLinearMap.comp
      ((freeSumLayerEquiv 3).toLinearMap.comp
        (mixedMap (i := 2) (j := 1) (by decide) (by decide))) =
        (ExteriorLowDegree.mixedTwoOneMap (ZMod 3) V W).comp
          (TensorProduct.congr (Free.sigmaTwo b) (freeFirstEquiv c)).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      freeSumLayerEquiv_mixedMap_tmul (i := 2) (j := 1),
      Free.sigmaThree_bracket_factors_two_one, TensorProduct.congr_tmul,
      ExteriorLowDegree.mixedTwoOneMap_tmul, oneEquiv_symm_freeFirstEquiv]
  exact DFunLike.congr_fun h z

/-- The entire `(1,2)` tensor component is the negative of ordered exterior multiplication.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free mixed degree three.
-/
theorem sigmaThree_freeSum_mixedMap_one_two
    (z : Layer (Free I) 1 ⊗[ZMod 3] Layer (Free J) 2) :
    Free.sigmaThree (b.prod c)
      (freeSumLayerEquiv 3 (mixedMap (by decide) (by decide) z)) =
      -ExteriorLowDegree.mixedOneTwoMap (ZMod 3) V W
        (TensorProduct.congr (freeFirstEquiv b) (Free.sigmaTwo c) z) := by
  have h : (Free.sigmaThree (b.prod c)).toLinearMap.comp
      ((freeSumLayerEquiv 3).toLinearMap.comp
        (mixedMap (i := 1) (j := 2) (by decide) (by decide))) =
        -((ExteriorLowDegree.mixedOneTwoMap (ZMod 3) V W).comp
          (TensorProduct.congr (freeFirstEquiv b) (Free.sigmaTwo c)).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.neg_apply,
      freeSumLayerEquiv_mixedMap_tmul (i := 1) (j := 2), Free.sigmaThree_bracket_factors_one_two,
      TensorProduct.congr_tmul, ExteriorLowDegree.mixedOneTwoMap_tmul,
      oneEquiv_symm_freeFirstEquiv]
  exact DFunLike.congr_fun h z

/-- In degree two, the canonical free coproduct map is the exterior decomposition map
after the specified changes of coordinates.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-two decomposition.
-/
theorem sigmaTwo_freeSumLayerTwoMap (x : LayerTwoBlocks (G := Free I) (H := Free J)) :
    Free.sigmaTwo (b.prod c) (freeSumLayerTwoMap x) =
      ExteriorLowDegree.twoMap (ZMod 3) V W (freeTwoBlocksEquiv b c x) := by
  simp only [freeSumLayerTwoMap_apply, map_add, Free.sigmaTwo_map_inl,
    Free.sigmaTwo_map_inr, sigmaTwo_freeSum_mixedMap, freeTwoBlocksEquiv_apply,
    ExteriorLowDegree.twoMap, LinearMap.coprod_apply]

/-- In degree three, the canonical free coproduct map is the exterior decomposition map
after changing coordinates and negating the right mixed tensor component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free degree-three decomposition.
-/
theorem sigmaThree_freeSumLayerThreeMap (x : LayerThreeBlocks (G := Free I) (H := Free J)) :
    Free.sigmaThree (b.prod c) (freeSumLayerThreeMap x) =
      ExteriorLowDegree.threeMap (ZMod 3) V W (freeThreeBlocksEquiv b c x) := by
  simp only [freeSumLayerThreeMap_apply, map_add, Free.sigmaThree_map_inl,
    Free.sigmaThree_map_inr, sigmaThree_freeSum_mixedMap_two_one,
    sigmaThree_freeSum_mixedMap_one_two, freeThreeBlocksEquiv_apply,
    ExteriorLowDegree.threeMap, LinearMap.coprod_apply, map_neg]

end Bases

/-- The canonical second-degree map into the combined free group is bijective in arbitrary rank.

Orders and coordinate bases are chosen only inside the proof; the map is the original canonical
map, with no ordered or finite generating-set hypothesis.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₂`.
-/
theorem freeSumLayerTwoMap_bijective :
    Function.Bijective (freeSumLayerTwoMap (I := I) (J := J)) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : LinearOrder J := linearOrderOfSTO WellOrderingRel
  let : LinearOrder (I ⊕ J) := linearOrderOfSTO WellOrderingRel
  let b : Basis I (ZMod 3) (I →₀ ZMod 3) := Finsupp.basisSingleOne
  let c : Basis J (ZMod 3) (J →₀ ZMod 3) := Finsupp.basisSingleOne
  have he : (Free.sigmaTwo (b.prod c)) ∘ freeSumLayerTwoMap =
      (ExteriorLowDegree.twoEquiv b c) ∘ freeTwoBlocksEquiv b c := by
    funext x
    change Free.sigmaTwo (b.prod c) (freeSumLayerTwoMap x) = _
    rw [sigmaTwo_freeSumLayerTwoMap]
    exact (DFunLike.congr_fun (ExteriorLowDegree.twoEquiv_toLinearMap b c) _).symm
  have h : Function.Bijective ((Free.sigmaTwo (b.prod c)) ∘ freeSumLayerTwoMap) := by
    rw [he]
    exact (ExteriorLowDegree.twoEquiv b c).bijective.comp (freeTwoBlocksEquiv b c).bijective
  exact h.of_comp_left (Free.sigmaTwo (b.prod c)).injective

/-- The canonical third-degree map into the combined free group is bijective in arbitrary rank.

The proof uses the signed exterior-coordinate equivalence. The canonical mixed brackets
themselves retain the paper's order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₃`.
-/
theorem freeSumLayerThreeMap_bijective :
    Function.Bijective (freeSumLayerThreeMap (I := I) (J := J)) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : LinearOrder J := linearOrderOfSTO WellOrderingRel
  let : LinearOrder (I ⊕ J) := linearOrderOfSTO WellOrderingRel
  let b : Basis I (ZMod 3) (I →₀ ZMod 3) := Finsupp.basisSingleOne
  let c : Basis J (ZMod 3) (J →₀ ZMod 3) := Finsupp.basisSingleOne
  have he : (Free.sigmaThree (b.prod c)) ∘ freeSumLayerThreeMap =
      (ExteriorLowDegree.threeEquiv b c) ∘ freeThreeBlocksEquiv b c := by
    funext x
    change Free.sigmaThree (b.prod c) (freeSumLayerThreeMap x) = _
    rw [sigmaThree_freeSumLayerThreeMap]
    exact (DFunLike.congr_fun (ExteriorLowDegree.threeEquiv_toLinearMap b c) _).symm
  have h : Function.Bijective ((Free.sigmaThree (b.prod c)) ∘ freeSumLayerThreeMap) := by
    rw [he]
    exact (ExteriorLowDegree.threeEquiv b c).bijective.comp (freeThreeBlocksEquiv b c).bijective
  exact h.of_comp_left (Free.sigmaThree (b.prod c)).injective

/-- The paper's actual second-degree coproduct map is bijective for arbitrary free factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₂`.
-/
theorem layerTwoMap_bijective_free :
    Function.Bijective (layerTwoMap (G := Free I) (H := Free J)) :=
  Function.Bijective.of_comp_left (f := freeSumLayerEquiv 2)
    (g := layerTwoMap) freeSumLayerTwoMap_bijective (freeSumLayerEquiv 2).injective

/-- The paper's actual third-degree coproduct map is bijective for arbitrary free factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₃`.
-/
theorem layerThreeMap_bijective_free :
    Function.Bijective (layerThreeMap (G := Free I) (H := Free J)) :=
  Function.Bijective.of_comp_left (f := freeSumLayerEquiv 3)
    (g := layerThreeMap) freeSumLayerThreeMap_bijective (freeSumLayerEquiv 3).injective

/-- The actual canonical second-degree map, bundled as an equivalence for arbitrary free factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₂`.
-/
noncomputable def freeLayerTwoEquiv : LayerTwoBlocks (G := Free I) (H := Free J) ≃ₗ[ZMod 3]
    Layer (Coproduct (Free I) (Free J)) 2 :=
  LinearEquiv.ofBijective layerTwoMap layerTwoMap_bijective_free

/-- The actual canonical third-degree map, bundled as an equivalence for arbitrary free factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, free case of `η₃`.
-/
noncomputable def freeLayerThreeEquiv : LayerThreeBlocks (G := Free I) (H := Free J) ≃ₗ[ZMod 3]
    Layer (Coproduct (Free I) (Free J)) 3 :=
  LinearEquiv.ofBijective layerThreeMap layerThreeMap_bijective_free

/-- The bundled free second-degree equivalence keeps the canonical map unchanged.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, canonical `η₂`.
-/
@[simp]
theorem freeLayerTwoEquiv_apply (x : LayerTwoBlocks (G := Free I) (H := Free J)) :
    freeLayerTwoEquiv x = layerTwoMap x := rfl

/-- The bundled free third-degree equivalence keeps the canonical map unchanged.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, canonical `η₃`.
-/
@[simp]
theorem freeLayerThreeEquiv_apply (x : LayerThreeBlocks (G := Free I) (H := Free J)) :
    freeLayerThreeEquiv x = layerThreeMap x := rfl

end T3.Coproduct
