/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.LinearAlgebra.TensorProduct
public import T3.GroupTheory.Coproduct.FreeGraded
public import T3.GroupTheory.Coproduct.Relations
public import T3.GroupTheory.GradedQuotient

/-!
# Quotient maps on the graded coproduct blocks

The maps induced on the pure and tensor blocks by two presentations are surjective. Their
kernels are the factor relations and the mixed tensor relations from the paper. Mapping these
kernels through the free decomposition gives the ambient graded image of the normal closure.
This identifies the quotient of the free decomposition with the canonical coproduct maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, proof lines 898–926.
-/

@[expose] public section

open scoped TensorProduct

namespace T3.Coproduct

open AssociatedGraded

section Maps

variable {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]
  [Fact (HasExponentThree G')] [Fact (HasExponentThree H')]
  (f : G →* G') (g : H →* H')

/-- The maps on the three blocks induced by homomorphisms of both factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient of the degree-two blocks.
-/
def layerTwoBlockMap : LayerTwoBlocks (G := G) (H := H) →ₗ[ZMod 3]
    LayerTwoBlocks (G := G') (H := H') :=
  (mapLayer f 2).prodMap
    ((TensorProduct.map (mapLayer f 1) (mapLayer g 1)).prodMap (mapLayer g 2))

/-- The maps on the four blocks induced by homomorphisms of both factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, degree-three block quotients.
-/
def layerThreeBlockMap : LayerThreeBlocks (G := G) (H := H) →ₗ[ZMod 3]
    LayerThreeBlocks (G := G') (H := H') :=
  (mapLayer f 3).prodMap ((TensorProduct.map (mapLayer f 2) (mapLayer g 1)).prodMap
    ((TensorProduct.map (mapLayer f 1) (mapLayer g 2)).prodMap (mapLayer g 3)))

/-- Surjective presentations induce a surjection on the degree-two blocks.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, block quotient maps.
-/
theorem layerTwoBlockMap_surjective (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (layerTwoBlockMap f g) :=
  (mapLayer_surjective f hf 2).prodMap
    ((TensorProduct.map_surjective (mapLayer_surjective f hf 1)
      (mapLayer_surjective g hg 1)).prodMap (mapLayer_surjective g hg 2))

/-- Surjective presentations induce a surjection on the degree-three blocks.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, block quotient maps.
-/
theorem layerThreeBlockMap_surjective (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (layerThreeBlockMap f g) :=
  (mapLayer_surjective f hf 3).prodMap
    ((TensorProduct.map_surjective (mapLayer_surjective f hf 2)
      (mapLayer_surjective g hg 1)).prodMap
        ((TensorProduct.map_surjective (mapLayer_surjective f hf 1)
          (mapLayer_surjective g hg 2)).prodMap (mapLayer_surjective g hg 3)))

/-- In degree two the relation space consists only of the two pure relation blocks.
The presentations are required to preserve the first layer, as supplied by the lifted bases.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 899–906.
-/
theorem layerTwoBlockMap_ker (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hKf : f.ker ≤ commutator G) (hKg : g.ker ≤ commutator H) :
    (layerTwoBlockMap f g).ker =
      (subgroupImage f.ker 2).prod ((⊥ : Submodule (ZMod 3)
        (Layer G 1 ⊗[ZMod 3] Layer H 1)).prod (subgroupImage g.ker 2)) := by
  simp only [layerTwoBlockMap, LinearMap.ker_prodMap,
    TensorProduct.map_ker_eq_map₂ _ _ (mapLayer_surjective f hf 1) (mapLayer_surjective g hg 1),
    mapLayer_ker f hf, mapLayer_ker g hg,
    subgroupImage_eq_bot_of_le 1 hKf, subgroupImage_eq_bot_of_le 1 hKg,
    Submodule.map₂_bot_left, Submodule.map₂_bot_right, sup_idem]

/-- In degree three, the two pure relation spaces are accompanied by exactly the two
mixed tensor relation spaces. All kernels are computed in their source groups.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 916–926.
-/
theorem layerThreeBlockMap_ker (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hKf : f.ker ≤ commutator G) (hKg : g.ker ≤ commutator H) :
    (layerThreeBlockMap f g).ker =
      (subgroupImage f.ker 3).prod
        ((Submodule.map₂ (TensorProduct.mk (ZMod 3) (Layer G 2) (Layer H 1))
          (subgroupImage f.ker 2) ⊤).prod
          ((Submodule.map₂ (TensorProduct.mk (ZMod 3) (Layer G 1) (Layer H 2))
            ⊤ (subgroupImage g.ker 2)).prod (subgroupImage g.ker 3))) := by
  simp only [layerThreeBlockMap, LinearMap.ker_prodMap,
    TensorProduct.map_ker_eq_map₂ _ _ (mapLayer_surjective f hf 2) (mapLayer_surjective g hg 1),
    TensorProduct.map_ker_eq_map₂ _ _ (mapLayer_surjective f hf 1) (mapLayer_surjective g hg 2),
    mapLayer_ker f hf, mapLayer_ker g hg,
    subgroupImage_eq_bot_of_le 1 hKf, subgroupImage_eq_bot_of_le 1 hKg,
    Submodule.map₂_bot_left, Submodule.map₂_bot_right, sup_bot_eq, bot_sup_eq]

end Maps

section Presentations

variable {I J G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

private theorem freeSumLayerEquiv_comp_inl (n : ℕ) :
    (freeSumLayerEquiv (I := I) (J := J) n).toLinearMap.comp (mapLayer inl n) =
      mapLayer (Free.map (Sum.inl : I → I ⊕ J)) n :=
  LinearMap.ext (freeSumLayerEquiv_inl n)

private theorem freeSumLayerEquiv_comp_inr (n : ℕ) :
    (freeSumLayerEquiv (I := I) (J := J) n).toLinearMap.comp (mapLayer inr n) =
      mapLayer (Free.map (Sum.inr : J → I ⊕ J)) n :=
  LinearMap.ext (freeSumLayerEquiv_inr n)

private theorem freeSumLayerEquiv_mixedMap_map₂ {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (A : Submodule (ZMod 3) (Layer (Free I) i))
    (B : Submodule (ZMod 3) (Layer (Free J) j)) :
    (Submodule.map₂ (TensorProduct.mk (ZMod 3) (Layer (Free I) i) (Layer (Free J) j)) A B).map
        ((freeSumLayerEquiv (i + j)).toLinearMap.comp (mixedMap hi hj)) =
      Submodule.map₂ (bracketLayer hi hj)
        (A.map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) i))
        (B.map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) j)) := by
  rw [Submodule.map_map₂, Submodule.map₂_map_map]
  congr 1
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact freeSumLayerEquiv_mixedMap_tmul hi hj x y

variable (f : Free I →* G) (g : Free J →* H)

/-- Mapping the degree-two block kernel into the combined free group gives exactly the
second-degree relations of the coproduct presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 899–906.
-/
theorem layerTwoBlockMap_ker_map_freeSum (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hKf : f.ker ≤ commutator (Free I))
    (hKg : g.ker ≤ commutator (Free J)) :
    (layerTwoBlockMap f g).ker.map freeSumLayerTwoMap =
      subgroupImage (Presentation.relationKernel f.ker g.ker) 2 := by
  rw [layerTwoBlockMap_ker f g hf hg hKf hKg,
    freeSumLayerTwoMap, layerTwoMap, LinearMap.comp_coprod, LinearMap.comp_coprod,
    LinearMap.coprod_map_prod, LinearMap.coprod_map_prod,
    freeSumLayerEquiv_comp_inl, freeSumLayerEquiv_comp_inr, Submodule.map_bot, bot_sup_eq,
    Presentation.subgroupImage_relationKernel_two f.ker g.ker hKf hKg]

/-- Mapping the degree-three block kernel into the combined free group gives the four
relation spaces of the normal closure, with the mixed bracket in the paper's order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 916–926.
-/
theorem layerThreeBlockMap_ker_map_freeSum (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hKf : f.ker ≤ commutator (Free I))
    (hKg : g.ker ≤ commutator (Free J)) :
    (layerThreeBlockMap f g).ker.map freeSumLayerThreeMap =
      subgroupImage (Presentation.relationKernel f.ker g.ker) 3 := by
  rw [layerThreeBlockMap_ker f g hf hg hKf hKg,
    freeSumLayerThreeMap, layerThreeMap,
    LinearMap.comp_coprod, LinearMap.comp_coprod, LinearMap.comp_coprod,
    LinearMap.coprod_map_prod, LinearMap.coprod_map_prod, LinearMap.coprod_map_prod,
    freeSumLayerEquiv_comp_inl, freeSumLayerEquiv_comp_inr,
    freeSumLayerEquiv_mixedMap_map₂ (i := 2) (j := 1),
    freeSumLayerEquiv_mixedMap_map₂ (i := 1) (j := 2),
    Submodule.map_top, Submodule.map_top,
    Presentation.subgroupImage_relationKernel_three_eq_four_blocks f.ker g.ker hKf hKg]
  ac_rfl

omit [Fact (HasExponentThree G)] [Fact (HasExponentThree H)] in
/-- The combined free presentation is compatible with the coproduct of the two factor maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical quotient presentation.
-/
theorem presentationMap_comp_coproductToSum :
    (Presentation.presentationMap f g).comp Free.coproductToSum = map f g := by
  apply hom_ext
  · intro x
    exact Presentation.presentationMap_map_inl f g x
  · intro x
    exact Presentation.presentationMap_map_inr f g x

/-- The degree-two free decomposition commutes with the presentation quotient maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical degree-two quotient.
-/
theorem freeSumLayerTwoMap_quotient_square :
    (mapLayer (Presentation.presentationMap f g) 2).comp freeSumLayerTwoMap =
      layerTwoMap.comp (layerTwoBlockMap f g) := by
  apply LinearMap.ext
  intro x
  change mapLayer (Presentation.presentationMap f g) 2
    (mapLayer Free.coproductToSum 2 (layerTwoMap x)) = _
  rw [← LinearMap.comp_apply, ← mapLayer_comp, presentationMap_comp_coproductToSum]
  exact layerTwoMap_natural f g x

/-- The degree-three free decomposition commutes with the presentation quotient maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical degree-three quotient.
-/
theorem freeSumLayerThreeMap_quotient_square :
    (mapLayer (Presentation.presentationMap f g) 3).comp freeSumLayerThreeMap =
      layerThreeMap.comp (layerThreeBlockMap f g) := by
  apply LinearMap.ext
  intro x
  change mapLayer (Presentation.presentationMap f g) 3
    (mapLayer Free.coproductToSum 3 (layerThreeMap x)) = _
  rw [← LinearMap.comp_apply, ← mapLayer_comp, presentationMap_comp_coproductToSum]
  exact layerThreeMap_natural f g x

end Presentations

end T3.Coproduct
