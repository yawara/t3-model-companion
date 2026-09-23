/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.GradedEquiv
public import Mathlib.RingTheory.Flat.Basic

/-!
# Coproducts preserve strict embeddings

The canonical graded decompositions identify a coproduct map with its pure maps and tensor
products. Injective graded maps on the factors therefore give an injective graded map on the
coproduct, since tensoring vector-space embeddings preserves injectivity. The graded
injectivity criterion then gives injectivity of the group map, exactly as in the paper.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, v8 Lemma 4.5, lines 1032–1045.
-/

@[expose] public section

namespace T3.Coproduct

open AssociatedGraded

section Maps

variable {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]
  [Fact (HasExponentThree G')] [Fact (HasExponentThree H')]
  (f : G →* G') (g : H →* H')

/-- Injectivity on factor layers gives injectivity on the degree-two blocks.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, degree-two tensor argument.
-/
theorem layerTwoBlockMap_injective (hf : ∀ n, Function.Injective (mapLayer f n))
    (hg : ∀ n, Function.Injective (mapLayer g n)) :
    Function.Injective (layerTwoBlockMap f g) :=
  (hf 2).prodMap ((TensorProduct.map_injective_of_flat_flat _ _ (hf 1) (hg 1)).prodMap (hg 2))

/-- Injectivity on factor layers gives injectivity on the degree-three blocks.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, degree-three tensor argument.
-/
theorem layerThreeBlockMap_injective (hf : ∀ n, Function.Injective (mapLayer f n))
    (hg : ∀ n, Function.Injective (mapLayer g n)) :
    Function.Injective (layerThreeBlockMap f g) :=
  (hf 3).prodMap ((TensorProduct.map_injective_of_flat_flat _ _ (hf 2) (hg 1)).prodMap
    ((TensorProduct.map_injective_of_flat_flat _ _ (hf 1) (hg 2)).prodMap (hg 3)))

/-- The coproduct map is injective on every layer if both factor maps are.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, graded injectivity.
-/
theorem mapLayer_map_injective (hf : ∀ n, Function.Injective (mapLayer f n))
    (hg : ∀ n, Function.Injective (mapLayer g n)) (n : ℕ) :
    Function.Injective (mapLayer (map f g) n) := by
  by_cases hn : 4 ≤ n
  · let := layer_subsingleton_of_four_le (G := Coproduct G H) Fact.out hn
    exact fun _ _ _ => Subsingleton.elim _ _
  have hn' : n ≤ 3 := by omega
  interval_cases n
  · exact fun _ _ _ => Subsingleton.elim _ _
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (layerOneEquiv (G := G) (H := H)).surjective x
    obtain ⟨y, rfl⟩ := (layerOneEquiv (G := G) (H := H)).surjective y
    apply congrArg (layerOneEquiv (G := G) (H := H))
    apply (hf 1).prodMap (hg 1)
    apply (layerOneEquiv (G := G') (H := H')).injective
    simpa only [layerOneEquiv_natural, Prod.map] using hxy
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (layerTwoMap_bijective (G := G) (H := H)).surjective x
    obtain ⟨y, rfl⟩ := (layerTwoMap_bijective (G := G) (H := H)).surjective y
    apply congrArg (layerTwoMap (G := G) (H := H))
    apply layerTwoBlockMap_injective f g hf hg
    apply (layerTwoMap_bijective (G := G') (H := H')).injective
    simpa only [layerTwoMap_natural, layerTwoBlockMap, LinearMap.coe_prodMap, Prod.map] using hxy
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (layerThreeMap_bijective (G := G) (H := H)).surjective x
    obtain ⟨y, rfl⟩ := (layerThreeMap_bijective (G := G) (H := H)).surjective y
    apply congrArg (layerThreeMap (G := G) (H := H))
    apply layerThreeBlockMap_injective f g hf hg
    apply (layerThreeMap_bijective (G := G') (H := H')).injective
    simpa only [layerThreeMap_natural, layerThreeBlockMap, LinearMap.coe_prodMap, Prod.map]
      using hxy

/-- The coproduct of two maps injective on their associated graded layers is injective.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, graded criterion for injectivity.
-/
theorem map_injective_of_mapLayer_injective (hf : ∀ n, Function.Injective (mapLayer f n))
    (hg : ∀ n, Function.Injective (mapLayer g n)) : Function.Injective (map f g) :=
  injective_of_mapAdd_injective Fact.out _ (mapLayer_map_injective f g hf hg)

end Maps

variable {G B : Type*} [Group G] [Group B]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree B)]

/-- **Lemma 4.5.** A strict subgroup inclusion stays injective after taking the coproduct
with any exponent-three group. Neither factor is assumed to be finitely generated.

Paper-ID: structure.strict_coproduct
TeX: T3_modelcompanion_v8.tex, `lemma:free-product-amalgam`, lines 1032–1045.
-/
theorem map_injective_of_strict (D : Subgroup G) (hD : IsStrict D) :
    Function.Injective (map D.subtype (MonoidHom.id B)) := by
  have hG : HasExponentThree G := Fact.out
  let : Fact (HasExponentThree D) := ⟨fun x => Subtype.ext (hG x)⟩
  have hgraded : Function.Injective (AssociatedGraded.map D.subtype) :=
    (map_injective_iff_isStrict D.subtype D.subtype_injective).mpr (by simpa using hD)
  apply map_injective_of_mapLayer_injective D.subtype (MonoidHom.id B)
    ((map_injective_iff D.subtype).mp hgraded)
  intro n
  rw [mapLayer_id]
  exact Function.injective_id

end T3.Coproduct
