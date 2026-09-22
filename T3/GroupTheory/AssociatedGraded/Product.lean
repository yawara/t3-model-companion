/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded
public import Mathlib.LinearAlgebra.Prod

/-!
# Associated graded layers of a direct product

The lower central terms of a product are the products of the corresponding terms. The
projections and inclusions therefore give inverse maps between the associated graded layer
of the product and the product of the two layers. No finite generation is assumed.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2, line 521.
-/

@[expose] public section

namespace T3

variable {G H : Type*} [Group G] [Group H]

/-- A direct product of exponent-three groups has exponent dividing three.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2.
-/
instance productHasExponentThree [Fact (HasExponentThree G)] [Fact (HasExponentThree H)] :
    Fact (HasExponentThree (G × H)) :=
  ⟨fun x => Prod.ext (Fact.out (p := HasExponentThree G) x.1)
    (Fact.out (p := HasExponentThree H) x.2)⟩

namespace AssociatedGraded

/-- The paper's lower central term commutes with direct products.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2.
-/
theorem term_prod (n : ℕ) : term (G × H) n = (term G n).prod (term H n) :=
  Subgroup.top_lowerCentralSeries_prod (n - 1)

/-- The canonical additive identification of a product's layer with the product of its layers.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2.
-/
def layerProdAddEquiv (n : ℕ) : Layer (G × H) n ≃+ Layer G n × Layer H n where
  toFun x := (mapAdd (MonoidHom.fst G H) n x, mapAdd (MonoidHom.snd G H) n x)
  invFun x := mapAdd (MonoidHom.inl G H) n x.1 + mapAdd (MonoidHom.inr G H) n x.2
  left_inv x := by
    obtain ⟨x, rfl⟩ := mk_surjective (G × H) n x
    simp only [mapAdd_mk, ← mk_mul]
    congr 1
    apply Subtype.ext
    exact Prod.ext (by simp [termMap]) (by simp [termMap])
  right_inv x := by
    rcases x with ⟨x, y⟩
    obtain ⟨x, rfl⟩ := mk_surjective G n x
    obtain ⟨y, rfl⟩ := mk_surjective H n y
    apply Prod.ext
    · simp only [mapAdd_mk, ← mk_mul]
      congr 1
      apply Subtype.ext
      simp [termMap]
    · simp only [mapAdd_mk, ← mk_mul]
      congr 1
      apply Subtype.ext
      simp [termMap]
  map_add' x y := by simp only [map_add]; rfl

variable [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- The canonical vector-space identification of the degree quotient of a product.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2.
-/
def layerProdEquiv (n : ℕ) : Layer (G × H) n ≃ₗ[ZMod 3] Layer G n × Layer H n :=
  { layerProdAddEquiv n with map_smul' := ZMod.map_smul (layerProdAddEquiv n) }

/-- The product equivalence is induced by the two group projections.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v7.tex, v7 Example 2.21, item 2.
-/
@[simp]
theorem layerProdEquiv_apply (n : ℕ) (x : Layer (G × H) n) :
    layerProdEquiv n x = (mapLayer (MonoidHom.fst G H) n x, mapLayer (MonoidHom.snd G H) n x) :=
  rfl

end AssociatedGraded

end T3
