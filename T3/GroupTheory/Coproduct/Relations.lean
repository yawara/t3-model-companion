/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Presentation
public import T3.GroupTheory.AssociatedGraded.Subgroup

/-!
# The graded relations of a coproduct presentation

The two free factors are retracts of the free group on their disjoint union. Thus the ambient
graded images of their relations are the images of the corresponding subspaces computed in
each factor. The normal-closure formulas then give the relation spaces in degrees two and three.
Normality of a factor relation subgroup absorbs its brackets with that same factor into its
third-degree relation space. No finite-rank or homogeneous-relation assumption is used.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 956–1007.
-/

@[expose] public section

open scoped commutatorElement

namespace T3.AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- A normal subgroup's ambient graded image is closed under brackets with ambient layers.

In degrees two and one this is the paper's inclusion `Rₙ ∧ Vₙ ⊆ Sₙ`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof line 995.
-/
theorem bracketLayer_subgroupImage_top_le (K : Subgroup G) [K.Normal]
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ (bracketLayer hi hj) (subgroupImage K i) ⊤ ≤ subgroupImage K (i + j) := by
  apply Submodule.map₂_le.mpr
  intro x hx y _
  obtain ⟨x, hxK, rfl⟩ := (mem_subgroupImage K i x).mp hx
  obtain ⟨y, rfl⟩ := mk_surjective G j y
  exact (mem_subgroupImage K (i + j) _).mpr
    ⟨termCommutator hi hj x y,
      Subgroup.commutator_le_left K ⊤
        (Subgroup.commutator_mem_commutator hxK (Subgroup.mem_top _)), rfl⟩

/-- The same-factor brackets remain absorbed after applying any ambient group homomorphism.

The relation subgroup need only be normal in the source factor, not in the target group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof line 995.
-/
theorem bracketLayer_map_subgroupImage_range_le (f : G →* H) (K : Subgroup G) [K.Normal]
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ (bracketLayer hi hj) ((subgroupImage K i).map (mapLayer f i))
      (LinearMap.range (mapLayer f j)) ≤ (subgroupImage K (i + j)).map (mapLayer f (i + j)) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨x, hx, rfl⟩ y ⟨y, rfl⟩
  rw [← mapLayer_bracketLayer]
  exact Submodule.mem_map.mpr ⟨_, bracketLayer_subgroupImage_top_le K hi hj
    (Submodule.apply_mem_map₂ _ hx Submodule.mem_top), rfl⟩

/-- Exchanging the arguments of the mixed bracket does not change its subspace image.

The two bracket maps differ by a minus sign; closure under negation removes that sign only
at the level of subspaces.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 996–999.
-/
theorem map₂_bracketLayer_one_two (A : Submodule (ZMod 3) (Layer G 1))
    (B : Submodule (ZMod 3) (Layer G 2)) :
    Submodule.map₂ (bracketLayer (by decide) (by decide)) A B =
      Submodule.map₂ (bracketLayer (by decide) (by decide)) B A := by
  apply le_antisymm
  · apply Submodule.map₂_le.mpr
    intro x hx y hy
    rw [bracketLayer_one_two]
    exact Submodule.neg_mem _ (Submodule.apply_mem_map₂ _ hy hx)
  · apply Submodule.map₂_le.mpr
    intro y hy x hx
    rw [← neg_neg (bracketLayer (by decide) (by decide) y x), ← bracketLayer_one_two]
    exact Submodule.neg_mem _ (Submodule.apply_mem_map₂ _ hx hy)

end T3.AssociatedGraded

namespace T3.Coproduct.Presentation

open AssociatedGraded

variable {I J : Type*}

/-- The left free-factor retraction kills all generators of the right factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
def freeProjectionLeft : Free (I ⊕ J) →* Free I :=
  liftFree Free.pow_three (MonoidHom.id _) 1

/-- The right free-factor retraction kills all generators of the left factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
def freeProjectionRight : Free (I ⊕ J) →* Free J :=
  liftFree Free.pow_three 1 (MonoidHom.id _)

/-- The left projection is a retraction on the entire left free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
@[simp]
theorem freeProjectionLeft_map_inl (x : Free I) :
    freeProjectionLeft (Free.map (Sum.inl : I → I ⊕ J) x) = x :=
  liftFree_map_inl Free.pow_three (MonoidHom.id _) 1 x

/-- The left projection kills the entire right free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
@[simp]
theorem freeProjectionLeft_map_inr (x : Free J) :
    freeProjectionLeft (Free.map (Sum.inr : J → I ⊕ J) x) = 1 :=
  liftFree_map_inr Free.pow_three (MonoidHom.id _) 1 x

/-- The right projection kills the entire left free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
@[simp]
theorem freeProjectionRight_map_inl (x : Free I) :
    freeProjectionRight (Free.map (Sum.inl : I → I ⊕ J) x) = 1 :=
  liftFree_map_inl Free.pow_three 1 (MonoidHom.id _) x

/-- The right projection is a retraction on the entire right free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor identifications.
-/
@[simp]
theorem freeProjectionRight_map_inr (x : Free J) :
    freeProjectionRight (Free.map (Sum.inr : J → I ⊕ J) x) = x :=
  liftFree_map_inr Free.pow_three 1 (MonoidHom.id _) x

/-- The left projection and inclusion compose to the identity homomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor retraction.
-/
@[simp]
theorem freeProjectionLeft_comp_map_inl :
    (freeProjectionLeft (I := I) (J := J)).comp (Free.map Sum.inl) = MonoidHom.id _ := by
  ext x
  simp

/-- The right projection and inclusion compose to the identity homomorphism.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, factor retraction.
-/
@[simp]
theorem freeProjectionRight_comp_map_inr :
    (freeProjectionRight (I := I) (J := J)).comp (Free.map Sum.inr) = MonoidHom.id _ := by
  ext x
  simp

/-- The left relation space is the transported ambient graded image computed in the left factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 980–982.
-/
theorem subgroupImage_map_inl (K : Subgroup (Free I)) (n : ℕ) :
    subgroupImage (K.map (Free.map (Sum.inl : I → I ⊕ J))) n =
      (subgroupImage K n).map (mapLayer (Free.map Sum.inl) n) :=
  subgroupImage_map_of_leftInverse _ freeProjectionLeft freeProjectionLeft_comp_map_inl K n

/-- The right relation space is the transported ambient graded image computed in the right factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 980–982.
-/
theorem subgroupImage_map_inr (K : Subgroup (Free J)) (n : ℕ) :
    subgroupImage (K.map (Free.map (Sum.inr : J → I ⊕ J))) n =
      (subgroupImage K n).map (mapLayer (Free.map Sum.inr) n) :=
  subgroupImage_map_of_leftInverse _ freeProjectionRight freeProjectionRight_comp_map_inr K n

/-- Every first-degree vector is the sum of its two canonical factor projections.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, equality `V = V₀ ⊕ V₁`.
-/
theorem mapLayer_inl_projection_add_inr_projection (x : Layer (Free (I ⊕ J)) 1) :
    mapLayer (Free.map Sum.inl) 1 (mapLayer freeProjectionLeft 1 x) +
      mapLayer (Free.map Sum.inr) 1 (mapLayer freeProjectionRight 1 x) = x := by
  let e : Layer (Free (I ⊕ J)) 1 →ₗ[ZMod 3] Layer (Free (I ⊕ J)) 1 :=
    (mapLayer (Free.map Sum.inl) 1).comp (mapLayer freeProjectionLeft 1) +
      (mapLayer (Free.map Sum.inr) 1).comp (mapLayer freeProjectionRight 1)
  let q : Free (I ⊕ J) →* MulLayer (Free (I ⊕ J)) 1 :=
    (QuotientGroup.mk' (relation (Free (I ⊕ J)) 1)).comp
      (Subgroup.topEquiv.symm.toMonoidHom)
  let h : MulLayer (Free (I ⊕ J)) 1 →* MulLayer (Free (I ⊕ J)) 1 :=
    MonoidHom.toAdditive.symm e.toAddMonoidHom
  have hh : h.comp q = q := by
    apply Free.hom_ext
    intro a
    apply Additive.ofMul.injective
    change e (mk _ 1 ⟨Free.of a, Subgroup.mem_top _⟩) =
      mk _ 1 ⟨Free.of a, Subgroup.mem_top _⟩
    cases a <;>
      simp [e, mapLayer_mk, termMap, freeProjectionLeft, freeProjectionRight, liftFree]
  obtain ⟨a, rfl⟩ := mk_surjective (Free (I ⊕ J)) 1 x
  exact congrArg Additive.ofMul (DFunLike.congr_fun hh (a : Free (I ⊕ J)))

/-- The two first-degree factor images exhaust the first layer of the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, equality `V = V₀ ⊕ V₁`.
-/
theorem range_mapLayer_inl_sup_range_mapLayer_inr_one :
    LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1) ⊔
      LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1) = ⊤ := by
  apply top_unique
  intro x _
  rw [← mapLayer_inl_projection_add_inr_projection x]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
    (LinearMap.mem_range_self _ _)

variable (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))

/-- The relation product's graded image is the sum of the two factor relation spaces,
transported by the canonical free inclusions.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 980–996.
-/
theorem subgroupImage_relationSubgroup_eq_sup_map (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) (n : ℕ) :
    subgroupImage (relationSubgroup K₀ K₁) n =
      (subgroupImage K₀ n).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) n) ⊔
        (subgroupImage K₁ n).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) n) := by
  rw [subgroupImage_relationSubgroup K₀ K₁ h₀ h₁ n,
    subgroupImage_map_inl, subgroupImage_map_inr]

/-- The normal closure of the factor relations has zero first-degree image.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof line 960.
-/
theorem subgroupImage_relationKernel_one (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) : subgroupImage (relationKernel K₀ K₁) 1 = ⊥ :=
  subgroupImage_eq_bot_of_le 1 (relationKernel_le_commutator K₀ K₁ h₀ h₁)

/-- The second-degree relations of the normal closure are exactly the transported factor images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 960–987.
-/
theorem subgroupImage_relationKernel_two (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 2 =
      (subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2) ⊔
        (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2) := by
  rw [relationKernel, subgroupImage_normalClosure_two
    (relationSubgroup_le_commutator K₀ K₁ h₀ h₁),
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁]

/-- The third-degree relations consist of the two factor images and brackets of the
second-degree relations with the full first layer of the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof lines 993–996.
-/
theorem subgroupImage_relationKernel_three (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 3 =
      ((subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) ⊔
        (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3)) ⊔
      Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
        ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2) ⊔
          (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)) ⊤ := by
  rw [relationKernel, subgroupImage_normalClosure_three
    (relationSubgroup_le_commutator K₀ K₁ h₀ h₁),
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁,
    subgroupImage_relationSubgroup_eq_sup_map K₀ K₁ h₀ h₁]

/-- Normal left-factor relations absorb their brackets with the left first-degree component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, inclusion `R₀ ∧ V₀ ⊆ S₀`.
-/
theorem bracketLayer_inl_relation_le [K₀.Normal] :
    Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
      ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2))
      (LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1)) ≤
        (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) :=
  bracketLayer_map_subgroupImage_range_le _ K₀ (by decide) (by decide)

/-- Normal right-factor relations absorb their brackets with the right first-degree component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, inclusion `R₁ ∧ V₁ ⊆ S₁`.
-/
theorem bracketLayer_inr_relation_le [K₁.Normal] :
    Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
      ((subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2))
      (LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)) ≤
        (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3) :=
  bracketLayer_map_subgroupImage_range_le _ K₁ (by decide) (by decide)

/-- After absorbing the same-factor brackets, the third-degree relation space consists of
the two pure relation spaces and the two mixed bracket spaces, in the paper's order.

The right mixed term is written with the left first-degree factor first. Its sign change is
valid because this is an equality of subspaces, not an equality of the two bracket maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, equality on line 997.
-/
theorem subgroupImage_relationKernel_three_eq_four_blocks [K₀.Normal] [K₁.Normal]
    (h₀ : K₀ ≤ commutator (Free I)) (h₁ : K₁ ≤ commutator (Free J)) :
    subgroupImage (relationKernel K₀ K₁) 3 =
      (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3) ⊔
      Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
        ((subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2))
        (LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)) ⊔
      Submodule.map₂ (bracketLayer (i := 1) (j := 2) (by decide) (by decide))
        (LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1))
        ((subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)) ⊔
      (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3) := by
  let R₀ := (subgroupImage K₀ 2).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 2)
  let R₁ := (subgroupImage K₁ 2).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 2)
  let S₀ := (subgroupImage K₀ 3).map (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 3)
  let S₁ := (subgroupImage K₁ 3).map (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 3)
  let V₀ := LinearMap.range (mapLayer (Free.map (Sum.inl : I → I ⊕ J)) 1)
  let V₁ := LinearMap.range (mapLayer (Free.map (Sum.inr : J → I ⊕ J)) 1)
  let b := bracketLayer (G := Free (I ⊕ J)) (i := 2) (j := 1) (by decide) (by decide)
  rw [subgroupImage_relationKernel_three K₀ K₁ h₀ h₁, map₂_bracketLayer_one_two]
  change (S₀ ⊔ S₁) ⊔ Submodule.map₂ b (R₀ ⊔ R₁) ⊤ =
    S₀ ⊔ Submodule.map₂ b R₀ V₁ ⊔ Submodule.map₂ b R₁ V₀ ⊔ S₁
  rw [← range_mapLayer_inl_sup_range_mapLayer_inr_one (I := I) (J := J),
    Submodule.map₂_sup_left, Submodule.map₂_sup_right, Submodule.map₂_sup_right]
  calc
    _ = (S₀ ⊔ Submodule.map₂ b R₀ V₀) ⊔ Submodule.map₂ b R₀ V₁ ⊔
        Submodule.map₂ b R₁ V₀ ⊔ (S₁ ⊔ Submodule.map₂ b R₁ V₁) := by ac_rfl
    _ = _ := by
      rw [sup_eq_left.mpr (bracketLayer_inl_relation_le (J := J) K₀),
        sup_eq_left.mpr (bracketLayer_inr_relation_le (I := I) K₁)]

end T3.Coproduct.Presentation
