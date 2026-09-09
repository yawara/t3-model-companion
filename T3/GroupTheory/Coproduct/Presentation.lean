/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Basic
public import T3.GroupTheory.GradedNormalClosure

/-!
# The free presentation of a coproduct

For surjections `φ₀ : Free I →* G₀` and `φ₁ : Free J →* G₁`, the coproduct is canonically
`Free (I ⊕ J)` modulo the normal closure of the two transported kernels. The equivalence is
constructed from the universal properties of the free groups, quotients, and coproduct. Its
formulas keep the given presentations and the canonical inclusions fixed.

The relation-subgroup and descended-map constructions reuse earlier proofs
by Yawara Ishida.
The final comparison is with the ordinary free product modulo cubes used by this paper.
The derived-subgroup assumptions are needed only for the final containment lemmas.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, v4 Proposition 4.3,
proof lines 870–877, the identification of the coproduct with `F/L`.
-/

@[expose] public section

namespace T3.Coproduct.Presentation

variable {I J G₀ G₁ H : Type*} [Group G₀] [Group G₁] [Group H]

/-- The join of the two relation subgroups transported into the free group on the disjoint union.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, subgroup `K` in its proof. -/
def relationSubgroup (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    Subgroup (Free (I ⊕ J)) :=
  K₀.map (Free.map Sum.inl) ⊔ K₁.map (Free.map Sum.inr)

/-- The normal closure of the transported relations, the paper's subgroup `L`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, subgroup `L` in its proof. -/
def relationKernel (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    Subgroup (Free (I ⊕ J)) :=
  Subgroup.normalClosure (relationSubgroup K₀ K₁ : Set (Free (I ⊕ J)))

instance relationKernel_normal (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    (relationKernel K₀ K₁).Normal := Subgroup.normalClosure_normal

/-- The concrete quotient presentation on the disjoint union of generating sets.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient `F/L`. -/
abbrev Quotient (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :=
  Free (I ⊕ J) ⧸ relationKernel K₀ K₁

/-- The quotient presentation has exponent dividing three for every choice of relations.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient `F/L`. -/
theorem quotient_pow_three (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    HasExponentThree (Quotient K₀ K₁) := by
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, Free.pow_three, QuotientGroup.mk_one]

/-- The left free factor map to the quotient presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor maps. -/
def freeInl (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    Free I →* Quotient K₀ K₁ :=
  (QuotientGroup.mk' (relationKernel K₀ K₁)).comp (Free.map Sum.inl)

/-- The right free factor map to the quotient presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor maps. -/
def freeInr (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    Free J →* Quotient K₀ K₁ :=
  (QuotientGroup.mk' (relationKernel K₀ K₁)).comp (Free.map Sum.inr)

/-- The left relations vanish under the canonical left free factor map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, factor descent. -/
theorem le_ker_freeInl (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    K₀ ≤ (freeInl K₀ K₁).ker := by
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure
    ((show K₀.map (Free.map Sum.inl) ≤ relationSubgroup K₀ K₁ from le_sup_left)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))

/-- The right relations vanish under the canonical right free factor map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, factor descent. -/
theorem le_ker_freeInr (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J)) :
    K₁ ≤ (freeInr K₀ K₁).ker := by
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure
    ((show K₁.map (Free.map Sum.inr) ≤ relationSubgroup K₀ K₁ from le_sup_right)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))

/-- Combine homomorphisms on the two free factors using the disjoint union of generators.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, free factor universal property. -/
def liftFree (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H) :
    Free (I ⊕ J) →* H :=
  Free.lift hH (Sum.elim (fun i => f₀ (Free.of i)) (fun j => f₁ (Free.of j)))

/-- The combination restricts to the specified map on the left free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, free factor universal property. -/
@[simp]
theorem liftFree_map_inl (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H)
    (x : Free I) : liftFree hH f₀ f₁ (Free.map Sum.inl x) = f₀ x :=
  DFunLike.congr_fun (show (liftFree hH f₀ f₁).comp (Free.map Sum.inl) = f₀ from
    Free.hom_ext fun i => by simp [liftFree]) x

/-- The combination restricts to the specified map on the right free factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, free factor universal property. -/
@[simp]
theorem liftFree_map_inr (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H)
    (x : Free J) : liftFree hH f₀ f₁ (Free.map Sum.inr x) = f₁ x :=
  DFunLike.congr_fun (show (liftFree hH f₀ f₁).comp (Free.map Sum.inr) = f₁ from
    Free.hom_ext fun j => by simp [liftFree]) x

/-- Killing both factor relations kills their normal closure in the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient universal property. -/
theorem relationKernel_le_ker_liftFree (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))
    (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H)
    (h₀ : K₀ ≤ f₀.ker) (h₁ : K₁ ≤ f₁.ker) :
    relationKernel K₀ K₁ ≤ (liftFree hH f₀ f₁).ker := by
  apply Subgroup.normalClosure_le_normal
  apply SetLike.coe_subset_coe.mpr
  apply sup_le
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [MonoidHom.mem_ker, liftFree_map_inl] using h₀ hx
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [MonoidHom.mem_ker, liftFree_map_inr] using h₁ hx

/-- A pair of maps killing the two relation subgroups descends to the presented quotient.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient universal property. -/
def liftQuotient (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))
    (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H)
    (h₀ : K₀ ≤ f₀.ker) (h₁ : K₁ ≤ f₁.ker) : Quotient K₀ K₁ →* H :=
  QuotientGroup.lift _ (liftFree hH f₀ f₁)
    (relationKernel_le_ker_liftFree K₀ K₁ hH f₀ f₁ h₀ h₁)

/-- The quotient lift agrees with its free-level combination on representatives.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, quotient universal property. -/
@[simp]
theorem liftQuotient_mk (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))
    (hH : HasExponentThree H) (f₀ : Free I →* H) (f₁ : Free J →* H)
    (h₀ : K₀ ≤ f₀.ker) (h₁ : K₁ ≤ f₁.ker) (x : Free (I ⊕ J)) :
    liftQuotient K₀ K₁ hH f₀ f₁ h₀ h₁ (QuotientGroup.mk x) = liftFree hH f₀ f₁ x := rfl

variable (φ₀ : Free I →* G₀) (φ₁ : Free J →* G₁)

/-- The canonical homomorphism from the combined free generators to the actual coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, the map `F → G₀ * G₁`. -/
def presentationMap : Free (I ⊕ J) →* Coproduct G₀ G₁ :=
  liftFree Coproduct.pow_three (Coproduct.inl.comp φ₀) (Coproduct.inr.comp φ₁)

/-- On the left free factor, the presentation map is the given map followed by inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem presentationMap_map_inl (x : Free I) :
    presentationMap φ₀ φ₁ (Free.map Sum.inl x) = Coproduct.inl (φ₀ x) :=
  liftFree_map_inl _ _ _ x

/-- On the right free factor, the presentation map is the given map followed by inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem presentationMap_map_inr (x : Free J) :
    presentationMap φ₀ φ₁ (Free.map Sum.inr x) = Coproduct.inr (φ₁ x) :=
  liftFree_map_inr _ _ _ x

/-- The canonical map from the quotient presentation to the actual coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, the identification `F/L`. -/
def quotientToCoproduct : Quotient φ₀.ker φ₁.ker →* Coproduct G₀ G₁ :=
  liftQuotient φ₀.ker φ₁.ker Coproduct.pow_three
    (Coproduct.inl.comp φ₀) (Coproduct.inr.comp φ₁)
    (fun x hx => by simp [MonoidHom.mem_ker.mp hx])
    (fun x hx => by simp [MonoidHom.mem_ker.mp hx])

/-- The quotient comparison keeps the canonical combined presentation map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, representative formula. -/
@[simp]
theorem quotientToCoproduct_mk (x : Free (I ⊕ J)) :
    quotientToCoproduct φ₀ φ₁ (QuotientGroup.mk x) = presentationMap φ₀ φ₁ x := rfl

/-- The descended left factor map, determined by the prescribed surjective presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, factor descent to `F/L`. -/
noncomputable def factorLeft (h₀ : Function.Surjective φ₀) : G₀ →* Quotient φ₀.ker φ₁.ker :=
  φ₀.liftOfSurjective h₀ ⟨freeInl φ₀.ker φ₁.ker, le_ker_freeInl _ _⟩

/-- The descended right factor map, determined by the prescribed surjective presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, factor descent to `F/L`. -/
noncomputable def factorRight (h₁ : Function.Surjective φ₁) : G₁ →* Quotient φ₀.ker φ₁.ker :=
  φ₁.liftOfSurjective h₁ ⟨freeInr φ₀.ker φ₁.ker, le_ker_freeInr _ _⟩

/-- The left descent commutes with the given presentation map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem factorLeft_apply (h₀ : Function.Surjective φ₀) (x : Free I) :
    factorLeft φ₀ φ₁ h₀ (φ₀ x) = freeInl φ₀.ker φ₁.ker x :=
  φ₀.liftOfRightInverse_comp_apply _ _ _ x

/-- The right descent commutes with the given presentation map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem factorRight_apply (h₁ : Function.Surjective φ₁) (x : Free J) :
    factorRight φ₀ φ₁ h₁ (φ₁ x) = freeInr φ₀.ker φ₁.ker x :=
  φ₁.liftOfRightInverse_comp_apply _ _ _ x

/-- The quotient comparison agrees with the left free factor inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientToCoproduct_freeInl (x : Free I) :
    quotientToCoproduct φ₀ φ₁ (freeInl φ₀.ker φ₁.ker x) = Coproduct.inl (φ₀ x) :=
  presentationMap_map_inl φ₀ φ₁ x

/-- The quotient comparison agrees with the right free factor inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientToCoproduct_freeInr (x : Free J) :
    quotientToCoproduct φ₀ φ₁ (freeInr φ₀.ker φ₁.ker x) = Coproduct.inr (φ₁ x) :=
  presentationMap_map_inr φ₀ φ₁ x

/-- The quotient comparison sends the descended left factor to the canonical coproduct factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientToCoproduct_factorLeft (h₀ : Function.Surjective φ₀) (g : G₀) :
    quotientToCoproduct φ₀ φ₁ (factorLeft φ₀ φ₁ h₀ g) = Coproduct.inl g := by
  obtain ⟨x, rfl⟩ := h₀ g
  rw [factorLeft_apply, quotientToCoproduct_freeInl]

/-- The quotient comparison sends the descended right factor to the canonical coproduct factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientToCoproduct_factorRight (h₁ : Function.Surjective φ₁) (g : G₁) :
    quotientToCoproduct φ₀ φ₁ (factorRight φ₀ φ₁ h₁ g) = Coproduct.inr g := by
  obtain ⟨x, rfl⟩ := h₁ g
  rw [factorRight_apply, quotientToCoproduct_freeInr]

/-- The canonical map back from the coproduct to the quotient presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, the identification `F/L`. -/
noncomputable def coproductToQuotient (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) : Coproduct G₀ G₁ →* Quotient φ₀.ker φ₁.ker :=
  Coproduct.lift (quotient_pow_three _ _) (factorLeft φ₀ φ₁ h₀) (factorRight φ₀ φ₁ h₁)

/-- The reverse comparison sends the left coproduct factor to its descended presentation map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem coproductToQuotient_inl (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) (g : G₀) :
    coproductToQuotient φ₀ φ₁ h₀ h₁ (Coproduct.inl g) = factorLeft φ₀ φ₁ h₀ g := rfl

/-- The reverse comparison sends the right coproduct factor to its descended presentation map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem coproductToQuotient_inr (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) (g : G₁) :
    coproductToQuotient φ₀ φ₁ h₀ h₁ (Coproduct.inr g) = factorRight φ₀ φ₁ h₁ g := rfl

/-- The reverse comparison composed with the combined free presentation is the quotient map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, inverse-map verification. -/
theorem coproductToQuotient_comp_presentationMap (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) :
    (coproductToQuotient φ₀ φ₁ h₀ h₁).comp (presentationMap φ₀ φ₁) =
      QuotientGroup.mk' (relationKernel φ₀.ker φ₁.ker) := by
  apply Free.hom_ext
  intro x
  cases x with
  | inl i =>
    simp [presentationMap, liftFree, coproductToQuotient, freeInl]
  | inr j =>
    simp [presentationMap, liftFree, coproductToQuotient, freeInr]

/-- The two canonical comparisons are inverse on the quotient presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, inverse-map verification. -/
theorem coproductToQuotient_comp_quotientToCoproduct (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) :
    (coproductToQuotient φ₀ φ₁ h₀ h₁).comp (quotientToCoproduct φ₀ φ₁) =
      MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  exact DFunLike.congr_fun (coproductToQuotient_comp_presentationMap φ₀ φ₁ h₀ h₁) x

/-- The two canonical comparisons are inverse on the actual coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, inverse-map verification. -/
theorem quotientToCoproduct_comp_coproductToQuotient (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) :
    (quotientToCoproduct φ₀ φ₁).comp (coproductToQuotient φ₀ φ₁ h₀ h₁) =
      MonoidHom.id _ := by
  apply Coproduct.hom_ext <;> intro g <;> simp

/-- The paper's canonical identification of the coproduct with the combined free presentation.

Only surjectivity of the given presentations is required. No rank, order, or derived-kernel
assumption is imposed here.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, identification `F/L`. -/
noncomputable def quotientEquiv (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁) :
    Quotient φ₀.ker φ₁.ker ≃* Coproduct G₀ G₁ :=
  MonoidHom.toMulEquiv (quotientToCoproduct φ₀ φ₁) (coproductToQuotient φ₀ φ₁ h₀ h₁)
    (coproductToQuotient_comp_quotientToCoproduct φ₀ φ₁ h₀ h₁)
    (quotientToCoproduct_comp_coproductToQuotient φ₀ φ₁ h₀ h₁)

/-- The canonical quotient equivalence keeps the combined presentation on every representative.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, representative formula. -/
@[simp]
theorem quotientEquiv_mk (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁)
    (x : Free (I ⊕ J)) :
    quotientEquiv φ₀ φ₁ h₀ h₁ (QuotientGroup.mk x) = presentationMap φ₀ φ₁ x := rfl

/-- The left free generator maps to its prescribed image in the left coproduct factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, generator formula. -/
@[simp]
theorem presentationMap_of_inl (i : I) :
    presentationMap φ₀ φ₁ (Free.of (Sum.inl i)) = Coproduct.inl (φ₀ (Free.of i)) :=
  Free.lift_of Coproduct.pow_three _ _

/-- The right free generator maps to its prescribed image in the right coproduct factor.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, generator formula. -/
@[simp]
theorem presentationMap_of_inr (j : J) :
    presentationMap φ₀ φ₁ (Free.of (Sum.inr j)) = Coproduct.inr (φ₁ (Free.of j)) :=
  Free.lift_of Coproduct.pow_three _ _

/-- The combined free presentation is surjective whenever both factor presentations are.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, the presentation `F → G₀ * G₁`. -/
theorem presentationMap_surjective (h₀ : Function.Surjective φ₀)
    (h₁ : Function.Surjective φ₁) : Function.Surjective (presentationMap φ₀ φ₁) :=
  (quotientEquiv φ₀ φ₁ h₀ h₁).surjective.comp (QuotientGroup.mk'_surjective _)

/-- The combined presentation has exactly the normal closure of the two transported kernels.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, the kernel `L` of `F → G₀ * G₁`. -/
theorem presentationMap_ker (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁) :
    (presentationMap φ₀ φ₁).ker = relationKernel φ₀.ker φ₁.ker := by
  ext x
  rw [MonoidHom.mem_ker, ← quotientEquiv_mk φ₀ φ₁ h₀ h₁]
  rw [map_eq_one_iff _ (quotientEquiv φ₀ φ₁ h₀ h₁).injective, QuotientGroup.eq_one_iff]

/-- The canonical equivalence identifies the descended left map with the actual factor inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientEquiv_factorLeft (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁)
    (g : G₀) : quotientEquiv φ₀ φ₁ h₀ h₁ (factorLeft φ₀ φ₁ h₀ g) = Coproduct.inl g :=
  quotientToCoproduct_factorLeft φ₀ φ₁ h₀ g

/-- The canonical equivalence identifies the descended right map with the actual factor inclusion.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, canonical factor formula. -/
@[simp]
theorem quotientEquiv_factorRight (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁)
    (g : G₁) : quotientEquiv φ₀ φ₁ h₀ h₁ (factorRight φ₀ φ₁ h₁ g) = Coproduct.inr g :=
  quotientToCoproduct_factorRight φ₀ φ₁ h₁ g

/-- The inverse equivalence preserves the left factor under the specified presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, inverse factor formula. -/
@[simp]
theorem quotientEquiv_symm_inl (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁)
    (g : G₀) : (quotientEquiv φ₀ φ₁ h₀ h₁).symm (Coproduct.inl g) =
      factorLeft φ₀ φ₁ h₀ g := rfl

/-- The inverse equivalence preserves the right factor under the specified presentation.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, inverse factor formula. -/
@[simp]
theorem quotientEquiv_symm_inr (h₀ : Function.Surjective φ₀) (h₁ : Function.Surjective φ₁)
    (g : G₁) : (quotientEquiv φ₀ φ₁ h₀ h₁).symm (Coproduct.inr g) =
      factorRight φ₀ φ₁ h₁ g := rfl

private theorem map_commutator_le_commutator {A C : Type*} [Group A] [Group C]
    (f : A →* C) : (commutator A).map f ≤ commutator C := by
  rw [commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

variable (K₀ : Subgroup (Free I)) (K₁ : Subgroup (Free J))

/-- If both factor relation subgroups are derived, their join is derived in the combined free group.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, containment of `K` in `γ₂(F)`. -/
theorem relationSubgroup_le_commutator (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    relationSubgroup K₀ K₁ ≤ commutator (Free (I ⊕ J)) :=
  sup_le ((Subgroup.map_mono h₀).trans (map_commutator_le_commutator _))
    ((Subgroup.map_mono h₁).trans (map_commutator_le_commutator _))

/-- Derived factor relations have normal closure contained in the combined derived subgroup.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, containment of `L` in `γ₂(F)`. -/
theorem relationKernel_le_commutator (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    relationKernel K₀ K₁ ≤ commutator (Free (I ⊕ J)) :=
  T3.normalClosure_le_commutator (relationSubgroup_le_commutator K₀ K₁ h₀ h₁)

open scoped Pointwise

/-- In the paper's derived presentations, the join `K` is the product of the transported kernels.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, equality `K = K₀ K₁`. -/
theorem relationSubgroup_coe_eq_mul (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) :
    (relationSubgroup K₀ K₁ : Set (Free (I ⊕ J))) =
      (↑(K₀.map (Free.map (Sum.inl : I → I ⊕ J))) : Set (Free (I ⊕ J))) *
        (↑(K₁.map (Free.map (Sum.inr : J → I ⊕ J))) : Set (Free (I ⊕ J))) := by
  apply Subgroup.coe_mul_of_left_le_normalizer_right
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (commute_of_mem_commutator Free.pow_three
    (((Subgroup.map_mono h₁).trans (map_commutator_le_commutator _)) hb)
    (((Subgroup.map_mono h₀).trans (map_commutator_le_commutator _)) ha)).eq

private def projectionLeft : Free (I ⊕ J) →* Free I :=
  liftFree Free.pow_three (MonoidHom.id _) 1

/-- Intersecting the product of the factor relations with any lower central term is componentwise.

The left retraction kills the right factor, so membership of a product in a lower central term
forces its left factor into that term. The right factor then belongs by subgroup closure.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`,
componentwise relation intersections. -/
theorem relationSubgroup_inf_term (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) (n : ℕ) :
    relationSubgroup K₀ K₁ ⊓ AssociatedGraded.term (Free (I ⊕ J)) n =
      (K₀.map (Free.map Sum.inl) ⊓ AssociatedGraded.term (Free (I ⊕ J)) n) ⊔
        (K₁.map (Free.map Sum.inr) ⊓ AssociatedGraded.term (Free (I ⊕ J)) n) := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (↑(K₀.map (Free.map (Sum.inl : I → I ⊕ J))) : Set (Free (I ⊕ J))) *
        (↑(K₁.map (Free.map (Sum.inr : J → I ⊕ J))) : Set (Free (I ⊕ J))) := by
      rw [← relationSubgroup_coe_eq_mul K₀ K₁ h₀ h₁]
      exact hx.1
    obtain ⟨a, ha, b, hb, rfl⟩ := hp
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have ha' : a ∈ AssociatedGraded.term (Free I) n := by
      have h := (AssociatedGraded.termMap (projectionLeft (I := I) (J := J)) n
        ⟨Free.map Sum.inl a * Free.map Sum.inr b, hx.2⟩).property
      simpa [projectionLeft, map_mul] using h
    have hal : Free.map (Sum.inl : I → I ⊕ J) a ∈
        AssociatedGraded.term (Free (I ⊕ J)) n :=
      (AssociatedGraded.termMap (Free.map Sum.inl) n ⟨a, ha'⟩).property
    have hbr : Free.map (Sum.inr : J → I ⊕ J) b ∈
        AssociatedGraded.term (Free (I ⊕ J)) n := by
      have h := (AssociatedGraded.term (Free (I ⊕ J)) n).mul_mem
        ((AssociatedGraded.term (Free (I ⊕ J)) n).inv_mem hal) hx.2
      simpa only [inv_mul_cancel_left] using h
    exact Subgroup.mul_mem_sup ⟨Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, hal⟩
      ⟨Subgroup.mem_map.mpr ⟨b, hb, rfl⟩, hbr⟩
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

/-- The ambient graded image of the relation product is the sum of the two factor images.

Together with transport of the factor images, this supplies the paper's decompositions of
`gr₂(K)` and `gr₃(K)` before taking the normal closure.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`,
degree-two and degree-three relations. -/
theorem subgroupImage_relationSubgroup (h₀ : K₀ ≤ commutator (Free I))
    (h₁ : K₁ ≤ commutator (Free J)) (n : ℕ) :
    AssociatedGraded.subgroupImage (relationSubgroup K₀ K₁) n =
      AssociatedGraded.subgroupImage (K₀.map (Free.map (Sum.inl : I → I ⊕ J))) n ⊔
        AssociatedGraded.subgroupImage (K₁.map (Free.map (Sum.inr : J → I ⊕ J))) n := by
  rw [← AssociatedGraded.subgroupImage_inf_term (relationSubgroup K₀ K₁) n,
    relationSubgroup_inf_term K₀ K₁ h₀ h₁ n,
    AssociatedGraded.subgroupImage_sup_of_le _ _ n inf_le_right inf_le_right,
    AssociatedGraded.subgroupImage_inf_term, AssociatedGraded.subgroupImage_inf_term]

end T3.Coproduct.Presentation
