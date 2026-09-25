/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded

/-!
# Transport of ambient graded images along retractions

An embedding with a group retraction reflects every lower central term. Consequently its
map on each graded layer is injective, and the ambient graded image of a transported subgroup
is exactly the transported graded image. The latter statement is needed for the two factor
relation subgroups in the coproduct proof; it makes no homogeneity assumption on those subgroups.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, proof, lines 995–1016.
-/

@[expose] public section

namespace T3.AssociatedGraded

variable {G H : Type*} [Group G] [Group H]

/-- A group embedding with a left inverse reflects the lower central filtration.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor retractions.
-/
theorem mem_term_map_iff_of_leftInverse (f : G →* H) (r : H →* G)
    (h : r.comp f = MonoidHom.id G) (n : ℕ) (x : G) : f x ∈ term H n ↔ x ∈ term G n := by
  constructor
  · intro hx
    have hr := (termMap r n ⟨f x, hx⟩).property
    change r (f x) ∈ term G n at hr
    simpa only [← MonoidHom.comp_apply, h, MonoidHom.id_apply] using hr
  · intro hx
    exact (termMap f n ⟨x, hx⟩).property

variable [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- A retraction induces a left inverse on every actual graded quotient.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor graded inclusions.
-/
theorem mapLayer_leftInverse (f : G →* H) (r : H →* G)
    (h : r.comp f = MonoidHom.id G) (n : ℕ) :
    Function.LeftInverse (mapLayer r n) (mapLayer f n) := by
  intro x
  rw [← LinearMap.comp_apply, ← mapLayer_comp, h, mapLayer_id]
  rfl

/-- A group homomorphism with a retraction induces an injective map on each graded layer.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor graded inclusions.
-/
theorem mapLayer_injective_of_leftInverse (f : G →* H) (r : H →* G)
    (h : r.comp f = MonoidHom.id G) (n : ℕ) : Function.Injective (mapLayer f n) :=
  (mapLayer_leftInverse f r h n).injective

/-- A subgroup which is the range of a group retraction is strict for the lower central series.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, factor inclusions.
-/
theorem isStrict_range_of_leftInverse (f : G →* H) (r : H →* G)
    (h : r.comp f = MonoidHom.id G) : IsStrict f.range := by
  have hf : Function.Injective f :=
    (show Function.LeftInverse r f from fun x => DFunLike.congr_fun h x).injective
  apply (map_injective_iff_isStrict f hf).mp
  exact (map_injective_iff f).mpr (mapLayer_injective_of_leftInverse f r h)

/-- Transporting a subgroup along a homomorphism with a retraction commutes with taking its
ambient graded image. No normality or homogeneous decomposition of the subgroup is assumed.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, identification of `Rₙ` and `Sₙ`.
-/
theorem subgroupImage_map_of_leftInverse (f : G →* H) (r : H →* G)
    (h : r.comp f = MonoidHom.id G) (K : Subgroup G) (n : ℕ) :
    subgroupImage (K.map f) n = (subgroupImage K n).map (mapLayer f n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage (K.map f) n x).mp hx
    obtain ⟨k, hk, he⟩ := ha
    have hkn : k ∈ term G n :=
      (mem_term_map_iff_of_leftInverse f r h n k).mp (he ▸ a.property)
    refine Submodule.mem_map.mpr ⟨mk G n ⟨k, hkn⟩,
      (mem_subgroupImage K n _).mpr ⟨⟨k, hkn⟩, hk, rfl⟩, ?_⟩
    rw [mapLayer_mk]
    congr 1
    exact Subtype.ext he
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage K n y).mp hy
    exact (mem_subgroupImage (K.map f) n _).mpr
      ⟨termMap f n a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩

end T3.AssociatedGraded
