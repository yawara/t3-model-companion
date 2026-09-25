/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Associated graded layers of a quotient group

The natural map `G → G ⧸ N` maps each lower central term onto the corresponding quotient term.
The induced map on each associated graded layer is therefore surjective. Its kernel is the
ambient graded image of `N`: a representative whose image lies in the next central term can
be divided by a lift from that next term to obtain a representative in `N`.

The first isomorphism theorem then gives the paper's canonical linear equivalence. Its formulas
on initial forms fix the canonical map. The construction works in every rank and every degree;
the additional degree zero in the Lean grading is zero on both sides.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31.
-/

@[expose] public section

namespace T3

variable {G : Type*} [Group G]

/-- A quotient of an exponent-three group again has exponent dividing three.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem hasExponentThree_quotient (hG : HasExponentThree G) (N : Subgroup G) [N.Normal] :
    HasExponentThree (G ⧸ N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [← map_pow, hG, map_one]

/-- The canonical exponent-three condition on a quotient group.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
instance quotientHasExponentThree [Fact (HasExponentThree G)] (N : Subgroup G) [N.Normal] :
    Fact (HasExponentThree (G ⧸ N)) := ⟨hasExponentThree_quotient Fact.out N⟩

namespace AssociatedGraded

variable {H : Type*} [Group H]

/-- A surjective group homomorphism maps each lower central term onto the target term.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem map_term_eq_of_surjective (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    (term G n).map f = term H n := by
  rw [term, term, Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective f hf]

/-- Restriction of a surjective homomorphism to corresponding central terms is surjective.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem termMap_surjective (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (termMap f n) := by
  intro y
  have hy : (y : H) ∈ (term G n).map f := by
    rw [map_term_eq_of_surjective f hf]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- A surjective group homomorphism induces a surjective additive map on every layer.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem mapAdd_surjective (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (mapAdd f n) := by
  intro y
  obtain ⟨y, rfl⟩ := mk_surjective H n y
  obtain ⟨x, rfl⟩ := termMap_surjective f hf n y
  exact ⟨mk G n x, mapAdd_mk f n x⟩

variable [Fact (HasExponentThree G)]

/-- A surjective homomorphism of exponent-three groups induces surjective linear maps on layers.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem mapLayer_surjective [Fact (HasExponentThree H)] (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) : Function.Surjective (mapLayer f n) :=
  mapAdd_surjective f hf n

/-- The kernel of a surjective homomorphism on a graded layer is the ambient graded image
of its group kernel. This is the quotient formula for a specified presentation map.

Paper-ID: preliminaries.graded_quotient, structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, applied in
`proposition:gr of free product`, proof lines 971–977.
-/
theorem mapLayer_ker [Fact (HasExponentThree H)] (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    (mapLayer f n).ker = subgroupImage f.ker n := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := mk_surjective G n x
    rw [LinearMap.mem_ker, mapLayer_mk, mk_eq_zero] at hx
    have hmap : ((⊤ : Subgroup G).lowerCentralSeries n).map f =
        (⊤ : Subgroup H).lowerCentralSeries n := by
      rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective _ hf]
    have hx' : f (a : G) ∈ ((⊤ : Subgroup G).lowerCentralSeries n).map f := by
      rw [hmap]
      exact hx
    obtain ⟨b, hb, hab⟩ := hx'
    have hb' : b ∈ term G n :=
      (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.sub_le n 1) hb
    apply (mem_subgroupImage f.ker n _).mpr
    refine ⟨a / ⟨b, hb'⟩, ?_, ?_⟩
    · change f ((a : G) / b) = 1
      rw [map_div, hab, div_self']
    · change mk G n a - mk G n ⟨b, hb'⟩ = mk G n a
      rw [(mk_eq_zero G n ⟨b, hb'⟩).mpr hb, sub_zero]
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage f.ker n x).mp hx
    rw [LinearMap.mem_ker, mapLayer_mk, mk_eq_zero]
    change f (a : G) ∈ (⊤ : Subgroup H).lowerCentralSeries n
    rw [MonoidHom.mem_ker.mp ha]
    exact Subgroup.one_mem _

/-- The quotient homomorphism induces a surjection on every associated graded layer.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem mapLayer_quotient_surjective (N : Subgroup G) [N.Normal] (n : ℕ) :
    Function.Surjective (mapLayer (QuotientGroup.mk' N) n) :=
  mapLayer_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) n

/-- The kernel of the quotient map on a layer is exactly the ambient graded image of `N`.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
theorem mapLayer_quotient_ker (N : Subgroup G) [N.Normal] (n : ℕ) :
    (mapLayer (QuotientGroup.mk' N) n).ker = subgroupImage N n := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := mk_surjective G n x
    rw [LinearMap.mem_ker, mapLayer_mk, mk_eq_zero] at hx
    have hmap : ((⊤ : Subgroup G).lowerCentralSeries n).map (QuotientGroup.mk' N) =
        (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries n := by
      rw [Subgroup.map_lowerCentralSeries,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have hx' : (QuotientGroup.mk' N) (a : G) ∈
        ((⊤ : Subgroup G).lowerCentralSeries n).map (QuotientGroup.mk' N) := by
      rw [hmap]
      exact hx
    obtain ⟨b, hb, hab⟩ := hx'
    have hb' : b ∈ term G n :=
      (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.sub_le n 1) hb
    apply (mem_subgroupImage N n _).mpr
    refine ⟨a / ⟨b, hb'⟩,
      (QuotientGroup.eq_iff_div_mem (N := N) (x := (a : G)) (y := b)).mp hab.symm, ?_⟩
    change mk G n a - mk G n ⟨b, hb'⟩ = mk G n a
    rw [(mk_eq_zero G n ⟨b, hb'⟩).mpr hb, sub_zero]
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage N n x).mp hx
    rw [LinearMap.mem_ker, mapLayer_mk, mk_eq_zero]
    change (QuotientGroup.mk' N) (a : G) ∈ (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries n
    rw [show (QuotientGroup.mk' N) (a : G) = 1 from (QuotientGroup.eq_one_iff _).mpr ha]
    exact Subgroup.one_mem _

/-- The canonical equivalence `grₙ(G/N) ≃ grₙ(G) / grₙᴳ(N)` from the paper.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
noncomputable def quotientLayerEquiv (N : Subgroup G) [N.Normal] (n : ℕ) :
    Layer (G ⧸ N) n ≃ₗ[ZMod 3] (Layer G n ⧸ subgroupImage N n) :=
  ((mapLayer (QuotientGroup.mk' N) n).quotKerEquivOfSurjective
    (mapLayer_quotient_surjective N n)).symm.trans
      (Submodule.quotEquivOfEq _ _ (mapLayer_quotient_ker N n))

/-- The canonical equivalence sends the image of a layer element to its class modulo `grₙᴳ(N)`.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
@[simp]
theorem quotientLayerEquiv_mapLayer (N : Subgroup G) [N.Normal] (n : ℕ) (x : Layer G n) :
    quotientLayerEquiv N n (mapLayer (QuotientGroup.mk' N) n x) =
      Submodule.Quotient.mk x := by
  simp [quotientLayerEquiv]

/-- On initial forms, the quotient equivalence sends a representative to its ambient layer class.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
@[simp]
theorem quotientLayerEquiv_mk (N : Subgroup G) [N.Normal] (n : ℕ) (x : term G n) :
    quotientLayerEquiv N n (mk (G ⧸ N) n (termMap (QuotientGroup.mk' N) n x)) =
      Submodule.Quotient.mk (mk G n x) := by
  rw [← mapLayer_mk, quotientLayerEquiv_mapLayer]

/-- The inverse equivalence is induced by the natural quotient homomorphism.

Paper-ID: preliminaries.graded_quotient
TeX: T3_modelcompanion_v9.tex, `lemma:gr of quotient`, v9 Lemma 2.31. -/
@[simp]
theorem quotientLayerEquiv_symm_mk (N : Subgroup G) [N.Normal] (n : ℕ) (x : Layer G n) :
    (quotientLayerEquiv N n).symm (Submodule.Quotient.mk x) =
      mapLayer (QuotientGroup.mk' N) n x := by
  apply (quotientLayerEquiv N n).injective
  simp

end AssociatedGraded

end T3
