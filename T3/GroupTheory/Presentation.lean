/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Graded
public import T3.GroupTheory.Generation
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The free presentation determined by a lifted basis

Given any basis of the actual quotient `G / γ₂(G)` and any specified representatives of its
basis vectors, the induced free exponent-three homomorphism is surjective and its kernel lies
in the derived subgroup. Its map on the actual degree-one quotient is a linear isomorphism.
The index type need not be finite, countable, or supplied with an order.

The results keep the prescribed basis and representatives as parameters. Surjectivity uses
the paper's two commutator inclusions from `T3.GroupTheory.Generation`; the kernel argument
uses the actual degree-one coordinate basis.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, v4 Proposition 4.1, lines 753–799.
-/

@[expose] public section

open Module

namespace T3

namespace AssociatedGraded

variable (G : Type*) [Group G]

/-- The canonical group homomorphism to the multiplicative first graded quotient.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, abelianization quotient.
-/
def quotientOne : G →* MulLayer G 1 where
  toFun g := QuotientGroup.mk' (relation G 1) ⟨g, Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The first quotient homomorphism is the multiplicative form of the initial-form map.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, abelianization quotient.
-/
theorem quotientOne_apply (g : G) :
    quotientOne G g = (mk G 1 ⟨g, Subgroup.mem_top _⟩).toMul := rfl

/-- The first quotient has exactly the derived subgroup as kernel.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, abelianization quotient.
-/
theorem quotientOne_ker : (quotientOne G).ker = commutator G := by
  ext g
  exact QuotientGroup.eq_one_iff (⟨g, Subgroup.mem_top _⟩ : term G 1)

end AssociatedGraded

namespace Free

open AssociatedGraded

variable {G I : Type*} [Group G] [Fact (HasExponentThree G)]
  (hG : HasExponentThree G) (b : Basis I (ZMod 3) (Layer G 1)) (a : I → G)
  (ha : ∀ i, mk G 1 ⟨a i, Subgroup.mem_top _⟩ = b i)
include b ha

/-- The image of the prescribed lifted basis covers the abelianization of the target group.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, equality `G = H γ₂(G)`.
-/
theorem lift_range_sup_commutator_of_basis : (lift hG a).range ⊔ commutator G = ⊤ := by
  classical
  let φ := lift hG a
  have hrep (i : I) : quotientOne G (a i) = (b i).toMul :=
    congrArg Additive.toMul (ha i)
  have hmap : φ.range.map (quotientOne G) = ⊤ := by
    let S : Submodule (ZMod 3) (Layer G 1) :=
      (φ.range.map (quotientOne G)).toAddSubgroup.toZModSubmodule 3
    have hS : S = ⊤ := by
      apply top_unique
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (b i).toMul ∈ φ.range.map (quotientOne G)
      rw [← hrep i]
      exact Subgroup.mem_map.mpr ⟨a i, ⟨of i, lift_of hG a i⟩, rfl⟩
    apply Subgroup.toAddSubgroup.injective
    apply (AddSubgroup.toZModSubmodule 3).injective
    simpa [S] using hS
  have hker : (quotientOne G).ker ≤ φ.range ⊔ commutator G := by
    rw [quotientOne_ker]
    exact le_sup_right
  change φ.range ⊔ commutator G = ⊤
  rw [← Subgroup.comap_map_eq_self hker, Subgroup.map_sup, hmap]
  simp

/-- Any prescribed representatives of a basis of `G / γ₂(G)` generate `G`; equivalently,
the corresponding free exponent-three homomorphism is surjective.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, surjectivity assertion.
-/
theorem lift_surjective_of_basis : Function.Surjective (lift hG a) := by
  rw [← MonoidHom.range_eq_top]
  exact eq_top_of_sup_commutator_eq_top hG (lift_range_sup_commutator_of_basis hG b a ha)

/-- The induced map on the actual first graded quotient is bijective: it sends the free
generator basis to the specified basis of `G / γ₂(G)`.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, induced abelianization isomorphism.
-/
theorem mapLayer_lift_bijective_of_basis : Function.Bijective (mapLayer (lift hG a) 1) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let e : Layer (Free I) 1 ≃ₗ[ZMod 3] Layer G 1 := layerOneEquiv.trans b.repr.symm
  have he : mapLayer (lift hG a) 1 = e.toLinearMap := by
    apply (Basis.ofRepr (layerOneEquiv (I := I))).ext
    intro i
    have hi : (Basis.ofRepr (layerOneEquiv (I := I))) i =
        mk (Free I) 1 ⟨of i, Subgroup.mem_top _⟩ := by
      apply layerOneEquiv.injective
      change layerOneEquiv (layerOneEquiv.symm _) = _
      rw [LinearEquiv.apply_symm_apply, layerOneEquiv_of]
    rw [hi, mapLayer_mk]
    change mk G 1 ⟨lift hG a (of i), _⟩ =
      b.repr.symm (layerOneEquiv (mk (Free I) 1 ⟨of i, Subgroup.mem_top _⟩))
    rw [layerOneEquiv_of, Basis.repr_symm_single_one]
    simpa only [lift_of hG a i] using ha i
  rw [he]
  exact e.bijective

/-- The actual abelianization map of the specified free presentation, bundled as a linear
equivalence. Its underlying map is the induced quotient map, without changing representatives.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, induced abelianization isomorphism.
-/
noncomputable def liftLayerOneEquiv : Layer (Free I) 1 ≃ₗ[ZMod 3] Layer G 1 :=
  LinearEquiv.ofBijective (mapLayer (lift hG a) 1) (mapLayer_lift_bijective_of_basis hG b a ha)

/-- The presentation's first-layer equivalence is the map induced by the given free lift.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, induced abelianization isomorphism.
-/
@[simp]
theorem liftLayerOneEquiv_apply (x : Layer (Free I) 1) :
    liftLayerOneEquiv hG b a ha x = mapLayer (lift hG a) 1 x := rfl

/-- Every relation of the specified presentation lies in the derived subgroup of the free
exponent-three group.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, kernel assertion.
-/
theorem lift_ker_le_commutator_of_basis : (lift hG a).ker ≤ commutator (Free I) := by
  intro x hx
  apply (mk_eq_zero (Free I) 1 ⟨x, Subgroup.mem_top _⟩).mp
  apply (mapLayer_lift_bijective_of_basis hG b a ha).injective
  rw [map_zero, mapLayer_mk]
  apply (mk_eq_zero G 1 _).mpr
  change lift hG a x ∈ (⊤ : Subgroup G).lowerCentralSeries 1
  rw [MonoidHom.mem_ker.mp hx]
  exact Subgroup.one_mem _

/-- The presentation prescribed by any basis of the abelianization and any representatives
is surjective, with all its defining relations in the derived subgroup.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v4.tex, `proposition:lift`, v4 Proposition 4.1.
-/
theorem presentation_of_basis : Function.Surjective (lift hG a) ∧
    (lift hG a).ker ≤ commutator (Free I) :=
  ⟨lift_surjective_of_basis hG b a ha, lift_ker_le_commutator_of_basis hG b a ha⟩

end Free

end T3
