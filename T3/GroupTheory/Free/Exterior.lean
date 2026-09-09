/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Graded
public import T3.LinearAlgebra.Wedge
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of the actual graded layers of a free exponent-three group

For an arbitrary ordered set `I` and a basis `b` of an `𝔽₃`-vector space `V` indexed by `I`,
the maps `Free.sigmaOne`, `Free.sigmaTwo`, and `Free.sigmaThree` identify the actual central-series
quotients of `Free I` with the first three exterior powers of `V`. They compose the finite-support
coordinate equivalences from `Free.Graded` with the standard exterior-power basis equivalences.
No finiteness or countability hypothesis on `I` is used.

The generator formulas are those of Proposition 2.29. The direct sum and preservation of the
Lie bracket are separate constructions. The wedge identities below adapt earlier proofs
by Yawara Ishida.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`,
v4 Proposition 2.29 and Remark 2.30, lines 550–602.
-/

@[expose] public section

open scoped ExteriorAlgebra commutatorElement

namespace T3

open Module

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A two-fold wedge is the canonical two-variable exterior-power map.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, degree two.
-/
theorem wedgeVV_eq_ιMulti (u v : V) :
    wedgeVV R V u v = exteriorPower.ιMulti R 2 ![u, v] := by
  apply Subtype.ext
  simp [wedgeVV, gradedMul, oneEquiv_symm_coe,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]

/-- A wedge of a two-fold wedge with a vector is the canonical three-variable map.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, degree three.
-/
theorem wedgeQV_wedgeVV_eq_ιMulti (u v w : V) :
    wedgeQV R V (wedgeVV R V u v) w = exteriorPower.ιMulti R 3 ![u, v, w] := by
  apply Subtype.ext
  simp [wedgeQV, wedgeVV, gradedMul, oneEquiv_symm_coe,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, mul_assoc]

variable {I : Type*} [LinearOrder I]

/-- The exterior basis vector indexed by an increasing pair is the wedge in that order.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, degree two.
-/
theorem exteriorPower_two_basis (b : Basis I R V) (p : IncreasingPair I) :
    b.exteriorPower 2 (IncreasingPair.equivPowersetCard p) =
      wedgeVV R V (b p.first) (b p.second) := by
  rw [exteriorPower.basis_apply, wedgeVV_eq_ιMulti]
  change exteriorPower.ιMulti R 2
      (⇑b ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm (IncreasingPair.equivPowersetCard p))) = _
  rw [IncreasingPair.ofFinEmbEquiv_symm_equivPowersetCard]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The exterior basis vector indexed by an increasing triple is the wedge in that order.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, degree three.
-/
theorem exteriorPower_three_basis (b : Basis I R V) (t : IncreasingTriple I) :
    b.exteriorPower 3 (IncreasingTriple.equivPowersetCard t) =
      wedgeQV R V (wedgeVV R V (b t.first) (b t.second)) (b t.third) := by
  rw [exteriorPower.basis_apply, wedgeQV_wedgeVV_eq_ιMulti]
  change exteriorPower.ιMulti R 3
      (⇑b ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm (IncreasingTriple.equivPowersetCard t))) = _
  rw [IncreasingTriple.ofFinEmbEquiv_symm_equivPowersetCard]
  congr 1
  funext i
  fin_cases i <;> rfl

namespace Free

variable [Module (ZMod 3) V] (b : Basis I (ZMod 3) V)

/-- The first actual graded layer of the free exponent-three group identifies with `⋀¹V`
by sending each generator class to its specified basis vector.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 1.
-/
noncomputable def sigmaOne :
    AssociatedGraded.Layer (Free I) 1 ≃ₗ[ZMod 3] ⋀[ZMod 3]^1 V :=
  (layerOneEquiv.trans b.repr.symm).trans (exteriorPower.oneEquiv (ZMod 3) V).symm

/-- The second actual graded layer identifies with `⋀²V` by its increasing-pair basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 2.
-/
noncomputable def sigmaTwo :
    AssociatedGraded.Layer (Free I) 2 ≃ₗ[ZMod 3] ⋀[ZMod 3]^2 V :=
  (layerTwoEquiv.trans (Finsupp.domLCongr IncreasingPair.equivPowersetCard)).trans
    (b.exteriorPower 2).repr.symm

/-- The third actual graded layer identifies with `⋀³V` by its increasing-triple basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 3.
-/
noncomputable def sigmaThree :
    AssociatedGraded.Layer (Free I) 3 ≃ₗ[ZMod 3] ⋀[ZMod 3]^3 V :=
  (layerThreeEquiv.trans (Finsupp.domLCongr IncreasingTriple.equivPowersetCard)).trans
    (b.exteriorPower 3).repr.symm

/-- The first exterior identification realizes the generator coefficients in the chosen basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 1.
-/
theorem sigmaOne_apply (x : AssociatedGraded.Layer (Free I) 1) :
    sigmaOne b x = (exteriorPower.oneEquiv (ZMod 3) V).symm (b.repr.symm (layerOneEquiv x)) :=
  rfl

/-- The second exterior identification realizes the pair coefficients in the exterior basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 2.
-/
theorem sigmaTwo_apply (x : AssociatedGraded.Layer (Free I) 2) :
    sigmaTwo b x = (b.exteriorPower 2).repr.symm
      (Finsupp.domLCongr (R := ZMod 3) IncreasingPair.equivPowersetCard (layerTwoEquiv x)) := rfl

/-- The third exterior identification realizes the triple coefficients in the exterior basis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 3.
-/
theorem sigmaThree_apply (x : AssociatedGraded.Layer (Free I) 3) :
    sigmaThree b x = (b.exteriorPower 3).repr.symm
      (Finsupp.domLCongr (R := ZMod 3) IncreasingTriple.equivPowersetCard (layerThreeEquiv x)) :=
  rfl

/-- A generator class maps to the corresponding degree-one exterior vector.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 1.
-/
theorem sigmaOne_of (i : I) :
    sigmaOne b (AssociatedGraded.mk (Free I) 1 ⟨of i, Subgroup.mem_top _⟩) =
      (exteriorPower.oneEquiv (ZMod 3) V).symm (b i) := by
  rw [sigmaOne_apply, layerOneEquiv_of, Basis.repr_symm_single, one_smul]

/-- An increasing generator commutator maps to the wedge of the corresponding basis vectors.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 2.
-/
theorem sigmaTwo_commutator (p : IncreasingPair I) :
    sigmaTwo b (AssociatedGraded.mk (Free I) 2
      (derivedCommutator (of p.first) (of p.second))) =
      wedgeVV (ZMod 3) V (b p.first) (b p.second) := by
  rw [sigmaTwo_apply, layerTwoEquiv_commutator, Finsupp.domLCongr_single,
    Basis.repr_symm_single, one_smul, exteriorPower_two_basis]

/-- An increasing triple commutator maps to the ordered three-fold wedge of basis vectors.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v4.tex, `proposition:gr(F) is Grassmann algebra`, item 3.
-/
theorem sigmaThree_tripleCommutator (t : IncreasingTriple I) :
    sigmaThree b (AssociatedGraded.mk (Free I) 3
      ⟨⁅⁅of t.first, of t.second⁆, of t.third⁆,
        commutator_mem_gammaThree
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _⟩) =
      wedgeQV (ZMod 3) V (wedgeVV (ZMod 3) V (b t.first) (b t.second)) (b t.third) := by
  rw [sigmaThree_apply, layerThreeEquiv_tripleCommutator, Finsupp.domLCongr_single,
    Basis.repr_symm_single, one_smul, exteriorPower_three_basis]

end Free

end T3
