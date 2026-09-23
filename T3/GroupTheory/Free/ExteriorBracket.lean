/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Exterior
public import T3.GroupTheory.AssociatedGraded.Bracket

/-!
# The free-group exterior identifications preserve the bracket

The maps `Free.sigmaOne`, `Free.sigmaTwo`, and `Free.sigmaThree` preserve the two nonzero
positive-degree brackets. The proofs use the bases of the actual central-series quotients and
the ordered generator formulas. Alternation and cyclic invariance cover all other orders,
including repeated indices. Bilinearity then extends the formulas to arbitrary vectors, with
no restriction on the cardinality of the generating set.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`,
v8 Proposition 2.29 and Remark 2.30, lines 657–686.
-/

@[expose] public section

open scoped ExteriorAlgebra commutatorElement

namespace T3

open Module AssociatedGraded

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Exterior multiplication between two fixed powers, as a bilinear map.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, bracket comparison.
-/
def gradedMulLinear {i j : ℕ} : ⋀[R]^i V →ₗ[R] ⋀[R]^j V →ₗ[R] ⋀[R]^(i + j) V :=
  LinearMap.mk₂ R gradedMul gradedMul_add_left gradedMul_smul_left
    gradedMul_add_right gradedMul_smul_right

/-- The bilinear exterior product evaluates to the graded algebra product.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, bracket comparison.
-/
theorem gradedMulLinear_apply {i j : ℕ} (x : ⋀[R]^i V) (y : ⋀[R]^j V) :
    gradedMulLinear x y = gradedMul x y := rfl

namespace Free

variable {I : Type*} [LinearOrder I]

/-- The basis of the actual first layer consisting of free-generator classes.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, first displayed basis.
-/
noncomputable def layerOneBasis : Basis I (ZMod 3) (Layer (Free I) 1) :=
  Basis.ofRepr layerOneEquiv

/-- The first layer basis vector is represented by the corresponding free generator.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, first displayed basis.
-/
theorem layerOneBasis_apply (i : I) :
    layerOneBasis i = mk (Free I) 1 ⟨of i, Subgroup.mem_top _⟩ := by
  apply layerOneEquiv.injective
  change layerOneEquiv (layerOneEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply, layerOneEquiv_of]

/-- The basis of the actual second layer consisting of increasing generator commutators.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, second displayed basis.
-/
noncomputable def layerTwoBasis : Basis (IncreasingPair I) (ZMod 3) (Layer (Free I) 2) :=
  Basis.ofRepr layerTwoEquiv

/-- The second layer basis vector is represented by its increasing generator commutator.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, second displayed basis.
-/
theorem layerTwoBasis_apply (p : IncreasingPair I) :
    layerTwoBasis p = mk (Free I) 2 (derivedCommutator (of p.first) (of p.second)) := by
  apply layerTwoEquiv.injective
  change layerTwoEquiv (layerTwoEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply, layerTwoEquiv_commutator]

/-- The second layer basis is the bracket of the corresponding first layer basis vectors.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, bracket comparison.
-/
theorem layerTwoBasis_eq_bracket (p : IncreasingPair I) :
    layerTwoBasis p = bracketLayer (by decide) (by decide)
      (layerOneBasis p.first) (layerOneBasis p.second) := by
  rw [layerTwoBasis_apply, layerOneBasis_apply, layerOneBasis_apply, bracketLayer_mk]
  rfl

variable [Module (ZMod 3) V] (b : Basis I (ZMod 3) V)

private theorem sigmaTwo_bracketLayer_basis_of_lt {i j : I} (hij : i < j) :
    sigmaTwo b (bracketLayer (by decide) (by decide) (layerOneBasis i) (layerOneBasis j)) =
      gradedMul (sigmaOne b (layerOneBasis i)) (sigmaOne b (layerOneBasis j)) := by
  rw [layerOneBasis_apply, layerOneBasis_apply, sigmaOne_of, sigmaOne_of, bracketLayer_mk]
  exact sigmaTwo_commutator b ⟨i, j, hij⟩

private theorem sigmaTwo_bracketLayer_basis (i j : I) :
    sigmaTwo b (bracketLayer (by decide) (by decide) (layerOneBasis i) (layerOneBasis j)) =
      gradedMul (sigmaOne b (layerOneBasis i)) (sigmaOne b (layerOneBasis j)) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact sigmaTwo_bracketLayer_basis_of_lt b hij
  · rw [bracketLayer_one_self, map_zero, gradedMul_one_self]
  · rw [bracketLayer_one_swap, map_neg, sigmaTwo_bracketLayer_basis_of_lt b hji]
    exact (gradedMul_one_swap _ _).symm

/-- The degree-two identification carries the bracket of first-layer vectors to their wedge.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, first bracket identity.
-/
theorem sigmaTwo_bracketLayer (x y : Layer (Free I) 1) :
    sigmaTwo b (bracketLayer (by decide) (by decide) x y) =
      gradedMul (sigmaOne b x) (sigmaOne b y) := by
  let left := (bracketLayer (G := Free I) (i := 1) (j := 1) (by decide) (by decide)).compr₂
    (sigmaTwo b).toLinearMap
  let right := gradedMulLinear.compl₁₂ (sigmaOne b).toLinearMap (sigmaOne b).toLinearMap
  have h : left = right := by
    apply (layerOneBasis (I := I)).ext
    intro i
    apply (layerOneBasis (I := I)).ext
    intro j
    exact sigmaTwo_bracketLayer_basis b i j
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

private theorem sigmaThree_triple_basis_of_lt {i j k : I} (hij : i < j) (hjk : j < k) :
    sigmaThree b (bracketLayer (by decide) (by decide)
      (bracketLayer (by decide) (by decide) (layerOneBasis i) (layerOneBasis j))
      (layerOneBasis k)) =
      gradedMul (gradedMul (sigmaOne b (layerOneBasis i)) (sigmaOne b (layerOneBasis j)))
        (sigmaOne b (layerOneBasis k)) := by
  rw [layerOneBasis_apply, layerOneBasis_apply, layerOneBasis_apply,
    sigmaOne_of, sigmaOne_of, sigmaOne_of, bracketLayer_mk, bracketLayer_mk]
  exact sigmaThree_tripleCommutator b ⟨i, j, k, hij, hjk⟩

omit [LinearOrder I] in
private theorem triple_swap_last (x y z : Layer (Free I) 1) :
    bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x y) z =
      -bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x z) y := by
  rw [bracketLayer_triple_cyclic x y z, bracketLayer_one_swap y z, map_neg,
    LinearMap.neg_apply, ← bracketLayer_triple_cyclic x z y]

private theorem exterior_triple_swap_last (x y z : ⋀[ZMod 3]^1 V) :
    gradedMul (gradedMul x y) z = -gradedMul (gradedMul x z) y := by
  rw [gradedMul_one_cyclic x y z, gradedMul_one_swap y z]
  change gradedMulLinear (-gradedMul z y) x = _
  rw [map_neg, LinearMap.neg_apply]
  change -gradedMul (gradedMul z y) x = _
  rw [← gradedMul_one_cyclic x z y]

private theorem sigmaThree_triple_basis {i j : I} (hij : i < j) (k : I) :
    sigmaThree b (bracketLayer (by decide) (by decide)
      (bracketLayer (by decide) (by decide) (layerOneBasis i) (layerOneBasis j))
      (layerOneBasis k)) =
      gradedMul (gradedMul (sigmaOne b (layerOneBasis i)) (sigmaOne b (layerOneBasis j)))
        (sigmaOne b (layerOneBasis k)) := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact sigmaThree_triple_basis_of_lt b hij hjk
  · rw [bracketLayer_triple_self, map_zero, gradedMul_one_repeat]
  · rcases lt_trichotomy i k with hik | rfl | hki
    · rw [triple_swap_last, map_neg, sigmaThree_triple_basis_of_lt b hik hkj]
      exact (exterior_triple_swap_last _ _ _).symm
    · rw [bracketLayer_triple_cyclic, bracketLayer_triple_self, map_zero,
        gradedMul_one_cyclic, gradedMul_one_repeat]
    · rw [← bracketLayer_triple_cyclic (layerOneBasis k) (layerOneBasis i) (layerOneBasis j),
        ← gradedMul_one_cyclic (sigmaOne b (layerOneBasis k)) (sigmaOne b (layerOneBasis i))
          (sigmaOne b (layerOneBasis j))]
      exact sigmaThree_triple_basis_of_lt b hki hij

private theorem sigmaThree_bracketLayer_basis (p : IncreasingPair I) (k : I) :
    sigmaThree b (bracketLayer (by decide) (by decide) (layerTwoBasis p) (layerOneBasis k)) =
      gradedMul (sigmaTwo b (layerTwoBasis p)) (sigmaOne b (layerOneBasis k)) := by
  rw [layerTwoBasis_eq_bracket, sigmaTwo_bracketLayer]
  exact sigmaThree_triple_basis b p.first_lt_second k

/-- The degree-three identification carries the bracket of a second-layer and a first-layer
vector to their exterior product.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v8.tex, `proposition:gr(F) is Grassmann algebra`, second bracket identity.
-/
theorem sigmaThree_bracketLayer (q : Layer (Free I) 2) (v : Layer (Free I) 1) :
    sigmaThree b (bracketLayer (by decide) (by decide) q v) =
      gradedMul (sigmaTwo b q) (sigmaOne b v) := by
  let left := (bracketLayer (G := Free I) (i := 2) (j := 1) (by decide) (by decide)).compr₂
    (sigmaThree b).toLinearMap
  let right := gradedMulLinear.compl₁₂ (sigmaTwo b).toLinearMap (sigmaOne b).toLinearMap
  have h : left = right := by
    apply (layerTwoBasis (I := I)).ext
    intro p
    apply (layerOneBasis (I := I)).ext
    intro k
    exact sigmaThree_bracketLayer_basis b p k
  exact LinearMap.congr_fun (LinearMap.congr_fun h q) v

end Free

end T3
