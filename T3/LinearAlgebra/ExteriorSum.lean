/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Exterior blocks of a basis on a disjoint union

An exterior basis on `I ⊕ J` is partitioned by the number of indices from `I`.
The resulting projections give a direct decomposition of each exterior power. These are the
basis blocks used in the paper's exterior decomposition before taking the relation quotient.
Identification of the mixed blocks with tensor products is a separate step.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, proof, lines 964–991.
-/

@[expose] public section

open scoped BigOperators ExteriorAlgebra DirectSum
open Module

namespace T3.ExteriorSum

variable {R M I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Count the left indices in an exterior-basis index on a disjoint union.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
def leftCount {n : ℕ} (s : Set.powersetCard (I ⊕ J) n) : ℕ :=
  ((s : Finset (I ⊕ J)).filter (fun z => z.isLeft = true)).card

/-- The coordinate projection of a finitely supported family onto a predicate.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
def filterLinearMap {ι : Type*} (p : ι → Prop) [DecidablePred p] :
    (ι →₀ R) →ₗ[R] (ι →₀ R) where
  toFun f := f.filter p
  map_add' _ _ := Finsupp.filter_add
  map_smul' c f := by
    ext i
    simp only [Finsupp.filter_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs <;> simp

/-- An exterior-basis index has at most its total degree many left indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem leftCount_le {n : ℕ} (s : Set.powersetCard (I ⊕ J) n) : leftCount s ≤ n :=
  (Finset.card_filter_le _ _).trans_eq s.property

variable [LinearOrder (I ⊕ J)] (b : Basis (I ⊕ J) R M)

/-- Keep exactly the exterior-basis coordinates containing `k` left indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
noncomputable def projection (n k : ℕ) : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M) :=
  (b.exteriorPower n).repr.symm.toLinearMap.comp <|
    (filterLinearMap (R := R) (fun s : Set.powersetCard (I ⊕ J) n => leftCount s = k)).comp
      (b.exteriorPower n).repr.toLinearMap

/-- The block projection filters the exterior coordinates by the number of left indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
@[simp]
theorem projection_repr (n k : ℕ) (x : ⋀[R]^n M) (s : Set.powersetCard (I ⊕ J) n) :
    (b.exteriorPower n).repr (projection b n k x) s =
      if leftCount s = k then (b.exteriorPower n).repr x s else 0 := by
  change (b.exteriorPower n).repr ((b.exteriorPower n).repr.symm
    ((filterLinearMap (R := R) (fun t : Set.powersetCard (I ⊕ J) n => leftCount t = k))
      ((b.exteriorPower n).repr x))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The finitely many possible block projections sum to the original exterior vector.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem sum_projection (n : ℕ) (x : ⋀[R]^n M) :
    (∑ k ∈ Finset.range (n + 1), projection b n k x) = x := by
  apply (b.exteriorPower n).repr.injective
  rw [map_sum]
  ext s
  rw [Finsupp.finsetSum_apply]
  change (∑ k ∈ Finset.range (n + 1), (b.exteriorPower n).repr (projection b n k x) s) =
    (b.exteriorPower n).repr x s
  simp_rw [projection_repr]
  simp [eq_comm, leftCount_le s]

/-- Each block projection is idempotent.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
@[simp]
theorem projection_idem (n k : ℕ) (x : ⋀[R]^n M) :
    projection b n k (projection b n k x) = projection b n k x := by
  apply (b.exteriorPower n).repr.injective
  ext s
  simp only [projection_repr]
  split_ifs <;> simp

/-- Distinct blocks have orthogonal projections.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem projection_orthogonal (n k l : ℕ) (hkl : k ≠ l) (x : ⋀[R]^n M) :
    projection b n k (projection b n l x) = 0 := by
  apply (b.exteriorPower n).repr.injective
  ext s
  simp only [projection_repr, map_zero, Finsupp.zero_apply]
  by_cases hsk : leftCount s = k
  · rw [ite_eq_left hsk, ite_eq_right]
    exact fun hsl => hkl (hsk.symm.trans hsl)
  · rw [ite_eq_right hsk]

/-- The subspace with exactly `k` left indices in degree `n`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
noncomputable def block (n : ℕ) (k : Fin (n + 1)) : Submodule R (⋀[R]^n M) :=
  LinearMap.range (projection b n k)

/-- The exterior projection with its codomain restricted to the corresponding block.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior blocks.
-/
noncomputable def blockProjection (n : ℕ) (k : Fin (n + 1)) :
    (⋀[R]^n M) →ₗ[R] block b n k :=
  (projection b n k).codRestrict (block b n k) fun x => ⟨x, rfl⟩

/-- Collect the block projections in the external direct sum of their ranges.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior decomposition.
-/
noncomputable def decompositionMap (n : ℕ) :
    (⋀[R]^n M) →ₗ[R] ⨁ k : Fin (n + 1), block b n k :=
  ∑ k, (DirectSum.lof R _ (fun k => block b n k) k).comp (blockProjection b n k)

/-- The component of the decomposition map is the corresponding exterior projection.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem decompositionMap_apply (n : ℕ) (x : ⋀[R]^n M) (k : Fin (n + 1)) :
    ((decompositionMap b n x) k : ⋀[R]^n M) = projection b n k x := by
  change (block b n k).subtype (DirectSum.component R (Fin (n + 1))
    (fun k => block b n k) k (decompositionMap b n x)) = _
  simp only [decompositionMap, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  rw [Finset.sum_eq_single k]
  · change ((DirectSum.lof R _ (fun k => block b n k) k
      (blockProjection b n k x)) k : ⋀[R]^n M) = _
    rw [DirectSum.lof_apply]
    rfl
  · intro i _ hik
    change ((DirectSum.lof R _ (fun k => block b n k) i
      (blockProjection b n i x)) k : ⋀[R]^n M) = 0
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne i k _ (Ne.symm hik)]
    rfl
  · simp

/-- The exterior blocks form an internal direct-sum decomposition in every degree.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior decomposition.
-/
noncomputable instance blockDecomposition (n : ℕ) : DirectSum.Decomposition (block b n) := by
  apply DirectSum.Decomposition.ofLinearMap _ (decompositionMap b n)
  · apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (block b n) (decompositionMap b n x) = x
    simp only [decompositionMap, LinearMap.sum_apply, LinearMap.comp_apply,
      map_sum, DirectSum.coeLinearMap_lof]
    change (∑ k : Fin (n + 1), projection b n k x) = x
    exact (Fin.sum_univ_eq_sum_range (fun k => projection b n k x) (n + 1)).trans
      (sum_projection b n x)
  · apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro x
    change decompositionMap b n (DirectSum.coeLinearMap (block b n)
      (DirectSum.lof R _ (fun k => block b n k) k x)) =
      DirectSum.lof R _ (fun k => block b n k) k x
    rw [DirectSum.coeLinearMap_lof]
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    rw [decompositionMap_apply]
    obtain ⟨y, hy⟩ := x.property
    by_cases h : i = k
    · subst i
      rw [DirectSum.lof_apply, ← hy, projection_idem]
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne k i _ h]
      change projection b n i (x : ⋀[R]^n M) = 0
      rw [← hy]
      exact projection_orthogonal b n i k (fun hval => h (Fin.ext hval)) y

/-- The standard decomposition exposes precisely the count-based exterior projections.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v7.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem coe_decompose (n : ℕ) (x : ⋀[R]^n M) (k : Fin (n + 1)) :
    (DirectSum.decompose (block b n) x k : ⋀[R]^n M) = projection b n k x :=
  decompositionMap_apply b n x k

end T3.ExteriorSum
