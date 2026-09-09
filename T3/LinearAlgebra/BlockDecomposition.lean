/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Block-homogeneous submodules and their quotients

For a decomposition `V = ⨁ i, B i`, block homogeneity means that every component of an element
of `W` remains in `W`. This is equivalent to the paper's equality `W = ⨆ i, W ⊓ B i`;
independence of the blocks is inherited from the given decomposition.

The canonical quotient equivalence sends the class of `v` to the classes of its components.
It is constructed from `DirectSum.decomposeLinearEquiv` and the direct sum of the component
quotient maps. Its kernel is exactly `W` and it is surjective. No finiteness condition on the
index or module is needed. The ring generality below includes the vector spaces in the paper.

Paper-ID: linear_algebra.block_homogeneous; linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Definition 2.10 and Proposition 2.11.
-/

@[expose] public section

open scoped DirectSum

namespace T3

variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [DecidableEq ι]
  (B : ι → Submodule R V) [DirectSum.Decomposition B] (W : Submodule R V)

/-- A block-homogeneous submodule is closed under the components of the chosen decomposition.

This is mathlib's homogeneous-substructure predicate. The equality with the direct sum of the
intersections is recorded in `isBlockHomogeneous_iff_iSup_eq`.

Paper-ID: linear_algebra.block_homogeneous
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Definition 2.10. -/
abbrev IsBlockHomogeneous : Prop := DirectSum.SetLike.IsHomogeneous B W

/-- Block homogeneity is equivalent to the paper's equality with the sum of block intersections.

Since the ambient blocks form a direct sum, their intersections with `W` are independent.

Paper-ID: linear_algebra.block_homogeneous
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Definition 2.10. -/
theorem isBlockHomogeneous_iff_iSup_eq :
    IsBlockHomogeneous B W ↔ W = ⨆ i, W ⊓ B i := by
  classical
  constructor
  · intro hW
    apply le_antisymm
    · intro v hv
      rw [← DirectSum.sum_support_decompose B v]
      apply Submodule.sum_mem
      intro i _
      exact (le_iSup (fun i => W ⊓ B i) i) ⟨hW i hv, (DirectSum.decompose B v i).property⟩
    · exact iSup_le fun _ => inf_le_left
  · intro hW i v hv
    rw [hW] at hv
    refine Submodule.iSup_induction (fun j => W ⊓ B j)
      (motive := fun x => (DirectSum.decompose B x i : V) ∈ W) hv ?_ ?_ ?_
    · intro j v hv
      by_cases hji : j = i
      · subst j
        rw [DirectSum.decompose_of_mem_same B hv.2]
        exact hv.1
      · rw [DirectSum.decompose_of_mem_ne B hv.2 hji]
        exact W.zero_mem
    · simp
    · intro x y hx hy
      simpa using W.add_mem hx hy

/-- The block intersections are independent, so the sum in the definition is an internal sum.

Paper-ID: linear_algebra.block_homogeneous
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Definition 2.10. -/
theorem blockIntersections_independent : iSupIndep (fun i => W ⊓ B i) :=
  (DirectSum.Decomposition.isInternal B).submodule_iSupIndep.mono fun _ => inf_le_right

namespace BlockDecomposition

/-- The intersection with `W`, regarded as a submodule of the block itself.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
abbrev intersection (i : ι) : Submodule R (B i) := W.comap (B i).subtype

/-- The quotient `B i / (W ∩ B i)` appearing in the paper.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
abbrev QuotientBlock (i : ι) := (B i) ⧸ intersection B W i

/-- The quotient of a block is canonically its image in the ambient quotient.

This individual-block isomorphism does not require block homogeneity of `W`.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
noncomputable def blockImageEquiv (i : ι) :
    QuotientBlock B W i ≃ₗ[R] (B i).map W.mkQ :=
  (Submodule.quotEquivOfEq (intersection B W i) (W.mkQ.comp (B i).subtype).ker
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
      ((W.mkQ.comp (B i).subtype).quotKerEquivRange.trans
        (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype])))

omit [DecidableEq ι] [DirectSum.Decomposition B] in
/-- The component quotient isomorphism sends a block representative to its ambient quotient class.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem blockImageEquiv_mk (i : ι) (v : B i) :
    (blockImageEquiv B W i (Submodule.Quotient.mk v) : V ⧸ W) =
      Submodule.Quotient.mk (v : V) := by
  simp [blockImageEquiv]

/-- Decompose a vector and take the class of each component modulo its block intersection.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
def toQuotientSum : V →ₗ[R] ⨁ i, QuotientBlock B W i :=
  (DirectSum.lmap fun i => (intersection B W i).mkQ).comp
    (DirectSum.decomposeLinearEquiv B).toLinearMap

/-- The `i`-th component is the quotient class of the `i`-th component of the original vector.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem toQuotientSum_apply (v : V) (i : ι) :
    toQuotientSum B W v i = Submodule.Quotient.mk (DirectSum.decompose B v i) := rfl

/-- A vector supported in a single block maps to the corresponding single quotient component.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem toQuotientSum_coe (i : ι) (v : B i) :
    toQuotientSum B W v =
      DirectSum.lof R ι (QuotientBlock B W) i (Submodule.Quotient.mk v) := by
  simp [toQuotientSum]

/-- All finitely supported families of quotient components have representatives in `V`.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
theorem toQuotientSum_surjective : Function.Surjective (toQuotientSum B W) :=
  ((DirectSum.lmap_surjective _).mpr fun i => (intersection B W i).mkQ_surjective).comp
    (DirectSum.decomposeLinearEquiv B).surjective

/-- For a block-homogeneous submodule, the component quotient map has precisely that kernel.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
theorem toQuotientSum_ker (hW : IsBlockHomogeneous B W) :
    (toQuotientSum B W).ker = W := by
  ext v
  rw [LinearMap.mem_ker, DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff B W hW]
  constructor
  · intro hv i
    have hi := DFunLike.congr_fun hv i
    exact (Submodule.Quotient.mk_eq_zero (intersection B W i)).mp hi
  · intro hv
    ext i
    exact (Submodule.Quotient.mk_eq_zero (intersection B W i)).mpr (hv i)

/-- The standard isomorphism from the quotient of a block decomposition to the sum of quotients.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
noncomputable def quotientEquiv (hW : IsBlockHomogeneous B W) :
    (V ⧸ W) ≃ₗ[R] ⨁ i, QuotientBlock B W i :=
  LinearEquiv.ofBijective
    (W.liftQ (τ₁₂ := RingHom.id R) (M₂ := ⨁ i, QuotientBlock B W i)
      (toQuotientSum B W) (by rw [toQuotientSum_ker B W hW])) (by
    constructor
    · exact LinearMap.ker_eq_bot.mp
        (W.ker_liftQ_eq_bot (τ₁₂ := RingHom.id R) (M₂ := ⨁ i, QuotientBlock B W i)
          (toQuotientSum B W) _ (toQuotientSum_ker B W hW).le)
    · intro x
      obtain ⟨v, rfl⟩ := toQuotientSum_surjective B W x
      exact ⟨Submodule.Quotient.mk v, rfl⟩)

/-- On a representative, the quotient equivalence is the direct sum of its component classes.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem quotientEquiv_mk (hW : IsBlockHomogeneous B W) (v : V) :
    quotientEquiv B W hW (Submodule.Quotient.mk v) = toQuotientSum B W v := rfl

/-- The coordinate formula printed in the paper for the canonical quotient isomorphism.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem quotientEquiv_mk_apply (hW : IsBlockHomogeneous B W) (v : V) (i : ι) :
    quotientEquiv B W hW (Submodule.Quotient.mk v) i =
      Submodule.Quotient.mk (DirectSum.decompose B v i) := by
  rw [quotientEquiv_mk, toQuotientSum_apply]

/-- A single block class has its canonical position under the quotient isomorphism.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
theorem quotientEquiv_mk_coe (hW : IsBlockHomogeneous B W) (i : ι) (v : B i) :
    quotientEquiv B W hW (Submodule.Quotient.mk (v : V)) =
      DirectSum.lof R ι (QuotientBlock B W) i (Submodule.Quotient.mk v) := by
  rw [quotientEquiv_mk, toQuotientSum_coe]

/-- The inverse equivalence sends a single quotient component to its class in the ambient quotient.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem quotientEquiv_symm_lof_mk (hW : IsBlockHomogeneous B W) (i : ι) (v : B i) :
    (quotientEquiv B W hW).symm
      (DirectSum.lof R ι (QuotientBlock B W) i (Submodule.Quotient.mk v)) =
      Submodule.Quotient.mk (v : V) := by
  rw [← quotientEquiv_mk_coe B W hW, LinearEquiv.symm_apply_apply]

/-- Under the full quotient decomposition, the image of an individual block is its own summand.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
@[simp]
theorem quotientEquiv_blockImageEquiv (hW : IsBlockHomogeneous B W) (i : ι)
    (v : QuotientBlock B W i) :
    quotientEquiv B W hW (blockImageEquiv B W i v : V ⧸ W) =
      DirectSum.lof R ι (QuotientBlock B W) i v := by
  obtain ⟨v, rfl⟩ := (intersection B W i).mkQ_surjective v
  simp

/-- The ambient image of a block is exactly the range of its canonical quotient-sum inclusion.

Paper-ID: linear_algebra.block_quotient
TeX: T3_modelcompanion_v4.tex, unlabelled v4 Proposition 2.11. -/
theorem map_blockImage (hW : IsBlockHomogeneous B W) (i : ι) :
    ((B i).map W.mkQ).map (quotientEquiv B W hW).toLinearMap =
      (DirectSum.lof R ι (QuotientBlock B W) i).range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨Submodule.Quotient.mk (⟨v, hv⟩ : B i),
      (quotientEquiv_mk_coe B W hW i ⟨v, hv⟩).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨blockImageEquiv B W i v, (blockImageEquiv B W i v).property,
      quotientEquiv_blockImageEquiv B W hW i v⟩

end BlockDecomposition

end T3
