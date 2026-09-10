/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.LinearAlgebra.ExteriorSum
public import T3.LinearAlgebra.Wedge
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Sum.Order
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor components of exterior powers of a direct sum

The exterior basis on the disjoint union of two bases splits into pairs of exterior indices.
Combining this split with the standard tensor-product bases identifies the actual exterior
power with the direct sum of the tensor products of complementary exterior powers. The bases
may have arbitrary cardinality. Left indices precede right indices in the combined order.
The inverse is the sum of the canonical exterior multiplication maps. Their ranges are exactly
the count-based blocks from `ExteriorSum`, and no basis is used to define these inverse maps.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, proof, lines 883–887.
-/

@[expose] public section

namespace Set.powersetCard

variable {I J : Type*}

/-- Split an `n`-element subset of a disjoint union by its number of left indices.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
def sumEquiv (n : ℕ) :
    powersetCard (I ⊕ J) n ≃
      Σ k : Fin (n + 1), powersetCard I k × powersetCard J (n - k) where
  toFun s :=
    ⟨⟨s.val.toLeft.card, Nat.lt_succ_of_le (Finset.card_toLeft_le.trans_eq s.property)⟩,
      ⟨⟨s.val.toLeft, rfl⟩, ⟨s.val.toRight, by
        change s.val.toRight.card = n - s.val.toLeft.card
        have h := Finset.card_toLeft_add_card_toRight (u := s.val)
        rw [s.property] at h
        omega⟩⟩⟩
  invFun s := ⟨s.2.1.val.disjSum s.2.2.val, by
    change (s.2.1.val.disjSum s.2.2.val).card = n
    rw [Finset.card_disjSum, s.2.1.property, s.2.2.property]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ s.1.isLt)⟩
  left_inv s := Subtype.ext Finset.toLeft_disjSum_toRight
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
    change s.card = k at hs
    subst k
    simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
    congr 1
    · exact Fin.ext (congrArg Finset.card Finset.toLeft_disjSum)
    · congr 1 <;> first
      | solve | simp only [Finset.toLeft_disjSum]
      | exact (Subtype.heq_iff_coe_eq (by simp [Finset.toLeft_disjSum])).mpr rfl

/-- The left degree in the split index is the cardinality of the left subset.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
theorem sumEquiv_fst (n : ℕ) (s : powersetCard (I ⊕ J) n) :
    ((sumEquiv n s).1 : ℕ) = s.val.toLeft.card := rfl

/-- The inverse index map forms the disjoint union of the two subsets.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
theorem sumEquiv_symm_val (n : ℕ) (k : Fin (n + 1))
    (s : powersetCard I k) (t : powersetCard J (n - k)) :
    ((sumEquiv n).symm ⟨k, s, t⟩).val = s.val.disjSum t.val := rfl

end Set.powersetCard

open scoped ExteriorAlgebra DirectSum TensorProduct
open Module

namespace T3.ExteriorTensor

variable {R V W I J : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [LinearOrder I] [LinearOrder J]

/-- Order the combined basis with every left index before every right index.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
abbrev sumLinearOrder : LinearOrder (I ⊕ J) := Sum.Lex.linearOrder

attribute [local instance] sumLinearOrder

private abbrev sumLE : LE (I ⊕ J) := (sumLinearOrder (I := I) (J := J)).toLE
private abbrev sumLT : LT (I ⊕ J) := (sumLinearOrder (I := I) (J := J)).toLT
private abbrev sumPreorder : Preorder (I ⊕ J) :=
  (sumLinearOrder (I := I) (J := J)).toPartialOrder.toPreorder

attribute [local instance] sumLE sumLT sumPreorder

private def appendOrderEmbedding {p q : ℕ} (s : Fin p ↪o I) (t : Fin q ↪o J) :
    Fin (p + q) ↪o (I ⊕ J) :=
  OrderEmbedding.ofStrictMono (Fin.append (Sum.inl ∘ s) (Sum.inr ∘ t)) (by
    intro i j hij
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · simp only [finSumFinEquiv_apply_left, Fin.append_left, Function.comp_apply]
      exact Sum.Lex.inl_lt_inl_iff.mpr (s.strictMono hij)
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.append_left, Fin.append_right, Function.comp_apply]
      exact Sum.Lex.inl_lt_inr _ _
    · have h := j.isLt
      change p + i.val < j.val at hij
      omega
    · simp only [finSumFinEquiv_apply_right, Fin.append_right, Function.comp_apply]
      exact Sum.Lex.inr_lt_inr_iff.mpr (t.strictMono (by simpa using hij)))

private theorem ofFinEmbEquiv_appendOrderEmbedding {p q : ℕ}
    (s : Set.powersetCard I p) (t : Set.powersetCard J q) :
    (Set.powersetCard.ofFinEmbEquiv
      (appendOrderEmbedding (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t))).val = s.val.disjSum t.val := by
  ext z
  rw [Set.powersetCard.mem_coe_iff, Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  cases z with
  | inl i =>
    rw [Finset.inl_mem_disjSum]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
      · simp only [appendOrderEmbedding, OrderEmbedding.coe_ofStrictMono,
          finSumFinEquiv_apply_left, Fin.append_left, Function.comp_apply,
          Sum.inl.injEq] at hj
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mp ⟨j, hj⟩
      · simp [appendOrderEmbedding] at hj
    · intro hi
      obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
      exact ⟨Fin.castAdd q j, by simpa [appendOrderEmbedding] using hj⟩
  | inr i =>
    rw [Finset.inr_mem_disjSum]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
      · simp [appendOrderEmbedding] at hj
      · simp only [appendOrderEmbedding, OrderEmbedding.coe_ofStrictMono,
          finSumFinEquiv_apply_right, Fin.append_right, Function.comp_apply,
          Sum.inr.injEq] at hj
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mp ⟨j, hj⟩
    · intro hi
      obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hi
      exact ⟨Fin.natAdd p j, by simpa [appendOrderEmbedding] using hj⟩

/-- The degree-`n` exterior tensor block with left degree `k`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 883–887.
-/
abbrev TensorBlock (R V W : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (n : ℕ) (k : Fin (n + 1)) :=
  (⋀[R]^k.val V) ⊗[R] (⋀[R]^(n - k.val) W)

variable (R V W) in
/-- Include the two exterior factors in the direct sum and multiply them, left before right.
This map is defined without choosing bases.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
noncomputable def wedgeMap (n : ℕ) (k : Fin (n + 1)) :
    TensorBlock R V W n k →ₗ[R] ⋀[R]^n (V × W) := by
  let f := exteriorPower.map k (LinearMap.inl R V W)
  let g := exteriorPower.map (n - k) (LinearMap.inr R V W)
  refine TensorProduct.lift (LinearMap.mk₂ R
    (fun (x : ⋀[R]^k.val V) (y : ⋀[R]^(n - k.val) W) =>
      (⟨(f x : ExteriorAlgebra R (V × W)) * g y, ?_⟩ : ⋀[R]^n (V × W)))
    (fun x x' y => ?_) (fun r x y => ?_) (fun x y y' => ?_) (fun r x y => ?_))
  · simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)] using
      (SetLike.mul_mem_graded (f x).property (g y).property)
  · exact Subtype.ext (by simp [add_mul])
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp [mul_add])
  · exact Subtype.ext (by simp)

/-- The canonical tensor map is exterior multiplication on pure tensors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem wedgeMap_tmul_coe (n : ℕ) (k : Fin (n + 1))
    (x : ⋀[R]^k.val V) (y : ⋀[R]^(n - k.val) W) :
    (wedgeMap R V W n k (x ⊗ₜ[R] y) : ExteriorAlgebra R (V × W)) =
      (exteriorPower.map k (LinearMap.inl R V W) x : ExteriorAlgebra R (V × W)) *
      (exteriorPower.map (n - k) (LinearMap.inr R V W) y : ExteriorAlgebra R (V × W)) :=
  rfl

variable (b : Basis I R V) (c : Basis J R W)

/-- The exterior basis on a disjoint union is the product of the images of its two exterior
basis factors. The left-first order gives the displayed product with positive sign.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, lines 883–887.
-/
theorem exteriorBasis_disjSum_coe {p q n : ℕ} (h : p + q = n)
    (s : Set.powersetCard I p) (t : Set.powersetCard J q) :
    ((b.prod c).exteriorPower n
      ⟨s.val.disjSum t.val, by rw [Set.powersetCard.mem_iff, Finset.card_disjSum,
        s.property, t.property, h]⟩ : ExteriorAlgebra R (V × W)) =
      (exteriorPower.map p (LinearMap.inl R V W) (b.exteriorPower p s) :
        ExteriorAlgebra R (V × W)) *
      (exteriorPower.map q (LinearMap.inr R V W) (c.exteriorPower q t) :
        ExteriorAlgebra R (V × W)) := by
  subst n
  have hs : (⟨s.val.disjSum t.val, by simp⟩ : Set.powersetCard (I ⊕ J) (p + q)) =
      Set.powersetCard.ofFinEmbEquiv
        (appendOrderEmbedding (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)) :=
    Subtype.ext (ofFinEmbEquiv_appendOrderEmbedding s t).symm
  rw [hs]
  simp only [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family,
    Equiv.symm_apply_apply, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [appendOrderEmbedding, Basis.prod_apply]

/-- The tensor-product bases assembled into a basis of the external direct sum.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
noncomputable def tensorBasis (n : ℕ) :
    Basis (Σ k : Fin (n + 1), Set.powersetCard I k × Set.powersetCard J (n - k)) R
      (⨁ k : Fin (n + 1), TensorBlock R V W n k) :=
  DFinsupp.basis fun k => (b.exteriorPower k).tensorProduct (c.exteriorPower (n - k))

/-- A tensor basis vector is included in its specified direct-sum component.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, supporting `proposition:gr of free product`, exterior blocks.
-/
theorem tensorBasis_apply (n : ℕ) (k : Fin (n + 1))
    (s : Set.powersetCard I k) (t : Set.powersetCard J (n - k)) :
    tensorBasis b c n ⟨k, s, t⟩ =
      DirectSum.lof R _ (TensorBlock R V W n) k
        (b.exteriorPower k s ⊗ₜ[R] c.exteriorPower (n - k) t) := by
  apply (tensorBasis b c n).repr.injective
  ext ⟨l, u, v⟩
  simp only [Basis.repr_self]
  change Finsupp.single
      (⟨k, s, t⟩ : Σ k : Fin (n + 1), Set.powersetCard I k × Set.powersetCard J (n - k))
      (1 : R) ⟨l, u, v⟩ =
    ((b.exteriorPower l).tensorProduct (c.exteriorPower (n - l))).repr
      ((DirectSum.lof R _ (TensorBlock R V W n) k
        (b.exteriorPower k s ⊗ₜ[R] c.exteriorPower (n - k) t)) l) (u, v)
  by_cases h : k = l
  · subst l
    rw [DirectSum.lof_apply, ← Basis.tensorProduct_apply, Basis.repr_self]
    simp only [Finsupp.single_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne k l _ (Ne.symm h), map_zero,
      Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (fun he => h (congrArg Sigma.fst he).symm)

/-- The exterior power of a direct sum is the direct sum of complementary exterior tensors.
This is an equivalence of the actual exterior-power and tensor-product modules, in arbitrary rank.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, proof, lines 883–887.
-/
noncomputable def tensorEquiv (n : ℕ) :
    (⋀[R]^n (V × W)) ≃ₗ[R] ⨁ k : Fin (n + 1), TensorBlock R V W n k :=
  ((b.prod c).exteriorPower n).equiv (tensorBasis b c n) (Set.powersetCard.sumEquiv n)

/-- The combined exterior basis vector maps to the tensor of its left and right basis vectors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_basis (n : ℕ) (k : Fin (n + 1))
    (s : Set.powersetCard I k) (t : Set.powersetCard J (n - k)) :
    tensorEquiv b c n ((b.prod c).exteriorPower n
      ((Set.powersetCard.sumEquiv n).symm ⟨k, s, t⟩)) =
      DirectSum.lof R _ (TensorBlock R V W n) k
        (b.exteriorPower k s ⊗ₜ[R] c.exteriorPower (n - k) t) := by
  rw [tensorEquiv, Basis.equiv_apply, Equiv.apply_symm_apply, tensorBasis_apply]

/-- The inverse tensor decomposition sends a tensor of exterior basis vectors to their union.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_symm_basis (n : ℕ) (k : Fin (n + 1))
    (s : Set.powersetCard I k) (t : Set.powersetCard J (n - k)) :
    (tensorEquiv b c n).symm
      (DirectSum.lof R _ (TensorBlock R V W n) k
        (b.exteriorPower k s ⊗ₜ[R] c.exteriorPower (n - k) t)) =
      (b.prod c).exteriorPower n ((Set.powersetCard.sumEquiv n).symm ⟨k, s, t⟩) :=
  (tensorEquiv b c n).symm_apply_eq.mpr (tensorEquiv_basis b c n k s t).symm

/-- On each tensor summand, the inverse decomposition is the canonical exterior product map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_symm_comp_lof (n : ℕ) (k : Fin (n + 1)) :
    (tensorEquiv b c n).symm.toLinearMap.comp
      (DirectSum.lof R _ (TensorBlock R V W n) k) = wedgeMap R V W n k := by
  apply ((b.exteriorPower k).tensorProduct (c.exteriorPower (n - k))).ext
  rintro ⟨s, t⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.tensorProduct_apply]
  rw [tensorEquiv_symm_basis]
  apply Subtype.ext
  exact exteriorBasis_disjSum_coe b c (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)) s t

/-- The inverse decomposition on arbitrary exterior pure tensors is their ordered product.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_symm_tmul_coe (n : ℕ) (k : Fin (n + 1))
    (x : ⋀[R]^k.val V) (y : ⋀[R]^(n - k.val) W) :
    ((tensorEquiv b c n).symm
      (DirectSum.lof R _ (TensorBlock R V W n) k (x ⊗ₜ[R] y)) :
        ExteriorAlgebra R (V × W)) =
      (exteriorPower.map k (LinearMap.inl R V W) x : ExteriorAlgebra R (V × W)) *
      (exteriorPower.map (n - k) (LinearMap.inr R V W) y : ExteriorAlgebra R (V × W)) := by
  rw [← wedgeMap_tmul_coe, ← tensorEquiv_symm_comp_lof b c]
  rfl

/-- Exterior multiplication of a tensor is recovered in its own summand by the decomposition.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_wedgeMap (n : ℕ) (k : Fin (n + 1)) (z : TensorBlock R V W n k) :
    tensorEquiv b c n (wedgeMap R V W n k z) =
      DirectSum.lof R _ (TensorBlock R V W n) k z := by
  rw [← tensorEquiv_symm_comp_lof b c]
  exact (tensorEquiv b c n).apply_symm_apply _

omit [LinearOrder I] [LinearOrder J] in
private theorem leftCount_sumEquiv_symm (n : ℕ) (k : Fin (n + 1))
    (s : Set.powersetCard I k) (t : Set.powersetCard J (n - k)) :
    ExteriorSum.leftCount ((Set.powersetCard.sumEquiv n).symm ⟨k, s, t⟩) = k := by
  have hf : ((s.val.disjSum t.val).filter (fun z => z.isLeft = true)) =
      s.val.map Function.Embedding.inl := by
    ext z
    cases z <;> simp
  change ((s.val.disjSum t.val).filter (fun z => z.isLeft = true)).card = k
  rw [hf, Finset.card_map, s.property]

private theorem projection_basis (n k : ℕ) (s : Set.powersetCard (I ⊕ J) n) :
    ExteriorSum.projection (b.prod c) n k ((b.prod c).exteriorPower n s) =
      if ExteriorSum.leftCount s = k then (b.prod c).exteriorPower n s else 0 := by
  apply ((b.prod c).exteriorPower n).repr.injective
  ext t
  rw [ExteriorSum.projection_repr]
  by_cases hs : ExteriorSum.leftCount s = k
  · rw [if_pos hs]
    by_cases hst : s = t
    · subst t
      rw [if_pos hs]
    · simp only [Basis.repr_self_apply, if_neg hst, ite_self]
  · rw [if_neg hs, map_zero, Finsupp.zero_apply]
    by_cases hst : s = t
    · subst t
      rw [if_neg hs]
    · simp only [Basis.repr_self_apply, if_neg hst, ite_self]

/-- The tensor decomposition has precisely the count-based exterior blocks as its components.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem wedgeMap_tensorEquiv_component (n : ℕ) (k : Fin (n + 1)) (x : ⋀[R]^n (V × W)) :
    wedgeMap R V W n k (tensorEquiv b c n x k) =
      ExteriorSum.projection (b.prod c) n k x := by
  suffices h : (wedgeMap R V W n k).comp
      ((DirectSum.component R _ (TensorBlock R V W n) k).comp
        (tensorEquiv b c n).toLinearMap) = ExteriorSum.projection (b.prod c) n k from
    DFunLike.congr_fun h x
  apply ((b.prod c).exteriorPower n).ext
  intro u
  obtain ⟨⟨l, s, t⟩, rfl⟩ := (Set.powersetCard.sumEquiv n).symm.surjective u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorEquiv_basis,
    DirectSum.component.of, projection_basis, leftCount_sumEquiv_symm]
  by_cases h : l = k
  · subst l
    rw [dif_pos rfl, if_pos rfl, ← tensorEquiv_symm_comp_lof b c]
    exact tensorEquiv_symm_basis b c n k s t
  · rw [dif_neg h, map_zero, if_neg (fun hv => h (Fin.ext hv))]

/-- The image of each canonical exterior tensor map is the corresponding exterior block.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem range_wedgeMap (n : ℕ) (k : Fin (n + 1)) :
    LinearMap.range (wedgeMap R V W n k) = ExteriorSum.block (b.prod c) n k := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(tensorEquiv b c n).symm (DirectSum.lof R _ (TensorBlock R V W n) k z), ?_⟩
    rw [← wedgeMap_tensorEquiv_component, LinearEquiv.apply_symm_apply, DirectSum.lof_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨tensorEquiv b c n y k, wedgeMap_tensorEquiv_component b c n k y⟩

include b c in
/-- Each canonical exterior tensor map is injective, including in infinite rank.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem wedgeMap_injective (n : ℕ) (k : Fin (n + 1)) :
    Function.Injective (wedgeMap R V W n k) := by
  rw [← tensorEquiv_symm_comp_lof b c]
  exact (tensorEquiv b c n).symm.injective.comp (DirectSum.of_injective k)

/-- A count-based exterior block is linearly equivalent to its actual exterior tensor product.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior blocks.
-/
noncomputable def blockTensorEquiv (n : ℕ) (k : Fin (n + 1)) :
    TensorBlock R V W n k ≃ₗ[R] ExteriorSum.block (b.prod c) n k :=
  (LinearEquiv.ofInjective (wedgeMap R V W n k) (wedgeMap_injective b c n k)).trans
    (LinearEquiv.ofEq _ _ (range_wedgeMap b c n k))

/-- The block equivalence includes each tensor by the canonical exterior multiplication map.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior blocks.
-/
theorem blockTensorEquiv_apply_coe (n : ℕ) (k : Fin (n + 1)) (z : TensorBlock R V W n k) :
    (blockTensorEquiv b c n k z : ⋀[R]^n (V × W)) = wedgeMap R V W n k z := rfl

/-- Recomposition is the sum of the canonical exterior tensor maps, so it does not depend on
the bases used to construct the inverse.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, exterior decomposition.
-/
theorem tensorEquiv_symm_toLinearMap (n : ℕ) :
    (tensorEquiv b c n).symm.toLinearMap =
      DirectSum.toModule R _ _ (wedgeMap R V W n) := by
  apply DirectSum.linearMap_ext
  intro k
  rw [tensorEquiv_symm_comp_lof]
  apply LinearMap.ext
  intro z
  exact (DirectSum.toModule_lof R k z).symm

end T3.ExteriorTensor
