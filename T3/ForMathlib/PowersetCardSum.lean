/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Set.PowersetCard

/-!
# Combinations in a disjoint union

A finite subset of a disjoint union is determined by its left and right subsets. For a fixed
total cardinality, this identifies its indices with the disjoint union of products of the
corresponding left and right combination types. No finiteness assumption on either type is used.

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
