/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Graded
public import T3.GroupTheory.AssociatedGraded.Lie
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# The bracket respects the two factor degrees of a coproduct

Pure blocks are the images of the factor layers and mixed blocks are the images of the
canonical tensor maps, all embedded in the actual graded Lie algebra. Only the nine blocks
of positive total degree at most three can be nonzero. The bracket adds both factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/

@[expose] public section

open scoped DirectSum TensorProduct

namespace T3.Coproduct

open AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- The left pure component in the actual graded Lie algebra of the coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, block `Bᵢ,₀`.
-/
def pureLeftBlock (i : ℕ) : Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) i).comp (mapLayer inl i))

/-- The right pure component in the actual graded Lie algebra of the coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, block `B₀,ⱼ`.
-/
def pureRightBlock (j : ℕ) : Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) j).comp (mapLayer inr j))

/-- The mixed tensor component in the actual graded Lie algebra, in positive factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, block `Bᵢ,ⱼ`.
-/
def mixedBlock {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) (i + j)).comp
    (mixedMap hi hj))

/-- The paper's blocks, using the canonical images in the graded coproduct.
Degree zero and degrees at least four vanish in the actual graded quotients.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
def block : ℕ → ℕ → Submodule (ZMod 3) (GradedModule (Coproduct G H))
  | 0, j => pureRightBlock j
  | i + 1, 0 => pureLeftBlock (i + 1)
  | i + 1, j + 1 => mixedBlock (Nat.succ_pos i) (Nat.succ_pos j)

omit [Fact (HasExponentThree H)] in
private theorem pureLeftBlock_le_grade (i : ℕ) :
    pureLeftBlock (G := G) (H := H) i ≤ grade (Coproduct G H) i := by
  rintro x ⟨y, rfl⟩
  exact ⟨mapLayer inl i y, rfl⟩

omit [Fact (HasExponentThree G)] in
private theorem pureRightBlock_le_grade (j : ℕ) :
    pureRightBlock (G := G) (H := H) j ≤ grade (Coproduct G H) j := by
  rintro x ⟨y, rfl⟩
  exact ⟨mapLayer inr j y, rfl⟩

private theorem mixedBlock_le_grade {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    mixedBlock (G := G) (H := H) hi hj ≤ grade (Coproduct G H) (i + j) := by
  rintro x ⟨y, rfl⟩
  exact ⟨mixedMap hi hj y, rfl⟩

omit [Fact (HasExponentThree H)] in
private theorem pureLeftBlock_zero : pureLeftBlock (G := G) (H := H) 0 = ⊥ := by
  apply eq_bot_iff.mpr
  exact (pureLeftBlock_le_grade 0).trans (le_of_eq grade_zero)

omit [Fact (HasExponentThree G)] in
private theorem pureRightBlock_zero : pureRightBlock (G := G) (H := H) 0 = ⊥ := by
  apply eq_bot_iff.mpr
  exact (pureRightBlock_le_grade 0).trans (le_of_eq grade_zero)

/-- On the right axis the blocks are the canonical right pure images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
@[simp]
theorem block_zero_left (j : ℕ) : block (G := G) (H := H) 0 j = pureRightBlock j := rfl

/-- On the left axis the blocks are the canonical left pure images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
@[simp]
theorem block_zero_right (i : ℕ) : block (G := G) (H := H) i 0 = pureLeftBlock i := by
  cases i with
  | zero => exact pureRightBlock_zero.trans pureLeftBlock_zero.symm
  | succ i => rfl

/-- In positive factor degrees the block is exactly the canonical mixed tensor image.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
theorem block_of_pos {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    block (G := G) (H := H) i j = mixedBlock hi hj := by
  cases i with
  | zero => omega
  | succ i => cases j with
    | zero => omega
    | succ j => rfl

/-- The total homogeneous degree of a block is the sum of its factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
theorem block_le_grade (i j : ℕ) :
    block (G := G) (H := H) i j ≤ grade (Coproduct G H) (i + j) := by
  cases i with
  | zero => simpa only [block, zero_add] using pureRightBlock_le_grade j
  | succ i => cases j with
    | zero => exact pureLeftBlock_le_grade (i + 1)
    | succ j => exact mixedBlock_le_grade _ _

/-- There is no block of total degree zero.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, positive grading.
-/
theorem block_zero_zero : block (G := G) (H := H) 0 0 = ⊥ := pureRightBlock_zero

/-- All blocks of total degree at least four vanish, as specified in the paper.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
theorem block_eq_bot_of_four_le {i j : ℕ} (h : 4 ≤ i + j) :
    block (G := G) (H := H) i j = ⊥ :=
  eq_bot_iff.mpr ((block_le_grade i j).trans (le_of_eq (grade_eq_bot_of_four_le h)))

omit [Fact (HasExponentThree H)] in
private theorem bracket_pureLeft_pureLeft {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ bracketLinear (pureLeftBlock (G := G) (H := H) i) (pureLeftBlock j) ≤
      pureLeftBlock (i + j) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨x, rfl⟩ y ⟨y, rfl⟩
  change ⁅DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) i (mapLayer inl i x),
    DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) j (mapLayer inl j y)⁆ ∈ _
  rw [bracket_lof hi hj, ← mapLayer_bracketLayer]
  exact ⟨bracketLayer hi hj x y, rfl⟩

omit [Fact (HasExponentThree G)] in
private theorem bracket_pureRight_pureRight {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ bracketLinear (pureRightBlock (G := G) (H := H) i) (pureRightBlock j) ≤
      pureRightBlock (i + j) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨x, rfl⟩ y ⟨y, rfl⟩
  change ⁅DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) i (mapLayer inr i x),
    DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) j (mapLayer inr j y)⁆ ∈ _
  rw [bracket_lof hi hj, ← mapLayer_bracketLayer]
  exact ⟨bracketLayer hi hj x y, rfl⟩

private theorem bracket_pureLeft_pureRight {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule.map₂ bracketLinear (pureLeftBlock (G := G) (H := H) i) (pureRightBlock j) ≤
      mixedBlock hi hj := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨x, rfl⟩ y ⟨y, rfl⟩
  change ⁅DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) i (mapLayer inl i x),
    DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) j (mapLayer inr j y)⁆ ∈ _
  rw [bracket_lof hi hj]
  exact ⟨x ⊗ₜ[ZMod 3] y, rfl⟩

omit [Fact (HasExponentThree G)] [Fact (HasExponentThree H)] in
private theorem bracket_swap_le
    {A B C : Submodule (ZMod 3) (GradedModule (Coproduct G H))}
    (h : Submodule.map₂ bracketLinear A B ≤ C) :
    Submodule.map₂ bracketLinear B A ≤ C := by
  apply Submodule.map₂_le.mpr
  intro x hx y hy
  change ⁅x, y⁆ ∈ C
  rw [← lie_skew]
  exact C.neg_mem (h (Submodule.apply_mem_map₂ _ hy hx))

/-- Bracketing a mixed `(1,1)` pure tensor with the left first layer gives its `(2,1)` component.
The left arguments occur in the cyclic order `c, a`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2, mixed bracket formula.
-/
theorem bracket_mixedMap_tmul_inl (a c : Layer G 1) (b : Layer H 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mixedMap (by decide) (by decide) (a ⊗ₜ[ZMod 3] b)) (mapLayer inl 1 c) =
      mixedMap (i := 2) (j := 1) (by decide) (by decide)
        (bracketLayer (by decide) (by decide) c a ⊗ₜ[ZMod 3] b) := by
  rw [mixedMap_tmul, mixedMap_tmul, mapLayer_bracketLayer (i := 1) (j := 1)]
  exact (bracketLayer_triple_cyclic _ _ _).trans (bracketLayer_triple_cyclic _ _ _)

/-- Bracketing a mixed `(1,1)` pure tensor with the right first layer gives the negative
`(1,2)` component, with the right arguments in their original order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2, mixed bracket formula.
-/
theorem bracket_mixedMap_tmul_inr (a : Layer G 1) (b c : Layer H 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mixedMap (by decide) (by decide) (a ⊗ₜ[ZMod 3] b)) (mapLayer inr 1 c) =
      -mixedMap (i := 1) (j := 2) (by decide) (by decide)
        (a ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) b c) := by
  rw [mixedMap_tmul, mixedMap_tmul, mapLayer_bracketLayer (i := 1) (j := 1),
    bracketLayer_one_two, neg_neg]
  exact bracketLayer_triple_cyclic _ _ _

private theorem bracket_mixed_pureLeft :
    Submodule.map₂ bracketLinear (mixedBlock (G := G) (H := H) (i := 1) (j := 1)
      (by decide) (by decide)) (pureLeftBlock 1) ≤
      mixedBlock (i := 2) (j := 1) (by decide) (by decide) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨t, rfl⟩ y ⟨z, rfl⟩
  change ⁅DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) 2 (mixedMap (by decide) (by decide) t),
    DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) 1 (mapLayer inl 1 z)⁆ ∈ _
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [bracket_lof (by decide) (by decide), bracket_mixedMap_tmul_inl]
    exact ⟨bracketLayer (by decide) (by decide) z x ⊗ₜ[ZMod 3] y, rfl⟩
  | add a b ha hb => simpa only [map_add, add_lie] using Submodule.add_mem _ ha hb

private theorem bracket_mixed_pureRight :
    Submodule.map₂ bracketLinear (mixedBlock (G := G) (H := H) (i := 1) (j := 1)
      (by decide) (by decide)) (pureRightBlock 1) ≤
      mixedBlock (i := 1) (j := 2) (by decide) (by decide) := by
  apply Submodule.map₂_le.mpr
  rintro x ⟨t, rfl⟩ y ⟨z, rfl⟩
  change ⁅DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) 2 (mixedMap (by decide) (by decide) t),
    DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) 1 (mapLayer inr 1 z)⁆ ∈ _
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [bracket_lof (by decide) (by decide), bracket_mixedMap_tmul_inr, map_neg]
    apply Submodule.neg_mem
    exact ⟨x ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) y z, rfl⟩
  | add a b ha hb => simpa only [map_add, add_lie] using Submodule.add_mem _ ha hb

/-- The actual Lie bracket adds the two factor degrees of the canonical coproduct blocks.

The mixed degree-three cases follow from cyclic invariance of the triple bracket. All larger
total degrees vanish in the actual associated graded Lie algebra.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
theorem bracket_block_le (i j k l : ℕ) :
    Submodule.map₂ bracketLinear (block (G := G) (H := H) i j) (block k l) ≤
      block (i + k) (j + l) := by
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    rw [block_zero_zero, Submodule.map₂_bot_left]
    exact bot_le
  by_cases hkl : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    rw [block_zero_zero, Submodule.map₂_bot_right]
    exact bot_le
  by_cases hhigh : 4 ≤ i + j + (k + l)
  · have hg : Submodule.map₂ bracketLinear (block (G := G) (H := H) i j) (block k l) ≤
        grade (Coproduct G H) (i + j + (k + l)) := by
      apply Submodule.map₂_le.mpr
      intro x hx y hy
      exact SetLike.GradedBracket.bracket_mem (block_le_grade i j hx) (block_le_grade k l hy)
    rw [grade_eq_bot_of_four_le hhigh] at hg
    exact hg.trans bot_le
  by_cases hj : j = 0
  · subst j
    have hi : 0 < i := by omega
    by_cases hl : l = 0
    · subst l
      simpa only [block_zero_right, add_zero] using
        bracket_pureLeft_pureLeft (G := G) (H := H) hi (by omega : 0 < k)
    by_cases hk : k = 0
    · subst k
      have hlp : 0 < l := by omega
      simpa only [block_zero_right, block_zero_left, add_zero, zero_add, block_of_pos hi hlp] using
        bracket_pureLeft_pureRight (G := G) (H := H) hi hlp
    have h : i = 1 ∧ k = 1 ∧ l = 1 := by omega
    rcases h with ⟨rfl, rfl, rfl⟩
    exact bracket_swap_le bracket_mixed_pureLeft
  by_cases hi : i = 0
  · subst i
    have hjp : 0 < j := by omega
    by_cases hk : k = 0
    · subst k
      simpa only [block_zero_left, zero_add] using
        bracket_pureRight_pureRight (G := G) (H := H) hjp (by omega : 0 < l)
    by_cases hl : l = 0
    · subst l
      have hkp : 0 < k := by omega
      simpa only [block_zero_right, block_zero_left, add_zero, zero_add, block_of_pos hkp hjp] using
        bracket_swap_le (bracket_pureLeft_pureRight (G := G) (H := H) hkp hjp)
    have h : j = 1 ∧ k = 1 ∧ l = 1 := by omega
    rcases h with ⟨rfl, rfl, rfl⟩
    exact bracket_swap_le bracket_mixed_pureRight
  by_cases hl : l = 0
  · subst l
    have h : i = 1 ∧ j = 1 ∧ k = 1 := by omega
    rcases h with ⟨rfl, rfl, rfl⟩
    exact bracket_mixed_pureLeft
  by_cases hk : k = 0
  · subst k
    have h : i = 1 ∧ j = 1 ∧ l = 1 := by omega
    rcases h with ⟨rfl, rfl, rfl⟩
    exact bracket_mixed_pureRight
  omega

/-- Elementwise form of the two-factor grading law for the actual Lie bracket.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v8.tex, `proposition:gr of free product`, item 2.
-/
theorem bracket_mem_block {i j k l : ℕ} {x y : GradedModule (Coproduct G H)}
    (hx : x ∈ block i j) (hy : y ∈ block k l) : ⁅x, y⁆ ∈ block (i + k) (j + l) :=
  bracket_block_le i j k l (Submodule.apply_mem_map₂ _ hx hy)

end T3.Coproduct
