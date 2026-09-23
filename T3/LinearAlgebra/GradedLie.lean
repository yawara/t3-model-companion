/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Positive gradings and generation in degree one

The paper's graded Lie ring is represented by mathlib's `LieRing`, its canonical Lie algebra
over the integers, and a `GradedLieAlgebra` with zero component trivial. The same definition
over any commutative ring includes the paper's graded Lie algebras over a field. Brackets of
components mean the submodule spanned by all brackets, expressed by `Submodule.map₂`.

Paper-ID: linear_algebra.graded_lie, linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Definition 2.7 and Remark 2.8, lines 351–371; no labels.
-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A submodule containing the generators and stable under bracketing on the right by
the generators contains the Lie algebra they generate.

Paper-ID: linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Remark 2.8, item 2, proof by the Jacobi identity.
-/
theorem lieSpan_le_of_lie_mem_right (S U : Submodule R L) (hS : S ≤ U)
    (hbr : ∀ x ∈ U, ∀ y ∈ S, ⁅x, y⁆ ∈ U) :
    (lieSpan R L (S : Set L)).toSubmodule ≤ U := by
  intro x hx
  change x ∈ lieSpan R L (S : Set L) at hx
  have hpair : x ∈ U ∧ ∀ u ∈ U, ⁅x, u⁆ ∈ U := by
    induction hx using lieSpan_induction with
    | mem x hx =>
      refine ⟨hS hx, fun u hu => ?_⟩
      rw [← lie_skew x u]
      exact U.neg_mem (hbr u hu x hx)
    | zero =>
      exact ⟨U.zero_mem, fun u _ => by simpa only [zero_lie] using U.zero_mem⟩
    | add x y _ _ ihx ihy =>
      refine ⟨U.add_mem ihx.1 ihy.1, fun u hu => ?_⟩
      rw [add_lie]
      exact U.add_mem (ihx.2 u hu) (ihy.2 u hu)
    | smul r x _ ih =>
      refine ⟨U.smul_mem r ih.1, fun u hu => ?_⟩
      rw [smul_lie]
      exact U.smul_mem r (ih.2 u hu)
    | lie x y _ _ ihx ihy =>
      refine ⟨ihx.2 y ihy.1, fun u hu => ?_⟩
      rw [lie_lie]
      exact U.sub_mem (ihx.2 _ (ihy.2 u hu)) (ihy.2 _ (ihx.2 u hu))
  exact hpair.1

end LieSubalgebra

namespace LieRing

/-- The paper's biadditive, alternating bracket and cyclic Jacobi identity give mathlib's
native Lie-ring structure. In particular its Leibniz convention is equivalent to the
left-nested cyclic identity, with no characteristic restriction.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, items 2–4, lines 357–359.
-/
@[implicit_reducible]
def ofCyclicJacobi {L : Type*} [AddCommGroup L] [Bracket L L]
    (hadd : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
    (hadd' : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆)
    (hself : ∀ x : L, ⁅x, x⁆ = 0)
    (hjacobi : ∀ x y z : L, ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0) :
    LieRing L where
  add_lie := hadd
  lie_add := hadd'
  lie_self := hself
  leibniz_lie x y z := by
    have hskew (a b : L) : ⁅a, b⁆ = -⁅b, a⁆ := by
      have h := hself (a + b)
      simp only [hadd, hadd', hself, zero_add, add_zero] at h
      exact eq_neg_of_add_eq_zero_left h
    have hneg (a b : L) : ⁅-a, b⁆ = -⁅a, b⁆ :=
      (AddMonoidHom.mk' (fun a => ⁅a, b⁆) (fun a a' => hadd a a' b)).map_neg a
    have h := hjacobi x y z
    rw [hskew ⁅y, z⁆ x, hskew z x, hneg, hskew ⁅x, z⁆ y, neg_neg] at h
    symm
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, add_right_comm] using h

variable {L : Type*} [LieRing L]

/-- Mathlib's bracket is additive in both variables, as in the paper's Lie-ring definition.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, item 2, line 357.
-/
theorem bracket_biadditive (x y z : L) :
    (⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆) ∧ (⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆) :=
  ⟨add_lie x y z, lie_add x y z⟩

/-- Mathlib's bracket is alternating, including in characteristic two.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, item 3, line 358.
-/
theorem bracket_alternating (x : L) : ⁅x, x⁆ = 0 := lie_self x

/-- The cyclic Jacobi identity in the paper's left-nested convention follows from mathlib's
Lie-ring axioms, over every characteristic and also over the integers.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, item 4, line 359.
-/
theorem cyclic_jacobi (x y z : L) :
    ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0 := by
  have h := congrArg Neg.neg (lie_jacobi z x y)
  simpa only [neg_add, neg_zero, lie_skew] using h

/-- Lie brackets are antisymmetric, without any restriction on the characteristic.

Paper-ID: linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Remark 2.8, item 1, line 367.
-/
theorem bracket_eq_neg_swap (x y : L) : ⁅x, y⁆ = -⁅y, x⁆ :=
  (lie_skew x y).symm

end LieRing

namespace GradedLieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ℕ → Submodule R L) [GradedLieAlgebra ℒ]

/-- A grading is positive when its degree-zero component is trivial. Together with mathlib's
`GradedLieAlgebra`, this represents the decomposition and all Lie axioms in the paper.
For a Lie ring use `R = ℤ`; for a Lie algebra over a field use that field as `R`.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, lines 351–363; no label.
-/
def IsPositive : Prop := ℒ 0 = ⊥

/-- The bracket of homogeneous components is contained in their sum degree.

Paper-ID: linear_algebra.graded_lie
TeX: T3_modelcompanion_v8.tex, Definition 2.7, item 1, line 356.
-/
theorem map₂_le_grade (i j : ℕ) :
    Submodule.map₂ (LieAlgebra.ad R L).toLinearMap (ℒ i) (ℒ j) ≤ ℒ (i + j) :=
  Submodule.map₂_le.mpr fun _ hx _ hy => SetLike.GradedBracket.bracket_mem hx hy

private def iteratedBracket (S : Submodule R L) : ℕ → Submodule R L
  | 0 => S
  | n + 1 => Submodule.map₂ (LieAlgebra.ad R L).toLinearMap (iteratedBracket S n) S

private theorem iteratedBracket_le_grade (n : ℕ) :
    iteratedBracket (ℒ 1) n ≤ ℒ (n + 1) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact (Submodule.map₂_le_map₂ ih le_rfl).trans (map₂_le_grade ℒ (n + 1) 1)

omit [GradedLieAlgebra ℒ] in
private theorem iSup_iteratedBracket_eq_top
    (hgen : LieSubalgebra.lieSpan R L (ℒ 1 : Set L) = ⊤) :
    (⨆ n, iteratedBracket (ℒ 1) n) = ⊤ := by
  let U := ⨆ n, iteratedBracket (ℒ 1) n
  have hS : ℒ 1 ≤ U := le_iSup (fun n => iteratedBracket (ℒ 1) n) 0
  have hbr : ∀ x ∈ U, ∀ y ∈ ℒ 1, ⁅x, y⁆ ∈ U := by
    intro x hx y hy
    refine Submodule.iSup_induction (fun n => iteratedBracket (ℒ 1) n)
      (motive := fun x => ⁅x, y⁆ ∈ U) hx ?_ ?_ ?_
    · intro n x hx
      exact (le_iSup (fun n => iteratedBracket (ℒ 1) n) (n + 1))
        (Submodule.apply_mem_map₂ _ hx hy)
    · simpa only [zero_lie] using U.zero_mem
    · intro x z hx hz
      simpa only [add_lie] using U.add_mem hx hz
  have h := LieSubalgebra.lieSpan_le_of_lie_mem_right (ℒ 1) U hS hbr
  rw [hgen] at h
  exact top_unique h

private theorem grade_le_iteratedBracket_of_iSup_eq_top
    (h : (⨆ n, iteratedBracket (ℒ 1) n) = ⊤) (n : ℕ) :
    ℒ (n + 1) ≤ iteratedBracket (ℒ 1) n := by
  intro x hx
  have hx' : x ∈ ⨆ n, iteratedBracket (ℒ 1) n := by rw [h]; trivial
  have hp : (DirectSum.decompose ℒ x (n + 1) : L) ∈ iteratedBracket (ℒ 1) n := by
    refine Submodule.iSup_induction (fun n => iteratedBracket (ℒ 1) n)
      (motive := fun x => (DirectSum.decompose ℒ x (n + 1) : L) ∈
        iteratedBracket (ℒ 1) n) hx' ?_ ?_ ?_
    · intro k y hy
      by_cases hk : k = n
      · subst k
        rwa [DirectSum.decompose_of_mem_same ℒ (iteratedBracket_le_grade ℒ n hy)]
      · rw [DirectSum.decompose_of_mem_ne ℒ (iteratedBracket_le_grade ℒ k hy)
          (fun heq => hk (Nat.add_right_cancel heq))]
        exact Submodule.zero_mem _
    · simp
    · intro y z hy hz
      simpa using (iteratedBracket (ℒ 1) n).add_mem hy hz
  rwa [DirectSum.decompose_of_mem_same ℒ hx] at hp

/-- If every positive component is the bracket of the preceding component with degree one,
then degree one generates the entire Lie algebra.

Paper-ID: linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Remark 2.8, item 2, lines 368–369, reverse implication.
-/
theorem lieSpan_eq_top_of_map₂_eq_grade (hzero : IsPositive ℒ)
    (hstep : ∀ i, 1 ≤ i →
      Submodule.map₂ (LieAlgebra.ad R L).toLinearMap (ℒ i) (ℒ 1) = ℒ (i + 1)) :
    LieSubalgebra.lieSpan R L (ℒ 1 : Set L) = ⊤ := by
  let K := LieSubalgebra.lieSpan R L (ℒ 1 : Set L)
  have hgrade : ∀ n, ℒ n ≤ K.toSubmodule := by
    intro n
    cases n with
    | zero => rw [show ℒ 0 = ⊥ from hzero]; exact bot_le
    | succ n =>
        induction n with
        | zero => exact LieSubalgebra.subset_lieSpan
        | succ n ih =>
            rw [← hstep (n + 1) (Nat.le_add_left 1 n)]
            exact Submodule.map₂_le.mpr fun _ hx _ hy =>
              K.lie_mem (ih hx) (LieSubalgebra.subset_lieSpan hy)
  apply top_unique
  intro x _
  exact DirectSum.Decomposition.inductionOn ℒ K.zero_mem
    (fun y => hgrade _ y.property) (fun _ _ hx hy => K.add_mem hx hy) x

/-- A Lie algebra generated by degree one has each positive successor component equal to
all linear combinations of brackets of the preceding component with degree one.

Paper-ID: linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Remark 2.8, item 2, lines 368–369, forward implication.
-/
theorem map₂_eq_grade_of_lieSpan_eq_top
    (hgen : LieSubalgebra.lieSpan R L (ℒ 1 : Set L) = ⊤) {i : ℕ} (hi : 1 ≤ i) :
    Submodule.map₂ (LieAlgebra.ad R L).toLinearMap (ℒ i) (ℒ 1) = ℒ (i + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  have heq : ∀ n, iteratedBracket (ℒ 1) n = ℒ (n + 1) := fun n =>
    le_antisymm (iteratedBracket_le_grade ℒ n)
      (grade_le_iteratedBracket_of_iSup_eq_top ℒ (iSup_iteratedBracket_eq_top ℒ hgen) n)
  rw [← heq n]
  exact heq (n + 1)

/-- For a positively graded Lie algebra, generation by degree one is equivalent to the
successor-bracket condition in every positive degree. The statement holds over any
commutative ring, so it includes Lie rings over the integers and Lie algebras over fields.

Paper-ID: linear_algebra.degree_one_generation
TeX: T3_modelcompanion_v8.tex, Remark 2.8, item 2, lines 368–369.
-/
theorem lieSpan_eq_top_iff_map₂_eq_grade (hzero : IsPositive ℒ) :
    LieSubalgebra.lieSpan R L (ℒ 1 : Set L) = ⊤ ↔
      ∀ i, 1 ≤ i →
        Submodule.map₂ (LieAlgebra.ad R L).toLinearMap (ℒ i) (ℒ 1) = ℒ (i + 1) :=
  ⟨fun h _ hi => map₂_eq_grade_of_lieSpan_eq_top ℒ h hi,
    lieSpan_eq_top_of_map₂_eq_grade ℒ hzero⟩

end GradedLieAlgebra
