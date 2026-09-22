/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.LinearAlgebra.Wedge
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Contraction of exterior two-forms

The contraction by a linear functional sends `u ∧ v` to `φ(u) • v - φ(v) • u`.
It preserves the supporting subspace. Applied to a sum of disjoint pairs of basis vectors,
the coordinate contractions recover all vectors in those pairs.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra BigOperators

namespace exteriorPower

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The alternating map inducing contraction.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
def contractionAlternating (φ : Module.Dual R V) : V [⋀^Fin 2]→ₗ[R] V where
  toFun v := φ (v 0) • v 1 - φ (v 1) • v 0
  map_update_add' v i x y := by
    fin_cases i <;> simp [add_smul, smul_add] <;> abel
  map_update_smul' v i r x := by
    fin_cases i <;> simp [smul_sub, smul_smul, mul_comm]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all

/-- Contraction of a two-form by an arbitrary linear functional.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
def contraction (φ : Module.Dual R V) : ⋀[R]^2 V →ₗ[R] V :=
  alternatingMapLinearEquiv (contractionAlternating φ)

/-- The defining contraction formula on a decomposable two-form.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
@[simp]
theorem contraction_wedge (φ : Module.Dual R V) (u v : V) :
    contraction φ (T3.wedgeVV R V u v) = φ u • v - φ v • u := by
  have hw : T3.wedgeVV R V u v = ιMulti R 2 ![u, v] := by
    apply Subtype.ext
    simp [T3.wedgeVV, T3.gradedMul, T3.oneEquiv_symm_coe,
      ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  rw [hw, contraction, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The ambient exterior square of a subspace, expressed as the span of its wedges.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3), `Λ²U` inside `Λ²V`.
-/
def wedgeSpan (U : Submodule R V) : Submodule R (⋀[R]^2 V) :=
  Submodule.span R {q | ∃ u ∈ U, ∃ v ∈ U, T3.wedgeVV R V u v = q}

/-- Contraction of the exterior square of a subspace takes values in that subspace.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem contraction_mem (φ : Module.Dual R V) (U : Submodule R V)
    {q : ⋀[R]^2 V} (hq : q ∈ wedgeSpan U) : contraction φ q ∈ U := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hq
    rw [contraction_wedge]
    exact U.sub_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
  | zero => simp
  | add q r hq hr hi hj => simpa using U.add_mem hi hj
  | smul r q hq hi => simpa using U.smul_mem r hi

variable (b : Module.Basis ℕ R V)

/-- The two-form consisting of the first `n` disjoint pairs of basis vectors.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3), `αₙ`.
-/
def pairedForm (n : ℕ) : ⋀[R]^2 V :=
  ∑ i ∈ Finset.range n, T3.wedgeVV R V (b (2 * i)) (b (2 * i + 1))

/-- Contraction by an even coordinate recovers the next odd basis vector.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem contraction_pairedForm_even {n k : ℕ} (hk : k < n) :
    contraction (b.coord (2 * k)) (pairedForm b n) = b (2 * k + 1) := by
  classical
  simp only [pairedForm, map_sum, contraction_wedge, Module.Basis.coord_apply,
    Module.Basis.repr_self]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    have h₁ : 2 * i ≠ 2 * k := by omega
    have h₂ : 2 * i + 1 ≠ 2 * k := by omega
    simp [h₁, h₂]
  · simp [hk]

/-- Contraction by an odd coordinate recovers the negative of the preceding basis vector.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem contraction_pairedForm_odd {n k : ℕ} (hk : k < n) :
    contraction (b.coord (2 * k + 1)) (pairedForm b n) = -b (2 * k) := by
  classical
  simp only [pairedForm, map_sum, contraction_wedge, Module.Basis.coord_apply,
    Module.Basis.repr_self]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    have h₁ : 2 * i ≠ 2 * k + 1 := by omega
    simp [h₁, hik]
  · simp [hk]

/-- Every vector in the first `2n` basis positions lies in a subspace supporting the paired form.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem basis_mem_of_pairedForm_mem {n : ℕ} {U : Submodule R V}
    (h : pairedForm b n ∈ wedgeSpan U) {j : ℕ} (hj : j < 2 * n) : b j ∈ U := by
  have hk : j / 2 < n := by omega
  have heven := contraction_mem (b.coord (2 * (j / 2))) U h
  have hodd := contraction_mem (b.coord (2 * (j / 2) + 1)) U h
  rw [contraction_pairedForm_even b hk] at heven
  rw [contraction_pairedForm_odd b hk] at hodd
  rcases Nat.mod_two_eq_zero_or_one j with hzero | hone
  · have hj' : j = 2 * (j / 2) := by omega
    rw [hj']
    exact U.neg_mem_iff.mp hodd
  · have hj' : j = 2 * (j / 2) + 1 := by omega
    rw [hj']
    exact heven

/-- A finite-dimensional supporting subspace has dimension at least twice the number of pairs.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedForm_finrank_le [StrongRankCondition R] {n : ℕ} {U : Submodule R V}
    [Module.Finite R U] (h : pairedForm b n ∈ wedgeSpan U) :
    2 * n ≤ Module.finrank R U := by
  let v : Fin (2 * n) → U := fun j => ⟨b j, basis_mem_of_pairedForm_mem b h j.isLt⟩
  have hi : LinearIndependent R v := LinearIndependent.of_comp U.subtype
    (b.linearIndependent.comp (fun j : Fin (2 * n) => (j : ℕ)) Fin.val_injective)
  simpa using hi.fintype_card_le_finrank

/-- A paired form with at least one pair is nonzero.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v7.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedForm_ne_zero [Nontrivial R] {n : ℕ} (hn : 0 < n) : pairedForm b n ≠ 0 := by
  intro hz
  have h := contraction_pairedForm_even b hn
  rw [hz, map_zero] at h
  exact b.ne_zero 1 h.symm

end exteriorPower
