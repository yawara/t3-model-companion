/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.ExteriorBracket
public import T3.GroupTheory.GeneratorRank
public import T3.GroupTheory.GeneratorRank.Cardinal
public import T3.LinearAlgebra.ExteriorContraction

/-!
# Generator lower bounds forced by paired commutators

In the free exponent-three group on countably many generators, the product of the first `n`
disjoint generator commutators can lie in the derived subgroup of `D` only if `D` needs at
least `2n` generators. The proof follows the manuscript: pass to the exterior square of the
first graded layer, contract by coordinate functionals, and recover `2n` independent vectors
in the image of the first layer of `D`. The cardinal statement applies to arbitrary subgroups.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3).
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra BigOperators commutatorElement

namespace T3.Free

open AssociatedGraded

/-- The product of the first `n` disjoint commutators in the countably generated free group.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3), `aₙ`.
-/
def pairedCommutator (n : ℕ) : Free ℕ :=
  ((List.range n).map fun i => ⁅of (2 * i), of (2 * i + 1)⁆).prod

/-- Every paired product belongs to the derived subgroup of the ambient free group.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedCommutator_mem_commutator (n : ℕ) :
    pairedCommutator n ∈ commutator (Free ℕ) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem sigmaOne_layerOneBasis (x : Layer (Free ℕ) 1) :
    sigmaOne (layerOneBasis (I := ℕ)) x = (exteriorPower.oneEquiv (ZMod 3) _).symm x := by
  change (exteriorPower.oneEquiv (ZMod 3) _).symm
    (layerOneEquiv.symm (layerOneEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The second initial form of the paired product is the sum of the corresponding wedges.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3), `gr₂(aₙ) = αₙ`.
-/
theorem sigmaTwo_pairedCommutator (n : ℕ) :
    sigmaTwo (layerOneBasis (I := ℕ))
      (mk (Free ℕ) 2 ⟨pairedCommutator n, pairedCommutator_mem_commutator n⟩) =
      exteriorPower.pairedForm (layerOneBasis (I := ℕ)) n := by
  induction n with
  | zero =>
    change sigmaTwo _ 0 = _
    simp [exteriorPower.pairedForm]
  | succ n ih =>
    have hp : pairedCommutator (n + 1) =
        pairedCommutator n * ⁅of (2 * n), of (2 * n + 1)⁆ := by
      simp [pairedCommutator, List.range_succ]
    have hm : (⟨pairedCommutator (n + 1), pairedCommutator_mem_commutator (n + 1)⟩ :
        term (Free ℕ) 2) = ⟨pairedCommutator n, pairedCommutator_mem_commutator n⟩ *
          ⟨⁅of (2 * n), of (2 * n + 1)⁆,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ :=
      Subtype.ext hp
    have hc : sigmaTwo (layerOneBasis (I := ℕ))
        (mk (Free ℕ) 2 ⟨⁅of (2 * n), of (2 * n + 1)⁆,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩) =
        wedgeVV (ZMod 3) _ (layerOneBasis (2 * n)) (layerOneBasis (2 * n + 1)) :=
      sigmaTwo_commutator (layerOneBasis (I := ℕ)) ⟨2 * n, 2 * n + 1, by omega⟩
    rw [hm, mk_mul, map_add, ih, hc]
    simp [exteriorPower.pairedForm, Finset.sum_range_succ]

/-- Every nonempty paired product is nonidentity.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedCommutator_ne_one {n : ℕ} (hn : 0 < n) : pairedCommutator n ≠ 1 := by
  intro h
  have hz : (mk (Free ℕ) 2
      ⟨pairedCommutator n, pairedCommutator_mem_commutator n⟩) = 0 := by
    apply (mk_eq_zero _ _ _).mpr
    change pairedCommutator n ∈ _
    rw [h]
    exact Subgroup.one_mem _
  have heq := sigmaTwo_pairedCommutator n
  rw [hz, map_zero] at heq
  exact exteriorPower.pairedForm_ne_zero (layerOneBasis (I := ℕ)) hn heq.symm

private instance subgroupExponentThree (D : Subgroup (Free ℕ)) : Fact (HasExponentThree D) :=
  ⟨fun d => Subtype.ext (pow_three (d : Free ℕ))⟩

private theorem first_mk_mem_range (D : Subgroup (Free ℕ)) (a : Free ℕ) (ha : a ∈ D) :
    mk (Free ℕ) 1 ⟨a, Subgroup.mem_top _⟩ ∈ LinearMap.range (mapLayer D.subtype 1) := by
  refine ⟨mk D 1 ⟨⟨a, ha⟩, Subgroup.mem_top _⟩, ?_⟩
  rw [mapLayer_mk]
  rfl

private theorem sigmaTwo_mem_wedgeSpan (D : Subgroup (Free ℕ))
    {a : Free ℕ} (ha : a ∈ D.lowerCentralSeries 1) :
    sigmaTwo (layerOneBasis (I := ℕ))
      (mk (Free ℕ) 2 ⟨a, (Subgroup.lowerCentralSeries_mono 1 (show D ≤ ⊤ from le_top)) ha⟩) ∈
      exteriorPower.wedgeSpan (LinearMap.range (mapLayer D.subtype 1)) := by
  change a ∈ ⁅D, D⁆ at ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ha
    have heq := sigmaTwo_bracketLayer (layerOneBasis (I := ℕ))
      (mk (Free ℕ) 1 ⟨x, Subgroup.mem_top _⟩)
      (mk (Free ℕ) 1 ⟨y, Subgroup.mem_top _⟩)
    rw [bracketLayer_mk, sigmaOne_layerOneBasis, sigmaOne_layerOneBasis] at heq
    change sigmaTwo (layerOneBasis (I := ℕ))
      (mk (Free ℕ) 2 ⟨⁅x, y⁆, _⟩) =
        wedgeVV (ZMod 3) _ (mk (Free ℕ) 1 ⟨x, Subgroup.mem_top _⟩)
          (mk (Free ℕ) 1 ⟨y, Subgroup.mem_top _⟩) at heq
    rw [heq]
    exact Submodule.subset_span ⟨_, first_mk_mem_range D x hx,
      _, first_mk_mem_range D y hy, rfl⟩
  | one =>
    change sigmaTwo _ 0 ∈ _
    simp
  | mul a b ha hb hia hib =>
    have ham : a ∈ term (Free ℕ) 2 :=
      Subgroup.lowerCentralSeries_mono 1 (show D ≤ ⊤ from le_top) ha
    have hbm : b ∈ term (Free ℕ) 2 :=
      Subgroup.lowerCentralSeries_mono 1 (show D ≤ ⊤ from le_top) hb
    have hm : (mk (Free ℕ) 2 ⟨a * b, (term (Free ℕ) 2).mul_mem ham hbm⟩) =
        mk (Free ℕ) 2 ⟨a, ham⟩ + mk (Free ℕ) 2 ⟨b, hbm⟩ := rfl
    rw [hm, map_add]
    exact Submodule.add_mem _ hia hib
  | inv a ha hia =>
    have ham : a ∈ term (Free ℕ) 2 :=
      Subgroup.lowerCentralSeries_mono 1 (show D ≤ ⊤ from le_top) ha
    have hi : (mk (Free ℕ) 2 ⟨a⁻¹, (term (Free ℕ) 2).inv_mem ham⟩) =
        -mk (Free ℕ) 2 ⟨a, ham⟩ := rfl
    rw [hi, map_neg]
    exact Submodule.neg_mem _ hia

/-- For a finitely generated subgroup, containing the paired product in its own derived
subgroup forces at least `2n` generators.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedCommutator_rank_le (D : Subgroup (Free ℕ)) [Group.FG D] (n : ℕ)
    (h : pairedCommutator n ∈ D.lowerCentralSeries 1) : 2 * n ≤ Group.rank D := by
  have hw := sigmaTwo_mem_wedgeSpan D h
  rw [sigmaTwo_pairedCommutator] at hw
  exact (exteriorPower.pairedForm_finrank_le (layerOneBasis (I := ℕ)) hw).trans
    ((LinearMap.finrank_range_le (mapLayer D.subtype 1)).trans finrank_layerOne_le_rank)

/-- The paired product forces at least `2n` generators in every subgroup, including subgroups
with no finite generating set. The hypothesis is exactly membership in the ambient image of
`γ₂(D)`, with no strictness assumption on `D`.

Paper-ID: examples.commutator_rank_lower_bound
TeX: T3_modelcompanion_v9.tex, `lemma:D can be large` (Lemma 5.3).
-/
theorem pairedCommutator_cardinalRank_le (D : Subgroup (Free ℕ)) (n : ℕ)
    (h : pairedCommutator n ∈ D.lowerCentralSeries 1) :
    ((2 * n : ℕ) : Cardinal) ≤ Group.cardinalRank D := by
  by_cases hfin : Group.FG D
  · let := hfin
    rw [Group.cardinalRank_eq_rank]
    exact_mod_cast pairedCommutator_rank_le D n h
  · exact Cardinal.natCast_lt_aleph0.le.trans
      (not_lt.mp (fun hh => hfin ((Group.cardinalRank_lt_aleph0_iff D).mp hh)))

end T3.Free
