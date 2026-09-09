/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded.Bracket
public import T3.GroupTheory.Generation

/-!
# A graded criterion for coincidence of the central series

The two claims in the coproduct-with-`F₂` argument detect noncentral elements by nonzero
brackets in the actual graded quotients. Triple brackets detect elements outside the derived
subgroup. Once this identifies the second center, brackets of degree-two vectors detect
elements outside the third lower central term. The general implications below apply without
finite generation; the coproduct-specific separation arguments supply their hypotheses.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, proof lines 974–1001.
-/

@[expose] public section

open scoped commutatorElement

namespace T3.AssociatedGraded

variable {G : Type*} [Group G] [Fact (HasExponentThree G)]

/-- A nontrivial exponent-three group has a nonzero first graded layer. This supplies the
element outside the derived subgroup used in both claims of the paper's `F₂` argument.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, lines 982 and 999.
-/
theorem exists_nonzero_layerOne [Nontrivial G] : ∃ a : Layer G 1, a ≠ 0 := by
  have hderived : commutator G ≠ ⊤ := by
    intro h
    have hbot : (⊥ : Subgroup G) = ⊤ :=
      eq_top_of_sup_commutator_eq_top Fact.out (by simpa only [bot_sup_eq] using h)
    exact bot_ne_top hbot
  obtain ⟨a, ha⟩ : ∃ a : G, a ∉ commutator G := by
    by_contra h
    apply hderived
    apply top_unique
    intro a _
    by_contra ha
    exact h ⟨a, ha⟩
  exact ⟨mk G 1 ⟨a, Subgroup.mem_top _⟩, fun h => ha ((mk_eq_zero G 1 _).mp h)⟩

/-- The first claim of the paper's argument: if every nonzero first-layer vector is detected
by a triple bracket, then the second center is contained in the derived subgroup.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, Claim A, lines 974–987.
-/
theorem upperCentralSeries_two_le_commutator_of_triple_bracket
    (hsep : ∀ a : Layer G 1, a ≠ 0 → ∃ b c : Layer G 1,
      bracketLayer (by decide) (by decide)
        (bracketLayer (by decide) (by decide) a b) c ≠ 0) :
    Subgroup.upperCentralSeries G 2 ≤ commutator G := by
  intro a ha
  by_contra hnot
  have hform : mk G 1 ⟨a, Subgroup.mem_top _⟩ ≠ 0 := by
    intro h
    exact hnot ((mk_eq_zero G 1 _).mp h)
  obtain ⟨b, c, hbc⟩ := hsep _ hform
  obtain ⟨b, rfl⟩ := mk_surjective G 1 b
  obtain ⟨c, rfl⟩ := mk_surjective G 1 c
  have hab : ⁅a, (b : G)⁆ ∈ Subgroup.center G := by
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.mem_upperCentralSeries_succ_iff.mp ha) (b : G)
  have habc : ⁅⁅a, (b : G)⁆, (c : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hab) c).symm
  apply hbc
  rw [bracketLayer_mk, bracketLayer_mk, mk_eq_zero]
  change ⁅⁅a, (b : G)⁆, (c : G)⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3
  rw [habc]
  exact Subgroup.one_mem _

/-- The second claim of the paper's argument: after the second center is in the derived
subgroup, nondegeneracy of the degree-two bracket puts the center in the third lower term.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, Claim B, lines 989–1001.
-/
theorem center_le_lowerCentralSeries_two_of_bracket
    (hsecond : Subgroup.upperCentralSeries G 2 ≤ commutator G)
    (hsep : ∀ a : Layer G 2, a ≠ 0 → ∃ b : Layer G 1,
      bracketLayer (by decide) (by decide) a b ≠ 0) :
    Subgroup.center G ≤ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  intro a ha
  have ha' : a ∈ Subgroup.upperCentralSeries G 1 := by
    simpa only [Subgroup.upperCentralSeries_one] using ha
  have haD : a ∈ commutator G :=
    hsecond (Subgroup.upperCentralSeries_mono G (by decide : 1 ≤ 2) ha')
  by_contra hnot
  have hform : mk G 2 ⟨a, haD⟩ ≠ 0 := by
    intro h
    exact hnot ((mk_eq_zero G 2 _).mp h)
  obtain ⟨b, hab⟩ := hsep _ hform
  obtain ⟨b, rfl⟩ := mk_surjective G 1 b
  have hab' : ⁅a, (b : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp ha) b).symm
  apply hab
  rw [bracketLayer_mk, mk_eq_zero]
  change ⁅a, (b : G)⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3
  rw [hab']
  exact Subgroup.one_mem _

/-- The two graded separation properties give precisely the reverse coincidence of the
upper and lower central series. The automatic inclusions use exponent three.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v4.tex, `lemma:coincidence of central series`, the two-claim proof.
-/
theorem centralSeriesCoincide_of_bracket_separation
    (hone : ∀ a : Layer G 1, a ≠ 0 → ∃ b c : Layer G 1,
      bracketLayer (by decide) (by decide)
        (bracketLayer (by decide) (by decide) a b) c ≠ 0)
    (htwo : ∀ a : Layer G 2, a ≠ 0 → ∃ b : Layer G 1,
      bracketLayer (by decide) (by decide) a b ≠ 0) : CentralSeriesCoincide G := by
  have hsecond := upperCentralSeries_two_le_commutator_of_triple_bracket hone
  exact (centralSeriesCoincide_iff Fact.out).mpr
    ⟨le_antisymm (commutator_le_upperCentralSeries_two Fact.out) hsecond,
      le_antisymm (lowerCentralSeries_two_le_center Fact.out)
        (center_le_lowerCentralSeries_two_of_bracket hsecond htwo)⟩

end T3.AssociatedGraded
