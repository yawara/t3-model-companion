/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Collection
public import T3.GroupTheory.Free.ModelComparison

/-!
# A noncommutative second center in an exponent-three group

The free exponent-three group on two generators has trivial third lower central term:
there are no strictly increasing triples of generator indices. Its second upper central term
is therefore the whole group. The coordinate model distinguishes the commutator of its two
generators from one, so this second upper central term is not commutative.

This supplies the example asserted in item 3 of the paper's elementary identities. The
commutativity of the derived subgroup is proved in `T3.GroupTheory.Identities`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v7.tex, `fact:elementary equations`, v7 Fact 2.15, item 3.
-/

@[expose] public section

namespace T3.Free

open scoped commutatorElement

/-- The third lower central term of the free exponent-three group on two generators is trivial.
Mathlib numbers this term by `2`, whereas the paper denotes it by `γ₃`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v7.tex, `fact:elementary equations`, v7 Fact 2.15, item 3.
-/
theorem lowerCentralSeries_two_fin_two_eq_bot :
    (⊤ : Subgroup (Free (Fin 2))).lowerCentralSeries 2 = ⊥ := by
  rw [lowerCentralSeries_two_eq_increasingTripleClosure, increasingTripleClosure]
  have h : Set.range (increasingTripleCommutator (I := Fin 2)) = ∅ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      have h₁ := t.first_lt_second
      have h₂ := t.second_lt_third
      have h₃ := t.third.isLt
      simp only [Fin.lt_def] at h₁ h₂
      omega
    · simp
  rw [h, Subgroup.closure_empty]

/-- The second upper central term of the free exponent-three group on two generators is full.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v7.tex, `fact:elementary equations`, v7 Fact 2.15, item 3.
-/
theorem upperCentralSeries_two_fin_two_eq_top :
    Subgroup.upperCentralSeries (Free (Fin 2)) 2 = ⊤ :=
  Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top.mp
    lowerCentralSeries_two_fin_two_eq_bot

/-- An exponent-three group can have a noncommutative second upper central term.
The explicit example is the free exponent-three group on two generators.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v7.tex, `fact:elementary equations`, v7 Fact 2.15, item 3.
-/
theorem not_isMulCommutative_upperCentralSeries_two_fin_two :
    ¬ IsMulCommutative (Subgroup.upperCentralSeries (Free (Fin 2)) 2) := by
  intro h
  let := h
  apply commutator_of_ne_one (show (0 : Fin 2) ≠ 1 by decide)
  rw [commutatorElement_eq_one_iff_mul_comm]
  apply setLike_mul_comm (s := Subgroup.upperCentralSeries (Free (Fin 2)) 2)
  · rw [upperCentralSeries_two_fin_two_eq_top]
    exact Subgroup.mem_top _
  · rw [upperCentralSeries_two_fin_two_eq_top]
    exact Subgroup.mem_top _

end T3.Free
