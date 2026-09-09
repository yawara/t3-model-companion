/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.ModelTheory.Complexity

/-!
# Uniform finite witnesses for existential formulas

The number of witnesses needed by an existential formula is bounded independently of its
model and parameter assignment. Once these witnesses and the parameters belong to an embedded
structure, the formula is realized there. Empty structures and empty witness sets are allowed.

This strengthens an earlier finite-witness induction by Yawara Ishida:
the cardinal bound is chosen before the model.
It records the length of the existential prefix over the quantifier-free matrix, as used to
choose the bound in the necessity direction of Fact 2.6.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 234–240.
-/

@[expose] public section

universe u v w w' w''

namespace FirstOrder.Language.BoundedFormula

variable {L : Language.{u, v}} {α : Type w}

/-- An existential formula has a uniform finite witness bound. Every embedded structure
containing the witnesses realizes the formula at any preimages of its parameters.
The bound is quantified before the structure and all assignments.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 234–240.
-/
theorem IsExistential.exists_bounded_finite_witnesses {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : φ.IsExistential) :
    ∃ k : ℕ, ∀ (N : Type w') [L.Structure N] (v : α → N) (xs : Fin n → N),
      φ.Realize v xs → ∃ s : Finset N, s.card ≤ k ∧
        ∀ (P : Type w'') [L.Structure P] (g : P ↪[L] N), (s : Set N) ⊆ Set.range g →
          ∀ (v' : α → P) (xs' : Fin n → P),
            g ∘ v' = v → g ∘ xs' = xs → φ.Realize v' xs' := by
  classical
  induction hφ with
  | of_isQF hQF =>
    refine ⟨0, fun N _ v xs h => ⟨∅, by simp, ?_⟩⟩
    intro P _ g _ v' xs' hv hxs
    apply (hQF.realize_embedding g).mp
    rw [hv, hxs]
    exact h
  | ex _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    intro N _ v xs h
    obtain ⟨a, ha⟩ := realize_ex.mp h
    obtain ⟨s, hs, htransfer⟩ := hk N v (Fin.snoc xs a) ha
    refine ⟨insert a s, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hs 1), ?_⟩
    intro P _ g hsub v' xs' hv hxs
    obtain ⟨a', ha'⟩ := hsub (Finset.mem_insert_self a s)
    apply realize_ex.mpr
    refine ⟨a', htransfer P g (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      v' (Fin.snoc xs' a') hv ?_⟩
    rw [Fin.comp_snoc, hxs, ha']

/-- The formula version of the uniform finite witness theorem.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 234–240.
-/
theorem IsExistential.exists_bounded_finite_witnesses_formula {φ : L.Formula α}
    (hφ : φ.IsExistential) :
    ∃ k : ℕ, ∀ (N : Type w') [L.Structure N] (v : α → N),
      φ.Realize v → ∃ s : Finset N, s.card ≤ k ∧
        ∀ (P : Type w'') [L.Structure P] (g : P ↪[L] N), (s : Set N) ⊆ Set.range g →
          ∀ v' : α → P, g ∘ v' = v → φ.Realize v' := by
  obtain ⟨k, hk⟩ := hφ.exists_bounded_finite_witnesses
  refine ⟨k, ?_⟩
  intro N _ v h
  obtain ⟨s, hs, htransfer⟩ := hk N v default h
  exact ⟨s, hs, fun P _ g hsub v' hv =>
    htransfer P g hsub v' default hv (Subsingleton.elim _ _)⟩

end FirstOrder.Language.BoundedFormula
