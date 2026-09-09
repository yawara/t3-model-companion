/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.Inductive
public import Mathlib.ModelTheory.DirectLimit

/-!
# Directed limits of models of Pi-two theories

A finite tuple in a directed limit lifts to one component. Existential formulas persist
along its canonical embedding, and induction over a universal prefix therefore proves
preservation of universal-existential sentences. Passing through an equivalent axiomatization
gives preservation for `Theory.IsPiTwo`, with no universality or finite-language assumption.

This extends an earlier argument by Yawara Ishida
from universal to Pi-two theories.
It supplies the limit-model step in the construction of existentially closed extensions.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language.DirectLimit

variable {L : Language.{u, v}} {ι : Type w'} [Preorder ι]
  {G : ι → Type w} [∀ i, L.Structure (G i)]
  (f : ∀ i j, i ≤ j → G i ↪[L] G j)
  [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] [Nonempty ι]

/-- A universal-existential formula holding at every tuple in every component holds at
every tuple of the directed limit. Existential witnesses are transported from a component.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem realize_of_isUniversalExistential :
    ∀ {n : ℕ} {φ : L.BoundedFormula Empty n}, φ.IsUniversalExistential →
      (∀ (i : ι) (xs : Fin n → G i), φ.Realize default xs) →
      ∀ xs : Fin n → DirectLimit G f, φ.Realize default xs := by
  intro n φ hφ
  induction hφ with
  | of_isExistential hE =>
    intro h xs
    obtain ⟨i, y, hy⟩ := exists_quotient_mk'_sigma_mk'_eq G f xs
    have hy' : xs = (of L ι G f i) ∘ y := hy
    subst hy'
    have hreal := hE.realize_embedding (of L ι G f i) (h i y)
    rwa [Subsingleton.elim ((of L ι G f i) ∘ (default : Empty → G i)) default] at hreal
  | all _ ih =>
    intro h xs
    rw [BoundedFormula.realize_all]
    intro a
    refine ih (fun i zs => ?_) (Fin.snoc xs a)
    have hi := h i (Fin.init zs)
    rw [BoundedFormula.realize_all] at hi
    have hlast := hi (zs (Fin.last _))
    rwa [Fin.snoc_init_self] at hlast

/-- A directed limit of nonempty models of a Pi-two theory, along embeddings, is a model
of that theory. The given axioms need not themselves be universal-existential sentences.
The index and structure universes are arbitrary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem models_of_isPiTwo {T : L.Theory} [∀ i, Nonempty (G i)] (hT : T.IsPiTwo)
    (h : ∀ i, G i ⊨ T) : DirectLimit G f ⊨ T := by
  classical
  obtain ⟨S, hS, hTS, hST⟩ := hT
  let i : ι := Classical.choice inferInstance
  letI : Nonempty (DirectLimit G f) := Nonempty.map (of L ι G f i) inferInstance
  have hmodels : ∀ i, G i ⊨ S := fun i =>
    (Theory.model_iff_of_mutual_consequence hTS hST (G i)).mp (h i)
  have hlim : DirectLimit G f ⊨ S := by
    rw [Theory.model_iff]
    intro φ hφ
    refine realize_of_isUniversalExistential f (hS φ hφ) (fun i xs => ?_) default
    letI := hmodels i
    have hi : G i ⊨ φ := Theory.realize_sentence_of_mem S hφ
    rwa [Subsingleton.elim xs default]
  exact (Theory.model_iff_of_mutual_consequence hTS hST (DirectLimit G f)).mpr hlim

end FirstOrder.Language.DirectLimit
