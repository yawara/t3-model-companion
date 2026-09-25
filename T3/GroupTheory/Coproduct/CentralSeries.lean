/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.FreeTwoSeparation

/-!
# Coincidence of the central series after adjoining two free generators

For every nontrivial exponent-three group `G`, the actual coproduct `G ∐ F₂` has its lower
and upper central series in reverse order. The proof uses the two graded separation claims
from the paper, through the general central-series criterion. The natural copy of `G` is
strict, as follows from injectivity on the graded layers.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v9.tex, `lemma:coincidence of central series` (Lemma 4.6).
-/

@[expose] public section

namespace T3.Coproduct

variable {G : Type*} [Group G] [Fact (HasExponentThree G)] [Nontrivial G]

/-- Adjoining two free generators makes the upper and lower central series coincide in
reverse order. Both graded separation claims apply to arbitrary nontrivial `G`.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v9.tex, `lemma:coincidence of central series` (Lemma 4.6).
-/
theorem centralSeriesCoincide_freeTwo : CentralSeriesCoincide (Coproduct G (Free (Fin 2))) :=
  AssociatedGraded.centralSeriesCoincide_of_bracket_separation
    FreeTwoSeparation.exists_triple_bracket_ne_zero FreeTwoSeparation.exists_bracket_ne_zero

/-- The natural copy of `G` in `G ∐ F₂` is strict, and the latter group has coincident
central series. This is the full statement of the paper's stabilization lemma.

Paper-ID: structure.free_two_stabilization
TeX: T3_modelcompanion_v9.tex, `lemma:coincidence of central series` (Lemma 4.6).
-/
theorem freeTwo_stabilization :
    IsStrict (inl (G := G) (H := Free (Fin 2))).range ∧
      CentralSeriesCoincide (Coproduct G (Free (Fin 2))) :=
  ⟨isStrict_inl, centralSeriesCoincide_freeTwo⟩

end T3.Coproduct
