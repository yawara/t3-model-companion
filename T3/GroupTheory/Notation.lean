/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# The paper's ordinary group operations and universal constructions

These reference bridges identify the paper's commutator and conjugation conventions with
mathlib's operations, and characterize the ordinary free product and normal closure by
their universal properties. There is no exponent or finiteness assumption.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v4.tex, Notation 2.1, items 1, 3, 5 and 6, lines 147–153.
-/

@[expose] public section

open scoped commutatorElement

namespace T3

/-- Mathlib's commutator uses exactly the paper's `a * b * a⁻¹ * b⁻¹` convention.

Paper-ID: preliminaries.notation.commutator
TeX: T3_modelcompanion_v4.tex, Notation 2.1, item 1, line 147.
-/
theorem commutator_eq {G : Type*} [Group G] (a b : G) :
    ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := commutatorElement_def a b

/-- The paper's right conjugation `a^b` is mathlib's inner automorphism at `b⁻¹`.

Paper-ID: preliminaries.notation.conjugation
TeX: T3_modelcompanion_v4.tex, Notation 2.1, item 3, line 149.
-/
theorem right_conjugation_eq {G : Type*} [Group G] (a b : G) :
    MulAut.conj b⁻¹ a = b⁻¹ * a * b := by simp only [MulAut.conj_apply, inv_inv]

end T3

namespace Monoid.Coprod

/-- The ordinary free product has the universal extension property, including uniqueness.
In the group case, mathlib's coproduct is itself a group, so this is the group free product.

Paper-ID: preliminaries.notation.free_product
TeX: T3_modelcompanion_v4.tex, Notation 2.1, item 5, line 151.
-/
theorem existsUnique_lift {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
    (f : G →* K) (g : H →* K) :
    ∃! h : Monoid.Coprod G H →* K, h.comp inl = f ∧ h.comp inr = g := by
  refine ⟨lift f g, ⟨lift_comp_inl f g, lift_comp_inr f g⟩, ?_⟩
  intro h hh
  exact lift_unique hh.1 hh.2

end Monoid.Coprod

namespace Subgroup

/-- The normal closure is the actual least normal subgroup containing the prescribed set.

Paper-ID: preliminaries.notation.normal_closure
TeX: T3_modelcompanion_v4.tex, Notation 2.1, item 6, lines 152–154.
-/
theorem isLeast_normalClosure {G : Type*} [Group G] (s : Set G) :
    IsLeast {N : Subgroup G | N.Normal ∧ s ⊆ N} (normalClosure s) := by
  refine ⟨⟨inferInstance, subset_normalClosure⟩, ?_⟩
  intro N hN
  letI := hN.1
  exact normalClosure_le_normal hN.2

end Subgroup
