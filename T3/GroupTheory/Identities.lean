/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Basic
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Nilpotent

import Mathlib.Tactic.Group

/-!
# Elementary identities in groups of exponent three

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations` (v4 Fact 2.15).

The commutator is mathlib's `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`, exactly as in the paper.
Conjugation in the paper is `a^g = g⁻¹ * a * g`; the preparatory lemmas also use conjugation
by `g * a * g⁻¹`, and the paper-facing statement substitutes inverse conjugators explicitly.

The proofs of the elementary identities and their subgroup consequences adapt earlier
formalization by Yawara Ishida.
They use only mathlib dependencies here.
The exponent-three commutator calculus follows Levi–van der Waerden (1933), pp. 154–155:
commuting conjugates give the two-Engel identity, and polarization gives cyclic triple
commutators and vanishing four-fold commutators. The final section states the product and
inverse identities in the precise order used by v4.
-/

@[expose] public section

namespace T3

open scoped commutatorElement

variable {G : Type*} [Group G]

section Basic

variable (hG : HasExponentThree G)
include hG

/-- In a group of exponent three the inverse of an element is its square.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem inv_eq_mul_self (x : G) : x⁻¹ = x * x := by
  have h := hG x
  rw [pow_succ, pow_succ, pow_one] at h
  exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h)

/-- Levi--van der Waerden 1933, p. 154, formula (1): `c * d * c = (d * c * d)⁻¹`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem mul_three_cycle (c d : G) : c * d * c = (d * c * d)⁻¹ := by
  have h := hG (c * d)
  rw [pow_succ, pow_succ, pow_one] at h
  refine eq_inv_of_mul_eq_one_left ?_
  calc c * d * c * (d * c * d) = c * d * (c * d) * (c * d) := by group
    _ = 1 := h

/-- In a group of exponent three the square of an inverse is the element itself.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem inv_mul_inv (x : G) : x⁻¹ * x⁻¹ = x := by
  have h := hG x
  rw [pow_succ, pow_succ, pow_one] at h
  rw [inv_eq_mul_self hG]
  calc x * x * (x * x) = x * x * x * x := by group
    _ = x := by rw [h, one_mul]

/-- The case `d₁ = d₂` of Levi--van der Waerden 1933, p. 155, formula (2).

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem inv_mul_conj_mul (c d : G) : c⁻¹ * d * c * d * c⁻¹ = d * c⁻¹ * d := by
  have h1 : c⁻¹ * d * c⁻¹ = (d * c⁻¹ * d)⁻¹ := mul_three_cycle hG c⁻¹ d
  have h2 : c⁻¹ * d * c⁻¹ * (c⁻¹ * d * c⁻¹) = c⁻¹ * d * (c⁻¹ * c⁻¹) * d * c⁻¹ := by group
  rw [inv_mul_inv hG] at h2
  rw [← h2, h1, inv_mul_inv hG]

/--
Levi--van der Waerden 1933, p. 154, formula (4): in a group of exponent three every element
commutes with all of its conjugates.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commute_conj (c d : G) : Commute d (c * d * c⁻¹) :=
  calc d * (c * d * c⁻¹) = c * (c⁻¹ * d * c * d * c⁻¹) := by group
    _ = c * (d * c⁻¹ * d) := by rw [inv_mul_conj_mul hG]
    _ = c * d * c⁻¹ * d := by group

/--
Any two conjugates of a fixed element commute. Equivalently, the normal closure of a single
element of a group of exponent three is abelian. This is fact (b) in the list of Burris--Lawrence
1979, p. 161.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 6.
-/
theorem commute_conj_conj (a g h : G) : Commute (g * a * g⁻¹) (h * a * h⁻¹) := by
  have h1 : Commute a (g⁻¹ * h * a * (g⁻¹ * h)⁻¹) := commute_conj hG (g⁻¹ * h) a
  have h2 := Commute.map h1 (MulAut.conj g)
  simpa [MulAut.conj_apply, mul_assoc] using h2

/-- A commutator commutes with its left argument.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commute_commutator_left (x y : G) : Commute x ⁅x, y⁆ := by
  have h1 : Commute x (y * x⁻¹ * y⁻¹) := Commute.inv_left_iff.mp (commute_conj hG y x⁻¹)
  have hx : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  rw [hx]
  exact (Commute.refl x).mul_right h1

/-- A commutator commutes with its right argument: the two-Engel law `⁅⁅x, y⁆, y⁆ = 1`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 4.
-/
theorem commutator_self_right (x y : G) : ⁅⁅x, y⁆, y⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  refine Commute.symm ?_
  rw [commutatorElement_def]
  exact (commute_conj hG x y).mul_right ((Commute.refl y).inv_right)

end Basic

section NormalClosure

variable (hG : HasExponentThree G)
include hG

/--
In a group of exponent three the normal closure of a single element is abelian. This is the
carrier on which the commutator calculus of `Identities` runs.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 6.
-/
theorem commute_of_mem_normalClosure {x a b : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G))
    (hb : b ∈ Subgroup.normalClosure ({x} : Set G)) : Commute a b := by
  induction ha, hb using Subgroup.closure_induction₂ with
  | mem u v hu hv =>
    rw [Group.mem_conjugatesOfSet_iff] at hu hv
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q, hq, hqv⟩ := hv
    rw [Set.mem_singleton_iff] at hp hq
    rw [hp] at hpu
    rw [hq] at hqv
    obtain ⟨g, hg⟩ := isConj_iff.mp hpu
    obtain ⟨h, hh⟩ := isConj_iff.mp hqv
    rw [← hg, ← hh]
    exact commute_conj_conj hG x g h
  | one_left _ _ => exact Commute.one_left _
  | one_right _ _ => exact Commute.one_right _
  | mul_left _ _ _ _ _ _ h₁ h₂ => exact h₁.mul_left h₂
  | mul_right _ _ _ _ _ _ h₁ h₂ => exact h₁.mul_right h₂
  | inv_left _ _ _ _ h => exact h.inv_left
  | inv_right _ _ _ _ h => exact h.inv_right

omit hG in
/-- The normal closure of `x` absorbs commutators of its own elements.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_mem_normalClosure {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (g : G) :
    ⁅a, g⁆ ∈ Subgroup.normalClosure ({x} : Set G) := by
  rw [commutatorElement_def]
  have h : g * a⁻¹ * g⁻¹ ∈ Subgroup.normalClosure ({x} : Set G) :=
    (Subgroup.normalClosure_normal).conj_mem _ (inv_mem ha) g
  have : a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) := by group
  rw [this]
  exact mul_mem ha h

/-- On the normal closure of `x` the map `⁅·, g⁆` is additive.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_mul_left_of_mem {x a b : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G))
    (hb : b ∈ Subgroup.normalClosure ({x} : Set G)) (g : G) :
    ⁅a * b, g⁆ = ⁅a, g⁆ * ⁅b, g⁆ := by
  have hab : Commute a ⁅b, g⁆ :=
    commute_of_mem_normalClosure hG ha (commutator_mem_normalClosure hb g)
  have hcc : Commute ⁅a, g⁆ ⁅b, g⁆ :=
    commute_of_mem_normalClosure hG (commutator_mem_normalClosure ha g)
      (commutator_mem_normalClosure hb g)
  calc ⁅a * b, g⁆ = a * ⁅b, g⁆ * a⁻¹ * ⁅a, g⁆ := commutatorElement_mul_left_eq_conj_mul a b g
    _ = ⁅b, g⁆ * a * a⁻¹ * ⁅a, g⁆ := by rw [hab.eq]
    _ = ⁅b, g⁆ * ⁅a, g⁆ := by group
    _ = ⁅a, g⁆ * ⁅b, g⁆ := hcc.eq.symm

/-- On the normal closure of `x` the map `⁅·, g⁆` sends inverses to inverses.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_inv_left_of_mem {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (g : G) :
    ⁅a⁻¹, g⁆ = ⁅a, g⁆⁻¹ := by
  have h := commutator_mul_left_of_mem hG (x := x) (inv_mem ha) ha g
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_left h.symm

omit hG in
/-- Rewriting a conjugate through a commutator, valid in any group.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem mul_commutator_inv_of_commute {c y : G} (h : Commute c (y * c * y⁻¹)) :
    c * ⁅c, y⁆⁻¹ = y * c * y⁻¹ := by
  calc c * ⁅c, y⁆⁻¹ = c * (y * c * y⁻¹) * c⁻¹ := by rw [commutatorElement_def]; group
    _ = y * c * y⁻¹ * c * c⁻¹ := by rw [h.eq]
    _ = y * c * y⁻¹ := by group

/-- In a group of exponent three, `c * ⁅c, y⁆⁻¹` is the conjugate `y * c * y⁻¹`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem mul_commutator_inv (c y : G) : c * ⁅c, y⁆⁻¹ = y * c * y⁻¹ :=
  mul_commutator_inv_of_commute (commute_conj hG y c)

/--
The composition rule for `⁅a, ·⁆`. In additive notation this is
`B (y * z) = B y + B z - B y ∘ B z`, the identity that turns the two-Engel law into a
polarization identity.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_mul_right_aux (a y z : G) :
    ⁅a, y * z⁆ = ⁅a, y⁆ * ⁅a, z⁆ * ⁅⁅a, z⁆, y⁆⁻¹ :=
  calc ⁅a, y * z⁆ = ⁅a, y⁆ * y * ⁅a, z⁆ * y⁻¹ := commutatorElement_mul_right_eq_mul_conj a y z
    _ = ⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹) := by group
    _ = ⁅a, y⁆ * (⁅a, z⁆ * ⁅⁅a, z⁆, y⁆⁻¹) := by rw [mul_commutator_inv hG]
    _ = ⁅a, y⁆ * ⁅a, z⁆ * ⁅⁅a, z⁆, y⁆⁻¹ := by group

/-- Applying `⁅·, g⁆` to a three-fold product of elements of `⟪x⟫`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_mul_left_three {x a b c : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G))
    (hb : b ∈ Subgroup.normalClosure ({x} : Set G))
    (hc : c ∈ Subgroup.normalClosure ({x} : Set G)) (g : G) :
    ⁅a * b * c, g⁆ = ⁅a, g⁆ * ⁅b, g⁆ * ⁅c, g⁆ := by
  rw [commutator_mul_left_of_mem hG (x := x) (mul_mem ha hb) hc g,
    commutator_mul_left_of_mem hG (x := x) ha hb g]

/--
The polarization of the two-Engel law, obtained by expanding `⁅⁅a, y * z⁆, y * z⁆ = 1` with the
composition rule. Writing `B g` for `⁅·, g⁆`, the five factors are, in order, `B y (B z a)`,
`B z (B y a)`, `B z (B y (B z a))`, `B y (B z (B y a))` and `B y (B z (B y (B z a)))`. This is the
identity used to obtain antisymmetry of the triple commutator.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem engel_polarization {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅a, z⁆, y⁆ * (⁅⁅a, y⁆, z⁆ * ⁅⁅⁅a, z⁆, y⁆, z⁆⁻¹)
        * (⁅⁅⁅a, y⁆, z⁆, y⁆ * ⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆⁻¹)⁻¹ = 1 := by
  have hay := commutator_mem_normalClosure ha y
  have haz := commutator_mem_normalClosure ha z
  have hazy := commutator_mem_normalClosure haz y
  have hayz := commutator_mem_normalClosure hay z
  have hazyz := commutator_mem_normalClosure hazy z
  have hw : ⁅a, y * z⁆ = ⁅a, y⁆ * ⁅a, z⁆ * ⁅⁅a, z⁆, y⁆⁻¹ := commutator_mul_right_aux hG a y z
  have hwy : ⁅⁅a, y * z⁆, y⁆ = ⁅⁅a, z⁆, y⁆ := by
    rw [hw, commutator_mul_left_three hG hay haz (inv_mem hazy) y,
      commutator_inv_left_of_mem hG hazy y, commutator_self_right hG a y,
      commutator_self_right hG ⁅a, z⁆ y, one_mul, inv_one, mul_one]
  have hwz : ⁅⁅a, y * z⁆, z⁆ = ⁅⁅a, y⁆, z⁆ * ⁅⁅⁅a, z⁆, y⁆, z⁆⁻¹ := by
    rw [hw, commutator_mul_left_three hG hay haz (inv_mem hazy) z,
      commutator_inv_left_of_mem hG hazy z, commutator_self_right hG a z, mul_one]
  have hwzy : ⁅⁅⁅a, y * z⁆, z⁆, y⁆
      = ⁅⁅⁅a, y⁆, z⁆, y⁆ * ⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆⁻¹ := by
    rw [hwz, commutator_mul_left_of_mem hG (x := x) hayz (inv_mem hazyz) y,
      commutator_inv_left_of_mem hG hazyz y]
  have key : ⁅⁅a, y * z⁆, y⁆ * ⁅⁅a, y * z⁆, z⁆ * ⁅⁅⁅a, y * z⁆, z⁆, y⁆⁻¹ = 1 := by
    rw [← commutator_mul_right_aux hG]
    exact commutator_self_right hG a (y * z)
  rw [hwy, hwzy, hwz] at key
  exact key

/-- Applying `⁅·, y⁆` to the polarization kills every term but two.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem engel_step_one {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅⁅a, y⁆, z⁆, y⁆ = ⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆ := by
  have hay := commutator_mem_normalClosure ha y
  have haz := commutator_mem_normalClosure ha z
  have hP₁ := commutator_mem_normalClosure haz y
  have hP₂ := commutator_mem_normalClosure hay z
  have hP₃ := commutator_mem_normalClosure hP₁ z
  have hP₄ := commutator_mem_normalClosure hP₂ y
  have hP₅ := commutator_mem_normalClosure hP₃ y
  have h := congrArg (fun t : G => ⁅t, y⁆) (engel_polarization hG ha y z)
  simp only [commutatorElement_one_left] at h
  rw [commutator_mul_left_of_mem hG (x := x) (mul_mem hP₁ (mul_mem hP₂ (inv_mem hP₃)))
      (inv_mem (mul_mem hP₄ (inv_mem hP₅))) y,
    commutator_mul_left_of_mem hG (x := x) hP₁ (mul_mem hP₂ (inv_mem hP₃)) y,
    commutator_mul_left_of_mem hG (x := x) hP₂ (inv_mem hP₃) y,
    commutator_inv_left_of_mem hG hP₃ y,
    commutator_inv_left_of_mem hG (mul_mem hP₄ (inv_mem hP₅)) y,
    commutator_mul_left_of_mem hG (x := x) hP₄ (inv_mem hP₅) y,
    commutator_inv_left_of_mem hG hP₅ y, commutator_self_right hG ⁅a, z⁆ y,
    commutator_self_right hG ⁅⁅a, y⁆, z⁆ y, commutator_self_right hG ⁅⁅⁅a, z⁆, y⁆, z⁆ y] at h
  simp only [one_mul, inv_one, mul_one] at h
  exact mul_inv_eq_one.mp h

/-- Instantiating the polarization at `⁅a, z⁆` kills every term but two.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem engel_step_two {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅⁅a, z⁆, y⁆, z⁆ = ⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆ := by
  have h := engel_polarization hG (commutator_mem_normalClosure ha z) y z
  rw [commutator_self_right hG a z] at h
  simp only [commutatorElement_one_left, one_mul, inv_one, mul_one] at h
  exact mul_inv_eq_one.mp h

/-- The polarization, reduced by `engel_step_one` and `engel_step_two`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem engel_step_three {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅a, z⁆, y⁆ * ⁅⁅a, y⁆, z⁆ = ⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆ := by
  have h := engel_polarization hG ha y z
  rw [engel_step_one hG ha y z, engel_step_two hG ha y z, mul_inv_cancel, inv_one, mul_one,
    ← mul_assoc] at h
  exact mul_inv_eq_one.mp h

/-- A four-fold commutator with a repeated entry is trivial.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_triple_repeat {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅⁅a, y⁆, z⁆, y⁆ = 1 := by
  have hay := commutator_mem_normalClosure ha y
  have haz := commutator_mem_normalClosure ha z
  have h : ⁅⁅⁅a, z⁆, y⁆ * ⁅⁅a, y⁆, z⁆, y⁆ = ⁅⁅⁅⁅⁅a, z⁆, y⁆, z⁆, y⁆, y⁆ :=
    congrArg (fun t : G => ⁅t, y⁆) (engel_step_three hG ha y z)
  rw [commutator_mul_left_of_mem hG (x := x) (commutator_mem_normalClosure haz y)
      (commutator_mem_normalClosure hay z) y,
    commutator_self_right hG ⁅a, z⁆ y, one_mul,
    commutator_self_right hG ⁅⁅⁅a, z⁆, y⁆, z⁆ y] at h
  exact h

/-- Antisymmetry of the triple commutator in its last two entries, for `a` in `⟪x⟫`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_triple_antisymm_of_mem {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z : G) :
    ⁅⁅a, z⁆, y⁆ * ⁅⁅a, y⁆, z⁆ = 1 :=
  (engel_step_three hG ha y z).trans
    ((engel_step_one hG ha y z).symm.trans (commutator_triple_repeat hG ha y z))

/--
Antisymmetry of the triple commutator in its last two entries. This is fact (e) in the list of
Burris--Lawrence 1979, p. 161.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_triple_antisymm (x y z : G) : ⁅⁅x, z⁆, y⁆ * ⁅⁅x, y⁆, z⁆ = 1 :=
  commutator_triple_antisymm_of_mem hG
    (Subgroup.subset_normalClosure (Set.mem_singleton x)) y z

omit hG in
/-- Cancelling two inverse pairs out of a product, used to isolate a weight-four term.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem mul_cancel_of_commute {A₁ A₂ B₁ B₂ C D : G}
    (h : A₁ * A₂ * C * (B₁ * B₂ * D) = 1) (h₁ : A₁ * B₁ = 1) (h₂ : A₂ * B₂ = 1)
    (c₁ : Commute A₁ A₂) (c₂ : Commute A₁ C) (c₃ : Commute A₂ C) : C * D = 1 := by
  rw [(mul_eq_one_iff_inv_eq.mp h₁).symm, (mul_eq_one_iff_inv_eq.mp h₂).symm] at h
  rw [← h]
  calc C * D = C * ⁅A₁, A₂⁆ * D := by rw [c₁.commutator_eq]; group
    _ = C * (A₁ * A₂ * A₁⁻¹ * A₂⁻¹) * D := by rw [commutatorElement_def]
    _ = C * A₁ * A₂ * (A₁⁻¹ * A₂⁻¹ * D) := by group
    _ = A₁ * C * A₂ * (A₁⁻¹ * A₂⁻¹ * D) := by rw [c₂.eq]
    _ = A₁ * (C * A₂) * (A₁⁻¹ * A₂⁻¹ * D) := by group
    _ = A₁ * (A₂ * C) * (A₁⁻¹ * A₂⁻¹ * D) := by rw [c₃.eq]
    _ = A₁ * A₂ * C * (A₁⁻¹ * A₂⁻¹ * D) := by group

/--
A group of exponent three has nilpotency class at most three. This is fact (a) in the list of
Burris--Lawrence 1979, p. 161.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_quadruple_of_mem {x a : G}
    (ha : a ∈ Subgroup.normalClosure ({x} : Set G)) (y z w : G) :
    ⁅⁅⁅a, w⁆, z⁆, y⁆ = 1 := by
  have hay := commutator_mem_normalClosure ha y
  have haz := commutator_mem_normalClosure ha z
  have haw := commutator_mem_normalClosure ha w
  have hazy := commutator_mem_normalClosure haz y
  have hawz := commutator_mem_normalClosure haw z
  have hQ : ⁅⁅⁅a, z⁆, y⁆, w⁆ = ⁅⁅⁅a, w⁆, z⁆, y⁆ := by
    have hzw : ⁅⁅a, z⁆, w⁆ = ⁅⁅a, w⁆, z⁆⁻¹ :=
      mul_eq_one_iff_eq_inv.mp (commutator_triple_antisymm_of_mem hG ha w z)
    have h := commutator_triple_antisymm_of_mem hG haz w y
    rw [hzw, commutator_inv_left_of_mem hG hawz y] at h
    exact mul_inv_eq_one.mp h
  have h := commutator_triple_antisymm_of_mem hG ha w (y * z)
  rw [commutator_mul_right_aux hG a y z,
    commutator_mul_left_three hG hay haz (inv_mem hazy) w,
    commutator_inv_left_of_mem hG hazy w, commutator_mul_right_aux hG ⁅a, w⁆ y z, hQ] at h
  have hcancel := mul_cancel_of_commute h
    (commutator_triple_antisymm_of_mem hG ha w y) (commutator_triple_antisymm_of_mem hG ha w z)
    (commute_of_mem_normalClosure hG (commutator_mem_normalClosure hay w)
      (commutator_mem_normalClosure haz w))
    (commute_of_mem_normalClosure hG (commutator_mem_normalClosure hay w)
      (inv_mem (commutator_mem_normalClosure hawz y)))
    (commute_of_mem_normalClosure hG (commutator_mem_normalClosure haz w)
      (inv_mem (commutator_mem_normalClosure hawz y)))
  exact (inv_mul_inv hG ⁅⁅⁅a, w⁆, z⁆, y⁆).symm.trans hcancel

/--
A group of exponent three has nilpotency class at most three: every four-fold commutator is
trivial.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 1.
-/
theorem commutator_quadruple_aux (x y z w : G) : ⁅⁅⁅x, w⁆, z⁆, y⁆ = 1 :=
  commutator_quadruple_of_mem hG (Subgroup.subset_normalClosure (Set.mem_singleton x)) y z w

/-- Antisymmetry of the triple commutator in its first two entries.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 7.
-/
theorem commutator_triple_swap (x y z : G) : ⁅⁅x, y⁆, z⁆ = ⁅⁅y, x⁆, z⁆⁻¹ := by
  have hxy : ⁅x, y⁆ ∈ Subgroup.normalClosure ({x} : Set G) :=
    commutator_mem_normalClosure (Subgroup.subset_normalClosure (Set.mem_singleton x)) y
  rw [(commutatorElement_inv x y).symm, commutator_inv_left_of_mem hG hxy z, inv_inv]

/--
The triple commutator is invariant under cyclic permutation. This is fact (c) in the list of
Burris--Lawrence 1979, p. 161.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 4.
-/
theorem commutator_triple_cyclic (x y z : G) : ⁅⁅x, y⁆, z⁆ = ⁅⁅y, z⁆, x⁆ := by
  have a23 : ∀ u v t : G, ⁅⁅u, v⁆, t⁆ = ⁅⁅u, t⁆, v⁆⁻¹ := fun u v t =>
    mul_eq_one_iff_eq_inv.mp (commutator_triple_antisymm hG u t v)
  calc ⁅⁅x, y⁆, z⁆ = ⁅⁅x, z⁆, y⁆⁻¹ := a23 x y z
    _ = (⁅⁅z, x⁆, y⁆⁻¹)⁻¹ := by rw [commutator_triple_swap hG x z y]
    _ = ⁅⁅z, x⁆, y⁆ := inv_inv _
    _ = ⁅⁅z, y⁆, x⁆⁻¹ := a23 z x y
    _ = (⁅⁅y, z⁆, x⁆⁻¹)⁻¹ := by rw [commutator_triple_swap hG z y x]
    _ = ⁅⁅y, z⁆, x⁆ := inv_inv _

/-- With class at most three, `⁅⁅x, y⁆, ·⁆` is a homomorphism.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15; proof ingredient for items 1, 4, 6 and 7.
-/
theorem commutator_commutator_mul_right (x y u v : G) :
    ⁅⁅x, y⁆, u * v⁆ = ⁅⁅x, y⁆, u⁆ * ⁅⁅x, y⁆, v⁆ := by
  rw [commutator_mul_right_aux hG ⁅x, y⁆ u v, commutator_quadruple_aux hG x u v y,
    inv_one, mul_one]

/--
Any two commutators commute. This is the second half of fact (b) in the list of Burris--Lawrence
1979, p. 161.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 3 (the derived subgroup is abelian).
-/
theorem commutator_commutator (x y z w : G) : ⁅⁅x, y⁆, ⁅z, w⁆⁆ = 1 := by
  have hxy : ⁅x, y⁆ ∈ Subgroup.normalClosure ({x} : Set G) :=
    commutator_mem_normalClosure (Subgroup.subset_normalClosure (Set.mem_singleton x)) y
  have hinv : ∀ u : G, ⁅⁅x, y⁆, u⁻¹⁆ = ⁅⁅x, y⁆, u⁆⁻¹ := by
    intro u
    have h := commutator_commutator_mul_right hG x y u u⁻¹
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    exact (mul_eq_one_iff_inv_eq.mp h.symm).symm
  have hcomm : Commute ⁅⁅x, y⁆, z⁆ ⁅⁅x, y⁆, w⁆ :=
    commute_of_mem_normalClosure hG (commutator_mem_normalClosure hxy z)
      (commutator_mem_normalClosure hxy w)
  calc ⁅⁅x, y⁆, ⁅z, w⁆⁆
      = ⁅⁅x, y⁆, z * w * z⁻¹ * w⁻¹⁆ := by rw [commutatorElement_def z w]
    _ = ⁅⁅x, y⁆, z⁆ * ⁅⁅x, y⁆, w⁆ * ⁅⁅x, y⁆, z⁆⁻¹ * ⁅⁅x, y⁆, w⁆⁻¹ := by
        rw [commutator_commutator_mul_right hG, commutator_commutator_mul_right hG,
          commutator_commutator_mul_right hG, hinv, hinv]
    _ = ⁅⁅⁅x, y⁆, z⁆, ⁅⁅x, y⁆, w⁆⁆ := (commutatorElement_def _ _).symm
    _ = 1 := hcomm.commutator_eq

end NormalClosure

section PaperStatements

variable (hG : HasExponentThree G)
include hG

/-- A triple commutator in a group of exponent three is central.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 2.
-/
theorem commutator_triple_mem_center (x y z : G) : ⁅⁅x, y⁆, z⁆ ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro w
  have h := commutator_quadruple_aux hG x w z y
  rw [commutatorElement_eq_one_iff_commute] at h
  exact h.symm.eq

/--
Commutators with a central second layer are multiplicative in the first argument on the derived
subgroup, which is what lets the previous lemma spread over `γ₃`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 2.
-/
theorem commutator_mem_center_of_mem_commutator {a : G} (ha : a ∈ commutator G) (z : G) :
    ⁅a, z⁆ ∈ Subgroup.center G := by
  induction ha using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨p, -, q, -, rfl⟩ := hu
    exact commutator_triple_mem_center hG p q z
  | one => simp
  | mul u v _ _ hu hv =>
    have h : ⁅u * v, z⁆ = ⁅v, z⁆ * ⁅u, z⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp hv u]
      group
    rw [h]
    exact Subgroup.mul_mem _ hv hu
  | inv u _ hu =>
    have hc : ⁅z, u⁆ ∈ Subgroup.center G := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hu
    have h : ⁅u⁻¹, z⁆ = ⁅z, u⁆ := by
      rw [commutatorElement_inv_left, Subgroup.mem_center_iff.mp hc u⁻¹]
      group
    rw [h]
    exact hc

/-- The third term of the lower central series of a group of exponent three is central.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 2.
-/
theorem lowerCentralSeries_two_le_center :
    (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G := by
  rw [Subgroup.lowerCentralSeries_succ]
  refine Subgroup.commutator_le.mpr fun a ha z _ => ?_
  exact commutator_mem_center_of_mem_commutator hG ha z

/-- A group of exponent three has nilpotency class at most three.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 1.
-/
theorem lowerCentralSeries_three_eq_bot : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine le_trans (lowerCentralSeries_two_le_center hG) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact Subgroup.mem_center_iff.mp ha g

/--
The derived subgroup of a group of exponent three is abelian: `⁅G', G'⁆ = 1`. This is the subgroup
form of `commutator_commutator`.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 3 (the derived subgroup is abelian).
-/
theorem commute_of_mem_commutator {a b : G} (ha : a ∈ commutator G) (hb : b ∈ commutator G) :
    Commute a b := by
  induction ha, hb using Subgroup.closure_induction₂ with
  | mem u v hu hv =>
    obtain ⟨p, -, q, -, rfl⟩ := hu
    obtain ⟨r, -, s, -, rfl⟩ := hv
    exact commutatorElement_eq_one_iff_commute.mp (commutator_commutator hG p q r s)
  | one_left _ _ => exact Commute.one_left _
  | one_right _ _ => exact Commute.one_right _
  | mul_left _ _ _ _ _ _ h₁ h₂ => exact h₁.mul_left h₂
  | mul_right _ _ _ _ _ _ h₁ h₂ => exact h₁.mul_right h₂
  | inv_left _ _ _ _ h => exact h.inv_left
  | inv_right _ _ _ _ h => exact h.inv_right

/-- The derived subgroup of a group of exponent three is commutative.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, item 3 (the derived subgroup is abelian).
-/
theorem isMulCommutative_commutator : IsMulCommutative (commutator G) :=
  ⟨⟨fun a b => Subtype.ext (commute_of_mem_commutator hG a.2 b.2)⟩⟩

/-- Every four-fold commutator is trivial, in the argument order used by the paper.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 1.
-/
theorem commutator_quadruple (a b c d : G) : ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1 :=
  commutator_quadruple_aux hG a d c b

/-- The derived subgroup lies in the second upper central subgroup.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 2.
-/
theorem commutator_le_upperCentralSeries_two :
    commutator G ≤ Subgroup.upperCentralSeries G 2 := by
  intro a ha
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro z
  rw [Subgroup.upperCentralSeries_one]
  exact commutator_mem_center_of_mem_commutator hG ha z

/-- Inverting the first argument inverts its commutator.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 5.
-/
theorem commutator_inv_left (a b : G) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ :=
  commutator_inv_left_of_mem hG (Subgroup.subset_normalClosure (Set.mem_singleton a)) b

/-- Inverting the second argument inverts its commutator.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 5.
-/
theorem commutator_inv_right (a b : G) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  rw [← commutatorElement_inv b⁻¹ a, commutator_inv_left hG, inv_inv,
    commutatorElement_inv]

/-- Two conjugates of the same element commute, using the paper's conjugation convention.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 6.
-/
theorem commutator_conjugates (a b c : G) : ⁅b⁻¹ * a * b, c⁻¹ * a * c⁆ = 1 := by
  simpa only [inv_inv] using (commute_conj_conj hG a b⁻¹ c⁻¹).commutator_eq

/-- The normal closure of a single element is an abelian group.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 6.
-/
theorem isMulCommutative_normalClosure (a : G) :
    IsMulCommutative (Subgroup.normalClosure ({a} : Set G)) :=
  ⟨⟨fun x y => Subtype.ext (commute_of_mem_normalClosure hG x.2 y.2)⟩⟩

/-- The product formula in the second argument, with the paper's triple-commutator order.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 8.
-/
theorem commutator_mul_right (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ * ⁅⁅a, b⁆, c⁆ := by
  rw [commutator_mul_right_aux hG,
    mul_eq_one_iff_inv_eq.mp (commutator_triple_antisymm hG a b c)]

/-- The product formula in the first argument, with the paper's factor and sign conventions.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 9.
-/
theorem commutator_mul_left (a b c : G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆⁻¹ := by
  rw [← commutatorElement_inv c (a * b), commutator_mul_right hG,
    mul_inv_rev, mul_inv_rev, commutatorElement_inv c b, commutatorElement_inv c a,
    commutator_triple_cyclic hG c a b]
  have hcenter : ⁅⁅a, b⁆, c⁆⁻¹ ∈ Subgroup.center G :=
    Subgroup.inv_mem _ (commutator_triple_mem_center hG a b c)
  rw [← Subgroup.mem_center_iff.mp hcenter (⁅b, c⁆ * ⁅a, c⁆)]
  rw [(commutatorElement_eq_one_iff_commute.mp (commutator_commutator hG b c a c)).eq]

open scoped Pointwise

/-- The join of two subgroups of the abelian derived subgroup is their pointwise product.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`,
v4 Fact 2.15, supporting lemma for items 10 and 11.
-/
private theorem coe_sup_of_le_commutator {A B : Subgroup G}
    (hA : A ≤ commutator G) (hB : B ≤ commutator G) :
    (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) := by
  apply Subgroup.coe_mul_of_left_le_normalizer_right
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (B : Set G))
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (commute_of_mem_commutator hG (hB hb) (hA ha)).eq

/-- The product inclusion in the second argument for arbitrary sets.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 10.
-/
theorem commutatorOfSets_mul_right (A B C : Set G) :
    (commutatorOfSets A (B * C) : Set G) ⊆
      (commutatorOfSets A B : Set G) * (commutatorOfSets A C : Set G) *
        (commutatorOfSets (commutatorOfSets A B : Set G) C : Set G) := by
  let K := commutatorOfSets A B
  let L := commutatorOfSets A C
  let P := commutatorOfSets (K : Set G) C
  have hK : K ≤ commutator G := commutatorOfSets_le_commutator A B
  have hL : L ≤ commutator G := commutatorOfSets_le_commutator A C
  have hP : P ≤ commutator G := commutatorOfSets_le_commutator (K : Set G) C
  have hproduct : (↑(K ⊔ L ⊔ P) : Set G) =
      (K : Set G) * (L : Set G) * (P : Set G) := by
    rw [coe_sup_of_le_commutator hG (sup_le hK hL) hP,
      coe_sup_of_le_commutator hG hK hL]
  change (commutatorOfSets A (B * C) : Set G) ⊆
    (K : Set G) * (L : Set G) * (P : Set G)
  rw [← hproduct]
  change commutatorOfSets A (B * C) ≤ K ⊔ L ⊔ P
  apply (K ⊔ L ⊔ P).closure_le.mpr
  rintro _ ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
  rw [commutator_mul_right hG]
  have hab : ⁅a, b⁆ ∈ K := commutator_mem_commutatorOfSets ha hb
  have hac : ⁅a, c⁆ ∈ L := commutator_mem_commutatorOfSets ha hc
  have habc : ⁅⁅a, b⁆, c⁆ ∈ P := commutator_mem_commutatorOfSets hab hc
  exact (K ⊔ L ⊔ P).mul_mem
    ((K ⊔ L ⊔ P).mul_mem ((show K ≤ K ⊔ L ⊔ P from le_trans le_sup_left le_sup_left) hab)
      ((show L ≤ K ⊔ L ⊔ P from le_trans le_sup_right le_sup_left) hac))
    ((show P ≤ K ⊔ L ⊔ P from le_sup_right) habc)

/-- The product inclusion in the first argument for arbitrary sets.

Paper-ID: preliminaries.elementary_identities
TeX: T3_modelcompanion_v4.tex, `fact:elementary equations`, v4 Fact 2.15, item 11.
-/
theorem commutatorOfSets_mul_left (A B C : Set G) :
    (commutatorOfSets (A * B) C : Set G) ⊆
      (commutatorOfSets A C : Set G) * (commutatorOfSets B C : Set G) *
        (commutatorOfSets (commutatorOfSets A B : Set G) C : Set G) := by
  let K := commutatorOfSets A C
  let L := commutatorOfSets B C
  let P := commutatorOfSets (commutatorOfSets A B : Set G) C
  have hK : K ≤ commutator G := commutatorOfSets_le_commutator A C
  have hL : L ≤ commutator G := commutatorOfSets_le_commutator B C
  have hP : P ≤ commutator G := commutatorOfSets_le_commutator _ C
  have hproduct : (↑(K ⊔ L ⊔ P) : Set G) =
      (K : Set G) * (L : Set G) * (P : Set G) := by
    rw [coe_sup_of_le_commutator hG (sup_le hK hL) hP,
      coe_sup_of_le_commutator hG hK hL]
  change (commutatorOfSets (A * B) C : Set G) ⊆
    (K : Set G) * (L : Set G) * (P : Set G)
  rw [← hproduct]
  change commutatorOfSets (A * B) C ≤ K ⊔ L ⊔ P
  apply (K ⊔ L ⊔ P).closure_le.mpr
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
  rw [commutator_mul_left hG]
  have hac : ⁅a, c⁆ ∈ K := commutator_mem_commutatorOfSets ha hc
  have hbc : ⁅b, c⁆ ∈ L := commutator_mem_commutatorOfSets hb hc
  have habc : ⁅⁅a, b⁆, c⁆ ∈ P :=
    commutator_mem_commutatorOfSets (commutator_mem_commutatorOfSets ha hb) hc
  exact (K ⊔ L ⊔ P).mul_mem
    ((K ⊔ L ⊔ P).mul_mem ((show K ≤ K ⊔ L ⊔ P from le_trans le_sup_left le_sup_left) hac)
      ((show L ≤ K ⊔ L ⊔ P from le_trans le_sup_right le_sup_left) hbc))
    ((show P ≤ K ⊔ L ⊔ P from le_sup_right) (P.inv_mem habc))

end PaperStatements

end T3
