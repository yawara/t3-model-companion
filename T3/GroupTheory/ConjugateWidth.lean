/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Identities
public import Mathlib.Data.ZMod.Basic

/-!
# Conjugate width three in exponent-three groups

For a fixed element `a`, the commutators with left argument `a` are closed under multiplication:
`⁅a, g⁆ * ⁅a, h⁆ = ⁅a, g * h * ⁅g, h⁆⁆`. Together with the inverse and commutation identities,
this makes the paper's set `Eₐ = {a ^ k.val * ⁅a, g⁆ | k : ZMod 3, g : G}` a subgroup.
It contains every conjugate of `a` and is contained in its normal closure, hence equals that
normal closure.

The three exponent values give products of three, one, or two conjugates. Throughout this file,
a conjugate uses the paper's convention `a^g = g⁻¹ * a * g`; every factor is a conjugate of `a`
itself. The empty product is included in the final set equality.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`, v8 Proposition 3.1.
-/

@[expose] public section

namespace T3

open scoped commutatorElement

variable {G : Type*} [Group G] (hG : HasExponentThree G)

include hG

/-- A commutator in the right argument is a triple commutator, with the required cyclic order.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem commutator_commutator_right (a g h : G) : ⁅a, ⁅g, h⁆⁆ = ⁅⁅a, h⁆, g⁆ := by
  have hah : ⁅a, h⁆ ∈ Subgroup.normalClosure ({a} : Set G) :=
    commutator_mem_normalClosure (Subgroup.subset_normalClosure (Set.mem_singleton a)) h
  calc ⁅a, ⁅g, h⁆⁆ = ⁅⁅g, h⁆, a⁆⁻¹ := (commutatorElement_inv ⁅g, h⁆ a).symm
    _ = ⁅⁅h, a⁆, g⁆⁻¹ := by rw [commutator_triple_cyclic hG g h a]
    _ = ⁅⁅a, h⁆⁻¹, g⁆⁻¹ := by rw [← commutatorElement_inv a h]
    _ = (⁅⁅a, h⁆, g⁆⁻¹)⁻¹ := by rw [commutator_inv_left_of_mem hG hah g]
    _ = ⁅⁅a, h⁆, g⁆ := inv_inv _

/-- Commutators with fixed left argument are closed under multiplication by the paper’s formula.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem commutator_mul_commutator (a g h : G) : ⁅a, g⁆ * ⁅a, h⁆ = ⁅a, g * h * ⁅g, h⁆⁆ := by
  have hsplit : ⁅a, g⁆ * ⁅a, h⁆ = ⁅a, g * h⁆ * ⁅⁅a, h⁆, g⁆ := by
    rw [commutator_mul_right_aux hG a g h]; group
  rw [hsplit, commutator_mul_right_aux hG a (g * h) ⁅g, h⁆,
    commutator_commutator_right hG a g h,
    commutator_quadruple hG a h g (g * h), inv_one, mul_one]

/-- A conjugate in the paper’s convention is the element times its commutator.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem conj_eq_mul_commutator (a g : G) : g⁻¹ * a * g = a * ⁅a, g⁆ := by
  simpa only [commutator_inv_right hG, inv_inv] using (mul_commutator_inv hG a g⁻¹).symm

/-- The paper’s subgroup `Eₐ`, using exponents in `𝔽₃`.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
def principalNormalForm (a : G) : Subgroup G where
  carrier := {x | ∃ (k : ZMod 3) (g : G), x = a ^ k.val * ⁅a, g⁆}
  one_mem' := ⟨0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨k, g, rfl⟩ ⟨l, h, rfl⟩
    refine ⟨k + l, g * h * ⁅g, h⁆, ?_⟩
    have hcomm : Commute ⁅a, g⁆ (a ^ l.val) := (commute_commutator_left hG a g).symm.pow_right _
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hG a), pow_add,
      ← commutator_mul_commutator hG a g h]
    calc a ^ k.val * ⁅a, g⁆ * (a ^ l.val * ⁅a, h⁆)
        = a ^ k.val * (⁅a, g⁆ * a ^ l.val) * ⁅a, h⁆ := by group
      _ = a ^ k.val * (a ^ l.val * ⁅a, g⁆) * ⁅a, h⁆ := by rw [hcomm.eq]
      _ = a ^ k.val * a ^ l.val * (⁅a, g⁆ * ⁅a, h⁆) := by group
  inv_mem' := by
    rintro x ⟨k, g, rfl⟩
    refine ⟨-k, g⁻¹, ?_⟩
    have hpow : (a ^ k.val)⁻¹ = a ^ (-k).val := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, pow_eq_pow_mod _ (hG a), ← ZMod.val_add, neg_add_cancel]
      simp
    have hcomm : Commute ⁅a, g⁻¹⁆ (a ^ (-k).val) :=
      (commute_commutator_left hG a g⁻¹).symm.pow_right _
    rw [mul_inv_rev, ← commutator_inv_right hG, hpow, hcomm.eq]

/-- Membership in `Eₐ` is the paper’s exponent-and-commutator expression.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem mem_principalNormalForm (a x : G) : x ∈ principalNormalForm hG a ↔
    ∃ (k : ZMod 3) (g : G), x = a ^ k.val * ⁅a, g⁆ := Iff.rfl

/-- The subgroup `Eₐ` is exactly the normal closure of its defining element.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem principalNormalForm_eq_normalClosure (a : G) :
    principalNormalForm hG a = Subgroup.normalClosure ({a} : Set G) := by
  apply le_antisymm
  · rintro x ⟨k, g, rfl⟩
    have ha := Subgroup.subset_normalClosure (Set.mem_singleton a)
    exact mul_mem (pow_mem ha k.val) (commutator_mem_normalClosure ha g)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a', ha', hax⟩ := hx
    rw [Set.mem_singleton_iff] at ha'
    subst a'
    obtain ⟨g, hg⟩ := isConj_iff.mp hax
    refine ⟨1, g⁻¹, ?_⟩
    rw [← hg]
    simpa only [ZMod.val_one, pow_one, inv_inv] using conj_eq_mul_commutator hG a g⁻¹

/-- Every element of a principal normal closure has the paper’s `Eₐ` expression.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem mem_normalClosure_iff (a x : G) :
    x ∈ Subgroup.normalClosure ({a} : Set G) ↔
      ∃ (k : ZMod 3) (g : G), x = a ^ k.val * ⁅a, g⁆ := by
  rw [← principalNormalForm_eq_normalClosure hG a, mem_principalNormalForm]

/-- Every element of a principal normal closure is a product of at most three conjugates.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem exists_conjList_of_mem_normalClosure {a x : G}
    (hx : x ∈ Subgroup.normalClosure ({a} : Set G)) :
    ∃ l : List G, l.length ≤ 3 ∧ x = (l.map fun g => g⁻¹ * a * g).prod := by
  obtain ⟨k, g, rfl⟩ := (mem_normalClosure_iff hG a x).mp hx
  have ha3 : a * a * a = 1 := by
    have h3 := hG a
    rwa [pow_succ, pow_succ, pow_one] at h3
  have hconj := conj_eq_mul_commutator hG a g
  have hk := k.val_lt
  have hcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hcases with hk | hk | hk
  · refine ⟨[1, 1, g], by simp, ?_⟩
    rw [hk]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one_mul, inv_one,
      mul_one, pow_zero, hconj]
    rw [← mul_assoc, ← mul_assoc, ha3, one_mul]
  · refine ⟨[g], by simp, ?_⟩
    rw [hk]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
      hconj]
  · refine ⟨[1, g], by simp, ?_⟩
    rw [hk]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one_mul, inv_one,
      mul_one, hconj]
    rw [pow_succ, pow_one, mul_assoc]

omit hG in
/-- Every finite product of conjugates lies in the principal normal closure.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem conjList_prod_mem (a : G) (l : List G) :
    (l.map fun g => g⁻¹ * a * g).prod ∈ Subgroup.normalClosure ({a} : Set G) := by
  induction l with
  | nil => simp
  | cons g t ih =>
    simp only [List.map_cons, List.prod_cons]
    apply mul_mem _ ih
    simpa only [inv_inv] using Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton a)) g⁻¹

/-- A principal normal closure is precisely the products of at most three positive conjugates.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem normalClosure_eq_conjList (a : G) :
    (Subgroup.normalClosure ({a} : Set G) : Set G) =
      {x | ∃ l : List G, l.length ≤ 3 ∧ x = (l.map fun g => g⁻¹ * a * g).prod} := by
  ext x
  constructor
  · exact exists_conjList_of_mem_normalClosure hG
  · rintro ⟨l, _, rfl⟩
    exact conjList_prod_mem a l

/-- Every finite product of conjugates compresses to at most three positive conjugates.

Paper-ID: main.conjugate_width
TeX: T3_modelcompanion_v8.tex, `proposition:bounded number of conjugates`,
v8 Proposition 3.1. -/
theorem exists_conjList_compression (a : G) (l : List G) :
    ∃ l' : List G, l'.length ≤ 3 ∧
      (l.map fun g => g⁻¹ * a * g).prod = (l'.map fun g => g⁻¹ * a * g).prod :=
  exists_conjList_of_mem_normalClosure hG (conjList_prod_mem a l)
end T3
