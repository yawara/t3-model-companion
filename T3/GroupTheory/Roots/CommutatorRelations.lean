/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.GradedNormalClosure

/-!
# Normal forms for finitely many derived relators

In an exponent-three group, a commutator with a derived element is central and multiplicative
in its second argument. Consequently the normal closure of a finite family of derived relators
consists of products of relator powers and one commutator per relator. This is the simultaneous
normal-form step of the paper's commutator-root construction.

Paper-ID: structure.simultaneous_commutator_roots
TeX: T3_modelcompanion_v8.tex, `lemma:basic commutator root`, Claim A.
-/

@[expose] public section

open scoped commutatorElement IsMulCommutative

namespace T3.CommutatorRoots

variable {G : Type*} [Group G] [Fact (HasExponentThree G)] {n : ℕ}

local instance : IsMulCommutative (commutator G) := isMulCommutative_commutator Fact.out

/-- The commutator with a derived element is a homomorphism into the abelian derived subgroup.

Paper-ID: structure.simultaneous_commutator_roots
TeX: T3_modelcompanion_v8.tex, `lemma:basic commutator root`, Claim A.
-/
def derivedBracketHom (r : commutator G) : G →* commutator G where
  toFun h := ⟨⁅(r : G), h⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  map_one' := Subtype.ext (commutatorElement_one_right _)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(r : G), a * b⁆ = ⁅(r : G), a⁆ * ⁅(r : G), b⁆
    have hc := commutator_mem_center_of_mem_commutator Fact.out r.property b
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc ⁅(r : G), a⁆ * a * ⁅(r : G), b⁆ * a⁻¹ =
        ⁅(r : G), a⁆ * (a * ⁅(r : G), b⁆) * a⁻¹ := by group
      _ = ⁅(r : G), a⁆ * (⁅(r : G), b⁆ * a) * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hc a]
      _ = ⁅(r : G), a⁆ * ⁅(r : G), b⁆ := by group

/-- A simultaneous relator word, with an integer exponent and one commutator per relator.
Integer exponents are subsequently read modulo three in the actual second graded layer.

Paper-ID: structure.simultaneous_commutator_roots
TeX: T3_modelcompanion_v8.tex, `lemma:basic commutator root`, Claim A.
-/
noncomputable def normalWord (r : Fin n → commutator G) (m : Fin n → ℤ) (h : Fin n → G) :
    commutator G := ∏ i, r i ^ m i * derivedBracketHom (r i) (h i)

private theorem normalWord_mul (r : Fin n → commutator G) (m k : Fin n → ℤ)
    (h l : Fin n → G) :
    normalWord r (m + k) (h * l) = normalWord r m h * normalWord r k l := by
  simp only [normalWord, Pi.add_apply, Pi.mul_apply, zpow_add, map_mul,
    mul_mul_mul_comm, Finset.prod_mul_distrib]

private theorem normalWord_inv (r : Fin n → commutator G) (m : Fin n → ℤ)
    (h : Fin n → G) : normalWord r (-m) h⁻¹ = (normalWord r m h)⁻¹ := by
  rw [normalWord, normalWord, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.neg_apply, Pi.inv_apply, zpow_neg, map_inv, mul_inv_rev]
  exact mul_comm _ _

private theorem normalWord_single (r : Fin n → commutator G) (i : Fin n) (g : G) :
    (normalWord r (Pi.single i 1) (Pi.mulSingle i g⁻¹) : G) = g * r i * g⁻¹ := by
  have hword : normalWord r (Pi.single i 1) (Pi.mulSingle i g⁻¹) =
      r i * derivedBracketHom (r i) g⁻¹ := by
    rw [normalWord, Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hword]
  change (r i : G) * ⁅(r i : G), g⁻¹⁆ = g * r i * g⁻¹
  rw [commutator_inv_right Fact.out, mul_commutator_inv Fact.out]

/-- Claim A: every element of the normal closure of the whole finite relator family has a
single simultaneous product expression. No iterative adjunction is used.

Paper-ID: structure.simultaneous_commutator_roots
TeX: T3_modelcompanion_v8.tex, `lemma:basic commutator root`, Claim A.
-/
theorem exists_normalWord (r : Fin n → commutator G) {a : G}
    (ha : a ∈ Subgroup.normalClosure (Set.range fun i => (r i : G))) :
    ∃ m : Fin n → ℤ, ∃ h : Fin n → G, (normalWord r m h : G) = a := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Group.mem_conjugatesOfSet_iff.mp ha
    obtain ⟨g, rfl⟩ := isConj_iff.mp hi
    exact ⟨Pi.single i 1, Pi.mulSingle i g⁻¹, normalWord_single r i g⟩
  | one => exact ⟨0, 1, by simp [normalWord]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, h, rfl⟩ := ha
    obtain ⟨k, l, rfl⟩ := hb
    exact ⟨m + k, h * l, by rw [normalWord_mul, Subgroup.coe_mul]⟩
  | inv a _ ha =>
    obtain ⟨m, h, rfl⟩ := ha
    exact ⟨-m, h⁻¹, by rw [normalWord_inv, Subgroup.coe_inv]⟩

end T3.CommutatorRoots
