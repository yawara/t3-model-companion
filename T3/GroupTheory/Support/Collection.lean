/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Nilpotent

/-!
# Collecting cross commutators along a generating list

In a group with central derived subgroup, every element of the join of two subgroups
collects into one element of each subgroup and a cross-commutator product indexed by a fixed
finite generating list of the first subgroup. Closure induction extends the single-generator
calculation to all first-factor elements; listing the entire subgroup is unnecessary.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, lines 760–771.
-/

@[expose] public section

namespace T3.Support

open scoped commutatorElement

variable {Q : Type*} [Group Q]

/-! ### Bilinearity of the commutator when the derived subgroup is central -/

section ClassTwo

variable (hQ : commutator Q ≤ Subgroup.center Q)
include hQ

/-- Every commutator is central. -/
theorem commutator_mem_center_of_le (x y : Q) : ⁅x, y⁆ ∈ Subgroup.center Q :=
  hQ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

/-- The commutator is multiplicative in its first argument. -/
theorem commutator_mul_left_of_le (a b c : Q) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hb : a * ⁅b, c⁆ = ⁅b, c⁆ * a :=
    Subgroup.mem_center_iff.mp (commutator_mem_center_of_le hQ b c) a
  have ha : ⁅b, c⁆ * ⁅a, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ :=
    Subgroup.mem_center_iff.mp (commutator_mem_center_of_le hQ a c) ⁅b, c⁆
  calc ⁅a * b, c⁆ = a * ⁅b, c⁆ * (c * a⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅b, c⁆ * a * (c * a⁻¹ * c⁻¹) := by rw [hb]
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅a, c⁆ * ⁅b, c⁆ := ha

/-- The commutator is multiplicative in its second argument. -/
theorem commutator_mul_right_of_le (a b c : Q) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hcomm : ⁅a, c⁆ * ⁅a, b⁆ = ⁅a, b⁆ * ⁅a, c⁆ :=
    Subgroup.mem_center_iff.mp (commutator_mem_center_of_le hQ a b) ⁅a, c⁆
  calc ⁅a, b * c⁆ = ⁅b * c, a⁆⁻¹ := (commutatorElement_inv (b * c) a).symm
    _ = (⁅b, a⁆ * ⁅c, a⁆)⁻¹ := by rw [commutator_mul_left_of_le hQ]
    _ = ⁅c, a⁆⁻¹ * ⁅b, a⁆⁻¹ := mul_inv_rev _ _
    _ = ⁅a, c⁆ * ⁅a, b⁆ := by rw [commutatorElement_inv, commutatorElement_inv]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := hcomm

/-- The commutator inverts in its second argument. -/
theorem commutator_inv_right_of_le (a b : Q) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have h := commutator_mul_right_of_le hQ a b b⁻¹
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

end ClassTwo

/-! ### The collected product of cross commutators -/

/-- The collected product `∏ ⁅x, m x⁆` along a list of first arguments. -/
def crossList (m : Q → Q) : List Q → Q
  | [] => 1
  | x :: t => ⁅x, m x⁆ * crossList m t

@[simp]
theorem crossList_nil (m : Q → Q) : crossList m ([] : List Q) = 1 := rfl

@[simp]
theorem crossList_cons (m : Q → Q) (x : Q) (t : List Q) :
    crossList m (x :: t) = ⁅x, m x⁆ * crossList m t := rfl

/-- A collected product with trivial second arguments is trivial. -/
theorem crossList_eq_one_of_forall {m : Q → Q} {l : List Q} (h : ∀ z ∈ l, m z = 1) :
    crossList m l = 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [crossList_cons, h x List.mem_cons_self, commutatorElement_one_right, one_mul]
      exact ih fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem crossList_one (l : List Q) : crossList (fun _ : Q => (1 : Q)) l = 1 :=
  crossList_eq_one_of_forall fun _ _ => rfl

/-- On a duplicate-free list, a single cross commutator is a collected product. -/
theorem crossList_single [DecidableEq Q] {β μ : Q} {l : List Q} (hnd : l.Nodup) (hβ : β ∈ l) :
    crossList (fun x => if x = β then μ else 1) l = ⁅β, μ⁆ := by
  induction l with
  | nil => exact absurd hβ List.not_mem_nil
  | cons x t ih =>
      rw [List.nodup_cons] at hnd
      rw [crossList_cons]
      rcases List.mem_cons.mp hβ with hx | hx
      · subst hx
        have hzero : crossList (fun z => if z = β then μ else 1) t = 1 :=
          crossList_eq_one_of_forall fun z hz =>
            ite_eq_right fun hzb => hnd.1 (by rw [← hzb]; exact hz)
        rw [ite_eq_left rfl, hzero, mul_one]
      · have hxne : x ≠ β := fun h => hnd.1 (h ▸ hx)
        rw [ite_eq_right hxne, commutatorElement_one_right, one_mul, ih hnd.2 hx]

/-- A collected product maps to a collected product. -/
theorem map_crossList {G H : Type*} [Group G] [Group H] (φ : G →* H) (m : G → G) (m' : H → H)
    (l : List G) (h : ∀ y ∈ l, φ (m y) = m' (φ y)) :
    φ (crossList m l) = crossList m' (l.map φ) := by
  induction l with
  | nil => rw [List.map_nil, crossList_nil, crossList_nil, map_one]
  | cons x t ih =>
      rw [crossList_cons, map_mul, map_commutatorElement, h x List.mem_cons_self,
        ih fun y hy => h y (List.mem_cons_of_mem _ hy), List.map_cons, crossList_cons]

section CrossLemmas

variable (hQ : commutator Q ≤ Subgroup.center Q)
include hQ

theorem crossList_mem_center (m : Q → Q) (l : List Q) : crossList m l ∈ Subgroup.center Q := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons x t ih => exact Subgroup.mul_mem _ (commutator_mem_center_of_le hQ x (m x)) ih

theorem crossList_mul (m m' : Q → Q) (l : List Q) :
    crossList m l * crossList m' l = crossList (fun x => m x * m' x) l := by
  induction l with
  | nil => rw [crossList_nil, crossList_nil, crossList_nil, mul_one]
  | cons x t ih =>
      have hcen : crossList m t * ⁅x, m' x⁆ = ⁅x, m' x⁆ * crossList m t :=
        Subgroup.mem_center_iff.mp (commutator_mem_center_of_le hQ x (m' x))
          (crossList m t)
      calc ⁅x, m x⁆ * crossList m t * (⁅x, m' x⁆ * crossList m' t)
          = ⁅x, m x⁆ * (crossList m t * ⁅x, m' x⁆) * crossList m' t := by group
        _ = ⁅x, m x⁆ * (⁅x, m' x⁆ * crossList m t) * crossList m' t := by rw [hcen]
        _ = ⁅x, m x⁆ * ⁅x, m' x⁆ * (crossList m t * crossList m' t) := by group
        _ = ⁅x, m x * m' x⁆ * crossList (fun y => m y * m' y) t := by
              rw [commutator_mul_right_of_le hQ, ih]

theorem crossList_inv (m : Q → Q) (l : List Q) :
    (crossList m l)⁻¹ = crossList (fun x => (m x)⁻¹) l := by
  have h := crossList_mul hQ m (fun x => (m x)⁻¹) l
  rw [show (fun x => m x * (m x)⁻¹) = fun _ : Q => (1 : Q) from
      funext fun x => mul_inv_cancel _, crossList_one] at h
  exact inv_eq_of_mul_eq_one_right h

/-! ### The collection -/

/-- A generating list of the first factor suffices to index the cross commutators in
an expression for every element of a group with central derived subgroup.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, lines 764–771.
-/
theorem exists_crossList_normalForm
    {BB MM : Subgroup Q} (hgen : BB ⊔ MM = ⊤) {l : List Q} (hnd : l.Nodup)
    (hl : Subgroup.closure {x | x ∈ l} = BB) (u : Q) :
    ∃ β ∈ BB, ∃ μ ∈ MM, ∃ m : Q → Q, (∀ x, m x ∈ MM) ∧ u = β * μ * crossList m l := by
  classical
  have hcomm : ∀ β ∈ BB, ∀ μ ∈ MM,
      ∃ m : Q → Q, (∀ x, m x ∈ MM) ∧ ⁅β, μ⁆ = crossList m l := by
    intro β hβ
    rw [← hl] at hβ
    induction hβ using Subgroup.closure_induction with
    | mem β hβ =>
      intro μ hμ
      refine ⟨fun x => if x = β then μ else 1, fun x => ?_, ?_⟩
      · dsimp only
        split
        · exact hμ
        · exact Subgroup.one_mem _
      · exact (crossList_single hnd hβ).symm
    | one =>
      intro μ _
      exact ⟨fun _ => 1, fun _ => Subgroup.one_mem _, by
        rw [commutatorElement_one_left, crossList_one]⟩
    | mul β β' _ _ ih ih' =>
      intro μ hμ
      obtain ⟨m, hm, heq⟩ := ih μ hμ
      obtain ⟨m', hm', heq'⟩ := ih' μ hμ
      exact ⟨fun x => m x * m' x, fun x => MM.mul_mem (hm x) (hm' x), by
        rw [commutator_mul_left_of_le hQ, heq, heq', crossList_mul hQ]⟩
    | inv β _ ih =>
      intro μ hμ
      obtain ⟨m, hm, heq⟩ := ih μ hμ
      refine ⟨fun x => (m x)⁻¹, fun x => MM.inv_mem (hm x), ?_⟩
      have hinv : ⁅β⁻¹, μ⁆ = ⁅β, μ⁆⁻¹ := by
        have h := commutator_mul_left_of_le hQ β β⁻¹ μ
        rw [mul_inv_cancel, commutatorElement_one_left] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      rw [hinv, heq, crossList_inv hQ]
  have hcen : ∀ (m : Q → Q) (y : Q), crossList m l * y = y * crossList m l := fun m y =>
    (Subgroup.mem_center_iff.mp (crossList_mem_center hQ m l) y).symm
  have hceninv : ∀ (m : Q → Q) (y : Q), (crossList m l)⁻¹ * y = y * (crossList m l)⁻¹ :=
    fun m y => (Subgroup.mem_center_iff.mp
      (Subgroup.inv_mem _ (crossList_mem_center hQ m l)) y).symm
  let T : Subgroup Q :=
    { carrier := {u | ∃ β ∈ BB, ∃ μ ∈ MM, ∃ m : Q → Q,
        (∀ x, m x ∈ MM) ∧ u = β * μ * crossList m l}
      one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, fun _ => 1,
        fun _ => Subgroup.one_mem _, by rw [crossList_one, mul_one, mul_one]⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨β₁, hβ₁, μ₁, hμ₁, m₁, hm₁, rfl⟩ ⟨β₂, hβ₂, μ₂, hμ₂, m₂, hm₂, rfl⟩
        obtain ⟨m₃, hm₃, hm₃eq⟩ := hcomm β₂ hβ₂ μ₁ hμ₁
        refine ⟨β₁ * β₂, Subgroup.mul_mem _ hβ₁ hβ₂, μ₁ * μ₂, Subgroup.mul_mem _ hμ₁ hμ₂,
          fun x => (m₃ x)⁻¹ * m₁ x * m₂ x,
          fun x => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hm₃ x))
            (hm₁ x)) (hm₂ x), ?_⟩
        have hswap : μ₁ * β₂ = ⁅μ₁, β₂⁆ * (β₂ * μ₁) := by
          rw [commutatorElement_def]; group
        have hinv : ⁅μ₁, β₂⁆ = (crossList m₃ l)⁻¹ := by
          rw [← commutatorElement_inv, hm₃eq]
        calc β₁ * μ₁ * crossList m₁ l * (β₂ * μ₂ * crossList m₂ l)
            = β₁ * μ₁ * (crossList m₁ l * (β₂ * μ₂)) * crossList m₂ l := by group
          _ = β₁ * μ₁ * (β₂ * μ₂ * crossList m₁ l) * crossList m₂ l := by rw [hcen]
          _ = β₁ * (μ₁ * β₂) * μ₂ * (crossList m₁ l * crossList m₂ l) := by group
          _ = β₁ * ((crossList m₃ l)⁻¹ * (β₂ * μ₁)) * μ₂ *
                (crossList m₁ l * crossList m₂ l) := by rw [hswap, hinv]
          _ = β₁ * (β₂ * μ₁ * (crossList m₃ l)⁻¹) * μ₂ *
                (crossList m₁ l * crossList m₂ l) := by rw [hceninv]
          _ = β₁ * β₂ * μ₁ * ((crossList m₃ l)⁻¹ * μ₂) *
                (crossList m₁ l * crossList m₂ l) := by group
          _ = β₁ * β₂ * μ₁ * (μ₂ * (crossList m₃ l)⁻¹) *
                (crossList m₁ l * crossList m₂ l) := by rw [hceninv]
          _ = β₁ * β₂ * (μ₁ * μ₂) *
                ((crossList m₃ l)⁻¹ * crossList m₁ l * crossList m₂ l) := by group
          _ = β₁ * β₂ * (μ₁ * μ₂) * crossList (fun x => (m₃ x)⁻¹ * m₁ x * m₂ x) l := by
                rw [crossList_inv hQ, crossList_mul hQ, crossList_mul hQ]
      inv_mem' := by
        rintro u ⟨β, hβ, μ, hμ, m, hm, rfl⟩
        obtain ⟨m₃, hm₃, hm₃eq⟩ := hcomm β⁻¹ (Subgroup.inv_mem _ hβ) μ⁻¹ (Subgroup.inv_mem _ hμ)
        refine ⟨β⁻¹, Subgroup.inv_mem _ hβ, μ⁻¹, Subgroup.inv_mem _ hμ,
          fun x => (m x)⁻¹ * (m₃ x)⁻¹,
          fun x => Subgroup.mul_mem _ (Subgroup.inv_mem _ (hm x))
            (Subgroup.inv_mem _ (hm₃ x)), ?_⟩
        have hswap : μ⁻¹ * β⁻¹ = ⁅μ⁻¹, β⁻¹⁆ * (β⁻¹ * μ⁻¹) := by
          rw [commutatorElement_def]; group
        have hinv : ⁅μ⁻¹, β⁻¹⁆ = (crossList m₃ l)⁻¹ := by
          rw [← commutatorElement_inv, hm₃eq]
        calc (β * μ * crossList m l)⁻¹
            = (crossList m l)⁻¹ * (μ⁻¹ * β⁻¹) := by group
          _ = (crossList m l)⁻¹ * ((crossList m₃ l)⁻¹ * (β⁻¹ * μ⁻¹)) := by rw [hswap, hinv]
          _ = (crossList m l)⁻¹ * (β⁻¹ * μ⁻¹ * (crossList m₃ l)⁻¹) := by
                rw [hceninv m₃ (β⁻¹ * μ⁻¹)]
          _ = (crossList m l)⁻¹ * (β⁻¹ * μ⁻¹) * (crossList m₃ l)⁻¹ := by rw [← mul_assoc]
          _ = β⁻¹ * μ⁻¹ * (crossList m l)⁻¹ * (crossList m₃ l)⁻¹ := by
                rw [hceninv m (β⁻¹ * μ⁻¹)]
          _ = β⁻¹ * μ⁻¹ * ((crossList m l)⁻¹ * (crossList m₃ l)⁻¹) := by group
          _ = β⁻¹ * μ⁻¹ * crossList (fun x => (m x)⁻¹ * (m₃ x)⁻¹) l := by
                rw [crossList_inv hQ m, crossList_inv hQ m₃, crossList_mul hQ] }
  have hBB : BB ≤ T := fun β hβ =>
    ⟨β, hβ, 1, Subgroup.one_mem _, fun _ => 1, fun _ => Subgroup.one_mem _, by
      rw [crossList_one, mul_one, mul_one]⟩
  have hMM : MM ≤ T := fun μ hμ =>
    ⟨1, Subgroup.one_mem _, μ, hμ, fun _ => 1, fun _ => Subgroup.one_mem _, by
      rw [crossList_one, mul_one, one_mul]⟩
  exact (hgen ▸ sup_le hBB hMM) (Subgroup.mem_top u)

end CrossLemmas

end T3.Support
