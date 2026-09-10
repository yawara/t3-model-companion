/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded.Bracket
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Normal closures in the derived subgroup and their graded images

For a subgroup `K` of the derived subgroup, its normal closure is `K [K, G]`.
The commutator factor lies in the central third term. This gives the paper's degree-two
and degree-three formulas without splitting a nonhomogeneous relation into its components.

The graded statements use the actual ambient layers and mathlib's bilinear image of subspaces.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, `lemma:gr of normal closure`, lines 802–840.
-/

@[expose] public section

open scoped commutatorElement

namespace T3

variable {G : Type*} [Group G]

/-- Commutators of a derived subgroup with the ambient group lie in the third central term.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem commutator_top_le_term_three {K : Subgroup G} (hK : K ≤ commutator G) :
    ⁅K, (⊤ : Subgroup G)⁆ ≤ AssociatedGraded.term G 3 := by
  simpa [AssociatedGraded.term, Subgroup.lowerCentralSeries_succ, commutator_def,
    Subgroup.commutator_comm] using Subgroup.commutator_mono hK (le_refl (⊤ : Subgroup G))

/-- The commutator factor of a derived subgroup is central and hence normal.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem commutator_top_normal (hG : HasExponentThree G) {K : Subgroup G}
    (hK : K ≤ commutator G) : Subgroup.Normal ⁅K, (⊤ : Subgroup G)⁆ := by
  have hcen := (commutator_top_le_term_three hK).trans (lowerCentralSeries_two_le_center hG)
  constructor
  intro c hc g
  have hcomm := Subgroup.mem_center_iff.mp (hcen hc) g
  rw [show g * c * g⁻¹ = c by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]]
  exact hc

/-- The normal closure of a subgroup of the derived subgroup adjoins its ambient commutators.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 1, `lemma:gr of normal closure`.
-/
theorem normalClosure_eq_sup_commutator (hG : HasExponentThree G) {K : Subgroup G}
    (hK : K ≤ commutator G) :
    Subgroup.normalClosure (K : Set G) = K ⊔ ⁅K, (⊤ : Subgroup G)⁆ := by
  have hcen : ⁅K, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G :=
    (commutator_top_le_term_three hK).trans (lowerCentralSeries_two_le_center hG)
  letI := commutator_top_normal hG hK
  refine le_antisymm ?_ ?_
  · haveI hsupN : Subgroup.Normal (K ⊔ ⁅K, (⊤ : Subgroup G)⁆) := by
      constructor
      intro n hn g
      rw [← SetLike.mem_coe, Subgroup.mul_normal] at hn
      obtain ⟨k, hk, c, hc, rfl⟩ := hn
      have hstep : g * (k * c) * g⁻¹ = ⁅g, k⁆ * k * c := by
        have hcomm : g⁻¹ * c = c * g⁻¹ := Subgroup.mem_center_iff.mp (hcen hc) g⁻¹
        calc g * (k * c) * g⁻¹ = g * k * (c * g⁻¹) := by group
          _ = g * k * (g⁻¹ * c) := by rw [hcomm]
          _ = ⁅g, k⁆ * k * c := by rw [commutatorElement_def]; group
      rw [hstep]
      have hgk : ⁅g, k⁆ ∈ ⁅K, (⊤ : Subgroup G)⁆ := by
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _
          (Subgroup.commutator_mem_commutator hk (Subgroup.mem_top g))
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (SetLike.le_def.mp le_sup_right hgk)
          (SetLike.le_def.mp le_sup_left hk))
        (SetLike.le_def.mp le_sup_right hc)
    exact Subgroup.normalClosure_le_normal fun x hx => SetLike.le_def.mp le_sup_left hx
  · refine sup_le Subgroup.le_normalClosure
      (Subgroup.commutator_le.mpr fun k hk z _ => ?_)
    have h1 : k ∈ Subgroup.normalClosure (K : Set G) := Subgroup.subset_normalClosure hk
    have h2 : z * k⁻¹ * z⁻¹ ∈ Subgroup.normalClosure (K : Set G) :=
      Subgroup.normalClosure_normal.conj_mem _ (Subgroup.inv_mem _ h1) z
    have hsplit : ⁅k, z⁆ = k * (z * k⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hsplit]
    exact Subgroup.mul_mem _ h1 h2

/-- Every element of the normal closure is an actual product of an element of `K`
and an element of its commutator factor.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 1, `lemma:gr of normal closure`.
-/
theorem mem_normalClosure_iff_mul_commutator (hG : HasExponentThree G) {K : Subgroup G}
    (hK : K ≤ commutator G) (a : G) :
    a ∈ Subgroup.normalClosure (K : Set G) ↔
      ∃ k ∈ K, ∃ p ∈ ⁅K, (⊤ : Subgroup G)⁆, k * p = a := by
  letI := commutator_top_normal hG hK
  rw [normalClosure_eq_sup_commutator hG hK, ← SetLike.mem_coe, Subgroup.mul_normal]
  rfl

/-- The normal closure of a subgroup of the derived subgroup remains in the derived subgroup.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 1, `lemma:gr of normal closure`.
-/
theorem normalClosure_le_commutator {K : Subgroup G} (hK : K ≤ commutator G) :
    Subgroup.normalClosure (K : Set G) ≤ commutator G :=
  Subgroup.normalClosure_le_normal hK

namespace AssociatedGraded

/-- The initial form of the identity is zero.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
@[simp]
theorem mk_one (n : ℕ) : mk G n 1 = 0 :=
  (mk_eq_zero G n 1).mpr (Subgroup.one_mem _)

/-- Inverting a representative negates its initial form.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
@[simp]
theorem mk_inv (n : ℕ) (x : term G n) : mk G n x⁻¹ = -mk G n x := rfl

variable [Fact (HasExponentThree G)]

/-- Ambient graded images are monotone in the subgroup.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem subgroupImage_mono {A B : Subgroup G} (h : A ≤ B) (n : ℕ) :
    subgroupImage A n ≤ subgroupImage B n := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage A n x).mp hx
  exact (mem_subgroupImage B n _).mpr ⟨a, h ha, rfl⟩

/-- Intersecting with the ambient term does not change its degree image.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem subgroupImage_inf_term (K : Subgroup G) (n : ℕ) :
    subgroupImage (K ⊓ term G n) n = subgroupImage K n := by
  apply le_antisymm (subgroupImage_mono inf_le_left n)
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage K n x).mp hx
  exact (mem_subgroupImage _ n _).mpr ⟨a, ⟨ha, a.property⟩, rfl⟩

/-- A subgroup in the next central term has zero image in the current degree.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem subgroupImage_eq_bot_of_le {K : Subgroup G} (n : ℕ)
    (hK : K ≤ (⊤ : Subgroup G).lowerCentralSeries n) : subgroupImage K n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_subgroupImage K n x).mp hx
  exact (mk_eq_zero G n a).mpr (hK ha)

/-- If both subgroups lie in the current term, taking their join adds their initial forms.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, supporting v4 Lemma 4.2, `lemma:gr of normal closure`.
-/
theorem subgroupImage_sup_of_le (A B : Subgroup G) (n : ℕ)
    (hA : A ≤ term G n) (hB : B ≤ term G n) :
    subgroupImage (A ⊔ B) n = subgroupImage A n ⊔ subgroupImage B n := by
  apply le_antisymm ?_ (sup_le (subgroupImage_mono le_sup_left n)
    (subgroupImage_mono le_sup_right n))
  intro x hx
  obtain ⟨⟨a, ha⟩, hab, rfl⟩ := (mem_subgroupImage _ n x).mp hx
  clear hx
  change a ∈ A ⊔ B at hab
  rw [Subgroup.sup_eq_closure] at hab
  revert ha
  induction hab using Subgroup.closure_induction with
  | mem a ha =>
      intro hat
      rcases ha with ha | ha
      · exact (show subgroupImage A n ≤ _ from le_sup_left)
          ((mem_subgroupImage A n _).mpr ⟨⟨a, hA ha⟩, ha, rfl⟩)
      · exact (show subgroupImage B n ≤ _ from le_sup_right)
          ((mem_subgroupImage B n _).mpr ⟨⟨a, hB ha⟩, ha, rfl⟩)
  | one =>
      intro h
      change mk G n 1 ∈ _
      rw [mk_one]
      exact (subgroupImage A n ⊔ subgroupImage B n).zero_mem
  | mul a b ha hb iha ihb =>
      intro h
      have hat : a ∈ term G n := (sup_le hA hB) (by rwa [Subgroup.sup_eq_closure])
      have hbt : b ∈ term G n := (sup_le hA hB) (by rwa [Subgroup.sup_eq_closure])
      exact (subgroupImage A n ⊔ subgroupImage B n).add_mem (iha hat) (ihb hbt)
  | inv a ha iha =>
      intro h
      have hat : a ∈ term G n := (sup_le hA hB) (by rwa [Subgroup.sup_eq_closure])
      exact (subgroupImage A n ⊔ subgroupImage B n).neg_mem (iha hat)

/-- The third-degree image of the commutator factor is the bilinear bracket image.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 3, `lemma:gr of normal closure`.
-/
theorem subgroupImage_commutator_top {K : Subgroup G} (hK : K ≤ commutator G) :
    subgroupImage ⁅K, (⊤ : Subgroup G)⁆ 3 =
      Submodule.map₂ (bracketLayer (i := 2) (j := 1) (by decide) (by decide))
        (subgroupImage K 2) ⊤ := by
  have hP := commutator_top_le_term_three hK
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨a, ha⟩, hab, rfl⟩ := (mem_subgroupImage _ 3 x).mp hx
    clear hx
    change a ∈ ⁅K, (⊤ : Subgroup G)⁆ at hab
    rw [Subgroup.commutator_def] at hab
    revert ha
    induction hab using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨k, hk, g, _, rfl⟩ := ha
        intro h
        have hk2 : k ∈ term G 2 := hK hk
        exact Submodule.apply_mem_map₂ _
          ((mem_subgroupImage K 2 _).mpr ⟨⟨k, hk2⟩, hk, rfl⟩)
          (show mk G 1 ⟨g, Subgroup.mem_top g⟩ ∈ (⊤ : Submodule (ZMod 3) (Layer G 1))
            from Submodule.mem_top)
    | one =>
        intro h
        change mk G 3 1 ∈ _
        rw [mk_one]
        exact Submodule.zero_mem _
    | mul a b ha hb iha ihb =>
        intro h
        exact Submodule.add_mem _ (iha (hP ha)) (ihb (hP hb))
    | inv a ha iha =>
        intro h
        exact Submodule.neg_mem _ (iha (hP ha))
  · apply Submodule.map₂_le.mpr
    intro x hx y _
    obtain ⟨x, hxK, rfl⟩ := (mem_subgroupImage K 2 x).mp hx
    obtain ⟨y, rfl⟩ := mk_surjective G 1 y
    exact (mem_subgroupImage _ 3 _).mpr
      ⟨termCommutator (by decide) (by decide) x y,
        Subgroup.commutator_mem_commutator hxK (Subgroup.mem_top _), rfl⟩

/-- Normal closure leaves the degree-two ambient image unchanged.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 2, `lemma:gr of normal closure`.
-/
theorem subgroupImage_normalClosure_two {K : Subgroup G} (hK : K ≤ commutator G) :
    subgroupImage (Subgroup.normalClosure (K : Set G)) 2 = subgroupImage K 2 := by
  rw [normalClosure_eq_sup_commutator Fact.out hK,
    subgroupImage_sup_of_le K ⁅K, (⊤ : Subgroup G)⁆ 2 hK
      ((commutator_top_le_term_three hK).trans
        ((⊤ : Subgroup G).lowerCentralSeries_antitone (by decide))),
    subgroupImage_eq_bot_of_le 2 (commutator_top_le_term_three hK), sup_bot_eq]

/-- The normal closure's intersection with the third term retains the whole commutator factor.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2 proof of item 3, `lemma:gr of normal closure`.
-/
theorem normalClosure_inf_term_three {K : Subgroup G} (hK : K ≤ commutator G) :
    Subgroup.normalClosure (K : Set G) ⊓ term G 3 =
      (K ⊓ term G 3) ⊔ ⁅K, (⊤ : Subgroup G)⁆ := by
  have hP := commutator_top_le_term_three hK
  letI := commutator_top_normal (Fact.out (p := HasExponentThree G)) hK
  rw [normalClosure_eq_sup_commutator Fact.out hK]
  apply le_antisymm
  · rintro a ⟨ha, ha3⟩
    change a ∈ K ⊔ ⁅K, (⊤ : Subgroup G)⁆ at ha
    change a ∈ term G 3 at ha3
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at ha
    obtain ⟨k, hk, p, hp, rfl⟩ := ha
    have hk3 : k ∈ term G 3 := by
      simpa only [mul_inv_cancel_right] using (term G 3).mul_mem ha3
        ((term G 3).inv_mem (hP hp))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hk, hk3⟩) (Subgroup.mem_sup_right hp)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hP)

/-- The third-degree image of the normal closure adds precisely the bracket directions.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, item 3, `lemma:gr of normal closure`.
-/
theorem subgroupImage_normalClosure_three {K : Subgroup G} (hK : K ≤ commutator G) :
    subgroupImage (Subgroup.normalClosure (K : Set G)) 3 =
      subgroupImage K 3 ⊔ Submodule.map₂
        (bracketLayer (i := 2) (j := 1) (by decide) (by decide)) (subgroupImage K 2) ⊤ := by
  rw [← subgroupImage_inf_term (Subgroup.normalClosure (K : Set G)) 3,
    normalClosure_inf_term_three hK,
    subgroupImage_sup_of_le (K ⊓ term G 3) ⁅K, (⊤ : Subgroup G)⁆ 3 inf_le_right
      (commutator_top_le_term_three hK),
    subgroupImage_inf_term, subgroupImage_commutator_top hK]

/-- The degree-one image of the normal closure is zero.

Paper-ID: structure.normal_closure_graded
TeX: T3_modelcompanion_v4.tex, v4 Lemma 4.2, used in Proposition 4.3,
`lemma:gr of normal closure`.
-/
theorem subgroupImage_normalClosure_one {K : Subgroup G} (hK : K ≤ commutator G) :
    subgroupImage (Subgroup.normalClosure (K : Set G)) 1 = ⊥ :=
  subgroupImage_eq_bot_of_le 1 (normalClosure_le_commutator hK)

end AssociatedGraded

end T3
