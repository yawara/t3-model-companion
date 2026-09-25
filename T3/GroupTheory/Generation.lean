/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Identities

/-!
# Generating an exponent-three group from its abelianization

If `H ⊔ G' = ⊤`, the paper first proves `G' ≤ H ⊔ ⁅H, G'⁆ ≤ H ⊔ γ₃(G)`.
Centrality of `γ₃(G)` then gives `⁅H, G'⁆ ≤ H`, and consequently `H = ⊤`.
The two subgroup inclusions are retained explicitly here.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, v9 Proposition 4.1, lines 862–882.
-/

@[expose] public section

open scoped commutatorElement Pointwise

namespace T3

variable {G : Type*} [Group G]

/-- Covering the abelianization expresses every element as a subgroup element times a
derived-subgroup element.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, equality `G = H γ₂(G)`.
-/
theorem exists_mem_mul_mem_commutator {H : Subgroup G} (hsup : H ⊔ commutator G = ⊤) (g : G) :
    ∃ h ∈ H, ∃ d ∈ commutator G, g = h * d := by
  have hmem : g ∈ (H : Set G) * (commutator G : Set G) := by
    rw [← Subgroup.mul_normal, hsup]
    trivial
  obtain ⟨h, hh, d, hd, rfl⟩ := hmem
  exact ⟨h, hh, d, hd, rfl⟩

variable (hG : HasExponentThree G)
include hG

/-- A derived factor in the left argument contributes a central commutator.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, first commutator inclusion.
-/
theorem commutator_mul_left_of_mem_commutator {d : G} (hd : d ∈ commutator G) (a b : G) :
    ⁅a * d, b⁆ = ⁅d, b⁆ * ⁅a, b⁆ := by
  have hz := commutator_mem_center_of_mem_commutator hG hd b
  rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp hz a]
  group

/-- A derived factor in the right argument contributes a central commutator.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, first commutator inclusion.
-/
theorem commutator_mul_right_of_mem_commutator {d : G} (hd : d ∈ commutator G) (a b : G) :
    ⁅a, b * d⁆ = ⁅a, d⁆ * ⁅a, b⁆ := by
  have hz : ⁅a, d⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (commutator_mem_center_of_mem_commutator hG hd a)
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅a, b⁆ * b * ⁅a, d⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, d⁆) * b⁻¹ := by group
    _ = ⁅a, b⁆ * (⁅a, d⁆ * b) * b⁻¹ := by rw [Subgroup.mem_center_iff.mp hz b]
    _ = ⁅a, b⁆ * ⁅a, d⁆ := by group
    _ = ⁅a, d⁆ * ⁅a, b⁆ := Subgroup.mem_center_iff.mp hz ⁅a, b⁆

/-- The first inclusion in the paper: if `G = H γ₂(G)`, then
`γ₂(G) ≤ H ⊔ [H, γ₂(G)]`.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, first displayed commutator inclusion.
-/
theorem commutator_le_sup_commutator_of_sup_eq_top {H : Subgroup G}
    (hsup : H ⊔ commutator G = ⊤) : commutator G ≤ H ⊔ ⁅H, commutator G⁆ := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  obtain ⟨ha, hha, da, hda, rfl⟩ := exists_mem_mul_mem_commutator hsup a
  obtain ⟨hb, hhb, db, hdb, rfl⟩ := exists_mem_mul_mem_commutator hsup b
  rw [commutator_mul_left_of_mem_commutator hG hda,
    commutator_mul_right_of_mem_commutator hG hdb,
    commutator_mul_right_of_mem_commutator hG hdb,
    (commute_of_mem_commutator hG hda hdb).commutator_eq, one_mul]
  apply Subgroup.mul_mem
  · rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator hhb hda))
  · apply Subgroup.mul_mem
    · exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hha hdb)
    · exact Subgroup.mem_sup_left (Subgroup.commutator_le_self H
        (Subgroup.commutator_mem_commutator hha hhb))

/-- The first inclusion implies `γ₂(G) ≤ H γ₃(G)`.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, first displayed commutator inclusion.
-/
theorem commutator_le_sup_lowerCentralSeries_two_of_sup_eq_top {H : Subgroup G}
    (hsup : H ⊔ commutator G = ⊤) :
    commutator G ≤ H ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  apply (commutator_le_sup_commutator_of_sup_eq_top hG hsup).trans
  apply sup_le_sup_left
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
  exact Subgroup.commutator_mono le_rfl le_top

/-- The second inclusion in the paper: centrality of `γ₃(G)` gives `[H, γ₂(G)] ≤ H`.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, second displayed commutator inclusion.
-/
theorem commutator_right_le_of_sup_commutator_eq_top {H : Subgroup G}
    (hsup : H ⊔ commutator G = ⊤) : ⁅H, commutator G⁆ ≤ H := by
  apply Subgroup.commutator_le.mpr
  intro a ha d hd
  have hmem : d ∈ (H : Set G) * ((⊤ : Subgroup G).lowerCentralSeries 2 : Set G) := by
    rw [← Subgroup.mul_normal]
    exact commutator_le_sup_lowerCentralSeries_two_of_sup_eq_top hG hsup hd
  obtain ⟨h, hh, z, hz, rfl⟩ := hmem
  have hcomm : ⁅a, z⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (lowerCentralSeries_two_le_center hG hz) a)
  rw [commutatorElement_mul_right_eq_mul_conj, hcomm]
  simpa using Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator ha hh)

/-- A subgroup covering the abelianization contains the entire derived subgroup.

Paper-ID: structure.basis_lift
TeX: T3_modelcompanion_v9.tex, `proposition:lift`, conclusion of the two inclusions.
-/
theorem commutator_le_of_sup_eq_top {H : Subgroup G} (hsup : H ⊔ commutator G = ⊤) :
    commutator G ≤ H :=
  (commutator_le_sup_commutator_of_sup_eq_top hG hsup).trans
    (sup_le le_rfl (commutator_right_le_of_sup_commutator_eq_top hG hsup))

/-- A subgroup covering the abelianization of an exponent-three group is the whole group.

Paper-ID: structure.basis_lift; structure.generation_mod_derived
TeX: T3_modelcompanion_v9.tex, `proposition:lift`; `remark:G=H`, Remark 4.2, lines 894–896.
-/
theorem eq_top_of_sup_commutator_eq_top {H : Subgroup G} (hsup : H ⊔ commutator G = ⊤) : H = ⊤ := by
  rw [← hsup, sup_eq_left.mpr (commutator_le_of_sup_eq_top hG hsup)]

end T3
