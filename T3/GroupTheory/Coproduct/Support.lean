/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Generation
public import T3.GroupTheory.Support.Transport

/-!
# Bounded support in a coproduct factor

Lemma 3.2 supplies a support set in the left factor's image. Pulling back its elements gives
at most `3(m+1)n` elements in the left factor itself. For every subgroup containing those
elements, the certificate is supported in its coproduct image once all relators lie there.
This retains the actual internal normal closure in the paper's subgroup `H₀`.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, lines 730–738.
-/

@[expose] public section

namespace T3.Coproduct

variable {G B : Type*} [Group G] [Group B]

/-- A normal-closure witness in the coproduct has support in a bounded finite subset of
the left factor. The right factor is bounded by its number of generators.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, the subgroup `C₀` and the inclusion of `H₀`.
-/
theorem exists_bounded_factor_support [Group.FG B] {m n : ℕ} (hB : Group.rank B ≤ m)
    (Δ : Set (Coproduct G B)) (hΔ : Δ.encard ≤ n) {w : Coproduct G B}
    (hw : w ∈ Subgroup.normalClosure Δ) :
    ∃ Y : Finset G, Y.card ≤ 3 * (m + 1) * n ∧
      ∀ D : Subgroup G, (↑Y : Set G) ⊆ D →
        Δ ⊆ (map D.subtype (MonoidHom.id B)).range →
        w ∈ Support.normalClosureIn (map D.subtype (MonoidHom.id B)).range Δ := by
  classical
  have hgen : (inr : B →* Coproduct G B).range ⊔ inl.range = ⊤ := by
    rw [sup_comm, range_inl_sup_range_inr]
  obtain ⟨C, hCG, Y, hYcard, hYC, hcert⟩ := Support.exists_bounded_support_set pow_three hgen
    (Group.rank_range_le.trans hB) Δ hΔ hw
  have hpull : ∀ y ∈ Y, ∃ x : G, inl x = y := fun y hy =>
    hCG (hYC ▸ Subgroup.subset_closure hy)
  choose pull hpull using hpull
  let Y₀ : Finset G := Y.attach.image fun y => pull y.1 y.2
  refine ⟨Y₀, (Finset.card_image_le.trans_eq Finset.card_attach).trans hYcard, ?_⟩
  intro D hYD hΔD
  let Φ := map D.subtype (MonoidHom.id B)
  have hCD : C ≤ Φ.range := by
    rw [← hYC, Subgroup.closure_le]
    intro y hy
    have hmem : pull y hy ∈ D := hYD (Finset.mem_image.mpr
      ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩)
    exact ⟨inl ⟨pull y hy, hmem⟩, hpull y hy⟩
  have hBD : (inr : B →* Coproduct G B).range ≤ Φ.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨inr b, rfl⟩
  exact Support.normalClosureIn_mono_ambient
    ((Subgroup.closure_le _).mpr (Set.union_subset (Set.union_subset hCD hBD) hΔD)) Δ hcert

end T3.Coproduct
