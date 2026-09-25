/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.Basic
public import T3.GroupTheory.GeneratorRank

/-!
# Generators and rank of exponent-three coproducts

The two factor images generate the actual cube quotient of the ordinary free product.
Consequently finite generating sets for the factors give a finite generating set for their
coproduct, with cardinality at most the sum of their cardinalities. Neither factor is required
to have exponent three, and the two factor universes may differ.

The free-two specialization is the final addition of two generators in Proposition 4.13.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, lines 1331–1350.
-/

@[expose] public section

namespace T3

namespace Coproduct

variable {G H : Type*} [Group G] [Group H]

/-- The factor images generate the coproduct, including when a factor has nontrivial cube
relations. This follows by mapping the ordinary free-product generation theorem to the quotient.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, generation of the free product.
-/
theorem range_inl_sup_range_inr :
    (inl : G →* Coproduct G H).range ⊔ (inr : H →* Coproduct G H).range = ⊤ := by
  rw [inl, inr,
    ← Monoid.Coprod.range_eq (powerQuotientMk (G := Monoid.Coprod G H) (n := 3))]
  exact MonoidHom.range_eq_top.mpr powerQuotientMk_surjective

/-- Images of generating sets of the factors generate the actual exponent-three coproduct.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, generation of the free product.
-/
theorem closure_image_inl_union_image_inr {s : Set G} {t : Set H}
    (hs : Subgroup.closure s = ⊤) (ht : Subgroup.closure t = ⊤) :
    Subgroup.closure (inl '' s ∪ inr '' t : Set (Coproduct G H)) = ⊤ := by
  rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
    hs, ht, ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_inl_sup_range_inr]

/-- Coproducts of finitely generated groups are finitely generated.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, finite generation of `D₃`.
-/
instance fg [Group.FG G] [Group.FG H] : Group.FG (Coproduct G H) := by
  obtain ⟨s, hs, hfs⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨t, ht, hft⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  exact Group.fg_iff.mpr ⟨inl '' s ∪ inr '' t, closure_image_inl_union_image_inr hs ht,
    (hfs.image _).union (hft.image _)⟩

/-- The rank of the coproduct is at most the sum of the ranks of its factors.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, the generator count for `D₃`.
-/
theorem rank_le [Group.FG G] [Group.FG H] :
    Group.rank (Coproduct G H) ≤ Group.rank G + Group.rank H := by
  classical
  obtain ⟨s, hs, hgenS⟩ := Group.rank_spec G
  obtain ⟨t, ht, hgenT⟩ := Group.rank_spec H
  have hgen : Subgroup.closure
      (↑(s.image inl ∪ t.image inr) : Set (Coproduct G H)) = ⊤ := by
    simpa only [Finset.coe_union, Finset.coe_image] using
      closure_image_inl_union_image_inr hgenS hgenT
  exact (Group.rank_le hgen).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_image_le.trans_eq hs) (Finset.card_image_le.trans_eq ht)))

/-- Adjoining a free factor on two generators increases the rank by at most two.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, lines 1341–1346.
-/
theorem rank_freeTwo_le [Group.FG G] :
    Group.rank (Coproduct G (Free (Fin 2))) ≤ Group.rank G + 2 :=
  rank_le.trans (Nat.add_le_add_left (by simpa using Free.rank_le_card (I := Fin 2)) _)

end Coproduct

end T3
