/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.Rank
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The minimum generating cardinal of an arbitrary group

The paper's `d(G)` is the least cardinality of a generating set. For a finitely generated
group this agrees with mathlib's natural-number-valued `Group.rank`. The cardinal definition
also treats groups with no finite generating set, without assigning them a default finite value.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, line 249.
-/

@[expose] public noncomputable section

universe u

namespace Group

variable (G : Type u) [Group G]

/-- The least cardinality of a generating set of a group, including infinitely generated groups.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, line 249.
-/
def cardinalRank : Cardinal.{u} :=
  sInf {c | ∃ s : Set G, Subgroup.closure s = ⊤ ∧ Cardinal.mk s = c}

private theorem generatingCardinals_nonempty :
    {c | ∃ s : Set G, Subgroup.closure s = ⊤ ∧ Cardinal.mk s = c}.Nonempty :=
  ⟨Cardinal.mk (Set.univ : Set G), Set.univ, Subgroup.closure_univ, rfl⟩

/-- The minimum generating cardinal is attained by an actual generating subset.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, line 249.
-/
theorem cardinalRank_spec :
    ∃ s : Set G, Cardinal.mk s = cardinalRank G ∧ Subgroup.closure s = ⊤ := by
  obtain ⟨s, hs, hcard⟩ := csInf_mem (generatingCardinals_nonempty G)
  exact ⟨s, hcard, hs⟩

/-- Every generating set bounds the minimum generating cardinal from above.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, line 249.
-/
theorem cardinalRank_le {s : Set G} (hs : Subgroup.closure s = ⊤) :
    cardinalRank G ≤ Cardinal.mk s :=
  csInf_le ⟨0, fun _ _ => zero_le⟩ ⟨s, hs, rfl⟩

/-- The minimum generating cardinal is bounded by a finite number precisely when a finite
set with at most that many elements generates the group.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, line 249.
-/
theorem cardinalRank_le_nat_iff (n : ℕ) :
    cardinalRank G ≤ n ↔
      ∃ s : Finset G, s.card ≤ n ∧ Subgroup.closure (s : Set G) = ⊤ := by
  classical
  constructor
  · intro hn
    obtain ⟨s, hcard, hs⟩ := cardinalRank_spec G
    have hfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp
      ((hcard.trans_le hn).trans_lt Cardinal.natCast_lt_aleph0)
    refine ⟨hfin.toFinset, ?_, by simpa only [hfin.coe_toFinset] using hs⟩
    have h : (hfin.toFinset.card : Cardinal.{u}) ≤ n := by
      calc
        (hfin.toFinset.card : Cardinal.{u}) = Cardinal.mk (hfin.toFinset : Set G) :=
          Cardinal.mk_coe_finset.symm
        _ = Cardinal.mk s := congrArg (fun t : Set G => Cardinal.mk t) hfin.coe_toFinset
        _ = cardinalRank G := hcard
        _ ≤ n := hn
    exact_mod_cast h
  · rintro ⟨s, hcard, hs⟩
    exact (cardinalRank_le G hs).trans <| by
      change Cardinal.mk (s : Set G) ≤ (n : Cardinal.{u})
      have hmk : Cardinal.mk (s : Set G) = (s.card : Cardinal.{u}) := Cardinal.mk_coe_finset
      rw [hmk]
      exact_mod_cast hcard

/-- The cardinal-valued minimum agrees with mathlib's minimum number of generators whenever
the group is finitely generated.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, and every finite generator bound.
-/
theorem cardinalRank_eq_rank [FG G] : cardinalRank G = (rank G : Cardinal.{u}) := by
  apply le_antisymm
  · obtain ⟨s, hcard, hs⟩ := rank_spec G
    exact (cardinalRank_le_nat_iff G (rank G)).mpr ⟨s, hcard.le, hs⟩
  · obtain ⟨s, hcard, hs⟩ := cardinalRank_spec G
    have hupper : cardinalRank G ≤ (rank G : Cardinal.{u}) := by
      obtain ⟨t, ht, htgen⟩ := rank_spec G
      exact (cardinalRank_le_nat_iff G (rank G)).mpr ⟨t, ht.le, htgen⟩
    have hfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp
      ((hcard.trans_le hupper).trans_lt Cardinal.natCast_lt_aleph0)
    have hmk : Cardinal.mk s = (hfin.toFinset.card : Cardinal.{u}) := by
      calc
        Cardinal.mk s = Cardinal.mk (hfin.toFinset : Set G) :=
          congrArg (fun t : Set G => Cardinal.mk t) hfin.coe_toFinset.symm
        _ = hfin.toFinset.card := Cardinal.mk_coe_finset
    rw [← hcard, hmk]
    exact_mod_cast rank_le (show Subgroup.closure (hfin.toFinset : Set G) = ⊤ by
      simpa only [hfin.coe_toFinset] using hs)

/-- Finitely generated groups are exactly those with a finite generating cardinal.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7.
-/
theorem cardinalRank_lt_aleph0_iff : cardinalRank G < Cardinal.aleph0 ↔ FG G := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := cardinalRank_spec G
    have hfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt h)
    exact fg_iff.mpr ⟨s, hs, hfin⟩
  · intro h
    let := h
    rw [cardinalRank_eq_rank]
    exact Cardinal.natCast_lt_aleph0

end Group
