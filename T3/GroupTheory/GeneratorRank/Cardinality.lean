/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.GeneratorRank
public import T3.GroupTheory.Presentation
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Nat.Log

/-!
# Generator rank and the cardinality bounds in the main theorem

For an exponent-three group, representatives of a basis of the first graded layer generate
its whole group. For finitely generated groups this identifies the minimum generator rank
with the dimension of the first layer. The first quotient supplies the order lower bound,
while the free group on a minimum generating set supplies the order upper bound.

The final comparison follows the paper's full logarithmic chain. `Nat.log 3` expresses its
integer inequalities without introducing real logarithms. An injective map into a finitely
generated exponent-three group also supplies finite generation of the source, so it is not
an extra hypothesis in the final package.

The free-quotient order argument uses the actual generator rank throughout.
No model-theory module is imported.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, lines 823–826.
-/

@[expose] public section

open Module

namespace T3

open AssociatedGraded

variable {G : Type*} [Group G] [Fact (HasExponentThree G)] [Group.FG G]

/-- The minimum generator rank equals the dimension of the actual first graded quotient.
Representatives of its finite basis generate the whole group by the two commutator inclusions.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem rank_eq_finrank_layerOne : Group.rank G = Module.finrank (ZMod 3) (Layer G 1) := by
  classical
  apply le_antisymm ?_ finrank_layerOne_le_rank
  let b := Module.finBasis (ZMod 3) (Layer G 1)
  choose a ha using fun i => mk_surjective G 1 (b i)
  have hsur := Free.lift_surjective_of_basis (show HasExponentThree G from Fact.out) b
    (fun i => (a i : G)) ha
  have hle := Group.rank_le_of_surjective _ hsur
  exact hle.trans (Free.rank_le_card.trans_eq (by simp))

/-- A finitely generated exponent-three group is finite, via its free presentation.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
private theorem finite_of_fg : Finite G := by
  classical
  obtain ⟨s, _, hs⟩ := Group.rank_spec G
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let : Finite (Free s) := Free.finite
  have hsur := Free.lift_surjective_of_generating_family (Subtype.val : s → G)
    (by simpa using hs)
  exact Finite.of_surjective _ hsur

/-- The first graded quotient has cardinality `3 ^ rank G`, giving the paper's order lower bound.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem three_pow_rank_le_natCard : 3 ^ Group.rank G ≤ Nat.card G := by
  let : Finite G := finite_of_fg
  have hsur : Function.Surjective (fun x : G => mk G 1 ⟨x, Subgroup.mem_top _⟩) := by
    intro y
    obtain ⟨x, rfl⟩ := mk_surjective G 1 y
    exact ⟨x, rfl⟩
  have h := Nat.card_le_card_of_surjective _ hsur
  rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod,
    ← rank_eq_finrank_layerOne] at h
  exact h

/-- A free presentation on a minimum generating set gives the paper's order upper bound.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem natCard_le_three_pow_freeOrderExponent_rank :
    Nat.card G ≤ 3 ^ freeOrderExponent (Group.rank G) := by
  classical
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec G
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let : Finite (Free s) := Free.finite
  have hsur := Free.lift_surjective_of_generating_family (Subtype.val : s → G)
    (by simpa using hs)
  have h := Nat.card_le_card_of_surjective _ hsur
  rw [Free.natCard_eq_pow_freeOrderExponent] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, hcard] using h

/-- The minimum number of generators is at most the base-three logarithm of the group order.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem rank_le_log_three_natCard : Group.rank G ≤ Nat.log 3 (Nat.card G) := by
  apply Nat.le_log_of_pow_le (by decide)
  exact three_pow_rank_le_natCard

/-- The exponent in the free-group order increases with the number of generators.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
private theorem monotone_freeOrderExponent : Monotone freeOrderExponent := by
  intro m n h
  exact Nat.add_le_add (Nat.add_le_add h (Nat.choose_mono 2 h)) (Nat.choose_mono 3 h)

/-- The logarithm of the group order is at most the exponent in the corresponding free-group order.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem log_three_natCard_le_freeOrderExponent_rank :
    Nat.log 3 (Nat.card G) ≤ freeOrderExponent (Group.rank G) := by
  have h := Nat.log_mono_right (b := 3) (natCard_le_three_pow_freeOrderExponent_rank (G := G))
  rwa [Nat.log_pow (by decide)] at h

variable {A B : Type*} [Group A] [Group B]

/-- The rank of a group embedded in an `m`-generated exponent-three group is at most `t(m)`.
The proof follows the paper's chain through both group orders and their base-three logarithms.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem rank_le_freeOrderExponent_of_injective [Group.FG A] [Group.FG B]
    (hB : HasExponentThree B) (f : A →* B) (hf : Function.Injective f)
    {m : ℕ} (hBm : Group.rank B ≤ m) : Group.rank A ≤ freeOrderExponent m := by
  let : Fact (HasExponentThree B) := ⟨hB⟩
  let : Finite B := finite_of_fg
  let : Fact (HasExponentThree A) := ⟨fun a => hf (by rw [map_pow, hB, map_one])⟩
  exact rank_le_log_three_natCard.trans ((Nat.log_mono_right
    (Nat.card_le_card_of_injective f hf)).trans
      (log_three_natCard_le_freeOrderExponent_rank.trans (monotone_freeOrderExponent hBm)))

/-- An embedding into an `m`-generated exponent-three group supplies finite generation and
the bound `t(m)` for the source. No finite-generation or exponent assumption on the source
is needed.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v9.tex, `thm:main`, the rank and order comparison on lines 823–826.
-/
theorem exists_fg_and_rank_le_freeOrderExponent_of_injective [Group.FG B]
    (hB : HasExponentThree B) (f : A →* B) (hf : Function.Injective f)
    {m : ℕ} (hBm : Group.rank B ≤ m) :
    ∃ hA : Group.FG A, letI := hA; Group.rank A ≤ freeOrderExponent m := by
  let : Fact (HasExponentThree B) := ⟨hB⟩
  let : Finite B := finite_of_fg
  let : Finite A := Finite.of_injective f hf
  exact ⟨inferInstance, rank_le_freeOrderExponent_of_injective hB f hf hBm⟩

end T3
