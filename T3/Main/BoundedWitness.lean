/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Amalgamation
public import T3.GroupTheory.Coproduct.Support
public import T3.GroupTheory.GeneratorRank.Cardinality
public import T3.ModelTheory.StrictEnvelope

/-!
# The bounded non-amalgamation witness

The bound depends only on the number of generators of the finite extension. The paper's
normal-closure witness is compressed by Lemma 3.2, enlarged to a strict envelope, and pulled
back through the injective comparison of coproducts. Both factor-witness alternatives are used.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, Theorem 3.3.
-/

@[expose] public section

namespace T3

open FirstOrder FirstOrder.Language FirstOrder.Group

/-- The paper's uniform bound, depending only on the number of generators of the extension.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, `f(m)=f₀((3m+4)t(m)+1)` on line 734.
-/
def witnessBound (m : ℕ) : ℕ := strictEnvelopeBound ((3 * m + 4) * freeOrderExponent m + 1)

private theorem support_card_le_argument {m n : ℕ} (hn : n ≤ freeOrderExponent m) :
    3 * (m + 1) * n + n + 1 ≤ (3 * m + 4) * freeOrderExponent m + 1 := by
  calc
    _ = (3 * m + 4) * n + 1 := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _

private theorem exists_strict_support {M : Type} [Group M] [CompatibleGroup M]
    (hM : exponentThreeTheory.IsExistentiallyClosed M) (A : Subgroup M) {B : Type*} [Group B]
    [Group.FG B] (j : A →* B) {m : ℕ} (hBm : Group.rank B ≤ m)
    (s : Finset A) (hs : Subgroup.closure (↑s : Set A) = ⊤)
    (hn : s.card ≤ freeOrderExponent m) {w : Coproduct M B}
    (hw : w ∈ Subgroup.normalClosure
      (Set.range fun a : s => Amalgamation.relator A.subtype j a))
    (Z : Finset M) (hZ : Z.card ≤ 1) :
    ∃ (D : Subgroup M) (hD : Group.FG D) (_ : A ≤ D),
      letI := hD
      (↑Z : Set M) ⊆ D ∧ Group.rank D ≤ witnessBound m ∧ IsStrict D ∧
        w ∈ Support.normalClosureIn (Coproduct.map D.subtype (MonoidHom.id B)).range
          (Set.range fun a : s => Amalgamation.relator A.subtype j a) := by
  classical
  let Δ := Set.range fun a : s => Amalgamation.relator A.subtype j a
  have hΔ : Δ.encard ≤ s.card := by
    change (Set.range fun a : (↑s : Set A) => Amalgamation.relator A.subtype j a).encard ≤ _
    rw [← Set.image_eq_range]
    exact (Set.encard_image_le _ _).trans_eq (Set.encard_coe_eq_coe_finsetCard s)
  obtain ⟨Y, hY, hcert⟩ := Coproduct.exists_bounded_factor_support hBm Δ hΔ hw
  let S : Finset M := Y ∪ s.image A.subtype ∪ Z
  have hS : S.card ≤ (3 * m + 4) * freeOrderExponent m + 1 := by
    have hcount := (Finset.card_union_le (Y ∪ s.image A.subtype) Z).trans
      (Nat.add_le_add ((Finset.card_union_le _ _).trans
        (Nat.add_le_add hY Finset.card_image_le)) hZ)
    exact hcount.trans (support_card_le_argument hn)
  let C := Subgroup.closure (↑S : Set M)
  have hAC : A ≤ C := by
    have hmap : A = (Subgroup.closure (↑s : Set A)).map A.subtype := by
      rw [hs, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  obtain ⟨D, hD, hCD, hbound, _, hstrict⟩ := exists_strict_envelope hM C
    ((Subgroup.rank_closure_finset_le_card S).trans hS)
  letI : Group.FG D := hD
  have hSD : (↑S : Set M) ⊆ D := fun _ hx => hCD (Subgroup.subset_closure hx)
  have hAD : A ≤ D := hAC.trans hCD
  refine ⟨D, hD, hAD, (fun z hz => hSD (Finset.mem_union_right _ hz)), hbound, hstrict, ?_⟩
  apply hcert D (fun y hy => hSD (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))
  rintro _ ⟨a, rfl⟩
  refine ⟨Amalgamation.relator (Subgroup.inclusion hAD) j a, ?_⟩
  simp [Amalgamation.relator]

private theorem preimage_relators {M B : Type*} [Group M] [Group B]
    (A D : Subgroup M) (hAD : A ≤ D) (j : A →* B) (s : Finset A)
    (hΦ : Function.Injective (Coproduct.map D.subtype (MonoidHom.id B))) :
    Coproduct.map D.subtype (MonoidHom.id B) ⁻¹'
        (Set.range fun a : s => Amalgamation.relator A.subtype j a) =
      Set.range fun a : s => Amalgamation.relator (Subgroup.inclusion hAD) j a := by
  have hrel (a : A) : Coproduct.map D.subtype (MonoidHom.id B)
      (Amalgamation.relator (Subgroup.inclusion hAD) j a) =
        Amalgamation.relator A.subtype j a := by
    simp [Amalgamation.relator]
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, hΦ ((hrel a).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, (hrel a).symm⟩

/-- If an existentially closed exponent-three group and an `m`-generated extension of its
finite subgroup do not amalgamate, the obstruction already occurs in a subgroup generated
by at most `witnessBound m` elements. The bound is independent of the common subgroup.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, Theorem 3.3, including both factor-witness cases.
-/
theorem exists_bounded_nonamalgamation_witness {M : Type} [Group M] [CompatibleGroup M]
    (hM : exponentThreeTheory.IsExistentiallyClosed M) (A : Subgroup M) [Group.FG A]
    {B : Type*} [Group B] [Group.FG B] (hB : HasExponentThree B)
    (j : A →* B) (hj : Function.Injective j) {m : ℕ} (hBm : Group.rank B ≤ m)
    (hna : ¬ Amalgamation.AmalgamableOver A.subtype j) :
    ∃ (D : Subgroup M) (hD : Group.FG D) (hAD : A ≤ D),
      letI := hD
      Group.rank D ≤ witnessBound m ∧
        ¬ Amalgamation.AmalgamableOver (Subgroup.inclusion hAD) j := by
  classical
  letI : Fact (HasExponentThree M) := ⟨exponentThreeTheory_model_iff.mp hM.2.1⟩
  letI : Fact (HasExponentThree B) := ⟨hB⟩
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec A
  have hgen : Subgroup.closure (Set.range (Subtype.val : s → A)) = ⊤ := by simpa using hs
  have hn : s.card ≤ freeOrderExponent m :=
    hcard.le.trans (rank_le_freeOrderExponent_of_injective hB j hj hBm)
  obtain hleft | hright := Amalgamation.exists_witness_of_generating_family A.subtype j
    (Subtype.val : s → A) hgen hna
  · obtain ⟨x, hx, hmem⟩ := hleft
    obtain ⟨D, hD, hAD, hXD, hbound, hstrict, hcert⟩ :=
      exists_strict_support hM A j hBm s hs hn hmem {x} (by simp)
    letI : Group.FG D := hD
    have hxD : x ∈ D := hXD (Finset.mem_singleton_self x)
    let Φ := Coproduct.map D.subtype (MonoidHom.id B)
    have hΦ : Function.Injective Φ := Coproduct.map_injective_of_strict D hstrict
    have hpull := Support.mem_normalClosure_of_mem_normalClosureIn Φ hΦ Φ.range le_rfl
      (Set.range fun a : s => Amalgamation.relator A.subtype j a)
      (x := Coproduct.inl (⟨x, hxD⟩ : D)) hcert
    rw [preimage_relators A D hAD j s hΦ,
      Amalgamation.normalClosure_relators_eq_of_closure_range_eq_top
        (Subgroup.inclusion hAD) j (Subtype.val : s → A) hgen] at hpull
    have hkill := (Amalgamation.leftMap_eq_one_iff (Subgroup.inclusion hAD) j
      (⟨x, hxD⟩ : D)).mpr hpull
    refine ⟨D, hD, hAD, hbound, ?_⟩
    intro ham
    have hi := ((Amalgamation.amalgamableOver_iff (Subgroup.inclusion hAD) j).mp ham).1
    exact hx (congrArg Subtype.val (hi (hkill.trans (map_one _).symm)))
  · obtain ⟨x, hx, hmem⟩ := hright
    obtain ⟨D, hD, hAD, _, hbound, hstrict, hcert⟩ :=
      exists_strict_support hM A j hBm s hs hn hmem ∅ (by simp)
    letI : Group.FG D := hD
    let Φ := Coproduct.map D.subtype (MonoidHom.id B)
    have hΦ : Function.Injective Φ := Coproduct.map_injective_of_strict D hstrict
    have hpull := Support.mem_normalClosure_of_mem_normalClosureIn Φ hΦ Φ.range le_rfl
      (Set.range fun a : s => Amalgamation.relator A.subtype j a)
      (x := Coproduct.inr x) hcert
    rw [preimage_relators A D hAD j s hΦ,
      Amalgamation.normalClosure_relators_eq_of_closure_range_eq_top
        (Subgroup.inclusion hAD) j (Subtype.val : s → A) hgen] at hpull
    have hkill := (Amalgamation.rightMap_eq_one_iff (Subgroup.inclusion hAD) j x).mpr hpull
    refine ⟨D, hD, hAD, hbound, ?_⟩
    intro ham
    have hi := ((Amalgamation.amalgamableOver_iff (Subgroup.inclusion hAD) j).mp ham).2
    exact hx (hi (hkill.trans (map_one _).symm))

/-- One function bounds the obstruction in every existentially closed model, uniformly in
the finite base and its extension. This is the existentially quantified form of Theorem 3.3.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, lines 702–712.
-/
theorem exists_uniform_nonamalgamation_bound :
    ∃ f : ℕ → ℕ, ∀ (m : ℕ) (M : Type) [Group M] [CompatibleGroup M],
      exponentThreeTheory.IsExistentiallyClosed M →
        ∀ (A : Subgroup M) [Group.FG A] (B : Type*) [Group B] [Group.FG B],
          HasExponentThree B → ∀ (j : A →* B), Function.Injective j → Group.rank B ≤ m →
            ¬ Amalgamation.AmalgamableOver A.subtype j →
              ∃ (D : Subgroup M) (hD : Group.FG D) (hAD : A ≤ D),
                letI := hD
                Group.rank D ≤ f m ∧
                  ¬ Amalgamation.AmalgamableOver (Subgroup.inclusion hAD) j := by
  refine ⟨witnessBound, ?_⟩
  intro m M _ _ hM A _ B _ _ hB j hj hBm hna
  exact exists_bounded_nonamalgamation_witness hM A hB j hj hBm hna

end T3
