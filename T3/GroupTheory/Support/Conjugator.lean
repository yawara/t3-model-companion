/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Support.Collection
public import T3.GroupTheory.CentralSeries

/-!
# Bounding a conjugator by the number of generators of one factor

Modulo the third lower central term, collection along a generating list of the first factor
uses one element of the second factor per generator, and one further element. The error in
lifting this expression is central, so the paper's right conjugation action is unchanged.

The quotient, lifting, and central-error calculations reuse earlier proofs by Yawara Ishida.
The bound by the whole first subgroup's cardinality is replaced
by the length of a generating list.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v4.tex, `lemma:witness in bdd support`, lines 681–693.
-/

@[expose] public section

namespace T3.Support

open scoped commutatorElement

variable {F : Type*} [Group F]

/-! ### The quotient by `γ₃` has central derived subgroup -/

/-- A commutator against a derived element lies in `γ₃`. -/
theorem commutator_mem_lowerCentralSeries_two {k : F} (hk : k ∈ commutator F) (w : F) :
    ⁅k, w⁆ ∈ (⊤ : Subgroup F).lowerCentralSeries 2 := by
  rw [show (2 : ℕ) = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one]
  exact Subgroup.commutator_mem_commutator hk (Subgroup.mem_top w)

/-- In the quotient by `γ₃` the derived subgroup is central. -/
theorem commutator_quotient_gammaThree_le_center :
    commutator (F ⧸ (⊤ : Subgroup F).lowerCentralSeries 2) ≤
      Subgroup.center (F ⧸ (⊤ : Subgroup F).lowerCentralSeries 2) := by
  have hmap : commutator (F ⧸ (⊤ : Subgroup F).lowerCentralSeries 2) =
      (commutator F).map (QuotientGroup.mk' ((⊤ : Subgroup F).lowerCentralSeries 2)) := by
    have htop : (⊤ : Subgroup F).map
        (QuotientGroup.mk' ((⊤ : Subgroup F).lowerCentralSeries 2)) = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [commutator_def, commutator_def, Subgroup.map_commutator, htop]
  intro q hq
  rw [hmap] at hq
  obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hq
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective
    (s := (⊤ : Subgroup F).lowerCentralSeries 2) y
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq]
  have hcomm : (h * f)⁻¹ * (f * h) = ⁅f⁻¹, h⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [hcomm]
  exact commutator_mem_lowerCentralSeries_two (Subgroup.inv_mem _ hf) _

/-! ### Lifting a list along the quotient -/

theorem exists_list_lift {N : Subgroup F} [N.Normal] (S : Subgroup F) :
    ∀ l : List (F ⧸ N), (∀ z ∈ l, z ∈ S.map (QuotientGroup.mk' N)) →
      ∃ lF : List F, (∀ y ∈ lF, y ∈ S) ∧
        lF.map (QuotientGroup.mk' N) = l ∧ lF.length = l.length := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], by simp, by simp, by simp⟩
  | cons z t ih =>
      intro h
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (h z List.mem_cons_self)
      obtain ⟨tF, htF, htFmap, htFlen⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
      refine ⟨y :: tF, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hy
        · exact htF w hw
      · rw [List.map_cons, hyz, htFmap]
      · rw [List.length_cons, List.length_cons, htFlen]

/-! ### Collected products lie in the generated subgroup -/

theorem crossList_mem_closure {S : Set F} {m : F → F} :
    ∀ {l : List F}, (∀ y ∈ l, y ∈ Subgroup.closure S) → (∀ y ∈ l, m y ∈ Subgroup.closure S) →
      crossList m l ∈ Subgroup.closure S := by
  intro l
  induction l with
  | nil => exact fun _ _ => Subgroup.one_mem _
  | cons x t ih =>
      intro hx hm
      refine Subgroup.mul_mem _ ?_
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
          (fun y hy => hm y (List.mem_cons_of_mem _ hy)))
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (hx x List.mem_cons_self) (hm x List.mem_cons_self))
        (Subgroup.inv_mem _ (hx x List.mem_cons_self)))
        (Subgroup.inv_mem _ (hm x List.mem_cons_self))

/-! ### The compression -/

/-- A generating list of length at most `k` for one factor allows compression of every
conjugator using at most `k + 1` elements of the other factor. The ambient group may be infinite.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v4.tex, `lemma:witness in bdd support`, lines 681–693.
-/
theorem exists_compressed_conjugator (hF : HasExponentThree F) {BB MM : Subgroup F}
    (hgen : BB ⊔ MM = ⊤) (b : List F)
    (hb : Subgroup.closure {x | x ∈ b} = BB) {k : ℕ} (hlen : b.length ≤ k) (u : F) :
    ∃ Y : Finset F, ↑Y ⊆ (MM : Set F) ∧ Y.card ≤ k + 1 ∧
      ∃ v ∈ Subgroup.closure ((BB : Set F) ∪ ↑Y), ∀ x : F, u⁻¹ * x * u = v⁻¹ * x * v := by
  classical
  set N : Subgroup F := (⊤ : Subgroup F).lowerCentralSeries 2 with hN
  set π : F →* F ⧸ N := QuotientGroup.mk' N with hπ
  have hQ : commutator (F ⧸ N) ≤ Subgroup.center (F ⧸ N) :=
    commutator_quotient_gammaThree_le_center
  -- the images of the two subgroups still generate
  have hgen' : BB.map π ⊔ MM.map π = ⊤ := by
    rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective N
  let l : List (F ⧸ N) := (b.map π).dedup
  have hlnd : l.Nodup := List.nodup_dedup _
  have hlgen : Subgroup.closure {x | x ∈ l} = BB.map π := by
    calc
      Subgroup.closure {x | x ∈ l} = Subgroup.closure (π '' {x | x ∈ b}) := by
        congr 1
        ext x
        simp [l]
      _ = (Subgroup.closure {x | x ∈ b}).map π := (MonoidHom.map_closure π _).symm
      _ = BB.map π := by rw [hb]
  have hlmem : ∀ z ∈ l, z ∈ BB.map π := fun z hz =>
    hlgen ▸ Subgroup.subset_closure hz
  have hllen : l.length ≤ k := by
    exact (List.dedup_sublist _).length_le.trans (by simpa only [List.length_map] using hlen)
  -- the normal form in the quotient
  obtain ⟨β', hβ', μ', hμ', m', hm', hu'⟩ :=
    exists_crossList_normalForm hQ hgen' hlnd hlgen (π u)
  -- lift everything back
  obtain ⟨b₀, hb₀, hb₀eq⟩ := Subgroup.mem_map.mp hβ'
  obtain ⟨μ, hμ, hμeq⟩ := Subgroup.mem_map.mp hμ'
  obtain ⟨lF, hlF, hlFmap, hlFlen⟩ := exists_list_lift BB l fun z hz => hlmem z hz
  have hsec : ∀ z : F ⧸ N, ∃ y : F, y ∈ MM ∧ (z ∈ MM.map π → π y = z) := by
    intro z
    by_cases hz : z ∈ MM.map π
    · obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      exact ⟨y, hy, fun _ => hyz⟩
    · exact ⟨1, Subgroup.one_mem _, fun h => absurd h hz⟩
  choose σ hσmem hσeq using hsec
  set m : F → F := fun y => σ (m' (π y)) with hm
  have hmmem : ∀ y : F, m y ∈ MM := fun y => hσmem _
  have hmeq : ∀ y : F, π (m y) = m' (π y) := fun y => hσeq _ (hm' (π y))
  -- the compressed conjugator
  set Y : Finset F := insert μ (lF.map m).toFinset with hY
  refine ⟨Y, ?_, ?_, b₀ * μ * crossList m lF, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_coe, hY, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hμ
    · rw [List.mem_toFinset, List.mem_map] at hy
      obtain ⟨w, -, rfl⟩ := hy
      exact hmmem w
  · refine le_trans (Finset.card_insert_le _ _) ?_
    refine Nat.succ_le_succ (le_trans (List.toFinset_card_le _) ?_)
    rw [List.length_map, hlFlen]
    exact hllen
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Set.mem_union_left _ hb₀)
    · exact Subgroup.subset_closure (Set.mem_union_right _ (by
        rw [Finset.mem_coe, hY]; exact Finset.mem_insert_self _ _))
    · refine crossList_mem_closure (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.subset_closure (Set.mem_union_left _ (hlF y hy))
      · refine Subgroup.subset_closure (Set.mem_union_right _ ?_)
        rw [Finset.mem_coe, hY]
        exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hy))
  · -- the two conjugators differ by a central element
    have hpi : π (b₀ * μ * crossList m lF) = π u := by
      rw [hu', map_mul, map_mul, hb₀eq, hμeq]
      refine congrArg (fun z => β' * μ' * z) ?_
      have hcross : π (crossList m lF) = crossList m' (lF.map π) := by
        refine map_crossList π m m' lF fun y _ => hmeq y
      rw [hcross, hlFmap]
    have hmemN : u * (b₀ * μ * crossList m lF)⁻¹ ∈ N := by
      have hone : π (u * (b₀ * μ * crossList m lF)⁻¹) = 1 := by
        rw [map_mul, map_inv, hpi, mul_inv_cancel]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
    have hcent : u * (b₀ * μ * crossList m lF)⁻¹ ∈ Subgroup.center F :=
      lowerCentralSeries_two_le_center hF hmemN
    intro x
    set v := b₀ * μ * crossList m lF with hv
    have heq := congrArg (fun z : F => u⁻¹ * z * v) (Subgroup.mem_center_iff.mp hcent x)
    change u⁻¹ * (x * (u * v⁻¹)) * v = u⁻¹ * ((u * v⁻¹) * x) * v at heq
    convert heq using 1 <;> group


end T3.Support
