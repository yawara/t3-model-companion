/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Support.Conjugator
public import T3.GroupTheory.ConjugateWidth
public import T3.GroupTheory.GeneratorRank
public import Mathlib.Data.Set.Card

/-!
# A normal-closure witness with bounded support

Each principal normal factor needs at most three conjugates. Compressing their conjugators
against a generating list of the first subgroup uses at most three times one plus its length
in the second subgroup. The finite union of these supports contains a certificate for the
whole relation family in the paper's smaller generated subgroup.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support` (Lemma 3.2).
-/

@[expose] public section

namespace T3.Support

variable {H : Type*} [Group H]

/-- The normal closure inside a specified subgroup, viewed in the original ambient group.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, the certificate in `H₀`.
-/
def normalClosureIn (E : Subgroup H) (Δ : Set H) : Subgroup H :=
  (Subgroup.normalClosure (E.subtype ⁻¹' Δ)).map E.subtype

private theorem normalClosureIn_mono (E : Subgroup H) {Δ Ξ : Set H} (h : Δ ⊆ Ξ) :
    normalClosureIn E Δ ≤ normalClosureIn E Ξ :=
  Subgroup.map_mono (Subgroup.normalClosure_mono (Set.preimage_mono h))

private theorem conj_mem_normalClosureIn (E : Subgroup H) {a u : H}
    (ha : a ∈ E) (hu : u ∈ E) : u⁻¹ * a * u ∈ normalClosureIn E {a} := by
  let a' : E := ⟨a, ha⟩
  let u' : E := ⟨u, hu⟩
  apply Subgroup.mem_map.mpr
  refine ⟨u'⁻¹ * a' * u', ?_, rfl⟩
  exact Subgroup.normalClosure_normal.conj_mem' _
    (Subgroup.subset_normalClosure (show a' ∈ E.subtype ⁻¹' ({a} : Set H) from rfl)) u'

private theorem exists_conjList_support (hH : HasExponentThree H) {B G : Subgroup H}
    (hgen : B ⊔ G = ⊤) (b : List H) (hb : Subgroup.closure {x | x ∈ b} = B)
    {m : ℕ} (hlen : b.length ≤ m) (a : H) (l : List H) :
    ∃ Y : Finset H, (↑Y : Set H) ⊆ G ∧ Y.card ≤ (m + 1) * l.length ∧
      ∀ E : Subgroup H, B ≤ E → (↑Y : Set H) ⊆ E → a ∈ E →
        (l.map fun u => u⁻¹ * a * u).prod ∈ normalClosureIn E {a} := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp, fun E _ _ _ => by simp [normalClosureIn]⟩
  | cons u l ih =>
    obtain ⟨Y₀, hY₀, hcard₀, v, hv, heq⟩ :=
      exists_compressed_conjugator hH hgen b hb hlen u
    obtain ⟨Y₁, hY₁, hcard₁, hcert₁⟩ := ih
    refine ⟨Y₀ ∪ Y₁, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hY₀ hY₁
    · calc
        (Y₀ ∪ Y₁).card ≤ Y₀.card + Y₁.card := Finset.card_union_le _ _
        _ ≤ (m + 1) + (m + 1) * l.length := Nat.add_le_add hcard₀ hcard₁
        _ = (m + 1) * (u :: l).length := by simp [Nat.mul_succ, Nat.add_comm]
    · intro E hBE hYE haE
      have hY₀E : (↑Y₀ : Set H) ⊆ E := fun x hx => hYE (Finset.mem_union_left _ hx)
      have hY₁E : (↑Y₁ : Set H) ⊆ E := fun x hx => hYE (Finset.mem_union_right _ hx)
      have hvE : v ∈ E := ((Subgroup.closure_le _).mpr (Set.union_subset hBE hY₀E)) hv
      simpa only [List.map_cons, List.prod_cons, heq a] using
        (normalClosureIn E {a}).mul_mem (conj_mem_normalClosureIn E haE hvE)
          (hcert₁ E hBE hY₁E haE)

private theorem exists_principal_support (hH : HasExponentThree H) {B G : Subgroup H}
    (hgen : B ⊔ G = ⊤) (b : List H) (hb : Subgroup.closure {x | x ∈ b} = B)
    {m : ℕ} (hlen : b.length ≤ m) {a h : H}
    (hh : h ∈ Subgroup.normalClosure ({a} : Set H)) :
    ∃ Y : Finset H, (↑Y : Set H) ⊆ G ∧ Y.card ≤ 3 * (m + 1) ∧
      ∀ E : Subgroup H, B ≤ E → (↑Y : Set H) ⊆ E → a ∈ E →
        h ∈ normalClosureIn E {a} := by
  obtain ⟨l, hl, rfl⟩ := exists_conjList_of_mem_normalClosure hH hh
  obtain ⟨Y, hY, hcard, hcert⟩ := exists_conjList_support hH hgen b hb hlen a l
  exact ⟨Y, hY, hcard.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (m + 1) hl),
    hcert⟩

/-- All relators admit one support set with the paper's generator bound. The certificate
holds in every subgroup containing that support, the first factor, and all relators.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, finite-relator reduction and bound.
-/
theorem exists_finite_support (hH : HasExponentThree H) {B G : Subgroup H}
    (hgen : B ⊔ G = ⊤) (b : List H) (hb : Subgroup.closure {x | x ∈ b} = B)
    {m : ℕ} (hlen : b.length ≤ m) (Δ : Finset H) {h : H}
    (hh : h ∈ Subgroup.normalClosure (↑Δ : Set H)) :
    ∃ Y : Finset H, (↑Y : Set H) ⊆ G ∧ Y.card ≤ 3 * (m + 1) * Δ.card ∧
      ∀ E : Subgroup H, B ≤ E → (↑Y : Set H) ⊆ E → (↑Δ : Set H) ⊆ E →
        h ∈ normalClosureIn E Δ := by
  classical
  induction Δ using Finset.induction_on generalizing h with
  | empty =>
    have heq : h = 1 := by simpa only [Finset.coe_empty, Subgroup.normalClosure_empty,
      Subgroup.mem_bot] using hh
    subst h
    exact ⟨∅, by simp, by simp, fun E _ _ _ =>
      (normalClosureIn E (↑(∅ : Finset H) : Set H)).one_mem⟩
  | @insert a Δ ha ih =>
    rw [Finset.coe_insert, ← Set.singleton_union, Subgroup.normalClosure_union] at hh
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    obtain ⟨Y₀, hY₀, hcard₀, hcert₀⟩ := exists_principal_support hH hgen b hb hlen hx
    obtain ⟨Y₁, hY₁, hcard₁, hcert₁⟩ := ih hy
    refine ⟨Y₀ ∪ Y₁, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hY₀ hY₁
    · calc
        (Y₀ ∪ Y₁).card ≤ Y₀.card + Y₁.card := Finset.card_union_le _ _
        _ ≤ 3 * (m + 1) + 3 * (m + 1) * Δ.card := Nat.add_le_add hcard₀ hcard₁
        _ = 3 * (m + 1) * (insert a Δ).card := by
          simp only [Finset.card_insert_of_notMem ha, Nat.mul_succ]
          omega
    · intro E hBE hYE hΔE
      have hx' := hcert₀ E hBE (fun z hz => hYE (Finset.mem_union_left _ hz))
        (hΔE (Finset.mem_insert_self _ _))
      have hy' := hcert₁ E hBE (fun z hz => hYE (Finset.mem_union_right _ hz))
        (fun z hz => hΔE (Finset.mem_insert_of_mem hz))
      have hsingle : ({a} : Set H) ⊆ (↑(insert a Δ) : Set H) := by
        rintro z rfl
        exact Finset.mem_insert_self _ _
      have htail : (↑Δ : Set H) ⊆ (↑(insert a Δ) : Set H) := fun _ hz =>
        Finset.mem_insert_of_mem hz
      exact (normalClosureIn E ↑(insert a Δ)).mul_mem
        (normalClosureIn_mono E hsingle hx') (normalClosureIn_mono E htail hy')

/-- A normal-closure witness lies in the normal closure computed inside the paper's smaller
subgroup `H₀ = ⟨C,B,Δ⟩`. The displayed generating set certifies the bound on `d(C)`.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, both conclusions.
-/
theorem exists_bounded_support_of_generating_list (hH : HasExponentThree H)
    {B G : Subgroup H} (hgen : B ⊔ G = ⊤) (b : List H)
    (hb : Subgroup.closure {x | x ∈ b} = B) {m n : ℕ} (hlen : b.length ≤ m)
    (Δ : Finset H) (hΔ : Δ.card ≤ n) {h : H}
    (hh : h ∈ Subgroup.normalClosure (↑Δ : Set H)) :
    ∃ C : Subgroup H, C ≤ G ∧ ∃ Y : Finset H,
      Y.card ≤ 3 * (m + 1) * n ∧ Subgroup.closure (↑Y : Set H) = C ∧
      h ∈ normalClosureIn (Subgroup.closure ((C : Set H) ∪ (B : Set H) ∪ ↑Δ)) Δ := by
  obtain ⟨Y, hY, hcard, hcert⟩ := exists_finite_support hH hgen b hb hlen Δ hh
  let C := Subgroup.closure (↑Y : Set H)
  refine ⟨C, (Subgroup.closure_le _).mpr hY, Y,
    hcard.trans (Nat.mul_le_mul_left _ hΔ), rfl, ?_⟩
  apply hcert
  · intro x hx
    exact Subgroup.subset_closure (Or.inl (Or.inr hx))
  · intro x hx
    exact Subgroup.subset_closure (Or.inl (Or.inl (Subgroup.subset_closure hx)))
  · intro x hx
    exact Subgroup.subset_closure (Or.inr hx)

/-- The paper's bounded-support lemma, using the minimum number of generators of `B`.
The returned explicit generating set for `C` has at most `3(m+1)n` elements. No ambient
finiteness or nontriviality hypothesis is imposed.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support` (Lemma 3.2).
-/
theorem exists_bounded_support (hH : HasExponentThree H) {B G : Subgroup H}
    [Group.FG B] (hgen : B ⊔ G = ⊤) {m n : ℕ} (hB : Group.rank B ≤ m)
    (Δ : Finset H) (hΔ : Δ.card ≤ n) {h : H}
    (hh : h ∈ Subgroup.normalClosure (↑Δ : Set H)) :
    ∃ C : Subgroup H, C ≤ G ∧ ∃ Y : Finset H,
      Y.card ≤ 3 * (m + 1) * n ∧ Subgroup.closure (↑Y : Set H) = C ∧
      h ∈ normalClosureIn (Subgroup.closure ((C : Set H) ∪ (B : Set H) ∪ ↑Δ)) Δ := by
  classical
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec B
  let b := s.toList.map (Subtype.val : B → H)
  have hb : Subgroup.closure {x | x ∈ b} = B := by
    have heq : {x | x ∈ b} = B.subtype '' (↑s : Set B) := by
      ext x
      simp [b]
    rw [heq, ← MonoidHom.map_closure, hs, ← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype B
  have hlen : b.length ≤ m := by
    simpa only [b, List.length_map, Finset.length_toList, hcard] using hB
  exact exists_bounded_support_of_generating_list hH hgen b hb hlen Δ hΔ hh

/-- The bounded-support lemma for an arbitrary relation set of cardinality at most `n`.
Using extended cardinality makes the cardinal bound itself imply finiteness.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support` (Lemma 3.2).
-/
theorem exists_bounded_support_set (hH : HasExponentThree H) {B G : Subgroup H}
    [Group.FG B] (hgen : B ⊔ G = ⊤) {m n : ℕ} (hB : Group.rank B ≤ m)
    (Δ : Set H) (hΔ : Δ.encard ≤ n) {h : H} (hh : h ∈ Subgroup.normalClosure Δ) :
    ∃ C : Subgroup H, C ≤ G ∧ ∃ Y : Finset H,
      Y.card ≤ 3 * (m + 1) * n ∧ Subgroup.closure (↑Y : Set H) = C ∧
      h ∈ normalClosureIn (Subgroup.closure ((C : Set H) ∪ (B : Set H) ∪ Δ)) Δ := by
  obtain ⟨hfinite, hcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hΔ
  rw [Set.ncard_eq_toFinset_card Δ hfinite] at hcard
  simpa only [hfinite.coe_toFinset] using
    exists_bounded_support hH hgen hB hfinite.toFinset hcard
      (by simpa only [hfinite.coe_toFinset] using hh)

/-- The exact generator-rank and normal-closure conclusions for the concrete support
subgroup `C = ⟨Y⟩` in Lemma 3.2.

Paper-ID: main.bounded_support
TeX: T3_modelcompanion_v8.tex, `lemma:witness in bdd support`, `d(C) ≤ 3(m+1)n` and the
certificate inside `H₀ = ⟨C,B,Δ⟩`.
-/
theorem exists_bounded_support_rank (hH : HasExponentThree H) {B G : Subgroup H}
    [Group.FG B] (hgen : B ⊔ G = ⊤) {m n : ℕ} (hB : Group.rank B ≤ m)
    (Δ : Set H) (hΔ : Δ.encard ≤ n) {h : H} (hh : h ∈ Subgroup.normalClosure Δ) :
    ∃ Y : Finset H, Subgroup.closure (↑Y : Set H) ≤ G ∧
      Group.rank (Subgroup.closure (↑Y : Set H)) ≤ 3 * (m + 1) * n ∧
      h ∈ normalClosureIn
        (Subgroup.closure ((Subgroup.closure (↑Y : Set H) : Set H) ∪ (B : Set H) ∪ Δ)) Δ := by
  obtain ⟨C, hCG, Y, hY, hYC, hcert⟩ := exists_bounded_support_set hH hgen hB Δ hΔ hh
  refine ⟨Y, ?_, (Subgroup.rank_closure_finset_le_card Y).trans hY, ?_⟩
  · simpa only [hYC] using hCG
  · simpa only [hYC] using hcert

end T3.Support
