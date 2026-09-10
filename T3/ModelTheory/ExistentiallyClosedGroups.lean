/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ExponentThree
public import T3.ModelTheory.ExistentialClosedness
public import T3.GroupTheory.Coproduct.CentralSeries
public import T3.GroupTheory.Roots.Commutator
public import T3.GroupTheory.Roots.Triple

/-!
# The structure of existentially closed exponent-three groups

Finite diagrams transfer the root witnesses and the noncommuting elements from the paper's
extensions back to the existentially closed group, fixing every designated parameter.
The existentially closed group is proved nontrivial before using the free-two stabilization.
The model and its extensions may lie in arbitrary, independent universes.
The simultaneous root constructions supply single commutator and triple-commutator witnesses,
and the graded free-two separation supplies the reverse central-series inclusions.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, `proposition:structure of e.c. model`, Proposition 4.11.
-/

@[expose] public section

open scoped FirstOrder commutatorElement

namespace T3.ExistentiallyClosedGroups

open FirstOrder FirstOrder.Language FirstOrder.Group
open AssociatedGraded

variable {M : Type*} [Group M] [CompatibleGroup M]
  (hM : exponentThreeTheory.IsExistentiallyClosedAt M)

include hM

/-- A finite group embedded in an extension has a copy in the existentially closed group
fixing each designated parameter. The finite group is not assumed to model the theory.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, `proposition:structure of e.c. model`, finite-diagram transfer.
-/
theorem exists_group_embedding {N : Type*} {A : Type*} [Group N] [Group A] [Finite A]
    (hN : HasExponentThree N) (f : M →* N) (hf : Function.Injective f)
    (r : A →* N) (hr : Function.Injective r) {α : Type*} [Finite α]
    (a : α → A) (b : α → M) (hab : r ∘ a = f ∘ b) :
    ∃ g : A →* M, Function.Injective g ∧ g ∘ a = b := by
  let : CompatibleGroup N := compatibleGroupOfGroup N
  let : CompatibleGroup A := compatibleGroupOfGroup A
  let : N ⊨ exponentThreeTheory := exponentThreeTheory_model_iff.mpr hN
  obtain ⟨g, hg⟩ := hM.exists_embedding_over_tuple N
    (show M ↪[Language.group] N from embeddingOfInjectiveMonoidHom f hf) a b
    (show A ↪[Language.group] N from embeddingOfInjectiveMonoidHom r hr) hab
  exact ⟨embeddingToMonoidHom g, g.injective, hg⟩

/-- A finite collection of extension witnesses and parameters lies in a finite subgroup
which embeds back while fixing all the parameters.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, `proposition:structure of e.c. model`, finite witness transfer.
-/
theorem exists_copy_of_tuples {N : Type*} [Group N] (hN : HasExponentThree N)
    (f : M →* N) (hf : Function.Injective f) {α β : Type*} [Finite α] [Finite β]
    (a : α → M) (b : β → N) :
    ∃ (C : Subgroup N) (ha : ∀ i, f (a i) ∈ C) (_hb : ∀ j, b j ∈ C)
      (g : C →* M), Function.Injective g ∧ ∀ i, g ⟨f (a i), ha i⟩ = a i := by
  let C := Subgroup.closure (Set.range (f ∘ a) ∪ Set.range b)
  let : Finite C := finite_closure_of_exponent_three hN
    ((Set.finite_range (f ∘ a)).union (Set.finite_range b))
  have ha : ∀ i, f (a i) ∈ C := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hb : ∀ j, b j ∈ C := fun j => Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
  obtain ⟨g, hg, hga⟩ := exists_group_embedding hM hN f hf C.subtype Subtype.val_injective
    (fun i => (⟨f (a i), ha i⟩ : C)) a rfl
  exact ⟨C, ha, hb, g, hg, congrFun hga⟩

/-- An existentially closed model of `T₃` is nontrivial; this is derived before applying
Lemma 4.5, whose free-two separation requires a nontrivial left factor.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, `proposition:structure of e.c. model`, use of Lemma 4.5.
-/
theorem nontrivial : Nontrivial M := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  let : Finite (Free (Fin 2)) := finite_free_of_finite _
  obtain ⟨g, hg, _⟩ := exists_group_embedding hM
    (N := Coproduct M (Free (Fin 2))) Coproduct.pow_three Coproduct.inl
    (Coproduct.inl_injective hG) Coproduct.inr (Coproduct.inr_injective Free.pow_three)
    (fun x : Empty => x.elim) (fun x : Empty => x.elim) (funext fun x => x.elim)
  have hx : (Free.of 0 : Free (Fin 2)) ≠ 1 := by
    intro h
    apply Coproduct.FreeTwo.x_ne_zero
    change Free.layerOneBasis 0 = 0
    rw [Free.layerOneBasis_apply]
    apply (mk_eq_zero _ _ _).mpr
    change Free.of 0 ∈ commutator (Free (Fin 2))
    rw [h]
    exact Subgroup.one_mem _
  exact ⟨⟨g (Free.of 0), 1, fun h => hx (hg (h.trans (map_one g).symm))⟩⟩

/-- A commutator equation with a parameter descends from an exponent-three extension.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1198–1201.
-/
theorem exists_commutator_eq_of_extension {N : Type*} [Group N]
    (hN : HasExponentThree N) (f : M →* N) (hf : Function.Injective f)
    (a : M) (b c : N) (h : f a = ⁅b, c⁆) : ∃ x y : M, a = ⁅x, y⁆ := by
  obtain ⟨C, ha, hb, g, _, hg⟩ := exists_copy_of_tuples hM hN f hf
    (fun _ : Fin 1 => a) ![b, c]
  let b' : C := ⟨b, hb 0⟩
  let c' : C := ⟨c, hb 1⟩
  have h' : (⟨f a, ha 0⟩ : C) = ⁅b', c'⁆ := Subtype.ext h
  refine ⟨g b', g c', ?_⟩
  rw [← hg 0, h', map_commutatorElement]

/-- A triple-commutator equation descends while fixing its designated parameter.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, line 1202.
-/
theorem exists_triple_commutator_eq_of_extension {N : Type*} [Group N]
    (hN : HasExponentThree N) (f : M →* N) (hf : Function.Injective f)
    (a : M) (b c d : N) (h : f a = ⁅⁅b, c⁆, d⁆) :
    ∃ x y z : M, a = ⁅⁅x, y⁆, z⁆ := by
  obtain ⟨C, ha, hb, g, _, hg⟩ := exists_copy_of_tuples hM hN f hf
    (fun _ : Fin 1 => a) ![b, c, d]
  let b' : C := ⟨b, hb 0⟩
  let c' : C := ⟨c, hb 1⟩
  let d' : C := ⟨d, hb 2⟩
  have h' : (⟨f a, ha 0⟩ : C) = ⁅⁅b', c'⁆, d'⁆ := Subtype.ext h
  refine ⟨g b', g c', g d', ?_⟩
  rw [← hg 0, h', map_commutatorElement, map_commutatorElement]

/-- Noncommutation with a fixed parameter descends from an extension.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, line 1209.
-/
theorem exists_commutator_ne_one_of_extension {N : Type*} [Group N]
    (hN : HasExponentThree N) (f : M →* N) (hf : Function.Injective f)
    (a : M) (b : N) (h : ⁅f a, b⁆ ≠ 1) : ∃ x : M, ⁅a, x⁆ ≠ 1 := by
  obtain ⟨C, ha, hb, g, hg, hga⟩ := exists_copy_of_tuples hM hN f hf
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
  let a' : C := ⟨f a, ha 0⟩
  let b' : C := ⟨b, hb 0⟩
  refine ⟨g b', fun hbad => h ?_⟩
  have heq : ⁅a', b'⁆ = 1 := hg (by
    rw [map_commutatorElement, map_one]
    exact (congrArg (fun x => ⁅x, g b'⁆) (hga 0)).trans hbad)
  exact congrArg Subtype.val heq

/-- A nontrivial triple commutator with a fixed first parameter descends from an extension.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1204–1208.
-/
theorem exists_triple_commutator_ne_one_of_extension {N : Type*} [Group N]
    (hN : HasExponentThree N) (f : M →* N) (hf : Function.Injective f)
    (a : M) (b c : N) (h : ⁅⁅f a, b⁆, c⁆ ≠ 1) :
    ∃ x y : M, ⁅⁅a, x⁆, y⁆ ≠ 1 := by
  obtain ⟨C, ha, hb, g, hg, hga⟩ := exists_copy_of_tuples hM hN f hf
    (fun _ : Fin 1 => a) ![b, c]
  let a' : C := ⟨f a, ha 0⟩
  let b' : C := ⟨b, hb 0⟩
  let c' : C := ⟨c, hb 1⟩
  refine ⟨g b', g c', fun hbad => h ?_⟩
  have heq : ⁅⁅a', b'⁆, c'⁆ = 1 := hg (by
    rw [map_commutatorElement, map_commutatorElement, map_one]
    exact (congrArg (fun x => ⁅⁅x, g b'⁆, g c'⁆) (hga 0)).trans hbad)
  exact congrArg Subtype.val heq

/-- Every element of the third lower central term is a single triple commutator.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1192–1194 and 1202.
-/
theorem exists_triple_commutator (a : M)
    (ha : a ∈ (⊤ : Subgroup M).lowerCentralSeries 2) :
    ∃ x y z : M, a = ⁅⁅x, y⁆, z⁆ := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  let z : Fin 1 → M := fun _ => a
  exact exists_triple_commutator_eq_of_extension hM
    (TripleRoots.hasExponentThree_extension hG z) (TripleRoots.baseMap z)
    (TripleRoots.baseMap_injective hG z (fun _ => lowerCentralSeries_two_le_center hG ha))
    a (TripleRoots.generator z 0 0) (TripleRoots.generator z 0 1)
    (TripleRoots.generator z 0 2) (TripleRoots.baseMap_root z 0)

/-- Every element of the derived subgroup is a single commutator. The witnesses are first
adjoined by the concrete simultaneous quotient of Lemma 4.6 with one prescribed root.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1189–1191 and 1198–1201.
-/
theorem exists_commutator (a : M) (ha : a ∈ commutator M) :
    ∃ x y : M, a = ⁅x, y⁆ := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  let z : Fin 1 → M := fun _ => a
  exact exists_commutator_eq_of_extension hM
    (CommutatorRoots.hasExponentThree_extension z) (CommutatorRoots.baseMap z)
    (CommutatorRoots.baseMap_injective hG z (fun _ => ha)) a
    (CommutatorRoots.generator z 0 0) (CommutatorRoots.generator z 0 1)
    (CommutatorRoots.baseMap_root z 0)

/-- Every element outside the derived subgroup is detected by a triple commutator.
The witnesses first exist in the strict extension `M ∐ F₂`, and finite diagrams transfer them.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1204–1208.
-/
theorem exists_triple_commutator_ne_one (a : M) (ha : a ∉ commutator M) :
    ∃ b c : M, ⁅⁅a, b⁆, c⁆ ≠ 1 := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  let : Fact (HasExponentThree M) := ⟨hG⟩
  let : Nontrivial M := nontrivial hM
  let H := Coproduct M (Free (Fin 2))
  let a₁ : Layer M 1 := mk M 1 ⟨a, Subgroup.mem_top _⟩
  have ha₁ : a₁ ≠ 0 := fun h => ha ((mk_eq_zero M 1 _).mp h)
  have haH : mapLayer (Coproduct.inl (H := Free (Fin 2))) 1 a₁ ≠ 0 := by
    intro h
    apply ha₁
    have h' := congrArg (mapLayer (Coproduct.fst (H := Free (Fin 2)) hG) 1) h
    simpa only [Coproduct.mapLayer_fst_inl, map_zero] using h'
  obtain ⟨b, c, hbc⟩ := Coproduct.FreeTwoSeparation.exists_triple_bracket_ne_zero _ haH
  obtain ⟨b, rfl⟩ := mk_surjective H 1 b
  obtain ⟨c, rfl⟩ := mk_surjective H 1 c
  have hword : ⁅⁅Coproduct.inl (H := Free (Fin 2)) a, (b : H)⁆, (c : H)⁆ ≠ 1 := by
    intro h
    apply hbc
    rw [mapLayer_mk, bracketLayer_mk, bracketLayer_mk, mk_eq_zero]
    change ⁅⁅Coproduct.inl (H := Free (Fin 2)) a, (b : H)⁆, (c : H)⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries 3
    rw [h]
    exact Subgroup.one_mem _
  exact exists_triple_commutator_ne_one_of_extension hM (N := H) Coproduct.pow_three
    Coproduct.inl (Coproduct.inl_injective hG) a (b : H) (c : H) hword

/-- A derived element outside the third lower term is detected by a commutator.
The nonzero degree-two bracket in `M ∐ F₂` supplies the witness before e.c. transfer.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, line 1209.
-/
theorem exists_commutator_ne_one (a : M) (ha : a ∈ commutator M)
    (ha₃ : a ∉ (⊤ : Subgroup M).lowerCentralSeries 2) : ∃ b : M, ⁅a, b⁆ ≠ 1 := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  let : Fact (HasExponentThree M) := ⟨hG⟩
  let : Nontrivial M := nontrivial hM
  let H := Coproduct M (Free (Fin 2))
  let a₂ : Layer M 2 := mk M 2 ⟨a, ha⟩
  have ha₂ : a₂ ≠ 0 := fun h => ha₃ ((mk_eq_zero M 2 _).mp h)
  have haH : mapLayer (Coproduct.inl (H := Free (Fin 2))) 2 a₂ ≠ 0 := by
    intro h
    apply ha₂
    have h' := congrArg (mapLayer (Coproduct.fst (H := Free (Fin 2)) hG) 2) h
    simpa only [Coproduct.mapLayer_fst_inl, map_zero] using h'
  obtain ⟨b, hb⟩ := Coproduct.FreeTwoSeparation.exists_bracket_ne_zero _ haH
  obtain ⟨b, rfl⟩ := mk_surjective H 1 b
  have hword : ⁅Coproduct.inl (H := Free (Fin 2)) a, (b : H)⁆ ≠ 1 := by
    intro h
    apply hb
    rw [mapLayer_mk, bracketLayer_mk, mk_eq_zero]
    change ⁅Coproduct.inl (H := Free (Fin 2)) a, (b : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 3
    rw [h]
    exact Subgroup.one_mem _
  exact exists_commutator_ne_one_of_extension hM (N := H) Coproduct.pow_three
    Coproduct.inl (Coproduct.inl_injective hG) a (b : H) hword

/-- The upper and lower central series of an existentially closed `T₃` model coincide in
reverse order. No nontriviality assumption is added to existential closedness.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1186–1187 and 1204–1209.
-/
theorem centralSeriesCoincide : CentralSeriesCoincide M := by
  have hG : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  have hsecond : Subgroup.upperCentralSeries M 2 ≤ commutator M := by
    intro a ha
    by_contra hnot
    obtain ⟨b, c, hbc⟩ := exists_triple_commutator_ne_one hM a hnot
    have hab : ⁅a, b⁆ ∈ Subgroup.center M := by
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp ha) b
    exact hbc (commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hab) c).symm)
  have hcenter : Subgroup.center M ≤ (⊤ : Subgroup M).lowerCentralSeries 2 := by
    intro a ha
    have ha' : a ∈ Subgroup.upperCentralSeries M 1 := by
      simpa only [Subgroup.upperCentralSeries_one] using ha
    have haD := hsecond (Subgroup.upperCentralSeries_mono M (by decide : 1 ≤ 2) ha')
    by_contra hnot
    obtain ⟨b, hb⟩ := exists_commutator_ne_one hM a haD hnot
    exact hb (commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp ha) b).symm)
  exact (centralSeriesCoincide_iff hG).mpr
    ⟨le_antisymm (commutator_le_upperCentralSeries_two hG) hsecond,
      le_antisymm (lowerCentralSeries_two_le_center hG) hcenter⟩

/-- The third lower central term is exactly the set of single triple commutators.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1192–1194.
-/
theorem lowerCentralSeries_two_eq_setOf_triple_commutator :
    ((⊤ : Subgroup M).lowerCentralSeries 2 : Set M) = {a | ∃ x y z : M, a = ⁅⁅x, y⁆, z⁆} := by
  ext a
  constructor
  · exact exists_triple_commutator hM a
  · rintro ⟨x, y, z, rfl⟩
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      (Subgroup.mem_top z)

/-- The derived subgroup is exactly the set of single commutators.

Paper-ID: structure.ec_central_series
TeX: T3_modelcompanion_v4.tex, Proposition 4.11, lines 1189–1191.
-/
theorem commutator_eq_setOf_commutator :
    (commutator M : Set M) = {a | ∃ x y : M, a = ⁅x, y⁆} := by
  ext a
  constructor
  · exact exists_commutator hM a
  · rintro ⟨x, y, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

end T3.ExistentiallyClosedGroups
