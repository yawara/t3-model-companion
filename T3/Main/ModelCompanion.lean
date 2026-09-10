/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.Main.BoundedWitness
public import T3.ModelTheory.GroupAmalgamation

/-!
# Existence of the model companion

The group-theoretic bounded witness supplies the hypothesis of the general finite-language,
locally finite, Pi-two amalgamation criterion. Finite structures embeddable in `T₃` inherit
the group and exponent laws by universality. The common base is identified with its actual
image in the existentially closed model before applying the bounded-witness theorem.

These conclusions use the canonical semantic universe documented in the model-theory modules.

Paper-ID: main.model_companion
TeX: T3_modelcompanion_v4.tex, Corollary 3.4, lines 742–745.
-/

@[expose] public section

namespace T3

open FirstOrder FirstOrder.Language FirstOrder.Group

private theorem generatedByAtMost_of_rank_le {M : Type*} [Group M] [CompatibleGroup M]
    (D : Subgroup M) [Group.FG D] {n : ℕ} (hn : Group.rank D ≤ n) :
    (subgroupToSubstructure D).GeneratedByAtMost n := by
  classical
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec D
  refine ⟨s.image D.subtype, Finset.card_image_le.trans (hcard.le.trans hn), ?_⟩
  apply SetLike.coe_injective
  rw [coe_substructure_closure_eq, Finset.coe_image, ← MonoidHom.map_closure, hs,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

/-- The exact group-theoretic witness bound verifies the general obstruction criterion for `T₃`.
The finite structures in the criterion receive their group laws from their embeddings.

Paper-ID: main.model_companion
TeX: T3_modelcompanion_v4.tex, applying Fact 2.6 after Theorem 3.3, line 742.
-/
theorem exponentThreeTheory_boundedAmalgamationObstructions :
    exponentThreeTheory.BoundedAmalgamationObstructions := by
  classical
  intro d
  obtain ⟨N, ⟨e⟩⟩ := d.embeddable
  let : d.ext ⊨ exponentThreeTheory := Theory.IsUniversal.models_of_embedding e
  let : d.ext ⊨ Theory.group := (inferInstance : d.ext ⊨ exponentThreeTheory).mono
    (fun _ h => Set.mem_insert_of_mem _ h)
  let : Group d.ext := groupOfModelGroup d.ext
  let : CompatibleGroup d.ext := compatibleGroupOfGroupStructure d.ext
  let : d.base ⊨ Theory.group := Theory.IsUniversal.models_of_embedding d.incl
  let : Group d.base := groupOfModelGroup d.base
  let : CompatibleGroup d.base := compatibleGroupOfGroupStructure d.base
  refine ⟨witnessBound (Group.rank d.ext), ?_⟩
  intro M hM j hna
  let : M ⊨ Theory.group := (inferInstance : M ⊨ exponentThreeTheory).mono
    (fun _ h => Set.mem_insert_of_mem _ h)
  let : Group M := groupOfModelGroup M
  let : CompatibleGroup M := compatibleGroupOfGroupStructure M
  let ι := embeddingToMonoidHom j
  let A := ι.range
  let q : d.base ≃* A := MonoidHom.ofInjective j.injective
  let k := embeddingToMonoidHom d.incl
  let jB : A →* d.ext := k.comp q.symm.toMonoidHom
  have hjB : Function.Injective jB := d.incl.injective.comp q.symm.injective
  have hbase : jB.comp q.toMonoidHom = k := by ext a; simp [jB]
  have himage : A.subtype.comp q.toMonoidHom = ι := by ext a; rfl
  have hnaA : ¬ Amalgamation.AmalgamableOver A.subtype jB := by
    intro ham
    have h := Amalgamation.AmalgamableOver.precomp A.subtype jB q.toMonoidHom ham
    rw [hbase, himage] at h
    exact hna ((GroupAmalgamation.amalgamableOver_embeddings_swap_iff d.incl j).mpr h)
  obtain ⟨D, hD, hAD, hbound, hbad⟩ := exists_bounded_nonamalgamation_witness hM A
    (exponentThreeTheory_model_iff.mp (inferInstance : d.ext ⊨ exponentThreeTheory))
    jB hjB le_rfl hnaA
  let : Group.FG D := hD
  let C := subgroupToSubstructure D
  have hjC : ∀ a, j a ∈ C := fun a => hAD ⟨a, rfl⟩
  refine ⟨C, hjC, generatedByAtMost_of_rank_le D hbound, ?_⟩
  intro ham
  let : C ⊨ Theory.group := Theory.IsUniversal.models_of_embedding C.subtype
  let : Group C := groupOfModelGroup C
  let : CompatibleGroup C := compatibleGroupOfGroupStructure C
  let eD : D →* C :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := by
        apply Subtype.ext
        exact (CompatibleGroup.funMap_one (G := M) _).symm
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (x : M) * (y : M) = Structure.funMap mulFunc _
        rw [CompatibleGroup.funMap_mul]
        rfl }
  have heD : Function.Injective eD := fun _ _ h => Subtype.ext (congrArg Subtype.val h)
  have h := (GroupAmalgamation.amalgamableOver_embeddings_swap_iff
    d.incl (j.codRestrict C hjC)).mp ham
  obtain ⟨K, hK, hpow, iC, iB, hiC, hiB, hij⟩ := h
  let : Group K := hK
  apply hbad
  refine ⟨K, hK, hpow, iC.comp eD, iB, hiC.comp heD, hiB, ?_⟩
  apply MonoidHom.ext
  intro a
  have hea : eD (Subgroup.inclusion hAD a) =
      embeddingToMonoidHom (j.codRestrict C hjC) (q.symm a) := by
    apply Subtype.ext
    exact (MonoidHom.apply_ofInjective_symm j.injective a).symm
  exact (congrArg iC hea).trans (DFunLike.congr_fun hij (q.symm a))

/-- The theory of groups of exponent three has a model companion.

Paper-ID: main.model_companion
TeX: T3_modelcompanion_v4.tex, Corollary 3.4, lines 743–745.
-/
theorem has_model_companion : exponentThreeTheory.HasModelCompanion :=
  exponentThreeTheory_hasModelCompanion_of_boundedAmalgamationObstructions
    exponentThreeTheory_boundedAmalgamationObstructions

end T3
