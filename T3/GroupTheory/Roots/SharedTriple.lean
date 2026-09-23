/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Roots.CentralRelations
public import T3.GroupTheory.Roots.SharedTripleCoordinates

/-!
# Four triple roots sharing four generators

The four increasing triples of the same four free generators provide independent central
coordinates. Quotienting the direct product by the four indicated root relations preserves
the base group and supplies all four root equations.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267.
-/

@[expose] public noncomputable section

open scoped commutatorElement

namespace T3.SharedTripleRoots

open AssociatedGraded

variable {G : Type*} [Group G]

/-- The four increasing triples on four generators, in the paper's lexicographic order.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1266.
-/
def tripleIndex (i : Fin 4) : IncreasingTriple (Fin 4) :=
  ![⟨0, 1, 2, by decide, by decide⟩, ⟨0, 1, 3, by decide, by decide⟩,
    ⟨0, 2, 3, by decide, by decide⟩, ⟨1, 2, 3, by decide, by decide⟩] i

private theorem tripleIndex_injective : Function.Injective tripleIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tripleIndex, IncreasingTriple.ext_iff]

/-- The shared triple commutator realizing one prescribed root.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1265–1266.
-/
def witness (i : Fin 4) : Free (Fin 4) :=
  ⁅⁅Free.of (tripleIndex i).first, Free.of (tripleIndex i).second⁆,
    Free.of (tripleIndex i).third⁆

/-- The four shared triples are independent in the actual third graded quotient.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1265.
-/
theorem independent : LinearIndependent (ZMod 3)
    (fun i : Fin 4 => mk (Free (Fin 4)) 3 (SharedTriple.triple (tripleIndex i))) :=
  SharedTriple.independent.comp tripleIndex tripleIndex_injective

/-- Each shared witness is central.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, the same construction as Lemma 4.9.
-/
theorem witness_mem_center (i : Fin 4) : witness i ∈ Subgroup.center (Free (Fin 4)) :=
  T3.commutator_mem_center_of_mem_commutator Free.pow_three
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _

/-- The shared root relator, with the prescribed inverse on the base element.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1266.
-/
def relator (z : Fin 4 → G) (i : Fin 4) : G × Free (Fin 4) := ((z i)⁻¹, witness i)

/-- The four simultaneous shared-root relations.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1266.
-/
def kernel (z : Fin 4 → G) : Subgroup (G × Free (Fin 4)) :=
  Subgroup.normalClosure (Set.range (relator z))

instance kernel_normal (z : Fin 4 → G) : (kernel z).Normal := Subgroup.normalClosure_normal

/-- The relators are central, so their normal closure is their ordinary generated subgroup.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1266.
-/
theorem kernel_eq_closure (z : Fin 4 → G) (hz : ∀ i, z i ∈ Subgroup.center G) :
    kernel z = Subgroup.closure (Set.range (relator z)) :=
  CentralRootRelations.normalClosure_eq_closure (term (Free (Fin 4)) 3)
    (lowerCentralSeries_two_le_center Free.pow_three) z hz
    (fun i => SharedTriple.triple (tripleIndex i))

private def coordinate (i : Fin 4) : term (Free (Fin 4)) 3 →* Multiplicative (ZMod 3) where
  toFun x := Multiplicative.ofAdd ((Free.tripleFinsuppReadout x).toAdd (tripleIndex i))
  map_one' := by
    change Multiplicative.ofAdd ((Free.tripleFinsuppReadout 1).toAdd (tripleIndex i)) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((Free.tripleFinsuppReadout (x * y)).toAdd (tripleIndex i)) = _
    rw [map_mul]
    rfl

private theorem coordinate_witness (i j : Fin 4) :
    coordinate i (SharedTriple.triple (tripleIndex j)) =
      Multiplicative.ofAdd (if i = j then 1 else 0) := by
  apply Multiplicative.toAdd.injective
  change (Free.tripleFinsuppReadout (SharedTriple.triple (tripleIndex j))).toAdd
    (tripleIndex i) = if i = j then 1 else 0
  have h := congrArg (fun f : IncreasingTriple (Fin 4) →₀ ZMod 3 => f (tripleIndex i))
    (Free.layerThreeEquiv_tripleCommutator (tripleIndex j))
  simpa only [Free.layerThreeEquiv_mk, SharedTriple.triple,
    Finsupp.single_apply, tripleIndex_injective.eq_iff, eq_comm] using h

/-- No nontrivial base element is killed by the four shared-root relations.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, line 1266, applying the Lemma 4.9 argument.
-/
theorem eq_one_of_inl_mem_kernel (hG : HasExponentThree G) (z : Fin 4 → G)
    (hz : ∀ i, z i ∈ Subgroup.center G) {g : G}
    (hg : MonoidHom.inl G (Free (Fin 4)) g ∈ kernel z) : g = 1 :=
  CentralRootRelations.eq_one_of_inl_mem_normalClosure (term (Free (Fin 4)) 3)
    (lowerCentralSeries_two_le_center Free.pow_three) z hz
    (fun i => SharedTriple.triple (tripleIndex i)) hG Free.pow_three coordinate
    coordinate_witness hg

/-- The paper's quotient of the direct product by the simultaneous triple root relations.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
abbrev Extension (z : Fin 4 → G) :=
  (G × Free (Fin 4)) ⧸ kernel z

/-- The canonical map from the original group to the simultaneous root extension.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
def baseMap (z : Fin 4 → G) : G →* Extension z :=
  (QuotientGroup.mk' (kernel z)).comp (MonoidHom.inl G _)

/-- The four free generators shared by all four prescribed roots.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
def generator (z : Fin 4 → G) (j : Fin 4) : Extension z :=
  (QuotientGroup.mk' (kernel z)) (MonoidHom.inr G _ (Free.of j))

/-- The simultaneous root extension again has exponent dividing three.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
theorem hasExponentThree_extension (hG : HasExponentThree G) (z : Fin 4 → G) :
    HasExponentThree (Extension z) := by
  let : Fact (HasExponentThree G) := ⟨hG⟩
  exact Fact.out

/-- The natural map into the paper's concrete simultaneous root quotient has trivial kernel.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
theorem baseMap_ker (hG : HasExponentThree G) (z : Fin 4 → G)
    (hz : ∀ i, z i ∈ Subgroup.center G) : (baseMap z).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply eq_one_of_inl_mem_kernel hG z hz
  exact (QuotientGroup.eq_one_iff _).mp hg

/-- Adjoining the finite central family of triple roots simultaneously preserves the base group.

There is no nontriviality or rank assumption on `G`, nor any independence assumption on `z`.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
theorem baseMap_injective (hG : HasExponentThree G) (z : Fin 4 → G)
    (hz : ∀ i, z i ∈ Subgroup.center G) : Function.Injective (baseMap z) :=
  (MonoidHom.ker_eq_bot_iff _).mp (baseMap_ker hG z hz)

/-- Each designated base element becomes its prescribed triple commutator in the quotient.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v8.tex, Remark 4.11, lines 1263–1267. -/
theorem baseMap_root (z : Fin 4 → G) (i : Fin 4) :
    baseMap z (z i) =
      ⁅⁅generator z (tripleIndex i).first, generator z (tripleIndex i).second⁆,
        generator z (tripleIndex i).third⁆ := by
  change (QuotientGroup.mk' (kernel z)) (MonoidHom.inl G _ (z i)) =
    ⁅⁅(QuotientGroup.mk' (kernel z)) (MonoidHom.inr G _ (Free.of ((tripleIndex i).first))),
      (QuotientGroup.mk' (kernel z)) (MonoidHom.inr G _ (Free.of ((tripleIndex i).second)))⁆,
      (QuotientGroup.mk' (kernel z)) (MonoidHom.inr G _ (Free.of ((tripleIndex i).third)))⁆
  rw [← map_commutatorElement, ← map_commutatorElement, ← map_commutatorElement,
    ← map_commutatorElement]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h : (MonoidHom.inl G (Free (Fin 4)) (z i))⁻¹ *
      MonoidHom.inr G _ (witness i) = relator z i := by
    simp only [MonoidHom.inl_apply, MonoidHom.inr_apply, Prod.inv_mk,
      Prod.mk_mul_mk, inv_one, mul_one, one_mul, relator]
  change (MonoidHom.inl G (Free (Fin 4)) (z i))⁻¹ *
    MonoidHom.inr G _ (witness i) ∈ kernel z
  rw [h]
  exact Subgroup.subset_normalClosure ⟨i, rfl⟩

end T3.SharedTripleRoots
