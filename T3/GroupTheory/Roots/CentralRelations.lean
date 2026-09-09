/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Roots.Triple

/-!
# Independent central coordinates for shared root relations

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/

@[expose] public section

namespace T3.CentralRootRelations

variable {G K I : Type*} [Group G] [Group K]
  (S : Subgroup K) (hS : S ≤ Subgroup.center K)
  (z : I → G) (hz : ∀ i, z i ∈ Subgroup.center G) (w : I → S)

/-- The simultaneous central relation identifying one base element with its witness.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
def relator (i : I) : G × K := ((z i)⁻¹, w i)

include hS hz in
/-- The simultaneous relation is central in the direct product.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
theorem relator_mem_center (i : I) : relator S z w i ∈ Subgroup.center (G × K) := by
  rw [Subgroup.mem_center_iff]
  intro a
  exact Prod.ext (Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem (hz i)) a.1)
    (Subgroup.mem_center_iff.mp (hS (w i).property) a.2)

include hS hz in
/-- Central relations generate a normal subgroup without further conjugates.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
theorem normalClosure_eq_closure :
    Subgroup.normalClosure (Set.range (relator S z w)) =
      Subgroup.closure (Set.range (relator S z w)) := by
  have hc : Subgroup.closure (Set.range (relator S z w)) ≤ Subgroup.center _ :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact relator_mem_center S hS z hz w i)
  haveI : (Subgroup.closure (Set.range (relator S z w))).Normal := by
    constructor
    intro a ha g
    rw [Subgroup.mem_center_iff.mp (hc ha) g, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  exact le_antisymm (Subgroup.normalClosure_le_normal Subgroup.subset_closure)
    Subgroup.closure_le_normalClosure

/-- The central subgroup of the product whose second coordinate lies in the witness subgroup.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
def relationAmbient : Subgroup (G × K) := Subgroup.center _ ⊓ S.comap (MonoidHom.snd G K)

/-- The central relation ambient subgroup is commutative.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
instance : CommGroup (relationAmbient (G := G) S) :=
  { (inferInstance : Group (relationAmbient (G := G) S)) with
    mul_comm a b := Subtype.ext (Subgroup.mem_center_iff.mp b.property.1 a) }

/-- The simultaneous relation bundled in its commutative ambient subgroup.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
def bundledRelator (i : I) : relationAmbient (G := G) S :=
  ⟨relator S z w i, relator_mem_center S hS z hz w i, (w i).property⟩

variable [Fintype I]

/-- The product of simultaneous relations with specified integer exponents.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
def relationWord (m : I → ℤ) : relationAmbient (G := G) S :=
  ∏ i, bundledRelator S hS z hz w i ^ m i

/-- Every element of the relation subgroup is a product with integer exponents.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
theorem exists_relationWord {a : G × K}
    (ha : a ∈ Subgroup.normalClosure (Set.range (relator S z w))) :
    ∃ m : I → ℤ, (relationWord S hS z hz w m : G × K) = a := by
  classical
  rw [normalClosure_eq_closure S hS z hz w] at ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    refine ⟨Pi.single i 1, ?_⟩
    simp [relationWord, Pi.single_apply, bundledRelator]
  | one => exact ⟨0, by simp [relationWord]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hb
    refine ⟨m + k, ?_⟩
    simp only [relationWord, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Subgroup.coe_mul]
  | inv a _ ha =>
    obtain ⟨m, rfl⟩ := ha
    refine ⟨-m, ?_⟩
    simp only [relationWord, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, Subgroup.coe_inv]

/-- The second-coordinate homomorphism from the relation ambient subgroup.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
def projection : relationAmbient (G := G) S →* S :=
  ((MonoidHom.snd G K).comp (relationAmbient (G := G) S).subtype).codRestrict S
    (fun x => x.property.2)

/-- Independent witness coordinates recover each exponent modulo three.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
theorem coordinate_relationWord [DecidableEq I] (c : I → S →* Multiplicative (ZMod 3))
    (hc : ∀ i j, c i (w j) = Multiplicative.ofAdd (if i = j then 1 else 0))
    (m : I → ℤ) (i : I) :
    c i (projection S (relationWord S hS z hz w m)) = Multiplicative.ofAdd (m i : ZMod 3) := by
  classical
  change ((c i).comp (projection S)) (relationWord S hS z hz w m) = _
  rw [relationWord, map_prod]
  simp only [map_zpow, MonoidHom.comp_apply]
  have hproj (j : I) : projection S (bundledRelator S hS z hz w j) = w j := rfl
  simp only [hproj, hc]
  rw [Finset.prod_eq_single i]
  · simp [← ofAdd_zsmul, zsmul_eq_mul]
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

omit [Fintype I] in
include hS hz in
/-- Independent central witness coordinates ensure that the relations kill no base element.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v4.tex, Remark 4.10, lines 1177–1181.
-/
theorem eq_one_of_inl_mem_normalClosure [Finite I] [DecidableEq I]
    (hG : HasExponentThree G) (hK : HasExponentThree K)
    (c : I → S →* Multiplicative (ZMod 3))
    (hc : ∀ i j, c i (w j) = Multiplicative.ofAdd (if i = j then 1 else 0)) {g : G}
    (hg : MonoidHom.inl G K g ∈ Subgroup.normalClosure (Set.range (relator S z w))) : g = 1 := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨m, hm⟩ := exists_relationWord S hS z hz w hg
  have hcoeff (i : I) : (m i : ZMod 3) = 0 := by
    have hp : projection S (relationWord S hS z hz w m) = 1 := by
      apply Subtype.ext
      exact congrArg Prod.snd hm
    have hc' := coordinate_relationWord S hS z hz w c hc m i
    rw [hp, map_one] at hc'
    exact ofAdd_eq_one.mp hc'.symm
  have hword : relationWord S hS z hz w m = 1 := by
    apply Finset.prod_eq_one
    intro i _
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (m i) 3).mp (hcoeff i)
    norm_num at hk
    rw [hk, zpow_mul]
    have hcube : bundledRelator S hS z hz w i ^ (3 : ℤ) = 1 := by
      apply Subtype.ext
      change ((z i)⁻¹, (w i : K)) ^ (3 : ℤ) = (1 : G × K)
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact Prod.ext (by change ((z i)⁻¹) ^ 3 = 1; rw [inv_pow, hG (z i), inv_one])
        (hK (w i))
    rw [hcube, one_zpow]
  have h := congrArg Prod.fst hm
  simpa only [hword, Subgroup.coe_one, Prod.fst_one, MonoidHom.inl_apply] using h.symm

end T3.CentralRootRelations
