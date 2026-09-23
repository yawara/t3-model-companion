/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Collection and intersections of subgroup images

An element of a join of two subgroups splits into an element of each subgroup and an element
of the derived subgroup of the join. A homomorphism preserves the intersection of two
subgroups when one contains its kernel. Both statements hold for arbitrary groups.

Paper-ID: structure.derived_strictification, structure.lcs_strictification
TeX: T3_modelcompanion_v8.tex, `lemma:commutator root`, lines 1182–1187, and
`lemma:number of generators for triple commutator roots`, lines 1240–1255.
-/

@[expose] public section

namespace Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- Modulo the derived subgroup of their join, an element splits into one factor from
each of the two subgroups.

Paper-ID: structure.derived_strictification
TeX: T3_modelcompanion_v8.tex, `lemma:commutator root`, lines 1182–1187.
-/
theorem exists_mul_mul_commutator_of_mem_sup (A B : Subgroup G) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ k ∈ ⁅A ⊔ B, A ⊔ B⁆, g = a * b * k := by
  classical
  let C : Subgroup G := A ⊔ B
  have hcomm : (_root_.commutator C).map C.subtype = ⁅C, C⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hsup : A.subgroupOf C ⊔ B.subgroupOf C = ⊤ := by
    apply map_injective (f := C.subtype) Subtype.val_injective
    rw [map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype, inf_eq_left.mpr le_sup_left,
      inf_eq_left.mpr le_sup_right]
  have htop : (A.subgroupOf C).map (Abelianization.of (G := C)) ⊔
      (B.subgroupOf C).map (Abelianization.of (G := C)) = ⊤ := by
    rw [← map_sup, hsup, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk_surjective
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    mem_sup.mp (htop ▸ mem_top (Abelianization.of (⟨g, hg⟩ : C)))
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hy
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hz
  have hker : (a * b)⁻¹ * (⟨g, hg⟩ : C) ∈ _root_.commutator C := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hyz,
      inv_mul_cancel]
  refine ⟨(a : G), ha, (b : G), hb, ((a * b)⁻¹ * (⟨g, hg⟩ : C) : C), ?_, ?_⟩
  · rw [← hcomm]
    exact mem_map_of_mem _ hker
  · have heq : ((a * b) * ((a * b)⁻¹ * (⟨g, hg⟩ : C)) : C) = (⟨g, hg⟩ : C) := by
      rw [mul_inv_cancel_left]
    exact congrArg (Subtype.val (p := fun x => x ∈ C)) heq.symm

/-- A homomorphism preserves the intersection when the right subgroup contains its kernel.
Neither injectivity nor surjectivity is required, and the left subgroup need not contain
the kernel.

Paper-ID: structure.lcs_strictification
TeX: T3_modelcompanion_v8.tex, `lemma:number of generators for triple commutator roots`,
lines 1240–1255.
-/
theorem map_inf_of_ker_le {f : G →* H} {U V : Subgroup G} (hV : f.ker ≤ V) :
    (U ⊓ V).map f = U.map f ⊓ V.map f := by
  refine le_antisymm (map_inf_le U V f) ?_
  intro x hx
  obtain ⟨hxU, hxV⟩ := mem_inf.mp hx
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hxU
  obtain ⟨v, hv, hveq⟩ := mem_map.mp hxV
  refine mem_map_of_mem _ (mem_inf.mpr ⟨hu, ?_⟩)
  have hker : v⁻¹ * u ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hveq, inv_mul_cancel]
  have heq : u = v * (v⁻¹ * u) := by simp
  rw [heq]
  exact V.mul_mem hv (hV hker)

end Subgroup
