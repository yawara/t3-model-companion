/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Support

/-!
# Transport of an internal normal-closure certificate

A certificate in the normal closure computed inside a subgroup remains valid in any larger
subgroup. If that subgroup lies in the range of an injective homomorphism, the certificate
pulls back, including its conjugating elements. No exponent or finiteness assumption is needed.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, the passage from `H₀` to `D ∐ B`, line 738.
-/

@[expose] public section

namespace T3.Support

variable {G H : Type*} [Group G] [Group H]

/-- Enlarging the subgroup in which a normal closure is computed preserves its certificate.
The relators need not all belong to the smaller subgroup.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, the inclusion of `H₀` in the smaller coproduct.
-/
theorem normalClosureIn_mono_ambient {E F : Subgroup H} (hEF : E ≤ F) (Δ : Set H) :
    normalClosureIn E Δ ≤ normalClosureIn F Δ := by
  let j := Subgroup.inclusion hEF
  have hle : Subgroup.normalClosure (E.subtype ⁻¹' Δ) ≤
      (Subgroup.normalClosure (F.subtype ⁻¹' Δ)).comap j := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.subset_normalClosure hx
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨j x, hle hx, rfl⟩

/-- A certificate supported inside the image of an embedding pulls back to the normal closure
of the inverse-image relators. The embedding's inverse on its range also lifts the conjugators.

Paper-ID: main.bounded_witness
TeX: T3_modelcompanion_v4.tex, `thm:main`, the certificate in `D ∐ B` on line 738.
-/
theorem mem_normalClosure_of_mem_normalClosureIn (f : G →* H) (hf : Function.Injective f)
    (E : Subgroup H) (hE : E ≤ f.range) (Δ : Set H) {x : G}
    (hx : f x ∈ normalClosureIn E Δ) : x ∈ Subgroup.normalClosure (f ⁻¹' Δ) := by
  classical
  let j : E →* G := (MonoidHom.ofInjective hf).symm.toMonoidHom.comp (Subgroup.inclusion hE)
  have hj (y : E) : f (j y) = y := MonoidHom.apply_ofInjective_symm hf _
  have hle : Subgroup.normalClosure (E.subtype ⁻¹' Δ) ≤
      (Subgroup.normalClosure (f ⁻¹' Δ)).comap j := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    apply Subgroup.subset_normalClosure
    change f (j y) ∈ Δ
    rw [hj]
    exact hy
  obtain ⟨y, hy, heq⟩ := hx
  have hxy : j y = x := hf ((hj y).trans heq)
  simpa only [Subgroup.mem_comap, hxy] using hle hy

end T3.Support
