/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Burnside
public import T3.ModelTheory.ExponentThree
public import T3.ModelTheory.LocallyFinite.Universes

/-!
# The Burnside formulation of local finiteness

The usual group theory with the exponent law is locally finite exactly when its free
Burnside groups of all positive finite ranks are finite. This is the established equivalence
used to interpret Conjecture 1.1 in the v8 introduction. Its detailed source remains the
archived v7 Section 6, which is disabled in v8. Neither implication between local finiteness
and the existence of a model companion is asserted here for a general exponent.

Paper-ID: questions.burnside_local_finiteness
TeX: archives/T3_modelcompanion_v7.tex, Section 6, lines 1520–1525.
-/

@[expose] public section

open scoped FirstOrder

namespace T3

open FirstOrder FirstOrder.Language

/-- Finiteness of finite-rank Burnside groups makes every finitely generated subgroup of any
group of that exponent finite.

Paper-ID: questions.burnside_local_finiteness
TeX: archives/T3_modelcompanion_v7.tex, Section 6, lines 1522–1525.
-/
theorem finite_closure_of_finite_burnside {n : ℕ}
    (hfree : ∀ r : ℕ, 0 < r → Finite (Burnside n (Fin r)))
    {G : Type*} [Group G] (hG : ∀ x : G, x ^ n = 1)
    {s : Set G} (hs : s.Finite) : Finite (Subgroup.closure s) := by
  let : Group.FG (Subgroup.closure s) :=
    (Group.fg_iff_subgroup_fg _).mpr ((Subgroup.fg_iff _).mpr ⟨s, rfl, hs⟩)
  exact Burnside.finite_of_fg hfree fun x => Subtype.ext (hG x)

/-- Local finiteness of the exponent theory is equivalent to finiteness of every positive
finite-rank free Burnside group. The statement uses the ordinary first-order group language.

Paper-ID: questions.burnside_local_finiteness
TeX: archives/T3_modelcompanion_v7.tex, Section 6, lines 1520–1525.
-/
theorem exponentGroupTheory_isLocallyFinite_iff_finite_burnside (n : ℕ) :
    (exponentGroupTheory n).IsLocallyFinite ↔
      ∀ r : ℕ, 0 < r → Finite (Burnside n (Fin r)) := by
  constructor
  · intro hT r _
    let G := Burnside n (Fin r)
    let : FirstOrder.Group.CompatibleGroup G := FirstOrder.Group.compatibleGroupOfGroup G
    let : G ⊨ exponentGroupTheory n :=
      (exponentGroupTheory_model_iff n).mpr Burnside.pow_exponent
    have hfinite := hT.finite_closure G (Set.range (Burnside.of : Fin r → G))
      (Set.finite_range _)
    have hfinite' : Finite (Subgroup.closure (Set.range (Burnside.of : Fin r → G))) :=
      Finite.of_equiv (Substructure.closure Language.group (Set.range (Burnside.of : Fin r → G)))
        (Set.equivOfEq (FirstOrder.Group.coe_substructure_closure_eq _))
    rw [Burnside.closure_range_of] at hfinite'
    exact Finite.of_equiv (⊤ : Subgroup G) (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
  · intro hfree M s hs
    let : M ⊨ Theory.group :=
      (inferInstance : M ⊨ exponentGroupTheory n).mono (fun _ h => Set.mem_insert_of_mem _ h)
    let : Group M := FirstOrder.Group.groupOfModelGroup M
    let : FirstOrder.Group.CompatibleGroup M :=
      FirstOrder.Group.compatibleGroupOfGroupStructure M
    have hpow : ∀ x : M, x ^ n = 1 :=
      (exponentGroupTheory_model_iff n).mp (inferInstance : M ⊨ exponentGroupTheory n)
    let := finite_closure_of_finite_burnside hfree hpow hs
    exact Finite.of_equiv (Subgroup.closure s)
      (Set.equivOfEq (FirstOrder.Group.coe_substructure_closure_eq s)).symm

end T3
