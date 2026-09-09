/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Linear maps induced on block quotients

A commutative square of surjective quotient maps transports a linear isomorphism precisely
when its kernels correspond. The tensor-product kernel is expressed as the sum of the two
relation subspaces. These formulations keep the canonical maps when passing from the free
exterior decomposition to a coproduct of presented groups.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, proof lines 898–926.
-/

@[expose] public section

namespace LinearMap

variable {R A B C D : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- An isomorphism descends through two surjections when it maps one kernel onto the other.
The resulting bijection is the given map making the square commute.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, block quotient identifications.
-/
theorem bijective_of_bijective_of_ker_map
    (u : A →ₗ[R] B) (p : A →ₗ[R] C) (q : B →ₗ[R] D) (v : C →ₗ[R] D)
    (hu : Function.Bijective u) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hsquare : q.comp u = v.comp p) (hker : q.ker = p.ker.map u) :
    Function.Bijective v := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    obtain ⟨a, rfl⟩ := hp x
    have ha : u a ∈ q.ker := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hsquare]
      exact hx
    rw [hker] at ha
    obtain ⟨b, hb, hab⟩ := ha
    have hba : b = a := hu.injective hab
    subst b
    exact hb
  · intro y
    obtain ⟨b, rfl⟩ := hq y
    obtain ⟨a, rfl⟩ := hu.surjective b
    exact ⟨p a, (DFunLike.congr_fun hsquare a).symm⟩

end LinearMap

namespace TensorProduct

variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- Tensoring two quotient maps kills exactly the sum of the two tensor relation subspaces.
No finite-dimensionality or flatness hypothesis is required.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, tensor quotients, lines 916–926.
-/
theorem map_ker_eq_map₂ (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (map f g).ker = Submodule.map₂ (mk R A B) f.ker ⊤ ⊔
      Submodule.map₂ (mk R A B) ⊤ g.ker := by
  rw [map_ker f.exact_subtype_ker_map hf g.exact_subtype_ker_map hg]
  simp only [LinearMap.lTensor, LinearMap.rTensor, range_map,
    LinearMap.range_id, Submodule.range_subtype]
  exact sup_comm _ _

end TensorProduct
