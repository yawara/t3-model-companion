/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Graded
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Independent central coordinates for shared root relations

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v7.tex, Remark 4.11, lines 1258–1262.
-/

@[expose] public section

open scoped commutatorElement

namespace T3.SharedTriple

/-- The increasing triple commutator as an element of the actual third central term.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v7.tex, Remark 4.11, lines 1258–1262.
-/
def triple (t : IncreasingTriple (Fin 4)) : AssociatedGraded.term (Free (Fin 4)) 3 :=
  ⟨⁅⁅Free.of t.first, Free.of t.second⁆, Free.of t.third⁆,
    Free.commutator_mem_gammaThree
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _⟩

/-- The four increasing triple initial forms are linearly independent in the actual third quotient.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v7.tex, Remark 4.11, lines 1258–1262.
-/
theorem independent : LinearIndependent (ZMod 3)
    (fun t : IncreasingTriple (Fin 4) => AssociatedGraded.mk (Free (Fin 4)) 3 (triple t)) := by
  convert (Module.Basis.ofRepr (Free.layerThreeEquiv (I := Fin 4))).linearIndependent using 1
  funext t
  apply Free.layerThreeEquiv.injective
  simpa only [triple, Module.Basis.coe_ofRepr, LinearEquiv.apply_symm_apply] using
    Free.layerThreeEquiv_tripleCommutator t

/-- There are exactly four increasing triples on four generator indices.

Paper-ID: structure.shared_triple_roots
TeX: T3_modelcompanion_v7.tex, Remark 4.11, lines 1258–1262.
-/
theorem number_of_triples : Nat.card (IncreasingTriple (Fin 4)) = 4 := by
  norm_num [IncreasingTriple.natCard_eq_choose]

end T3.SharedTriple
