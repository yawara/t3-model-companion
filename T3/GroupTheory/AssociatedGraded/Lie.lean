/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded.Bracket
public import T3.LinearAlgebra.DirectSum
public import Mathlib.Algebra.Lie.Graded

/-!
# The associated graded Lie algebra of an exponent-three group

Only brackets in degrees `(1, 1)`, `(2, 1)`, and `(1, 2)` can be nonzero. The bracket
on the direct sum is the sum of these three homogeneous brackets. The component brackets
are the actual group-commutator quotient maps constructed in `AssociatedGraded.Bracket`.

Paper-ID: preliminaries.associated_graded, preliminaries.associated_graded_properties,
preliminaries.associated_graded_map, preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, Lemma 2.19, Definition 2.22,
and Proposition 2.24, `proposition:gr(f) and LCS`.
-/

@[expose] public section

open scoped DirectSum

namespace T3.AssociatedGraded

variable {G : Type*} [Group G] [Fact (HasExponentThree G)]

/-- The bilinear extension of the positive-degree commutator bracket to the direct sum.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 2.
-/
def bracketLinear : GradedModule G →ₗ[ZMod 3] GradedModule G →ₗ[ZMod 3] GradedModule G :=
  LinearMap.mk₂ (ZMod 3) (fun x y =>
    DirectSum.lof (ZMod 3) ℕ (Layer G) 2 (bracketLayer (by decide) (by decide) (x 1) (y 1)) +
    DirectSum.lof (ZMod 3) ℕ (Layer G) 3
      (bracketLayer (by decide) (by decide) (x 2) (y 1) -
        bracketLayer (by decide) (by decide) (y 2) (x 1)))
    (by intros; simp only [DirectSum.add_apply, map_add, LinearMap.add_apply, map_sub]; abel)
    (by intros; simp only [DirectSum.smul_apply, map_smul, LinearMap.smul_apply, map_sub,
      smul_sub, smul_add])
    (by intros; simp only [DirectSum.add_apply, map_add, LinearMap.add_apply, map_sub]; abel)
    (by intros; simp only [DirectSum.smul_apply, map_smul, LinearMap.smul_apply, map_sub,
      smul_sub, smul_add])

/-- The associated graded bracket, extending the commutator on homogeneous representatives.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 2.
-/
instance gradedBracket : Bracket (GradedModule G) (GradedModule G) := ⟨fun x y => bracketLinear x y⟩

/-- The bracket is the sum of its degree-two and degree-three components.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 2.
-/
theorem bracket_eq (x y : GradedModule G) :
    ⁅x, y⁆ =
      DirectSum.lof (ZMod 3) ℕ (Layer G) 2
        (bracketLayer (by decide) (by decide) (x 1) (y 1)) +
      DirectSum.lof (ZMod 3) ℕ (Layer G) 3
        (bracketLayer (by decide) (by decide) (x 2) (y 1) -
          bracketLayer (by decide) (by decide) (y 2) (x 1)) := rfl

/-- A bracket has no degree-one component.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18.
-/
@[simp]
theorem bracket_one (x y : GradedModule G) : ⁅x, y⁆ 1 = 0 := by
  simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

/-- The degree-two component is the bracket of the degree-one components.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18.
-/
@[simp]
theorem bracket_two (x y : GradedModule G) :
    ⁅x, y⁆ 2 = bracketLayer (by decide) (by decide) (x 1) (y 1) := by
  simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne]

private theorem triple_neg (x y z : Layer G 1) :
    -bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) y z) x =
      bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x y) z -
        bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x z) y := by
  rw [bracketLayer_triple_cyclic x z y, bracketLayer_one_swap z y,
    map_neg, LinearMap.neg_apply, sub_neg_eq_add, bracketLayer_triple_cyclic x y z]
  apply neg_eq_iff_add_eq_zero.mpr
  have h := three_nsmul_eq_zero G Fact.out 3
    (bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) y z) x)
  simpa only [succ_nsmul, zero_nsmul, zero_add, add_assoc] using h

/-- The commutator bracket satisfies alternation and Jacobi on the associated graded.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, Lie axioms.
-/
instance gradedLieRing : LieRing (GradedModule G) where
  add_lie x y z := by exact LinearMap.congr_fun (map_add bracketLinear x y) z
  lie_add x y z := by exact map_add (bracketLinear x) y z
  lie_self x := by simp [bracket_eq]
  leibniz_lie x y z := by
    rw [bracket_eq x ⁅y, z⁆, bracket_eq ⁅x, y⁆ z, bracket_eq y ⁅x, z⁆]
    simp only [bracket_one, bracket_two, map_zero, LinearMap.zero_apply, zero_sub,
      sub_zero, zero_add]
    rw [triple_neg, map_sub, map_neg, sub_eq_add_neg]

/-- The associated graded Lie bracket is bilinear over the canonical field `𝔽₃`.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, Lie algebra structure.
-/
instance gradedLieAlgebra : LieAlgebra (ZMod 3) (GradedModule G) where
  lie_smul r x y := by exact map_smul (bracketLinear x) r y

/-- A triple bracket depends only on the three degree-one components.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 2.
-/
theorem triple_bracket_eq (x y z : GradedModule G) :
    ⁅⁅x, y⁆, z⁆ = DirectSum.lof (ZMod 3) ℕ (Layer G) 3
      (bracketLayer (by decide) (by decide)
        (bracketLayer (by decide) (by decide) (x 1) (y 1)) (z 1)) := by
  rw [bracket_eq ⁅x, y⁆ z]
  simp

/-- The triple bracket is cyclically invariant on the whole associated graded Lie algebra.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 2.
-/
theorem triple_bracket_cyclic (x y z : GradedModule G) : ⁅⁅x, y⁆, z⁆ = ⁅⁅y, z⁆, x⁆ := by
  simp only [triple_bracket_eq, bracketLayer_triple_cyclic (x 1) (y 1) (z 1)]

/-- A repeated final argument annihilates a triple bracket.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 2.
-/
theorem triple_bracket_self (x y : GradedModule G) : ⁅⁅x, y⁆, y⁆ = 0 := by
  rw [triple_bracket_eq, bracketLayer_triple_self, map_zero]

/-- The direct-sum bracket agrees with the group-commutator quotient in every positive degree.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 2.
-/
theorem bracket_lof {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (x : Layer G i) (y : Layer G j) :
    ⁅DirectSum.lof (ZMod 3) ℕ (Layer G) i x, DirectSum.lof (ZMod 3) ℕ (Layer G) j y⁆ =
      DirectSum.lof (ZMod 3) ℕ (Layer G) (i + j) (bracketLayer hi hj x y) := by
  by_cases hsum : 4 ≤ i + j
  · have := layer_subsingleton_of_four_le (G := G) Fact.out hsum
    have hz : bracketLayer hi hj x y = 0 := Subsingleton.elim _ _
    rw [hz, map_zero]
    by_cases hi1 : i = 1
    · subst i
      have hj1 : j ≠ 1 := by omega
      have hj2 : j ≠ 2 := by omega
      simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne,
        Ne.symm hj1, Ne.symm hj2]
    · by_cases hi2 : i = 2
      · subst i
        have hj1 : j ≠ 1 := by omega
        simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, Ne.symm hj1]
      · simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne,
          Ne.symm hi1, Ne.symm hi2]
  · have hi' : i = 1 ∨ i = 2 := by omega
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    · simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, bracketLayer_one_two]
    · simp [bracket_eq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    · omega

/-- On homogeneous initial forms the full Lie bracket is the initial form of the commutator.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 2.
-/
@[simp]
theorem bracket_lof_mk {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) :
    ⁅DirectSum.lof (ZMod 3) ℕ (Layer G) i (mk G i x),
      DirectSum.lof (ZMod 3) ℕ (Layer G) j (mk G j y)⁆ =
        DirectSum.lof (ZMod 3) ℕ (Layer G) (i + j)
          (mk G (i + j) (termCommutator hi hj x y)) := by
  rw [bracket_lof hi hj, bracketLayer_mk]

/-- The degree-`n` homogeneous subspace in the associated graded Lie algebra.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, direct-sum grading.
-/
def grade (G : Type*) [Group G] [Fact (HasExponentThree G)] (n : ℕ) :
    Submodule (ZMod 3) (GradedModule G) :=
  LinearMap.range (DirectSum.lof (ZMod 3) ℕ (Layer G) n)

/-- The canonical homogeneous subspaces decompose the associated graded.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, direct-sum grading.
-/
instance gradedDecomposition : DirectSum.Decomposition (grade G) :=
  DirectSum.rangeLofDecomposition (ZMod 3) ℕ (Layer G)

/-- The positive central grading is compatible with the Lie bracket.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, graded Lie algebra structure.
-/
instance gradedLieGrading : GradedLieAlgebra (grade G) where
  bracket_mem {i j} {x y} hx hy := by
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hy : y = 0 := Subsingleton.elim _ _
      simp [hy]
    exact ⟨bracketLayer hi hj x y, (bracket_lof hi hj x y).symm⟩

/-- The artificial degree zero contributes no vectors to the positive grading.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, positive grading.
-/
@[simp]
theorem grade_zero : grade G 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hy]

/-- All homogeneous subspaces of degree at least four vanish.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 1.
-/
theorem grade_eq_bot_of_four_le {n : ℕ} (hn : 4 ≤ n) : grade G n = ⊥ := by
  have := layer_subsingleton_of_four_le (G := G) Fact.out hn
  apply le_antisymm ?_ bot_le
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hy]

variable {H : Type*} [Group H] [Fact (HasExponentThree H)]

/-- The associated graded map preserves the actual Lie bracket.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
theorem map_bracket (f : G →* H) (x y : GradedModule G) :
    map f ⁅x, y⁆ = ⁅map f x, map f y⁆ := by
  rw [bracket_eq, bracket_eq]
  simp only [map_add, map_lof, map_sub, map_apply]
  rw [mapLayer_bracketLayer f (i := 1) (j := 1),
    mapLayer_bracketLayer f (i := 2) (j := 1), mapLayer_bracketLayer f (i := 2) (j := 1)]

/-- The natural Lie algebra homomorphism induced by a group homomorphism.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
def mapLie (f : G →* H) : GradedModule G →ₗ⁅ZMod 3⁆ GradedModule H :=
  { map f with map_lie' := fun {x y} => map_bracket f x y }

/-- The Lie homomorphism is the already constructed direct sum of quotient maps.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
@[simp]
theorem mapLie_apply (f : G →* H) (x : GradedModule G) : mapLie f x = map f x := rfl

/-- The natural Lie map preserves every homogeneous subspace.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
theorem mapLie_mem_grade (f : G →* H) (n : ℕ) {x : GradedModule G} (hx : x ∈ grade G n) :
    mapLie f x ∈ grade H n := by
  obtain ⟨x, rfl⟩ := hx
  exact ⟨mapLayer f n x, (map_lof f n x).symm⟩

/-- The induced Lie map respects identity homomorphisms.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
@[simp]
theorem mapLie_id : mapLie (MonoidHom.id G) = LieHom.id := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun map_id x

/-- The induced Lie map respects composition.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22.
-/
@[simp]
theorem mapLie_comp {K : Type*} [Group K] [Fact (HasExponentThree K)]
    (f : G →* H) (g : H →* K) : mapLie (g.comp f) = (mapLie g).comp (mapLie f) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun (map_comp f g) x

/-- Injectivity of the associated graded Lie map implies injectivity of the group map.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, `proposition:gr(f) and LCS`, v9 Proposition 2.24, item 1.
-/
theorem injective_of_mapLie_injective (f : G →* H) (hf : Function.Injective (mapLie f)) :
    Function.Injective f := injective_of_map_injective f hf

/-- An embedding induces an injective Lie map exactly when its image is lower-central strict.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, `proposition:gr(f) and LCS`, v9 Proposition 2.24, item 2.
-/
theorem mapLie_injective_iff_isStrict (f : G →* H) (hf : Function.Injective f) :
    Function.Injective (mapLie f) ↔ IsStrict f.range := map_injective_iff_isStrict f hf

end T3.AssociatedGraded
