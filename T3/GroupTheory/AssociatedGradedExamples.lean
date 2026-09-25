/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded.Lie
public import T3.GroupTheory.Free.Examples
public import T3.GroupTheory.Free.ExteriorBracket
public import Mathlib.Algebra.Lie.Abelian

/-!
# Concrete examples of associated graded Lie algebras

For an abelian exponent-three group the canonical first quotient is the group itself,
written additively. Every other homogeneous component vanishes, and the canonical map
from the whole graded Lie algebra preserves its zero bracket.

For the free group on two generators, the second central term is exactly the three powers
of the generator commutator. The named generator and commutator classes give bases of the
actual layers. Canonical coordinates on the full graded Lie algebra identify its bracket
with the alternating determinant, and identify its two nonzero homogeneous subspaces.
The direct-product example is proved separately in `AssociatedGraded.Product`.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, lines 533–539; no label.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace T3.AssociatedGraded

variable (G : Type*) [CommGroup G]

/-- Every lower central term after the first vanishes in an abelian group.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem term_eq_bot_of_commutative {n : ℕ} (hn : 2 ≤ n) : term G n = ⊥ := by
  apply eq_bot_iff.mpr
  calc
    term G n ≤ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      Subgroup.lowerCentralSeries_antitone _ (by omega)
    _ = ⊥ := Subgroup.lowerCentralSeries_one_eq_bot_iff.mpr inferInstance

/-- The first quotient has no relations beyond the identity in an abelian group.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem relation_one_eq_bot_of_commutative : relation G 1 = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change (x : G) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 at hx
  rw [Subgroup.top_lowerCentralSeries_one, commutator_eq_bot] at hx
  exact Subtype.ext (Subgroup.mem_bot.mp hx)

/-- The canonical first quotient of an abelian group is the group itself, in additive notation.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
def abelianLayerOneAddEquiv : Layer G 1 ≃+ Additive G :=
  ((QuotientGroup.quotientMulEquivOfEq (relation_one_eq_bot_of_commutative G)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)).toAdditive

/-- The first-layer identification keeps the chosen representative unchanged.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
@[simp]
theorem abelianLayerOneAddEquiv_mk (x : G) :
    abelianLayerOneAddEquiv G (mk G 1 ⟨x, Subgroup.mem_top x⟩) = Additive.ofMul x := rfl

/-- All degrees other than one vanish in the associated graded of an abelian group.
The artificial degree zero also vanishes.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem layer_subsingleton_of_commutative {n : ℕ} (hn : n ≠ 1) :
    Subsingleton (Layer G n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn'
  · infer_instance
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  have hx : x = 1 := Subtype.ext <| Subgroup.mem_bot.mp <|
    (term_eq_bot_of_commutative G (show 2 ≤ n by omega)) ▸ x.property
  rw [hx]
  rfl

variable [Fact (HasExponentThree G)]

/-- The canonical vector-space structure on an abelian exponent-three group.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
instance abelianModule : Module (ZMod 3) (Additive G) :=
  AddCommGroup.zmodModule fun x => Fact.out (p := HasExponentThree G) x.toMul

/-- The degree-one identification respects the canonical field action.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
def abelianLayerOneEquiv : Layer G 1 ≃ₗ[ZMod 3] Additive G :=
  { abelianLayerOneAddEquiv G with map_smul' := ZMod.map_smul (abelianLayerOneAddEquiv G) }

/-- The full associated graded of an abelian exponent-three group is its first component.
The forward map reads degree one and keeps its representative; the inverse inserts degree one.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
def abelianEquiv : GradedModule G ≃ₗ[ZMod 3] Additive G where
  toFun x := abelianLayerOneEquiv G (x 1)
  invFun x := DirectSum.lof (ZMod 3) ℕ (Layer G) 1 ((abelianLayerOneEquiv G).symm x)
  left_inv x := by
    apply DFinsupp.ext
    intro n
    by_cases hn : n = 1
    · subst n
      simp [DirectSum.lof_eq_of]
    · let := layer_subsingleton_of_commutative G hn
      exact Subsingleton.elim _ _
  right_inv x := by simp [DirectSum.lof_eq_of]
  map_add' x y := by simp
  map_smul' r x := by
    rw [DirectSum.smul_apply, map_smul]
    rfl

/-- The whole-graded identification sends the initial form of a group element to that element.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
@[simp]
theorem abelianEquiv_lof_mk (x : G) :
    abelianEquiv G (DirectSum.lof (ZMod 3) ℕ (Layer G) 1
      (mk G 1 ⟨x, Subgroup.mem_top x⟩)) = Additive.ofMul x := by
  change abelianLayerOneAddEquiv G _ = _
  exact abelianLayerOneAddEquiv_mk G x

/-- The associated graded of an abelian group has identically zero Lie bracket.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem bracket_eq_zero_of_commutative (x y : GradedModule G) : ⁅x, y⁆ = 0 := by
  apply (abelianEquiv G).injective
  change abelianLayerOneEquiv G (⁅x, y⁆ 1) = abelianLayerOneEquiv G 0
  rw [bracket_one]

/-- The abelian group on the right side of the example carries the zero Lie bracket.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
@[implicit_reducible]
def abelianLieRing : LieRing (Additive G) where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add 0).symm
  lie_add _ _ _ := (zero_add 0).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add 0).symm

attribute [local instance] abelianLieRing

/-- The canonical field action is compatible with the zero Lie bracket.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
@[implicit_reducible]
def abelianLieAlgebra : LieAlgebra (ZMod 3) (Additive G) where
  lie_smul _ _ _ := (smul_zero _).symm

attribute [local instance] abelianLieAlgebra

/-- The canonical identification with the abelian group is an actual Lie-algebra equivalence.
The target uses `abelianLieRing` and `abelianLieAlgebra`, with identically zero bracket.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
def abelianLieEquiv : GradedModule G ≃ₗ⁅ZMod 3⁆ Additive G :=
  { abelianEquiv G with
    map_lie' := by
      intro x y
      change abelianEquiv G ⁅x, y⁆ = 0
      rw [bracket_eq_zero_of_commutative, map_zero] }

/-- Degree one is the whole graded Lie algebra of an abelian group.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem grade_one_eq_top_of_commutative : grade G 1 = ⊤ := by
  apply top_unique
  intro x _
  exact ⟨(abelianLayerOneEquiv G).symm (abelianEquiv G x), (abelianEquiv G).left_inv x⟩

/-- All remaining homogeneous submodules of an abelian group's graded Lie algebra vanish.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, line 535.
-/
theorem grade_eq_bot_of_commutative {n : ℕ} (hn : n ≠ 1) : grade G n = ⊥ := by
  let := layer_subsingleton_of_commutative G hn
  apply eq_bot_iff.mpr
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy, map_zero]
  exact Submodule.zero_mem _

/-- The abelian identification is natural for group homomorphisms: the induced graded Lie
map acts on the same underlying group element.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 1, the canonical equality on line 535.
-/
theorem abelianEquiv_mapLie {H : Type*} [CommGroup H] [Fact (HasExponentThree H)]
    (f : G →* H) (x : GradedModule G) :
    abelianEquiv H (mapLie f x) = f.toAdditive (abelianEquiv G x) := by
  change abelianLayerOneEquiv H (map f x 1) =
    f.toAdditive (abelianLayerOneEquiv G (x 1))
  rw [map_apply]
  obtain ⟨y, hy⟩ := mk_surjective G 1 (x 1)
  rw [← hy, mapLayer_mk]
  rfl

end T3.AssociatedGraded

open scoped commutatorElement DirectSum
open Module T3.AssociatedGraded

namespace T3.FreeTwo

/-- The unique increasing pair of the two named generator indices.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
def pairIndex : IncreasingPair (Fin 2) := ⟨0, 1, by decide⟩

/-- Every increasing pair is the ordered pair of the two named generators.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem pair_eq (p : IncreasingPair (Fin 2)) : p = pairIndex := by
  apply IncreasingPair.ext
  · apply Fin.ext
    have h := p.first_lt_second
    have h' := p.second.isLt
    simp only [Fin.lt_def] at h
    change p.first.val = 0
    omega
  · apply Fin.ext
    have h := p.first_lt_second
    have h' := p.second.isLt
    simp only [Fin.lt_def] at h
    change p.second.val = 1
    omega

/-- Increasing pairs of two generator indices are indexed by a singleton.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
def pairEquiv : IncreasingPair (Fin 2) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := pairIndex
  left_inv p := (pair_eq p).symm
  right_inv _ := Subsingleton.elim _ _

private theorem pairEquiv_symm (i : Fin 1) : pairEquiv.symm i = pairIndex := rfl

/-- The two free-generator classes form the actual degree-one basis.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
def firstLayerBasis : Basis (Fin 2) (ZMod 3) (Layer (Free (Fin 2)) 1) :=
  Free.layerOneBasis

/-- The commutator class forms the one-element basis of the actual second layer.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
def secondLayerBasis : Basis (Fin 1) (ZMod 3) (Layer (Free (Fin 2)) 2) :=
  Free.layerTwoBasis.reindex pairEquiv

/-- Each degree-one basis vector is the initial form of its named free generator.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem firstLayerBasis_apply (i : Fin 2) :
    firstLayerBasis i = mk (Free (Fin 2)) 1 ⟨Free.of i, Subgroup.mem_top _⟩ :=
  Free.layerOneBasis_apply i

/-- The degree-two basis vector is the actual initial form of the generator commutator.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem secondLayerBasis_apply :
    secondLayerBasis 0 = mk (Free (Fin 2)) 2
      (Free.derivedCommutator (Free.of 0) (Free.of 1)) := by
  simpa only [secondLayerBasis, Basis.reindex_apply, pairEquiv_symm, pairIndex] using
    Free.layerTwoBasis_apply pairIndex

/-- The third lower central term of the free group on two generators is trivial.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem term_three_eq_bot : term (Free (Fin 2)) 3 = ⊥ :=
  Free.lowerCentralSeries_two_fin_two_eq_bot

/-- Every layer in degree at least three vanishes, including the actual third quotient.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem layer_subsingleton {n : ℕ} (hn : 3 ≤ n) : Subsingleton (Layer (Free (Fin 2)) n) := by
  have hterm : term (Free (Fin 2)) n = ⊥ := by
    apply bot_unique
    exact ((⊤ : Subgroup (Free (Fin 2))).lowerCentralSeries_antitone
      (show 2 ≤ n - 1 by omega)).trans_eq term_three_eq_bot
  have : Subsingleton (term (Free (Fin 2)) n) := by rw [hterm]; infer_instance
  exact Function.Surjective.subsingleton (mk_surjective (Free (Fin 2)) n)

private theorem mk_two_injective : Function.Injective (mk (Free (Fin 2)) 2) := by
  apply Additive.ofMul.injective.comp
  apply (QuotientGroup.mk' (relation (Free (Fin 2)) 2)).ker_eq_bot_iff.mp
  rw [QuotientGroup.ker_mk', relation, Free.lowerCentralSeries_two_fin_two_eq_bot,
    MonoidHom.comap_bot]
  exact MonoidHom.ker_eq_bot _ Subtype.val_injective

private theorem mk_pow (x : term (Free (Fin 2)) 2) (k : ℕ) :
    mk (Free (Fin 2)) 2 (x ^ k) = k • mk (Free (Fin 2)) 2 x := by
  unfold AssociatedGraded.mk
  rw [map_pow, ofMul_pow]

/-- Every second-layer vector has its unique commutator coefficient.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem secondLayer_eq_repr_smul (v : Layer (Free (Fin 2)) 2) :
    v = secondLayerBasis.repr v 0 • secondLayerBasis 0 := by
  simpa only [Fin.sum_univ_one] using (secondLayerBasis.sum_repr v).symm

/-- The second central term consists exactly of the three powers of the generator commutator.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem mem_term_two_iff (g : Free (Fin 2)) :
    g ∈ term (Free (Fin 2)) 2 ↔
      ∃ k : Fin 3, g = ⁅Free.of (0 : Fin 2), Free.of 1⁆ ^ k.val := by
  constructor
  · intro hg
    let a := secondLayerBasis.repr (mk (Free (Fin 2)) 2 ⟨g, hg⟩) 0
    let c : term (Free (Fin 2)) 2 := ⟨⁅Free.of 0, Free.of 1⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    have hc : mk (Free (Fin 2)) 2 c = secondLayerBasis 0 := secondLayerBasis_apply.symm
    refine ⟨⟨a.val, a.val_lt⟩, ?_⟩
    have heq : (⟨g, hg⟩ : term (Free (Fin 2)) 2) = c ^ a.val := by
      apply mk_two_injective
      rw [mk_pow, hc]
      have h := secondLayer_eq_repr_smul (mk (Free (Fin 2)) 2 ⟨g, hg⟩)
      simpa only [← Nat.cast_smul_eq_nsmul (R := ZMod 3), ZMod.natCast_zmod_val] using h
    exact congrArg Subtype.val heq
  · rintro ⟨k, rfl⟩
    exact Subgroup.pow_mem _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _

/-- Every first-layer vector has its two generator coefficients.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem firstLayer_eq_repr_smul (v : Layer (Free (Fin 2)) 1) :
    v = firstLayerBasis.repr v 0 • firstLayerBasis 0 +
      firstLayerBasis.repr v 1 • firstLayerBasis 1 := by
  simpa only [Fin.sum_univ_two] using (firstLayerBasis.sum_repr v).symm

/-- The bracket of the two generator classes is the commutator basis vector.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem bracket_basis :
    bracketLayer (by decide) (by decide) (firstLayerBasis 0) (firstLayerBasis 1) =
      secondLayerBasis 0 :=
  by
    simpa only [secondLayerBasis, Basis.reindex_apply, pairEquiv_symm, pairIndex, firstLayerBasis]
      using (Free.layerTwoBasis_eq_bracket pairIndex).symm

/-- The bracket in degree two is the alternating determinant of the generator coordinates.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem bracketLayer_eq_determinant (v w : Layer (Free (Fin 2)) 1) :
    bracketLayer (by decide) (by decide) v w =
      (firstLayerBasis.repr v 0 * firstLayerBasis.repr w 1 -
        firstLayerBasis.repr v 1 * firstLayerBasis.repr w 0) • secondLayerBasis 0 := by
  conv_lhs => rw [firstLayer_eq_repr_smul v, firstLayer_eq_repr_smul w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    bracketLayer_one_self, smul_zero, zero_add, add_zero]
  rw [bracketLayer_one_swap (firstLayerBasis 1) (firstLayerBasis 0), bracket_basis]
  simp only [smul_neg, smul_smul]
  rw [sub_smul, mul_comm (firstLayerBasis.repr w 0) (firstLayerBasis.repr v 1),
    mul_comm (firstLayerBasis.repr w 1) (firstLayerBasis.repr v 0)]
  abel

/-- The complete associated graded Lie bracket lies in the commutator line and is given by
the alternating determinant of the two degree-one coordinates.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem graded_bracket_eq_determinant (v w : GradedModule (Free (Fin 2))) :
    ⁅v, w⁆ =
      (firstLayerBasis.repr (v 1) 0 * firstLayerBasis.repr (w 1) 1 -
        firstLayerBasis.repr (v 1) 1 * firstLayerBasis.repr (w 1) 0) •
        DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 2 (secondLayerBasis 0) := by
  let := layer_subsingleton (n := 3) le_rfl
  rw [bracket_eq, bracketLayer_eq_determinant]
  have hz : bracketLayer (by decide) (by decide) (v 2) (w 1) -
      bracketLayer (by decide) (by decide) (w 2) (v 1) = 0 := Subsingleton.elim _ _
  simp only [hz, map_zero, add_zero, map_smul]

end T3.FreeTwo

namespace T3.FreeTwo

/-- The complete associated graded has two generator coordinates in degree one and a
single commutator coordinate in degree two, with its canonical named bases.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
def coordinates : GradedModule (Free (Fin 2)) ≃ₗ[ZMod 3] (ZMod 3 × ZMod 3) × ZMod 3 where
  toFun v := ((firstLayerBasis.repr (v 1) 0, firstLayerBasis.repr (v 1) 1),
    secondLayerBasis.repr (v 2) 0)
  invFun c := DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 1
      (c.1.1 • firstLayerBasis 0 + c.1.2 • firstLayerBasis 1) +
    DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 2 (c.2 • secondLayerBasis 0)
  left_inv v := by
    apply DFinsupp.ext
    intro n
    by_cases h1 : n = 1
    · subst n
      simpa [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.smul_apply] using
        (firstLayer_eq_repr_smul (v 1)).symm
    by_cases h2 : n = 2
    · subst n
      simpa [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.smul_apply] using
        (secondLayer_eq_repr_smul (v 2)).symm
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subsingleton.elim _ _
    · let := layer_subsingleton (show 3 ≤ n by omega)
      exact Subsingleton.elim _ _
  right_inv c := by
    rcases c with ⟨⟨a, b⟩, c⟩
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.smul_apply]
  map_add' v w := by simp
  map_smul' r v := by
    simp only [DirectSum.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl

/-- The coordinates are the three coefficients in the named homogeneous bases.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
@[simp]
theorem coordinates_apply (v : GradedModule (Free (Fin 2))) :
    coordinates v = ((firstLayerBasis.repr (v 1) 0, firstLayerBasis.repr (v 1) 1),
      secondLayerBasis.repr (v 2) 0) := rfl

/-- In the canonical coordinates the complete Lie bracket is the alternating determinant
in degree one, with its value on the degree-two commutator line.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem coordinates_bracket (v w : GradedModule (Free (Fin 2))) :
    coordinates ⁅v, w⁆ =
      ((0, 0), (coordinates v).1.1 * (coordinates w).1.2 -
        (coordinates v).1.2 * (coordinates w).1.1) := by
  rw [graded_bracket_eq_determinant, map_smul]
  simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]

/-- A vector is homogeneous of degree one precisely when its commutator coordinate vanishes.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem mem_grade_one_iff (v : GradedModule (Free (Fin 2))) :
    v ∈ grade (Free (Fin 2)) 1 ↔ (coordinates v).2 = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
  · intro hv
    rw [← coordinates.symm_apply_apply v]
    change DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 1 _ +
      DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 2 ((coordinates v).2 • _) ∈ _
    simp only [hv, zero_smul, map_zero, add_zero]
    exact ⟨_, rfl⟩

/-- A vector is homogeneous of degree two precisely when its two generator coordinates vanish.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem mem_grade_two_iff (v : GradedModule (Free (Fin 2))) :
    v ∈ grade (Free (Fin 2)) 2 ↔ (coordinates v).1 = (0, 0) := by
  constructor
  · rintro ⟨v, rfl⟩
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
  · intro hv
    rw [← coordinates.symm_apply_apply v]
    change DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 1
      ((coordinates v).1.1 • _ + (coordinates v).1.2 • _) +
      DirectSum.lof (ZMod 3) ℕ (Layer (Free (Fin 2))) 2 _ ∈ _
    rw [hv]
    simp only [zero_smul, add_zero, map_zero, zero_add]
    exact ⟨_, rfl⟩

/-- There are no other homogeneous components in the graded Lie algebra of the free group
on two generators.

Paper-ID: preliminaries.associated_graded_examples
TeX: T3_modelcompanion_v9.tex, Example 2.21, item 3, line 537.
-/
theorem grade_eq_bot {n : ℕ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    grade (Free (Fin 2)) n = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact AssociatedGraded.grade_zero
  let := layer_subsingleton (show 3 ≤ n by omega)
  apply eq_bot_iff.mpr
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy, map_zero]
  exact Submodule.zero_mem _

end T3.FreeTwo
