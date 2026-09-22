/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded
public import Mathlib.Algebra.Lie.Basic

/-!
# The commutator bracket on the lower central quotients

The bracket is obtained by descending the group commutator through both quotient maps.
Its value on representatives is the initial form of their commutator. The construction of
the additive bracket uses the lower central degree bound for arbitrary groups.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/

@[expose] public section

open scoped commutatorElement DirectSum

namespace T3.AssociatedGraded

variable {G : Type*} [Group G]

/-- A commutator of representatives has the sum of their positive central degrees.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/
def termCommutator {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) : term G (i + j) :=
  ⟨⁅(x : G), (y : G)⁆, by
    have h := Subgroup.commutator_lowerCentralSeries_le (G := G) (i - 1) (j - 1)
      (Subgroup.commutator_mem_commutator x.property y.property)
    have he : i - 1 + (j - 1) + 1 = i + j - 1 := by omega
    simpa only [term, he] using h⟩

/-- Ambient conjugation preserves a lower central term. -/
def termConj (n : ℕ) (x : G) (a : term G n) : term G n :=
  ⟨x * a * x⁻¹, Subgroup.Normal.conj_mem inferInstance (a : G) a.property x⟩

private theorem quotient_conj {n : ℕ} (hn : 0 < n) (x : G) (a : term G n) :
    QuotientGroup.mk' (relation G n) (termConj n x a) =
      QuotientGroup.mk' (relation G n) a := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (x * (a : G) * x⁻¹) / a ∈ (⊤ : Subgroup G).lowerCentralSeries n
  rw [div_eq_mul_inv, ← commutatorElement_def]
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) a.property
  change ⁅x, (a : G)⁆ ∈ ⁅⊤, (⊤ : Subgroup G).lowerCentralSeries (n - 1)⁆ at h
  rw [Subgroup.commutator_comm, ← Subgroup.lowerCentralSeries_succ] at h
  simpa only [Nat.sub_add_cancel hn] using h

/-- The commutator of representatives, in the multiplicative target quotient. -/
def commutatorMul {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) : MulLayer G (i + j) :=
  QuotientGroup.mk' (relation G (i + j)) (termCommutator hi hj x y)

private theorem commutatorMul_mul_left {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x y : term G i) (z : term G j) :
    commutatorMul hi hj (x * y) z = commutatorMul hi hj x z * commutatorMul hi hj y z := by
  have h : termCommutator hi hj (x * y) z =
      termConj (i + j) (x : G) (termCommutator hi hj y z) * termCommutator hi hj x z := by
    apply Subtype.ext
    exact commutatorElement_mul_left_eq_conj_mul (x : G) y z
  simp only [commutatorMul, h, map_mul]
  rw [quotient_conj (by omega)]
  exact mul_comm _ _

private theorem commutatorMul_mul_right {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y z : term G j) :
    commutatorMul hi hj x (y * z) = commutatorMul hi hj x y * commutatorMul hi hj x z := by
  have h : termCommutator hi hj x (y * z) =
      termCommutator hi hj x y * termConj (i + j) (y : G) (termCommutator hi hj x z) := by
    apply Subtype.ext
    change ⁅(x : G), (y : G) * z⁆ =
      ⁅(x : G), (y : G)⁆ * ((y : G) * ⁅(x : G), (z : G)⁆ * (y : G)⁻¹)
    simpa only [mul_assoc] using commutatorElement_mul_right_eq_mul_conj (x : G) y z
  simp only [commutatorMul, h, map_mul]
  rw [quotient_conj (by omega)]

private theorem commutatorMul_eq_one_left {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (hx : x ∈ relation G i) (y : term G j) :
    commutatorMul hi hj x y = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅(x : G), (y : G)⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (i + j)
  change (x : G) ∈ (⊤ : Subgroup G).lowerCentralSeries i at hx
  have h := Subgroup.commutator_lowerCentralSeries_le (G := G) i (j - 1)
    (Subgroup.commutator_mem_commutator hx y.property)
  have he : i + (j - 1) + 1 = i + j := by omega
  simpa only [he] using h

private theorem commutatorMul_eq_one_right {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) (hy : y ∈ relation G j) :
    commutatorMul hi hj x y = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅(x : G), (y : G)⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (i + j)
  change (y : G) ∈ (⊤ : Subgroup G).lowerCentralSeries j at hy
  have h := Subgroup.commutator_lowerCentralSeries_le (G := G) (i - 1) j
    (Subgroup.commutator_mem_commutator x.property hy)
  have he : i - 1 + j + 1 = i + j := by omega
  simpa only [he] using h

/-- With a fixed left representative, the quotient commutator is a group homomorphism. -/
def commutatorRightHom {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (x : term G i) :
    term G j →* MulLayer G (i + j) where
  toFun := commutatorMul hi hj x
  map_one' := by exact commutatorMul_eq_one_right hi hj x 1 (Subgroup.one_mem _)
  map_mul' := by exact commutatorMul_mul_right hi hj x

/-- The commutator descended through the right quotient. -/
def commutatorRightLift {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (x : term G i) :
    MulLayer G j →* MulLayer G (i + j) :=
  QuotientGroup.lift (relation G j) (commutatorRightHom hi hj x)
    (by exact fun y hy => commutatorMul_eq_one_right hi hj x y hy)

/-- The right-descended commutator, as a homomorphism in the left representative. -/
def commutatorLeftHom {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    term G i →* (MulLayer G j →* MulLayer G (i + j)) where
  toFun := commutatorRightLift hi hj
  map_one' := by
    apply MonoidHom.ext
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (relation G j) y
    exact commutatorMul_eq_one_left hi hj 1 (Subgroup.one_mem _) y
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (relation G j) z
    exact commutatorMul_mul_left hi hj x y z

/-- The commutator descended through both multiplicative degree quotients. -/
def commutatorLift {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    MulLayer G i →* (MulLayer G j →* MulLayer G (i + j)) :=
  QuotientGroup.lift (relation G i) (commutatorLeftHom hi hj) fun x hx => by
    apply MonoidHom.ext
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (relation G j) y
    exact commutatorMul_eq_one_left hi hj x hx y

/-- The biadditive commutator on two positive lower central quotients.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/
def bracketAdd {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Layer G i →+ (Layer G j →+ Layer G (i + j)) where
  toFun x := (commutatorLift hi hj x.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg (fun f : MulLayer G j →* MulLayer G (i + j) => Additive.ofMul (f y.toMul))
      (map_one (commutatorLift hi hj))
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    exact congrArg (fun f : MulLayer G j →* MulLayer G (i + j) => Additive.ofMul (f z.toMul))
      (map_mul (commutatorLift hi hj) x.toMul y.toMul)

/-- The descended bracket is the initial form of the group commutator.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/
@[simp]
theorem bracketAdd_mk {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) :
    bracketAdd hi hj (mk G i x) (mk G j y) = mk G (i + j) (termCommutator hi hj x y) :=
  rfl

variable [Fact (HasExponentThree G)]

/-- The bilinear bracket between two positive degrees of the associated graded.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/
def bracketLayer {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Layer G i →ₗ[ZMod 3] (Layer G j →ₗ[ZMod 3] Layer G (i + j)) :=
  ((AddMonoidHom.toZModLinearMapEquiv 3).toAddMonoidHom.comp (bracketAdd hi hj)).toZModLinearMap 3

/-- The bilinear bracket has precisely the paper's value on representatives.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, item 2.
-/
@[simp]
theorem bracketLayer_mk {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (x : term G i) (y : term G j) :
    bracketLayer hi hj (mk G i x) (mk G j y) = mk G (i + j) (termCommutator hi hj x y) := rfl

/-- The bracket of a degree-one vector with itself is zero.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, alternation.
-/
@[simp]
theorem bracketLayer_one_self (x : Layer G 1) : bracketLayer (by decide) (by decide) x x = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective G 1 x
  rw [bracketLayer_mk, mk_eq_zero]
  change ⁅(x : G), (x : G)⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2
  simp

/-- The bracket in degree one changes sign when its arguments are exchanged.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, alternation.
-/
theorem bracketLayer_one_swap (x y : Layer G 1) :
    bracketLayer (by decide) (by decide) x y = -bracketLayer (by decide) (by decide) y x := by
  apply eq_neg_of_add_eq_zero_left
  have h := bracketLayer_one_self (x + y)
  simp only [map_add, LinearMap.add_apply, bracketLayer_one_self, zero_add, add_zero] at h
  exact (add_comm _ _).trans h

/-- The two mixed-degree brackets are negatives of one another.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.18, alternation.
-/
theorem bracketLayer_one_two (x : Layer G 1) (y : Layer G 2) :
    bracketLayer (by decide) (by decide) x y = -bracketLayer (by decide) (by decide) y x := by
  obtain ⟨x, rfl⟩ := mk_surjective G 1 x
  obtain ⟨y, rfl⟩ := mk_surjective G 2 y
  simp only [bracketLayer_mk]
  change QuotientGroup.mk' (relation G 3) _ = (QuotientGroup.mk' (relation G 3) _)⁻¹
  rw [← map_inv]
  congr 1
  exact Subtype.ext (commutatorElement_inv (y : G) x).symm

/-- The triple bracket of degree-one vectors is cyclically invariant.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v7.tex, v7 Lemma 2.19, item 2.
-/
theorem bracketLayer_triple_cyclic (x y z : Layer G 1) :
    bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x y) z =
      bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) y z) x := by
  obtain ⟨x, rfl⟩ := mk_surjective G 1 x
  obtain ⟨y, rfl⟩ := mk_surjective G 1 y
  obtain ⟨z, rfl⟩ := mk_surjective G 1 z
  simp only [bracketLayer_mk]
  congr 1
  exact Subtype.ext (T3.commutator_triple_cyclic Fact.out (x : G) y z)

/-- A repeated final argument annihilates the degree-one triple bracket.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v7.tex, v7 Lemma 2.19, item 2.
-/
@[simp]
theorem bracketLayer_triple_self (x y : Layer G 1) :
    bracketLayer (by decide) (by decide) (bracketLayer (by decide) (by decide) x y) y = 0 := by
  rw [bracketLayer_triple_cyclic, bracketLayer_one_self, map_zero, LinearMap.zero_apply]

/-- Group homomorphisms preserve the bracket of initial forms in every positive degree.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v7.tex, v7 Definition 2.22.
-/
theorem mapLayer_bracketLayer {H : Type*} [Group H] [Fact (HasExponentThree H)]
    (f : G →* H) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (x : Layer G i) (y : Layer G j) :
    mapLayer f (i + j) (bracketLayer hi hj x y) =
      bracketLayer hi hj (mapLayer f i x) (mapLayer f j y) := by
  obtain ⟨x, rfl⟩ := mk_surjective G i x
  obtain ⟨y, rfl⟩ := mk_surjective G j y
  simp only [bracketLayer_mk, mapLayer_mk]
  congr 1
  exact Subtype.ext (map_commutatorElement f (x : G) y)

end T3.AssociatedGraded
