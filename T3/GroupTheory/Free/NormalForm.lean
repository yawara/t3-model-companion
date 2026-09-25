/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Collection
public import T3.GroupTheory.Free.ModelComparison
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The collection theorem for the free group of exponent three

`Collection.lean` bounds a finite-rank free group of exponent three by
`3 ^ (n + choose n 2 + choose n 3)`. This file closes the matching lower bound with a counting
argument through the Levi--van der Waerden model and draws the consequences: the comparison map
`Free.toLvdW` is injective, the order is exactly `3 ^ (n + choose n 2 + choose n 3)`,
and the increasing coordinates realise every value exactly once. The final part proves
`Free.existsUnique_normalWord`: every element has a unique expression as the paper's actual
ascending generator product followed by commutator and triple commutator products.

The counting is a tower of three coordinate readouts. The degree-one coordinates of the model
are additive on all of `LvdW`; on the kernel of that readout the degree-two and degree-three
coordinates are additive as well, because every correction term of law (9) carries a degree-one
factor. Each readout is surjective — the generators, the increasing commutators and the
increasing triple commutators hit the coordinate deltas — so the order of the free group is
`3 ^ (n + choose n 2 + choose n 3)` times the order of the final kernel. The upper bound then
forces that kernel to be trivial. The same readouts successively recover the three blocks
of a normal word, proving injectivity of word evaluation; the order formula gives surjectivity.

## Main definitions

* `LvdW.genHom`, `LvdW.pairHom`, `LvdW.tripleHom`: the coordinate readouts of the model;
* `LvdW.collect`: the increasing coordinates of an exponent system;
* `Free.genReadout`, `Free.pairReadout`, `Free.tripleReadout`: the
  readout tower of the free group;
* `Free.collectEquiv`: the increasing model coordinates as a bijection;
* `Free.normalWord`: the collected word with generator factors in ascending order;
* `freeOrderExponent`: the paper's numerical function `t`.

## Main results

* `Free.toLvdW_injective_of_finite`: the comparison map is injective in finite rank;
* `Free.natCard_eq`: `|F(V)| = 3 ^ (n + choose n 2 + choose n 3)`;
* `Free.collect_toLvdW_bijective` and `Free.collect_bijOn_range`: the image of
  the comparison map is a graph over the increasing coordinates;
* `Free.normalWord_bijective` and `Free.existsUnique_normalWord`: existence and uniqueness
  of the ascending collected word itself.
-/

@[expose] public section

open scoped commutatorElement

namespace T3

/-- The exponent in the order of the free exponent-three group of rank `n`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def freeOrderExponent (n : ℕ) : ℕ := n + n.choose 2 + n.choose 3

namespace LvdW

variable {I : Type*}

/-! ### The readout homomorphisms of the model -/

/-- The degree-one coordinates, as a homomorphism to the additive group of functions.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def genHom : LvdW I →* Multiplicative (I → ZMod 3) where
  toFun x := Multiplicative.ofAdd x.gen
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Supporting declaration `genHom_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem genHom_apply (x : LvdW I) : genHom x = Multiplicative.ofAdd x.gen :=
  rfl

/-- Supporting declaration `mem_genHom_ker` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem mem_genHom_ker {x : LvdW I} : x ∈ genHom.ker ↔ ∀ i, x.gen i = 0 := by
  simp [MonoidHom.mem_ker, funext_iff]

/-- Two exponent systems with the same degree-one coordinates have a quotient with vanishing
degree-one coordinates.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem gen_inv_mul_eq_zero {x y : LvdW I} (hgen : x.gen = y.gen) (i : I) :
    (y⁻¹ * x).gen i = 0 := by
  rw [mul_gen, inv_gen, congrFun hgen i]
  ring

/-- If two exponent systems agree in degree one everywhere and in degree two at one pair, their
quotient vanishes in degree two at that pair.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem pair_inv_mul_eq_zero {x y : LvdW I} (hgen : x.gen = y.gen) {a b : I}
    (hpair : x.pair a b = y.pair a b) : (y⁻¹ * x).pair a b = 0 := by
  rw [mul_pair, inv_pair, inv_gen, hpair, congrFun hgen a]
  ring

/-- If two exponent systems agree in degree one everywhere and in degree three at one triple,
their quotient vanishes in degree three at that triple.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem triple_inv_mul_eq_zero {x y : LvdW I} (hgen : x.gen = y.gen) {a b c : I}
    (htriple : x.triple a b c = y.triple a b c) : (y⁻¹ * x).triple a b c = 0 := by
  let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
  simp only [mul_triple, inv_triple, inv_pair, inv_gen]
  rw [htriple, congrFun hgen a, congrFun hgen b, congrFun hgen c]
  linear_combination (-(y.gen a * y.gen b * y.gen c)) * LvdW.three_eq_zero

variable [LinearOrder I]

/--
On the kernel of `genHom`, the degree-two coordinates at increasing pairs are additive: the
correction term of law (9) carries a degree-one factor.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def pairHom : (genHom (I := I)).ker →* Multiplicative (IncreasingPair I → ZMod 3) where
  toFun x := Multiplicative.ofAdd fun p => (x : LvdW I).pair p.first p.second
  map_one' := rfl
  map_mul' x y := by
    let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
    have hy := mem_genHom_ker.mp y.2
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (funext fun p => ?_)
    change ((x : LvdW I) * (y : LvdW I)).pair p.first p.second = _
    rw [mul_pair, hy p.first, mul_zero, sub_zero]
    rfl

/-- Supporting declaration `pairHom_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem pairHom_apply (x : (genHom (I := I)).ker) :
    pairHom x = Multiplicative.ofAdd fun p => (x : LvdW I).pair p.first p.second :=
  rfl

/--
On the kernel of `genHom`, the degree-three coordinates at increasing triples are additive:
every correction term of law (9) carries a degree-one factor.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def tripleHom : (genHom (I := I)).ker →* Multiplicative (IncreasingTriple I → ZMod 3) where
  toFun x := Multiplicative.ofAdd fun t => (x : LvdW I).triple t.first t.second t.third
  map_one' := rfl
  map_mul' x y := by
    have hy := mem_genHom_ker.mp y.2
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (funext fun t => ?_)
    change ((x : LvdW I) * (y : LvdW I)).triple t.first t.second t.third =
      (x : LvdW I).triple t.first t.second t.third +
        (y : LvdW I).triple t.first t.second t.third
    rw [mul_triple, hy t.first, hy t.second, hy t.third]
    ring

/-- Supporting declaration `tripleHom_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem tripleHom_apply (x : (genHom (I := I)).ker) :
    tripleHom x = Multiplicative.ofAdd fun t => (x : LvdW I).triple t.first t.second t.third :=
  rfl

/-! ### Delta values of the generator commutators -/

/-- At an increasing pair, the degree-two coordinate of a generator commutator is a delta.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem commutator_of_pair_of_lt {i j a b : I} (hij : i < j) (hab : a < b) :
    ⁅of i, of j⁆.pair a b = if a = i ∧ b = j then 1 else 0 := by
  let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
  rw [commutator_pair]
  have h₂ : (of i).gen b * (of j).gen a = 0 := by
    rcases eq_or_ne b i with rfl | hbi
    · rcases eq_or_ne a j with rfl | haj
      · exact absurd (hij.trans hab) (lt_irrefl _)
      · simp [of_gen_of_ne haj]
    · simp [of_gen_of_ne hbi]
  rw [h₂, sub_zero, of_gen, of_gen]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj]

/-- At an increasing triple, the degree-three coordinate of a triple generator commutator is a
delta.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem triple_commutator_of_triple_of_lt {i j k a b c : I}
    (hij : i < j) (hjk : j < k) (hab : a < b) (hbc : b < c) :
    ⁅⁅of i, of j⁆, of k⁆.triple a b c = if a = i ∧ b = j ∧ c = k then 1 else 0 := by
  let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
  rw [triple_commutator_triple]
  have h₁ : (of j).gen c * (of k).gen b = 0 := by
    rcases eq_or_ne c j with rfl | hcj
    · rcases eq_or_ne b k with rfl | hbk
      · exact absurd (hjk.trans hbc) (lt_irrefl _)
      · simp [of_gen_of_ne hbk]
    · simp [of_gen_of_ne hcj]
  have h₂ : (of i).gen b * ((of j).gen a * (of k).gen c - (of j).gen c * (of k).gen a) = 0 := by
    rcases eq_or_ne b i with rfl | hbi
    · have haj : a ≠ j := fun h => lt_asymm hij (h ▸ hab)
      have hak : a ≠ k := fun h => lt_asymm (hij.trans hjk) (h ▸ hab)
      simp [of_gen_of_ne haj, of_gen_of_ne hak]
    · simp [of_gen_of_ne hbi]
  have h₃ : (of i).gen c * ((of j).gen a * (of k).gen b - (of j).gen b * (of k).gen a) = 0 := by
    rcases eq_or_ne c i with rfl | hci
    · have haj : a ≠ j := fun h => lt_asymm hij (h ▸ (hab.trans hbc))
      have hbj : b ≠ j := fun h => lt_asymm hij (h ▸ hbc)
      simp [of_gen_of_ne haj, of_gen_of_ne hbj]
    · simp [of_gen_of_ne hci]
  rw [h₁, sub_zero, h₂, sub_zero, h₃, add_zero, of_gen, of_gen, of_gen]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> by_cases hck : c = k <;>
    simp [hai, hbj, hck]

/-! ### The collected coordinates -/

/-- The increasing, "collected", coordinates of an exponent system.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def collect (x : LvdW I) :
    (I → ZMod 3) × (IncreasingPair I → ZMod 3) × (IncreasingTriple I → ZMod 3) :=
  (x.gen, fun p => x.pair p.first p.second, fun t => x.triple t.first t.second t.third)

/-- Supporting declaration `collect_one` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem collect_one : collect (1 : LvdW I) = 0 :=
  rfl

end LvdW

namespace Free

variable {I : Type*} [LinearOrder I]

/-! ### The readout tower of the free group -/

/-- The degree-one readout of the comparison map.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def genReadout : Free I →* Multiplicative (I → ZMod 3) :=
  LvdW.genHom.comp toLvdW

/-- Supporting declaration `genReadout_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem genReadout_apply (g : Free I) :
    genReadout g = Multiplicative.ofAdd (toLvdW g).gen :=
  rfl

/-- `toLvdW`, restricted to the kernel of the degree-one readout.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def toLvdWGenKer : (genReadout (I := I)).ker →* (LvdW.genHom (I := I)).ker :=
  (toLvdW.comp (genReadout (I := I)).ker.subtype).codRestrict _ fun x => x.2

/-- Supporting declaration `toLvdWGenKer_coe` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem toLvdWGenKer_coe (x : (genReadout (I := I)).ker) :
    (toLvdWGenKer x : LvdW I) = toLvdW (x : Free I) :=
  rfl

/-- The degree-two readout, on the kernel of the degree-one readout.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def pairReadout : (genReadout (I := I)).ker →* Multiplicative (IncreasingPair I → ZMod 3) :=
  LvdW.pairHom.comp toLvdWGenKer

/-- Supporting declaration `pairReadout_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem pairReadout_apply (x : (genReadout (I := I)).ker) :
    pairReadout x =
      Multiplicative.ofAdd fun p =>
        (toLvdW (x : Free I)).pair p.first p.second :=
  rfl

/-- The degree-three readout, on the kernel of the degree-two readout.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def tripleReadout : (pairReadout (I := I)).ker →* Multiplicative (IncreasingTriple I → ZMod 3) :=
  LvdW.tripleHom.comp (toLvdWGenKer.comp (pairReadout (I := I)).ker.subtype)

/-- Supporting declaration `tripleReadout_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem tripleReadout_apply (x : (pairReadout (I := I)).ker) :
    tripleReadout x =
      Multiplicative.ofAdd fun t =>
        (toLvdW ((x : (genReadout (I := I)).ker) : Free I)).triple
          t.first t.second t.third :=
  rfl

/-- Commutators die in the degree-one readout, whose target is commutative.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem commutator_mem_genReadout_ker (a b : Free I) :
    ⁅a, b⁆ ∈ (genReadout (I := I)).ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

/-- Triple generator commutators die in the degree-two readout as well.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem tripleCommutator_mem_pairReadout_ker (i j k : I) :
    (⟨⁅⁅of i, of j⁆, of k⁆, commutator_mem_genReadout_ker _ _⟩ :
        (genReadout (I := I)).ker) ∈ (pairReadout (I := I)).ker := by
  rw [MonoidHom.mem_ker, pairReadout_apply, ofAdd_eq_one]
  funext q
  rw [map_commutatorElement, map_commutatorElement, toLvdW_of, toLvdW_of, toLvdW_of]
  exact LvdW.triple_commutator_pair _ _ _ _ _

/-! ### Surjectivity of the readouts -/

/-- The scalar multiple of a coordinate delta realised by a power of a witness. -/
private theorem val_nsmul_single {α : Type*} [DecidableEq α] (p : α) (m : ZMod 3) :
    m.val • Pi.single p (1 : ZMod 3) = (Pi.single p m : α → ZMod 3) := by
  funext q
  rcases eq_or_ne q p with rfl | hqp
  · simp [ZMod.natCast_rightInverse m]
  · simp [Pi.single_eq_of_ne hqp]

section Surjective

variable [Finite I]

/-- The degree-one readout is surjective: the generators hit the coordinate deltas.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem genReadout_surjective : Function.Surjective (genReadout (I := I)) := by
  intro v
  suffices h : ∃ g, genReadout (I := I) g = Multiplicative.ofAdd v.toAdd by simpa using h
  refine Pi.single_induction (fun w => ∃ g, genReadout (I := I) g = Multiplicative.ofAdd w)
    v.toAdd ⟨1, by rw [map_one, ofAdd_zero]⟩ ?_ ?_
  · rintro f₁ f₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    exact ⟨g₁ * g₂, by rw [map_mul, h₁, h₂, ← ofAdd_add]⟩
  · intro i m
    refine ⟨of i ^ m.val, ?_⟩
    have hgen : genReadout (I := I) (of i) =
        Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)) := by
      rw [genReadout_apply, toLvdW_of]
      exact congrArg _ (funext fun j => by rw [LvdW.of_gen, Pi.single_apply])
    rw [map_pow, hgen, ← ofAdd_nsmul, val_nsmul_single]

/-- The degree-two readout is surjective: the increasing commutators hit the deltas.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem pairReadout_surjective : Function.Surjective (pairReadout (I := I)) := by
  intro v
  suffices h : ∃ g, pairReadout (I := I) g = Multiplicative.ofAdd v.toAdd by simpa using h
  refine Pi.single_induction (fun w => ∃ g, pairReadout (I := I) g = Multiplicative.ofAdd w)
    v.toAdd ⟨1, by rw [map_one, ofAdd_zero]⟩ ?_ ?_
  · rintro f₁ f₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    exact ⟨g₁ * g₂, by rw [map_mul, h₁, h₂, ← ofAdd_add]⟩
  · intro p m
    refine ⟨(⟨⁅of p.first, of p.second⁆, commutator_mem_genReadout_ker _ _⟩ :
        (genReadout (I := I)).ker) ^ m.val, ?_⟩
    have hbase :
        pairReadout (I := I)
            ⟨⁅of p.first, of p.second⁆, commutator_mem_genReadout_ker _ _⟩ =
          Multiplicative.ofAdd (Pi.single p (1 : ZMod 3)) := by
      rw [pairReadout_apply]
      refine congrArg _ (funext fun q => ?_)
      rw [map_commutatorElement, toLvdW_of, toLvdW_of,
        LvdW.commutator_of_pair_of_lt p.first_lt_second q.first_lt_second, Pi.single_apply]
      simp only [IncreasingPair.ext_iff]
    rw [map_pow, hbase, ← ofAdd_nsmul, val_nsmul_single]

/-- The degree-three readout is surjective: the increasing triple commutators hit the deltas.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem tripleReadout_surjective : Function.Surjective (tripleReadout (I := I)) := by
  intro v
  suffices h : ∃ g, tripleReadout (I := I) g = Multiplicative.ofAdd v.toAdd by simpa using h
  refine Pi.single_induction (fun w => ∃ g, tripleReadout (I := I) g = Multiplicative.ofAdd w)
    v.toAdd ⟨1, by rw [map_one, ofAdd_zero]⟩ ?_ ?_
  · rintro f₁ f₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    exact ⟨g₁ * g₂, by rw [map_mul, h₁, h₂, ← ofAdd_add]⟩
  · intro t m
    refine ⟨(⟨⟨⁅⁅of t.first, of t.second⁆, of t.third⁆, commutator_mem_genReadout_ker _ _⟩,
        tripleCommutator_mem_pairReadout_ker _ _ _⟩ :
          (pairReadout (I := I)).ker) ^ m.val, ?_⟩
    have hbase :
        tripleReadout (I := I)
            ⟨⟨⁅⁅of t.first, of t.second⁆, of t.third⁆, commutator_mem_genReadout_ker _ _⟩,
              tripleCommutator_mem_pairReadout_ker _ _ _⟩ =
          Multiplicative.ofAdd (Pi.single t (1 : ZMod 3)) := by
      rw [tripleReadout_apply]
      refine congrArg _ (funext fun s => ?_)
      rw [map_commutatorElement, map_commutatorElement, toLvdW_of, toLvdW_of, toLvdW_of,
        LvdW.triple_commutator_of_triple_of_lt t.first_lt_second t.second_lt_third
          s.first_lt_second s.second_lt_third,
        Pi.single_apply]
      simp only [IncreasingTriple.ext_iff]
    rw [map_pow, hbase, ← ofAdd_nsmul, val_nsmul_single]

end Surjective

/-! ### The sandwich -/

section Finite

variable [Finite I]

private theorem card_mult_fun {α : Type*} [Finite α] :
    Nat.card (Multiplicative (α → ZMod 3)) = 3 ^ Nat.card α := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod]

private theorem card_free_eq_mul :
    Nat.card (Free I) =
      3 ^ Nat.card I * Nat.card (genReadout (I := I)).ker := by
  let : Finite (Free I) := finite
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (genReadout (I := I)).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ genReadout_surjective).toEquiv,
    card_mult_fun]

private theorem card_genKer_eq_mul :
    Nat.card (genReadout (I := I)).ker =
      3 ^ (Nat.card I).choose 2 * Nat.card (pairReadout (I := I)).ker := by
  let : Finite (Free I) := finite
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pairReadout (I := I)).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ pairReadout_surjective).toEquiv,
    card_mult_fun, IncreasingPair.natCard_eq_choose]

private theorem card_pairKer_eq_mul :
    Nat.card (pairReadout (I := I)).ker =
      3 ^ (Nat.card I).choose 3 * Nat.card (tripleReadout (I := I)).ker := by
  let : Finite (Free I) := finite
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (tripleReadout (I := I)).ker,
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ tripleReadout_surjective).toEquiv,
    card_mult_fun, IncreasingTriple.natCard_eq_choose]

/-- The final kernel of the readout tower is trivial: the collected coordinates are exact.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem tripleReadout_ker_eq_bot : (tripleReadout (I := I)).ker = ⊥ := by
  let : Finite (Free I) := finite
  rw [← Subgroup.card_eq_one]
  have hchain : Nat.card (Free I) =
      3 ^ (Nat.card I + (Nat.card I).choose 2 + (Nat.card I).choose 3) *
        Nat.card (tripleReadout (I := I)).ker := by
    rw [card_free_eq_mul, card_genKer_eq_mul, card_pairKer_eq_mul, pow_add, pow_add]
    ring
  have hupper := natCard_le (I := I)
  rw [hchain] at hupper
  have hupper' :
      3 ^ (Nat.card I + (Nat.card I).choose 2 + (Nat.card I).choose 3) *
          Nat.card (tripleReadout (I := I)).ker ≤
        3 ^ (Nat.card I + (Nat.card I).choose 2 + (Nat.card I).choose 3) * 1 := by
    rwa [mul_one]
  have hk₁ : Nat.card (tripleReadout (I := I)).ker ≤ 1 :=
    Nat.le_of_mul_le_mul_left hupper' (pow_pos (by norm_num) _)
  have hk₂ : 0 < Nat.card (tripleReadout (I := I)).ker := Nat.card_pos
  omega

/-- The kernel of the degree-one readout carries the degree-two and degree-three layers.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem natCard_genReadout_ker :
    Nat.card (genReadout (I := I)).ker =
      3 ^ ((Nat.card I).choose 2 + (Nat.card I).choose 3) := by
  rw [card_genKer_eq_mul, card_pairKer_eq_mul, tripleReadout_ker_eq_bot, Subgroup.card_bot,
    mul_one, pow_add]

/-- The kernel of the degree-two readout carries exactly the degree-three layer.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem natCard_pairReadout_ker :
    Nat.card (pairReadout (I := I)).ker = 3 ^ (Nat.card I).choose 3 := by
  rw [card_pairKer_eq_mul, tripleReadout_ker_eq_bot, Subgroup.card_bot, mul_one]

/-- An element of the free group whose collected coordinates all vanish is the identity.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem eq_one_of_toLvdW_coords_of_finite {g : Free I}
    (hgen : ∀ i, (toLvdW g).gen i = 0)
    (hpair : ∀ p : IncreasingPair I, (toLvdW g).pair p.first p.second = 0)
    (htriple : ∀ t : IncreasingTriple I, (toLvdW g).triple t.first t.second t.third = 0) :
    g = 1 := by
  have h₁ : g ∈ (genReadout (I := I)).ker := by
    rw [MonoidHom.mem_ker, genReadout_apply, ofAdd_eq_one]
    exact funext fun i => hgen i
  have h₂ : (⟨g, h₁⟩ : (genReadout (I := I)).ker) ∈ (pairReadout (I := I)).ker := by
    rw [MonoidHom.mem_ker, pairReadout_apply, ofAdd_eq_one]
    exact funext fun p => hpair p
  have h₃ : (⟨⟨g, h₁⟩, h₂⟩ : (pairReadout (I := I)).ker) ∈ (tripleReadout (I := I)).ker := by
    rw [MonoidHom.mem_ker, tripleReadout_apply, ofAdd_eq_one]
    exact funext fun t => htriple t
  rw [tripleReadout_ker_eq_bot, Subgroup.mem_bot] at h₃
  exact Subtype.ext_iff.mp (Subtype.ext_iff.mp h₃)

/-- The comparison map with the Levi--van der Waerden model is injective.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem toLvdW_injective_of_finite : Function.Injective (toLvdW (I := I)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_toLvdW_coords_of_finite (fun i => ?_) (fun p => ?_) (fun t => ?_) <;>
    simp [hg]

/-- The order formula for the free group of exponent three of finite rank.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem natCard_eq :
    Nat.card (Free I) =
      3 ^ (Nat.card I + (Nat.card I).choose 2 + (Nat.card I).choose 3) := by
  rw [card_free_eq_mul, card_genKer_eq_mul, card_pairKer_eq_mul, tripleReadout_ker_eq_bot,
    Subgroup.card_bot, mul_one, pow_add, pow_add]
  ring

/-- The order formula using the paper's numerical function `t`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem natCard_eq_pow_freeOrderExponent :
    Nat.card (Free I) = 3 ^ freeOrderExponent (Nat.card I) :=
  natCard_eq

/-! ### The collected normal form -/

/-- Uniqueness of the collected normal form: elements with equal increasing coordinates are
equal.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem collect_toLvdW_injective_of_finite :
    Function.Injective fun g : Free I => LvdW.collect (toLvdW g) := by
  intro g h hgh
  have hgen : (toLvdW g).gen = (toLvdW h).gen := congrArg Prod.fst hgh
  have hpair : ∀ p : IncreasingPair I,
      (toLvdW g).pair p.first p.second = (toLvdW h).pair p.first p.second :=
    fun p => congrFun (congrArg (fun z => z.2.1) hgh) p
  have htriple : ∀ t : IncreasingTriple I,
      (toLvdW g).triple t.first t.second t.third =
        (toLvdW h).triple t.first t.second t.third :=
    fun t => congrFun (congrArg (fun z => z.2.2) hgh) t
  have key : h⁻¹ * g = 1 := by
    refine eq_one_of_toLvdW_coords_of_finite (fun i => ?_) (fun p => ?_) (fun t => ?_)
    · rw [map_mul, map_inv]
      exact LvdW.gen_inv_mul_eq_zero hgen i
    · rw [map_mul, map_inv]
      exact LvdW.pair_inv_mul_eq_zero hgen (hpair p)
    · rw [map_mul, map_inv]
      exact LvdW.triple_inv_mul_eq_zero hgen (htriple t)
  exact (inv_mul_eq_one.mp key).symm

/--
The collection theorem in coordinate form: the increasing coordinates of the comparison map
realise every coordinate system exactly once.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem collect_toLvdW_bijective :
    Function.Bijective fun g : Free I => LvdW.collect (toLvdW g) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨collect_toLvdW_injective_of_finite, ?_⟩
  rw [natCard_eq, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fun,
    Nat.card_zmod, IncreasingPair.natCard_eq_choose, IncreasingTriple.natCard_eq_choose,
    pow_add, pow_add]
  ring

/-- The collected normal form, as a bijection with the increasing coordinate systems.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
noncomputable def collectEquiv :
    Free I ≃
      (I → ZMod 3) × (IncreasingPair I → ZMod 3) × (IncreasingTriple I → ZMod 3) :=
  Equiv.ofBijective _ collect_toLvdW_bijective

/-- Supporting declaration `collectEquiv_apply` for the finite-rank collection theorem.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[simp]
theorem collectEquiv_apply (g : Free I) :
    collectEquiv g = LvdW.collect (toLvdW g) :=
  rfl

/--
The image of the comparison map is a graph over the increasing coordinates: on the range of
`toLvdW`, the collected coordinates are a bijection onto all coordinate systems.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem collect_bijOn_range :
    Set.BijOn (LvdW.collect (I := I)) (Set.range (toLvdW (I := I))) Set.univ := by
  refine ⟨fun x _ => Set.mem_univ _, ?_, ?_⟩
  · rintro x ⟨g, rfl⟩ y ⟨h, rfl⟩ hxy
    exact congrArg toLvdW (collect_toLvdW_injective_of_finite hxy)
  · rintro c -
    obtain ⟨g, hg⟩ := collect_toLvdW_bijective.surjective c
    exact ⟨toLvdW g, ⟨g, rfl⟩, hg⟩

/-! ### The ascending word in the paper

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/

private theorem readout_word {α G : Type*} [DecidableEq α] [Fintype α] [Group G]
    (f : G →* Multiplicative (α → ZMod 3)) (b : α → G)
    (hb : ∀ a, f (b a) = Multiplicative.ofAdd (Pi.single a (1 : ZMod 3)))
    (l : List α) (hn : l.Nodup) (hl : l.toFinset = Finset.univ) (c : α → ZMod 3) :
    f ((l.map fun a => b a ^ (c a).val).prod) = Multiplicative.ofAdd c := by
  have hp : f ((l.map fun a => b a ^ (c a).val).prod) =
      Multiplicative.ofAdd ((l.map fun a => Pi.single a (c a)).sum) := by
    clear hn hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, map_pow, hb,
        ← ofAdd_nsmul, val_nsmul_single, ih, List.sum_cons, ofAdd_add]
  rw [hp]
  congr 1
  rw [← List.sum_toFinset _ hn, hl]
  ext a
  simp

/-- The generator block, with generators multiplied in ascending order.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
noncomputable def generatorWord (l : I → ZMod 3) : Free I := by
  classical
  letI := Fintype.ofFinite I
  exact ((Finset.univ.sort (· ≤ ·)).map fun i => of i ^ (l i).val).prod

/-- The commutator block of the normal word, viewed in the first readout kernel.
All factors have increasing indices and lie in the abelian derived subgroup, so the
choice of their enumeration has no mathematical effect.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
noncomputable def pairWord (m : IncreasingPair I → ZMod 3) :
    (genReadout (I := I)).ker := by
  classical
  letI := Fintype.ofFinite (IncreasingPair I)
  exact (Finset.univ.toList.map fun p =>
    (⟨⁅of p.first, of p.second⁆, commutator_mem_genReadout_ker _ _⟩ :
      (genReadout (I := I)).ker) ^ (m p).val).prod

/-- The triple commutator block, viewed in the second readout kernel.
Every factor has increasing indices and is central.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
noncomputable def tripleWord (n : IncreasingTriple I → ZMod 3) :
    (pairReadout (I := I)).ker := by
  classical
  letI := Fintype.ofFinite (IncreasingTriple I)
  exact (Finset.univ.toList.map fun t =>
    (⟨⟨⁅⁅of t.first, of t.second⁆, of t.third⁆, commutator_mem_genReadout_ker _ _⟩,
      tripleCommutator_mem_pairReadout_ker _ _ _⟩ :
        (pairReadout (I := I)).ker) ^ (n t).val).prod

/-- The collected word from the paper: ascending generator powers, followed by increasing
commutator powers and increasing triple commutator powers. Exponents are the representatives
`0`, `1`, `2` of the specified elements of `ZMod 3`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
noncomputable def normalWord (l : I → ZMod 3) (m : IncreasingPair I → ZMod 3)
    (n : IncreasingTriple I → ZMod 3) : Free I :=
  generatorWord l * (pairWord m : Free I) *
    ((tripleWord n : (genReadout (I := I)).ker) : Free I)

/-- The degree-one readout recovers the generator exponents of the ascending block.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem genReadout_generatorWord (l : I → ZMod 3) :
    genReadout (generatorWord l) = Multiplicative.ofAdd l := by
  classical
  let := Fintype.ofFinite I
  apply readout_word _ _ ?_ _ (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _)
  intro i
  rw [genReadout_apply, toLvdW_of]
  exact congrArg _ (funext fun j => by rw [LvdW.of_gen, Pi.single_apply])

/-- The degree-two readout recovers the commutator exponents of the second block.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem pairReadout_pairWord (m : IncreasingPair I → ZMod 3) :
    pairReadout (pairWord m) = Multiplicative.ofAdd m := by
  classical
  let := Fintype.ofFinite (IncreasingPair I)
  apply readout_word _ _ ?_ _ (Finset.nodup_toList _) (Finset.toList_toFinset _)
  intro p
  rw [pairReadout_apply]
  refine congrArg _ (funext fun q => ?_)
  rw [map_commutatorElement, toLvdW_of, toLvdW_of,
    LvdW.commutator_of_pair_of_lt p.first_lt_second q.first_lt_second, Pi.single_apply]
  simp only [IncreasingPair.ext_iff]

/-- The degree-three readout recovers the triple commutator exponents of the final block.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem tripleReadout_tripleWord (n : IncreasingTriple I → ZMod 3) :
    tripleReadout (tripleWord n) = Multiplicative.ofAdd n := by
  classical
  let := Fintype.ofFinite (IncreasingTriple I)
  apply readout_word _ _ ?_ _ (Finset.nodup_toList _) (Finset.toList_toFinset _)
  intro t
  rw [tripleReadout_apply]
  refine congrArg _ (funext fun s => ?_)
  rw [map_commutatorElement, map_commutatorElement, toLvdW_of, toLvdW_of, toLvdW_of,
    LvdW.triple_commutator_of_triple_of_lt t.first_lt_second t.second_lt_third
      s.first_lt_second s.second_lt_third, Pi.single_apply]
  simp only [IncreasingTriple.ext_iff]

/-- The degree-one readout of the whole normal word gives its generator exponents.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem genReadout_normalWord (l : I → ZMod 3) (m : IncreasingPair I → ZMod 3)
    (n : IncreasingTriple I → ZMod 3) :
    genReadout (normalWord l m n) = Multiplicative.ofAdd l := by
  have hm : genReadout (pairWord m : Free I) = 1 := (pairWord m).property
  have hn : genReadout ((tripleWord n : (genReadout (I := I)).ker) : Free I) = 1 :=
    (tripleWord n).val.property
  rw [normalWord, map_mul, map_mul, genReadout_generatorWord, hm, hn, mul_one, mul_one]

/-- Equality of two ascending collected words forces equality of every exponent.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem normalWord_injective : Function.Injective
    (fun c : (I → ZMod 3) × (IncreasingPair I → ZMod 3) × (IncreasingTriple I → ZMod 3) =>
      normalWord c.1 c.2.1 c.2.2) := by
  rintro ⟨l, m, n⟩ ⟨l', m', n'⟩ h
  have hl : l = l' := by
    have hgen := congrArg genReadout h
    rw [genReadout_normalWord, genReadout_normalWord] at hgen
    exact congrArg Multiplicative.toAdd hgen
  subst l'
  have hp : pairWord m * (tripleWord n : (genReadout (I := I)).ker) =
      pairWord m' * (tripleWord n' : (genReadout (I := I)).ker) := by
    apply Subtype.ext
    apply mul_left_cancel (a := generatorWord l)
    simpa only [normalWord, mul_assoc, Subgroup.coe_mul] using h
  have hm : m = m' := by
    have hn : pairReadout (tripleWord n : (genReadout (I := I)).ker) = 1 :=
      (tripleWord n).property
    have hn' : pairReadout (tripleWord n' : (genReadout (I := I)).ker) = 1 :=
      (tripleWord n').property
    have hpair := congrArg pairReadout hp
    rw [map_mul, map_mul, pairReadout_pairWord, pairReadout_pairWord, hn, hn',
      mul_one, mul_one] at hpair
    exact congrArg Multiplicative.toAdd hpair
  subst m'
  have ht : tripleWord n = tripleWord n' := Subtype.ext (mul_left_cancel hp)
  have hn := congrArg tripleReadout ht
  rw [tripleReadout_tripleWord, tripleReadout_tripleWord] at hn
  have hn' : n = n' := congrArg Multiplicative.toAdd hn
  subst n'
  rfl

/-- The paper's ascending collected words give a bijection between exponent systems and
free-group elements. This statement concerns the displayed words themselves, independently
of the raw model-coordinate bijection `collectEquiv`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem normalWord_bijective : Function.Bijective
    (fun c : (I → ZMod 3) × (IncreasingPair I → ZMod 3) × (IncreasingTriple I → ZMod 3) =>
      normalWord c.1 c.2.1 c.2.2) := by
  let : Finite (Free I) := finite
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨normalWord_injective, ?_⟩
  rw [natCard_eq, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fun,
    Nat.card_zmod, IncreasingPair.natCard_eq_choose, IncreasingTriple.natCard_eq_choose,
    pow_add, pow_add]
  ring

/-- Every element has a unique expression as the ascending collected word in the paper.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem existsUnique_normalWord (g : Free I) :
    ∃! c : (I → ZMod 3) × (IncreasingPair I → ZMod 3) × (IncreasingTriple I → ZMod 3),
      normalWord c.1 c.2.1 c.2.2 = g := by
  obtain ⟨c, hc⟩ := normalWord_bijective.surjective g
  exact ⟨c, hc, fun d hd => normalWord_injective (hd.trans hc.symm)⟩

end Finite

end Free

end T3
