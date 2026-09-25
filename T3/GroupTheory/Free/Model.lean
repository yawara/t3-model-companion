/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# A coordinate model for the Levi–van der Waerden normal form

Levi and van der Waerden (1933), pp. 155–156, use generators `aᵢ`, commutators
`aᵢ,ⱼ = ⁅aᵢ, aⱼ⁆`, and triple commutators `aᵢ,ⱼ,ₖ = ⁅⁅aᵢ, aⱼ⁆, aₖ⁆`.
Their composition law (9) on p. 156 gives the multiplication below. Its group axioms,
inverse formula, and cube identity are verified directly over `ZMod 3`.

`LvdW I` has coordinates at every pair and triple of indices. The same polynomial formulas
work without an order on `I`; when the indices are ordered, restriction to increasing
coordinates recovers the formulas of the source. This larger coordinate group is a comparison
model, not a definition of the free group or a claim that the free group fills all coordinates.
It supplies the coordinate calculations used in proving the paper's normal form.

## Main definitions

* `T3.LvdW`: the coordinate systems, with the group structure given by law (9).
* `T3.LvdW.of`: the element corresponding to a generator.

## Main results

* `T3.LvdW.pow_three`: every model element has cube one.
* `T3.LvdW.commutator_pair`: the degree-two coordinate is a `2 × 2` determinant.
* `T3.LvdW.triple_commutator_triple`: the degree-three coordinate of a triple commutator
  is a `3 × 3` determinant.
* `T3.LvdW.triple_commutator_of_ne_one`: three distinct indices give a nontrivial
  triple commutator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
Primary source: Levi–van der Waerden (1933), pp. 155–156, equations (5)–(9).
-/

@[expose] public section

namespace T3

open scoped commutatorElement

/--
A coordinate system over `ZMod 3`, with arbitrary generator, pair, and triple coordinates.
This is an auxiliary comparison model for the normal form.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
@[ext]
structure LvdW (I : Type*) where
  /-- The exponent `cⁱ` of the generator `aᵢ`. -/
  gen : I → ZMod 3
  /-- The exponent `cⁱ'ʲ` of the double commutator `aᵢ,ⱼ`. -/
  pair : I → I → ZMod 3
  /-- The exponent `cⁱ'ʲ'ᵏ` of the triple commutator `aᵢ,ⱼ,ₖ`. -/
  triple : I → I → I → ZMod 3

namespace LvdW

variable {I : Type*}

/-- The characteristic of the coefficient ring, which every law below is only valid modulo. -/
protected theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

/-- Law (9) of Levi–van der Waerden (1933), p. 156, applied to all index tuples.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
instance : Mul (LvdW I) where
  mul x y :=
    { gen := fun i => x.gen i + y.gen i
      pair := fun i j => x.pair i j + y.pair i j - x.gen j * y.gen i
      triple := fun i j k =>
        x.triple i j k + y.triple i j k + x.pair i j * y.gen k - x.pair i k * y.gen j
          + (x.pair j k - x.gen j * x.gen k - x.gen j * y.gen k + x.gen k * y.gen j) * y.gen i }

@[simp]
theorem mul_gen (x y : LvdW I) (i : I) : (x * y).gen i = x.gen i + y.gen i := rfl

@[simp]
theorem mul_pair (x y : LvdW I) (i j : I) :
    (x * y).pair i j = x.pair i j + y.pair i j - x.gen j * y.gen i := rfl

@[simp]
theorem mul_triple (x y : LvdW I) (i j k : I) :
    (x * y).triple i j k =
      x.triple i j k + y.triple i j k + x.pair i j * y.gen k - x.pair i k * y.gen j
        + (x.pair j k - x.gen j * x.gen k - x.gen j * y.gen k + x.gen k * y.gen j) * y.gen i :=
  rfl

/-- The empty exponent system. -/
instance : One (LvdW I) where
  one := { gen := fun _ => 0, pair := fun _ _ => 0, triple := fun _ _ _ => 0 }

@[simp] theorem one_gen (i : I) : (1 : LvdW I).gen i = 0 := rfl

@[simp] theorem one_pair (i j : I) : (1 : LvdW I).pair i j = 0 := rfl

@[simp] theorem one_triple (i j k : I) : (1 : LvdW I).triple i j k = 0 := rfl

/-- The inverse formula of Levi–van der Waerden (1933), p. 156, below law (9).

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
instance : Inv (LvdW I) where
  inv x :=
    { gen := fun i => -x.gen i
      pair := fun i j => -x.pair i j - x.gen i * x.gen j
      triple := fun i j k =>
        -x.triple i j k + x.pair i j * x.gen k - x.pair i k * x.gen j + x.pair j k * x.gen i
          - x.gen i * x.gen j * x.gen k }

@[simp] theorem inv_gen (x : LvdW I) (i : I) : x⁻¹.gen i = -x.gen i := rfl

@[simp]
theorem inv_pair (x : LvdW I) (i j : I) : x⁻¹.pair i j = -x.pair i j - x.gen i * x.gen j := rfl

@[simp]
theorem inv_triple (x : LvdW I) (i j k : I) :
    x⁻¹.triple i j k =
      -x.triple i j k + x.pair i j * x.gen k - x.pair i k * x.gen j + x.pair j k * x.gen i
        - x.gen i * x.gen j * x.gen k :=
  rfl

protected theorem mul_assoc' (x y z : LvdW I) : x * y * z = x * (y * z) := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen]; ring
  · simp only [mul_gen, mul_pair]; ring
  · simp only [mul_gen, mul_pair, mul_triple]
    linear_combination (-(x.gen k * y.gen j * z.gen i)) * LvdW.three_eq_zero

protected theorem one_mul' (x : LvdW I) : 1 * x = x := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, one_gen]; ring
  · simp only [mul_pair, one_gen, one_pair]; ring
  · simp only [mul_triple, one_gen, one_pair, one_triple]; ring

protected theorem inv_mul_cancel' (x : LvdW I) : x⁻¹ * x = 1 := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, inv_gen, one_gen]; ring
  · simp only [mul_pair, inv_gen, inv_pair, one_pair]; ring
  · simp only [mul_triple, inv_gen, inv_pair, inv_triple, one_triple]
    linear_combination (-(x.gen i * x.gen j * x.gen k)) * LvdW.three_eq_zero

instance : Group (LvdW I) := Group.ofLeftAxioms LvdW.mul_assoc' LvdW.one_mul' LvdW.inv_mul_cancel'

/-- Every model element has cube one, as in Levi–van der Waerden (1933), p. 156.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem pow_three (x : LvdW I) : x ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, one_gen]
    linear_combination (x.gen i) * LvdW.three_eq_zero
  · simp only [mul_gen, mul_pair, one_pair]
    linear_combination (x.pair i j - x.gen i * x.gen j) * LvdW.three_eq_zero
  · simp only [mul_gen, mul_pair, mul_triple, one_triple]
    linear_combination (x.triple i j k + x.gen i * x.pair j k - x.gen j * x.pair i k
      + x.gen k * x.pair i j - 2 * (x.gen i * x.gen j * x.gen k)) * LvdW.three_eq_zero

/-! ### Commutators

A commutator has degree-two coordinates given by `2 × 2` determinants of generator
coordinates. A triple commutator has zero coordinates in degrees one and two, and its degree-three
coordinates are `3 × 3` determinants. These calculations will distinguish the commutator
coefficients in the free group's collected normal form.
-/

@[simp]
theorem commutator_gen (x y : LvdW I) (i : I) : ⁅x, y⁆.gen i = 0 := by
  simp only [commutatorElement_def, mul_gen, inv_gen]; ring

/-- The pair coordinate of a commutator is the determinant of its generator coordinates.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem commutator_pair (x y : LvdW I) (i j : I) :
    ⁅x, y⁆.pair i j = x.gen i * y.gen j - x.gen j * y.gen i := by
  simp only [commutatorElement_def, mul_gen, mul_pair, inv_gen, inv_pair]; ring

theorem triple_commutator_gen (x y z : LvdW I) (i : I) : ⁅⁅x, y⁆, z⁆.gen i = 0 :=
  commutator_gen _ z i

theorem triple_commutator_pair (x y z : LvdW I) (i j : I) : ⁅⁅x, y⁆, z⁆.pair i j = 0 := by
  rw [commutator_pair, commutator_gen, commutator_gen]; ring

/--
The triple coordinate of a triple commutator is the determinant of the generator coordinates.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem triple_commutator_triple (x y z : LvdW I) (i j k : I) :
    ⁅⁅x, y⁆, z⁆.triple i j k =
      x.gen i * (y.gen j * z.gen k - y.gen k * z.gen j)
        - x.gen j * (y.gen i * z.gen k - y.gen k * z.gen i)
        + x.gen k * (y.gen i * z.gen j - y.gen j * z.gen i) := by
  simp only [commutatorElement_def, mul_gen, mul_pair, mul_triple, inv_gen, inv_pair, inv_triple]
  ring

/-! ### Generators -/

variable [DecidableEq I]

/-- The model element corresponding to a free generator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
def of (i : I) : LvdW I where
  gen j := if j = i then 1 else 0
  pair _ _ := 0
  triple _ _ _ := 0

theorem of_gen (i j : I) : (of i).gen j = if j = i then 1 else 0 := rfl

@[simp] theorem of_gen_self (i : I) : (of i).gen i = 1 := ite_eq_left rfl

theorem of_gen_of_ne {i j : I} (h : j ≠ i) : (of i).gen j = 0 := ite_eq_right h

@[simp] theorem of_pair (i j k : I) : (of i).pair j k = 0 := rfl

@[simp] theorem of_triple (i j k l : I) : (of i).triple j k l = 0 := rfl

/-- Three distinct generator elements have a triple commutator with triple coordinate `1`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem triple_commutator_of_triple {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅⁅of i, of j⁆, of k⁆.triple i j k = 1 := by
  rw [triple_commutator_triple, of_gen_self, of_gen_self, of_gen_self,
    of_gen_of_ne hij.symm, of_gen_of_ne hik.symm, of_gen_of_ne hij, of_gen_of_ne hjk.symm,
    of_gen_of_ne hik, of_gen_of_ne hjk]
  ring

/--
Three distinct generator elements have a nontrivial triple commutator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
-/
theorem triple_commutator_of_ne_one {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅⁅of i, of j⁆, of k⁆ ≠ 1 := by
  intro h
  have := triple_commutator_of_triple hij hik hjk
  rw [h, one_triple] at this
  exact zero_ne_one this

end LvdW

end T3
