/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.ModelTheory.Substructures
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.ModelTheory.Complexity
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The first-order language, structures, and embeddings of groups

This file defines the purely functional first-order language of groups, with symbols for the
identity, inversion, and multiplication. It also provides term notation and an explicit bridge
from Lean's `Group` structures to first-order structures.

The bridge is deliberately a definition rather than a global instance. To use a Lean group `G` as
a first-order structure, write `letI := FirstOrder.Group.compatibleGroupOfGroup G`.

Group substructures and subgroups are identified with their actual carriers.

Paper-ID: preliminaries.exponent_three
TeX: T3_modelcompanion_v7.tex, the group-language and group-theory convention, lines 215–221.
-/

@[expose] public section

open scoped FirstOrder

universe u v

variable {α : Type*}

namespace FirstOrder

/-- The function symbols of the language of groups. -/
inductive GroupFunc : ℕ → Type
  | one : GroupFunc 0
  | inv : GroupFunc 1
  | mul : GroupFunc 2
  deriving DecidableEq

/-- The purely functional first-order language with symbols for `1`, inversion, and multiplication.
-/
def Language.group : Language where
  Functions := GroupFunc
  Relations := fun _ => Empty
deriving IsAlgebraic

namespace Group

open GroupFunc Language

/-- The identity symbol, with its definitional arity exposed. -/
abbrev oneFunc : Language.group.Functions 0 := one

/-- The inversion symbol, with its definitional arity exposed. -/
abbrev invFunc : Language.group.Functions 1 := inv

/-- The multiplication symbol, with its definitional arity exposed. -/
abbrev mulFunc : Language.group.Functions 2 := mul

instance (α : Type*) : One (Language.group.Term α) where
  one := Constants.term oneFunc

theorem one_def (α : Type*) :
    (1 : Language.group.Term α) = Constants.term oneFunc :=
  rfl

instance (α : Type*) : Inv (Language.group.Term α) where
  inv := invFunc.apply₁

theorem inv_def (α : Type*) (t : Language.group.Term α) :
    t⁻¹ = invFunc.apply₁ t :=
  rfl

instance (α : Type*) : Mul (Language.group.Term α) where
  mul := mulFunc.apply₂

theorem mul_def (α : Type*) (t₁ t₂ : Language.group.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ :=
  rfl

open Structure

/--
A type is a `CompatibleGroup` when its first-order group-language structure interprets `1`,
inversion, and multiplication using the corresponding Lean operations.

This class does not extend `One`, `Inv`, or `Mul`, so it can coexist with an existing `Group`
instance without creating duplicate algebraic structures.
-/
class CompatibleGroup (G : Type*) [One G] [Inv G] [Mul G]
    extends Language.group.Structure G where
  /-- The group-language identity is Lean's identity. -/
  funMap_one : ∀ x, funMap (oneFunc : Language.group.Constants) x = 1
  /-- Group-language inversion is Lean's inversion. -/
  funMap_inv : ∀ x, funMap invFunc x = (x 0)⁻¹
  /-- Group-language multiplication is Lean's multiplication. -/
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1

open CompatibleGroup

attribute [simp] funMap_one funMap_inv funMap_mul

section Realize

variable {G : Type*} [One G] [Inv G] [Mul G] [CompatibleGroup G]

@[simp]
theorem realize_one (v : α → G) :
    Term.realize v (1 : Language.group.Term α) = 1 := by
  simp [one_def, funMap_one, constantMap]

@[simp]
theorem realize_inv (t : Language.group.Term α) (v : α → G) :
    Term.realize v t⁻¹ = (Term.realize v t)⁻¹ := by
  simp [inv_def, funMap_inv]

@[simp]
theorem realize_mul (t₁ t₂ : Language.group.Term α) (v : α → G) :
    Term.realize v (t₁ * t₂) = Term.realize v t₁ * Term.realize v t₂ := by
  simp [mul_def, funMap_mul]

end Realize

/--
Equip a Lean group with the compatible first-order group-language structure.

This is intentionally a definition, not a global instance: use
`letI := compatibleGroupOfGroup G` at the point where the first-order structure is needed.
-/
@[instance_reducible]
def compatibleGroupOfGroup (G : Type*) [Group G] : CompatibleGroup G where
  funMap := fun {n} f =>
    match n, f with
    | _, .one => fun _ => 1
    | _, .inv => fun x => (x 0)⁻¹
    | _, .mul => fun x => x 0 * x 1
  funMap_one := fun _ => rfl
  funMap_inv := fun _ => rfl
  funMap_mul := fun _ => rfl

end Group

end FirstOrder

namespace FirstOrder

namespace Group

open Language Language.Structure

variable {α : Type*}

/-- The three left-handed axioms used to present the first-order theory of groups. -/
inductive GroupAxiom
  | mulAssoc
  | oneMul
  | invMul
  deriving DecidableEq

/-- The first-order sentence corresponding to a group axiom. -/
@[simp]
def GroupAxiom.toSentence : GroupAxiom → Language.group.Sentence
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .oneMul => ∀' (((1 : Language.group.Term _) * &0) =' &0)
  | .invMul => ∀' (((&0)⁻¹ * &0) =' (1 : Language.group.Term _))

/-- The algebraic proposition corresponding to a group axiom. -/
@[simp]
def GroupAxiom.toProp (G : Type*) [One G] [Inv G] [Mul G] : GroupAxiom → Prop
  | .mulAssoc => ∀ x y z : G, (x * y) * z = x * (y * z)
  | .oneMul => ∀ x : G, 1 * x = x
  | .invMul => ∀ x : G, x⁻¹ * x = 1

/-- Realizing a group-axiom sentence is equivalent to its algebraic proposition. -/
theorem GroupAxiom.realize_toSentence_iff_toProp {G : Type*}
    [One G] [Inv G] [Mul G] [CompatibleGroup G] (ax : GroupAxiom) :
    G ⊨ (ax.toSentence : Language.group.Sentence) ↔ ax.toProp G := by
  cases ax <;> simp [Sentence.Realize, Formula.Realize, Fin.snoc]

/-- The three group axioms form a first-order theory in the language of groups. -/
def _root_.FirstOrder.Language.Theory.group : Language.group.Theory :=
  Set.range GroupAxiom.toSentence

/-- Extract the algebraic content of a group axiom from a model of the group theory. -/
theorem GroupAxiom.toProp_of_model {G : Type*}
    [One G] [Inv G] [Mul G] [CompatibleGroup G]
    [Language.Theory.group.Model G] (ax : GroupAxiom) : ax.toProp G :=
  (ax.realize_toSentence_iff_toProp).1
    (Language.Theory.realize_sentence_of_mem Language.Theory.group (Set.mem_range_self ax))

section StructureToGroup

variable (G : Type*) [Language.group.Structure G]

/-- The identity operation induced by a group-language structure. -/
abbrev oneOfGroupStructure : One G :=
  ⟨funMap oneFunc ![]⟩

/-- The inversion operation induced by a group-language structure. -/
abbrev invOfGroupStructure : Inv G :=
  ⟨fun x ↦ funMap invFunc ![x]⟩

/-- The multiplication operation induced by a group-language structure. -/
abbrev mulOfGroupStructure : Mul G :=
  ⟨fun x y ↦ funMap mulFunc ![x, y]⟩

attribute [local instance] oneOfGroupStructure invOfGroupStructure mulOfGroupStructure

/--
The operations induced by a group-language structure are compatible with that structure.

This definition is intended for use with `oneOfGroupStructure`, `invOfGroupStructure`, and
`mulOfGroupStructure` installed as local instances.
-/
abbrev compatibleGroupOfGroupStructure : CompatibleGroup G where
  funMap_one := by
    simp only [Fin.forall_fin_zero_pi]
    rfl
  funMap_inv := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
    intros
    rfl
  funMap_mul := by
    simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
    intros
    rfl

/--
A model of the first-order group theory carries a Lean `Group` structure.

Use this as a local instance together with `compatibleGroupOfGroupStructure`.
-/
abbrev groupOfModelGroup (G : Type*) [Language.group.Structure G]
    [Language.Theory.group.Model G] : _root_.Group G :=
  letI := oneOfGroupStructure G
  letI := invOfGroupStructure G
  letI := mulOfGroupStructure G
  letI := compatibleGroupOfGroupStructure G
  _root_.Group.ofLeftAxioms
    GroupAxiom.mulAssoc.toProp_of_model
    GroupAxiom.oneMul.toProp_of_model
    GroupAxiom.invMul.toProp_of_model

end StructureToGroup

variable {G : Type u}

/-- Every Lean group with a compatible group-language structure models the group theory. -/
instance [Group G] [CompatibleGroup G] : Language.Theory.group.Model G where
  realize_of_mem := by
    simp only [Language.Theory.group, Set.mem_range, exists_imp]
    rintro φ ax rfl
    rw [ax.realize_toSentence_iff_toProp]
    cases ax with
    | mulAssoc => exact mul_assoc
    | oneMul => exact one_mul
    | invMul => exact inv_mul_cancel

/-- Each group axiom is a universal sentence. -/
theorem GroupAxiom.isUniversal (ax : GroupAxiom) : ax.toSentence.IsUniversal := by
  cases ax with
  | mulAssoc => exact (BoundedFormula.IsAtomic.equal _ _).isUniversal.all.all.all
  | oneMul => exact (BoundedFormula.IsAtomic.equal _ _).isUniversal.all
  | invMul => exact (BoundedFormula.IsAtomic.equal _ _).isUniversal.all

/-- The first-order theory of groups is universal. -/
instance : Language.Theory.group.IsUniversal := ⟨by
  rintro φ ⟨ax, rfl⟩
  exact ax.isUniversal⟩

end Group

end FirstOrder

namespace FirstOrder
namespace Group

variable {G : Type u} {H : Type v}
variable [Group G] [Group H] [CompatibleGroup G] [CompatibleGroup H]

/-- A first-order embedding in the language of groups, viewed as a monoid homomorphism. -/
def embeddingToMonoidHom (f : G ↪[Language.group] H) : G →* H where
  toFun := f
  map_one' := by
    simpa using! f.map_fun oneFunc ![]
  map_mul' x y := by
    simpa using! f.map_fun mulFunc ![x, y]

@[simp]
theorem embeddingToMonoidHom_apply (f : G ↪[Language.group] H) (x : G) :
    embeddingToMonoidHom f x = f x :=
  rfl

/-- An injective monoid homomorphism, viewed as an embedding in the language of groups. -/
def embeddingOfInjectiveMonoidHom (f : G →* H) (hf : Function.Injective f) :
    G ↪[Language.group] H where
  toFun := f
  inj' := hf
  map_fun' := fun {n} g => by
    cases g <;> simp
  map_rel' := fun {n} r => by
    cases r

@[simp]
theorem embeddingOfInjectiveMonoidHom_apply (f : G →* H) (hf : Function.Injective f) (x : G) :
    embeddingOfInjectiveMonoidHom f hf x = f x :=
  rfl

@[simp]
theorem embeddingToMonoidHom_embeddingOfInjectiveMonoidHom
    (f : G →* H) (hf : Function.Injective f) :
    embeddingToMonoidHom (embeddingOfInjectiveMonoidHom f hf) = f := by
  ext x
  rfl

@[simp]
theorem embeddingOfInjectiveMonoidHom_embeddingToMonoidHom
    (f : G ↪[Language.group] H) :
    embeddingOfInjectiveMonoidHom (embeddingToMonoidHom f) f.injective = f := by
  ext x
  rfl

end Group
end FirstOrder

namespace FirstOrder

/-- The group language has precisely the three displayed function symbols and no relations.

Paper-ID: preliminaries.exponent_three
TeX: T3_modelcompanion_v7.tex, the language convention, lines 215–217.
-/
instance finiteGroupSymbols : Finite Language.group.Symbols := by
  let f : Fin 3 → Language.group.Symbols :=
    ![Sum.inl ⟨0, Group.oneFunc⟩, Sum.inl ⟨1, Group.invFunc⟩, Sum.inl ⟨2, Group.mulFunc⟩]
  apply Finite.of_surjective f
  rintro (⟨n, g⟩ | ⟨n, r⟩)
  · cases g with
    | one => exact ⟨0, rfl⟩
    | inv => exact ⟨1, rfl⟩
    | mul => exact ⟨2, rfl⟩
  · cases r

namespace Group

variable {G : Type*} [Group G] [CompatibleGroup G]

/-- A subgroup is a first-order substructure for the group language, with the same carrier.

Paper-ID: preliminaries.exponent_three, model_theory.local_finiteness
TeX: T3_modelcompanion_v7.tex, lines 215–221, 282–285.
-/
def subgroupToSubstructure (H : Subgroup G) : Language.group.Substructure G where
  carrier := H
  fun_mem := by
    intro n f x hx
    cases f with
    | one => simp
    | inv => simpa using H.inv_mem (hx 0)
    | mul => simpa using H.mul_mem (hx 0) (hx 1)

/-- A first-order substructure of a group is a subgroup, with the same carrier.

Paper-ID: preliminaries.exponent_three, model_theory.local_finiteness
TeX: T3_modelcompanion_v7.tex, lines 215–221, 282–285.
-/
def substructureToSubgroup (S : Language.group.Substructure G) : Subgroup G where
  carrier := S
  one_mem' := by
    simpa using S.fun_mem oneFunc ![] (fun i => Fin.elim0 i)
  inv_mem' := by
    intro x hx
    simpa using S.fun_mem invFunc ![x] (by simpa using hx)
  mul_mem' := by
    intro x y hx hy
    simpa using S.fun_mem mulFunc ![x, y] (by simpa using And.intro hx hy)

/-- The two notions of generated closure have exactly the same elements.

Paper-ID: preliminaries.exponent_three, model_theory.local_finiteness
TeX: T3_modelcompanion_v7.tex, applying Definition 2.4 to the group language.
-/
theorem coe_substructure_closure_eq (s : Set G) :
    (Language.Substructure.closure Language.group s : Set G) = (Subgroup.closure s : Set G) := by
  apply Set.Subset.antisymm
  · exact (Language.Substructure.closure_le.mpr
      (Subgroup.subset_closure (k := s)) :
        Language.Substructure.closure Language.group s ≤
          subgroupToSubstructure (Subgroup.closure s))
  · exact ((Subgroup.closure_le _).mpr
      (Language.Substructure.subset_closure (L := Language.group)) :
      Subgroup.closure s ≤ substructureToSubgroup (Language.Substructure.closure Language.group s))

end Group

end FirstOrder
