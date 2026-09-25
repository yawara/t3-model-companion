/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Rank
public import Mathlib.ModelTheory.Complexity

/-!
# Specification of the two main results

This independent specification imports only Mathlib. Its concrete definitions reproduce those
used by the mathematical library; Comparator checks their agreement through the theorem types.
Only the two theorem proofs are holes. `Solution` imports their complete proofs separately.

The paper is *Existence of a Model Companion for Groups of Exponent 3* by
Yawara Ishida, Ryosuke Mizuno, and Kota Takeuchi, available as
[arXiv:2609.30061](https://arxiv.org/abs/2609.30061).

The bounded-witness statement uses groups in arbitrary universes. Existential closedness is
tested in the maximum of the model and language universes. Companions use Mathlib's canonical
semantic universe of bundled nonempty models, here `Type` for the finite group language.
An amalgam is ordinary amalgamation: its factor images need only agree on the common base.
Finite generation of the base is equivalent to finiteness here by local finiteness of `T₃`.

Paper-ID: main.bounded_witness, main.model_companion
TeX: T3_modelcompanion_v9.tex, `thm:main`, Theorem 3.3 and Corollary 3.4, lines 795–838.
-/

@[expose] public section

open scoped FirstOrder

universe u v w

section GroupLanguage

variable {α : Type*}

namespace FirstOrder

/-- Symbols for the group operations.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
inductive GroupFunc : ℕ → Type
  | one : GroupFunc 0
  | inv : GroupFunc 1
  | mul : GroupFunc 2
  deriving DecidableEq

/-- The purely functional language of groups.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
def Language.group : Language where
  Functions := GroupFunc
  Relations := fun _ => Empty
deriving IsAlgebraic

namespace Group

open GroupFunc Language

/-- Identity symbol. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
abbrev oneFunc : Language.group.Functions 0 := one

/-- Inversion symbol. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
abbrev invFunc : Language.group.Functions 1 := inv

/-- Multiplication symbol. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
abbrev mulFunc : Language.group.Functions 2 := mul

/-- Identity term. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
instance (α : Type*) : One (Language.group.Term α) where
  one := Constants.term oneFunc

/-- Inverse term. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
instance (α : Type*) : Inv (Language.group.Term α) where
  inv := invFunc.apply₁

/-- Product term. Paper-ID: preliminaries.exponent_three; TeX: lines 230–236. -/
instance (α : Type*) : Mul (Language.group.Term α) where
  mul := mulFunc.apply₂

open Structure

/-- The first-order operations agree with the given algebraic operations.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
class CompatibleGroup (G : Type*) [One G] [Inv G] [Mul G]
    extends Language.group.Structure G where
  /-- The identity is interpreted by the algebraic identity. -/
  funMap_one : ∀ x, funMap (oneFunc : Language.group.Constants) x = 1
  /-- Inversion is interpreted by algebraic inversion. -/
  funMap_inv : ∀ x, funMap invFunc x = (x 0)⁻¹
  /-- Multiplication is interpreted by algebraic multiplication. -/
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1

/-- The canonical compatible structure on a Lean group.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
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

/-- Three left-handed group axioms.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
inductive GroupAxiom
  | mulAssoc
  | oneMul
  | invMul
  deriving DecidableEq

/-- The sentences asserting associativity, left identity, and left inverse.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
def GroupAxiom.toSentence : GroupAxiom → Language.group.Sentence
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .oneMul => ∀' (((1 : Language.group.Term _) * &0) =' &0)
  | .invMul => ∀' (((&0)⁻¹ * &0) =' (1 : Language.group.Term _))

/-- The first-order theory of groups.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
def _root_.FirstOrder.Language.Theory.group : Language.group.Theory :=
  Set.range GroupAxiom.toSentence

end Group

end FirstOrder

end GroupLanguage

namespace FirstOrder

namespace Group

open Language

/-- The natural-power term.
Paper-ID: preliminaries.exponent_three; TeX: lines 232–235.
-/
def powerTerm {α : Type*} (n : ℕ) (t : Language.group.Term α) : Language.group.Term α :=
  match n with
  | 0 => 1
  | n + 1 => powerTerm n t * t

/-- The sentence asserting that every element has `n`-th power one.
Paper-ID: preliminaries.exponent_three; TeX: lines 232–235.
-/
def exponentSentence (n : ℕ) : Language.group.Sentence :=
  ∀' ((powerTerm n &⟨0, Nat.zero_lt_one⟩) =' (1 : Language.group.Term _))

end Group

namespace Language.Theory

variable {L : Language.{u, v}}

/-- Every nonempty model of the first theory embeds into one of the second.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 1, line 274.
-/
def ModelsEmbedInto (T T' : L.Theory) : Prop :=
  ∀ M : T.ModelType.{u, v, max u v},
    ∃ N : T'.ModelType.{u, v, max u v}, Nonempty (M ↪[L] N)

/-- Each theory's models embed into models of the other theory.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 1, line 274.
-/
def IsCompanion (T T' : L.Theory) : Prop :=
  T.ModelsEmbedInto T' ∧ T'.ModelsEmbedInto T

/-- Every formula is equivalent modulo the theory to an existential formula.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 2, line 275.
-/
def IsModelComplete (T : L.Theory) : Prop :=
  ∀ {n : ℕ} (φ : L.Formula (Fin n)),
    ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧ (φ ⇔[T] ψ)

/-- A model companion is a model-complete companion.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 3, line 276.
-/
def IsModelCompanionOf (Tstar T : L.Theory) : Prop :=
  Tstar.IsCompanion T ∧ Tstar.IsModelComplete

/-- Existence of a model-complete companion theory.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 3, line 276.
-/
def HasModelCompanion (T : L.Theory) : Prop :=
  ∃ Tstar : L.Theory, Tstar.IsModelCompanionOf T

/-- Existential formulas over the model reflect from extensions in its semantic universe.
Paper-ID: model_theory.basic_definitions; TeX: Definition 2.2, item 4, line 277.
-/
def IsExistentiallyClosedAt (T : L.Theory) (M : Type w) [L.Structure M] : Prop :=
  Nonempty M ∧ M ⊨ T ∧
    ∀ (N : T.ModelType.{u, v, max u v w}) (f : M ↪[L] N)
      {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M),
      φ.IsExistential → φ.Realize (f ∘ x) → φ.Realize x

end Language.Theory

end FirstOrder

namespace T3

open FirstOrder FirstOrder.Language FirstOrder.Group

/-- Every element has cube one, including in the trivial group.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
def HasExponentThree (G : Type*) [Group G] : Prop := ∀ g : G, g ^ 3 = 1

/-- Group theory together with the universal exponent law.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
def exponentGroupTheory (n : ℕ) : Language.group.Theory :=
  insert (FirstOrder.Group.exponentSentence n) Language.Theory.group

/-- The first-order theory `T₃`.
Paper-ID: preliminaries.exponent_three; TeX: lines 230–236.
-/
abbrev exponentThreeTheory : Language.group.Theory := exponentGroupTheory 3

/-- The exponent `t(n)` in the order of the free exponent-three group.
Paper-ID: preliminaries.finite_normal_form;
TeX: `fact:Levi and van der Waerden`, Fact 2.27, and line 823.
-/
def freeOrderExponent (n : ℕ) : ℕ := n + n.choose 2 + n.choose 3

/-- The strict-envelope bound `f₀(n) = 15n²`.
Paper-ID: structure.strict_envelope, main.proposition_a;
TeX: `proposition:bdd LCS`, Proposition 4.13, lines 1308–1314.
-/
def strictEnvelopeBound (n : ℕ) : ℕ := 15 * n ^ 2

/-- The explicit bound `f(m) = f₀((3m + 4)t(m) + 1)`.
Paper-ID: main.bounded_witness; TeX: `thm:main`, line 825.
-/
def witnessBound (m : ℕ) : ℕ := strictEnvelopeBound ((3 * m + 4) * freeOrderExponent m + 1)

namespace Amalgamation

variable {A : Type u} {G : Type v} {H : Type w} [Group A] [Group G] [Group H]
  (f : A →* G) (g : A →* H)

/-- An exponent-three group with embeddings of both factors that agree on the base.
Paper-ID: main.bounded_witness; TeX: `thm:main`, Theorem 3.3.
-/
def AmalgamableOver : Prop :=
  ∃ (K : Type (max v w)) (hK : Group K),
    letI := hK
    HasExponentThree K ∧ ∃ (i : G →* K) (j : H →* K),
      Function.Injective i ∧ Function.Injective j ∧ i.comp f = j.comp g

end Amalgamation

/-- Non-amalgamation has a witness with the paper's explicit uniform generator bound.
Paper-ID: main.bounded_witness; TeX: `thm:main`, Theorem 3.3, lines 795–833.
-/
theorem exists_bounded_nonamalgamation_witness {M : Type*} [Group M] [CompatibleGroup M]
    (hM : exponentThreeTheory.IsExistentiallyClosedAt M) (A : Subgroup M) [Group.FG A]
    {B : Type*} [Group B] [Group.FG B] (hB : HasExponentThree B)
    (j : A →* B) (hj : Function.Injective j) {m : ℕ} (hBm : Group.rank B ≤ m)
    (hna : ¬ Amalgamation.AmalgamableOver A.subtype j) :
    ∃ (D : Subgroup M) (hD : Group.FG D) (hAD : A ≤ D),
      letI := hD
      Group.rank D ≤ witnessBound m ∧
        ¬ Amalgamation.AmalgamableOver (Subgroup.inclusion hAD) j := by
  sorry

/-- The theory of groups of exponent three has a model companion.
Paper-ID: main.model_companion; TeX: Corollary 3.4, lines 836–838; no label.
-/
theorem has_model_companion : exponentThreeTheory.HasModelCompanion := by
  sorry

end T3
