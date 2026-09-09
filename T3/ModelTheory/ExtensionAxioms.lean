/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.Amalgamation

/-!
# Extension axioms with finitely many forbidden marked structures

For a finite inclusion `A → B` and a finite family `A → Cᵢ`, the extension axiom says that every
copy of `A` admitting none of the forbidden extensions extends to a copy of `B`. This is an
ordinary first-order sentence, formed using the full finite diagrams and finite conjunction.

This generalizes an earlier Boolean and quantifier construction by Yawara Ishida
from the group language to any finite language.
None of the finite structures is assumed to satisfy a theory or to be nonempty.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, line 255.
-/

@[expose] public noncomputable section

open scoped FirstOrder

universe u v w w' w'' w'''

namespace FirstOrder.Language

variable {L : Language.{u, v}} [Finite L.Symbols]
  {A : Type w} [L.Structure A] [Finite A]
  {B : Type w'} [L.Structure B] [Finite B]
  {ι : Type w''} [Finite ι] {C : ι → Type w'''}
  [∀ k, L.Structure (C k)] [∀ k, Finite (C k)]

/-- The formula excluding every extension from a finite marked family.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, line 255.
-/
def excludedExtensions (j : ∀ k, A ↪[L] C k) : L.Formula A :=
  Formula.iInf fun k => (extensionFormula (L := L) (j k : A → C k)).not

/-- The exclusion formula means that no member of the family embeds over the assignment.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, line 255.
-/
theorem realize_excludedExtensions {M : Type*} [L.Structure M]
    (j : ∀ k, A ↪[L] C k) (a : A → M) :
    (excludedExtensions j).Realize a ↔ ∀ k, ¬ ∃ f : C k ↪[L] M, f ∘ j k = a := by
  simp only [excludedExtensions, Formula.realize_iInf, Formula.realize_not,
    realize_extensionFormula_iff]

/-- The extension axiom attached to a finite inclusion and a finite forbidden family.
The full diagram of `A` ensures that quantified assignments really are embeddings.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, line 255.
-/
def extensionAxiom (i : A ↪[L] B) (j : ∀ k, A ↪[L] C k) : L.Sentence :=
  Formula.iAlls A (((finiteDiagram (L := L) A ⊓ excludedExtensions j).imp
    (extensionFormula (L := L) (i : A → B))).relabel Sum.inr)

/-- The extension axiom holds precisely when every marked copy of the base with no forbidden
extension has an embedding of the prescribed extension over it.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v4.tex, `fact:locally finiteness and model companion`, lines 255–262.
-/
theorem realize_extensionAxiom_iff {M : Type*} [L.Structure M]
    (i : A ↪[L] B) (j : ∀ k, A ↪[L] C k) :
    M ⊨ extensionAxiom i j ↔
      ∀ a : A ↪[L] M, (∀ k, ¬ ∃ f : C k ↪[L] M, f.comp (j k) = a) →
        ∃ f : B ↪[L] M, f.comp i = a := by
  have hraw : M ⊨ extensionAxiom i j ↔
      ∀ x : A → M, (∃ e : A ↪[L] M, (e : A → M) = x) →
        (∀ k, ¬ ∃ f : C k ↪[L] M, f ∘ j k = x) →
          ∃ f : B ↪[L] M, f ∘ i = x := by
    rw [Sentence.Realize, extensionAxiom, Formula.realize_iAlls]
    refine forall_congr' fun x => ?_
    rw [Formula.realize_relabel]
    change ((finiteDiagram (L := L) A ⊓ excludedExtensions j).imp
      (extensionFormula (L := L) (i : A → B))).Realize x ↔ _
    rw [Formula.realize_imp, Formula.realize_inf, realize_finiteDiagram_iff,
      realize_excludedExtensions, realize_extensionFormula_iff]
    exact and_imp
  rw [hraw]
  constructor
  · intro h a hgood
    obtain ⟨f, hf⟩ := h a ⟨a, rfl⟩ (fun k ⟨g, hg⟩ =>
      hgood k ⟨g, Embedding.ext (congrFun hg)⟩)
    exact ⟨f, Embedding.ext (congrFun hf)⟩
  · intro h x hx hgood
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨f, hf⟩ := h a (fun k ⟨g, hg⟩ => hgood k ⟨g, congrArg DFunLike.coe hg⟩)
    exact ⟨f, congrArg DFunLike.coe hf⟩

end FirstOrder.Language
