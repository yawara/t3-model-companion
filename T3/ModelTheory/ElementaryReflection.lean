/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelEmbeddings

/-!
# Existential reflection and elementary embeddings in arbitrary universes

Finite Skolem hulls transfer the quantifier-free existential neighborhoods used in the
Tarski-Vaught proof to arbitrary models. The source of the embedding need not model the theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, Definition 2.2, items 2 and 4, lines 275–277; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} {T : L.Theory}

/-- In a model-complete theory, a true parameter formula in an arbitrary model has a
quantifier-free existential neighborhood implying it over the theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, item 2; no label.
-/
theorem AllEmbeddingsElementary.exists_qf_existential_imp_of_model
    (h : T.AllEmbeddingsElementary) (M : Type w) [L.Structure M] [Nonempty M] [M ⊨ T]
    {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) (ha : φ.Realize a) :
    ∃ (k : ℕ) (θ : L.Formula (Fin n ⊕ Fin k)), θ.IsQF ∧
      (θ.iExs (Fin k)).Realize a ∧ (θ.iExs (Fin k) ⟹[T] φ) := by
  classical
  obtain ⟨S, hS, hsmall⟩ := exists_small_elementarySubstructure_containing_finset
    (L := L) M (Finset.univ.image a)
  let := hsmall
  let N : T.ModelType.{u, v, max u v} := (ModelType.of T S).shrink
  let e : S ≃[L] N := (equivShrink S).inducedStructureEquiv
  let a' : Fin n → S := fun i => ⟨a i, hS (by simp)⟩
  have ha' : φ.Realize a' := (S.subtype.map_formula φ a').mp ha
  have heφ := e.toElementaryEmbedding.map_formula φ a'
  simp only [Equiv.coe_toElementaryEmbedding] at heφ
  obtain ⟨k, θ, hθ, hr, himp⟩ := h.exists_qf_existential_imp N φ (e ∘ a') (heφ.mpr ha')
  refine ⟨k, θ, hθ, ?_, himp⟩
  have heθ := e.toElementaryEmbedding.map_formula (θ.iExs (Fin k)) a'
  simp only [Equiv.coe_toElementaryEmbedding] at heθ
  exact (S.subtype.map_formula _ a').mpr (heθ.mp hr)

/-- An embedding into a model of a model-complete theory is elementary if it reflects existential
formulas. The source is not assumed to satisfy the theory. The Tarski-Vaught witnesses are
obtained from the finite quantifier-free matrices constructed above.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v9.tex, supporting Definition 2.2, items 2 and 4; no label.
-/
theorem IsModelComplete.exists_elementaryEmbedding_of_reflects_existential
    (h : T.IsModelComplete) {M : Type w} [L.Structure M]
    (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T] (f : M ↪[L] N)
    (hex : ∀ {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M),
      φ.IsExistential → φ.Realize (f ∘ a) → φ.Realize a) :
    ∃ e : M ↪ₑ[L] N, e.toEmbedding = f := by
  classical
  have hsem : T.AllEmbeddingsElementary := h.allEmbeddingsElementary
  refine ⟨f.toElementaryEmbedding ?_, Embedding.ext fun _ => rfl⟩
  intro n φ x a hφ
  let φ' : L.Formula (Fin (n + 1)) := φ.toFormula.relabel (Sum.elim Empty.elim id)
  have hreal (y : Fin (n + 1) → N) : φ'.Realize y ↔ φ.Realize default y := by
    simp only [φ', Formula.realize_relabel, BoundedFormula.realize_toFormula,
      Function.comp_def, Sum.elim_inr, id_eq, Unique.eq_default]
  obtain ⟨k, θ, hqf, hθ, himp⟩ := hsem.exists_qf_existential_imp_of_model N φ'
    (Fin.snoc (f ∘ x) a) ((hreal _).mpr hφ)
  obtain ⟨w, hw⟩ := Formula.realize_iExs.mp hθ
  let eqs : L.Formula (Fin n ⊕ (Fin (n + 1) ⊕ Fin k)) := Formula.iInf (fun i : Fin n =>
    (Term.var (Sum.inl i)).equal (Term.var (Sum.inr (Sum.inl i.castSucc))))
  let χ := θ.relabel Sum.inr ⊓ eqs
  have hχ : χ.IsQF := (hqf.relabel _).inf
    (BoundedFormula.isQF_iInf fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF)
  have hN : (χ.iExs (Fin (n + 1) ⊕ Fin k)).Realize (f ∘ x) := by
    apply Formula.realize_iExs.mpr
    refine ⟨Sum.elim (Fin.snoc (f ∘ x) a) w, ?_⟩
    simp only [χ, eqs, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc]
    exact ⟨hw, fun _ => trivial⟩
  have hM := hex _ x hχ.isExistential_iExs hN
  obtain ⟨v, hv⟩ := Formula.realize_iExs.mp hM
  have hθM := (Formula.realize_inf.mp hv).1
  have heqs := (Formula.realize_inf.mp hv).2
  simp only [Formula.realize_relabel, Function.comp_def, Sum.elim_inr] at hθM
  simp only [eqs, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr] at heqs
  let b := v (Sum.inl (Fin.last n))
  have hvx : (fun i => v (Sum.inl i)) = Fin.snoc x b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, b]
    · simpa only [Fin.snoc_castSucc] using (heqs j).symm
  have hθN : (θ.iExs (Fin k)).Realize (Fin.snoc (f ∘ x) (f b)) := by
    apply Formula.realize_iExs.mpr
    refine ⟨fun i => f (v (Sum.inr i)), ?_⟩
    have htrans : θ.Realize (f ∘ v) := by
      simpa only [Formula.Realize, Unique.eq_default (f ∘ default)] using
        hqf.isExistential.realize_embedding f hθM
    convert htrans using 1
    funext i
    cases i with
    | inl i =>
      rw [Function.comp_apply, Sum.elim_inl, ← Fin.comp_snoc]
      exact congrArg f (congrFun hvx i).symm
    | inr i => rfl
  refine ⟨b, (hreal _).mp ?_⟩
  exact (himp.realize_formula N) hθN


end FirstOrder.Language.Theory
