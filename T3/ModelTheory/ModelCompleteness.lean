/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelCompanion
public import Mathlib.Basic.Finite.Sigma

/-!
# Syntactic and semantic model completeness

`Theory.isModelComplete_iff_allEmbeddingsElementary` proves that the paper's syntactic definition
of model completeness is equivalent to elementary preservation by embeddings of models in the
canonical semantic universe. The syntactic conclusion then gives formula preservation and
reflection between models in arbitrary universes by `Theory.IsModelComplete.realize_embedding_iff`.

The proof first uses compactness to force each true parameter formula by finitely many
quantifier-free diagram facts. It replaces their constants by existential variables, retaining
the original parameter tuple through equations. A second compactness argument chooses finitely
many of these local formulas. Their quantifier-free matrices are combined under one existential
prefix, giving the required existential equivalent.

The compactness step uses mathlib's `Theory.models_iff_finset_models`.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2, line 260; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w' x

namespace FirstOrder.Language

open Structure

variable {L : Language.{u, v}}

namespace BoundedFormula

variable {α : Type w} {n : ℕ}

/-- Existentially closing the bound variables preserves existential formulas.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem IsExistential.exs : ∀ {n : ℕ} {φ : L.BoundedFormula α n},
    φ.IsExistential → φ.exs.IsExistential
  | 0, _, h => h
  | _ + 1, _, h => h.ex.exs

private theorem isQF_foldr_inf : ∀ {l : List (L.BoundedFormula α n)},
    (∀ ψ ∈ l, ψ.IsQF) → (l.foldr (· ⊓ ·) ⊤).IsQF
  | [], _ => IsQF.top
  | ψ :: l, h =>
    (h ψ (by simp)).inf (isQF_foldr_inf fun χ hχ => h χ (by simp [hχ]))

/-- A finite conjunction of quantifier-free formulas is quantifier free.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem isQF_iInf {β : Type w'} [Finite β] {f : β → L.BoundedFormula α n}
    (h : ∀ b, (f b).IsQF) : (iInf f).IsQF := by
  simp only [iInf]
  exact isQF_foldr_inf fun ψ hψ => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hψ
    exact h b

private theorem isQF_foldr_sup : ∀ {l : List (L.BoundedFormula α n)},
    (∀ ψ ∈ l, ψ.IsQF) → (l.foldr (· ⊔ ·) ⊥).IsQF
  | [], _ => isQF_bot
  | ψ :: l, h =>
    (h ψ (by simp)).sup (isQF_foldr_sup fun χ hχ => h χ (by simp [hχ]))

/-- A finite disjunction of quantifier-free formulas is quantifier free.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem isQF_iSup {β : Type w'} [Finite β] {f : β → L.BoundedFormula α n}
    (h : ∀ b, (f b).IsQF) : (iSup f).IsQF := by
  simp only [iSup]
  exact isQF_foldr_sup fun ψ hψ => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hψ
    exact h b

/-- Existentially quantifying a finite set of variables in a quantifier-free matrix gives an
existential formula.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem IsQF.isExistential_iExs {β : Type w'} [Finite β] {φ : L.Formula (α ⊕ β)}
    (h : φ.IsQF) : (φ.iExs β).IsExistential := by
  simp only [Formula.iExs]
  exact ((h.relabel _).isExistential).exs

end BoundedFormula

namespace Formula

variable {α : Type w} {ι : Type w'} [Finite ι] (k : ι → ℕ)
  (θ : ∀ i, L.Formula (α ⊕ Fin (k i)))

/-- Combine finitely many existential formulas by quantifying all their witness variables
and taking the disjunction of their matrices. This has one existential prefix.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
noncomputable def existentialDisjunction : L.Formula α :=
  (Formula.iSup fun i => (θ i).relabel (Sum.map id (Sigma.mk i))).iExs (Σ i, Fin (k i))

/-- The finite disjunction construction is existential when all its matrices are quantifier free.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem isExistential_existentialDisjunction (hθ : ∀ i, (θ i).IsQF) :
    (existentialDisjunction k θ).IsExistential :=
  (BoundedFormula.isQF_iSup fun i => (hθ i).relabel _).isExistential_iExs

/-- The combined formula holds exactly when one of the original existential formulas holds.
Nonemptiness supplies unused witnesses for the other disjuncts.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem realize_existentialDisjunction {N : Type x} [L.Structure N] [Nonempty N]
    (a : α → N) : (existentialDisjunction k θ).Realize a ↔
      ∃ i, ((θ i).iExs (Fin (k i))).Realize a := by
  classical
  simp only [existentialDisjunction, Formula.realize_iExs, Formula.realize_iSup,
    Formula.realize_relabel]
  constructor
  · rintro ⟨w, i, hi⟩
    refine ⟨i, fun j => w ⟨i, j⟩, ?_⟩
    convert hi using 1
    funext z
    cases z <;> rfl
  · rintro ⟨i, w, hw⟩
    let ws : (Σ j, Fin (k j)) → N := fun z =>
      if h : z.1 = i then w (h ▸ z.2) else Classical.choice (inferInstance : Nonempty N)
    refine ⟨ws, i, ?_⟩
    convert hw using 1
    funext z
    cases z <;> simp [ws]

end Formula

variable (L) in
/-- The quantifier-free diagram consists of all true finite quantifier-free formulas after
substituting constants for their parameters.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
def qfDiagram (M : Type w) [L.Structure M] : L[[M]].Theory :=
  {θ | ∃ (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
    φ.IsQF ∧ φ.Realize a ∧ θ = Formula.equivSentence (φ.relabel a)}

/-- Substitution of parameters into a sentence realizes the formula at their interpretations.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
theorem realize_equivSentence_relabel {M : Type w} {N : Type w'} [L[[M]].Structure N]
    [L.Structure N] [(L.lhomWithConstants M).IsExpansionOn N]
    {α : Type x} (φ : L.Formula α) (a : α → M) :
    N ⊨ Formula.equivSentence (φ.relabel a) ↔ φ.Realize (fun i => (L.con (a i) : N)) := by
  rw [Formula.realize_equivSentence]
  exact Formula.realize_relabel

/-- A model of the quantifier-free diagram receives a canonical embedding of the original
structure, sending each element to the interpretation of its constant.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
def Embedding.ofModelsQfDiagram (L : Language.{u, v}) (M : Type w) [L.Structure M]
    (N : Type w') [L.Structure N] [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] [N ⊨ L.qfDiagram M] : M ↪[L] N := by
  classical
  have hqf : ∀ (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
      φ.IsQF → φ.Realize a → φ.Realize (fun i => (L.con (a i) : N)) := by
    intro n φ a hφ ha
    have hmem : Formula.equivSentence (φ.relabel a) ∈ L.qfDiagram M :=
      ⟨n, φ, a, hφ, ha, rfl⟩
    have hN := Theory.realize_sentence_of_mem (L.qfDiagram M) hmem (M := N)
    rwa [realize_equivSentence_relabel] at hN
  have hinj : Function.Injective (fun a : M => (L.con a : N)) := by
    intro a b hab
    by_contra hne
    have hM : (((Term.var (0 : Fin 2)).equal (Term.var 1)).not : L.Formula (Fin 2)).Realize
        ![a, b] := by
      rw [Formula.realize_not, Formula.realize_equal]
      simpa using hne
    have hN := hqf 2 (((Term.var (0 : Fin 2)).equal (Term.var 1)).not) ![a, b]
      ((BoundedFormula.IsAtomic.equal _ _).isQF.not) hM
    rw [Formula.realize_not, Formula.realize_equal] at hN
    exact hN (by simpa using hab)
  have hfun : ∀ {n : ℕ} (F : L.Functions n) (a : Fin n → M),
      (L.con (funMap F a) : N) = funMap F (fun i => (L.con (a i) : N)) := by
    intro n F a
    have hM : (Formula.graph F).Realize (Fin.cons (funMap F a) a) :=
      Formula.realize_graph.mpr rfl
    have hN := hqf (n + 1) (Formula.graph F) (Fin.cons (funMap F a) a)
      (Formula.isAtomic_graph F).isQF hM
    have hcons : (fun i => (L.con ((Fin.cons (funMap F a) a : Fin (n + 1) → M) i) : N)) =
        Fin.cons (L.con (funMap F a) : N) (fun i => (L.con (a i) : N)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
      · simp only [Fin.cons_succ]
    rw [hcons, Formula.realize_graph] at hN
    exact hN.symm
  have hrel : ∀ {n : ℕ} (R : L.Relations n) (a : Fin n → M),
      RelMap R (fun i => (L.con (a i) : N)) ↔ RelMap R a := by
    intro n R a
    constructor
    · intro hN
      by_contra hR
      have hM : ((R.formula Term.var).not : L.Formula (Fin n)).Realize a := by
        rw [Formula.realize_not, Formula.realize_rel]
        simpa using hR
      have h := hqf n ((R.formula Term.var).not) a ((R.isAtomic _).isQF.not) hM
      rw [Formula.realize_not, Formula.realize_rel] at h
      exact h hN
    · intro hR
      have hM : (R.formula Term.var).Realize a := by
        rw [Formula.realize_rel]
        simpa using hR
      have h := hqf n (R.formula Term.var) a (R.isAtomic _).isQF hM
      rw [Formula.realize_rel] at h
      exact h
  exact ⟨⟨fun a => (L.con a : N), hinj⟩, fun F a => hfun F a, fun R a => hrel R a⟩

/-- The canonical quantifier-free-diagram embedding sends an element to its named constant.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, item 2; no label.
-/
@[simp]
theorem Embedding.ofModelsQfDiagram_apply (L : Language.{u, v}) (M : Type w) [L.Structure M]
    (N : Type w') [L.Structure N] [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] [N ⊨ L.qfDiagram M] (a : M) :
    Embedding.ofModelsQfDiagram L M N a = (L.con a : N) := rfl

namespace Theory

variable {T : L.Theory}

/-- If every embedding of models is elementary, the theory together with the quantifier-free
diagram of a model entails every formula true of its named tuples.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2; no label.
-/
theorem AllEmbeddingsElementary.models_equivSentence_of_qfDiagram
    (h : T.AllEmbeddingsElementary) (M : T.ModelType.{u, v, max u v})
    {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) (hφ : φ.Realize a) :
    (L.lhomWithConstants (M : Type (max u v))).onTheory T ∪
      L.qfDiagram (M : Type (max u v)) ⊨ᵇ Formula.equivSentence (φ.relabel a) := by
  apply models_sentence_iff.mpr
  intro N
  let : L.Structure N := (L.lhomWithConstants (M : Type (max u v))).reduct N
  have hNT : N ⊨ T := (LHom.onTheory_model _ _).mp
    (N.is_model.mono Set.subset_union_left)
  have : N ⊨ L.qfDiagram (M : Type (max u v)) :=
    N.is_model.mono Set.subset_union_right
  let f := Embedding.ofModelsQfDiagram L (M : Type (max u v)) N
  obtain ⟨e, he⟩ := h M (ModelType.of T N) f
  have heval : e ∘ a = fun i => (L.con (a i) : N) := by
    funext i
    exact congrArg (fun k : M ↪[L] ModelType.of T N => k (a i)) he
  rw [realize_equivSentence_relabel, ← heval]
  exact (e.map_formula φ a).mpr hφ

/-- In a semantically model-complete theory, every true parameter formula is forced by finitely
many true quantifier-free facts together with the original theory. This gives the finite input
for replacing the extra named constants by existentially quantified variables.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2; no label.
-/
theorem AllEmbeddingsElementary.exists_finset_qfDiagram_entails
    (h : T.AllEmbeddingsElementary) (M : T.ModelType.{u, v, max u v})
    {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) (hφ : φ.Realize a) :
    ∃ Δ : Finset L[[(M : Type (max u v))]].Sentence,
      (Δ : L[[(M : Type (max u v))]].Theory) ⊆ L.qfDiagram (M : Type (max u v)) ∧
      ((L.lhomWithConstants (M : Type (max u v))).onTheory T ∪
        (Δ : L[[(M : Type (max u v))]].Theory)) ⊨ᵇ Formula.equivSentence (φ.relabel a) := by
  classical
  obtain ⟨Θ, hΘ, hforces⟩ := models_iff_finset_models.mp
    (h.models_equivSentence_of_qfDiagram M φ a hφ)
  let Δ := Θ.filter (· ∈ L.qfDiagram (M : Type (max u v)))
  refine ⟨Δ, fun θ hθ => (Finset.mem_filter.mp hθ).2, ?_⟩
  apply models_sentence_iff.mpr
  intro N
  have : N ⊨ (Θ : L[[(M : Type (max u v))]].Theory) := N.is_model.mono (by
    intro θ hθ
    rcases hΘ hθ with hT | hd
    · exact Set.mem_union_left _ hT
    · exact Set.mem_union_right _ (Finset.mem_filter.mpr ⟨hθ, hd⟩))
  exact hforces.realize_sentence N

/-- Every true parameter formula in a semantically model-complete theory has an existential
neighborhood implying it over the theory. The matrix is quantifier free and its witnesses are
indexed by a finite tuple. Equations retain repeated entries of the original parameter tuple.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2; no label.
-/
theorem AllEmbeddingsElementary.exists_qf_existential_imp
    (h : T.AllEmbeddingsElementary) (M : T.ModelType.{u, v, max u v})
    {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) (hφ : φ.Realize a) :
    ∃ (k : ℕ) (θ : L.Formula (Fin n ⊕ Fin k)), θ.IsQF ∧
      (θ.iExs (Fin k)).Realize a ∧ (θ.iExs (Fin k) ⟹[T] φ) := by
  classical
  obtain ⟨Δ, hΔ, hforces⟩ := h.exists_finset_qfDiagram_entails M φ a hφ
  have hdata : ∀ δ : Δ, ∃ (k : ℕ) (ψ : L.Formula (Fin k)) (b : Fin k → M),
      ψ.IsQF ∧ ψ.Realize b ∧ δ.val = Formula.equivSentence (ψ.relabel b) :=
    fun δ => hΔ δ.property
  choose kk ff bb hqf hreal heq using hdata
  let s : Finset M := Finset.image a Finset.univ ∪
    Finset.univ.biUnion (fun δ : Δ => Finset.image (bb δ) Finset.univ)
  have ha (i : Fin n) : a i ∈ s :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hb (δ : Δ) (i : Fin (kk δ)) : bb δ i ∈ s :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨δ, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
  let ia (i : Fin n) : Fin s.card := s.equivFin ⟨a i, ha i⟩
  let ib (δ : Δ) (i : Fin (kk δ)) : Fin s.card := s.equivFin ⟨bb δ i, hb δ i⟩
  let facts : L.Formula (Fin n ⊕ Fin s.card) :=
    Formula.iInf (fun δ : Δ => (ff δ).relabel (fun i => Sum.inr (ib δ i)))
  let eqs : L.Formula (Fin n ⊕ Fin s.card) := Formula.iInf (fun i : Fin n =>
    (Term.var (Sum.inl i)).equal (Term.var (Sum.inr (ia i))))
  let θ := facts ⊓ eqs
  have hθ : θ.IsQF := (BoundedFormula.isQF_iInf fun δ => (hqf δ).relabel _).inf
    (BoundedFormula.isQF_iInf fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF)
  refine ⟨s.card, θ, hθ, ?_, ?_⟩
  · rw [Formula.realize_iExs]
    refine ⟨fun i => (s.equivFin.symm i).val, ?_⟩
    simp only [θ, facts, eqs, Formula.realize_inf, Formula.realize_iInf,
      Formula.realize_relabel, Formula.realize_equal, Term.realize_var,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, ia, ib, _root_.Equiv.symm_apply_apply]
    exact ⟨hreal, fun _ => trivial⟩
  · apply models_formula_iff.mpr
    intro N x hx
    obtain ⟨w, hw⟩ := Formula.realize_iExs.mp hx
    have hwfacts := (Formula.realize_inf.mp hw).1
    have hweqs := (Formula.realize_inf.mp hw).2
    simp only [facts, Formula.realize_iInf, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr] at hwfacts
    simp only [eqs, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Sum.elim_inl, Sum.elim_inr] at hweqs
    let val : M → N := fun b => if hb : b ∈ s then w (s.equivFin ⟨b, hb⟩)
      else Classical.choice (inferInstance : Nonempty N)
    have hval (b : M) (hb : b ∈ s) : val b = w (s.equivFin ⟨b, hb⟩) := dite_eq_left hb
    let : (constantsOn (M : Type (max u v))).Structure N := constantsOn.structure val
    have hNT : N ⊨ (L.lhomWithConstants (M : Type (max u v))).onTheory T :=
      (LHom.onTheory_model _ _).mpr N.is_model
    have hND : N ⊨ (Δ : L[[(M : Type (max u v))]].Theory) := by
      apply (Theory.model_iff _).mpr
      intro δ hδ
      have hδeq : δ = Formula.equivSentence ((ff ⟨δ, hδ⟩).relabel (bb ⟨δ, hδ⟩)) := heq ⟨δ, hδ⟩
      rw [hδeq, realize_equivSentence_relabel]
      change (ff ⟨δ, hδ⟩).Realize (fun i => val (bb ⟨δ, hδ⟩ i))
      simpa only [hval _ (hb _ _), ib] using hwfacts ⟨δ, hδ⟩
    have : N ⊨ (L.lhomWithConstants (M : Type (max u v))).onTheory T ∪
        (Δ : L[[(M : Type (max u v))]].Theory) := hNT.union hND
    have hN := hforces.realize_sentence N
    rw [realize_equivSentence_relabel] at hN
    change φ.Realize (fun i => val (a i)) at hN
    have hva : (fun i => val (a i)) = x := by
      funext i
      exact (hval _ (ha i)).trans (hweqs i).symm
    rwa [hva] at hN

/-- If every embedding between models is elementary, every formula is equivalent over the
theory to an existential formula. Compactness selects finitely many local existential
neighborhoods, and their matrices are combined under a single existential prefix.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2, line 260; no label.
-/
theorem AllEmbeddingsElementary.isModelComplete (h : T.AllEmbeddingsElementary) :
    T.IsModelComplete := by
  classical
  intro n φ
  let negs : L[[Fin n]].Theory := {σ | ∃ (k : ℕ) (θ : L.Formula (Fin n ⊕ Fin k)),
    θ.IsQF ∧ (θ.iExs (Fin k) ⟹[T] φ) ∧ σ = (Formula.equivSentence (θ.iExs (Fin k))).not}
  have hneg : (L.lhomWithConstants (Fin n)).onTheory T ∪ negs ⊨ᵇ
      (Formula.equivSentence φ).not := by
    apply models_sentence_iff.mpr
    intro M
    let : L.Structure M := (L.lhomWithConstants (Fin n)).reduct M
    have : M ⊨ T := (LHom.onTheory_model _ _).mp
      (M.is_model.mono Set.subset_union_left)
    rw [Sentence.realize_not, Formula.realize_equivSentence]
    intro hφ
    obtain ⟨k, θ, hqf, hθ, himp⟩ := h.exists_qf_existential_imp (ModelType.of T M) φ
      (fun i => (L.con i : M)) hφ
    have hmem : (Formula.equivSentence (θ.iExs (Fin k))).not ∈
        (L.lhomWithConstants (Fin n)).onTheory T ∪ negs :=
      Set.mem_union_right _ ⟨k, θ, hqf, himp, rfl⟩
    have hn := M.is_model.realize_of_mem _ hmem
    rw [Sentence.realize_not, Formula.realize_equivSentence] at hn
    exact hn hθ
  obtain ⟨Ω, hΩ, hforces⟩ := models_iff_finset_models.mp hneg
  let Δ := Ω.filter (· ∈ negs)
  have hdata : ∀ δ : Δ, ∃ (k : ℕ) (θ : L.Formula (Fin n ⊕ Fin k)), θ.IsQF ∧
      (θ.iExs (Fin k) ⟹[T] φ) ∧ δ.val = (Formula.equivSentence (θ.iExs (Fin k))).not :=
    fun δ => (Finset.mem_filter.mp δ.property).2
  choose kk θ hqf himp heq using hdata
  let ψ := Formula.existentialDisjunction kk θ
  refine ⟨ψ, Formula.isExistential_existentialDisjunction kk θ hqf, imp_antisymm ?_ ?_⟩
  · apply models_formula_iff.mpr
    intro N a hφ
    apply (Formula.realize_existentialDisjunction kk θ a).mpr
    by_contra hn
    let : (constantsOn (Fin n)).Structure N := constantsOn.structure a
    have hNT : N ⊨ (L.lhomWithConstants (Fin n)).onTheory T :=
      (LHom.onTheory_model _ _).mpr N.is_model
    have : N ⊨ (Ω : L[[Fin n]].Theory) := by
      apply (Theory.model_iff _).mpr
      intro δ hδ
      rcases hΩ hδ with hδT | hδneg
      · exact hNT.realize_of_mem _ hδT
      · have hδΔ : δ ∈ Δ := Finset.mem_filter.mpr ⟨hδ, hδneg⟩
        have hδeq : δ = (Formula.equivSentence ((θ ⟨δ, hδΔ⟩).iExs (Fin (kk ⟨δ, hδΔ⟩)))).not :=
          heq ⟨δ, hδΔ⟩
        rw [hδeq, Sentence.realize_not, Formula.realize_equivSentence]
        exact fun hθ => hn ⟨⟨δ, hδΔ⟩, hθ⟩
    have hnot := hforces.realize_sentence N
    rw [Sentence.realize_not, Formula.realize_equivSentence] at hnot
    exact hnot hφ
  · apply models_formula_iff.mpr
    intro N a hψ
    obtain ⟨δ, hδ⟩ := (Formula.realize_existentialDisjunction kk θ a).mp hψ
    exact himp δ N a default hδ

/-- The syntactic model completeness used in the paper is equivalent to elementary preservation
by embeddings of bundled models in the canonical semantic universe.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, semantic comparison for Definition 2.2, item 2, line 260; no label.
-/
theorem isModelComplete_iff_allEmbeddingsElementary :
    T.IsModelComplete ↔ T.AllEmbeddingsElementary :=
  ⟨IsModelComplete.allEmbeddingsElementary, AllEmbeddingsElementary.isModelComplete⟩

/-- An embedding into a model of a model-complete theory is elementary if it reflects existential
formulas. The source is not assumed to satisfy the theory. The Tarski-Vaught witnesses are
obtained from the finite quantifier-free matrices constructed above.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v7.tex, supporting Definition 2.2, items 2 and 4; no label.
-/
theorem IsModelComplete.exists_elementaryEmbedding_of_existential_reflection
    (h : T.IsModelComplete) {M : Type (max u v)} [L.Structure M]
    (N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N)
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
  obtain ⟨k, θ, hqf, hθ, himp⟩ := hsem.exists_qf_existential_imp N φ'
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
  exact himp N (Fin.snoc (f ∘ x) (f b)) default hθN

end Theory

end FirstOrder.Language
