/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.FiniteDiagram
public import T3.ModelTheory.ElementaryChain

/-!
# Robinson's model-completeness test

An embedding-reflection hypothesis for existential formulas implies syntactic model
completeness. Compactness supplies an alternating chain with elementary two-step composites;
the elementary chain theorem makes the original embedding elementary. The existing
`AllEmbeddingsElementary.isModelComplete` bridge supplies the syntactic conclusion required by
Definition 2.2(2).

The quantifier-free diagram construction and the semantic-to-syntactic bridge use the general
model-theory API. No universal, Π₂, finite-language, or local-finiteness hypothesis is required
for Robinson's test itself.
Model quantifiers use the canonical semantic universe `Type (max u v)`.

Paper-ID: `model_theory.companion_iff_ec`.
Source: `T3_modelcompanion_v9.tex`, Fact 2.3, lines 289–295.
-/

@[expose] public section

open scoped FirstOrder

universe u v x

namespace FirstOrder

namespace Language

namespace Theory

open Structure

variable {L : Language.{u, v}} {T : L.Theory}

/-- Every embedding between models of the theory reflects existential formulas.

Model quantifiers use the canonical semantic universe `Type (max u v)`.

Paper-ID: `model_theory.companion_iff_ec`.
Source: `T3_modelcompanion_v9.tex`, Fact 2.3, lines 289–295. -/
def IsExistentiallyClosedInModels (T : L.Theory) : Prop :=
  ∀ (M N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N) {n : ℕ}
    (φ : L.Formula (Fin n)) (x : Fin n → M),
    φ.IsExistential → φ.Realize (f ∘ x) → φ.Realize x

/--
The key consequence of the hypothesis of Robinson's test: any finite family of quantifier-free
facts with parameters in `B` can be realized in `A` by a single interpretation `v : B → A` of
the parameters that inverts `h` on its range.

The shared parameter support is existentially quantified at once, so that equal parameters in
different facts receive the same witness.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem IsExistentiallyClosedInModels.exists_assignment
    (hec : T.IsExistentiallyClosedInModels)
    (A B : T.ModelType.{u, v, max u v}) (h : A ↪[L] B)
    {κ : Type x} [Finite κ] {nn : κ → ℕ}
    (ff : ∀ θ : κ, L.Formula (Fin (nn θ))) (bb : ∀ θ : κ, Fin (nn θ) → B)
    (hQF : ∀ θ, (ff θ).IsQF) (hReal : ∀ θ, (ff θ).Realize (bb θ)) :
    ∃ v : B → (A : Type (max u v)), v ∘ ⇑h = id ∧ ∀ θ, (ff θ).Realize (v ∘ bb θ) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  -- The finite parameter support, split into the range of `h` and its complement.
  set s : Finset (B : Type (max u v)) :=
    Finset.univ.biUnion (fun θ : κ => Finset.image (bb θ) Finset.univ) with hs
  have hmem : ∀ (θ : κ) (i : Fin (nn θ)), bb θ i ∈ s := fun θ i => by
    rw [hs]
    exact Finset.mem_biUnion.2
      ⟨θ, Finset.mem_univ θ, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  set sIn : Finset (B : Type (max u v)) := s.filter (· ∈ Set.range ⇑h) with hsIn
  set sOut : Finset (B : Type (max u v)) := s.filter (· ∉ Set.range ⇑h) with hsOut
  -- The variables of the conjunction: one for each element of the support.
  set ρ : ∀ θ : κ, Fin (nn θ) → (↥sIn ⊕ ↥sOut) := fun θ i =>
    if hb : bb θ i ∈ Set.range ⇑h
    then Sum.inl ⟨bb θ i, Finset.mem_filter.2 ⟨hmem θ i, hb⟩⟩
    else Sum.inr ⟨bb θ i, Finset.mem_filter.2 ⟨hmem θ i, hb⟩⟩ with hρ
  set conj : L.Formula (↥sIn ⊕ ↥sOut) :=
    Formula.iInf (fun θ : κ => Formula.relabel (ρ θ) (ff θ)) with hconj
  set Ψ : L.Formula (Fin sIn.card) :=
    Formula.relabel ⇑sIn.equivFin (conj.iExs ↥sOut) with hΨdef
  -- Parameters in `A` for the in-range part of the support.
  have hpre : ∀ z : ↥sIn, ∃ a : (A : Type (max u v)), h a = ↑z := fun z =>
    (Finset.mem_filter.1 z.2).2
  choose pre hpre_spec using hpre
  set X : Fin sIn.card → (A : Type (max u v)) := fun k => pre (sIn.equivFin.symm k) with hX
  have hXB : ∀ k, h (X k) = ↑(sIn.equivFin.symm k) := fun k => hpre_spec _
  -- `Ψ` is realized in `B` at the parameters `h ∘ X`, witnessed by the support itself.
  have hΨB : Ψ.Realize (⇑h ∘ X) := by
    rw [hΨdef, Formula.realize_relabel, Formula.realize_iExs]
    refine ⟨fun z => ↑z, ?_⟩
    rw [hconj, Formula.realize_iInf]
    intro θ
    rw [Formula.realize_relabel]
    have hasgn : (Sum.elim ((⇑h ∘ X) ∘ ⇑sIn.equivFin)
        (fun z : ↥sOut => (z : (B : Type (max u v)))) ∘ ρ θ) = bb θ := by
      funext i
      by_cases hb : bb θ i ∈ Set.range ⇑h
      · have hρi : ρ θ i = Sum.inl ⟨bb θ i, Finset.mem_filter.2 ⟨hmem θ i, hb⟩⟩ := by
          rw [hρ]; exact dite_eq_left hb
        simp only [Function.comp_apply, hρi, Sum.elim_inl]
        rw [hXB]
        exact congrArg Subtype.val (sIn.equivFin.symm_apply_apply _)
      · have hρi : ρ θ i = Sum.inr ⟨bb θ i, Finset.mem_filter.2 ⟨hmem θ i, hb⟩⟩ := by
          rw [hρ]; exact dite_eq_right hb
        rw [Function.comp_apply, hρi]
        rfl
    rw [hasgn]
    exact hReal θ
  -- Push the existential formula `Ψ` down into `A`.
  have hΨA : Ψ.Realize X := by
    refine hec A B h Ψ X ?_ hΨB
    rw [hΨdef]
    refine BoundedFormula.IsExistential.relabel ?_ _
    rw [hconj]
    exact (BoundedFormula.isQF_iInf fun θ => (hQF θ).relabel _).isExistential_iExs
  rw [hΨdef, Formula.realize_relabel, Formula.realize_iExs] at hΨA
  obtain ⟨w, hw⟩ := hΨA
  rw [hconj, Formula.realize_iInf] at hw
  -- Assemble the assignment from the inverse of `h` and the witnesses.
  set v : ↥B → ↥A := fun b =>
    if hb : b ∈ sOut then w ⟨b, hb⟩ else Function.invFun ⇑h b with hv
  refine ⟨v, ?_, ?_⟩
  · funext a
    have h1 : h a ∉ sOut := fun hmem' => (Finset.mem_filter.1 hmem').2 ⟨a, rfl⟩
    have hva : v (h a) = Function.invFun ⇑h (h a) := by
      rw [hv]; exact dite_eq_right h1
    rw [Function.comp_apply, hva, id_eq]
    exact Function.leftInverse_invFun h.injective a
  · intro θ
    have hwθ := hw θ
    rw [Formula.realize_relabel] at hwθ
    have hasgn : (Sum.elim (X ∘ ⇑sIn.equivFin) w ∘ ρ θ) = v ∘ bb θ := by
      funext i
      by_cases hb : bb θ i ∈ Set.range ⇑h
      · have hρi : ρ θ i = Sum.inl ⟨bb θ i, Finset.mem_filter.2 ⟨hmem θ i, hb⟩⟩ := by
          rw [hρ]; exact dite_eq_left hb
        have h2 : bb θ i ∉ sOut := fun hmem' => (Finset.mem_filter.1 hmem').2 hb
        have hvi : v (bb θ i) = Function.invFun ⇑h (bb θ i) := by
          rw [hv]; exact dite_eq_right h2
        simp only [Function.comp_apply, hρi, Sum.elim_inl, hvi]
        apply h.injective
        rw [hXB, Function.invFun_eq hb]
        exact congrArg Subtype.val (sIn.equivFin.symm_apply_apply _)
      · have h2 : bb θ i ∈ sOut := Finset.mem_filter.2 ⟨hmem θ i, hb⟩
        have hρi : ρ θ i = Sum.inr ⟨bb θ i, h2⟩ := by
          rw [hρ]; exact dite_eq_right hb
        have hvi : v (bb θ i) = w ⟨bb θ i, h2⟩ := by
          rw [hv]; exact dite_eq_left h2
        rw [Function.comp_apply, Function.comp_apply, hρi, hvi]
        rfl
    rw [hasgn] at hwθ
    exact hwθ

/--
**The sandwich lemma.** Under the hypothesis of Robinson's test, any embedding `h : A ↪ B`
between models of `T` extends to a model `P` of `T` by an embedding `g : B ↪ P` such that the
composite `g ∘ h : A ↪ P` is elementary.

`P` is obtained by compactness from the union of the elementary diagram of `A` (with constants
renamed along `h`) and the quantifier-free diagram of `B`; finite satisfiability is exactly
`exists_assignment`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem IsExistentiallyClosedInModels.exists_embedding_elementary_comp
    (hec : T.IsExistentiallyClosedInModels)
    (A B : T.ModelType.{u, v, max u v}) (h : A ↪[L] B) :
    ∃ (P : T.ModelType.{u, v, max u v}) (g : B ↪[L] P),
      ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → A),
        φ.Realize (⇑(g.comp h) ∘ x) ↔ φ.Realize x := by
  classical
  -- The sandwich theory over `L[[B]]` and its finite satisfiability.
  have hsat : ((L.lhomWithConstantsMap (⇑h : ↥A → ↥B)).onTheory
      (L.elementaryDiagram (A : Type (max u v))) ∪
        L.qfDiagram (B : Type (max u v))).IsSatisfiable := by
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro Θ₀ hΘ₀
    have hdata : ∀ θ : {θ : L[[(B : Type (max u v))]].Sentence //
        θ ∈ Θ₀.filter (· ∈ L.qfDiagram (B : Type (max u v)))},
        ∃ (n : ℕ) (φ : L.Formula (Fin n)) (b : Fin n → (B : Type (max u v))),
          φ.IsQF ∧ φ.Realize b ∧ (θ : L[[(B : Type (max u v))]].Sentence) =
            Formula.equivSentence (φ.relabel b) :=
      fun θ => (Finset.mem_filter.1 θ.2).2
    choose nn ff bb hQF hReal hEq using hdata
    obtain ⟨v, hvh, hv⟩ := hec.exists_assignment A B h ff bb hQF hReal
    -- Interpret the constants of `B` in `A` through the assignment.
    let : (constantsOn (B : Type (max u v))).Structure (A : Type (max u v)) :=
      constantsOn.structure v
    have : (L.lhomWithConstantsMap (⇑h : ↥A → ↥B)).IsExpansionOn (A : Type (max u v)) := by
      refine ⟨fun {n} F xa => ?_, fun {n} R xa => ?_⟩
      · match F with
        | Sum.inl F => rfl
        | Sum.inr c =>
          match n, c with
          | 0, c => exact congrFun hvh c
      · match R with
        | Sum.inl R => rfl
        | Sum.inr r => exact isEmptyElim r
    have hmodel : (A : Type (max u v)) ⊨ (↑Θ₀ : L[[(B : Type (max u v))]].Theory) := by
      rw [model_iff]
      intro θ hθ
      rcases hΘ₀ hθ with hθ₁ | hθ₂
      · have hA : (A : Type (max u v)) ⊨ (L.lhomWithConstantsMap (⇑h : ↥A → ↥B)).onTheory
            (L.elementaryDiagram (A : Type (max u v))) := by
          rw [LHom.onTheory_model]
          infer_instance
        exact hA.realize_of_mem θ hθ₁
      · have hθ' : θ ∈ Θ₀.filter (· ∈ L.qfDiagram (B : Type (max u v))) :=
          Finset.mem_filter.2 ⟨Finset.mem_coe.1 hθ, hθ₂⟩
        have hEq' : θ = Formula.equivSentence
            ((ff ⟨θ, hθ'⟩).relabel (bb ⟨θ, hθ'⟩)) := hEq ⟨θ, hθ'⟩
        rw [hEq', realize_equivSentence_relabel]
        exact hv ⟨θ, hθ'⟩
    exact Model.isSatisfiable (A : Type (max u v))
  obtain ⟨P0⟩ := hsat
  -- The reducts of the compactness model.
  let : L.Structure P0 := (L.lhomWithConstants (B : Type (max u v))).reduct P0
  let : L[[(A : Type (max u v))]].Structure P0 :=
    (L.lhomWithConstantsMap (⇑h : ↥A → ↥B)).reduct P0
  have : (L.lhomWithConstants (A : Type (max u v))).IsExpansionOn (P0 : Type (max u v)) :=
    ⟨fun {n} F x => rfl, fun {n} R x => rfl⟩
  have : (L.lhomWithConstants (B : Type (max u v))).IsExpansionOn (P0 : Type (max u v)) :=
    ⟨fun {n} F x => rfl, fun {n} R x => rfl⟩
  -- The canonical elementary embedding of `A`.
  have hPdiag : (P0 : Type (max u v)) ⊨ L.elementaryDiagram (A : Type (max u v)) := by
    have h1 : (P0 : Type (max u v)) ⊨ (L.lhomWithConstantsMap (⇑h : ↥A → ↥B)).onTheory
        (L.elementaryDiagram (A : Type (max u v))) :=
      P0.is_model.mono Set.subset_union_left
    rwa [LHom.onTheory_model] at h1
  let e : (A : Type (max u v)) ↪ₑ[L] P0 :=
    ElementaryEmbedding.ofModelsElementaryDiagram L (A : Type (max u v)) P0
  -- The canonical embedding supplied by the quantifier-free diagram.
  have : (P0 : Type (max u v)) ⊨ L.qfDiagram (B : Type (max u v)) :=
    P0.is_model.mono Set.subset_union_right
  let g : (B : Type (max u v)) ↪[L] (P0 : Type (max u v)) :=
    Embedding.ofModelsQfDiagram L (B : Type (max u v)) P0
  -- Bundle `P0` as a model of `T` via the elementary embedding.
  have hPT : (P0 : Type (max u v)) ⊨ T := (e.theory_model_iff T).1 A.is_model
  refine ⟨ModelType.of T (P0 : Type (max u v)), g, ?_⟩
  intro n φ x
  -- `g ∘ h` and `e` agree definitionally: both send `a` to the constant `h a` of `P0`.
  exact e.map_formula φ x

/--
One step of the alternating sandwich chain: from a state `(X, Y, h)` pass to `(Y, P, g)`, where
`P` and `g` are produced by the sandwich lemma, so that `g ∘ h` is elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable def IsExistentiallyClosedInModels.chainStep
    (hec : T.IsExistentiallyClosedInModels)
    (s : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y) :
    Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y :=
  ⟨s.2.1, (hec.exists_embedding_elementary_comp s.1 s.2.1 s.2.2).choose,
    (hec.exists_embedding_elementary_comp s.1 s.2.1 s.2.2).choose_spec.choose⟩

/-- The alternating sandwich chain determined by a starting embedding.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable def IsExistentiallyClosedInModels.chainAux
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (n : ℕ) :
    Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y :=
  Nat.rec s₀ (fun _ s => hec.chainStep s) n

/-- The carriers of the alternating sandwich chain.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable abbrev IsExistentiallyClosedInModels.chainCarrier
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (n : ℕ) : Type (max u v) :=
  ((hec.chainAux s₀ n).1 : Type (max u v))

/-- The transition embeddings of the alternating sandwich chain.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable def IsExistentiallyClosedInModels.chainEmbedding
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (n : ℕ) : hec.chainCarrier s₀ n ↪[L] hec.chainCarrier s₀ (n + 1) :=
  (hec.chainAux s₀ n).2.2

/-- Composites of two consecutive transitions of the sandwich chain are elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem IsExistentiallyClosedInModels.chainEmbedding_comp_elementary
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (m : ℕ) (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → hec.chainCarrier s₀ m) :
    φ.Realize (⇑((hec.chainEmbedding s₀ (m + 1)).comp (hec.chainEmbedding s₀ m)) ∘ x) ↔
      φ.Realize x :=
  (hec.exists_embedding_elementary_comp (hec.chainAux s₀ m).1 (hec.chainAux s₀ m).2.1
    (hec.chainAux s₀ m).2.2).choose_spec.choose_spec n φ x

/-- Transitions of the sandwich chain over an even gap are elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem IsExistentiallyClosedInModels.chain_natLERec_elementary
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (i m : ℕ) :
    ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → hec.chainCarrier s₀ i),
      φ.Realize (⇑(DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * m)
        (Nat.le_add_right i (2 * m))) ∘ x) ↔ φ.Realize x := by
  induction m with
  | zero =>
    intro n φ x
    have h1 : DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * 0)
        (Nat.le_add_right i (2 * 0)) = Embedding.refl L _ := Nat.leRecOn_self _
    have h2 : ⇑(DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * 0)
        (Nat.le_add_right i (2 * 0))) ∘ x = x := by
      funext a
      rw [Function.comp_apply, h1]
      exact Embedding.refl_apply (x a)
    rw [h2]
  | succ m ih =>
    intro n φ x
    have h1 : DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * (m + 1))
        (Nat.le_add_right i (2 * (m + 1))) =
        (hec.chainEmbedding s₀ (i + 2 * m + 1)).comp
          (DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * m + 1)
            (Nat.le_succ_of_le (Nat.le_add_right i (2 * m)))) :=
      Nat.leRecOn_succ _ _
    have h2 : DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * m + 1)
        (Nat.le_succ_of_le (Nat.le_add_right i (2 * m))) =
        (hec.chainEmbedding s₀ (i + 2 * m)).comp
          (DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * m)
            (Nat.le_add_right i (2 * m))) :=
      Nat.leRecOn_succ _ _
    have hsplit : ⇑(DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * (m + 1))
        (Nat.le_add_right i (2 * (m + 1)))) ∘ x =
        ⇑((hec.chainEmbedding s₀ (i + 2 * m + 1)).comp (hec.chainEmbedding s₀ (i + 2 * m))) ∘
          (⇑(DirectedSystem.natLERec (hec.chainEmbedding s₀) i (i + 2 * m)
            (Nat.le_add_right i (2 * m))) ∘ x) := by
      funext a
      rw [Function.comp_apply, h1, h2]
      rfl
    rw [hsplit, hec.chainEmbedding_comp_elementary s₀ (i + 2 * m) n φ _]
    exact ih n φ _

/--
The first transition of the sandwich chain is elementary: sandwich it between the elementary
canonical maps into the direct limit of the chain, using the elementary chain theorem.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem IsExistentiallyClosedInModels.chainEmbedding_zero_elementary
    (hec : T.IsExistentiallyClosedInModels)
    (s₀ : Σ (X : T.ModelType.{u, v, max u v}) (Y : T.ModelType.{u, v, max u v}), X ↪[L] Y)
    (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → hec.chainCarrier s₀ 0) :
    φ.Realize (⇑(hec.chainEmbedding s₀ 0) ∘ x) ↔ φ.Realize x := by
  have hcof : DirectLimit.CofinallyElementary
      (DirectedSystem.natLERec (hec.chainEmbedding s₀)) := by
    intro i j
    exact ⟨i + 2 * j, Nat.le_add_right i (2 * j), by omega,
      hec.chain_natLERec_elementary s₀ i j⟩
  have h0 : ∀ (k : ℕ) (φ' : L.Formula (Fin n)) (v : Fin n → hec.chainCarrier s₀ k),
      φ'.Realize (⇑(DirectLimit.of L ℕ (hec.chainCarrier s₀)
        (DirectedSystem.natLERec (hec.chainEmbedding s₀)) k) ∘ v) ↔ φ'.Realize v :=
    fun k φ' v => DirectLimit.realize_formula_of hcof φ' k v
  have hone : ∀ a : hec.chainCarrier s₀ 0,
      DirectedSystem.natLERec (hec.chainEmbedding s₀) 0 1 (Nat.le_succ 0) a =
        hec.chainEmbedding s₀ 0 a := by
    intro a
    have h2 : DirectedSystem.natLERec (hec.chainEmbedding s₀) 0 1 (Nat.le_succ 0) =
        (hec.chainEmbedding s₀ 0).comp (Embedding.refl L _) := Nat.leRecOn_succ' _
    rw [h2]
    rfl
  have hcomm : ⇑(DirectLimit.of L ℕ (hec.chainCarrier s₀)
      (DirectedSystem.natLERec (hec.chainEmbedding s₀)) 1) ∘
        (⇑(hec.chainEmbedding s₀ 0) ∘ x) =
      ⇑(DirectLimit.of L ℕ (hec.chainCarrier s₀)
        (DirectedSystem.natLERec (hec.chainEmbedding s₀)) 0) ∘ x := by
    funext i
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, ← hone (x i)]
    exact DirectLimit.of_f
  calc φ.Realize (⇑(hec.chainEmbedding s₀ 0) ∘ x)
      ↔ φ.Realize (⇑(DirectLimit.of L ℕ (hec.chainCarrier s₀)
          (DirectedSystem.natLERec (hec.chainEmbedding s₀)) 1) ∘
            (⇑(hec.chainEmbedding s₀ 0) ∘ x)) := (h0 1 φ _).symm
    _ ↔ φ.Realize (⇑(DirectLimit.of L ℕ (hec.chainCarrier s₀)
          (DirectedSystem.natLERec (hec.chainEmbedding s₀)) 0) ∘ x) := by rw [hcomm]
    _ ↔ φ.Realize x := h0 0 φ x

/--
**Robinson's test, semantic conclusion.** If every embedding between models of a theory
reflects existential formulas, then every such embedding is elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem allEmbeddingsElementary_of_isExistentiallyClosedInModels
    (hec : T.IsExistentiallyClosedInModels) : T.AllEmbeddingsElementary := by
  intro M N f
  exact ⟨⟨⇑f, fun n φ x => hec.chainEmbedding_zero_elementary ⟨M, N, f⟩ n φ x⟩,
    Embedding.ext fun a => rfl⟩

/-- **Robinson's model-completeness test, syntactic conclusion.** Every formula is equivalent
modulo the theory to an existential formula if every embedding between its models reflects
existential formulas.

Paper-ID: `model_theory.companion_iff_ec`.
Source: `T3_modelcompanion_v9.tex`, Fact 2.3, lines 289–295. -/
theorem isModelComplete_of_isExistentiallyClosedInModels
    (hec : T.IsExistentiallyClosedInModels) : T.IsModelComplete :=
  (allEmbeddingsElementary_of_isExistentiallyClosedInModels hec).isModelComplete

end Theory

end Language

end FirstOrder
