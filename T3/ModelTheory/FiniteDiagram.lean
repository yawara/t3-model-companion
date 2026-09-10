/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ModelCompleteness

/-!
# Finite diagrams and embeddings over a tuple

For a finite language, the function tables, positive and negative relation tables, and
inequalities of a finite structure form one quantifier-free formula. Its realizations are
exactly embeddings. Replacing the element variables by terms in a generating tuple gives a
quantifier-free formula on that tuple, together with equations fixing its parameter values.

All function arities and both truth values of every relation are included.
No finite substructure is assumed to be a model of the ambient theory. Finiteness concerns a
representing formula, not the syntactic set of all true quantifier-free formulas.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 185–193; no label.
The embedding extension interpretation supports the final transfer in Proposition 4.12,
`proposition:bdd LCS`, line 1250.
-/

@[expose] public noncomputable section

open scoped FirstOrder

universe u v w w' w''

namespace FirstOrder.Language

open Structure

variable {L : Language.{u, v}}

/-- Substitution of terms does not introduce quantifiers.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6; no label.
-/
theorem BoundedFormula.IsQF.subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : φ.IsQF) (t : α → L.Term β) : (φ.subst t).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal s t => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel r ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihφ ihψ => exact ihφ.imp ihψ

/-- Relabeling the free variables preserves existential formulas.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 4; no label.
-/
theorem BoundedFormula.IsExistential.relabel {α β : Type*} {m n : ℕ}
    {φ : L.BoundedFormula α m} (h : φ.IsExistential) (f : α → β ⊕ Fin n) :
    (φ.relabel f).IsExistential :=
  BoundedFormula.IsExistential.recOn h (fun h => (h.relabel f).isExistential)
    (fun _ ih => by simpa using ih.ex)

section FiniteStructure

variable [Finite L.Symbols] (A : Type w) [L.Structure A] [Finite A]

instance finiteFunctions : Finite (Σ n, L.Functions n) :=
  Finite.of_injective (Sum.inl : (Σ n, L.Functions n) → L.Symbols) Sum.inl_injective

instance finiteRelations : Finite (Σ n, L.Relations n) :=
  Finite.of_injective (Sum.inr : (Σ n, L.Relations n) → L.Symbols) Sum.inr_injective

/-- The full function table of a finite structure in a finite language. -/
def functionDiagram : L.Formula A :=
  .iInf fun s : Σ n, L.Functions n => .iInf fun a : Fin s.1 → A =>
    (Term.func s.2 (Term.var ∘ a)).equal (Term.var (funMap s.2 a))

/-- All positive and negative relation facts about a finite structure. -/
def relationDiagram : L.Formula A := by
  classical
  exact .iInf fun s : Σ n, L.Relations n => .iInf fun a : Fin s.1 → A =>
    if RelMap s.2 a then s.2.formula (Term.var ∘ a) else ∼(s.2.formula (Term.var ∘ a))

/-- The inequalities between every pair of distinct elements of a finite type. -/
def distinctnessDiagram : L.Formula A := by
  classical
  exact .iInf fun a : A => .iInf fun b : A =>
    if a = b then ⊤ else ∼((Term.var a).equal (Term.var b))

/-- One quantifier-free formula recording a finite structure in a finite language.
It includes all function tables, positive and negative relation tables, and inequalities.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, finite representation in Definition 2.2, item 6; no label.
-/
def finiteDiagram : L.Formula A :=
  (functionDiagram A ⊓ relationDiagram A) ⊓ distinctnessDiagram (L := L) A

private theorem realize_functionDiagram {N : Type*} [L.Structure N] (x : A → N) :
    (functionDiagram (L := L) A).Realize x ↔
      ∀ (n : ℕ) (f : L.Functions n) (a : Fin n → A), x (funMap f a) = funMap f (x ∘ a) := by
  simp only [functionDiagram, Formula.realize_iInf, Formula.realize_equal,
    Term.realize, Function.comp_def, eq_comm, Sigma.forall]

private theorem realize_relationDiagram {N : Type*} [L.Structure N] (x : A → N) :
    (relationDiagram (L := L) A).Realize x ↔
      ∀ (n : ℕ) (r : L.Relations n) (a : Fin n → A), RelMap r (x ∘ a) ↔ RelMap r a := by
  simp only [relationDiagram, Formula.realize_iInf, Sigma.forall]
  refine forall_congr' fun n => forall_congr' fun r => forall_congr' fun a => ?_
  split <;> simp_all only [Formula.realize_rel, Formula.realize_not, Term.realize_var,
    Function.comp_def, iff_true, iff_false]

omit [Finite L.Symbols] [L.Structure A] in
private theorem realize_distinctnessDiagram {N : Type*} [L.Structure N] (x : A → N) :
    (distinctnessDiagram (L := L) A).Realize x ↔ Function.Injective x := by
  classical
  simp only [distinctnessDiagram, Formula.realize_iInf]
  constructor
  · intro h a b hab
    by_contra hne
    have h' := h a b
    rw [if_neg hne, Formula.realize_not, Formula.realize_equal] at h'
    exact h' hab
  · intro h a b
    by_cases hab : a = b
    · rw [if_pos hab]
      exact Formula.realize_top.mpr trivial
    · rw [if_neg hab, Formula.realize_not, Formula.realize_equal]
      exact fun h' => hab (h h')

/-- Realizing the complete finite diagram is equivalent to being an embedding.
No theory or nonemptiness assumptions are needed.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, finite representation in Definition 2.2, item 6; no label.
-/
theorem realize_finiteDiagram_iff {N : Type*} [L.Structure N] (x : A → N) :
    (finiteDiagram (L := L) A).Realize x ↔ ∃ f : A ↪[L] N, (f : A → N) = x := by
  simp only [finiteDiagram, Formula.realize_inf, realize_functionDiagram,
    realize_relationDiagram, realize_distinctnessDiagram]
  constructor
  · rintro ⟨⟨hf, hr⟩, hi⟩
    exact ⟨⟨⟨x, hi⟩, fun f a => hf _ f a, fun r a => hr _ r a⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨⟨fun _ => f.map_fun, fun _ => f.map_rel⟩, f.injective⟩

/-- The finite table diagram has no quantifiers.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, finite representation in Definition 2.2, item 6; no label.
-/
theorem finiteDiagram_isQF : (finiteDiagram (L := L) A).IsQF := by
  classical
  unfold finiteDiagram functionDiagram relationDiagram distinctnessDiagram
  refine (BoundedFormula.IsQF.inf ?_ ?_).inf ?_
  · exact BoundedFormula.isQF_iInf fun _ => BoundedFormula.isQF_iInf fun _ =>
      (BoundedFormula.IsAtomic.equal _ _).isQF
  · refine BoundedFormula.isQF_iInf fun _ => BoundedFormula.isQF_iInf fun _ => ?_
    split
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF
    · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not
  · refine BoundedFormula.isQF_iInf fun _ => BoundedFormula.isQF_iInf fun _ => ?_
    split
    · exact BoundedFormula.IsQF.top
    · exact (BoundedFormula.IsAtomic.equal _ _).isQF.not

end FiniteStructure

section GeneratedTuple

variable [Finite L.Symbols] {A : Type w} [L.Structure A] [Finite A]
  {α : Type w'} [Finite α] (a : α → A) (t : A → L.Term α)

/-- The finite diagram expressed using terms in a generating tuple. The final equations
ensure that the variables of the tuple retain their prescribed values.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 185–193; no label.
-/
def tupleDiagram : L.Formula α :=
  (finiteDiagram (L := L) A).subst t ⊓
    Formula.iInf fun i : α => (t (a i)).equal (Term.var i)

/-- The diagram expressed on the generating tuple is quantifier free.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6; no label.
-/
theorem tupleDiagram_isQF : (tupleDiagram a t).IsQF :=
  ((finiteDiagram_isQF A).subst t).inf (BoundedFormula.isQF_iInf fun _ =>
    (BoundedFormula.IsAtomic.equal _ _).isQF)

/-- A tuple realizes the finite generating diagram exactly when it extends to an embedding.
The tuple may have repetitions or be empty, and the target structure can have any universe.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6; no label.
-/
theorem realize_tupleDiagram_iff (ht : ∀ x, (t x).realize a = x)
    {N : Type*} [L.Structure N] (b : α → N) :
    (tupleDiagram a t).Realize b ↔ ∃ f : A ↪[L] N, (f : A → N) ∘ a = b := by
  rw [tupleDiagram, Formula.realize_inf, Formula.realize_iInf]
  have hsubst : Formula.Realize ((finiteDiagram (L := L) A).subst t) b ↔
      (finiteDiagram (L := L) A).Realize (fun x => (t x).realize b) :=
    BoundedFormula.realize_subst
  rw [hsubst, realize_finiteDiagram_iff]
  simp only [Formula.realize_equal, Term.realize_var]
  constructor
  · rintro ⟨⟨f, hf⟩, hb⟩
    exact ⟨f, funext fun i => (congrFun hf (a i)).trans (hb i)⟩
  · rintro ⟨f, rfl⟩
    have hterm (x : A) : (t x).realize ((f : A → N) ∘ a) = f x := by
      rw [HomClass.realize_term, ht]
    exact ⟨⟨f, funext fun x => (hterm x).symm⟩, fun i => hterm (a i)⟩

end GeneratedTuple

/-- The full quantifier-free diagram of a tuple, before choosing a finite representation.
This set of formulas is not asserted to be finite.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 185–191; no label.
-/
def tupleQfDiagram {α : Type*} {M : Type*} [L.Structure M] (a : α → M) :
    Set (L.Formula α) := {φ | φ.IsQF ∧ φ.Realize a}

/-- Every member of the substructure generated by a tuple is represented by a term in it.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6; no label.
-/
theorem Substructure.exists_term_of_mem_closure_range {α : Type*} {M : Type*}
    [L.Structure M] (a : α → M) {x : M}
    (hx : x ∈ Substructure.closure L (Set.range a)) :
    ∃ t : L.Term α, t.realize a = x := by
  classical
  obtain ⟨t, ht⟩ := Substructure.mem_closure_iff_exists_term.mp hx
  let r : Set.range a → α := fun x => Classical.choose x.property
  have hr : a ∘ r = ((↑) : Set.range a → M) :=
    funext fun x => Classical.choose_spec x.property
  exact ⟨t.relabel r, by simpa only [Term.realize_relabel, hr] using ht⟩

section FiniteClosure

variable {α : Type w'} {M : Type w} [L.Structure M] (a : α → M)

/-- The original tuple viewed in the substructure it generates. -/
def closureTuple : α → Substructure.closure L (Set.range a) :=
  fun i => ⟨a i, Substructure.subset_closure ⟨i, rfl⟩⟩

/-- A chosen term in the tuple representing each element of its generated substructure. -/
def closureTerm (x : Substructure.closure L (Set.range a)) : L.Term α :=
  Classical.choose (Substructure.exists_term_of_mem_closure_range a x.property)

/-- The chosen terms evaluate to their represented elements in the ambient structure. -/
theorem realize_closureTerm (x : Substructure.closure L (Set.range a)) :
    (closureTerm a x).realize a = x :=
  Classical.choose_spec (Substructure.exists_term_of_mem_closure_range a x.property)

private theorem realize_closureTerm_closureTuple (x : Substructure.closure L (Set.range a)) :
    (closureTerm a x).realize (closureTuple a) = x := by
  apply Subtype.val_injective
  change (Substructure.closure L (Set.range a)).subtype
    ((closureTerm a x).realize (closureTuple a)) = _
  rw [← HomClass.realize_term (Substructure.closure L (Set.range a)).subtype]
  exact realize_closureTerm a x

variable [Finite L.Symbols] [Finite α] [Finite (Substructure.closure L (Set.range a))]

/-- One quantifier-free formula representing the full diagram of a tuple whose generated
substructure is finite, in a finite language.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 185–193; no label.
-/
def finiteGeneratedDiagram : L.Formula α :=
  tupleDiagram (closureTuple a) (closureTerm a)

/-- The finite representation on the original tuple has no quantifiers.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6; no label.
-/
theorem finiteGeneratedDiagram_isQF : (finiteGeneratedDiagram (L := L) a).IsQF :=
  tupleDiagram_isQF _ _

/-- A realization of the finite diagram extends the tuple to an embedding of its generated
substructure. The target need not satisfy a theory or have a finite generated substructure.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6; no label.
-/
theorem realize_finiteGeneratedDiagram_iff {N : Type*} [L.Structure N] (b : α → N) :
    (finiteGeneratedDiagram (L := L) a).Realize b ↔
      ∃ f : Substructure.closure L (Set.range a) ↪[L] N,
        (f : Substructure.closure L (Set.range a) → N) ∘ closureTuple a = b :=
  realize_tupleDiagram_iff _ _ (realize_closureTerm_closureTuple a) b

/-- The finite representative belongs to the full quantifier-free diagram of the tuple.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6; no label.
-/
theorem finiteGeneratedDiagram_mem_tupleQfDiagram :
    finiteGeneratedDiagram (L := L) a ∈ tupleQfDiagram (L := L) a :=
  ⟨finiteGeneratedDiagram_isQF a, (realize_finiteGeneratedDiagram_iff a a).mpr
    ⟨(Substructure.closure L (Set.range a)).subtype, rfl⟩⟩

/-- A single quantifier-free formula is equivalent to the entire diagram of a tuple with
finite generated substructure. The equivalence holds in every target structure, and hence
also modulo any theory in which the original structure is a model.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 6, lines 192–193; no label.
-/
theorem realize_finiteGeneratedDiagram_iff_tupleQfDiagram {N : Type*} [L.Structure N]
    (b : α → N) : (finiteGeneratedDiagram (L := L) a).Realize b ↔
      ∀ φ ∈ tupleQfDiagram (L := L) a, φ.Realize b := by
  constructor
  · intro hb φ hφ
    obtain ⟨f, rfl⟩ := (realize_finiteGeneratedDiagram_iff a b).mp hb
    have hC : φ.Realize (closureTuple (L := L) a) := by
      have h := hφ.1.realize_embedding (Substructure.closure L (Set.range a)).subtype
        (v := closureTuple (L := L) a) (xs := default)
      have h' : φ.Realize a ↔ φ.Realize (closureTuple (L := L) a) := by
        simpa only [Formula.Realize, Unique.eq_default (_ ∘ default), closureTuple,
          Function.comp_def, Substructure.coe_subtype] using h
      exact h'.mp hφ.2
    have h := hφ.1.realize_embedding f (v := closureTuple (L := L) a) (xs := default)
    simpa only [Formula.Realize, Unique.eq_default (_ ∘ default)] using h.mpr hC
  · intro h
    exact h _ (finiteGeneratedDiagram_mem_tupleQfDiagram a)

end FiniteClosure

section EmbeddingExtension

variable [Finite L.Symbols] {A : Type w} [L.Structure A] [Finite A]
  {α : Type w'} [Finite α] (a : α → A)

/-- The quantifier-free matrix for embedding a finite structure over a prescribed tuple.
The left variables are parameters; the right variables enumerate the finite structure.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6, and Proposition 4.12,
`proposition:bdd LCS`, final finite-diagram transfer.
-/
def embeddingExtensionDiagram : L.Formula (α ⊕ A) :=
  (finiteDiagram (L := L) A).relabel Sum.inr ⊓
    Formula.iInf fun i : α => (Term.var (Sum.inr (a i))).equal (Term.var (Sum.inl i))

/-- The matrix asserting a finite embedding extension is quantifier free.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6; no label.
-/
theorem embeddingExtensionDiagram_isQF : (embeddingExtensionDiagram (L := L) a).IsQF :=
  ((finiteDiagram_isQF A).relabel _).inf (BoundedFormula.isQF_iInf fun _ =>
    (BoundedFormula.IsAtomic.equal _ _).isQF)

/-- Existentially closing the element variables asserts precisely the existence of an
embedding that extends the prescribed tuple. Parameters need not enumerate a substructure.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6, and Proposition 4.12,
`proposition:bdd LCS`, final finite-diagram transfer.
-/
theorem realize_exists_embeddingExtensionDiagram_iff {N : Type*} [L.Structure N]
    (b : α → N) : ((embeddingExtensionDiagram (L := L) a).iExs A).Realize b ↔
      ∃ f : A ↪[L] N, (f : A → N) ∘ a = b := by
  simp only [Formula.realize_iExs, embeddingExtensionDiagram, Formula.realize_inf,
    Formula.realize_relabel, Formula.realize_iInf, Formula.realize_equal, Term.realize_var]
  change (∃ x : A → N, (finiteDiagram (L := L) A).Realize x ∧ ∀ i, x (a i) = b i) ↔ _
  constructor
  · rintro ⟨x, hx, hxb⟩
    obtain ⟨f, rfl⟩ := (realize_finiteDiagram_iff A x).mp hx
    exact ⟨f, funext hxb⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, (realize_finiteDiagram_iff A f).mpr ⟨f, rfl⟩, fun _ => rfl⟩

end EmbeddingExtension

namespace Theory

variable {T : L.Theory} {M : Type (max u v)} [L.Structure M]

/-- Existential closedness applies to formulas indexed by any finite parameter type.
The model universes are those in the definition of existential closedness.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Definition 2.2, item 4; no label.
-/
theorem IsExistentiallyClosed.realize_of_finite (hM : T.IsExistentiallyClosed M)
    (N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N)
    {α : Type*} [Finite α] (φ : L.Formula α) (a : α → M)
    (hφ : φ.IsExistential) (hN : φ.Realize (f ∘ a)) : φ.Realize a := by
  letI := Fintype.ofFinite α
  let e := Fintype.equivFin α
  let ψ : L.Formula (Fin (Fintype.card α)) := φ.relabel e
  have hψ : ψ.IsExistential := hφ.relabel _
  have ha : (a ∘ e.symm) ∘ e = a :=
    funext fun i => congrArg a (e.symm_apply_apply i)
  have hfa : (f ∘ (a ∘ e.symm)) ∘ e = f ∘ a :=
    funext fun i => congrArg (fun j => f (a j)) (e.symm_apply_apply i)
  have hNψ : ψ.Realize (f ∘ (a ∘ e.symm)) := by
    change (φ.relabel e).Realize _
    rw [Formula.realize_relabel, hfa]
    exact hN
  have h := hM.2.2 N f ψ (a ∘ e.symm) hψ hNψ
  change (φ.relabel e).Realize _ at h
  rwa [Formula.realize_relabel, ha] at h

/-- A finite structure embedded into an extension of an existentially closed model can be
embedded back over any prescribed finite tuple already in the original model. The finite
structure is not required to satisfy the theory.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, supporting Definition 2.2, item 6, and Proposition 4.12,
`proposition:bdd LCS`, final finite-diagram transfer.
-/
theorem IsExistentiallyClosed.exists_embedding_over_tuple [Finite L.Symbols]
    (hM : T.IsExistentiallyClosed M) (N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N)
    {A : Type w} [L.Structure A] [Finite A] {α : Type w'} [Finite α]
    (a : α → A) (b : α → M) (g : A ↪[L] N) (hcompat : (g : A → N) ∘ a = f ∘ b) :
    ∃ h : A ↪[L] M, (h : A → M) ∘ a = b := by
  apply (realize_exists_embeddingExtensionDiagram_iff a b).mp
  apply hM.realize_of_finite N f _ b
  · exact (embeddingExtensionDiagram_isQF a).isExistential_iExs
  · exact (realize_exists_embeddingExtensionDiagram_iff a (f ∘ b)).mpr ⟨g, hcompat⟩

/-- A finite substructure of an extension has a copy inside the existentially closed model
that fixes a given finite common substructure. This is the finite-diagram transfer used
when bringing the constructed strict envelope back into the original model.

Paper-ID: model_theory.basic_definitions
TeX: T3_modelcompanion_v4.tex, Proposition 4.12, `proposition:bdd LCS`, line 1250.
-/
theorem IsExistentiallyClosed.exists_embedding_of_finite_substructure [Finite L.Symbols]
    (hM : T.IsExistentiallyClosed M) (N : T.ModelType.{u, v, max u v}) (f : M ↪[L] N)
    (A : L.Substructure N) [Finite A] (C : L.Substructure M) [Finite C]
    (hC : ∀ c : C, f (c : M) ∈ A) :
    ∃ g : A ↪[L] M, ∀ c : C, g ⟨f (c : M), hC c⟩ = c := by
  obtain ⟨g, hg⟩ := hM.exists_embedding_over_tuple N f
    (fun c : C => (⟨f (c : M), hC c⟩ : A)) ((↑) : C → M) A.subtype rfl
  exact ⟨g, fun c => congrFun hg c⟩

end Theory

end FirstOrder.Language
