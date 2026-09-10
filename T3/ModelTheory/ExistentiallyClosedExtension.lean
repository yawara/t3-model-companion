/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.PiTwoDirectLimit
public import Mathlib.Order.Zorn

/-!
# Existentially closed extensions of models of Pi-two theories

For an arbitrary theory, compactness and Zorn's lemma give an extension that realizes every
existential condition over the original model that remains possible in any further extension.
Iterating this step and taking a directed limit gives an existentially closed extension when
the theory is Pi-two. The directed-limit model theorem uses an equivalent universal-existential
axiomatization, with no universal-theory, finite-language, or amalgamation assumption.

The limit-model step uses `DirectLimit.models_of_isPiTwo`. The canonical quantifier-free-diagram
embedding is supplied by `T3.ModelTheory.ModelCompleteness`. Models and extensions use the
canonical semantic universe.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder

namespace Language

namespace BoundedFormula

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {n : ℕ}

/-- Quantifier-free formulas are absolute for embeddings.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem IsQF.realize_formula_embedding {φ : L.Formula (Fin n)} (hφ : φ.IsQF) (g : M ↪[L] N)
    (v : Fin n → M) : φ.Realize (⇑g ∘ v) ↔ φ.Realize v := by
  have h := hφ.realize_embedding g (v := v) (xs := (default : Fin 0 → M))
  rwa [Unique.eq_default (⇑g ∘ (default : Fin 0 → M))] at h

/-- Existential formulas are preserved by embeddings.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem IsExistential.realize_formula_embedding {φ : L.Formula (Fin n)} (hφ : φ.IsExistential)
    (g : M ↪[L] N) {v : Fin n → M} (h : φ.Realize v) : φ.Realize (⇑g ∘ v) := by
  have h2 := hφ.realize_embedding g (v := v) (xs := (default : Fin 0 → M)) h
  rwa [Unique.eq_default (⇑g ∘ (default : Fin 0 → M))] at h2

end BoundedFormula

/--
An existential condition over a structure `M`: an existential formula together with a tuple of
parameters from `M`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
structure ExCondition (L : Language.{u, v}) (M : Type w) [L.Structure M] where
  /-- The number of parameters. -/
  arity : ℕ
  /-- The formula of the condition. -/
  formula : L.Formula (Fin arity)
  /-- The formula is existential. -/
  isExistential : formula.IsExistential
  /-- The parameters, taken from `M`. -/
  param : Fin arity → M

namespace ExCondition

variable {L : Language.{u, v}} {M : Type (max u v)} [L.Structure M]

/-- The sentence of `L[[M]]` expressing a condition at its own parameters.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
def sentence (p : ExCondition L M) : L[[M]].Sentence :=
  Formula.equivSentence (p.formula.relabel p.param)

/-- A structure interpreting the constants realizes the sentence of a condition exactly when it
realizes the formula at the interpretations of the parameters.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem realize_sentence_iff (p : ExCondition L M) {N : Type (max u v)} [L[[M]].Structure N]
    [L.Structure N] [(L.lhomWithConstants M).IsExpansionOn N] :
    N ⊨ p.sentence ↔ p.formula.Realize (fun i => (L.con (p.param i) : N)) :=
  realize_equivSentence_relabel _ _

end ExCondition

namespace Theory

open Structure

variable {L : Language.{u, v}} {T : L.Theory}

/--
A set of existential conditions over `M` is realizable when a single model of `T` receives an
embedding of `M` realizing all of them at the images of their parameters.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
def IsRealizable (T : L.Theory) {M : Type (max u v)} [L.Structure M]
    (S : Set (ExCondition L M)) : Prop :=
  ∃ (N : T.ModelType.{u, v, max u v}) (g : M ↪[L] N), ∀ p ∈ S, p.formula.Realize (⇑g ∘ p.param)

/-- Realizability passes to subsets.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem IsRealizable.mono {M : Type (max u v)} [L.Structure M] {S S' : Set (ExCondition L M)}
    (h : T.IsRealizable S) (hsub : S' ⊆ S) : T.IsRealizable S' := by
  obtain ⟨N, g, hg⟩ := h
  exact ⟨N, g, fun p hp => hg p (hsub hp)⟩

/--
**Realizability has finite character.** If every finite set of conditions from `S` is realizable,
then `S` is realizable: apply compactness to the union of the lifted theory, the quantifier-free
diagram of `M`, and the sentences of `S`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem isRealizable_of_forall_finite {M : Type (max u v)} [L.Structure M]
    {S : Set (ExCondition L M)} (h : ∀ S₀ ⊆ S, S₀.Finite → T.IsRealizable S₀) :
    T.IsRealizable S := by
  classical
  have hsat : ((L.lhomWithConstants M).onTheory T ∪ L.qfDiagram M ∪
      ExCondition.sentence '' S).IsSatisfiable := by
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro Θ₀ hΘ₀
    -- Choose a condition of `S` for each sentence of `Θ₀` that comes from one.
    have hdata : ∀ θ : {θ : L[[M]].Sentence // θ ∈ Θ₀.filter (· ∈ ExCondition.sentence '' S)},
        ∃ p : ExCondition L M, p ∈ S ∧ p.sentence = (θ : L[[M]].Sentence) := by
      intro θ
      obtain ⟨p, hp, hps⟩ := (Finset.mem_filter.1 θ.2).2
      exact ⟨p, hp, hps⟩
    choose pp hppS hppEq using hdata
    obtain ⟨N, g, hg⟩ := h (Set.range pp) (by rintro _ ⟨θ, rfl⟩; exact hppS θ) (Set.finite_range pp)
    -- Interpret the constants of `M` in `N` through the embedding.
    letI : (constantsOn M).Structure (N : Type (max u v)) := constantsOn.structure ⇑g
    have hcon : ∀ a : M, (L.con a : (N : Type (max u v))) = g a := fun _ => rfl
    haveI hmodel : (N : Type (max u v)) ⊨ (↑Θ₀ : L[[M]].Theory) := by
      rw [model_iff]
      intro θ hθ
      rcases hΘ₀ hθ with (h1 | h2) | h3
      · have hNT : (N : Type (max u v)) ⊨ (L.lhomWithConstants M).onTheory T :=
          (LHom.onTheory_model _ _).2 inferInstance
        exact hNT.realize_of_mem θ h1
      · obtain ⟨n, φ, b, hφ, hb, rfl⟩ := h2
        rw [realize_equivSentence_relabel]
        have hgb : (fun i => (L.con (b i) : (N : Type (max u v)))) = ⇑g ∘ b := by
          funext i
          exact hcon (b i)
        rw [hgb]
        exact (hφ.realize_formula_embedding g b).2 hb
      · have hθ' : θ ∈ Θ₀.filter (· ∈ ExCondition.sentence '' S) :=
          Finset.mem_filter.2 ⟨Finset.mem_coe.1 hθ, h3⟩
        have hEq : (pp ⟨θ, hθ'⟩).sentence = θ := hppEq ⟨θ, hθ'⟩
        rw [← hEq, ExCondition.realize_sentence_iff]
        have hgp : (fun i => (L.con ((pp ⟨θ, hθ'⟩).param i) : (N : Type (max u v)))) =
            ⇑g ∘ (pp ⟨θ, hθ'⟩).param := by
          funext i
          exact hcon _
        rw [hgp]
        exact hg _ ⟨⟨θ, hθ'⟩, rfl⟩
    exact Model.isSatisfiable (N : Type (max u v))
  obtain ⟨P0⟩ := hsat
  -- The `L`-reduct of the compactness model.
  letI : L.Structure (P0 : Type (max u v)) := (L.lhomWithConstants M).reduct P0
  haveI : (L.lhomWithConstants M).IsExpansionOn (P0 : Type (max u v)) :=
    ⟨fun {_} _ _ => rfl, fun {_} _ _ => rfl⟩
  haveI hPT : (P0 : Type (max u v)) ⊨ T :=
    (LHom.onTheory_model _ _).1
      (P0.is_model.mono (Set.subset_union_left.trans Set.subset_union_left))
  haveI hPqf : (P0 : Type (max u v)) ⊨ L.qfDiagram M :=
    P0.is_model.mono (Set.subset_union_right.trans Set.subset_union_left)
  refine ⟨ModelType.of T (P0 : Type (max u v)),
    (Embedding.ofModelsQfDiagram L M (P0 : Type (max u v))), ?_⟩
  intro p hp
  have hmem : p.sentence ∈ (L.lhomWithConstants M).onTheory T ∪ L.qfDiagram M ∪
      ExCondition.sentence '' S := Set.mem_union_right _ ⟨p, hp, rfl⟩
  have hreal := P0.is_model.realize_of_mem _ hmem
  rw [ExCondition.realize_sentence_iff] at hreal
  exact hreal

/--
**The one-step extension.** Every model `M` of `T` has an extension `N ⊨ T` in which every
existential condition with parameters from `M` that is realizable in a further extension of `N` is
already realized.

The proof is Zorn's lemma applied to the simultaneously realizable sets of conditions over `M`;
maximality is used *backwards*, against a given counterexample, exactly as the transfinite
recursion of the classical proof is justified stage by stage after the fact.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem exists_partiallyExistentiallyClosed (T : L.Theory) (M : Type (max u v)) [L.Structure M]
    [Nonempty M] [M ⊨ T] :
    ∃ (N : T.ModelType.{u, v, max u v}) (g : M ↪[L] N),
      ∀ (N' : T.ModelType.{u, v, max u v}) (g' : (N : Type (max u v)) ↪[L] N') {n : ℕ}
        (φ : L.Formula (Fin n)) (x : Fin n → M), φ.IsExistential →
        φ.Realize (⇑g' ∘ (⇑g ∘ x)) → φ.Realize (⇑g ∘ x) := by
  classical
  have hchain : ∀ c ⊆ {S : Set (ExCondition L M) | T.IsRealizable S}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {S : Set (ExCondition L M) | T.IsRealizable S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine isRealizable_of_forall_finite (fun S₀ hS₀ hfin => ?_)
    rcases c.eq_empty_or_nonempty with rfl | hne
    · rw [Set.sUnion_empty, Set.subset_empty_iff] at hS₀
      subst hS₀
      exact ⟨ModelType.of T M, Embedding.refl L M, by simp⟩
    · obtain ⟨t, htc, hS₀t⟩ :=
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hcchain.directedOn hfin hS₀
      exact (hc htc).mono hS₀t
  obtain ⟨S, hSmem, hSmax⟩ := zorn_subset {S : Set (ExCondition L M) | T.IsRealizable S} hchain
  obtain ⟨N, g, hg⟩ := hSmem
  refine ⟨N, g, ?_⟩
  intro N' g' n φ x hφ hreal
  -- The counterexample itself realizes `S` together with the new condition.
  have hins : T.IsRealizable (insert ⟨n, φ, hφ, x⟩ S) := by
    refine ⟨N', g'.comp g, ?_⟩
    rintro q (rfl | hq)
    · exact hreal
    · exact q.isExistential.realize_formula_embedding g' (hg q hq)
  have hsub := hSmax hins (Set.subset_insert _ _)
  exact hg _ (hsub (Set.mem_insert _ _))

section Tower

variable {T : L.Theory}

/-- The extension of a model provided by `exists_partiallyExistentiallyClosed`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
noncomputable def ecStep (X : T.ModelType.{u, v, max u v}) : T.ModelType.{u, v, max u v} :=
  (exists_partiallyExistentiallyClosed T (X : Type (max u v))).choose

/-- The embedding into `ecStep X`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
noncomputable def ecStepEmbedding (X : T.ModelType.{u, v, max u v}) :
    (X : Type (max u v)) ↪[L] (ecStep X : Type (max u v)) :=
  (exists_partiallyExistentiallyClosed T (X : Type (max u v))).choose_spec.choose

/-- Existential conditions with parameters from `X` that survive into an extension of `ecStep X`
are already realized in `ecStep X`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem ecStep_spec (X : T.ModelType.{u, v, max u v}) :
    ∀ (N' : T.ModelType.{u, v, max u v}) (g' : (ecStep X : Type (max u v)) ↪[L] N') {n : ℕ}
      (φ : L.Formula (Fin n)) (x : Fin n → (X : Type (max u v))), φ.IsExistential →
      φ.Realize (⇑g' ∘ (⇑(ecStepEmbedding X) ∘ x)) → φ.Realize (⇑(ecStepEmbedding X) ∘ x) :=
  (exists_partiallyExistentiallyClosed T (X : Type (max u v))).choose_spec.choose_spec

/-- The tower of models over `M` obtained by iterating the one-step extension.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
noncomputable def ecTower (M : T.ModelType.{u, v, max u v}) : ℕ → T.ModelType.{u, v, max u v} :=
  fun n => Nat.rec M (fun _ X => ecStep X) n

/-- The carriers of the tower.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
noncomputable abbrev ecCarrier (M : T.ModelType.{u, v, max u v}) (n : ℕ) : Type (max u v) :=
  (ecTower M n : Type (max u v))

/-- The transition embeddings of the tower.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
noncomputable def ecTransition (M : T.ModelType.{u, v, max u v}) (n : ℕ) :
    ecCarrier M n ↪[L] ecCarrier M (n + 1) :=
  ecStepEmbedding (ecTower M n)

/-- The one-step property, at a stage of the tower.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem ecTransition_spec (M : T.ModelType.{u, v, max u v}) (m : ℕ) :
    ∀ (N' : T.ModelType.{u, v, max u v}) (g' : ecCarrier M (m + 1) ↪[L] N') {n : ℕ}
      (φ : L.Formula (Fin n)) (x : Fin n → ecCarrier M m), φ.IsExistential →
      φ.Realize (⇑g' ∘ (⇑(ecTransition M m) ∘ x)) → φ.Realize (⇑(ecTransition M m) ∘ x) :=
  ecStep_spec (ecTower M m)

/--
**Every model of a Pi-two theory embeds into an existentially closed model.** The model is the
direct limit of the tower of one-step extensions.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem exists_isExistentiallyClosed_embedding (hT : T.IsPiTwo) (M : T.ModelType.{u, v, max u v}) :
    ∃ N : T.ModelType.{u, v, max u v}, T.IsExistentiallyClosed (N : Type (max u v)) ∧
      Nonempty ((M : Type (max u v)) ↪[L] N) := by
  haveI : ∀ n : ℕ, Nonempty (ecCarrier M n) := fun n => (ecTower M n).nonempty'
  have hmodels : ∀ n : ℕ, (ecCarrier M n) ⊨ T := fun n => (ecTower M n).is_model
  haveI hlim : DirectLimit (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) ⊨ T :=
    DirectLimit.models_of_isPiTwo (DirectedSystem.natLERec (ecTransition M)) hT hmodels
  haveI : Nonempty (DirectLimit (ecCarrier M) (DirectedSystem.natLERec (ecTransition M))) :=
    ⟨DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) 0
      (Classical.arbitrary _)⟩
  refine ⟨ModelType.of T (DirectLimit (ecCarrier M) (DirectedSystem.natLERec (ecTransition M))),
    ⟨inferInstance, inferInstance, ?_⟩,
    ⟨DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) 0⟩⟩
  intro N' h n φ x hφ hreal
  -- A finite tuple of the limit comes from a single stage.
  obtain ⟨m, y, hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq (ecCarrier M)
    (DirectedSystem.natLERec (ecTransition M)) x
  have hy' : x = ⇑(DirectLimit.of L ℕ (ecCarrier M)
      (DirectedSystem.natLERec (ecTransition M)) m) ∘ y := hy
  subst hy'
  have hstep : ∀ a : ecCarrier M m,
      DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) (m + 1)
          (ecTransition M m a) =
        DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) m a := by
    intro a
    have h2 : DirectedSystem.natLERec (ecTransition M) m (m + 1) (Nat.le_succ m) =
        (ecTransition M m).comp (Embedding.refl L _) := Nat.leRecOn_succ' _
    have h3 : DirectedSystem.natLERec (ecTransition M) m (m + 1) (Nat.le_succ m) a =
        ecTransition M m a := by rw [h2]; rfl
    rw [← h3]
    exact DirectLimit.of_f
  -- Pull the condition down to stage `m + 1`, then push it back into the limit.
  have hpull := ecTransition_spec M m N'
    (h.comp (DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) (m + 1)))
    φ y hφ ?_
  · have hpush := hφ.realize_formula_embedding
      (DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) (m + 1)) hpull
    have hcomp : ⇑(DirectLimit.of L ℕ (ecCarrier M)
          (DirectedSystem.natLERec (ecTransition M)) (m + 1)) ∘ (⇑(ecTransition M m) ∘ y) =
        ⇑(DirectLimit.of L ℕ (ecCarrier M) (DirectedSystem.natLERec (ecTransition M)) m) ∘ y := by
      funext i
      exact hstep (y i)
    rwa [hcomp] at hpush
  · have hcomp : ⇑(h.comp (DirectLimit.of L ℕ (ecCarrier M)
          (DirectedSystem.natLERec (ecTransition M)) (m + 1))) ∘ (⇑(ecTransition M m) ∘ y) =
        ⇑h ∘ (⇑(DirectLimit.of L ℕ (ecCarrier M)
          (DirectedSystem.natLERec (ecTransition M)) m) ∘ y) := by
      funext i
      exact congrArg (⇑h) (hstep (y i))
    rw [hcomp]
    exact hreal

end Tower

section Corollaries

variable {Tstar : L.Theory}

/--
If every existentially closed model of `T` is a model of `Tstar`, then every model of `T` embeds
into a model of `Tstar`.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v4.tex, supporting Fact 2.3, lines 195–201; no label.
-/
theorem modelsEmbedInto_of_isExistentiallyClosed_models (hT : T.IsPiTwo)
    (h : ∀ N : T.ModelType.{u, v, max u v}, T.IsExistentiallyClosed (N : Type (max u v)) →
      (N : Type (max u v)) ⊨ Tstar) :
    T.ModelsEmbedInto Tstar := by
  intro M
  obtain ⟨N, hec, ⟨e⟩⟩ := exists_isExistentiallyClosed_embedding hT M
  haveI : (N : Type (max u v)) ⊨ Tstar := h N hec
  exact ⟨ModelType.of Tstar (N : Type (max u v)), ⟨e⟩⟩

end Corollaries

end Theory

end Language

end FirstOrder
