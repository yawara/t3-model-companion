/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.ExtensionAxioms
public import T3.ModelTheory.FiniteObstructions

/-!
# The bounded-amalgamation criterion for model companionship

For each finite inclusion choose its finite family of forbidden marked extensions. The
extension axioms assert that every copy of the base admitting none of these forbidden
extensions extends to the prescribed finite structure. Bounded obstructions imply that every
existentially closed model satisfies these axioms. Conversely, local finiteness places any
existential witnesses in a finite extension, to which the axiom applies.

Fact 2.3 then turns this axiomatization of the existentially closed class into a model companion
for an arbitrary Pi-two theory. The finite structures may be empty and need not be models.
Model and amalgam universes are the canonical semantic universe `max u v`.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 293–342.
-/

@[expose] public noncomputable section

open scoped FirstOrder

universe u v

namespace FirstOrder.Language.Theory

variable {L : Language.{u, v}} [Finite L.Symbols] {T : L.Theory}

/-- A cardinal bound making the finite marked obstruction family complete.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 330–331.
-/
def obstructionCardBound (hLF : T.IsLocallyFinite) (d : FiniteInclusion T) (n : ℕ) : ℕ :=
  (hLF.exists_finite_bad_marked_cover d n).choose

/-- Every obstruction of the specified total generator bound has a representative in the
chosen finite family, with all base elements fixed.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 325–331.
-/
theorem exists_badMarkedStructure (hLF : T.IsLocallyFinite) (d : FiniteInclusion T) (n : ℕ)
    (M : T.ModelType.{u, v, max u v}) (C : L.Substructure M) (j : d.base ↪[L] C)
    (hgen : C.GeneratedByAtMost n) (hbad : ¬ T.AmalgamableOver d.incl j) :
    ∃ (p : BadMarkedStructure d n (obstructionCardBound hLF d n))
      (e : p.Carrier ≃[L] C), e.toEmbedding.comp p.mark = j :=
  (hLF.exists_finite_bad_marked_cover d n).choose_spec M C j hgen hbad

/-- The extension axiom excluding the complete finite family of obstructions with bound `n`.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, line 334.
-/
def extensionScheme (hLF : T.IsLocallyFinite) (d : FiniteInclusion T) (n : ℕ) : L.Sentence :=
  extensionAxiom d.incl
    (fun p : BadMarkedStructure d n (obstructionCardBound hLF d n) => p.mark)

/-- The extension scheme applies exactly to base embeddings admitting no forbidden copy.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 334–341.
-/
theorem realize_extensionScheme_iff (hLF : T.IsLocallyFinite) (d : FiniteInclusion T) (n : ℕ)
    {M : Type*} [L.Structure M] :
    M ⊨ extensionScheme hLF d n ↔
      ∀ a : d.base ↪[L] M,
        (∀ p : BadMarkedStructure d n (obstructionCardBound hLF d n),
          ¬ ∃ f : p.Carrier ↪[L] M, f.comp p.mark = a) →
            ∃ f : d.ext ↪[L] M, f.comp d.incl = a :=
  realize_extensionAxiom_iff _ _

/-- The theory containing the extension axiom for every realizable finite inclusion.
The given bounds count the total number of generators, including the marked base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, line 334.
-/
def extensionTheory (hLF : T.IsLocallyFinite) (bound : FiniteInclusion T → ℕ) : L.Theory :=
  Set.range (fun d => extensionScheme hLF d (bound d))

/-- An existentially closed model satisfies the extension axiom whenever all its failures
of amalgamation admit obstructions with the specified total generator bound.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, line 336.
-/
theorem IsExistentiallyClosed.realize_extensionScheme_of_bound (hLF : T.IsLocallyFinite)
    (d : FiniteInclusion T) (n : ℕ) (M : T.ModelType.{u, v, max u v})
    (hM : T.IsExistentiallyClosed M)
    (hbound : ∀ j : d.base ↪[L] M, ¬ T.AmalgamableOver d.incl j →
      ∃ (C : L.Substructure M) (hj : ∀ a, j a ∈ C), C.GeneratedByAtMost n ∧
        ¬ T.AmalgamableOver d.incl (j.codRestrict C hj)) :
    M ⊨ extensionScheme hLF d n := by
  classical
  apply (realize_extensionScheme_iff hLF d n).mpr
  intro j hgood
  apply (hM.amalgamableOver_iff_exists_embedding d.incl j).mp
  by_contra hbad
  obtain ⟨C, hj, hgen, hbadC⟩ := hbound j hbad
  obtain ⟨p, e, he⟩ := exists_badMarkedStructure hLF d n M C
    (j.codRestrict C hj) hgen hbadC
  apply hgood p
  refine ⟨C.subtype.comp e.toEmbedding, ?_⟩
  apply Embedding.ext
  intro a
  exact congrArg (fun c : C => (c : M)) (DFunLike.congr_fun he a)

/-- Every model satisfying the extension axioms is existentially closed. Only soundness of
the forbidden families is used here; the chosen generator bounds may be arbitrary.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 337–341.
-/
theorem isExistentiallyClosed_of_models_extensionTheory (hLF : T.IsLocallyFinite)
    (bound : FiniteInclusion T → ℕ) (M : T.ModelType.{u, v, max u v})
    (hSigma : M ⊨ extensionTheory hLF bound) : T.IsExistentiallyClosed M := by
  classical
  refine ⟨M.nonempty', M.is_model, ?_⟩
  intro N f m φ x hφ hreal
  obtain ⟨k, hk⟩ := hφ.exists_bounded_finite_witnesses_formula
  obtain ⟨s, hs, htransfer⟩ := hk N (f ∘ x) hreal
  let A : L.Substructure M := Substructure.closure L (Set.range x)
  let : Finite A := hLF.finite_closure_range M x
  let B : L.Substructure N := Substructure.closure L
    ((s : Set N) ∪ Set.range (f ∘ A.subtype))
  let : Finite B := hLF N _ (s.finite_toSet.union (Set.finite_range (f ∘ A.subtype)))
  have hmemB : ∀ a : A, f (a : M) ∈ B := fun a =>
    Substructure.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)
  let i : A ↪[L] B := (f.comp A.subtype).codRestrict B hmemB
  let d : FiniteInclusion T :=
    { base := A, ext := B, incl := i, embeddable := ⟨N, ⟨B.subtype⟩⟩ }
  have hax : M ⊨ extensionScheme hLF d (bound d) :=
    hSigma.realize_of_mem _ (Set.mem_range_self d)
  rw [realize_extensionScheme_iff] at hax
  have hgood : ∀ p : BadMarkedStructure d (bound d) (obstructionCardBound hLF d (bound d)),
      ¬ ∃ g : p.Carrier ↪[L] M, g.comp p.mark = A.subtype := by
    rintro p ⟨g, hg⟩
    apply p.not_amalgamable
    refine ⟨N, B.subtype, f.comp g, ?_⟩
    apply Embedding.ext
    intro a
    exact (congrArg f (DFunLike.congr_fun hg a)).symm
  obtain ⟨g, hg⟩ := hax A.subtype hgood
  have hxA : ∀ l, x l ∈ A := fun l => Substructure.subset_closure ⟨l, rfl⟩
  let xB : Fin m → B := fun l => ⟨f (x l), hmemB ⟨x l, hxA l⟩⟩
  have hsB : (s : Set N) ⊆ Set.range B.subtype := fun y hy =>
    ⟨⟨y, Substructure.subset_closure (Set.mem_union_left _ hy)⟩, rfl⟩
  have hBreal : φ.Realize xB := htransfer B B.subtype hsB xB rfl
  have hMreal := hφ.realize_formula_embedding g hBreal
  have hcomp : (g : B → M) ∘ xB = x := by
    funext l
    exact DFunLike.congr_fun hg ⟨x l, hxA l⟩
  rwa [hcomp] at hMreal

/-- **Fact 2.6, sufficiency.** Bounded finite amalgamation obstructions axiomatize the
existentially closed class of a locally finite Pi-two theory in a finite language, and hence
produce a model companion. No universality assumption on the theory is used.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, implication 2 → 1.
-/
theorem hasModelCompanion_of_boundedAmalgamationObstructions (hPi : T.IsPiTwo)
    (hLF : T.IsLocallyFinite) (hbound : T.BoundedAmalgamationObstructions) :
    T.HasModelCompanion := by
  classical
  choose bound hbound using hbound
  let Tstar := T ∪ extensionTheory hLF bound
  refine ⟨Tstar, isModelCompanionOf_of_isExistentiallyClosed_iff hPi ?_ ?_⟩
  · intro M
    let : M ⊨ T := M.is_model.mono Set.subset_union_left
    exact isExistentiallyClosed_of_models_extensionTheory hLF bound (ModelType.of T M)
      (M.is_model.mono Set.subset_union_right)
  · intro M hM
    apply (model_iff _).mpr
    intro σ hσ
    rcases hσ with hσ | ⟨d, rfl⟩
    · exact M.is_model.realize_of_mem _ hσ
    · exact hM.realize_extensionScheme_of_bound hLF d (bound d) M (hbound d M hM)

/-- **Fact 2.6.** For a locally finite Pi-two theory in a finite language, existence of a
model companion is equivalent to the bounded-amalgamation-obstruction condition.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v7.tex, `fact:locally finiteness and model companion`, lines 293–306.
-/
theorem hasModelCompanion_iff_boundedAmalgamationObstructions (hPi : T.IsPiTwo)
    (hLF : T.IsLocallyFinite) : T.HasModelCompanion ↔ T.BoundedAmalgamationObstructions :=
  ⟨fun h => h.boundedAmalgamationObstructions hPi,
    hasModelCompanion_of_boundedAmalgamationObstructions hPi hLF⟩

end FirstOrder.Language.Theory
