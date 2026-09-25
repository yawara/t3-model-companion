/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.ModelTheory.DirectLimit
public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Complexity

/-!
# The elementary chain theorem

Tarski's elementary chain theorem: the canonical maps into the direct limit of a directed
system of first-order embeddings are elementary, provided the transition maps are elementary
cofinally often. The precise hypothesis is that for all indices `i` and `j` there is an upper
bound `k` of both such that the transition `f i k` is elementary; this covers both the classical
statement (all transitions elementary) and interleaved chains where only the composites of
consecutive pairs of transitions are elementary, which is the form needed for Robinson's
model-completeness test.

This file depends only on mathlib. It supplies the elementary-chain step in the converse of
Fact 2.3, without any assumption on a theory.

Paper-ID: `model_theory.companion_iff_ec`.
Source: `T3_modelcompanion_v9.tex`, Fact 2.3, lines 289–295.

## Main results

- `FirstOrder.Language.DirectLimit.realize_boundedFormula_of` : the canonical map
  `of L ι G f i` preserves and reflects all bounded formulas, under the cofinal elementarity
  hypothesis;
- `FirstOrder.Language.DirectLimit.realize_formula_of` : the same for formulas;
- `FirstOrder.Language.DirectLimit.ofElementary` : the canonical map bundled as an elementary
  embedding `G i ↪ₑ[L] DirectLimit G f`;
- `FirstOrder.Language.DirectLimit.ofElementaryOfForallElementary` : the classical elementary
  chain theorem, where every transition map is elementary.
-/

@[expose] public section

universe v w u'

open FirstOrder

namespace FirstOrder

namespace Language

namespace DirectLimit

open Structure Set

variable {L : Language} {ι : Type v} [Preorder ι]
variable {G : ι → Type w} [∀ i, L.Structure (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪[L] G j)

/--
The hypothesis of the refined elementary chain theorem: any two indices admit a common upper
bound to which the transition from the first index is elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
def CofinallyElementary : Prop :=
  ∀ i j : ι, ∃ (k : ι) (hik : i ≤ k) (_hjk : j ≤ k),
    ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → G i),
      φ.Realize (f i k hik ∘ x) ↔ φ.Realize x

/-- If every transition map of the system is elementary, then it is cofinally elementary.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem CofinallyElementary.of_forall_elementary [IsDirectedOrder ι]
    (h : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → G i),
      φ.Realize (f i j hij ∘ x) ↔ φ.Realize x) :
    CofinallyElementary f := by
  intro i j
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨k, hik, hjk, h i k hik⟩

variable {f}

/-- A transition map witnessing cofinal elementarity, as an elementary embedding.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
def CofinallyElementary.elementaryEmbedding {i k : ι} {hik : i ≤ k}
    (hel : ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → G i),
      φ.Realize (f i k hik ∘ x) ↔ φ.Realize x) :
    G i ↪ₑ[L] G k :=
  ⟨f i k hik, fun _ φ x => hel _ φ x⟩

variable [DirectedSystem G fun i j h => f i j h] [IsDirectedOrder ι] [Nonempty ι]

/--
**The elementary chain theorem**, bounded-formula version: in a cofinally elementary directed
system, the canonical maps into the direct limit preserve and reflect all bounded formulas.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem realize_boundedFormula_of (h : CofinallyElementary f) {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) (i : ι) (v : α → G i) (xs : Fin n → G i) :
    φ.Realize (of L ι G f i ∘ v) (of L ι G f i ∘ xs) ↔ φ.Realize v xs := by
  induction φ generalizing i with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    exact (BoundedFormula.IsAtomic.equal t₁ t₂).isQF.realize_embedding (of L ι G f i)
  | rel R ts =>
    exact (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding (of L ι G f i)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, ih₁ i v xs, ih₂ i v xs]
  | all φ' ih =>
    rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
    constructor
    · -- The universal statement descends to the component along the canonical map.
      intro hD b
      have hb := hD (of L ι G f i b)
      rw [← Fin.comp_snoc] at hb
      exact (ih i v (Fin.snoc xs b)).1 hb
    · -- The direct limit satisfies the universal statement: push the witness index upward.
      intro hG a
      obtain ⟨j, y, rfl⟩ := exists_of a
      obtain ⟨k, hik, hjk, hel⟩ := h i j
      have hall : (φ'.all).Realize v xs := BoundedFormula.realize_all.2 hG
      have hallk : (φ'.all).Realize (f i k hik ∘ v) (f i k hik ∘ xs) :=
        ((CofinallyElementary.elementaryEmbedding hel).map_boundedFormula φ'.all v xs).2 hall
      have hk : φ'.Realize (f i k hik ∘ v) (Fin.snoc (f i k hik ∘ xs) (f j k hjk y)) :=
        BoundedFormula.realize_all.1 hallk (f j k hjk y)
      have hD := (ih k (f i k hik ∘ v) (Fin.snoc (f i k hik ∘ xs) (f j k hjk y))).2 hk
      have hv : of L ι G f k ∘ (f i k hik ∘ v) = of L ι G f i ∘ v := by
        funext a
        exact of_f
      have hxs : of L ι G f k ∘ (Fin.snoc (f i k hik ∘ xs) (f j k hjk y) : _ → G k) =
          Fin.snoc (of L ι G f i ∘ xs) (of L ι G f j y) := by
        rw [Fin.comp_snoc]
        congr 1
        · funext a
          exact of_f
        · exact of_f
      rw [hv, hxs] at hD
      exact hD

/--
**The elementary chain theorem**, formula version: in a cofinally elementary directed system,
the canonical maps into the direct limit preserve and reflect all formulas.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
theorem realize_formula_of (h : CofinallyElementary f) {α : Type u'}
    (φ : L.Formula α) (i : ι) (v : α → G i) :
    φ.Realize (of L ι G f i ∘ v) ↔ φ.Realize v := by
  have hb := realize_boundedFormula_of h φ i v default
  rwa [Unique.eq_default (of L ι G f i ∘ (default : Fin 0 → G i))] at hb

variable (f)

/--
**The elementary chain theorem**: in a cofinally elementary directed system, the canonical map
from any component to the direct limit is an elementary embedding.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable def ofElementary (h : CofinallyElementary f) (i : ι) :
    G i ↪ₑ[L] DirectLimit G f :=
  ⟨of L ι G f i, fun _ φ x => realize_formula_of h φ i x⟩

@[simp]
theorem ofElementary_apply (h : CofinallyElementary f) (i : ι) (x : G i) :
    ofElementary f h i x = of L ι G f i x :=
  rfl

/--
The classical elementary chain theorem: if every transition map of a directed system is
elementary, then the canonical map from any component to the direct limit is an elementary
embedding.

Paper-ID: model_theory.companion_iff_ec
TeX: T3_modelcompanion_v9.tex, supporting Fact 2.3, lines 289–295; no label.
-/
noncomputable def ofElementaryOfForallElementary
    (h : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → G i),
      φ.Realize (f i j hij ∘ x) ↔ φ.Realize x) (i : ι) :
    G i ↪ₑ[L] DirectLimit G f :=
  ofElementary f (CofinallyElementary.of_forall_elementary f h) i

end DirectLimit

end Language

end FirstOrder
