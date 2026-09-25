/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.ModelTheory.BoundedAmalgamation
public import T3.ModelTheory.UniformLocalFiniteness

/-!
# Finite families of marked amalgamation obstructions

The uniform cardinal bound for a locally finite theory bounds the carriers of all obstructions
with a fixed total generator bound. On each finite carrier there are finitely many structures
in a finite language, including all function tables and both truth values of every relation.
There are also finitely many markings by a finite base. Transporting to these carriers therefore
gives finitely many marked isomorphism types of obstructions.

The representatives are selected from actual substructures of models of the theory. They retain
the total generator bound and non-amalgamability. Empty finite structures are allowed, and the
representatives are not assumed to satisfy the theory.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 340–346.
-/

@[expose] public section

open scoped FirstOrder

universe u v w w'

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- A finite language has only finitely many structures on a fixed finite carrier.
Nullary symbols and positive and negative relation tables are included.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, line 346.
-/
instance finiteStructure [Finite L.Symbols] (A : Type w) [Finite A] : Finite (L.Structure A) := by
  let encode (s : L.Structure A) :
      ((p : Σ n, L.Functions n) → (Fin p.1 → A) → A) ×
        ((p : Σ n, L.Relations n) → (Fin p.1 → A) → Prop) :=
    (fun p => @s.funMap p.1 p.2, fun p => @s.RelMap p.1 p.2)
  apply Finite.of_injective encode
  intro s t h
  have hf := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  cases s
  cases t
  congr
  · funext n f x
    exact congrFun (congrFun hf ⟨n, f⟩) x
  · funext n r x
    exact congrFun (congrFun hr ⟨n, r⟩) x

/-- Embeddings between fixed finite structures form a finite type.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, marked types on
line 346.
-/
instance finiteEmbedding {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] : Finite (A ↪[L] B) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

namespace Theory

variable {T : L.Theory}

/-- A finite carrier of size at most `m`, its structure, and a marking by the base.
The carrier is lifted to the canonical semantic universe, without changing its size.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, line 346.
-/
def FiniteMarkedStructure (A : Type w) [L.Structure A] (m : ℕ) :=
  Σ k : Fin (m + 1), Σ s : L.Structure (ULift.{max u v} (Fin k)),
    @Embedding L A (ULift.{max u v} (Fin k)) _ s

namespace FiniteMarkedStructure

variable {A : Type w} [L.Structure A] {m : ℕ}

/-- The carrier of a finite marked structure. -/
abbrev Carrier (p : FiniteMarkedStructure (L := L) A m) := ULift.{max u v} (Fin p.1)

/-- The recorded structure on the finite carrier. -/
instance (p : FiniteMarkedStructure (L := L) A m) : L.Structure p.Carrier := p.2.1

/-- The recorded marking of the base. -/
def mark (p : FiniteMarkedStructure (L := L) A m) : A ↪[L] p.Carrier := p.2.2

instance [Finite L.Symbols] [Finite A] : Finite (FiniteMarkedStructure (L := L) A m) := by
  unfold FiniteMarkedStructure
  infer_instance

/-- Every finite marked structure of bounded cardinality is isomorphic over its base to
one of the finitely many fixed-carrier structures.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, line 346.
-/
theorem exists_equiv {C : Type w'} [L.Structure C] [Finite C]
    (j : A ↪[L] C) (hC : Nat.card C ≤ m) :
    ∃ (p : FiniteMarkedStructure (L := L) A m) (e : C ≃[L] p.Carrier),
      e.toEmbedding.comp j = p.mark := by
  classical
  let k : Fin (m + 1) := ⟨Nat.card C, Nat.lt_succ_of_le hC⟩
  let : Fintype C := Fintype.ofFinite C
  let e₀ : C ≃ Fin (Nat.card C) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.equivFin C
  let e : C ≃ ULift.{max u v} (Fin k) :=
    e₀.trans Equiv.ulift.symm
  let : L.Structure (ULift.{max u v} (Fin k)) := e.inducedStructure
  let eL : C ≃[L] ULift.{max u v} (Fin k) := e.inducedStructureEquiv
  exact ⟨⟨k, inferInstance, eL.toEmbedding.comp j⟩, eL, rfl⟩

end FiniteMarkedStructure

/-- A fixed-carrier marked structure represents an actual obstruction of total generator
bound `n` inside a model of `T`. The equivalence preserves every element of the marked base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 340–344.
-/
def IsBadMarkedStructure (d : FiniteInclusion T) (n : ℕ) {m : ℕ}
    (p : FiniteMarkedStructure (L := L) d.base m) : Prop :=
  ∃ (M : T.ModelType.{u, v, max u v}) (C : L.Substructure M) (j : d.base ↪[L] C),
    C.GeneratedByAtMost n ∧ ¬ T.AmalgamableOver d.incl j ∧
      ∃ e : C ≃[L] p.Carrier, e.toEmbedding.comp j = p.mark

/-- The finite index type of bad marked structures on carriers of size at most `m`.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, `K(A,B)`.
-/
def BadMarkedStructure (d : FiniteInclusion T) (n m : ℕ) :=
  {p : FiniteMarkedStructure (L := L) d.base m // IsBadMarkedStructure d n p}

namespace BadMarkedStructure

variable {d : FiniteInclusion T} {n m : ℕ}

instance [Finite L.Symbols] : Finite (BadMarkedStructure d n m) := by
  unfold BadMarkedStructure
  infer_instance

/-- The finite carrier of a forbidden marked structure. -/
abbrev Carrier (p : BadMarkedStructure d n m) := p.val.Carrier

/-- The structure of a forbidden representative. -/
instance (p : BadMarkedStructure d n m) : L.Structure p.Carrier := inferInstanceAs
  (L.Structure p.val.Carrier)

/-- The marking of a forbidden representative. -/
def mark (p : BadMarkedStructure d n m) : d.base ↪[L] p.Carrier := p.val.mark

/-- Every forbidden representative embeds into a model of the original theory.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, item 1, line 342.
-/
theorem embeddable (p : BadMarkedStructure d n m) : T.Embeddable p.Carrier := by
  obtain ⟨M, C, j, hgen, hbad, e, he⟩ := p.property
  exact ⟨M, ⟨C.subtype.comp e.symm.toEmbedding⟩⟩

/-- No forbidden representative has an amalgam with the prescribed extension over its base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, item 2, line 343.
-/
theorem not_amalgamable (p : BadMarkedStructure d n m) :
    ¬ T.AmalgamableOver d.incl p.mark := by
  obtain ⟨M, C, j, hgen, hbad, e, he⟩ := p.property
  intro h
  apply hbad
  apply AmalgamableOver.of_comp_right e.toEmbedding
  rwa [he]

end BadMarkedStructure

/-- For each total generator bound, finitely many bad marked structures represent every
obstruction occurring inside a model. The isomorphisms fix the complete marked base.

Paper-ID: model_theory.bounded_amalgamation_criterion
TeX: T3_modelcompanion_v9.tex, `fact:locally finiteness and model companion`, lines 340–346.
-/
theorem IsLocallyFinite.exists_finite_bad_marked_cover [Finite L.Symbols]
    (hLF : T.IsLocallyFinite) (d : FiniteInclusion T) (n : ℕ) :
    ∃ m : ℕ, ∀ (M : T.ModelType.{u, v, max u v}) (C : L.Substructure M)
      (j : d.base ↪[L] C), C.GeneratedByAtMost n → ¬ T.AmalgamableOver d.incl j →
        ∃ (p : BadMarkedStructure d n m) (e : p.Carrier ≃[L] C),
          e.toEmbedding.comp p.mark = j := by
  classical
  obtain ⟨m, hm⟩ := exists_card_closure_le_of_isLocallyFinite hLF n
  refine ⟨m, ?_⟩
  intro M C j hgen hbad
  let : Finite C := hgen.finite hLF
  have hcard : Nat.card C ≤ m := by
    obtain ⟨s, hs, hC⟩ := hgen
    rw [← hC]
    exact hm M s hs
  obtain ⟨p, e, he⟩ := FiniteMarkedStructure.exists_equiv j hcard
  refine ⟨⟨p, M, C, j, hgen, hbad, e, he⟩, e.symm, ?_⟩
  apply Embedding.ext
  intro a
  change e.symm (p.mark a) = j a
  rw [← DFunLike.congr_fun he a]
  exact e.symm_apply_apply _

end Theory

end FirstOrder.Language
