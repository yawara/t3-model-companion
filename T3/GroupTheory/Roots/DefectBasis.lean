/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.GeneratorRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Representatives of bases for the strictness defects

For a subgroup inclusion, the kernel of its map on the first graded layer is exactly the
defect `(C ∩ γ₂(G)) / γ₂(C)` in Lemma 4.8. In degree two the kernel describes
`(γ₂(C) ∩ γ₃(G)) / γ₃(C)`; identifying this numerator with `C ∩ γ₃(G)` requires the
first strictness conclusion, as in Lemma 4.10.

This module chooses a basis of the actual kernel and lifts it to group elements. Its final
subgroup equality states that these representatives generate the defect modulo the next
intrinsic central term. Finiteness is required only for the source layer, not the ambient group.

Paper-ID: structure.derived_strictification, structure.lcs_strictification
TeX: T3_modelcompanion_v7.tex, `lemma:commutator root`, lines 1165–1167, and
`lemma:number of generators for triple commutator roots`, lines 1225–1226.
-/

@[expose] public section

namespace T3.AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- A finite-dimensional graded kernel has a basis represented by group elements. Those
representatives generate its full group preimage modulo the next intrinsic central term.

For an inclusion this is the basis choice used in the two strictification steps. The theorem
also applies to general homomorphisms and includes zero-dimensional kernels.

Paper-ID: structure.derived_strictification, structure.lcs_strictification
TeX: T3_modelcompanion_v7.tex, `lemma:commutator root`, lines 1165–1167, and
`lemma:number of generators for triple commutator roots`, lines 1225–1226.
-/
theorem exists_layer_kernel_basis_representatives (f : G →* H) (k : ℕ)
    [Module.Finite (ZMod 3) (Layer G k)] :
    ∃ d ≤ Module.finrank (ZMod 3) (Layer G k),
      ∃ b : Module.Basis (Fin d) (ZMod 3) (mapLayer f k).ker,
      ∃ g : Fin d → term G k,
        (∀ i, mk G k (g i) = (b i : Layer G k)) ∧
        (∀ i, f (g i) ∈ term H (k + 1)) ∧
        (term H (k + 1)).comap f ⊓ term G k =
          term G (k + 1) ⊔ Subgroup.closure (Set.range fun i => (g i : G)) := by
  classical
  let W := (mapLayer f k).ker
  let d := Module.finrank (ZMod 3) W
  let b := Module.finBasis (ZMod 3) W
  choose g hg using fun i : Fin d => mk_surjective G k (b i : Layer G k)
  have hfg (i : Fin d) : f (g i) ∈ term H (k + 1) := by
    have hi := (b i).property
    change mapLayer f k (b i : Layer G k) = 0 at hi
    rw [← hg i, mapLayer_mk, mk_eq_zero] at hi
    exact hi
  refine ⟨d, Submodule.finrank_le W, b, g, hg, hfg, ?_⟩
  let S := term G (k + 1) ⊔ Subgroup.closure (Set.range fun i => (g i : G))
  have hspan (w : W) : (w : Layer G k) ∈ subgroupImage S k := by
    have hw : w ∈ Submodule.span (ZMod 3) (Set.range b) := by
      rw [b.span_eq]
      trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hg i]
      exact (mem_subgroupImage S k _).mpr
        ⟨g i, (show Subgroup.closure (Set.range fun i => (g i : G)) ≤ S from le_sup_right)
          (Subgroup.subset_closure ⟨i, rfl⟩), rfl⟩
    | zero => exact (subgroupImage S k).zero_mem
    | add x y hx hy ihx ihy => exact (subgroupImage S k).add_mem ihx ihy
    | smul c x hx ih => exact (subgroupImage S k).smul_mem c ih
  apply le_antisymm
  · intro x hx
    let a : term G k := ⟨x, hx.2⟩
    have ha : mk G k a ∈ W := by
      change mapLayer f k (mk G k a) = 0
      rw [mapLayer_mk, mk_eq_zero]
      exact hx.1
    obtain ⟨y, hy, he⟩ := (mem_subgroupImage S k _).mp (hspan ⟨mk G k a, ha⟩)
    have hxy : (a * y⁻¹ : term G k) ∈ relation G k := by
      change ((a * y⁻¹ : term G k) : G) ∈ (⊤ : Subgroup G).lowerCentralSeries k
      apply (mk_eq_zero G k _).mp
      change mk G k a + -mk G k y = 0
      rw [he, add_neg_cancel]
    have hxyS : x * (y : G)⁻¹ ∈ S :=
      (show term G (k + 1) ≤ S from le_sup_left) hxy
    have h := S.mul_mem hxyS hy
    simpa using h
  · apply sup_le
    · intro x hx
      refine ⟨?_, ?_⟩
      · exact (termMap f (k + 1) ⟨x, hx⟩).property
      · exact Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by omega) hx
    · apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      exact ⟨hfg i, (g i).property⟩

/-- The first strictness defect is generated modulo the derived subgroup by at most the
minimum number of generators of the source group. The generators lift a basis of the actual
first-layer kernel in `exists_layer_kernel_basis_representatives`.

Paper-ID: structure.derived_strictification
TeX: T3_modelcompanion_v7.tex, `lemma:commutator root`, lines 1165–1167.
-/
theorem exists_derived_defect_generators [Group.FG G] (f : G →* H) :
    ∃ d ≤ Group.rank G, ∃ g : Fin d → G,
      (∀ i, f (g i) ∈ commutator H) ∧
      (commutator H).comap f = commutator G ⊔ Subgroup.closure (Set.range g) := by
  obtain ⟨d, hd, b, g, _, hg, he⟩ := exists_layer_kernel_basis_representatives f 1
  refine ⟨d, hd.trans finrank_layerOne_le_rank, fun i => g i, ?_, ?_⟩
  · simpa only [term, Nat.reduceAdd, Nat.reduceSub, Subgroup.top_lowerCentralSeries_one] using hg
  · simpa only [term, Nat.reduceAdd, Nat.reduceSub, Subgroup.top_lowerCentralSeries_one,
      Subgroup.lowerCentralSeries_zero, inf_top_eq] using he

/-- Once the first strictness equality holds, the second defect is generated modulo `γ₃`
by at most the number of pairs of a minimum generating family. Each representative lies in
the intrinsic derived subgroup and maps into the ambient third lower central term.

The first strictness hypothesis is used to identify the whole inverse image of `γ₃(H)` with
its intersection with `γ₂(G)`; it is not dropped when choosing the degree-two kernel basis.

Paper-ID: structure.lcs_strictification
TeX: T3_modelcompanion_v7.tex, `lemma:number of generators for triple commutator roots`,
lines 1225–1226.
-/
theorem exists_lowerCentral_defect_generators [Group.FG G] (f : G →* H)
    (hf : (commutator H).comap f = commutator G) :
    ∃ d ≤ (Group.rank G).choose 2, ∃ g : Fin d → G,
      (∀ i, g i ∈ commutator G) ∧ (∀ i, f (g i) ∈ term H 3) ∧
      (term H 3).comap f = term G 3 ⊔ Subgroup.closure (Set.range g) := by
  obtain ⟨d, hd, b, g, _, hg, he⟩ := exists_layer_kernel_basis_representatives f 2
  refine ⟨d, hd.trans finrank_layerTwo_le_rank, fun i => g i, ?_, hg, ?_⟩
  · intro i
    exact (g i).property
  · have hle : (term H 3).comap f ≤ term G 2 := by
      change (term H 3).comap f ≤ commutator G
      rw [← hf]
      apply Subgroup.comap_mono
      exact Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup H) (show 1 ≤ 2 by decide)
    simpa only [inf_eq_left.mpr hle] using he

end T3.AssociatedGraded
