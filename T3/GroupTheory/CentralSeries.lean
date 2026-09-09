/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Identities
public import Mathlib.GroupTheory.Nilpotent

/-!
# Central series and strict subgroups

We use mathlib's central series directly. Its `(⊤ : Subgroup G).lowerCentralSeries n`
is the paper's `γₙ₊₁(G)`, while `Subgroup.upperCentralSeries G n` is the paper's `Zₙ(G)`.
The relative lower central series `S.lowerCentralSeries n` is the image of the internal
series of `S`, by `Subgroup.top_subtype_lowerCentralSeries`.

The general group results identify the upper series by iterated commutators, bound commutators
of lower central terms, prove that successive quotients are commutative, and compare the lower
and upper series under a nilpotency bound. The degree bound follows from mathlib's Three
Subgroups Lemma, applied in a quotient; none of these results assumes exponent three.

`T3.IsStrict S` states the paper's two intersection equalities for a subgroup `S`.
For an injective homomorphism `f`, `T3.isStrict_range_iff_comap` gives the equivalent
inverse-image equalities. `T3.CentralSeriesCoincide G` states equality of the lower and upper
series in reverse order. The final inclusion chain proves that this internal condition makes
an exponent-three subgroup strict in every exponent-three ambient group.

Paper-ID: preliminaries.central_series, preliminaries.upper_central_recursive,
preliminaries.central_series_properties, preliminaries.lcs_strictness,
preliminaries.central_series_coincide, preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.12, Remark 2.13, Fact 2.14,
Definitions 2.23 and 2.25, and Lemma 2.26.
-/

@[expose] public section

open scoped commutatorElement

namespace Subgroup
variable {G : Type*} [Group G]

/-- The Three Subgroups Lemma modulo a normal subgroup, used for the lower central degree bound.

Paper-ID: preliminaries.central_series_properties
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.14, supporting lemma for item 1.
-/
theorem commutator_commutator_le_of_rotate (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ N) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  have hmap (S : Subgroup G) : S.map (QuotientGroup.mk' N) = ⊥ ↔ S ≤ N := by
    rw [map_eq_bot_iff, QuotientGroup.ker_mk']
  apply (hmap _).mp
  rw [map_commutator, map_commutator]
  apply commutator_commutator_eq_bot_of_rotate
  · simpa only [map_commutator] using (hmap _).mpr h₁
  · simpa only [map_commutator] using (hmap _).mpr h₂

/-- Commutators add lower central degrees. Mathlib indices `m` and `n` correspond to
the paper's degrees `m + 1` and `n + 1`, so the resulting mathlib index is `m + n + 1`.

Paper-ID: preliminaries.central_series_properties
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.14, item 1.
-/
theorem commutator_lowerCentralSeries_le (m n : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries m, (⊤ : Subgroup G).lowerCentralSeries n⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (m + n + 1) := by
  induction n generalizing m with
  | zero => simp only [lowerCentralSeries_zero, Nat.add_zero, lowerCentralSeries_succ, le_refl]
  | succ n ih =>
    rw [lowerCentralSeries_succ, commutator_comm]
    apply commutator_commutator_le_of_rotate
    · rw [commutator_comm ⊤ _, ← lowerCentralSeries_succ]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (m + 1)
    · calc
        ⁅⁅(⊤ : Subgroup G).lowerCentralSeries m, (⊤ : Subgroup G).lowerCentralSeries n⁆, ⊤⁆ ≤
            ⁅(⊤ : Subgroup G).lowerCentralSeries (m + n + 1), ⊤⁆ :=
          commutator_mono (ih m) (le_refl (⊤ : Subgroup G))
        _ = (⊤ : Subgroup G).lowerCentralSeries (m + n.succ + 1) := by
          rw [← lowerCentralSeries_succ]
          congr 1

/-- A lower central series terminating at index `n` lies below the reversed upper series.

Paper-ID: preliminaries.central_series_properties
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.14, supporting form of item 2.
-/
theorem lowerCentralSeries_le_upperCentralSeries_of_eq_bot {n : ℕ}
    (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥) (i : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries i ≤ upperCentralSeries G (n - i) :=
  descending_central_series_ge_lower _
    (is_descending_rev_series_of_is_ascending G
      (lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top.mp hn)
      (upperCentralSeries_isAscendingCentralSeries G)) i

/-- If a group has nilpotency class at most `n`, its lower series lies below the reversed
upper series. The index `i` here denotes the paper's degree `i + 1`.

Paper-ID: preliminaries.central_series_properties
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.14, item 2.
-/
theorem lowerCentralSeries_le_upperCentralSeries [Group.IsNilpotent G] {n : ℕ}
    (hn : Group.nilpotencyClass G ≤ n) (i : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries i ≤ upperCentralSeries G (n - i) :=
  lowerCentralSeries_le_upperCentralSeries_of_eq_bot
    (lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn) i

/-- An injective homomorphism reflects membership in the upper central series.
For a subgroup inclusion, this gives `Zₙ(H) ∩ G ≤ Zₙ(G)`.

Paper-ID: preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.26, supporting lemma for item 1.
-/
theorem comap_upperCentralSeries_le_of_injective {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Injective f) (n : ℕ) :
    (upperCentralSeries H n).comap f ≤ upperCentralSeries G n := by
  induction n with
  | zero =>
    intro x hx
    apply hf
    simpa only [upperCentralSeries_zero, mem_comap, mem_bot, map_one] using hx
  | succ n ih =>
    intro x hx
    rw [mem_upperCentralSeries_succ_iff]
    intro y
    apply ih
    change f ⁅x, y⁆ ∈ upperCentralSeries H n
    rw [map_commutatorElement]
    exact mem_upperCentralSeries_succ_iff.mp hx (f y)

/-- Each quotient of consecutive lower central terms is commutative, for an arbitrary group.

Paper-ID: preliminaries.central_series_properties
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.14, item 1.
-/
theorem isMulCommutative_lowerCentralSeries_quotient (n : ℕ) :
    IsMulCommutative ((⊤ : Subgroup G).lowerCentralSeries n ⧸
      ((⊤ : Subgroup G).lowerCentralSeries (n + 1)).subgroupOf
        ((⊤ : Subgroup G).lowerCentralSeries n)) := by
  apply Normal.quotient_commutative_iff_commutator_le.mpr
  change (_root_.commutator ((⊤ : Subgroup G).lowerCentralSeries n)) ≤
    ((⊤ : Subgroup G).lowerCentralSeries (n + 1)).comap
      ((⊤ : Subgroup G).lowerCentralSeries n).subtype
  rw [← map_le_iff_le_comap]
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, subtype_range]
  exact commutator_mono le_rfl le_top

end Subgroup

namespace T3

variable {G : Type*} [Group G]

/-- The left-associated commutator starting at `a` and successively using the entries of `l`.
For the empty list, its value is `a`.

Paper-ID: preliminaries.notation, preliminaries.central_series
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1, item 2, and Definition 2.12.
-/
def iteratedCommutator (a : G) (l : List G) : G :=
  l.foldl (fun x y => ⁅x, y⁆) a

/-- Membership in the recursive upper central series is equivalent to vanishing of every
iterated commutator with a list of `n` further arguments.

Paper-ID: preliminaries.upper_central_recursive
TeX: T3_modelcompanion_v4.tex, v4 Remark 2.13.
-/
theorem mem_upperCentralSeries_iff_forall_iteratedCommutator (a : G) (n : ℕ) :
    a ∈ Subgroup.upperCentralSeries G n ↔
      ∀ l : List G, l.length = n → iteratedCommutator a l = 1 := by
  induction n generalizing a with
  | zero => simp [Subgroup.upperCentralSeries_zero, iteratedCommutator]
  | succ n ih =>
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    simp_rw [ih]
    constructor
    · intro h l hl
      cases l with
      | nil => simp at hl
      | cons x l =>
        exact h x l (Nat.succ.inj hl)
    · intro h x l hl
      exact h (x :: l) (by simp [hl])
/-- The paper's description of the upper central series by all `n`-tuples of arguments.
This agrees with mathlib's recursive definition, including `Z₀(G) = 1`.

Paper-ID: preliminaries.central_series, preliminaries.upper_central_recursive
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.12, item 2, and Remark 2.13.
-/
theorem mem_upperCentralSeries_iff_forall_fin (a : G) (n : ℕ) :
    a ∈ Subgroup.upperCentralSeries G n ↔
      ∀ v : Fin n → G, iteratedCommutator a (List.ofFn v) = 1 := by
  rw [mem_upperCentralSeries_iff_forall_iteratedCommutator]
  constructor
  · intro h v
    exact h (List.ofFn v) (List.length_ofFn)
  · intro h l hl
    subst n
    simpa only [List.ofFn_get] using h l.get

/-- The lower central series begins with the whole group: the paper's `γ₁(G) = G`.

Paper-ID: preliminaries.central_series
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.12, item 1.
-/
theorem lowerCentralSeries_initial (G : Type*) [Group G] :
    (⊤ : Subgroup G).lowerCentralSeries 0 = ⊤ := rfl

/-- The next lower central term is the commutator with the whole group.
The index `n` here represents the paper's degree `n + 1`.

Paper-ID: preliminaries.central_series
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.12, item 1.
-/
theorem lowerCentralSeries_step (G : Type*) [Group G] (n : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries (n + 1) =
      ⁅(⊤ : Subgroup G).lowerCentralSeries n, ⊤⁆ := rfl

/-- A subgroup is strict if its second and third lower central terms are the intersections
with the corresponding ambient terms. The relative series is read in the ambient group;
`Subgroup.top_subtype_lowerCentralSeries` identifies it with the internal series.

Paper-ID: preliminaries.lcs_strictness
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.23.
-/
def IsStrict (S : Subgroup G) : Prop :=
  S.lowerCentralSeries 1 = (⊤ : Subgroup G).lowerCentralSeries 1 ⊓ S ∧
    S.lowerCentralSeries 2 = (⊤ : Subgroup G).lowerCentralSeries 2 ⊓ S

/-- The lower and upper central series coincide in reverse order through class three.
The mathlib indices `0`, `1`, and `2` represent the paper's degrees `1`, `2`, and `3`.

Paper-ID: preliminaries.central_series_coincide
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.25.
-/
def CentralSeriesCoincide (G : Type*) [Group G] : Prop :=
  ∀ i : ℕ, i < 3 → (⊤ : Subgroup G).lowerCentralSeries i =
    Subgroup.upperCentralSeries G (3 - i)

/-- For an injective homomorphism, strictness of its image is equivalent to the two
inverse-image equalities for lower central terms. No exponent assumption is needed.

Paper-ID: preliminaries.lcs_strictness
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.23, homomorphism form.
-/
theorem isStrict_range_iff_comap {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Injective f) :
    IsStrict f.range ↔
      (⊤ : Subgroup G).lowerCentralSeries 1 =
        ((⊤ : Subgroup H).lowerCentralSeries 1).comap f ∧
      (⊤ : Subgroup G).lowerCentralSeries 2 =
        ((⊤ : Subgroup H).lowerCentralSeries 2).comap f := by
  have h (n : ℕ) :
      f.range.lowerCentralSeries n = (⊤ : Subgroup H).lowerCentralSeries n ⊓ f.range ↔
        (⊤ : Subgroup G).lowerCentralSeries n =
          ((⊤ : Subgroup H).lowerCentralSeries n).comap f := by
    constructor
    · intro hn
      apply Subgroup.map_injective hf
      rw [Subgroup.map_lowerCentralSeries, ← MonoidHom.range_eq_map,
        Subgroup.map_comap_eq, hn, inf_comm]
    · intro hn
      have hm := congrArg (Subgroup.map f) hn
      simpa only [Subgroup.map_lowerCentralSeries, ← MonoidHom.range_eq_map,
        Subgroup.map_comap_eq, inf_comm] using hm
  exact and_congr (h 1) (h 2)

/-- A subgroup's lower central terms lie in the corresponding ambient terms and in the subgroup.

Paper-ID: preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.26, first inclusion in item 1.
-/
theorem lowerCentralSeries_le_ambient_inf (S : Subgroup G) (n : ℕ) :
    S.lowerCentralSeries n ≤ (⊤ : Subgroup G).lowerCentralSeries n ⊓ S :=
  le_inf (Subgroup.lowerCentralSeries_mono n le_top) (S.lowerCentralSeries_le_self n)

/-- The intersection of an ambient upper central term with a subgroup lies in its internal
upper central term, read in the ambient group.

Paper-ID: preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.26, last inclusion in item 1.
-/
theorem upperCentralSeries_inf_le_map_subtype (S : Subgroup G) (n : ℕ) :
    Subgroup.upperCentralSeries G n ⊓ S ≤ (Subgroup.upperCentralSeries S n).map S.subtype := by
  intro x hx
  have hu : (⟨x, hx.2⟩ : S) ∈ Subgroup.upperCentralSeries S n :=
    Subgroup.comap_upperCentralSeries_le_of_injective S.subtype Subtype.val_injective n hx.1
  exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hu, rfl⟩

/-- The chain from a subgroup's lower central series to its reversed upper central series
inside an exponent-three ambient group. The paper uses indices `n < 3`; the same chain
also holds afterward, when all these terms are trivial.

Paper-ID: preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.26, item 1.
-/
theorem centralSeries_inclusions (hG : HasExponentThree G) (S : Subgroup G) (n : ℕ) :
    S.lowerCentralSeries n ≤ (⊤ : Subgroup G).lowerCentralSeries n ⊓ S ∧
    (⊤ : Subgroup G).lowerCentralSeries n ⊓ S ≤
      Subgroup.upperCentralSeries G (3 - n) ⊓ S ∧
    Subgroup.upperCentralSeries G (3 - n) ⊓ S ≤
      (Subgroup.upperCentralSeries S (3 - n)).map S.subtype :=
  ⟨lowerCentralSeries_le_ambient_inf S n,
    inf_le_inf (Subgroup.lowerCentralSeries_le_upperCentralSeries_of_eq_bot
      (lowerCentralSeries_three_eq_bot hG) n) le_rfl,
    upperCentralSeries_inf_le_map_subtype S (3 - n)⟩

/-- Internal coincidence of the central series implies strictness in every exponent-three
ambient group, by the inclusion chain of the paper.

Paper-ID: preliminaries.strict_of_internal
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.26, item 2.
-/
theorem isStrict_of_centralSeriesCoincide (hG : HasExponentThree G) (S : Subgroup G)
    (hS : CentralSeriesCoincide S) : IsStrict S := by
  have heq (n : ℕ) (hn : n < 3) :
      S.lowerCentralSeries n = (⊤ : Subgroup G).lowerCentralSeries n ⊓ S := by
    have hc := centralSeries_inclusions hG S n
    apply le_antisymm hc.1
    calc
      (⊤ : Subgroup G).lowerCentralSeries n ⊓ S ≤
          (Subgroup.upperCentralSeries S (3 - n)).map S.subtype := hc.2.1.trans hc.2.2
      _ = S.lowerCentralSeries n := by
        rw [← hS n hn, Subgroup.top_subtype_lowerCentralSeries]
  exact ⟨heq 1 (by decide), heq 2 (by decide)⟩
/-- Strictness of a subgroup, expressed using its internal lower central series and the
inverse images of ambient lower central terms.

Paper-ID: preliminaries.lcs_strictness
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.23, internal form.
-/
theorem isStrict_iff_comap_subtype (S : Subgroup G) :
    IsStrict S ↔
      (⊤ : Subgroup S).lowerCentralSeries 1 =
        ((⊤ : Subgroup G).lowerCentralSeries 1).comap S.subtype ∧
      (⊤ : Subgroup S).lowerCentralSeries 2 =
        ((⊤ : Subgroup G).lowerCentralSeries 2).comap S.subtype := by
  simpa only [Subgroup.range_subtype] using
    isStrict_range_iff_comap S.subtype Subtype.val_injective

/-- For an exponent-three group, internal coincidence reduces to the two nonautomatic
equalities: the derived subgroup is the second center, and the third lower term is the center.

Paper-ID: preliminaries.central_series_coincide
TeX: T3_modelcompanion_v4.tex, v4 Definition 2.25.
-/
theorem centralSeriesCoincide_iff (hG : HasExponentThree G) :
    CentralSeriesCoincide G ↔ commutator G = Subgroup.upperCentralSeries G 2 ∧
      (⊤ : Subgroup G).lowerCentralSeries 2 = Subgroup.center G := by
  constructor
  · intro h
    constructor
    · simpa only [Subgroup.top_lowerCentralSeries_one, Nat.reduceSub] using h 1 (by decide)
    · simpa only [Subgroup.upperCentralSeries_one, Nat.reduceSub] using h 2 (by decide)
  · rintro ⟨h₁, h₂⟩ n hn
    have h₀ : Subgroup.upperCentralSeries G 3 = ⊤ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top.mp
        (lowerCentralSeries_three_eq_bot hG)
    interval_cases n
    · simpa only [Subgroup.lowerCentralSeries_zero, Nat.sub_zero] using h₀.symm
    · simpa only [Subgroup.top_lowerCentralSeries_one, Nat.reduceSub] using h₁
    · simpa only [Subgroup.upperCentralSeries_one, Nat.reduceSub] using h₂

/-- Internal coincidence of the two central series is preserved by group isomorphisms.
No exponent or finiteness condition is needed for this transport.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v4.tex, `proposition:bdd LCS`, transporting the structure of D₃ to D.
-/
theorem CentralSeriesCoincide.mulEquiv {H : Type*} [Group H]
    (hG : CentralSeriesCoincide G) (e : G ≃* H) : CentralSeriesCoincide H := by
  intro i hi
  calc
    (⊤ : Subgroup H).lowerCentralSeries i =
        ((⊤ : Subgroup G).lowerCentralSeries i).map e := by
      rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective _ e.surjective]
    _ = (Subgroup.upperCentralSeries G (3 - i)).map e :=
      congrArg (Subgroup.map e.toMonoidHom) (hG i hi)
    _ = Subgroup.upperCentralSeries H (3 - i) := by
      rw [← Subgroup.comap_upperCentralSeries e, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq]

end T3

namespace Subgroup

variable {G : Type*} [Group G]

/-- A single lower-central intersection equality is equivalent to the corresponding
inverse-image equality for the subgroup's inclusion.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v4.tex, `proposition:bdd LCS`, the passage from the first to the
second strictification step, lines 1224–1229.
-/
theorem lowerCentralSeries_eq_inf_iff_comap (S : Subgroup G) (k : ℕ) :
    S.lowerCentralSeries k = (⊤ : Subgroup G).lowerCentralSeries k ⊓ S ↔
      (⊤ : Subgroup S).lowerCentralSeries k =
        ((⊤ : Subgroup G).lowerCentralSeries k).comap S.subtype := by
  constructor
  · intro h
    apply map_injective (f := S.subtype) Subtype.val_injective
    rw [top_subtype_lowerCentralSeries, map_comap_eq, range_subtype, h, inf_comm]
  · intro h
    have hm := congrArg (Subgroup.map S.subtype) h
    simpa only [top_subtype_lowerCentralSeries, map_comap_eq, range_subtype, inf_comm] using hm

end Subgroup
