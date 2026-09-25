/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.CentralSeries
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The vector spaces underlying the associated graded Lie algebra

`AssociatedGraded.Layer G n` is the additive group of the paper's quotient
`γₙ(G) / γₙ₊₁(G)` for positive `n`. Degree zero is `G / G`, hence zero.
The construction uses mathlib's lower central series, whose index zero is `G`.
For exponent-three groups the layers carry the canonical `ZMod 3` module structure.

`subgroupLayerEquiv` identifies the quotient of a subgroup's ambiently induced filtration
with its graded image. `map` is the direct sum of the induced linear maps and preserves
identities and composition. Its injectivity detects injectivity of the group homomorphism;
for an embedding, `map_injective_iff_isStrict` characterizes it by lower-central strictness.

This module constructs the underlying graded modules. `AssociatedGraded.Bracket` and
`AssociatedGraded.Lie` equip them with the commutator Lie bracket. The field-action instances use
`[Fact (HasExponentThree G)]`; an explicit exponent assumption supplies this instance locally.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, lines 485–502.
-/

@[expose] public section

open scoped commutatorElement DirectSum

namespace T3.AssociatedGraded

variable (G : Type*) [Group G]

/-- The paper's `γₙ(G)` for positive `n`, with `term G 0 = G` as well.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 1.
-/
abbrev term (n : ℕ) : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries (n - 1)

/-- The denominator `γₙ₊₁(G)` regarded as a subgroup of `γₙ(G)`.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 1.
-/
def relation (n : ℕ) : Subgroup (term G n) :=
  ((⊤ : Subgroup G).lowerCentralSeries n).comap (term G n).subtype

/-- The relation subgroup is normal in its central term.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, underlying degree quotients and direct sum.
-/
instance relation_normal (n : ℕ) : (relation G n).Normal := by
  unfold relation
  infer_instance

private theorem commutator_le_relation (n : ℕ) :
    commutator (term G n) ≤ relation G n := by
  cases n with
  | zero => exact le_top
  | succ n =>
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (Subgroup.isMulCommutative_lowerCentralSeries_quotient n)

/-- The multiplicative presentation of the degree quotient.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 1.
-/
abbrev MulLayer (n : ℕ) := term G n ⧸ relation G n

/-- The consecutive lower central quotient is commutative.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, underlying degree quotients and direct sum.
-/
instance mulLayerCommGroup (n : ℕ) : CommGroup (MulLayer G n) where
  __ := QuotientGroup.Quotient.group (relation G n)
  mul_comm := by
    let : IsMulCommutative (MulLayer G n) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (commutator_le_relation G n)
    exact mul_comm'

/-- The degree quotient with additive notation, ready for the canonical field action.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, item 1.
-/
abbrev Layer (n : ℕ) := Additive (MulLayer G n)

/-- The initial form of an element of `γₙ(G)` in degree `n`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20, item 1.
-/
def mk (n : ℕ) (x : term G n) : Layer G n :=
  Additive.ofMul (QuotientGroup.mk' (relation G n) x)

/-- Every element of a layer is the initial form of a representative in that central term.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20, item 1.
-/
theorem mk_surjective (n : ℕ) : Function.Surjective (mk G n) :=
  Additive.ofMul.surjective.comp (QuotientGroup.mk'_surjective _)

/-- An initial form vanishes precisely when its representative lies in the next central term.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20, item 1.
-/
@[simp]
theorem mk_eq_zero (n : ℕ) (x : term G n) :
    mk G n x = 0 ↔ (x : G) ∈ (⊤ : Subgroup G).lowerCentralSeries n :=
  QuotientGroup.eq_one_iff x

/-- Multiplication of representatives becomes addition in the layer.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20, item 1.
-/
@[simp]
theorem mk_mul (n : ℕ) (x y : term G n) : mk G n (x * y) = mk G n x + mk G n y :=
  rfl

/-- The artificial degree zero is zero, preserving the paper's positive grading.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, positive-degree direct sum.
-/
instance layerZeroSubsingleton : Subsingleton (Layer G 0) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G 0 x
  exact (mk_eq_zero G 0 x).mpr (Subgroup.mem_top _)

/-- Every layer has exponent dividing three when the group does.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, lines 498–500.
-/
theorem three_nsmul_eq_zero (hG : HasExponentThree G) (n : ℕ) (x : Layer G n) :
    3 • x = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  change (QuotientGroup.mk' (relation G n) x) ^ 3 = 1
  rw [← map_pow]
  have hx : x ^ 3 = 1 := Subtype.ext (hG x)
  rw [hx, map_one]

/-- The canonical vector-space structure on an exponent-three degree quotient.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, underlying degree quotients and direct sum.
-/
instance layerModule [Fact (HasExponentThree G)] (n : ℕ) : Module (ZMod 3) (Layer G n) :=
  AddCommGroup.zmodModule (three_nsmul_eq_zero G Fact.out n)

variable {G} {H K : Type*} [Group H] [Group K]

/-- A homomorphism maps each lower central term into the corresponding target term.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
theorem map_lowerCentralSeries_le (f : G →* H) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f ≤
      (⊤ : Subgroup H).lowerCentralSeries n := by
  rw [Subgroup.map_lowerCentralSeries]
  exact Subgroup.lowerCentralSeries_mono n le_top

/-- The restriction of a homomorphism to the paper's `n`-th lower central term.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
def termMap (f : G →* H) (n : ℕ) : term G n →* term H n :=
  (f.comp (term G n).subtype).codRestrict _ fun x =>
    map_lowerCentralSeries_le f (n - 1) (Subgroup.mem_map_of_mem _ x.property)

/-- The restricted homomorphism acts on the same underlying element.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem termMap_coe (f : G →* H) (n : ℕ) (x : term G n) :
    (termMap f n x : H) = f x := rfl

/-- A homomorphism respects the relations defining each degree quotient.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
theorem relation_le_comap (f : G →* H) (n : ℕ) :
    relation G n ≤ (relation H n).comap (termMap f n) := by
  intro x hx
  exact map_lowerCentralSeries_le f n (Subgroup.mem_map_of_mem _ hx)

/-- The induced additive map on a degree quotient, without any exponent assumption.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
def mapAdd (f : G →* H) (n : ℕ) : Layer G n →+ Layer H n :=
  (QuotientGroup.map (relation G n) (relation H n) (termMap f n)
    (relation_le_comap f n)).toAdditive

/-- The induced map sends the initial form of `x` to that of `f x`.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapAdd_mk (f : G →* H) (n : ℕ) (x : term G n) :
    mapAdd f n (mk G n x) = mk H n (termMap f n x) := rfl

/-- Inducing a map on a layer preserves identity maps.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapAdd_id (n : ℕ) : mapAdd (MonoidHom.id G) n = AddMonoidHom.id (Layer G n) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  rfl

/-- The trivial group homomorphism induces the zero map on every graded quotient. -/
@[simp]
theorem mapAdd_one (n : ℕ) : mapAdd (1 : G →* H) n = 0 := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  rfl

/-- Inducing a map on a layer preserves composition.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapAdd_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    mapAdd (g.comp f) n = (mapAdd g n).comp (mapAdd f n) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  rfl

/-- A degree map is injective exactly when representatives mapping into the next central term
already lie in the next source central term.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem mapAdd_injective_iff (f : G →* H) (n : ℕ) :
    Function.Injective (mapAdd f n) ↔
      ∀ x : term G n, f x ∈ (⊤ : Subgroup H).lowerCentralSeries n →
        (x : G) ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
  constructor
  · intro hf x hx
    apply (mk_eq_zero G n x).mp
    apply hf
    simpa only [mapAdd_mk, map_zero] using (mk_eq_zero H n (termMap f n x)).mpr hx
  · intro h
    rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := mk_surjective G n y
    rw [AddMonoidHom.mem_ker, mapAdd_mk, mk_eq_zero] at hy
    rw [AddSubgroup.mem_bot, mk_eq_zero]
    exact h x hy

/-- All layers in degree at least four vanish in an exponent-three group.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 1.
-/
theorem layer_subsingleton_of_four_le (hG : HasExponentThree G) {n : ℕ} (hn : 4 ≤ n) :
    Subsingleton (Layer G n) := by
  have hterm : term G n = ⊥ := by
    apply le_antisymm ?_ bot_le
    calc
      term G n ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
      _ = ⊥ := lowerCentralSeries_three_eq_bot hG
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective G n x
  apply (mk_eq_zero G n x).mpr
  have hx : (x : G) = 1 := by
    simpa only [hterm, Subgroup.mem_bot] using x.property
  rw [hx]
  exact Subgroup.one_mem _

/-- Degree four of the associated graded is zero.

Paper-ID: preliminaries.associated_graded_properties
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.19, item 1.
-/
theorem layer_four_subsingleton (hG : HasExponentThree G) : Subsingleton (Layer G 4) :=
  layer_subsingleton_of_four_le hG le_rfl

/-- Injectivity on all degree quotients detects injectivity of a homomorphism from an
exponent-three group.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem injective_of_mapAdd_injective (hG : HasExponentThree G) (f : G →* H)
    (hf : ∀ n, Function.Injective (mapAdd f n)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx1 : (f x) = 1 := hx
  have h₁ : x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    (mapAdd_injective_iff f 1).mp (hf 1) ⟨x, Subgroup.mem_top _⟩ (by
      change f x ∈ _
      rw [hx1]
      exact Subgroup.one_mem _)
  have h₂ : x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (mapAdd_injective_iff f 2).mp (hf 2) ⟨x, h₁⟩ (by
      change f x ∈ _
      rw [hx1]
      exact Subgroup.one_mem _)
  have h₃ : x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (mapAdd_injective_iff f 3).mp (hf 3) ⟨x, h₂⟩ (by
      change f x ∈ _
      rw [hx1]
      exact Subgroup.one_mem _)
  simpa only [lowerCentralSeries_three_eq_bot hG] using h₃

/-- For an injective homomorphism into an exponent-three group, injectivity on all layers
is equivalent to the two strictness equalities for inverse images of central terms.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem mapAdd_injective_iff_comap (hH : HasExponentThree H) (f : G →* H)
    (hf : Function.Injective f) :
    (∀ n, Function.Injective (mapAdd f n)) ↔
      ((⊤ : Subgroup G).lowerCentralSeries 1 =
        ((⊤ : Subgroup H).lowerCentralSeries 1).comap f ∧
      (⊤ : Subgroup G).lowerCentralSeries 2 =
        ((⊤ : Subgroup H).lowerCentralSeries 2).comap f) := by
  constructor
  · intro hi
    have h₁ : (⊤ : Subgroup G).lowerCentralSeries 1 =
        ((⊤ : Subgroup H).lowerCentralSeries 1).comap f := by
      apply le_antisymm
      · exact (Subgroup.map_le_iff_le_comap).mp (map_lowerCentralSeries_le f 1)
      · intro x hx
        exact (mapAdd_injective_iff f 1).mp (hi 1) ⟨x, Subgroup.mem_top _⟩ hx
    refine ⟨h₁, le_antisymm
      ((Subgroup.map_le_iff_le_comap).mp (map_lowerCentralSeries_le f 2)) ?_⟩
    intro x hx
    have hx₁ : x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
      rw [h₁]
      exact (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 1 ≤ 2) hx
    exact (mapAdd_injective_iff f 2).mp (hi 2) ⟨x, hx₁⟩ hx
  · rintro ⟨h₁, h₂⟩ n
    apply (mapAdd_injective_iff f n).mpr
    intro x hx
    rcases n with _ | _ | _ | n
    · exact Subgroup.mem_top _
    · exact h₁ ▸ hx
    · exact h₂ ▸ hx
    · have hfx : f x = 1 := by
        have hbot := (⊤ : Subgroup H).lowerCentralSeries_antitone
          (by omega : 3 ≤ n + 3) hx
        simpa only [lowerCentralSeries_three_eq_bot hH, Subgroup.mem_bot] using hbot
      have hxone : (x : G) = 1 := hf (hfx.trans f.map_one.symm)
      rw [hxone]
      exact Subgroup.one_mem _


/-- Initial forms of elements of the intersection with an ambient central term.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
def subgroupMk (S : Subgroup G) (n : ℕ) : ↥(S ⊓ term G n) →* MulLayer G n :=
  (QuotientGroup.mk' (relation G n)).comp (Subgroup.inclusion inf_le_right)

/-- The kernel consists of elements of `S ∩ γₙ(G)` that lie in `γₙ₊₁(G)`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
theorem subgroupMk_ker (S : Subgroup G) (n : ℕ) :
    (subgroupMk S n).ker =
      ((⊤ : Subgroup G).lowerCentralSeries n).comap (S ⊓ term G n).subtype := by
  ext x
  exact QuotientGroup.eq_one_iff (Subgroup.inclusion inf_le_right x)

/-- The multiplicative quotient `(S ∩ γₙ(G)) / (S ∩ γₙ₊₁(G))`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
abbrev SubgroupMulLayer (S : Subgroup G) (n : ℕ) :=
  ↥(S ⊓ term G n) ⧸ (subgroupMk S n).ker

/-- The induced-filtration quotient of a subgroup is commutative.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
instance subgroupMulLayerCommGroup (S : Subgroup G) (n : ℕ) :
    CommGroup (SubgroupMulLayer S n) where
  __ := QuotientGroup.Quotient.group _
  mul_comm := by
    let : IsMulCommutative (SubgroupMulLayer S n) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (Abelianization.commutator_subset_ker (subgroupMk S n))
    exact mul_comm'

/-- The quotient of the filtration on `S` induced by the ambient lower central series.
This uses intersections with ambient terms, rather than the intrinsic lower central series of `S`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
abbrev SubgroupLayer (S : Subgroup G) (n : ℕ) := Additive (SubgroupMulLayer S n)

/-- The canonical vector-space structure on the induced-filtration quotient.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
instance subgroupLayerModule [Fact (HasExponentThree G)] (S : Subgroup G) (n : ℕ) :
    Module (ZMod 3) (SubgroupLayer S n) := AddCommGroup.zmodModule <| by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (subgroupMk S n).ker y.toMul
  change y.toMul ^ 3 = 1
  rw [← hx, ← map_pow]
  have hG : HasExponentThree G := Fact.out
  have hx3 : x ^ 3 = 1 := Subtype.ext (hG x)
  rw [hx3, map_one]

section ExponentThree

variable [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]
  [Fact (HasExponentThree K)]


/-- The subspace of degree `n` consisting of initial forms of elements of `S`.
This is the paper's ambient graded image `grₙᴳ(S)`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
def subgroupImage (S : Subgroup G) (n : ℕ) : Submodule (ZMod 3) (Layer G n) :=
  AddSubgroup.toZModSubmodule 3 (subgroupMk S n).range.toAddSubgroup

/-- Membership in the ambient graded image is given by a representative in `S ∩ γₙ(G)`.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
theorem mem_subgroupImage (S : Subgroup G) (n : ℕ) (x : Layer G n) :
    x ∈ subgroupImage S n ↔ ∃ a : term G n, (a : G) ∈ S ∧ mk G n a = x := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, a.property.2⟩, a.property.1, congrArg Additive.ofMul ha⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, ha, a.property⟩, congrArg Additive.toMul h⟩

/-- The canonical linear isomorphism between the induced-filtration quotient of a subgroup
and its image in the ambient degree quotient.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
noncomputable def subgroupLayerEquiv (S : Subgroup G) (n : ℕ) :
    SubgroupLayer S n ≃ₗ[ZMod 3] subgroupImage S n := by
  let e : Additive (subgroupMk S n).range ≃+ subgroupImage S n :=
    { toFun := fun x => ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
      invFun := fun x => Additive.ofMul ⟨x.val.toMul, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let e' := (QuotientGroup.quotientKerEquivRange (subgroupMk S n)).toAdditive.trans e
  exact { e' with map_smul' := ZMod.map_smul e' }

/-- The canonical isomorphism sends the class of a subgroup element to its ambient initial form.

Paper-ID: preliminaries.graded_image
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.20.
-/
@[simp]
theorem subgroupLayerEquiv_mk (S : Subgroup G) (n : ℕ) (a : ↥(S ⊓ term G n)) :
    (subgroupLayerEquiv S n
      (Additive.ofMul (a : SubgroupMulLayer S n)) : Layer G n) =
      mk G n ⟨a, a.property.2⟩ := rfl

/-- The induced map on a degree quotient as an `𝔽₃`-linear map.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
def mapLayer (f : G →* H) (n : ℕ) : Layer G n →ₗ[ZMod 3] Layer H n :=
  (mapAdd f n).toZModLinearMap 3

/-- The induced linear map has the representative formula prescribed in the paper.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapLayer_mk (f : G →* H) (n : ℕ) (x : term G n) :
    mapLayer f n (mk G n x) = mk H n (termMap f n x) := rfl

/-- Degreewise linear maps preserve identities.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapLayer_id (n : ℕ) : mapLayer (MonoidHom.id G) n = LinearMap.id := by
  ext x
  exact DFunLike.congr_fun (mapAdd_id n) x

/-- The trivial group homomorphism induces the zero linear map on every layer. -/
@[simp]
theorem mapLayer_one (n : ℕ) : mapLayer (1 : G →* H) n = 0 := by
  ext x
  exact DFunLike.congr_fun (mapAdd_one n) x

/-- Degreewise linear maps preserve composition.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem mapLayer_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    mapLayer (g.comp f) n = (mapLayer g n).comp (mapLayer f n) := by
  ext x
  exact DFunLike.congr_fun (mapAdd_comp f g n) x

variable (G)

/-- The direct sum of the degree quotients, with its standard `𝔽₃`-module structure.
The Lie bracket is not part of this definition.

Paper-ID: preliminaries.associated_graded
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.18, underlying degree quotients and direct sum.
-/
abbrev GradedModule := ⨁ n : ℕ, Layer G n

variable {G}

/-- The direct sum of the induced linear maps on all degrees.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
def map (f : G →* H) : GradedModule G →ₗ[ZMod 3] GradedModule H :=
  DirectSum.lmap (mapLayer f)

/-- The induced graded linear map acts on each homogeneous component by the quotient map.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem map_lof (f : G →* H) (n : ℕ) (x : Layer G n) :
    map f (DirectSum.lof (ZMod 3) ℕ (Layer G) n x) =
      DirectSum.lof (ZMod 3) ℕ (Layer H) n (mapLayer f n x) :=
  DirectSum.lmap_lof _ _ _

/-- The induced graded linear map acts degreewise.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem map_apply (f : G →* H) (x : GradedModule G) (n : ℕ) :
    map f x n = mapLayer f n (x n) := rfl

/-- The induced graded linear map preserves identity maps.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem map_id : map (MonoidHom.id G) = LinearMap.id := by
  ext x n
  simp

/-- The induced graded linear map preserves composition.

Paper-ID: preliminaries.associated_graded_map
TeX: T3_modelcompanion_v9.tex, v9 Definition 2.22, underlying linear maps.
-/
@[simp]
theorem map_comp (f : G →* H) (g : H →* K) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x n
  simp

/-- Injectivity of the direct-sum map is equivalent to injectivity on every layer.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem map_injective_iff (f : G →* H) :
    Function.Injective (map f) ↔ ∀ n, Function.Injective (mapLayer f n) := by
  constructor
  · intro hf n x y hxy
    have h : DirectSum.lof (ZMod 3) ℕ (Layer G) n x =
        DirectSum.lof (ZMod 3) ℕ (Layer G) n y := hf (by rw [map_lof, map_lof, hxy])
    simpa only [DirectSum.lof_apply] using congrArg (fun z : GradedModule G => z n) h
  · intro hf x y hxy
    ext n
    exact hf n (congrArg (fun z : GradedModule H => z n) hxy)

/-- Injectivity of the underlying graded map implies injectivity of the group homomorphism.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem injective_of_map_injective (f : G →* H) (hf : Function.Injective (map f)) :
    Function.Injective f :=
  injective_of_mapAdd_injective Fact.out f ((map_injective_iff f).mp hf)

/-- An embedding induces an injective graded linear map exactly when its range is strict
for the lower central series.

Paper-ID: preliminaries.graded_injectivity_strictness
TeX: T3_modelcompanion_v9.tex, v9 Proposition 2.24, `proposition:gr(f) and LCS`.
-/
theorem map_injective_iff_isStrict (f : G →* H) (hf : Function.Injective f) :
    Function.Injective (map f) ↔ IsStrict f.range := by
  rw [map_injective_iff, isStrict_range_iff_comap f hf]
  exact mapAdd_injective_iff_comap Fact.out f hf

end ExponentThree

end T3.AssociatedGraded
