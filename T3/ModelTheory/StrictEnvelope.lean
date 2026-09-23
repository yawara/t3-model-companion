/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Coproduct.CentralSeries
public import T3.GroupTheory.Coproduct.Generation
public import T3.GroupTheory.Coproduct.Strict
public import T3.GroupTheory.Roots.DerivedStrictification
public import T3.GroupTheory.Roots.LowerCentralStrictification
public import T3.ModelTheory.ExistentiallyClosedGroups

/-!
# Bounded strict envelopes in existentially closed exponent-three groups

The two simultaneous strictification steps are followed by adjoining a free factor on two
generators. The resulting finite group has coincident lower and upper central series. Its
embedding into an extension is transferred back to the existentially closed group, fixing
the whole original subgroup. The trivial subgroup is handled separately, so the bound also
holds at zero.

The numerical function `strictEnvelopeBound` is defined here, at the paper result supplying it.
Both the model-theoretic conclusion and the preceding algebraic extension construction
work in every universe.

Paper-ID: structure.strict_envelope, main.proposition_a
TeX: T3_modelcompanion_v8.tex, `proposition:bdd LCS`, v8 Proposition 4.13, and Proposition A.
-/

@[expose] public section

universe u

namespace T3

/-- The bound supplied by the paper's strict-envelope construction.

Paper-ID: structure.strict_envelope, main.proposition_a
TeX: T3_modelcompanion_v8.tex, `proposition:bdd LCS`, the function `f₀(n) = 15n²`.
-/
def strictEnvelopeBound (n : ℕ) : ℕ := 15 * n ^ 2

/-- The three generator counts fit the paper's quadratic bound for nontrivial input.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v8.tex, `proposition:bdd LCS`, lines 1333–1337.
-/
theorem three_stage_rank_le_strictEnvelopeBound {n : ℕ} (hn : 0 < n) :
    3 * n + 3 * (3 * n).choose 2 + 2 ≤ strictEnvelopeBound n := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.mul_div_le ((3 * n) * (3 * n - 1)) 2
  have hsub : 3 * n - 1 + 1 = 3 * n := Nat.sub_add_cancel (by omega)
  unfold strictEnvelopeBound
  nlinarith

namespace StrictEnvelope

variable {G : Type u} [Group G]

/-- The algebraic part of the envelope construction, before existentially closed transfer.
The finite group `A = D₂ ∐ F₂` embeds in an extension of `G` over the given subgroup.

Paper-ID: structure.strict_envelope
TeX: T3_modelcompanion_v8.tex, `proposition:bdd LCS`, lines 1309–1339.
-/
theorem exists_centralSeries_extension (hG : HasExponentThree G) (C : Subgroup G)
    [Group.FG C] [Nontrivial C] {n : ℕ} (hC : Group.rank C ≤ n) :
    ∃ (H : Type u) (hH : Group H),
      letI := hH
      HasExponentThree H ∧ ∃ f : G →* H, Function.Injective f ∧
        ∃ (A : Type u) (hA : Group A),
          letI := hA
          ∃ hfg : Group.FG A,
            letI := hfg
            Finite A ∧ CentralSeriesCoincide A ∧ Group.rank A ≤ strictEnvelopeBound n ∧
              ∃ r : A →* H, Function.Injective r ∧
                ∃ a : C →* A, r.comp a = f.comp C.subtype := by
  obtain ⟨H₁, hH₁, hpow₁, f₁, hf₁, D₁, hfg₁, hC₁, _, _, _, hrank₁, hstrict₁⟩ :=
    DerivedStrictification.exists_derived_strictification hG C hC
  let : Group H₁ := hH₁
  let : Group.FG D₁ := hfg₁
  have hfirst : (commutator H₁).comap D₁.subtype = commutator D₁ := by
    simpa only [Subgroup.top_lowerCentralSeries_one] using
      ((Subgroup.lowerCentralSeries_eq_inf_iff_comap D₁ 1).mp hstrict₁).symm
  obtain ⟨H₂, hH₂, hpow₂, f₂, hf₂, D₂, hfg₂, hC₂, _, _, _, hrank₂, hstrict₂⟩ :=
    LowerCentralStrictification.exists_strict_extension D₁ hpow₁ hfirst hrank₁
  let : Group H₂ := hH₂
  let : Group.FG D₂ := hfg₂
  let : Fact (HasExponentThree H₂) := ⟨hpow₂⟩
  let : Fact (HasExponentThree D₂) := ⟨fun d => Subtype.ext (hpow₂ d)⟩
  let c : C →* D₂ := ((f₂.comp f₁).comp C.subtype).codRestrict D₂ fun x =>
    hC₂ (Subgroup.mem_map_of_mem f₂ (hC₁ (Subgroup.mem_map_of_mem f₁ x.property)))
  have hc : Function.Injective c := by
    intro x y h
    exact Subtype.ext ((hf₂.comp hf₁) (congrArg Subtype.val h))
  let : Nontrivial D₂ := hc.nontrivial
  let A := Coproduct D₂ (Free (Fin 2))
  let H := Coproduct H₂ (Free (Fin 2))
  let r : A →* H := Coproduct.map D₂.subtype (MonoidHom.id _)
  let f : G →* H := Coproduct.inl.comp (f₂.comp f₁)
  let a : C →* A := Coproduct.inl.comp c
  have hr : Function.Injective r := Coproduct.map_injective_of_strict D₂ hstrict₂
  have hf : Function.Injective f := (Coproduct.inl_injective hpow₂).comp (hf₂.comp hf₁)
  have hA : CentralSeriesCoincide A := Coproduct.centralSeriesCoincide_freeTwo
  have hbound : Group.rank A ≤ strictEnvelopeBound n :=
    Coproduct.rank_freeTwo_le.trans ((Nat.add_le_add_right hrank₂ 2).trans
      (three_stage_rank_le_strictEnvelopeBound ((Group.rank_pos C).trans_le hC)))
  refine ⟨H, inferInstance, Coproduct.pow_three, f, hf, A, inferInstance, inferInstance,
    finite_of_fg_of_exponent_three Coproduct.pow_three, hA, hbound, r, hr, a, ?_⟩
  ext x
  rfl

end StrictEnvelope

open FirstOrder FirstOrder.Language FirstOrder.Group

/-- A finite subgroup of an existentially closed exponent-three group lies in a subgroup
with coincident central series, generated by at most `15n²` elements. Finite generation
is equivalent to finiteness here, by local finiteness.

The finite-diagram transfer fixes every element of `C`. The returned subgroup is therefore
an actual overgroup of `C` inside `M`, with its intrinsic central-series structure intact.

Paper-ID: structure.strict_envelope, main.proposition_a
TeX: T3_modelcompanion_v8.tex, `proposition:bdd LCS`, v8 Proposition 4.13, and Proposition A.
-/
theorem exists_strict_envelope {M : Type*} [Group M] [CompatibleGroup M]
    (hM : exponentThreeTheory.IsExistentiallyClosedAt M) (C : Subgroup M) [Group.FG C]
    {n : ℕ} (hC : Group.rank C ≤ n) :
    ∃ (D : Subgroup M) (hD : Group.FG D),
      letI := hD
      C ≤ D ∧ Group.rank D ≤ strictEnvelopeBound n ∧ CentralSeriesCoincide D ∧ IsStrict D := by
  classical
  have hpow : HasExponentThree M := exponentThreeTheory_model_iff.mp hM.2.1
  by_cases htriv : Subsingleton C
  · let : Subsingleton C := htriv
    have hcoincide : CentralSeriesCoincide C := fun _ _ => Subsingleton.elim _ _
    refine ⟨C, inferInstance, le_rfl, ?_, hcoincide,
      isStrict_of_centralSeriesCoincide hpow C hcoincide⟩
    rw [Group.rank_eq_zero]
    exact Nat.zero_le _
  · let : Nontrivial C := not_subsingleton_iff_nontrivial.mp htriv
    let : Finite C := finite_of_fg_of_exponent_three (fun c => Subtype.ext (hpow c))
    obtain ⟨H, hH, hpowH, f, hf, A, hA, hfgA, hfinA, hcoincide, hbound, r, hr, a, ha⟩ :=
      StrictEnvelope.exists_centralSeries_extension hpow C hC
    let : Group H := hH
    let : Group A := hA
    let : Group.FG A := hfgA
    let : Finite A := hfinA
    obtain ⟨g, hg, hga⟩ := ExistentiallyClosedGroups.exists_group_embedding hM hpowH f hf r hr
      a C.subtype (funext (DFunLike.congr_fun ha))
    have hCimage : C ≤ g.range := by
      intro x hx
      refine ⟨a ⟨x, hx⟩, ?_⟩
      exact congrFun hga ⟨x, hx⟩
    have hcoincideD : CentralSeriesCoincide g.range := hcoincide.mulEquiv (MonoidHom.ofInjective hg)
    exact ⟨g.range, inferInstance, hCimage, Group.rank_range_le.trans hbound, hcoincideD,
      isStrict_of_centralSeriesCoincide hpow g.range hcoincideD⟩

/-- There is one numerical function bounding strict envelopes in every existentially closed
model. It is the explicit function from Proposition 4.13 and is independent of the model,
the subgroup, and its chosen generating family.

Paper-ID: main.proposition_a
TeX: T3_modelcompanion_v8.tex, Proposition A, lines 780–782.
-/
theorem exists_bounded_strict_envelope :
    ∃ f₀ : ℕ → ℕ, ∀ (n : ℕ) (M : Type u) [Group M] [CompatibleGroup M],
      exponentThreeTheory.IsExistentiallyClosedAt M → ∀ (C : Subgroup M) [Group.FG C],
        Group.rank C ≤ n → ∃ (D : Subgroup M) (hD : Group.FG D),
          letI := hD
          C ≤ D ∧ Group.rank D ≤ f₀ n ∧ IsStrict D := by
  refine ⟨strictEnvelopeBound, ?_⟩
  intro n M _ _ hM C _ hC
  obtain ⟨D, hD, hCD, hbound, _, hstrict⟩ := exists_strict_envelope hM C hC
  exact ⟨D, hD, hCD, hbound, hstrict⟩

end T3
