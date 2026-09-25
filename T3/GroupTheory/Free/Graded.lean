/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.AssociatedGraded
public import T3.GroupTheory.Free.InfiniteNormalForm

/-!
# The actual graded quotients of a free exponent-three group

The readout kernels identify the first three lower central terms in arbitrary rank.
The resulting quotient maps identify the actual associated graded layers with finitely
supported coefficient spaces. Their comparison with exterior powers and preservation of
Lie brackets are separate steps.

The pure third-layer and readout-kernel arguments use finitely supported normal words.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/

@[expose] public section

open scoped commutatorElement

namespace T3

namespace LvdW

variable {I : Type*}

/-- The subgroup of exponent systems supported purely in degree three.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
def tripleLayer : Subgroup (LvdW I) where
  carrier := {x | (∀ i, x.gen i = 0) ∧ ∀ i j, x.pair i j = 0}
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro x y ⟨hxg, hxp⟩ ⟨hyg, hyp⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [mul_gen, hxg, hyg, add_zero]
    · rw [mul_pair, hxp, hyp, hyg]
      ring
  inv_mem' := by
    let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
    rintro x ⟨hxg, hxp⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [inv_gen, hxg, neg_zero]
    · rw [inv_pair, hxp, hxg]
      ring

/-- An exponent system is in the third layer precisely when its lower coordinates vanish.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem mem_tripleLayer {x : LvdW I} :
    x ∈ tripleLayer ↔ (∀ i, x.gen i = 0) ∧ ∀ i j, x.pair i j = 0 :=
  Iff.rfl

end LvdW

namespace Free

variable {I : Type*}

/-- `γ₃` of the free exponent-three group, as a subgroup.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
abbrev GammaThree : Subgroup (Free I) :=
  (⊤ : Subgroup (Free I)).lowerCentralSeries 2

/-- `γ₃` sits inside the derived subgroup.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem gammaThree_le_derived :
    GammaThree (I := I) ≤ commutator (Free I) :=
  (⊤ : Subgroup (Free I)).lowerCentralSeries_antitone (show 1 ≤ 2 by omega)

/-- A commutator against a derived element lands in `γ₃`.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem commutator_mem_gammaThree {k : Free I}
    (hk : k ∈ commutator (Free I)) (w : Free I) :
    ⁅k, w⁆ ∈ GammaThree (I := I) := by
  change ⁅k, w⁆ ∈ (⊤ : Subgroup (Free I)).lowerCentralSeries 2
  rw [show (2 : ℕ) = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one]
  exact Subgroup.commutator_mem_commutator hk (Subgroup.mem_top w)

variable [LinearOrder I]

/-- The derived subgroup dies in the degree-one readout.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem commutator_le_genReadout_ker :
    commutator (Free I) ≤ (genReadout (I := I)).ker := by
  rw [commutator_def]
  exact Subgroup.commutator_le.mpr fun p _ q _ => commutator_mem_genReadout_ker p q

/-- Elements of the derived subgroup have vanishing degree-one coordinates.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem toLvdW_gen_eq_zero_of_mem_commutator {g : Free I}
    (hg : g ∈ commutator (Free I)) : ∀ i, (toLvdW g).gen i = 0 := by
  have h := commutator_le_genReadout_ker hg
  rw [MonoidHom.mem_ker, genReadout_apply, ofAdd_eq_one] at h
  exact fun i => congrFun h i

/-- Elements of `γ₃` map into the pure degree-three layer of the model.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem toLvdW_mem_tripleLayer {g : Free I} (hg : g ∈ GammaThree (I := I)) :
    toLvdW g ∈ LvdW.tripleLayer (I := I) := by
  have hg' : g ∈ increasingTripleClosure (I := I) := by
    rw [← lowerCentralSeries_two_eq_increasingTripleClosure]
    exact hg
  have hle : increasingTripleClosure (I := I) ≤ (LvdW.tripleLayer (I := I)).comap toLvdW := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine ⟨fun i => ?_, fun i j => ?_⟩ <;>
      rw [increasingTripleCommutator, map_commutatorElement, map_commutatorElement,
        toLvdW_of, toLvdW_of, toLvdW_of]
    · exact LvdW.triple_commutator_gen _ _ _ _
    · exact LvdW.triple_commutator_pair _ _ _ _ _
  exact hle hg'


/-- Every finitely supported pair block belongs to the derived subgroup.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem pairWordFinsupp_mem_derived (m : IncreasingPair I →₀ ZMod 3) :
    (pairWordFinsupp m : Free I) ∈ Derived (I := I) := by
  classical
  change pairWordFinsupp m ∈ (Derived (I := I)).comap (genReadout (I := I)).ker.subtype
  unfold pairWordFinsupp
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  apply Subgroup.pow_mem
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Every finitely supported triple block belongs to the third lower central term.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem tripleWordFinsupp_mem_gammaThree (n : IncreasingTriple I →₀ ZMod 3) :
    ((tripleWordFinsupp n : (genReadout (I := I)).ker) : Free I) ∈ GammaThree (I := I) := by
  classical
  change tripleWordFinsupp n ∈ (GammaThree (I := I)).comap
    ((genReadout (I := I)).ker.subtype.comp (pairReadout (I := I)).ker.subtype)
  unfold tripleWordFinsupp
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  apply Subgroup.pow_mem
  exact commutator_mem_gammaThree
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _

/-- The degree-one readout kernel is exactly the derived subgroup in every rank.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem derived_eq_genReadout_ker :
    Derived (I := I) = (genReadout (I := I)).ker := by
  apply le_antisymm commutator_le_genReadout_ker
  intro g hg
  obtain ⟨⟨l, m, n⟩, hword⟩ := normalWordFinsupp_surjective g
  rw [MonoidHom.mem_ker, ← hword, genReadout_normalWordFinsupp, ofAdd_eq_one] at hg
  have hl : l = 0 := DFunLike.coe_injective hg
  rw [← hword]
  change normalWordFinsupp l m n ∈ Derived (I := I)
  rw [normalWordFinsupp, hl]
  simpa [generatorWordFinsupp] using (Derived (I := I)).mul_mem
    (pairWordFinsupp_mem_derived m)
    (gammaThree_le_derived (tripleWordFinsupp_mem_gammaThree n))

/-- Inside the degree-one kernel, the degree-two kernel is exactly the third central term.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem pairReadout_ker_eq_gammaThree :
    (pairReadout (I := I)).ker =
      (GammaThree (I := I)).comap (genReadout (I := I)).ker.subtype := by
  apply le_antisymm
  · intro x hx
    let y : (pairReadout (I := I)).ker := ⟨x, hx⟩
    let n : IncreasingTriple I →₀ ZMod 3 := Finsupp.ofSupportFinite
      (fun t => (toLvdW y.val.val).triple t.first t.second t.third)
      (finite_support_triple y.val.val)
    have hn : tripleReadout (tripleWordFinsupp n) = tripleReadout y :=
      tripleReadout_tripleWordFinsupp n
    have hy : tripleWordFinsupp n = y := tripleReadout_injective hn
    have hmem := tripleWordFinsupp_mem_gammaThree n
    rw [hy] at hmem
    exact hmem
  · intro x hx
    rw [MonoidHom.mem_ker, pairReadout_apply, ofAdd_eq_one]
    funext p
    exact (toLvdW_mem_tripleLayer hx).2 p.first p.second

/-- The derived subgroup mapped into the first readout kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
def derivedToGenKer : Derived (I := I) →* (genReadout (I := I)).ker :=
  Subgroup.inclusion commutator_le_genReadout_ker

/-- The third central term mapped into the first readout kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
def gammaThreeToGenKer : GammaThree (I := I) →* (genReadout (I := I)).ker :=
  Subgroup.inclusion (gammaThree_le_derived.trans commutator_le_genReadout_ker)

/-- The third central term mapped into the degree-two readout kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
def gammaThreeToPairKer : GammaThree (I := I) →* (pairReadout (I := I)).ker :=
  gammaThreeToGenKer.codRestrict _ fun x => by
    rw [pairReadout_ker_eq_gammaThree]
    exact x.property

/-- The degree-one readout with its actual finite support.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def genFinsuppReadout : Free I →* Multiplicative (I →₀ ZMod 3) where
  toFun g := Multiplicative.ofAdd <|
    Finsupp.ofSupportFinite (toLvdW g).gen (finite_support_gen g)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext i
    exact congrArg (fun z : Multiplicative (I → ZMod 3) => z.toAdd i)
      ((genReadout (I := I)).map_mul g h)

/-- The finitely supported readout has the same generator coordinates as the model.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem genFinsuppReadout_apply (g : Free I) (i : I) :
    (genFinsuppReadout g).toAdd i = (toLvdW g).gen i := rfl

/-- Recording finite support does not change the first readout kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem genFinsuppReadout_eq_one (g : Free I) :
    genFinsuppReadout g = 1 ↔ genReadout g = 1 :=
  Finsupp.coe_eq_zero.symm

/-- The finitely supported degree-one readout is surjective.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem genFinsuppReadout_surjective : Function.Surjective (genFinsuppReadout (I := I)) := by
  intro l
  refine ⟨generatorWordFinsupp l.toAdd, ?_⟩
  apply Multiplicative.toAdd.injective
  ext i
  exact congrFun (congrArg Multiplicative.toAdd (genReadout_generatorWordFinsupp l.toAdd)) i

/-- The degree-one coefficient kernel is precisely the derived subgroup.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem genFinsuppReadout_ker : (genFinsuppReadout (I := I)).ker = Derived (I := I) := by
  ext g
  rw [MonoidHom.mem_ker, genFinsuppReadout_eq_one, ← MonoidHom.mem_ker,
    ← derived_eq_genReadout_ker]

/-- The degree-two readout on the derived subgroup, with its actual finite support.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def pairFinsuppReadout :
    Derived (I := I) →* Multiplicative (IncreasingPair I →₀ ZMod 3) where
  toFun (g : Derived (I := I)) := Multiplicative.ofAdd <| Finsupp.ofSupportFinite
    (fun p => (toLvdW (g : Free I)).pair p.first p.second) (finite_support_pair (g : Free I))
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext p
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext p
    exact congrArg (fun z : Multiplicative (IncreasingPair I → ZMod 3) => z.toAdd p)
      (((pairReadout (I := I)).comp (derivedToGenKer (I := I))).map_mul g h)

/-- The degree-two readout gives the increasing pair coordinates of a representative.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem pairFinsuppReadout_apply (g : Derived (I := I)) (p : IncreasingPair I) :
    (pairFinsuppReadout g).toAdd p = (toLvdW (g : Free I)).pair p.first p.second := rfl

/-- Recording finite support does not change the second readout kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem pairFinsuppReadout_eq_one (g : Derived (I := I)) :
    pairFinsuppReadout g = 1 ↔ pairReadout (derivedToGenKer g) = 1 :=
  Finsupp.coe_eq_zero.symm

/-- Every finitely supported pair coefficient family is realized by a derived element.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem pairFinsuppReadout_surjective : Function.Surjective (pairFinsuppReadout (I := I)) := by
  intro m
  refine ⟨⟨pairWordFinsupp m.toAdd, pairWordFinsupp_mem_derived m.toAdd⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  ext p
  exact congrFun (congrArg Multiplicative.toAdd (pairReadout_pairWordFinsupp m.toAdd)) p

/-- The degree-two coefficient kernel is the third central term inside the derived subgroup.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem pairFinsuppReadout_ker :
    (pairFinsuppReadout (I := I)).ker = GammaThreeInDerived (I := I) := by
  ext g
  rw [MonoidHom.mem_ker, pairFinsuppReadout_eq_one, ← MonoidHom.mem_ker,
    pairReadout_ker_eq_gammaThree]
  rfl

/-- The degree-three readout on the third central term, with its actual finite support.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def tripleFinsuppReadout :
    GammaThree (I := I) →* Multiplicative (IncreasingTriple I →₀ ZMod 3) where
  toFun (g : GammaThree (I := I)) := Multiplicative.ofAdd <| Finsupp.ofSupportFinite
    (fun t => (toLvdW (g : Free I)).triple t.first t.second t.third)
    (finite_support_triple (g : Free I))
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext t
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext t
    exact congrArg (fun z : Multiplicative (IncreasingTriple I → ZMod 3) => z.toAdd t)
      (((tripleReadout (I := I)).comp (gammaThreeToPairKer (I := I))).map_mul g h)

/-- The degree-three readout gives the increasing triple coordinates of a representative.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem tripleFinsuppReadout_apply (g : GammaThree (I := I)) (t : IncreasingTriple I) :
    (tripleFinsuppReadout g).toAdd t =
      (toLvdW (g : Free I)).triple t.first t.second t.third := rfl

/-- Every finitely supported triple coefficient family is realized in the third central term.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem tripleFinsuppReadout_surjective :
    Function.Surjective (tripleFinsuppReadout (I := I)) := by
  intro n
  refine ⟨⟨(tripleWordFinsupp n.toAdd).val.val,
    tripleWordFinsupp_mem_gammaThree n.toAdd⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  ext t
  exact congrFun (congrArg Multiplicative.toAdd (tripleReadout_tripleWordFinsupp n.toAdd)) t

/-- The finitely supported third readout is injective.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem tripleFinsuppReadout_injective : Function.Injective (tripleFinsuppReadout (I := I)) := by
  intro g h hgh
  have hread : tripleReadout (gammaThreeToPairKer g) = tripleReadout (gammaThreeToPairKer h) := by
    apply Multiplicative.toAdd.injective
    funext t
    exact congrArg (fun z : Multiplicative (IncreasingTriple I →₀ ZMod 3) => z.toAdd t) hgh
  have hker := tripleReadout_injective hread
  exact Subtype.ext (congrArg (fun x : (pairReadout (I := I)).ker => x.val.val) hker)

/-- The third readout has trivial kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem tripleFinsuppReadout_ker : (tripleFinsuppReadout (I := I)).ker = ⊥ :=
  (tripleFinsuppReadout (I := I)).ker_eq_bot tripleFinsuppReadout_injective

omit [LinearOrder I] in
/-- The first isomorphism theorem, applied to an actual degree quotient and a surjective
coefficient readout with precisely the defining relation as its kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def layerEquivOfReadout {J : Type*} (n : ℕ)
    (f : AssociatedGraded.term (Free I) n →* Multiplicative (J →₀ ZMod 3))
    (hker : f.ker = AssociatedGraded.relation (Free I) n) (hsurj : Function.Surjective f) :
    AssociatedGraded.Layer (Free I) n ≃ₗ[ZMod 3] (J →₀ ZMod 3) := by
  let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  let a := e.toAdditiveLeft
  exact { a with map_smul' := ZMod.map_smul a }

omit [LinearOrder I] in
/-- The quotient isomorphism evaluates an initial form by its defining coefficient readout.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem layerEquivOfReadout_mk {J : Type*} (n : ℕ)
    (f : AssociatedGraded.term (Free I) n →* Multiplicative (J →₀ ZMod 3))
    (hker : f.ker = AssociatedGraded.relation (Free I) n) (hsurj : Function.Surjective f)
    (x : AssociatedGraded.term (Free I) n) :
    layerEquivOfReadout n f hker hsurj (AssociatedGraded.mk (Free I) n x) = (f x).toAdd := rfl

/-- The degree-one coefficient readout on the literal first central term.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def layerOneReadout :
    AssociatedGraded.term (Free I) 1 →* Multiplicative (I →₀ ZMod 3) :=
  genFinsuppReadout.comp (AssociatedGraded.term (Free I) 1).subtype

/-- The first coefficient readout has exactly the relation of the actual first layer as kernel.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem layerOneReadout_ker :
    (layerOneReadout (I := I)).ker = AssociatedGraded.relation (Free I) 1 := by
  rw [layerOneReadout, ← MonoidHom.comap_ker, genFinsuppReadout_ker]
  rfl

/-- The coefficient readout on the first central term is surjective.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem layerOneReadout_surjective : Function.Surjective (layerOneReadout (I := I)) := by
  intro l
  obtain ⟨g, hg⟩ := genFinsuppReadout_surjective l
  exact ⟨⟨g, Subgroup.mem_top _⟩, hg⟩

/-- The actual degree-one associated graded quotient is the space of finitely supported
generator coefficients, for an arbitrary ordered generating set.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def layerOneEquiv :
    AssociatedGraded.Layer (Free I) 1 ≃ₗ[ZMod 3] (I →₀ ZMod 3) :=
  layerEquivOfReadout 1 layerOneReadout layerOneReadout_ker layerOneReadout_surjective

/-- The degree-one equivalence evaluates an initial form by the generator coefficient readout.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem layerOneEquiv_mk (x : AssociatedGraded.term (Free I) 1) :
    layerOneEquiv (AssociatedGraded.mk (Free I) 1 x) =
      (genFinsuppReadout (x : Free I)).toAdd := rfl

/-- The actual degree-two associated graded quotient is the space of finitely supported
increasing-pair coefficients, without a finite-rank hypothesis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def layerTwoEquiv :
    AssociatedGraded.Layer (Free I) 2 ≃ₗ[ZMod 3] (IncreasingPair I →₀ ZMod 3) :=
  layerEquivOfReadout 2 pairFinsuppReadout pairFinsuppReadout_ker pairFinsuppReadout_surjective

/-- The degree-two equivalence evaluates an initial form by the pair coefficient readout.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem layerTwoEquiv_mk (x : AssociatedGraded.term (Free I) 2) :
    layerTwoEquiv (AssociatedGraded.mk (Free I) 2 x) = (pairFinsuppReadout x).toAdd := rfl

omit [LinearOrder I] in
/-- The relation of the third layer is trivial: exponent-three groups have class at most three.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem relation_three_eq_bot : AssociatedGraded.relation (Free I) 3 = ⊥ := by
  unfold AssociatedGraded.relation
  rw [lowerCentralSeries_three_eq_bot (pow_three (X := I)), MonoidHom.comap_bot]
  exact MonoidHom.ker_eq_bot _ Subtype.val_injective

/-- The actual degree-three associated graded quotient is the space of finitely supported
increasing-triple coefficients, without a finite-rank hypothesis.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
noncomputable def layerThreeEquiv :
    AssociatedGraded.Layer (Free I) 3 ≃ₗ[ZMod 3] (IncreasingTriple I →₀ ZMod 3) :=
  layerEquivOfReadout 3 tripleFinsuppReadout
    (tripleFinsuppReadout_ker.trans relation_three_eq_bot.symm) tripleFinsuppReadout_surjective

/-- The degree-three equivalence evaluates an initial form by the triple coefficient readout.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
@[simp]
theorem layerThreeEquiv_mk (x : AssociatedGraded.term (Free I) 3) :
    layerThreeEquiv (AssociatedGraded.mk (Free I) 3 x) = (tripleFinsuppReadout x).toAdd := rfl

/-- A free generator has the corresponding unit coordinate in the first layer.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem layerOneEquiv_of (i : I) :
    layerOneEquiv (AssociatedGraded.mk (Free I) 1 ⟨of i, Subgroup.mem_top _⟩) =
      Finsupp.single i 1 := by
  ext j
  rw [layerOneEquiv_mk, genFinsuppReadout_apply, toLvdW_of, LvdW.of_gen]
  simp [Finsupp.single_apply, eq_comm]

/-- An increasing generator commutator has its unit coordinate in the actual second layer.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem layerTwoEquiv_commutator (p : IncreasingPair I) :
    layerTwoEquiv (AssociatedGraded.mk (Free I) 2
      (derivedCommutator (of p.first) (of p.second))) = Finsupp.single p 1 := by
  ext q
  rw [layerTwoEquiv_mk (derivedCommutator (of p.first) (of p.second)),
    pairFinsuppReadout_apply]
  change (toLvdW ⁅of p.first, of p.second⁆).pair q.first q.second = _
  rw [map_commutatorElement, toLvdW_of, toLvdW_of,
    LvdW.commutator_of_pair_of_lt p.first_lt_second q.first_lt_second, Finsupp.single_apply]
  simp only [IncreasingPair.ext_iff, eq_comm]

/-- An increasing triple generator commutator has its unit coordinate in the actual third layer.

Paper-ID: preliminaries.free_graded_equiv, preliminaries.infinite_free_graded
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`,
v9 Proposition 2.29 and Remark 2.30, underlying degree quotients.
-/
theorem layerThreeEquiv_tripleCommutator (t : IncreasingTriple I) :
    layerThreeEquiv (AssociatedGraded.mk (Free I) 3
      ⟨⁅⁅of t.first, of t.second⁆, of t.third⁆,
        commutator_mem_gammaThree
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) _⟩) =
      Finsupp.single t 1 := by
  ext s
  rw [layerThreeEquiv_mk, tripleFinsuppReadout_apply]
  rw [map_commutatorElement, map_commutatorElement, toLvdW_of, toLvdW_of, toLvdW_of,
    LvdW.triple_commutator_of_triple_of_lt t.first_lt_second t.second_lt_third
      s.first_lt_second s.second_lt_third, Finsupp.single_apply]
  simp only [IncreasingTriple.ext_iff, eq_comm]

end Free

end T3
