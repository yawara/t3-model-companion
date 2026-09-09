/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.FiniteSupport

/-!
# Finitely supported normal words in arbitrary rank

The three coefficient families are finitely supported functions over `ZMod 3`.
Their normal word is the ascending product of generator powers followed by powers of
increasing commutators and triple commutators, as displayed in the paper. The readout and
cancellation proofs reuse the finite-rank normal-form argument.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/

@[expose] public section

open scoped commutatorElement

namespace T3.Free

variable {I : Type*} [LinearOrder I]

/-- The scalar multiple of a coordinate delta realised by a power of a witness. -/
private theorem val_nsmul_single {α : Type*} [DecidableEq α] (p : α) (m : ZMod 3) :
    m.val • Pi.single p (1 : ZMod 3) = (Pi.single p m : α → ZMod 3) := by
  funext q
  rcases eq_or_ne q p with rfl | hqp
  · simp [ZMod.natCast_rightInverse m]
  · simp [Pi.single_eq_of_ne hqp]

private theorem readout_word {α G : Type*} [DecidableEq α] [Group G]
    (f : G →* Multiplicative (α → ZMod 3)) (b : α → G)
    (hb : ∀ a, f (b a) = Multiplicative.ofAdd (Pi.single a (1 : ZMod 3)))
    {c : α →₀ ZMod 3} (l : List α) (hn : l.Nodup) (hl : l.toFinset = c.support) :
    f ((l.map fun a => b a ^ (c a).val).prod) = Multiplicative.ofAdd (c : α → ZMod 3) := by
  have hp : f ((l.map fun a => b a ^ (c a).val).prod) =
      Multiplicative.ofAdd ((l.map fun a => Pi.single a (c a)).sum) := by
    clear hn hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, map_pow, hb,
        ← ofAdd_nsmul, val_nsmul_single, ih, List.sum_cons, ofAdd_add]
  rw [hp]
  congr 1
  rw [← List.sum_toFinset _ hn, hl]
  ext a
  classical
  by_cases ha : a ∈ c.support
  · simp [Pi.single_apply, ha]
  · simp [Pi.single_apply, ha, Finsupp.notMem_support_iff.mp ha]

/-- The generator block, with generators multiplied in ascending order.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
noncomputable def generatorWordFinsupp (l : I →₀ ZMod 3) : Free I := by
  classical
  exact ((l.support.sort (· ≤ ·)).map fun i => of i ^ (l i).val).prod

/-- The commutator block of the normal word, viewed in the first readout kernel.
All factors have increasing indices and lie in the abelian derived subgroup, so the
choice of their enumeration has no mathematical effect.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
noncomputable def pairWordFinsupp (m : IncreasingPair I →₀ ZMod 3) :
    (genReadout (I := I)).ker := by
  classical
  exact (m.support.toList.map fun p =>
    (⟨⁅of p.first, of p.second⁆, commutator_mem_genReadout_ker _ _⟩ :
      (genReadout (I := I)).ker) ^ (m p).val).prod

/-- The triple commutator block, viewed in the second readout kernel.
Every factor has increasing indices and is central.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
noncomputable def tripleWordFinsupp (n : IncreasingTriple I →₀ ZMod 3) :
    (pairReadout (I := I)).ker := by
  classical
  exact (n.support.toList.map fun t =>
    (⟨⟨⁅⁅of t.first, of t.second⁆, of t.third⁆, commutator_mem_genReadout_ker _ _⟩,
      tripleCommutator_mem_pairReadout_ker _ _ _⟩ :
        (pairReadout (I := I)).ker) ^ (n t).val).prod

/-- The collected word from the paper: ascending generator powers, followed by increasing
commutator powers and increasing triple commutator powers. Exponents are the representatives
`0`, `1`, `2` of the specified elements of `ZMod 3`.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
noncomputable def normalWordFinsupp (l : I →₀ ZMod 3) (m : IncreasingPair I →₀ ZMod 3)
    (n : IncreasingTriple I →₀ ZMod 3) : Free I :=
  generatorWordFinsupp l * (pairWordFinsupp m : Free I) *
    ((tripleWordFinsupp n : (genReadout (I := I)).ker) : Free I)

/-- The degree-one readout recovers the generator exponents of the ascending block.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem genReadout_generatorWordFinsupp (l : I →₀ ZMod 3) :
    genReadout (generatorWordFinsupp l) = Multiplicative.ofAdd (l : I → ZMod 3) := by
  classical
  apply readout_word _ _ ?_ _ (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _)
  intro i
  rw [genReadout_apply, toLvdW_of]
  exact congrArg _ (funext fun j => by rw [LvdW.of_gen, Pi.single_apply])

/-- The degree-two readout recovers the commutator exponents of the second block.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem pairReadout_pairWordFinsupp (m : IncreasingPair I →₀ ZMod 3) :
    pairReadout (pairWordFinsupp m) =
      Multiplicative.ofAdd (m : IncreasingPair I → ZMod 3) := by
  classical
  apply readout_word _ _ ?_ _ (Finset.nodup_toList _) (Finset.toList_toFinset _)
  intro p
  rw [pairReadout_apply]
  refine congrArg _ (funext fun q => ?_)
  rw [map_commutatorElement, toLvdW_of, toLvdW_of,
    LvdW.commutator_of_pair_of_lt p.first_lt_second q.first_lt_second, Pi.single_apply]
  simp only [IncreasingPair.ext_iff]

/-- The degree-three readout recovers the triple commutator exponents of the final block.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem tripleReadout_tripleWordFinsupp (n : IncreasingTriple I →₀ ZMod 3) :
    tripleReadout (tripleWordFinsupp n) =
      Multiplicative.ofAdd (n : IncreasingTriple I → ZMod 3) := by
  classical
  apply readout_word _ _ ?_ _ (Finset.nodup_toList _) (Finset.toList_toFinset _)
  intro t
  rw [tripleReadout_apply]
  refine congrArg _ (funext fun s => ?_)
  rw [map_commutatorElement, map_commutatorElement, toLvdW_of, toLvdW_of, toLvdW_of,
    LvdW.triple_commutator_of_triple_of_lt t.first_lt_second t.second_lt_third
      s.first_lt_second s.second_lt_third, Pi.single_apply]
  simp only [IncreasingTriple.ext_iff]

/-- The degree-one readout of the whole normal word gives its generator exponents.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem genReadout_normalWordFinsupp (l : I →₀ ZMod 3) (m : IncreasingPair I →₀ ZMod 3)
    (n : IncreasingTriple I →₀ ZMod 3) :
    genReadout (normalWordFinsupp l m n) = Multiplicative.ofAdd (l : I → ZMod 3) := by
  have hm : genReadout (pairWordFinsupp m : Free I) = 1 := (pairWordFinsupp m).property
  have hn : genReadout ((tripleWordFinsupp n : (genReadout (I := I)).ker) : Free I) = 1 :=
    (tripleWordFinsupp n).val.property
  rw [normalWordFinsupp, map_mul, map_mul, genReadout_generatorWordFinsupp, hm, hn,
    mul_one, mul_one]

/-- Equality of two ascending collected words forces equality of every exponent.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem normalWordFinsupp_injective : Function.Injective
    (fun c : (I →₀ ZMod 3) × (IncreasingPair I →₀ ZMod 3) × (IncreasingTriple I →₀ ZMod 3) =>
      normalWordFinsupp c.1 c.2.1 c.2.2) := by
  rintro ⟨l, m, n⟩ ⟨l', m', n'⟩ h
  have hl : l = l' := by
    have hgen := congrArg genReadout h
    rw [genReadout_normalWordFinsupp, genReadout_normalWordFinsupp] at hgen
    exact DFunLike.coe_injective (congrArg Multiplicative.toAdd hgen)
  subst l'
  have hp : pairWordFinsupp m * (tripleWordFinsupp n : (genReadout (I := I)).ker) =
      pairWordFinsupp m' * (tripleWordFinsupp n' : (genReadout (I := I)).ker) := by
    apply Subtype.ext
    apply mul_left_cancel (a := generatorWordFinsupp l)
    simpa only [normalWordFinsupp, mul_assoc, Subgroup.coe_mul] using h
  have hm : m = m' := by
    have hn : pairReadout (tripleWordFinsupp n : (genReadout (I := I)).ker) = 1 :=
      (tripleWordFinsupp n).property
    have hn' : pairReadout (tripleWordFinsupp n' : (genReadout (I := I)).ker) = 1 :=
      (tripleWordFinsupp n').property
    have hpair := congrArg pairReadout hp
    rw [map_mul, map_mul, pairReadout_pairWordFinsupp, pairReadout_pairWordFinsupp, hn, hn',
      mul_one, mul_one] at hpair
    exact DFunLike.coe_injective (congrArg Multiplicative.toAdd hpair)
  subst m'
  have ht : tripleWordFinsupp n = tripleWordFinsupp n' := Subtype.ext (mul_left_cancel hp)
  have hn := congrArg tripleReadout ht
  rw [tripleReadout_tripleWordFinsupp, tripleReadout_tripleWordFinsupp] at hn
  have hn' : n = n' := DFunLike.coe_injective (congrArg Multiplicative.toAdd hn)
  subst n'
  rfl

/-- The final readout is injective without a finite-rank assumption.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem tripleReadout_injective : Function.Injective (tripleReadout (I := I)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  apply eq_one_of_toLvdW_coords
  · intro i
    have h := x.val.property
    rw [MonoidHom.mem_ker, genReadout_apply, ofAdd_eq_one] at h
    exact congrFun h i
  · intro p
    have h := x.property
    rw [MonoidHom.mem_ker, pairReadout_apply, ofAdd_eq_one] at h
    exact congrFun h p
  · intro t
    rw [MonoidHom.mem_ker, tripleReadout_apply, ofAdd_eq_one] at hx
    exact congrFun hx t

/-- Every element in arbitrary rank is represented by a finitely supported normal word.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem normalWordFinsupp_surjective : Function.Surjective
    (fun c : (I →₀ ZMod 3) × (IncreasingPair I →₀ ZMod 3) × (IncreasingTriple I →₀ ZMod 3) =>
      normalWordFinsupp c.1 c.2.1 c.2.2) := by
  intro g
  let l : I →₀ ZMod 3 := Finsupp.ofSupportFinite (toLvdW g).gen (finite_support_gen g)
  have hl : genReadout (generatorWordFinsupp l) = genReadout g :=
    genReadout_generatorWordFinsupp l
  let x : (genReadout (I := I)).ker := ⟨(generatorWordFinsupp l)⁻¹ * g, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]⟩
  let m : IncreasingPair I →₀ ZMod 3 := Finsupp.ofSupportFinite
    (fun p => (toLvdW x.val).pair p.first p.second) (finite_support_pair x.val)
  have hm : pairReadout (pairWordFinsupp m) = pairReadout x :=
    pairReadout_pairWordFinsupp m
  let y : (pairReadout (I := I)).ker := ⟨(pairWordFinsupp m)⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm, inv_mul_cancel]⟩
  let n : IncreasingTriple I →₀ ZMod 3 := Finsupp.ofSupportFinite
    (fun t => (toLvdW y.val.val).triple t.first t.second t.third)
    (finite_support_triple y.val.val)
  have hn : tripleReadout (tripleWordFinsupp n) = tripleReadout y :=
    tripleReadout_tripleWordFinsupp n
  have hy : tripleWordFinsupp n = y := tripleReadout_injective hn
  refine ⟨(l, m, n), ?_⟩
  change normalWordFinsupp l m n = g
  rw [normalWordFinsupp, hy]
  change generatorWordFinsupp l * (pairWordFinsupp m : Free I) *
    ((pairWordFinsupp m : Free I)⁻¹ * ((generatorWordFinsupp l)⁻¹ * g)) = g
  group

/-- The finitely supported coefficient families parameterize the free group in every rank.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem normalWordFinsupp_bijective : Function.Bijective
    (fun c : (I →₀ ZMod 3) × (IncreasingPair I →₀ ZMod 3) × (IncreasingTriple I →₀ ZMod 3) =>
      normalWordFinsupp c.1 c.2.1 c.2.2) :=
  ⟨normalWordFinsupp_injective, normalWordFinsupp_surjective⟩

/-- Every element has the unique finitely supported expression displayed in the paper.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v4.tex, `remark:infinite dim`, v4 Remark 2.28.
-/
theorem existsUnique_normalWordFinsupp (g : Free I) :
    ∃! c : (I →₀ ZMod 3) × (IncreasingPair I →₀ ZMod 3) × (IncreasingTriple I →₀ ZMod 3),
      normalWordFinsupp c.1 c.2.1 c.2.2 = g := by
  obtain ⟨c, hc⟩ := normalWordFinsupp_surjective g
  exact ⟨c, hc, fun d hd => normalWordFinsupp_injective (hd.trans hc.symm)⟩

end T3.Free
