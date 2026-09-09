/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import T3.GroupTheory.Free.Basic
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Coproducts of exponent-three groups

The coproduct is the ordinary free product modulo cubes, exactly as in the paper.
The power quotient API is reused from the exponent-groups repository. The construction allows
arbitrary factors; the retraction to a factor assumes its exponent divides three.
No finite presentation is chosen.

Paper-ID: preliminaries.notation, preliminaries.free_coproduct,
preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1(8), Fact 2.16, and Lemma 2.17.
-/

@[expose] public section

namespace T3

/-- The ordinary free product modulo the normal closure of cubes.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1, item 8.
-/
abbrev Coproduct (G H : Type*) [Group G] [Group H] :=
  PowerQuotient (Monoid.Coprod G H) 3

namespace Coproduct

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- The left factor map into the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17.
-/
def inl : G →* Coproduct G H := powerQuotientMk.comp Monoid.Coprod.inl

/-- The right factor map into the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17.
-/
def inr : H →* Coproduct G H := powerQuotientMk.comp Monoid.Coprod.inr

/-- The coproduct satisfies the exponent-three law.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1, item 8.
-/
theorem pow_three (g : Coproduct G H) : g ^ 3 = 1 := powerQuotient_hasExponent g

/-- Every coproduct in the exponent-three variety satisfies the defining law. -/
instance hasExponentThree : Fact (HasExponentThree (Coproduct G H)) := ⟨pow_three⟩

/-- A pair of homomorphisms to an exponent-three group descends from the free product.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1, item 8.
-/
def lift (hK : HasExponentThree K) (f : G →* K) (g : H →* K) :
    Coproduct G H →* K :=
  powerQuotientLift (Monoid.Coprod.lift f g) fun _ => hK _

@[simp]
theorem lift_inl (hK : HasExponentThree K) (f : G →* K) (g : H →* K) (x : G) :
    lift hK f g (inl x) = f x := rfl

@[simp]
theorem lift_inr (hK : HasExponentThree K) (f : G →* K) (g : H →* K) (x : H) :
    lift hK f g (inr x) = g x := rfl

/-- Homomorphisms out of the coproduct are determined by their restrictions to both factors.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v4.tex, v4 Notation 2.1, item 8.
-/
theorem hom_ext {f g : Coproduct G H →* K}
    (hl : ∀ x, f (inl x) = g (inl x)) (hr : ∀ x, f (inr x) = g (inr x)) : f = g := by
  have heq : f.comp powerQuotientMk = g.comp powerQuotientMk :=
    Monoid.Coprod.hom_ext (MonoidHom.ext hl) (MonoidHom.ext hr)
  refine MonoidHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := powerQuotientMk_surjective x
  exact DFunLike.congr_fun heq x

/-- The retraction to the left factor used in the paper's injectivity proof.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17 and its proof.
-/
def fst (hG : HasExponentThree G) : Coproduct G H →* G := lift hG (.id G) 1

/-- The retraction to the right factor.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17 and its proof.
-/
def snd (hH : HasExponentThree H) : Coproduct G H →* H := lift hH 1 (.id H)

@[simp]
theorem fst_inl (hG : HasExponentThree G) (x : G) : fst hG (inl (H := H) x) = x := rfl

@[simp]
theorem snd_inr (hH : HasExponentThree H) (x : H) : snd hH (inr (G := G) x) = x := rfl

@[simp]
theorem fst_inr (hG : HasExponentThree G) (x : H) : fst hG (inr x) = 1 := rfl

@[simp]
theorem snd_inl (hH : HasExponentThree H) (x : G) : snd hH (inl x) = 1 := rfl

@[simp]
theorem fst_comp_inl (hG : HasExponentThree G) :
    (fst (H := H) hG).comp inl = MonoidHom.id G := rfl

@[simp]
theorem fst_comp_inr (hG : HasExponentThree G) : (fst hG).comp (inr (H := H)) = 1 := rfl

@[simp]
theorem snd_comp_inl (hH : HasExponentThree H) : (snd hH).comp (inl (G := G)) = 1 := rfl

@[simp]
theorem snd_comp_inr (hH : HasExponentThree H) :
    (snd (G := G) hH).comp inr = MonoidHom.id H := rfl

variable {G' H' G'' H'' : Type*} [Group G'] [Group H'] [Group G''] [Group H'']

/-- The homomorphism of coproducts induced by homomorphisms of both factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v4.tex, `proposition:gr of free product`, naturality of the factor maps.
-/
def map (f : G →* G') (g : H →* H') : Coproduct G H →* Coproduct G' H' :=
  lift pow_three (inl.comp f) (inr.comp g)

@[simp]
theorem map_inl (f : G →* G') (g : H →* H') (x : G) : map f g (inl x) = inl (f x) := rfl

@[simp]
theorem map_inr (f : G →* G') (g : H →* H') (x : H) : map f g (inr x) = inr (g x) := rfl

@[simp]
theorem map_comp_inl (f : G →* G') (g : H →* H') :
    (map f g).comp inl = inl.comp f := rfl

@[simp]
theorem map_comp_inr (f : G →* G') (g : H →* H') :
    (map f g).comp inr = inr.comp g := rfl

@[simp]
theorem map_id : map (MonoidHom.id G) (MonoidHom.id H) = MonoidHom.id (Coproduct G H) :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

@[simp]
theorem map_comp (f : G →* G') (g : H →* H') (f' : G' →* G'') (g' : H' →* H'') :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

/-- The left factor of exponent three embeds in the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17.
-/
theorem inl_injective (hG : HasExponentThree G) :
    Function.Injective (inl : G → Coproduct G H) :=
  (show Function.LeftInverse (fst hG) inl from fst_inl hG).injective

/-- The right factor of exponent three embeds in the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v4.tex, v4 Lemma 2.17.
-/
theorem inr_injective (hH : HasExponentThree H) :
    Function.Injective (inr : H → Coproduct G H) :=
  (show Function.LeftInverse (snd hH) inr from snd_inr hH).injective

end Coproduct

namespace Free

variable {X Y : Type*}

/-- The map from the free group on a disjoint union to the coproduct of its free factors.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.16.
-/
def sumToCoproduct : Free (X ⊕ Y) →* Coproduct (Free X) (Free Y) :=
  lift Coproduct.pow_three (Sum.elim (fun x => Coproduct.inl (of x))
    (fun y => Coproduct.inr (of y)))

@[simp]
theorem sumToCoproduct_of_inl (x : X) :
    sumToCoproduct (of (Sum.inl x : X ⊕ Y)) = Coproduct.inl (of x) := lift_of _ _ _

@[simp]
theorem sumToCoproduct_of_inr (y : Y) :
    sumToCoproduct (of (Sum.inr y : X ⊕ Y)) = Coproduct.inr (of y) := lift_of _ _ _

/-- The inverse map induced by the two inclusions of generating sets.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.16.
-/
def coproductToSum : Coproduct (Free X) (Free Y) →* Free (X ⊕ Y) :=
  Coproduct.lift pow_three (map Sum.inl) (map Sum.inr)

/-- The free exponent-three group on a disjoint union is the coproduct of the free factors.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v4.tex, v4 Fact 2.16.
-/
def sumEquivCoproduct : Free (X ⊕ Y) ≃* Coproduct (Free X) (Free Y) :=
  MonoidHom.toMulEquiv sumToCoproduct coproductToSum
    (hom_ext fun x => by cases x <;> simp [coproductToSum])
    (Coproduct.hom_ext
      (fun x => DFunLike.congr_fun
        (show sumToCoproduct.comp (map Sum.inl) = Coproduct.inl from
          hom_ext fun x => by simp) x)
      (fun y => DFunLike.congr_fun
        (show sumToCoproduct.comp (map Sum.inr) = Coproduct.inr from
          hom_ext fun y => by simp) y))

end Free

end T3
