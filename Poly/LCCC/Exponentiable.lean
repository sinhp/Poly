/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Awodey, Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Tactic.ApplyFun


/-!
# Expontentiable morphisms in a category


## Notation

We provide the following notations:

given a morphism `f : J ⟶ I` in a category `C`,
* `Σ_f` is for the object part of the functor `Over.map f : Over I ⥤ Over J`. As such, for an object
`X : Over J`, we have `Σ_f X : Over I`
* `Δ_f` is for the object part of the functor `baseChange f : Over J ⥤ Over I`. As such, for an object
`X : Over I`, we have `Δ_f X : Over J`
* `Π_f` is for object part of the functor `pushforward f : Over J ⥤ Over I`. As such, for an object
`X : Over J`, we have `Π_f X : Over I`

-/

noncomputable section

open CategoryTheory Category MonoidalCategory Limits Functor Adjunction IsConnected Over


namespace OverMapBaseChange

variable {C : Type*} [Category C] [HasFiniteWidePullbacks C]

attribute [local instance] monoidalOfHasFiniteProducts

local notation "Σ_" f => Prefunctor.obj (Functor.toPrefunctor (Over.map f))

local notation3 "Δ_" f => Prefunctor.obj (Functor.toPrefunctor (baseChange f))

variable {I : C} {X Y : Over I}

/-- The base-change of `Y` along `X` is `pullback.snd (f:= Y.hom) (g:= X.hom)` -/
lemma baseChange_pullback_snd :
    ((Δ_ X.hom) Y).hom = pullback.snd := by
  rfl

-- lemma baseChang_pullback_snd' [HasPullbacks C] {I : C} (X Y : Over I) :
--     (Δ_ Y.hom |>.obj X).hom =  pullback.snd := by
--   rfl

-- @[ext]
-- lemma Over.obj_ext {X Y : Over I}
--   (h : X.left = Y.left)
--   (h' : X.hom = h ▸ Y.hom) : X = Y := by
--   obtain ⟨ x, ⟨⟩, f ⟩ := X
--   obtain ⟨ y, ⟨⟩, g ⟩ := Y
--   cases h
--   cases h'
--   rfl

@[simps]
def swapIso :
    (Σ_ X.hom) ((Δ_ X.hom) Y) ≅ (Σ_ Y.hom) ((Δ_ Y.hom) X)  := by
  fapply Over.isoMk
  · apply pullbackSymmetry
  · simp [pullback.condition]

@[simp]
lemma swap_eq_hom :
    ((Σ_ X.hom) ((Δ_ X.hom) Y)).hom = (pullbackSymmetry _ _).hom ≫ ((Σ_ Y.hom) ((Δ_ Y.hom) X)).hom  := by
  sorry

/-- The base-change of `Y` along `X` is `pullback.fst (f:= Y.hom) (g:= X.hom)` -/
@[simp]
def projLeft {I : C} (X Y : Over I) :
    (Σ_ X.hom) ((Δ_ X.hom) Y) ⟶ X :=
  Over.homMk (pullback.snd) (by simp [baseChange_pullback_snd])

@[simp]
def projRight  {I : C} (X Y : Over I) :
    (Σ_ X.hom) ((Δ_ X.hom) Y) ⟶ Y :=
  Over.homMk (pullback.fst) (by simp [pullback.condition])

lemma projRight_counit {I : C} (X Y : Over I) :
    projRight X Y = (Over.mapAdjunction X.hom).counit.app Y := by
  simp_all only [const_obj_obj, id_obj, mapAdjunction_counit_app]
  rfl

local notation "π_"   => projLeft

local notation "μ_"   => projRight

-- pullbackCompositionIsBinaryProduct
/-- Compsotion after base change gives the binary product in slices.-/
def isBinaryProduct  :
    IsLimit (BinaryFan.mk (π_ X Y) (μ_ X Y)) := by
  fapply IsLimit.mk
  · intro s
    fapply Over.homMk
    apply pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop_cat)
    simp
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;> simp
  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
    · apply congr_arg CommaMorphism.left (h ⟨ .right⟩)
    · apply congr_arg CommaMorphism.left (h ⟨ .left⟩)

/-- The object `(Σ_ X.hom) ((Δ_ X.hom) Y)` is isomorphic to the binary product `X × Y` in the slice category. -/
@[simps!]
def isoProd  :
    (Σ_ X.hom) ((Δ_ X.hom) Y) ≅ Limits.prod X Y := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProduct) (prodIsProd X Y)

@[simp]
lemma isoProd_comp_fst :
    (isoProd).hom ≫ prod.fst = (π_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct) (Limits.prodIsProd X Y) ⟨.left⟩

@[simp]
lemma isoProd_comp_snd :
    (isoProd).hom ≫ prod.snd = (μ_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct) (Limits.prodIsProd X Y) ⟨.right⟩

-- NatOverProdIso
/-- The functor composition `(baseChange X.hom).comp (Over.map X.hom)` is naturally isomorphic
to the left tensor product functor `X × _` -/
def natIsoTensorLeft [HasFiniteWidePullbacks C] {I : C} (X : Over I) :
    (baseChange X.hom).comp (Over.map X.hom) ≅ tensorLeft X := by
  fapply NatIso.ofComponents
  · intro Y
    apply isoProd
  · intro Y Z f
    simp
    ext1 <;> simp_rw [assoc]
    · simp_rw [prod.map_fst, comp_id]
      iterate rw [isoProd_comp_fst]
      ext
      simp
    · simp_rw [prod.map_snd]
      iterate rw [isoProd_comp_snd, ← assoc, isoProd_comp_snd]
      ext
      simp

end OverMapBaseChange

namespace Pushforward

variable {C : Type*} [Category C] [HasFiniteWidePullbacks C]

open OverMapBaseChange

class Pushforward {X Y : C} (f : X ⟶ Y) where
  functor : Over X ⥤ Over Y
  adj : baseChange f ⊣ pushforward := by aesop_cat

abbrev pushforward {X Y : C} (X : X ⟶ Y) [Pushforward X] := Pushforward.functor X

namespace Pushforward

variable {C : Type*} [Category C]

attribute [local instance] monoidalOfHasFiniteProducts
/-- An arrow with a pushforward is exponentiable in the slice category. -/
instance mkExponentiable {I : C} [HasFiniteWidePullbacks C]  (f : X ⟶ I) [Pushforward f] : Exponentiable (Over.mk f) where
  rightAdj := baseChange f ⋙ pushforward f
  adj := by
    fapply ofNatIsoLeft
    apply (baseChange f ⋙ Over.map f)
    sorry
    sorry

end Pushforward


#check Exponentiable
