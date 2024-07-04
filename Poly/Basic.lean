/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Sina Hazratpour
-/

-- import Mathlib.CategoryTheory.Adjunction.Mates

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering

import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Limits.Shapes.CommSq

import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

import Mathlib.CategoryTheory.Monad.Products

import Poly.TempMates -- Contains an open mathlib PR redoing the mates file


/-!
# Some basic equalities and isomorphisms of composition and base change functors


## Notation

We provide the following notations:

Given a morphism `f : J ⟶ I` in a category `C`,
* `Σ_ f` is the functor `Over.map f : Over I ⥤ Over J`.
* `Δ_ f` is the functor `baseChange f : Over J ⥤ Over I`.

Given an object `I : C`,
* `Σ_ I` is the functor `Over.forget : Over I ⥤ C`.
* `Δ_ I` is the functor `Over.star : C ⥤ Over I`.

For `X Y : Over I`,
* `μ_ X Y` is the projection morphism `(Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ Y`
defined via the counit of the adjunction `Σ_ ⊣ Δ_`, namely `(mapAdjunction Y.hom).counit.app`.
* `π_ X Y` is the projection morphism `(Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ X`
defined via the counit  of the adjunction `Σ_ ⊣ Δ_` and the isomorphism
`swapIso X Y : (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ≅ (Σ_ Y.hom).obj ((Δ_ Y.hom).obj X)`.

We prove that `μ_ X Y` and `π_ X Y` form a pullback square:

```
  P ---- μ --> •
  |            |
  π            Y
  |            |
  v            v
  • ---X--->  I
```

### Implementation Notes

(SH): The definitions `Over.pullback` and `mapPullbackAdj` already existed in mathlib.
Later, `Over.baseChange` and `Over.mapAdjunction` were added
which are duplicates, but the latter have additional `simp` lemmas, namely `unit_app` and `counit_app` which makes proving things with
`simp` easier.

We might change instances of `Over.mapAdjunction` to `Over.mapPullbackAdj`.

(SH) : WIP -- adiding `simp` attributes to `Over.forgetAdjStar`. This means
we no longer will need the lemmas in the namespace `Over.forgetAdjStar`.


#### Other diagrams

```

                      .fst
        pullback p f ------> X
          |                  |
          |                  | p
    .snd  |                  |
          v                  v
          J   ---------->    I
                    f
```

Using the notation above, we have
* `hom_eq_pullback_snd` proves that `(Δ_ f Over.mk p).hom` is `pullback.snd`
* `natIsoTensorLeft` proves that `Δ_ f` ⋙ `Σ_ f` is isomorphic to the product functor `f × _` in the slice category `Over I`.

-/

namespace CategoryTheory
-- universe v₁ v₂ v₃ u₁ u₂ u₃ v u

open Category Functor Adjunction Limits NatTrans Over

variable {C : Type*} [Category C]

@[inherit_doc]
prefix:90 "Σ_ " => Over.map

@[inherit_doc]
prefix:90 "Σ_ " => Over.forget

@[inherit_doc]
prefix:90 "Δ_ " => Over.baseChange -- we might change this to `Over.pullback` later.

@[inherit_doc]
prefix:90 "Δ_ " => Over.star


namespace Over.forgetAdjStar

variable [HasBinaryProducts C] {I : C}

@[simp]
theorem unit_app_left_eq (X : Over I):
    ((Over.forgetAdjStar I).unit.app X).left = prod.lift X.hom (𝟙 X.left) := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

@[simp]
theorem unit_app_eq (X : Over I):
    (Over.forgetAdjStar I).unit.app X = homMk (by simp; exact prod.lift X.hom (𝟙 _)) := by
  ext
  simp

@[simp]
def counit_app_eq (X : C) :
    ((Over.forgetAdjStar I).counit.app X) = prod.snd := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

@[simp]
theorem homEquiv (X : Over I) (A : C) (f : X.left ⟶ A) :
    (Over.forgetAdjStar I).homEquiv X A f =
    homMk (V := (Δ_ I).obj A) (prod.lift X.hom f) := by
  rw [homEquiv_unit, unit_app_eq]
  ext
  simp

@[simp]
theorem homEquiv_symm [HasBinaryProducts C] (X : Over I) (A : C) (f : X ⟶ (Δ_ I).obj A) :
     ((Over.forgetAdjStar I).homEquiv X A).symm f = f.left ≫ prod.snd := by
   rw [homEquiv_counit, counit_app_eq]
   simp

end Over.forgetAdjStar


section NaturalityOfWhiskering

variable {A B : Type*}
variable [Category A] [Category B]
variable {F G : A ⥤ B} {H K : B ⥤ C}

-- Naturality of β implies naturality of whiskering; this is not used.
@[simp]
theorem WhiskeringNaturality
    (α : F ⟶ G) (β : H ⟶ K) :
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

section

variable {C : Type u} [Category.{v} C]

@[simp]
lemma pullback.map_id {W X S : C} (f : W ⟶ S) (g : X ⟶ S) [HasPullback f g] (h) (h') :
    pullback.map f g f g (𝟙 W) (𝟙 X) (𝟙 S) h h' = 𝟙 (pullback f g) := by
  unfold pullback.map
  ext <;> simp

end

noncomputable section

namespace Over

@[simp]
theorem eqToHom_left {X : C} {U V : Over X} (e : U = V) :
    (eqToHom e).left = eqToHom (e ▸ rfl : U.left = V.left) := by
  subst e; rfl

theorem mapForget_eq {X Y : C} (f : X ⟶ Y) :
    Σ_ f ⋙ Σ_ Y = Σ_ X := by
  fapply Functor.ext
  · dsimp [Over, Over.map]; intro x; exact rfl
  · intros x y u; simp

/--Equality of functors should be avoided if possible, instead we use the isomorphism version.
For use elsewhere.-/
def mapForgetIso {X Y : C} (f : X ⟶ Y) :
    Σ_ f ⋙ Σ_ Y ≅ Σ_ X := eqToIso (mapForget_eq f)

theorem mapComp_eq {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Σ_ f ⋙ Σ_ g = Σ_ (f ≫ g) := by
  fapply Functor.ext
  · simp [Over.map, Comma.mapRight]
  · intro U V k
    ext
    simp

/- Note (SH) : note tha `mapComp` already exists in mathlib, and indeed the components of
of it are `Iso.refl`.
 -/
def mapCompIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Σ_ f ⋙ Σ_ g ≅ Σ_ (f ≫ g) := eqToIso (mapComp_eq f g)

end Over

namespace baseChange

open Over MonoidalCategory

/-- For an arrow `f : J ⟶ I` and an object `X : Over I`, the base-change of `X` along `f` is `pullback.snd`. -/
lemma obj_hom_eq_pullback_snd [HasPullbacks C] {I J : C} (f : J ⟶ I) (X : Over I):
    ((Δ_ f).obj X).hom = pullback.snd := by
  rfl

lemma Over.star_obj_eq_mk_prod_fst [HasBinaryProducts C] (I X : C) :
    (Δ_ I).obj X = Over.mk (prod.fst : I ⨯ X ⟶ I) := by
  simp [Over.star, Over.mk]

variable [HasPullbacks C]

/-- The base-change along `terminal.from` ER: Changed statement from an equality to an isomorphism. Proof of commutativity is stuck because of the rewrite. Perhaps I can do this another way? -/
def terminal_from [HasTerminal C] [HasBinaryProducts C] (I : C) (X : Over (⊤_ C)) :
    (Δ_ (terminal.from I)).obj X ≅ (Δ_ I).obj (X.left) := by
  fapply Over.isoMk
  · simp
    have := prodIsoPullback I X.left
    have lem := terminal.hom_ext X.hom (terminal.from X.left)
    rw [← lem] at this
    exact pullbackSymmetry X.hom (terminal.from I) ≪≫ this.symm
  · simp
    sorry

@[simps!]
def swapIso {I : C} (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ≅ (Σ_ Y.hom).obj ((Δ_ Y.hom).obj X)  := by
  fapply Over.isoMk
  · apply pullbackSymmetry
  · simp [pullback.condition]

@[simp]
lemma swap_eq_hom {I : C} {X Y : Over I} :
    ((Σ_ X.hom).obj ((Δ_ X.hom).obj Y)).hom =
    (pullbackSymmetry _ _).hom ≫ ((Σ_ Y.hom).obj ((Δ_ Y.hom).obj X)).hom  := by
  simp [← pullback.condition]

/-- For `X Y : Over I`, the map `μ := projFst`, defined via the counit of the adjunction
`Σ_ ⊣ Δ_`, is a morphism form the base-change of `Y` along `X` to `Y` .
```
  P ---- μ --> •
  |            |
  π            Y
  |            |
  v            v
  • ---X--->  I
```
-/
@[simp]
def projFst {I : C} (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ Y :=
  (mapAdjunction X.hom).counit.app Y

local notation "μ_ "  => projFst

/-- For `X Y : Over I`, the map `π := projSnd` is a morphism form the base-change of `X` along `Y` to `X`.
```
  P ---- μ --> •
  |            |
  π            Y
  |            |
  v            v
  • ---X--->  I
```
-/
@[simp]
def projSnd {I : C} (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ X :=
  (swapIso X Y).hom ≫ (mapAdjunction Y.hom).counit.app X

local notation "π_ "  => projSnd

lemma projFst_eq_pullback_fst {I : C} {X Y : Over I} :
    μ_ X Y =
    Over.homMk (by simp; exact pullback.fst) (by simp [pullback.condition]) := by
  simp

lemma projFst_left_eq_pullback_fst {I : C} {X Y : Over I} :
    (μ_ X Y).left = pullback.fst := by
  simp

lemma projSnd_eq_pullback_snd {I : C} {X Y : Over I} :
    π_ X Y =
    Over.homMk (by simp; exact pullback.snd) (by simp)  := by
  aesop

lemma projSnd_left_eq_pullback_snd {I : C} {X Y : Over I} :
    (π_ X Y).left = (pullback.snd) := by
  simp

-- Note (SH): We already know that `(π_ X Y)` and `(μ_ X Y)` are components of a pullback
-- square in the underlying category `C`. We also know that the binary products in the
-- over category are pullbacks in the base category. Note that the folder
-- `CategoryTheory.Limits.Shapes.Constructions.Over` shows that `Over X`
-- has `J`-indexed products if `C` has `J`-indexed wide pullbacks.
-- We should take advantage of these facts
-- to prove `IsLimit <| BinaryFan.mk (π_ X Y) (μ_ X Y) ` in `Over I` rather than giving a
-- direct proof.

def isBinaryProduct {I : C} (X Y : Over I) :
    IsLimit <| BinaryFan.mk (π_ X Y) (μ_ X Y) := by
  rw [projFst_eq_pullback_fst, projSnd_eq_pullback_snd]
  fapply IsLimit.mk
  · intro s
    fapply Over.homMk
    apply pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop_cat)
    simp
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;> simp
  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
    · apply congr_arg CommaMorphism.left (h ⟨ .right⟩)
    · apply congr_arg CommaMorphism.left (h ⟨ .left ⟩)

/-- The object `(Σ_ X.hom) ((Δ_ X.hom) Y)` is isomorphic to the binary product `X × Y`
in `Over I`. -/
@[simps!]
def isoProd {I : C} (X Y : Over I) [HasBinaryProduct X Y] :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ≅ Limits.prod X Y := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProduct X Y) (prodIsProd X Y)

def isoProdmk {I J : C} (f : J ⟶ I) (Y : Over I) [HasBinaryProduct (Over.mk f) Y]:
    (Σ_ f).obj ((Δ_ f).obj Y) ≅ Limits.prod (Over.mk f) Y :=
  isoProd (Over.mk f) _

@[simp]
lemma isoProd_comp_fst {I : C} (X Y : Over I) [HasBinaryProduct X Y]:
    (isoProd X Y).hom ≫ prod.fst = (π_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct X Y) (Limits.prodIsProd X Y) ⟨.left⟩

@[simp]
lemma isoProdmk_comp_fst {I J : C} (f : J ⟶ I) (Y : Over I) [HasBinaryProduct (Over.mk f) Y] :
    (isoProdmk f Y).hom ≫ prod.fst = (π_ (Over.mk f) Y) :=
  isoProd_comp_fst (Over.mk f) Y

@[simp]
lemma isoProd_comp_snd {I : C} {X Y : Over I} [HasBinaryProduct X Y] :
    (isoProd X Y).hom ≫ prod.snd = (μ_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct X Y) (Limits.prodIsProd X Y) ⟨.right⟩

variable [HasFiniteWidePullbacks C] {I : C}

attribute [local instance] monoidalOfHasFiniteProducts

-- NatOverProdIso
/-- The functor composition `(baseChange X.hom) ⋙ (Over.map X.hom)` is naturally isomorphic
to the left tensor product functor `X × _` -/
def natIsoTensorLeft {I : C} (X : Over I) :
    (Δ_ X.hom) ⋙ (Σ_ X.hom) ≅ tensorLeft X := by
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

def natIsoTensorLeftOverMk {I J : C} (f : J ⟶ I) :
    (Δ_ f) ⋙ (Σ_ f) ≅ tensorLeft (Over.mk f) := by
  apply natIsoTensorLeft (Over.mk f)

/--
The isomorphism between the base change functors obtained as the conjugate of the `mapForgetIso`.
For use elsewhere.-/
def mapStarIso [HasBinaryProducts C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Δ_ X ≅ Δ_ Y ⋙ Δ_ f :=
  conjugateIsoEquiv (Over.forgetAdjStar X) ((mapAdjunction f).comp (Over.forgetAdjStar Y)) (mapForgetIso f)

def id (I : C) : Δ_ (𝟙 I) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapAdjunction (𝟙 I)) Adjunction.id (mapId I).symm

/- Note (SH): This has already been done in `Over.pullbackComp`. What is different in this variant? -/
/-- The conjugate isomorphism between pullback functors. -/
def comp [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Δ_ (f ≫ g) ≅ Δ_ g ⋙ Δ_ f :=
  conjugateIsoEquiv (mapAdjunction (f ≫ g)) ((mapAdjunction f).comp (mapAdjunction g)) (mapCompIso f g)

end Over

end baseChange
namespace Limits

/- Note (SH) : In general, in `Poly` project, we use `IsPullback` instead of `HasPullback`. -/
@[simp]
lemma pullback.map_id {W X S : C} (f : W ⟶ S) (g : X ⟶ S) [HasPullback f g] (h) (h') :
    pullback.map f g f g (𝟙 W) (𝟙 X) (𝟙 S) h h' = 𝟙 (Limits.pullback f g) := by
  simp only [pullback.map]
  ext <;> simp

end Limits

variable {C : Type*} [Category C] [HasPullbacks C]

-- Proof by Markus Himmel (with commentary by Dagur Asgeirsson)
@[simps]
def toOverTerminal' (T : C) (h : IsTerminal T) : C ⥤ Over T where
  obj X := Over.mk (h.from _)
  map f := Over.homMk f

/-- Note (SH): the difference between this and `Δ_ (⊤_ C)` is that we only use the
assumption that `C` has only terminal but not binary products.
On the other hand, I recommend using `Δ_ (⊤_ C)` in general since we know more facts
about it such its adjunction (top of the file).
-/
def toOverTerminal [HasTerminal C] : C ⥤ Over (⊤_ C) :=
  toOverTerminal' (⊤_ C) terminalIsTerminal

def equivOverTerminal' (T : C) (h : IsTerminal T) : C ≌ Over T :=
  CategoryTheory.Equivalence.mk (toOverTerminal' T h) (Over.forget _)
    (NatIso.ofComponents (fun X => Iso.refl _))
    (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _) (by simpa using h.hom_ext _ _)))

def equivOverTerminal [HasTerminal C] : C ≌ Over (⊤_ C) :=
  equivOverTerminal' (⊤_ C) terminalIsTerminal

def isoOverTerminal [HasTerminal C] : Cat.of (ULift C) ≅ Cat.of (Over (⊤_ C)) where
  hom := {
    obj  := fun ⟨X⟩ => by
      exact Over.mk (terminalIsTerminal.from X)
    map := @fun ⟨X⟩ ⟨Y⟩ f => by
      exact Over.homMk f
  }
  inv := {
    obj := fun X => sorry
    map := sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

def toOverTerminalStarIso [HasTerminal C] [HasBinaryProducts C] : Δ_ (⊤_ C) ≅ toOverTerminal := by
  have := Iso.refl (Σ_ (⊤_ C))
  sorry -- I can't seem to infer that the inverse equivalence used above is an equivalence.
  -- have : (Over.forget (⊤_ C)).IsEquivalence := by infer_instance
  -- have := (Over.forget (⊤_ C)).asEquivalence.toAdjunction
  -- have := conjugateIsoEquiv (Over.forgetAdjStar (⊤_ C)) _ this

def toOverTerminalStarTriangleIso [HasTerminal C] [HasBinaryProducts C] (X : C) :
    Δ_ X ≅ toOverTerminal ⋙ Δ_ (terminal.from X) :=
  baseChange.mapStarIso (terminal.from X) ≪≫ isoWhiskerRight (toOverTerminalStarIso (C := C)) (Δ_ (terminal.from X))
