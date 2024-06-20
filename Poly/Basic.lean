/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

-- import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering

import Poly.TempMates -- Contains an open mathlib PR redoing the mates file

/-!
# Some basic equalities and isomorphisms
-/

namespace CategoryTheory
universe v₁ v₂ v₃ u₁ u₂ u₃ v u

open Category Functor Adjunction Limits NatTrans Over

section NaturalityOfWhiskering

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable {F G : A ⥤ B}{H K : B ⥤ C}

-- Naturality of β implies naturality of whiskering; this is not used.
@[simp]
theorem WhiskeringNaturality
    (α : F ⟶ G)(β : H ⟶ K) :
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

noncomputable section

namespace Over
variable {C : Type u} [Category.{v} C]

@[simp]
theorem eqToHom_left {X : C} {x y : Over X} (e : x = y) : (eqToHom e).left = eqToHom (e ▸ rfl) := by
  subst e; rfl

theorem mapForget_eq {X Y : C}(f : X ⟶ Y) :
    map f ⋙ forget Y = forget X := by
  fapply Functor.ext
  · dsimp [Over, Over.map]; intro x; exact rfl
  · intros x y u; simp

/-- For use elsewhere.-/
def mapForgetIso {X Y : C}(f : X ⟶ Y) :
    map f ⋙ forget Y ≅ forget X := eqToIso (mapForget_eq f)

/-- For use elsewhere.-/
def mapStarIso [HasBinaryProducts C] [HasPullbacks C] {X Y : C}(f : X ⟶ Y) :
  star X ≅ star Y ⋙ baseChange f := conjugateIsoEquiv (forgetAdjStar X) ((mapAdjunction f).comp (forgetAdjStar Y)) (mapForgetIso f)

theorem mapComp_eq {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) :
    map f ⋙ map g = map (f ≫ g) := by
  fapply Functor.ext
  · dsimp [Over, Over.map]; intro x; unfold Comma.mapRight; simp
  · intros x y u; ext; simp

def mapCompIso {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) :
    Over.map f ⋙ Over.map g ≅ Over.map (f ≫ g) := eqToIso (mapComp_eq f g)

/-- The conjugate isomorphism between pullback functors. -/
def pullbackCompIso [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  conjugateIsoEquiv (mapAdjunction (f ≫ g)) ((mapAdjunction f).comp (mapAdjunction g)) (mapCompIso f g)

end Over
