/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
-- import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

-- Likely too many imports!


/-!
# Locally cartesian closed categories

-/


noncomputable section

open CategoryTheory Category Limits Functor Adjunction

variable {C : Type*}[Category C]

def hasPullbackOverAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over.map f ⊣ baseChange f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y ↦ {
      toFun := fun u ↦ {
        left := by
          simp
          fapply pullback.lift
          · exact u.left
          · exact x.hom
          · aesop_cat
        right := by
          apply eqToHom
          aesop
        w := by simp}
      invFun := fun v ↦ {
        left := by
          simp at*
          exact v.left ≫ pullback.fst
        right := by
          apply eqToHom
          aesop
        w := by
          simp
          rw [pullback.condition]
          rw [← Category.assoc]
          apply eq_whisker
          simpa using v.w}
      left_inv := by aesop_cat
      right_inv := fun v ↦ Over.OverMorphism.ext (by
        simp
        apply pullback.hom_ext
        · aesop_cat
        · rw [pullback.lift_snd]
          have vtriangle := v.w
          simp at vtriangle
          exact vtriangle.symm)}
    homEquiv_naturality_left_symm := by aesop_cat
    homEquiv_naturality_right := by aesop_cat}

/-
There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices C/I are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks and terminal object such that each base change functor has a right adjoint, called the pushforward functor.

In this file we prove the equivalence of these conditions.
-/

attribute [local instance] monoidalOfHasFiniteProducts


variable {C : Type} [Category C] [HasTerminal C] [HasBinaryProducts C]

#check MonoidalCategory
#print CartesianClosed

#check monoidalOfHasFiniteProducts

#synth (MonoidalCategory C)

example : MonoidalCategory C := by apply monoidalOfHasFiniteProducts

#check MonoidalClosed

variable (C : Type*) [Category C] [HasFiniteProducts C] [HasPullbacks C]

#check Comma

#check Over

#check CategoryTheory.Limits.pullback

#check baseChange


#check IsLeftAdjoint


#check Over


class LocallyCartesianClosed' where
  pushforward {X Y : C} (f : X ⟶ Y) : IsLeftAdjoint (baseChange f) := by infer_instance

class LocallyCartesianClosed where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance

namespace LocallyCartesianClosed

example [HasFiniteLimits C] : HasFiniteProducts C := by infer_instance

set_option trace.Meta.synthInstance.instances true in
example [HasFiniteWidePullbacks C] {I : C} : HasFiniteLimits (Over I ) := by infer_instance

#check Over.hasFiniteLimits

example [LocallyCartesianClosed C] [HasFiniteWidePullbacks C] : HasFiniteLimits (Over (terminal C)) := by infer_instance

#check Adjunction

def cartesianClosedOfOver [LocallyCartesianClosed C] [HasFiniteWidePullbacks C]
    {I : C} : CartesianClosed (Over I) where
      closed := fun f => {
        rightAdj := baseChange f.hom ⋙ pushforward f.hom
        adj := by
          apply ofNatIsoLeft
          · apply Adjunction.comp
            · exact (LocallyCartesianClosed.adj f.hom)
            · exact (hasPullbackOverAdj f.hom)
          · apply NatIso.ofComponents
            · sorry
            · sorry
      }

end LocallyCartesianClosed

#check LocallyCartesianClosed

-- Every locally cartesian closed category is cartesian closed.

namespace LocallyCartesianClosed

variable {C : Type*} [Category C] [HasTerminal C] [HasFiniteProducts C] [HasPullbacks C]


example [LocallyCartesianClosed C] : CartesianClosed C where
  closed X := {
    rightAdj := sorry
    adj := sorry
  }



end LocallyCartesianClosed





-- The slices of a locally cartesian closed category are locally cartesian closed.

#check Over.iteratedSliceEquiv



#check CartesianClosed

-- class LCCC where
--   slice : ∀ I : C, CartesianClosed (Over I)
