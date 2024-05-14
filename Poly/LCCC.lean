/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
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

noncomputable section

open CategoryTheory Category Limits Functor

/-
There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices C/I are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks and terminal objecr such that each base change functor has a right adjoint, called the pushforward functor.

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
  pushforwad {X Y : C} (f : X ⟶ Y) : IsLeftAdjoint (baseChange f) := by infer_instance

class LocallyCartesianClosed where
  pushforwad {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj : baseChange f ⊣ pushforwad f := by infer_instance

namespace LocallyCartesianClosed

example [HasFiniteLimits C] : HasFiniteProducts C := by infer_instance

set_option trace.Meta.synthInstance.instances true in
example [HasFiniteWidePullbacks C] {I : C} : HasFiniteLimits (Over I ) := by infer_instance

#check Over.hasFiniteLimits

example [LocallyCartesianClosed C] [HasFiniteWidePullbacks C] : HasFiniteLimits (Over (terminal C)) := by infer_instance

lemma closed_left [LocallyCartesianClosed C]


example [LocallyCartesianClosed C] [HasFiniteWidePullbacks C] :
    CartesianClosed (Over I) where
  closed := fun f ↦ {
    rightAdj := {
      obj := fun g => {
        left := (ihom f.left).obj g.left
        right := _
        hom := _
      }
      map := sorry
    }
    adj := _
  }


end LocallyCartesianClosed

#check LocallyCartesianClosed

-- Every locally cartesian closed category is cartesian closed.

namespace LocallyCartesianClosed

variable {C : Type*} [Category C] [HasTerminal C] [HasFiniteProducts C] [HasPullbacks C]


example [LocallyCartesianClosed C] : CartesianClosed C where
  closed X := {
    rightAdj := _
    adj := _
  }



end LocallyCartesianClosed





-- The slices of a locally cartesian closed category are locally cartesian closed.

#check Over.iteratedSliceEquiv



#check CartesianClosed

-- class LCCC where
--   slice : ∀ I : C, CartesianClosed (Over I)
