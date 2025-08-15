/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.UvPoly.Basic

/-!  We show that the polynomial functor preserve connected limits. -/

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Functor Adjunction Over ExponentiableMorphism
  LocallyCartesianClosed

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance forgetPreservesConnectedLimitsOfShape_of_hasLimitsOfShape {J : Type*} [SmallCategory J]
    [IsConnected J] [HasLimitsOfShape J C] {B : C} :
    PreservesLimitsOfShape J (forget B) := by
  apply preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape

namespace UvPoly

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] [HasTerminal C] {E B : C}

instance foo : PreservesLimits (star E) :=
  forgetAdjStar E |>.rightAdjoint_preservesLimits

instance pushforward_preservesLimits (P : UvPoly E B) : PreservesLimits (pushforward P.p) :=
  (adj P.p).rightAdjoint_preservesLimits

instance preservesConnectedLimitsOfShape_of_hasLimitsOfShape {J : Type v₁} [SmallCategory J] [IsConnected J]
    [HasLimitsOfShape J C] (P : UvPoly E B) :
    PreservesLimitsOfShape J (P.functor) := by
  refine @comp_preservesLimitsOfShape _ _ _ _ (J:= J) _ _ _ (Over.star E)
    (pushforward P.p ⋙ forget B) ?_ ?_
  · apply forgetAdjStar E |>.rightAdjoint_preservesLimits |>.preservesLimitsOfShape (J:= J)
  · apply @comp_preservesLimitsOfShape _ _ _ _ (J:= J) _ _ _ (pushforward P.p) (forget B) ?_ ?_
    · apply P.pushforward_preservesLimits |>.preservesLimitsOfShape (J:= J)
    · apply forgetPreservesConnectedLimitsOfShape_of_hasLimitsOfShape

instance preservesConnectedLimitsOfShape_of_hasLimitsOfShape' {J : Type v₁} [SmallCategory J]
    [IsConnected J] [HasLimitsOfShape J C] (P : UvPoly E B) :
    PreservesLimitsOfShape J (P.functor) := by
  infer_instance

end UvPoly
