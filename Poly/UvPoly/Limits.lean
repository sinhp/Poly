/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.UvPoly.Basic

/-!  We show that the polynomial functor preserve connected limits. -/

universe v₁ u₁

open CategoryTheory Limits

namespace UvPoly

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] [HasTerminal C] {E B : C}

instance preservesConnectedLimitsOfShape_of_hasLimitsOfShape {J : Type v₁} [SmallCategory J]
    [IsConnected J] [HasLimitsOfShape J C] (P : UvPoly E B) :
    PreservesLimitsOfShape J (P.functor) := by
  unfold UvPoly.functor
  infer_instance

end UvPoly
