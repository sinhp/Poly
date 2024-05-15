/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
import Poly.LCCC.LCCC

/-!
# Polynomial Functor
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction

variable {C : Type*} [Category C] [HasPullbacks C] [LocallyCartesianClosed C]

namespace LocallyCartesianClosed

structure Poly (I O : C) :=
  (B E : C)
  (s : E ⟶ I)
  (p : E ⟶ B)
  (t : B ⟶ O)

namespace Poly

variable {I O : C} (P : Poly I O)

#check LocallyCartesianClosed.pushforward

def functor : Over I ⥤ Over O :=
  baseChange (P.s) ⋙ (LocallyCartesianClosed.pushforward P.p) ⋙ Over.map (P.t)

end Poly

end LocallyCartesianClosed
