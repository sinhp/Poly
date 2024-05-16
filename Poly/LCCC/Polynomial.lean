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

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [LocallyCartesianClosed C]

open LocallyCartesianClosed

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I` and output variables in `O`. -/
structure MvPoly (I O : C) :=
  (B E : C)
  (s : E ⟶ I)
  (p : E ⟶ B)
  (t : B ⟶ O)

variable (C)

/-- `P : UvPoly C` is a one-variable polynomial. -/
structure UvPoly :=
  (B E : C)
  (p : E ⟶ B)

namespace MvPoly

open LocallyCartesianClosed

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [LocallyCartesianClosed C] (I O : C)

def functor (P : MvPoly I O) : Over I ⥤ Over O :=
  baseChange (P.s) ⋙ (pushforward P.p) ⋙ Over.map (P.t)

-- TODO: examples monomials, linear polynomials, 1/1-X, ...

-- TODO: basic operations: sum, product, composition, differential

-- TODO (Steve's idea): a subcategory of small maps to be thought of as context extensions in LCCC. These are morphisms for which the pushforward functor has a further right adjoint (maps with tiny fibres).

end MvPoly


namespace UvPoly

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [LocallyCartesianClosed C]

#check UvPoly
#check terminal C -- ⊤_ C

def toMvPoly (P : UvPoly C) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨P.B, P.E, terminal.from P.E, P.p, terminal.from P.B⟩

#check (toMvPoly _).functor

def functor' (P : UvPoly C) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor (⊤_ C) (⊤_ C) P.toMvPoly

-- Note (SH): we can use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials.

-- Note (SH): Seems like this is missing from mathlib!
-- Note (SH): maybe isomorphism would be better, although we do prefer equivalence in general.
def overTerminalEquivalence : Over (⊤_ C) ≌ C where
  functor := {
    obj := fun f => f.left
    map := @fun f g k => k.left
    map_id := by sorry
    map_comp := by sorry
  }
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

def functor (P : UvPoly C) : C ⥤ C :=  overTerminalEquivalence.inverse ⋙  P.functor'  ⋙ overTerminalEquivalence.functor





end UvPoly
