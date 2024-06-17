/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monad.Products

import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Over

import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
-- import Mathlib.CategoryTheory.Category.Limit
import Poly.LCCC.LCCC
import Poly.Exponentiable

/-!
# Polynomial Functor
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I` and output variables in `O`. -/
structure MvPoly (I O : C) :=
  (B E : C)
  (s : E ⟶ I)
  (p : E ⟶ B)
  (t : B ⟶ O)

variable (C)

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly :=
  (B E : C)
  (p : E ⟶ B)


namespace MvPoly

open Pushforward

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

/-- The identity polynomial functor in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, 𝟙 I⟩

instance (I : C) : Pushforward (id I).p := sorry

def functor (I O : C) (P : MvPoly I O) [Pushforward P.p] : Over I ⥤ Over O :=
  baseChange (P.s) ⋙ (Pushforward.functor P.p) ⋙ Over.map (P.t)

variable (I O : C) (P : MvPoly I O)
-- #check (Σ_ P.t)

def apply (P : MvPoly I O) [Pushforward P.p] : Over I → Over O := (P.functor).obj


def id_apply (q : X ⟶ I) [Pushforward q]: (id I).apply (Over.mk q) ≅ Over.mk q where
  hom := by
    simp [apply]
    simp [functor]
    dsimp
    exact {
      left := by
        dsimp
        sorry
      right := sorry
      w := sorry
    }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry



-- TODO: examples monomials, linear polynomials, 1/1-X, ...

-- TODO: basic operations: sum, product, composition, differential

-- TODO (Steve's idea): a subcategory of small maps to be thought of as context extensions in LCCC. These are morphisms for which the pushforward functor has a further right adjoint (maps with tiny fibres).

end MvPoly


namespace UvPoly
#print LCC
variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C] [LCC C]

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id (X : C) : UvPoly C := ⟨X, X, 𝟙 X⟩

-- Note (SH): We define the functor associated to a single variable polyonimal in terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.

def toMvPoly (P : UvPoly C) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨P.B, P.E, terminal.from P.E, P.p, terminal.from P.B⟩

-- #check (toMvPoly _).functor

instance (P : UvPoly C) : Pushforward P.toMvPoly.p := sorry

def functor' (P : UvPoly C) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor (⊤_ C) (⊤_ C) P.toMvPoly

-- Note (SH): we can use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials.

-- Note (SH): Seems like this is missing from mathlib!
-- Note (SH): maybe isomorphism would be better, although we do prefer equivalence in general.
-- Note (SH): Isomorphisms of categories in mathlib is isomorphism in the category of cateogories.
-- Note that if we use this definition, we
def overTerminalEquivalence : Over (⊤_ C) ≌ C := .mk (F:= sorry) (G:= sorry) (η:= sorry) (ε:= sorry)

def functor (P : UvPoly C) : C ⥤ C :=  overTerminalEquivalence.inverse ⋙  P.functor'  ⋙ overTerminalEquivalence.functor

end UvPoly
