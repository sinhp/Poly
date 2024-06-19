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
import Poly.Exponentiable
import Poly.LCCC.Basic

/-!
# Polynomial Functor
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasFiniteWidePullbacks C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I` and output variables in `O`. -/
structure MvPoly (I O : C) :=
  (B E : C)
  (s : E ⟶ I)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)
  (t : B ⟶ O)

variable (C)

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly :=
  (B E : C)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)


namespace MvPoly

open CartesianExponentiable

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

-- instance (I O : C) (P : MvPoly I O) : Inhabited (MvPoly I O) := ⟨P⟩

-- instance (I O : C) (P : MvPoly I O) : CartesianExponentiable P.p := P.exp

attribute [instance] MvPoly.exp

attribute [instance] UvPoly.exp

/-- The identity polynomial functor in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, CartesianExponentiable.id, 𝟙 I⟩

instance (I : C) : CartesianExponentiable ((id I).p) := CartesianExponentiable.id

/-- The constant polynomial functor in many variables: for this we need the initial object. -/

local notation "Σ_" => Over.map

local notation "Δ_" => baseChange

local notation "Π_" => CartesianExponentiable.functor

def functor {I O : C} (P : MvPoly I O) :
    Over I ⥤ Over O :=
  Δ_ (P.s) ⋙ (Π_ P.p) ⋙ Σ_ (P.t)

variable (I O : C) (P : MvPoly I O)
-- #check (Σ_ P.t)

def apply (P : MvPoly I O) [CartesianExponentiable P.p] : Over I → Over O := (P.functor).obj

-- TODO: write a coercion from `MvPoly` to a functor for evalutation of polynomials at a given object.

def id_apply (q : X ⟶ I) : (id I).apply (Over.mk q) ≅ Over.mk q where
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

-- TODO: The set of connected components of el(P) is in bijection with the set P(1) ≅ A

def comp (P: MvPoly I J) (Q : MvPoly J K) : MvPoly I K := sorry

end MvPoly


namespace UvPoly

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

local notation "Σ_" => Over.map

local notation "Δ_" => baseChange

local notation "Π_" => CartesianExponentiable.functor


/-- The identity polynomial functor in single variable. -/
@[simps!]
def id (B : C) : UvPoly C := ⟨B, B, 𝟙 B, by infer_instance⟩

-- Note (SH): We define the functor associated to a single variable polyonimal in terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.

def toMvPoly (P : UvPoly C) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨P.B, P.E, terminal.from P.E, P.p, P.exp, terminal.from P.B⟩

#check (toMvPoly _).functor

def auxFunctor (P : UvPoly C) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor P.toMvPoly

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials. -/

def functor (P : UvPoly C) : C ⥤ C :=  equivOverTerminal.functor ⋙  P.auxFunctor ⋙ equivOverTerminal.inverse

example [HasBinaryProducts C] (X  Y : C) : X ⨯  Y ⟶ X := prod.fst

#check Over.star -- Δ_ (prod.snd (X:= B) (Y:= E))

def functor' (P : UvPoly C) : C ⥤ C := (Over.star P.E) ⋙ (Π_ P.p) ⋙ (Over.forget P.B)

/-- Evaluating a single variable polynomial at an object `X` -/
def apply (P : UvPoly C) (X : C) : C := P.functor.obj X

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `X` -/
def id_apply (X : C) : (id I).apply X ≅ X where
  hom := by
    simp [id, apply, functor]
    sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B`. -/
def proj (P : UvPoly C) (X : Over (⊤_ C)) :
  ((Π_ P.p).obj ((Δ_ (terminal.from P.E)).obj X)).left ⟶ P.B :=
  ((Δ_ (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

-- set_option synthInstance.maxHeartbeats 100000 in
def comp (P Q : UvPoly C) : UvPoly C :=
  let E := P.E
  let B := P.B
  let D := Q.E
  let C := Q.B
  let f : E ⟶ B := P.p
  let g : D ⟶ C := Q.p
  {
    B := P.functor.obj C
    E := sorry
    p := sorry
    exp := sorry
  }

/-- The universal property of the polynomial functor.-/
def equiv (P : UvPoly C) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ P.B, pullback P.p b ⟶ X := sorry

end UvPoly
