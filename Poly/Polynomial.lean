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
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
--import Mathlib.CategoryTheory.Category.Limit
import Poly.Exponentiable
-- import Poly.LCCC.Basic

/-!
# Polynomial Functor
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I` and output variables in `O`. -/
structure MvPoly (I O : C) :=
  (E B : C)
  (s : E ⟶ I)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)
  (t : B ⟶ O)

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly (E B : C) :=
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

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

local notation "Σ_" => Over.map

local notation "Δ_" => baseChange

local notation "Π_" => CartesianExponentiable.functor

instance : HasBinaryProducts C := by sorry --infer_instance --not woking; we should get this from `HasTerminal` and `HasPullbacks`?

variable {E B : C}

-- Note (SH): We define the functor associated to a single variable polyonimal in terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.

def toMvPoly (P : UvPoly E B) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨E, B, terminal.from E, P.p, P.exp, terminal.from B⟩

#check (toMvPoly _).functor

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B`. -/
def proj (P : UvPoly E B) (X : Over (⊤_ C)) :
  ((Π_ P.p).obj ((Δ_ (terminal.from E)).obj X)).left ⟶ B :=
  ((Δ_ (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

def auxFunctor (P : UvPoly E B) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor P.toMvPoly

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials. -/
def functor_alt (P : UvPoly E B) : C ⥤ C :=  equivOverTerminal.functor ⋙  P.auxFunctor ⋙ equivOverTerminal.inverse

-- (SH): The following definition might be more ergonomic but it assumes more, namely that the category `C` has binary products.
def functor [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C := Over.star E ⋙ Π_ P.p ⋙ Over.forget B

def functor_is_iso_functor_alt [HasBinaryProducts C] (P : UvPoly E B) : P.functor ≅ P.functor_alt := by
  unfold functor_alt auxFunctor functor MvPoly.functor



/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def proj' (P : UvPoly E B) (X : C) : (functor P).obj X ⟶ B :=
  ((Over.star E ⋙ Π_ P.p).obj X).hom



example [HasBinaryProducts C] (X  Y : C) : X ⨯  Y ⟶ X := prod.fst

#check Over.star -- Δ_ (prod.snd (X:= B) (Y:= E))

def functor' [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C := (Over.star E) ⋙ (Π_ P.p) ⋙ (Over.forget B)

/-- Evaluating a single variable polynomial at an object `X` -/
def apply (P : UvPoly E B) (X : C) : C := P.functor.obj X

variable (B)
/-- The identity polynomial functor in single variable. -/
@[simps!]
def id : UvPoly B B := ⟨𝟙 B, by infer_instance⟩

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `X` -/
def id_apply (X : C) : (id B).apply X ≅ X where
  hom := by
    simp [id, apply, functor]
    sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

variable {B}

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'` and `b : B ⟶ B'` such that the diagram
```
  E ---P.p--> B
  |          |
 e            b
  |          |
  v          v
  E' --Q.p--> B'
```
is a pullback square. -/
structure Hom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') where
  e : E ⟶ E'
  b : B ⟶ B'
  is_pullback : IsPullback P.p e b Q.p

namespace Hom

open IsPullback

-- baseChange.isLimitPullbackConeId _
def id (P : UvPoly E B) : Hom P P := ⟨𝟙 E, 𝟙 B, ⟨by aesop, ⟨ sorry ⟩⟩⟩

def comp {E' B' E'' B'' : C} {P : UvPoly E B} {Q : UvPoly E' B'} {R : UvPoly E'' B''} (f : Hom P Q) (g : Hom Q R) :
  Hom P R where
    e := f.e ≫ g.e
    b := f.b ≫ g.b
    is_pullback := paste_vert f.is_pullback g.is_pullback

end Hom


/-- Bundling up the all the polynomials over different bases to form the underlying type of the category of polynomials. -/
structure Total (C : Type*) [Category C] [HasPullbacks C] where
  (E B : C)
  (P : UvPoly E B)

end UvPoly

open UvPoly

/-- The category of polynomial functors in a single variable. -/
instance : Category (UvPoly.Total (C:= C)) where
  Hom P Q := UvPoly.Hom P.P Q.P
  id P := UvPoly.Hom.id P.P
  comp := UvPoly.Hom.comp
  id_comp := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  comp_id := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  assoc := by
    simp [UvPoly.Hom.comp]

namespace UvPoly

-- def toPair (P : UvPoly E B) (Γ : C) (X : C) :
--     (Γ ⟶ P.functor.obj X) → Σ b : Γ ⟶ B, pullback P.p b ⟶ X := by
--   intro be
--   fconstructor
--   · exact (be ≫ proj' P X)
--   ·


/-- The universal property of the polynomial functor.-/
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ B, pullback P.p b ⟶ X := sorry


/-- A map of polynomials induces a natural transformation between their associated functors. -/
def natural [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q): P.P.functor ⟶ Q.P.functor := by
  sorry

end UvPoly

end
