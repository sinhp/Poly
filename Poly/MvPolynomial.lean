/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.LCCC.BeckChevalley


/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`CartesianExponentiable` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I`,
output variables in `O`, and with arities `E` dependent on `I`. -/
structure MvPoly (I O : C) where
  (E B : C)
  (i : E ⟶ I)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)
  (o : B ⟶ O)

namespace MvPoly

open CartesianExponentiable

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

attribute [instance] MvPoly.exp

/-- The identity polynomial in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, CartesianExponentiable.id, 𝟙 I⟩

instance (I : C) : CartesianExponentiable ((id I).p) := CartesianExponentiable.id



-- let's prove that the pullback along `initial.to` is isomorphic to the initial object
example [HasInitial C] {X Y : C} (f : Y ⟶ X) :
    IsPullback (initial.to Y) (𝟙 _) f (initial.to X) where
      w := by aesop
      isLimit' := by
        refine ⟨?_⟩
        sorry


/-- Given an object `X`, The unique map `initial.to X : ⊥_ C ⟶ X ` is exponentiable. -/
instance [HasInitial C] (X : C) : CartesianExponentiable (initial.to X) where
  functor := {
    obj := sorry
    map := sorry
  }
  adj := sorry


/-- The constant polynomial in many variables: for this we need the initial object. -/
def const {I O : C} [HasInitial C] (A : C) [HasBinaryProduct O A] : MvPoly I O :=
  ⟨⊥_ C, prod O A, initial.to I , initial.to _, inferInstance, prod.fst⟩

/-- The monomial polynomial in many variables. -/
def monomial {I O E : C} (i : E ⟶ I) (p : E ⟶ O) [CartesianExponentiable p]: MvPoly I O :=
  ⟨E, O, i, p, inferInstance, 𝟙 O⟩

/-- The sum of two polynomials in many variables. -/
def sum {I O : C} [HasBinaryCoproducts C] (P Q : MvPoly I O) : MvPoly I O where
  E := P.E ⨿ Q.E
  B := P.B ⨿ Q.B
  i := coprod.desc P.i Q.i
  p := coprod.map P.p Q.p
  exp := {
    functor := sorry  -- prove that the sum of exponentiables is exponentiable.
    adj := sorry
  }
  o := coprod.desc P.o Q.o

/-- The product of two polynomials in many variables. -/
def prod {I O : C} [HasBinaryProducts C] (P Q : MvPoly I O) : MvPoly I O :=
  sorry

def functor {I O : C} (P : MvPoly I O) :
    Over I ⥤ Over O :=
  (Δ_ P.i) ⋙ (Π_ P.p) ⋙ (Σ_ P.o)

variable (I O : C) (P : MvPoly I O)

def apply {I O : C} (P : MvPoly I O) [CartesianExponentiable P.p] : Over I → Over O := (P.functor).obj

/-TODO: write a coercion from `MvPoly` to a functor for evaluation of polynomials at a given
object.-/

def id_apply (q : X ⟶ I) : (id I).apply (Over.mk q) ≅ Over.mk q where
  hom := by
    simp [apply]
    simp [functor]
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

-- TODO: The set of connected components of el(P) is in bijection with the set P(1) ≅ A

section Composition

variable {I}

variable {J K : C}

variable (P : MvPoly I J) (Q : MvPoly J K)

def pullback_counit :
    (Δ_ Q.p).obj  ((Π_ Q.p).obj (Over.mk <| pullback.snd P.o Q.i)) ⟶ (Over.mk <| pullback.snd P.o Q.i) :=
  adj.counit.app _

def comp (P: MvPoly I J) (Q : MvPoly J K) : MvPoly I K := sorry

end Composition

end MvPoly

end
