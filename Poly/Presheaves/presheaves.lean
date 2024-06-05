/-
The category of presheaves on a (small) cat C is an LCCC:
(1) the category of presheaves on a (small) cat C is a CCC.
(2) the category of elements of a presheaf P the comma category (yoneda, P)
(3) the slice of presheaves over P is presheaves on (yoneda, P).
(4) so every slice is a CCC by (1).
(5) use the results on LCCCs to infer that presheaves is LCC.
-/

import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/- the rest of these are apparently dependent on the above -/
--import Mathlib.CategoryTheory.Yoneda
--import Mathlib.CategoryTheory.Category.Basic
--import Mathlib.CategoryTheory.Closed.Monoidal
--import Mathlib.CategoryTheory.Closed.Cartesian
--import Mathlib.CategoryTheory.Adjunction.Mates
--import Mathlib.CategoryTheory.Adjunction.Over
--import Mathlib.CategoryTheory.Opposites
--import Mathlib.CategoryTheory.Elements
--import Mathlib.CategoryTheory.Equivalence
--import Mathlib.CategoryTheory.Comma.Presheaf
--import Mathlib.CategoryTheory.Closed.Cartesian

namespace CategoryTheory

universe u v w

variable {C : Type*} [Category C]

open Category Limits Functor Adjunction Over Opposite Equivalence

/-!
# 1. Presheaves are a CCC
The category of presheaves on a small category is cartesian closed
-/

noncomputable section

@[simp]
abbrev Psh (C : Type*) [SmallCategory C] := Cᵒᵖ ⥤ Type*
/- Note (SH): In general `abbrev` works better with `simp` and instance inference. Another alternative is to use `notation`: `notation "Psh" "(" C ")" => Cᵒᵖ ⥤ Type`
-/

def diagCCC (C : Type v₁) [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := isLeftAdjointOfPreservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

def pshCCC {C : Type v₁} [SmallCategory C] : CartesianClosed (Psh C) :=
  diagCCC (Cᵒᵖ)

/-!
# 2. The category of elements
The category of elements of a *contravariant* functor P : Cᵒᵖ ⥤ Type is the opposite of the category of elements of P regarded as a covariant functor P : Cᵒᵖ ⥤ Type.  Thus an object of `(Elements P)ᵒᵖ` is a pair `(X : C, x : P.obj X)` and a morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C` for which `P.map f` takes `y` back to `x`.
We have an equivalence (Elements P)ᵒᵖ ≌ (yoneda, P).
In MathLib the comma category is called the ``costructured arrow category''.
-/

namespace CategoryOfElements

def costructuredArrowYonedaEquivalenceOp (P : Psh C) :
  (Elements P)ᵒᵖ ≌ CostructuredArrow yoneda P :=
    Equivalence.mk (toCostructuredArrow P) (fromCostructuredArrow P).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq P))) (eqToIso <| to_fromCostructuredArrow_eq P)

def equivOp (C D : Type*)[Category C][Category D] : (C ≌ D) → (Cᵒᵖ ≌ Dᵒᵖ) := fun e => op e

def equivSymm (C D : Type*)[Category C][Category D] : (C ≌ D) → (D ≌ C) := symm

def equivTrans {C D E : Type*}[Category C][Category D][Category E] (d : C ≌ D) (e : D ≌ E) :
 (C ≌ E) := trans d e

def equivPsh {C D : Type*} [Category C][Category D] :
  (C ≌ D) → (Psh C ≌ Psh D) := by
  intro e
  apply congrLeft
  apply equivOp
  apply e

def pshElementsOpIsPshCostArrowYon (P : Psh C) :
  Psh (Elements P)ᵒᵖ ≌ Psh (CostructuredArrow yoneda P) := by
  apply equivPsh
  apply costructuredArrowYonedaEquivalenceOp

def pshCostArrowYonIsPshElementsOp {P : Psh C} :
  Psh (CostructuredArrow yoneda P) ≌ Psh ((Elements P)ᵒᵖ) :=
  symm (pshElementsOpIsPshCostArrowYon P)

/-!
# 3. The slice category of presheaves
The slice category (Psh C)/P  is called the "over category" in MathLib and written "Over P".
-/

def overPshIsPshCostArrowYon {P : Psh C} : Over P ≌ Psh (CostructuredArrow yoneda P) :=
 overEquivPresheafCostructuredArrow P

def overPshIsPshElementsOp {P : Psh C} : Over P ≌ Psh ((Elements P)ᵒᵖ) :=
  equivTrans overPshIsPshCostArrowYon pshCostArrowYonIsPshElementsOp

def pshElementsOpIsOverPsh {P : Psh C} : Psh ((Elements P)ᵒᵖ) ≌ Over P :=
  symm overPshIsPshElementsOp

/-!
# 4. The slice category Psh(C)/P is a CCC
We can transfer the CCC structure across the equivalence (Psh C)/P ≃ Psh((Elements P)ᵒᵖ) using the following:

def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D := MonoidalClosed.ofEquiv (e.inverse.toMonoidalFunctorOfHasFiniteProducts) e.symm.toAdjunction
-/

def pshOverCCC (P : Psh C) : CartesianClosed (Over P) :=
  cartesianClosedOfEquiv pshElementsOpIsOverPsh

def allPshOverCCC : Π (P : Psh C), CartesianClosed (Over P) :=
  fun P => (pshOverCCC P)

/-!
# 5. Presheaves is an LCCC
Use results on locally cartesian closed categories.
-/
