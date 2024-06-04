/-
The plan for this file is to show that the category of presheaves on a (small) cat C is LCC, as follows:
(1) define the category of presheaves on a (small) cat C and show it is a CCC.
  [* apparently this has already been done *]
(2) the slice category over any presheaf is presheaves on its category of elements,
  [* the category of elements is already done, but not the equivalence *]
(3) infer that every slice of presheaves is a CCC,
  [* by transferring CCC across the foregoing equivalence *]
(4) use the results from the LCCC development to infer that presheaves is LCC.
  [* since every slice category is CC *]
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Comma.Presheaf
import Mathlib.CategoryTheory.Closed.Cartesian

namespace CategoryTheory

universe u v w

variable {C : Type*} [Category C]

/-!
# 1. Presheaves are a CCC
The category of presheaves on a small category is cartesian closed
-/

noncomputable section
open Category Limits Functor Adjunction Over Opposite Equivalence

abbrev Psh (C : Type*) [Category C] := Cᵒᵖ ⥤ Type*

/- Note (SH): In general `abbrev` works better with `simp` and istance inference. Another alternative is to use `notation`:
`notation "Psh" "(" C ")" => Cᵒᵖ ⥤ Type` -/

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := isLeftAdjointOfPreservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (Psh C) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := isLeftAdjointOfPreservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))
/-!
# 2. The (dual) category of elements
The category of elements of a *contravariant* functor P : Cᵒᵖ ⥤ Type is the opposite of the category of elements of the covariant functor P : Cᵒᵖ ⥤ Type.
The difference is seen in the projection OpEl(P) ⥤ C , versus El(P) ⥤ Cᵒᵖ.

Given a functor `P : Cᵒᵖ ⥤ Type`, an object of
`P.OpElements` is a pair `(X : C, x : P.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C` for which `P.map f` takes `y` back to `x`.

We show that (Elements P)ᵒᵖ is equivalent to the comma category Yoneda/P.
-/

--noncomputable section Elements

/-
The type of objects for the category of elements of a functor `P : Cᵒᵖ ⥤ Type` is the type of pairs `(X : Cᵒᵖ, x : P.obj X)`.
-/

-- def Functor.OpElements (P : Psh C) := (Functor.Elements P)ᵒᵖ --  Σ X : Cᵒᵖ, P.obj X

/-lemma Functor.OpElements.ext {P : Psh C} (x y : P.Elements) (h₁ : x.fst = y.fst)
  (h₂ : P.map (eqToHom h₁)  x.snd = y.snd) : x = y := by
    cases x
    cases y
    cases h₁
    simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
    simp [h₂]
-/
/-
The category structure on `P.OpElements`, for `P : Cᵒᵖ ⥤ Type`.  A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C` for which `F.map f` takes `y` back to `x`.
 -/

 /- instance categoryOfOpElements (P : Psh C) : Category (OpElements P) where
  Hom p q := { f : q.1 ⟶ p.1 // p.2 = P.map f q.2 } -- P is contravariant
  id p := ⟨𝟙 p.1, by aesop_cat⟩
  comp {p q r} f g := ⟨g.val ≫ f.val, by
    simp [f.2, g.2]
    apply Eq.trans
    apply f.2
    apply congr
    rfl
    apply g.2⟩

--abbrev OpElements (P : Psh C) := (Elements P)ᵒᵖ
--namespace CategoryTheory
-/

namespace CategoryOfElements
namespace Equivalence

--def elementsOpIsOpElements {P : Psh C} : (Elements P)ᵒᵖ ≌ (OpElements P) := sorry

/-!
The equivalence `(P.Elements)ᵒᵖ ≌ (yoneda, P)` given by the Yoneda lemma.
-/

def costructuredArrowYonedaEquivalenceOp (P : Psh C) :
    (Elements P)ᵒᵖ ≌ CostructuredArrow yoneda P :=
  Equivalence.mk (toCostructuredArrow P) (fromCostructuredArrow P).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq P))) (eqToIso <| to_fromCostructuredArrow_eq P)

def equivOp (C D : Type*)[Category C][Category D] : (C ≌ D) → (Cᵒᵖ ≌ Dᵒᵖ) := sorry

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

def overPshIsPshCostArrowYon {P : Psh C} :
  Over P ≌ Psh (CostructuredArrow yoneda P) := overEquivPresheafCostructuredArrow P

def overPshIsPshElementsOp {P : Psh C} :
  Over P ≌ Psh ((Elements P)ᵒᵖ) :=
  equivTrans overPshIsPshCostArrowYon pshCostArrowYonIsPshElementsOp

def pshElementsOpIsOverPsh {P : Psh C} :
  Psh ((Elements P)ᵒᵖ) ≌ Over P :=
  symm overPshIsPshElementsOp

/- there could be a problem here because Cᵒᵖᵒᵖ is not definitionally equal to C
In that case, maybe use this instead:

def overPshIsCovPshElements {P : Psh C} :
  Over P ≌ ((Elements P) ⥤ Type*) := sorry
-/

/-
The following two are used for the OpElements, but that doesn't seem to work:

def pshElementsOpIsPshOpElements {P : Psh C} :
   Psh ((Elements P)ᵒᵖ) ≌ Psh (OpElements P) :=
   equivPsh elementsOpIsOpElements

def overPshIsPshOpElements {P : Psh C} :
  Over P ≌ Psh (OpElements P) :=
  trans overPshIsPshElementsOp pshElementsOpIsPshOpElements
-/

/-!
# 4. The slice category Psh(C)/P is a CCC
-/
/-!
Now that we have (Psh C)/P ≃ Psh((Elements P)ᵒᵖ), use the following to transfer CCC across the equivalence, from: mathlib4/Mathlib/CategoryTheory/Closed/Cartesian.lean

def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D :=
  MonoidalClosed.ofEquiv (e.inverse.toMonoidalFunctorOfHasFiniteProducts) e.symm.toAdjunction
-/

def pshOverCCC {P : Psh C} : CartesianClosed (Over P) :=
  cartesianClosedOfEquiv pshElementsOpIsOverPsh

def allPshOverCCC {C : Type*} [Category C] : ∀ (P : Psh C) , CartesianClosed (Over P) := sorry
