/-
The plan for this file is to show that the category of presheaves on a (small) cat C is LCC, as follows:
(1) define the category of presheaves on a (small) cat C and show it is a CCC,
  [* apparently this has already been done *]
(2) the slice category over any presheaf is presheaves on its category of elements,
  [* the category of elements is already done, but not the equivalence *]
(3) infer that every slice of presheaves is a CCC,
(4) use the results from the LCCC development to infer that presheaves is LCC.
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
--import Mathlib.CategoryTheory.Comma.StructuredArrow

/-!
# Presheaves are a CCC
The category of presheaves on a small category is cartesian closed
-/

noncomputable section

open CategoryTheory Functor Adjunction Over Opposite

universe w v u

variable {C : Type*} [Category C]

/- Question: how can we define the notation Psh C in place of (Cᵒᵖ ⥤ Type u) ? -/
/- Answer: -/
/- Note (SH): In general `abbrev` works better with `simp` and istance inference. Another alternative is to use `notation`. -/
abbrev Psh (C : Type*) [Category C] := Cᵒᵖ ⥤ Type
/- Alternative: `notation "Psh" "(" C ")" => Cᵒᵖ ⥤ Type` -/

/-!
# The dual category of elements
The category of elements of a contravariant functor P : Psh Cs the opposite of the category of elements of the covariant functor P : Cᵒᵖ ⥤ Type.

Given a functor `P : Cᵒᵖ ⥤ Type`, an object of
`P.OpElements` is a pair `(X : C, x : P.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C` for which `P.map f` takes `y` back to `x`.

P.OpElements is equivalent to the comma category Yoneda/P.
-/

noncomputable section Elements

/--
The type of objects for the category of elements of a functor `P : Cᵒᵖ ⥤ Type` is the type of pairs `(X : Cᵒᵖ, x : P.obj X)`.
-/

def Functor.OpElements (P : Psh C) :=
(Functor.Elements P) --  Σ X : Cᵒᵖ, P.obj X

lemma Functor.OpElements.ext {P : Psh C} (x y : P.Elements) (h₁ : x.fst = y.fst)
  (h₂ : P.map (eqToHom h₁)
    x.snd = y.snd) : x = y := by
    cases x
    cases y
    cases h₁
    simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
    simp [h₂]

/--
The category structure on `P.OpElements`, for `P : Cᵒᵖ ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `y` to `x`.
 -/

 instance categoryOfOpElements (P : Psh C) : Category (OpElements P) where
  Hom p q := { f : q.1 ⟶ p.1 // p.2 = P.map f q.2 }
  id p := ⟨𝟙 p.1, by aesop_cat⟩
  comp {p q r} f g := ⟨g.val ≫ f.val, by
    simp [f.2, g.2]
    apply Eq.trans
    apply f.2
    apply congr
    rfl
    apply g.2⟩

namespace CategoryTheory
namespace CategoryOfElements

/-- The equivalence `P.OpElements ≅ (yoneda, P)` given by the Yoneda lemma. -/

/- there's still a mismatch here, since (Functor.Elements P)ᵒᵖ should be the same as (Functor.OpElements P), but apparently isn't definitionally equal-/

def costructuredArrowYonedaEquivalenceOp (P : Psh C) :
    (Functor.Elements P)ᵒᵖ ≌ CostructuredArrow yoneda P :=
  Equivalence.mk (toCostructuredArrow P) (fromCostructuredArrow P).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq P))) (eqToIso <| to_fromCostructuredArrow_eq P)


/-
next: - show that OpElements P ≃ (Yoneda, P) implies Psh(OpElements P) ≃ Psh(Yoneda, P)
  - show that Psh C/P ≃ Psh(Yoneda, P).
  - infer that Psh C/P ≃ Psh(OpElements P)
  - then use the following to transfer CCC across the equivalence

variable {D : Type u₂} [Category.{v} D]

copied from: mathlib4/Mathlib/CategoryTheory/Closed
/Cartesian.lean

universe v u u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] monoidalOfHasFiniteProducts

...

section Functor

variable [HasFiniteProducts D]

/-- Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D :=
  MonoidalClosed.ofEquiv (e.inverse.toMonoidalFunctorOfHasFiniteProducts) e.symm.toAdjunction
#align category_theory.cartesian_closed_of_equiv CategoryTheory.cartesianClosedOfEquiv

end Functor

attribute [nolint simpNF] CategoryTheory.CartesianClosed.homEquiv_apply_eq
  CategoryTheory.CartesianClosed.homEquiv_symm_apply_eq
end CategoryTheory
-/
