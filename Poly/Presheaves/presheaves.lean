
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
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Elements

/-!
# Presheaves
-/

noncomputable section

open CategoryTheory Functor Adjunction Over Opposite

universe u v w

variable {C : Type u} [Category.{u} C]

/- the category of presheaves on a small category is cartesian closed -/

#check CartesianClosed (Cᵒᵖ ⥤ Type u)

/-!
# Category of Elements
The Category of Elements of a contravariant functor
-/
noncomputable section Elements

-- variable {C : Type u} [Category.{u} C]

/- The category of elements of a contravariant functor X : Cᵒᵖ ⥤ Type is the opposite of the category of elements of the opposite functor Xᵒᵖ : C ⥤ Typeᵒᵖ. -/

def Functor.OpElements {X : Cᵒᵖ ⥤ Type u} :=
(Functor.Elements X)ᵒᵖ --  Σ c : Cᵒᵖ, X.obj c

lemma Functor.OpElements.ext {X : Cᵒᵖ ⥤ Type u} (x y : OpElements) (h₁ : (unop x).fst = (unop y).fst)
  (h₂ : X.map (eqToHom h₁)
    (unop x).snd = (unop y).snd) : x = y := by
sorry

instance categoryOfOpElements (X : Cᵒᵖ ⥤ Type u) : Category.{u} (X.Elements) where
  Hom a b := { f : a.1 ⟶ b.1 // (X.map f) a.2 = b.2 }
  id a := ⟨𝟙 a.1, by aesop_cat⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩


/- use this to transfer CCC across an equivalence
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
