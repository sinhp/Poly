/-
Preamble copied and modified from LCCC.lean
-/

/-
Here's a plan for this file to show that the category of presheaves on a (small) cat C is LCC:
(1) define the category of presheaves on a (small) cat C and show it is a CCC,
(2) the slice category over any presheaf is presheaves on its category of elements,
(3) infer that every slice of presheaves is a CCC,
(4) use the results from the LCCC development to infer that presheaves is LCC.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Elements

-- All the imports below are transitively imported by the above import.
-- import Mathlib.CategoryTheory.Adjunction.Basic
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
-- import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Adjunction.Limits
-- import Mathlib.CategoryTheory.Functor
-- import Mathlib.CategoryTheory.Products.Basic
-- import Mathlib.Data.ULift

/-!
# Presheaves
-/

noncomputable section

open CategoryTheory Functor Adjunction Over Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

/- the category of presheaves on a small category is cartesian closed -/

#check CartesianClosed (Cᵒᵖ ⥤ Type u)

section Elements

-- variable (X : Cᵒᵖ ⥤ Type u)

def Functor.OpElements {X : Cᵒᵖ ⥤ Type w} :=
  Σ c : Cᵒᵖ, X.obj c

lemma Functor.OpElements.ext {X : Cᵒᵖ ⥤ Type w} (x y : OpElements) (h₁ : x.fst = y.fst) (h₂ : X.map (eqToHom h₁) x.snd = y.snd) : x = y := by
cases x
cases y
cases h₁
simp [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
simp [h₂]

instance categoryOfOpElements (X : Cᵒᵖ ⥤ Type w) : Category.{v} (X.Elements) where
  Hom a b := { f : a.1 ⟶ b.1 // (X.map f) a.2 = b.2 }
  id a := ⟨𝟙 a.1, by aesop_cat⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩
