/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-!
# Slice categories from scratch
-/

namespace CategoryTheory

open Category Functor

universe v u

variable {C : Type u} [Category.{v} C]

-- ER: What does structure mean?
structure Slice (X : C) : Type max u v where
  dom : C
  hom : dom ⟶ X

-- Satisfying the inhabited linter -- ER: What is this?
instance Slice.inhabited [Inhabited C] : Inhabited (Slice (C := C) default) where
  default :=
    { dom := default
      hom := 𝟙 default }

-- Generates SliceMorphism.ext; see a test below
@[ext]
structure SliceMorphism {X : C}(f g : Slice X) where
  dom : f.dom ⟶ g.dom
  w : dom ≫ g.hom = f.hom := by aesop_cat -- What is this?

instance sliceCategory (X : C) : Category (Slice X) where
  Hom f g := SliceMorphism f g
  id f := {
    dom := 𝟙 f.dom
  }
  comp {f g h : Slice X} u v := {
    dom := u.dom ≫ v.dom
    w := by rw [assoc, v.w, u.w]
  }
#align category_theory.slice_category CategoryTheory.sliceCategory

-- Test of SliceMorphism.ext
theorem test {X : C} {f g : Slice X} {u v : f ⟶ g}
    (h : u.dom = v.dom) : u = v := by
  apply SliceMorphism.ext
  exact h

@[simps]
def project (X : C) : (Slice X) ⥤ C where
  obj f := f.dom
  map u := u.dom

def compFunctor {X Y : C} (f : X ⟶ Y) : (Slice X) ⥤ (Slice Y) where
  obj x := {
    dom := x.dom
    hom := x.hom ≫ f
  }
  map {x x' : Slice X} u := {
    dom := u.dom
    w := by rw [← assoc, u.w]
  }

theorem compFunctorial.comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    compFunctor f ⋙ compFunctor g = compFunctor (f ≫ g) := by
  dsimp [sliceCategory, Functor.comp, compFunctor]
  congr! 4
  · rw [assoc]
  · subst_vars
    congr! 3 <;> rw [assoc]

  -- show ({obj := {..}, ..} : Comma _ _ ⥤ Comma _ _ ) = {..}
  -- congr 2
  -- rfl

-- theorem Over.postComp.square {W X Y Z : C}
--     (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (w : f ≫ g = h ≫ k) :
--     Over.map f ⋙ Over.map g = Over.map h ⋙ Over.map k := by
--   sorry
