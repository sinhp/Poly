/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category

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

structure UnpackedSliceFunctor (D) [Category D] (X) where
  dom : D → C
  hom (a) : dom a ⟶ X
  map {a b : D} : (a ⟶ b) → (dom a ⟶ dom b)

def unpackSliceFunctor {D} [Category D] {X : C} (F : D ⥤ Slice X) : UnpackedSliceFunctor D X where
  dom := fun x => (F.obj x).dom
  hom := fun x => (F.obj x).hom
  map := fun f => (F.map f).1

theorem unpackSliceFunctor.inj {D} [Category D] {X : C} {F G : D ⥤ Slice X}
    (eq : unpackSliceFunctor F = unpackSliceFunctor G) : F = G :=
  let f (F : D ⥤ Slice X) : { F : UnpackedSliceFunctor D X //
    (∀ {x x' : D} (u : x ⟶ x'), F.map u ≫ F.hom x' = F.hom x) ∧
    (∀ X, F.map (𝟙 X) = 𝟙 (F.dom X)) ∧
    (∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), F.map (f ≫ g) = F.map f ≫ F.map g) } :=
  ⟨unpackSliceFunctor F,
    fun u => (F.map u).2,
    fun X => (SliceMorphism.ext_iff ..).1 (F.map_id X),
    fun f g => (SliceMorphism.ext_iff ..).1 (F.map_comp f g)⟩
  let g F : D ⥤ Slice X := {
    obj := fun x => ⟨F.1.dom x, F.1.hom x⟩
    map := fun x => ⟨F.1.map x, F.2.1 x⟩
    map_id := fun x => (SliceMorphism.ext_iff ..).2 (F.2.2.1 x)
    map_comp := fun f g => (SliceMorphism.ext_iff ..).2 (F.2.2.2 f g)
  }
  (show Function.LeftInverse g f from fun _ => rfl).injective (Subtype.ext eq)

theorem compFunctorial.comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    compFunctor f ⋙ compFunctor g = compFunctor (f ≫ g) := by
  apply unpackSliceFunctor.inj
  dsimp [unpackSliceFunctor]
  congr 1; ext x
  dsimp [compFunctor]
  rw [assoc]


  -- show ({obj := {..}, ..} : Comma _ _ ⥤ Comma _ _ ) = {..}
  -- congr 2
  -- rfl

-- theorem Over.postComp.square {W X Y Z : C}
--     (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (w : f ≫ g = h ≫ k) :
--     Over.map f ⋙ Over.map g = Over.map h ⋙ Over.map k := by
--   sorry
