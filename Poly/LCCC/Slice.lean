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
@[ext]
structure Slice (X : C) : Type max u v where
  dom : C
  hom : dom ⟶ X

-- Satisfying the inhabited linter -- ER: What is this?
instance Slice.inhabited [Inhabited C] : Inhabited (Slice (C := C) default) where
  default :=
    { dom := default
      hom := 𝟙 default }

structure SliceMorphism' {X : C}(A : C) (f : A ⟶ X) (B : C) (g : B ⟶ X) where
  dom : A ⟶ B
  w : dom ≫ g = f := by aesop_cat -- What is this?

-- Generates SliceMorphism.ext; see a test below
@[ext]
structure SliceMorphism {X : C}(f g : Slice X) where
  dom : f.dom ⟶ g.dom
  w : dom ≫ g.hom = f.hom := by aesop_cat -- What is this?

instance sliceCategory' (X : C) : Category (Slice X) where
  Hom f g := { dom : f.dom ⟶ g.dom // dom ≫ g.hom = f.hom }
  id f := {
    val := 𝟙 f.dom
    property := by aesop_cat
  }
  comp {f g h : Slice X} u v := {
    val := u.val ≫ v.val
    property := by rw [assoc, v.property, u.property]
  }

-- instance sliceCategory (X : C) : Category (Slice X) where
--   Hom f g := SliceMorphism f g
--   id f := {
--     dom := 𝟙 f.dom
--   }
--   comp {f g h : Slice X} u v := {
--     dom := u.dom ≫ v.dom
--     w := by rw [assoc, v.w, u.w]
--   }
-- #align category_theory.slice_category CategoryTheory.sliceCategory

-- Test of SliceMorphism.ext
-- theorem test {X : C} {f g : Slice X} {u v : f ⟶ g}
--     (h : u.dom = v.dom) : u = v := by
--   apply SliceMorphism.ext
--   exact h

@[simps]
def project (X : C) : (Slice X) ⥤ C where
  obj f := f.dom
  map u := u.val

def compFunctor {X Y : C} (f : X ⟶ Y) : (Slice X) ⥤ (Slice Y) where
  obj x := {
    dom := x.dom
    hom := x.hom ≫ f
  }
  map {x x' : Slice X} u := {
    val := u.val
    property := by rw [← assoc, u.property]
  }

theorem compProject {X Y : C} (f : X ⟶ Y) : 
    compFunctor f ⋙ project Y = project X := by 
  show ({..} : Slice _ ⥤ _) = {..}
  congr

theorem compFunctorial.comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    compFunctor f ⋙ compFunctor g = compFunctor (f ≫ g) := by
  have : ∀ D : Slice X → C, 
      
    ∀ F G : Slice X ⥤ Slice Z,
      (D = fun x => (F.obj x).dom) →  
      (D' = fun x => (G.obj x).dom) →
      (∀ x, HEq (F.obj x).hom (G.obj x).hom) →
      (∀ A B (h : A ⟶ B), HEq (F.map h).1 (G.map h).1) →
      F = G := by
    rintro _ _ eq1 ⟨F_obj, F_map⟩ ⟨G_obj, G_map⟩ eq2 eq3 h1 h2
    have h : F_obj = G_obj := by
      congr
      ext x
      · exact congrFun (eq2.symm.trans <| eq1.trans eq3) _
      
      exact fun x => eq_of_heq (h1 x)
    cases h; rfl
  apply this _ _ rfl _ _ rfl rfl
  · intro x 
    simp [compFunctor]
  · intros
    simp [compFunctor]
  
  let T (s : Slice X) := (s.hom ≫ f) ≫ g
  show ({obj := _, ..} : Slice _ ⥤ Slice _) = {..}
  dsimp [compFunctor]
  show ({
    obj := fun x => ({hom := T x, ..} : Slice _),
    map := fun {X Y} f => ({..} : Subtype _),
    ..} : Slice _ ⥤ Slice _) = {..}
  dsimp
  suffices ∀ T : (s : Slice X) → s.dom ⟶ Z,
    ({ obj := fun x ↦ { dom := x.dom, hom := T x }, map := fun {X_1 Y_1} f_1 ↦ ⟨f_1.1, _⟩, map_id := _, map_comp := _ } : Slice X ⥤ Slice Z) =
    { obj := fun x ↦ { dom := x.dom, hom := x.hom ≫ f ≫ g }, map := fun {x x'} u ↦ ⟨u.1, _⟩, map_id := _, map_comp := _ } by
    convert this T
  clear_value T
  congr
  · refine funext ?e_toPrefunctor.h.e_5.h.h
    intro x
    show ({.. } : Slice _) = {..}
    congr 1
    rw [assoc]
  · dsimp
    have : ({X_1 Y_1 : Slice X} → (X_1 ⟶ Y_1) → { dom // dom ≫ (Y_1.hom ≫ f) ≫ g = (X_1.hom ≫ f) ≫ g }) =
      ({x x' : Slice X} → (x ⟶ x') → { dom // dom ≫ x'.hom ≫ f ≫ g = x.hom ≫ f ≫ g }) := sorry
    
    apply heq_iff_eq.2

    apply Sigma.ext

    unfold compFunctor
    ext

    refine Function.hfunext rfl ?e_toPrefunctor.h.e_6.h
    intro x x' prf
    refine Function.hfunext rfl ?e_toPrefunctor.h.e_6.h.h
    intro y y' prf'



  -- show ({obj := {..}, ..} : Comma _ _ ⥤ Comma _ _ ) = {..}
  -- congr 2
  -- rfl

-- theorem Over.postComp.square {W X Y Z : C}
--     (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (w : f ≫ g = h ≫ k) :
--     Over.map f ⋙ Over.map g = Over.map h ⋙ Over.map k := by
--   sorry
