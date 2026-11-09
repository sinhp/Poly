/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Elements

namespace CategoryTheory.CategoryOfElements

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
variable (F : 𝒞 ⥤ Type*) (G : F.Elements ⥤ 𝒟)

@[simp]
theorem map_homMk_id {X : 𝒞} (a : F.obj X) (eq : F.map (𝟙 X) a = a) :
    G.map (X := F.elementsMk X a) (Y := F.elementsMk X a)
      (Functor.Elements.homMk (𝟙 X) eq) = 𝟙 (G.obj (F.elementsMk X a)) :=
  show G.map (𝟙 _) = 𝟙 _ by simp

@[simp]
theorem map_homMk_comp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) eq :
    G.map (X := F.elementsMk X a) (Y := F.elementsMk Z (F.map g (F.map f a)))
      (Functor.Elements.homMk (f ≫ g) eq) =
    G.map (X := F.elementsMk X a) (Y := F.elementsMk Y (F.map f a))
      (Functor.Elements.homMk f rfl) ≫
    G.map (Functor.Elements.homMk g rfl) := by
  set X : F.Elements := F.elementsMk X a
  set Y : F.Elements := F.elementsMk Y (F.map f a)
  set Z : F.Elements := F.elementsMk Z (F.map g (F.map f a))
  set f : X ⟶ Y := ⟨f, rfl⟩
  set g : Y ⟶ Z := ⟨g, rfl⟩
  show G.map (f ≫ g) = G.map f ≫ G.map g
  simp

end CategoryTheory.CategoryOfElements
