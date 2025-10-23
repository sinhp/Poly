/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Elements

namespace CategoryTheory.CategoryOfElements

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
variable (F : 𝒞 ⥤ Type*) (G : F.Elements ⥤ 𝒟)

-- FIXME(mathlib): `NatTrans.mapElements` and `CategoryOfElements.map` are the same thing

@[simp]
theorem map_homMk_id {X : 𝒞} (a : F.obj X) (eq : F.map (𝟙 X) a = a) :
    -- NOTE: without `α := X ⟶ X`, a bad discrimination tree key involving `⟨X, a⟩.1` is generated.
    G.map (Subtype.mk (α := X ⟶ X) (𝟙 X) eq) = 𝟙 (G.obj ⟨X, a⟩) :=
  show G.map (𝟙 _) = 𝟙 _ by simp

@[simp]
theorem map_homMk_comp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) eq :
    G.map (Y := ⟨Z, F.map g (F.map f a)⟩) (Subtype.mk (α := X ⟶ Z) (f ≫ g) eq) =
    G.map (X := ⟨X, a⟩) (Y := ⟨Y, F.map f a⟩) (Subtype.mk (α := X ⟶ Y) f rfl) ≫
    G.map (Subtype.mk g rfl) := by
  set X : F.Elements := ⟨X, a⟩
  set Y : F.Elements := ⟨Y, F.map f a⟩
  set Z : F.Elements := ⟨Z, F.map g (F.map f a)⟩
  set f : X ⟶ Y := ⟨f, rfl⟩
  set g : Y ⟶ Z := ⟨g, rfl⟩
  show G.map (f ≫ g) = G.map f ≫ G.map g
  simp

end CategoryTheory.CategoryOfElements
