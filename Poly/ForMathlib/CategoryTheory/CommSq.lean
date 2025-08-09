/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.CommSq

namespace CategoryTheory.Functor

theorem reflect_commSq
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Functor.Faithful F]
    {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {i : Z ⟶ W} :
    CommSq (F.map f) (F.map g) (F.map h) (F.map i) →
    CommSq f g h i := by
  intro cs
  constructor
  apply Functor.map_injective F
  simpa [← Functor.map_comp] using cs.w

end CategoryTheory.Functor
