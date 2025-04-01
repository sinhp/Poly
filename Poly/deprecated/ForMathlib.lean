/-
Copyright (c) 2024 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-! Lemmas that should possibly be in mathlib.
Do *not* introduce new definitions here. -/

/-! ## Over categories -/

namespace CategoryTheory.Over

variable {C : Type*} [Category C]

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
lemma homMk_comp {B : C} {U V W : Over B} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (fg_comp f_comp g_comp) :
    homMk (f ≫ g) fg_comp = homMk (V := V) f f_comp ≫ homMk (U := V) g g_comp := by
  ext; simp

@[simp]
lemma left_homMk {B : C} {U V : Over B} (f : U ⟶ V) (h) :
    homMk f.left h = f := by
  rfl

end CategoryTheory.Over

/-! ## ChosenFiniteProducts.ofFiniteProducts

Simplify monoidal structure coming from `HasFiniteProducts` into `prod.foo`.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Cartesian.20closed.20Monoidal.20categories.2E
-/

namespace CategoryTheory.ChosenFiniteProducts
open Limits MonoidalCategory

variable {C : Type*} [Category C] [HasFiniteProducts C]

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

@[simp]
theorem ofFiniteProducts_fst (X Y : C) : fst X Y = prod.fst := by
  rfl

@[simp]
theorem ofFiniteProducts_snd  (X Y : C) : snd X Y = prod.snd := by
  rfl

@[simp]
theorem ofFiniteProducts_whiskerLeft {Y Z : C} (X : C) (f : Y ⟶ Z) :
    X ◁ f = prod.map (𝟙 X) f := by
  ext <;> simp [↓whiskerLeft_fst, ↓whiskerLeft_snd]

@[simp]
theorem ofFiniteProducts_whiskerRight {X Y : C} (Z : C) (f : X ⟶ Y) :
    f ▷ Z = prod.map f (𝟙 Z) := by
  ext <;> simp [↓whiskerRight_fst, ↓whiskerRight_snd]

namespace CategoryTheory.ChosenFiniteProducts
