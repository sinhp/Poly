/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits IsPullback

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans

/-- A natural transformation is cartesian if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def cartesian {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

theorem cartesian_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : cartesian α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩

theorem isIso_of_cartesian [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G) (hα : cartesian α)
    [IsIso (α.app (⊤_ J))] : IsIso α := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α
    (fun j ↦ isIso_snd_of_isIso <| hα <| terminal.from j)

theorem cartesian.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : cartesian α)
    (hβ : cartesian β) : cartesian (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

theorem cartesian.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : cartesian α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    cartesian (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

theorem cartesian.whiskerLeft {K : Type*} [Category K]  {F G : J ⥤ C} {α : F ⟶ G}
    (hα : cartesian α) (H : K ⥤ J) : cartesian (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem cartesian_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : cartesian α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

theorem cartesian_of_isPullback_to_terminal [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G)
    (pb : ∀ j,
    IsPullback (F.map (terminal.from j)) (α.app j) (α.app (⊤_ J)) (G.map (terminal.from j))) :
    cartesian α := by
  intro i j f
  apply IsPullback.of_right (h₁₂ := F.map (terminal.from j)) (h₂₂ := G.map (terminal.from j))
  simpa [← F.map_comp, ← G.map_comp]  using (pb i)
  exact α.naturality f
  exact pb j


end NatTrans

open NatTrans

theorem mapPair_cartesian {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') : cartesian α :=
  cartesian_of_discrete α
