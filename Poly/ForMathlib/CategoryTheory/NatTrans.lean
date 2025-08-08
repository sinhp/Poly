/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits IsPullback

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans

open Functor

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

theorem cartesian.comp_horizz {M N K : Type*}
  [Category M] [Category N] [Category K] {F G : J ⥤ C} {M N : C ⥤ K} {α : F ⟶ G} {β : M ⟶ N}
  (hα : cartesian α) (hβ : cartesian β)
  [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) M] :
    cartesian (NatTrans.hcomp α β) := by {
      have ha := cartesian.whiskerRight hα M
      have hb := cartesian.whiskerLeft hβ G
      have hc := cartesian.comp ha hb
      unfold cartesian
      intros i j f
      specialize hc f
      simp only [Functor.comp_obj, Functor.comp_map, comp_app,
        whiskerRight_app, whiskerLeft_app,
        naturality] at hc
      exact hc
    }

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

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

open TwoSquare in
theorem cartesian_vComp {w : TwoSquare T L R B} {w' : TwoSquare B L' R'' B''}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) R''] :
    cartesian w → cartesian w' → cartesian (w ≫ᵥ w') :=
  fun cw cw' =>
    (cartesian_of_isIso _).comp <|
    (cartesian.whiskerRight cw _).comp <|
    (cartesian_of_isIso _).comp <|
    (cartesian.whiskerLeft cw' _).comp <|
    (cartesian_of_isIso _)

open TwoSquare in
theorem cartesian_hComp {w : TwoSquare T L R B} {w' : TwoSquare T' R R' B'}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) B'] :
    cartesian w → cartesian w' → cartesian (w ≫ₕ w') :=
  fun cw cw' =>
    (cartesian_of_isIso _).comp <|
    (cartesian.whiskerLeft cw' _).comp <|
    (cartesian_of_isIso _).comp <|
    (cartesian.whiskerRight cw _).comp <|
    (cartesian_of_isIso _)

end NatTrans

open NatTrans

theorem mapPair_cartesian {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') : cartesian α :=
  cartesian_of_discrete α
