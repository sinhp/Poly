/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Sina Hazratpour
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Tactic.ApplyFun

import Poly.Basic
import Poly.Exponentiable

/-!
# Beck-Chevalley natural transformations and natural isomorphisms
-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans

universe v u

namespace Over
variable {C : Type u} [Category.{v} C]

section BeckChevalleyTransformations

theorem mapSquare_eq {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g = Over.map h ⋙ Over.map k := by
  rw [mapComp_eq, w, ← mapComp_eq]

/-- The Beck Chevalley transformations are iterated mates of this isomorphism.-/
def mapSquareIso {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k :=
  eqToIso (mapSquare_eq f g h k w)

-- Is this better or worse?
def mapSquareIso' {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k := by
  rw [mapSquare_eq]
  exact w

/-- The Beck-Chevalley natural transformation. -/
def pullbackBeckChevalleyNatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange h ⋙ Over.map f ⟶ Over.map k ⋙ baseChange g :=
  (mateEquiv (mapAdjunction h) (mapAdjunction g)) ((mapSquareIso f g h k w).hom)

def pullbackBeckChevalleyOfMap [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) : baseChange f ⋙ forget X ⟶ forget Y := by
  have := (mapForgetIso f).inv
  rw [← Functor.comp_id (forget X)] at this
  exact (mateEquiv (mapAdjunction f) (Adjunction.id)) (this)

/-- The conjugate isomorphism between the pullbacks along a commutative square. -/
def pullbackSquareIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange k ⋙ baseChange h ≅ baseChange g ⋙ baseChange f :=
  conjugateIsoEquiv ((mapAdjunction h).comp (mapAdjunction k)) ((mapAdjunction f).comp (mapAdjunction g)) (mapSquareIso f g h k w)

/-- The Beck-Chevalley natural transformations in a square of pullbacks and pushforwards.-/
def pushforwardBeckChevalleyNatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h)
     : gexp.functor ⋙ baseChange k ⟶ baseChange f ⋙ hexp.functor :=
  conjugateEquiv ((mapAdjunction k).comp gexp.adj) (hexp.adj.comp (mapAdjunction f)) (pullbackBeckChevalleyNatTrans f g h k w)

/-- The conjugate isomorphism between the pushforwards along a commutative square. -/
def pushforwardSquareIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (fexp : CartesianExponentiable f)
    (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h)
    (kexp : CartesianExponentiable k) :
    fexp.functor ⋙ gexp.functor ≅ hexp.functor ⋙ kexp.functor :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) (kexp.adj.comp hexp.adj) (pullbackSquareIso f g h k w)


end BeckChevalleyTransformations

end Over

section BeckChevalleyIsos

variable {C : Type u} [Category.{v} C]

open IsPullback Over

/-- Calculating the counit components of mapAdjunction. -/
theorem mapAdjunction.counit.app_pullback.fst  [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (y : Over Y) :
    ((mapAdjunction f).counit.app y).left = pullback.fst := by simp

def pullbackNatTrans.app.map [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).obj ((baseChange h ⋙ map f).obj y) ⟶ (forget X).obj ((map k ⋙ baseChange g).obj y) :=
  pullback.map y.hom h (y.hom ≫ k) g (𝟙 y.left) f k (Eq.symm (id_comp (y.hom ≫ k))) w.symm

theorem pullbackBeckChevalleyComponent_pullbackMap [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((pullbackBeckChevalleyNatTrans f g h k w).app y) = pullbackNatTrans.app.map f g h k w y := by
  dsimp
  ext <;> unfold pullbackNatTrans.app.map pullback.map
  · simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    dsimp [pullbackBeckChevalleyNatTrans, mateEquiv]
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_fst, ← assoc, pullback.lift_fst]
      }
    rw [mapAdjunction.counit.app_pullback.fst, ← assoc, ← assoc, pullback.lift_fst]
    unfold mapSquareIso
    simp
  · simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    dsimp [pullbackBeckChevalleyNatTrans, mateEquiv]
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_snd, ← assoc, pullback.lift_snd]
      }
    simp

-- NB: I seem to have symmetry of HasPullback but not IsPullback
-- SH: yes, we do have that: it is given by the function `.flip`
theorem pullbackNatTrans_of_IsPullback_component_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (y : Over Y) :
    IsIso ((forget X).map ((pullbackBeckChevalleyNatTrans f g h k pb.w).app y)) := by
  rw [pullbackBeckChevalleyComponent_pullbackMap f g h k pb.w y]
  have P := bigSquareIsPullback _ _ _ _ _ _ _ _ pb.w.symm (isLimit pb.flip) (pullbackIsPullback y.hom h)
  have Q := pullbackIsPullback (y.hom ≫ k) g
  let conemap : (PullbackCone.mk _ _
        (show (pullback.fst : pullback y.hom h ⟶ _) ≫ y.hom ≫ k = ((pullback.snd : pullback y.hom h ⟶ _) ≫ f) ≫ g by
          rw [← Category.assoc, pullback.condition (f := y.hom) (g := h), Category.assoc, pb.w.symm, Category.assoc])) ⟶ (PullbackCone.mk (pullback.fst : pullback (y.hom ≫ k) g ⟶ _) pullback.snd pullback.condition) := {
    hom := pullbackNatTrans.app.map f g h k pb.w y
    w := by
      rintro (_|(left|right)) <;>
      · unfold pullbackNatTrans.app.map
        simp
  }
  have mapiso := (IsLimit.hom_isIso P Q conemap)
  have dumb : conemap.hom = pullbackNatTrans.app.map f g h k pb.w y := by rfl
  rw [← dumb]
  exact ((Cones.forget _).map_isIso conemap)

/-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (pb : IsPullback f h g k)
     :
    IsIso (pullbackBeckChevalleyNatTrans f g h k pb.w) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro y
  have := pullbackNatTrans_of_IsPullback_component_is_iso f g h k pb y
  apply (forget_reflects_iso (X := X)).reflects
    ((pullbackBeckChevalleyNatTrans f g h k pb.w).app y)

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h) :
    IsIso (pushforwardBeckChevalleyNatTrans f g h k pb.w gexp hexp) := by
  have := pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso f g h k pb
  apply conjugateEquiv_iso

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleyNatTrans_of_isPullback_isIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h) :
    IsIso (pushforwardBeckChevalleyNatTrans f g h k pb.w gexp hexp) := by
  have := pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso f g h k pb
  apply conjugateEquiv_iso

end BeckChevalleyIsos
