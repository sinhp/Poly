/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

-- import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Whiskering

import Mathlib.Tactic.ApplyFun

import Poly.Exponentiable
import Poly.TempMates -- Contains an open mathlib PR redoing the mates file

/-!
# Beck-Chevalley natural transformations and natural isomorphisms
-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans

universe v u
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section NaturalityOfWhiskering

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable {F G : A ⥤ B}{H K : B ⥤ C}

-- Naturality of β implies naturality of whiskering; this is not used.
@[simp]
theorem WhiskeringNaturality
    (α : F ⟶ G)(β : H ⟶ K) :
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

namespace Over
variable {C : Type u} [Category.{v} C]

section BeckChevalleyTransformations

@[simp]
theorem eqToHom_left {X : C} {x y : Over X} (e : x = y) : (eqToHom e).left = eqToHom (e ▸ rfl) := by
  subst e; rfl

theorem map.comp_eq {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) :
    map f ⋙ map g = map (f ≫ g) := by
  fapply Functor.ext
  · dsimp [Over, Over.map]; intro x; unfold Comma.mapRight; simp
  · intros x y u; ext; simp

def mapCompIso {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) :
    Over.map f ⋙ Over.map g ≅ Over.map (f ≫ g) := eqToIso (map.comp_eq f g)

theorem map.square_eq {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g = Over.map h ⋙ Over.map k := by
  rw [map.comp_eq, w, ← map.comp_eq]

/-- The Beck Chevalley transformations are iterated mates of this isomorphism.-/
def mapSquareIso {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k :=
  eqToIso (map.square_eq f g h k w)

-- Is this better or worse?
def mapSquareIso' {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k := by
  rw [map.square_eq]
  exact w

/-- The Beck-Chevalley natural transformation. -/
def pullbackBeckChevalleyNatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange h ⋙ Over.map f ⟶ Over.map k ⋙ baseChange g :=
  (mateEquiv (mapAdjunction h) (mapAdjunction g)) ((mapSquareIso f g h k w).hom)

/-- The conjugate isomorphism between pullback functors. -/
def pullbackCompIso [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  conjugateIsoEquiv (mapAdjunction (f ≫ g)) ((mapAdjunction f).comp (mapAdjunction g)) (mapCompIso f g)

/-- The conjugate isomorphism between the pullbacks along a commutative square. -/
def pullbackSquareIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange k ⋙ baseChange h ≅ baseChange g ⋙ baseChange f :=
  conjugateIsoEquiv ((mapAdjunction h).comp (mapAdjunction k)) ((mapAdjunction f).comp (mapAdjunction g)) (mapSquareIso f g h k w)

-- Why finite wide pullbacks and not just pullbacks?
def pushforwardBeckChevalleyNatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h)
     : gexp.functor ⋙ baseChange k ⟶ baseChange f ⋙ hexp.functor :=
  conjugateEquiv ((mapAdjunction k).comp gexp.adj) (hexp.adj.comp (mapAdjunction f)) (pullbackBeckChevalleyNatTrans f g h k w)

/-- The conjugate isomorphism between the pushforwards along a commutative square. -/
def pushforwardSquareIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (fexp : CartesianExponentiable f) (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h) (kexp : CartesianExponentiable k) : fexp.functor ⋙ gexp.functor ≅ hexp.functor ⋙ kexp.functor := conjugateIsoEquiv (gexp.adj.comp fexp.adj) (kexp.adj.comp hexp.adj) (pullbackSquareIso f g h k w)


end BeckChevalleyTransformations
section BeckChevalleyIsos

/-- Calculating the counit components of mapAdjunction. -/
theorem mapAdjunction.counit.app_pullback.fst  [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (y : Over Y) :
    ((mapAdjunction f).counit.app y).left = pullback.fst := by simp

def pullback.NatTrans.app.map [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).obj ((baseChange h ⋙ map f).obj y) ⟶ (forget X).obj ((map k ⋙ baseChange g).obj y) :=
  pullback.map y.hom h (y.hom ≫ k) g (𝟙 y.left) f k (Eq.symm (id_comp (y.hom ≫ k))) w.symm

theorem pullbackBeckChevalleyComponent_pullbackMap [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((pullbackBeckChevalleyNatTrans f g h k w).app y) = pullback.NatTrans.app.map f g h k w y := by
  dsimp
  ext <;> unfold pullback.NatTrans.app.map pullback.map
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
theorem pullback.NatTrans.isPullback.componentIsIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) (y : Over Y) :
    IsIso ((forget X).map ((pullbackBeckChevalleyNatTrans f g h k w).app y)) := by
  rw [pullbackBeckChevalleyComponent_pullbackMap f g h k w y]
  have s := PullbackCone.mk _ _
        (show (pullback.fst : pullback y.hom h ⟶ _) ≫ y.hom ≫ k = ((pullback.snd : pullback y.hom h ⟶ _) ≫ f) ≫ g by
          rw [← Category.assoc, pullback.condition (f := y.hom) (g := h), Category.assoc, w.symm, Category.assoc])
  let t := PullbackCone.mk (pullback.fst : pullback (y.hom ≫ k) g ⟶ _) pullback.snd pullback.condition
  have P := bigSquareIsPullback _ _ _ _ _ _ _ _ w.symm hyp (pullbackIsPullback y.hom h)
  have Q := pullbackIsPullback (y.hom ≫ k) g
  let conemap : (PullbackCone.mk _ _
        (show (pullback.fst : pullback y.hom h ⟶ _) ≫ y.hom ≫ k = ((pullback.snd : pullback y.hom h ⟶ _) ≫ f) ≫ g by
          rw [← Category.assoc, pullback.condition (f := y.hom) (g := h), Category.assoc, w.symm, Category.assoc])) ⟶ (PullbackCone.mk (pullback.fst : pullback (y.hom ≫ k) g ⟶ _) pullback.snd pullback.condition) := {
    hom := pullback.NatTrans.app.map f g h k w y
    w := by
      rintro (_|(left|right)) <;>
      · unfold app.map
        simp
  }
  have mapiso := (IsLimit.hom_isIso P Q conemap)
  have dumb : conemap.hom = pullback.NatTrans.app.map f g h k w y := by rfl
  rw [← dumb]
  exact ((Cones.forget _).map_isIso conemap)

/-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pullbackBeckChevalleyNatTrans.isPullback.isIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) :
    IsIso (pullbackBeckChevalleyNatTrans f g h k w) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro y
  have := pullback.NatTrans.isPullback.componentIsIso f g h k w hyp y
  apply (forget_reflects_iso (X := X)).reflects
    ((pullbackBeckChevalleyNatTrans f g h k w).app y)

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleyNatTrans.isPullback.isIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h) :
    IsIso (pushforwardBeckChevalleyNatTrans f g h k w gexp hexp) := by
  have := pullbackBeckChevalleyNatTrans.isPullback.isIso f g h k w hyp
  apply conjugateEquiv_iso

end BeckChevalleyIsos


end Over
