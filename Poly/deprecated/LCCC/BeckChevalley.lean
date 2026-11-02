/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Sina Hazratpour
-/

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
  rw [← mapComp_eq, w, mapComp_eq]

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
    pullback h ⋙ Over.map f ⟶ Over.map k ⋙ pullback g :=
  (mateEquiv (mapPullbackAdj h) (mapPullbackAdj g)) ((mapSquareIso f g h k w).hom)

def pullbackBeckChevalleyOfMap [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) : pullback f ⋙ forget X ⟶ forget Y := by
  have := (mapForgetIso f).inv
  rw [← Functor.comp_id (forget X)] at this
  exact (mateEquiv (mapPullbackAdj f) (Adjunction.id)) (this)

/-- The conjugate isomorphism between the pullbacks along a commutative square. -/
def pullbackSquareIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    pullback k ⋙ pullback h ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv ((mapPullbackAdj h).comp (mapPullbackAdj k)) ((mapPullbackAdj f).comp
    (mapPullbackAdj g)) (mapSquareIso f g h k w)

/-- The Beck-Chevalley natural transformations in a square of pullbacks and pushforwards.-/
def pushforwardBeckChevalleyNatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (gexp : CartesianExponentiable g) (hexp : CartesianExponentiable h)
     : gexp.functor ⋙ pullback k ⟶ pullback f ⋙ hexp.functor :=
  conjugateEquiv ((mapPullbackAdj k).comp gexp.adj) (hexp.adj.comp (mapPullbackAdj f))
    (pullbackBeckChevalleyNatTrans f g h k w)

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
theorem mapPullbackAdj.counit.app_pullback.fst [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) (y : Over Y) :
    ((mapPullbackAdj f).counit.app y).left = pullback.fst _ _ := by simp

def pullbackNatTrans.app.map [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).obj ((pullback h ⋙ map f).obj y) ⟶ (forget X).obj ((map k ⋙ pullback g).obj y) :=
  pullback.map y.hom h (y.hom ≫ k) g (𝟙 y.left) f k (Eq.symm (id_comp (y.hom ≫ k))) w.symm

theorem pullbackBeckChevalleyComponent_pullbackMap [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((pullbackBeckChevalleyNatTrans f g h k w).app y) =
    pullbackNatTrans.app.map f g h k w y := by
  dsimp
  ext <;> simp [pullbackNatTrans.app.map, pullbackBeckChevalleyNatTrans, mapSquareIso]

-- NB: I seem to have symmetry of HasPullback but not IsPullback
-- SH: yes, we do have that: it is given by the function `.flip`
theorem pullbackNatTrans_of_IsPullback_component_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (y : Over Y) :
    IsIso ((forget X).map ((pullbackBeckChevalleyNatTrans f g h k pb.w).app y)) := by
  rw [pullbackBeckChevalleyComponent_pullbackMap f g h k pb.w y]
  have P := pasteHorizIsPullback rfl (isLimit pb.flip) (pullbackIsPullback y.hom h)
  have Q := pullbackIsPullback (y.hom ≫ k) g
  let conemap :
      (PullbackCone.mk _ _
        (show pullback.fst y.hom h ≫ y.hom ≫ k = (pullback.snd y.hom h ≫ f) ≫ g by
          simp [reassoc_of% pullback.condition (f := y.hom) (g := h), pb.w])) ⟶
      (PullbackCone.mk
        (pullback.fst (y.hom ≫ k) g) (pullback.snd _ _) pullback.condition) := {
    hom := pullbackNatTrans.app.map f g h k pb.w y
    w := by
      rintro (_|(left|right)) <;>
      · unfold pullbackNatTrans.app.map
        simp
  }
  haveI mapiso := IsLimit.hom_isIso P Q conemap
  exact ((Cones.forget _).map_isIso conemap)

/-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (pb : IsPullback f h g k) :
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
