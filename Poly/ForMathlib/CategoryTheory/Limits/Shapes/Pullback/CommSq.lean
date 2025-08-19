/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Poly.ForMathlib.CategoryTheory.CommSq

namespace CategoryTheory.Functor
open Limits

theorem reflect_isPullback
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (i : Z ⟶ W)
    [rl : ReflectsLimit (cospan h i) F] [Functor.Faithful F] :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) →
    IsPullback f g h i := by
  intro pb
  have sq := F.reflect_commSq pb.toCommSq
  apply IsPullback.mk sq
  apply rl.reflects
  let i := cospanCompIso F h i
  apply IsLimit.equivOfNatIsoOfIso i.symm pb.cone _ _ pb.isLimit
  let j :
      ((Cones.postcompose i.symm.hom).obj pb.cone).pt ≅
      (F.mapCone <| PullbackCone.mk f g sq.w).pt :=
    Iso.refl _
  apply WalkingCospan.ext j <;> simp +zetaDelta

end CategoryTheory.Functor
