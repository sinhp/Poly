/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
-- import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

-- Likely too many imports!


/-!
# Locally cartesian closed categories
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction

variable {C : Type*}[Category C]

def hasPullbackOverAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over.map f ⊣ baseChange f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y ↦ {
      toFun := fun u ↦ {
        left := by
          simp
          fapply pullback.lift
          · exact u.left
          · exact x.hom
          · aesop_cat
        right := by
          apply eqToHom
          aesop
        w := by simp}
      invFun := fun v ↦ {
        left := by
          simp at*
          exact v.left ≫ pullback.fst
        right := by
          apply eqToHom
          aesop
        w := by
          simp
          rw [pullback.condition]
          rw [← Category.assoc]
          apply eq_whisker
          simpa using v.w}
      left_inv := by aesop_cat
      right_inv := fun v ↦ Over.OverMorphism.ext (by
        simp
        apply pullback.hom_ext
        · aesop_cat
        · rw [pullback.lift_snd]
          have vtriangle := v.w
          simp at vtriangle
          exact vtriangle.symm)}
    homEquiv_naturality_left_symm := by aesop_cat
    homEquiv_naturality_right := by aesop_cat}

/-
There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices `Over I` are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks such that each base change functor has a right adjoint, called the pushforward functor.

In this file we prove the equivalence of these conditions.

We also show that a locally cartesian closed category with a terminal object is cartesian closed.
-/

attribute [local instance] monoidalOfHasFiniteProducts

variable (C : Type*) [Category C] [HasTerminal C] [HasPullbacks C]

class LocallyCartesianClosed' where
  pushforward {X Y : C} (f : X ⟶ Y) : IsLeftAdjoint (baseChange f) := by infer_instance

-- Note (SH): Maybe conveniet to include the fact that lcccs have a terminal object?
-- Will see if that is needed. For now, we do not include that in the definition.
class LocallyCartesianClosed where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance

namespace LocallyCartesianClosed

instance cartesianClosedOfOver [LocallyCartesianClosed C] [HasFiniteWidePullbacks C]
    {I : C} : CartesianClosed (Over I) := by
      refine .mk _ fun f ↦ .mk f (baseChange f.hom ⋙ pushforward f.hom) (ofNatIsoLeft (F := ?functor ) ?adj ?iso )
      case functor =>
        exact (baseChange f.hom ⋙ Over.map f.hom)
      case adj =>
        exact ((LocallyCartesianClosed.adj f.hom).comp (hasPullbackOverAdj f.hom))
      case iso =>
        fapply NatIso.ofComponents
        case app =>
          intro g
          dsimp
          let Q := Limits.prodIsProd f g
          fapply IsLimit.conePointUniqueUpToIso (s := Limits.BinaryFan.mk _ _ ) _ (Q := Q)
          · fapply Over.homMk
            · exact pullback.snd
            · aesop_cat
          · fapply Over.homMk
            · exact pullback.fst
            · exact pullback.condition
          · fconstructor
            case lift =>
              intro s
              fapply Over.homMk
              · dsimp
                refine pullback.lift ?f.h ?f.k ?f.w
                case f.h =>
                  exact ((s.π.app ⟨ .right ⟩).left)
                case f.k =>
                  exact ((s.π.app ⟨ .left ⟩).left)
                case f.w =>
                  aesop_cat
              · simp
            case fac =>
              intros s lr
              apply Over.OverMorphism.ext
              sorry
            case uniq =>
              intros s t prf
              apply Over.OverMorphism.ext
              simp
              refine (pullback.hom_ext ?h.h₀ ?h.h₁).symm
              case h.h₀ =>
                have thisl := prf ⟨ .left⟩
                have thisr := prf ⟨ .right⟩
                simp at thisl thisr
                rw [← thisl]
                have lthisl := congr_arg CommaMorphism.left thisl
                have lthisr := congr_arg CommaMorphism.left thisr
                simp at lthisl lthisr
                generalize_proofs h1 h2 h3
                revert h3
                rw [Over.comp_left]
                intro h3
                rw [pullback.lift_fst]
                exact _root_.id lthisr.symm
              case h.h₁ =>
                sorry
        case naturality => sorry

end LocallyCartesianClosed

#check LocallyCartesianClosed

-- Every locally cartesian closed category with 1 is cartesian closed.

namespace LocallyCartesianClosed

variable {C : Type*} [Category C] [HasTerminal C] [HasFiniteProducts C] [HasPullbacks C]

instance cartesianClosed [LocallyCartesianClosed C] : CartesianClosed C where
  closed X := {
    rightAdj := sorry
    adj := sorry
  }


end LocallyCartesianClosed


-- TODO: The slices of a locally cartesian closed category are locally cartesian closed.
