/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over

-- All the imports below are transitively imported by the above import.
-- import Mathlib.CategoryTheory.Adjunction.Basic
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
-- import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Locally cartesian closed categories
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*}[Category C]

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

-- def pbleg1 {I : C} (f x : Over I) : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ f := homMk pullback.snd rfl

-- def pbleg2 {I : C} (f x : Over I) : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ x :=
-- Over.homMk (pullback.fst) (by simp [pullback.condition])

def pullbackCompositionIsBinaryProduct {I : C} (f x : Over I)
:
let pbleg1 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ f := homMk pullback.snd rfl
let pbleg2 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ x :=
Over.homMk (pullback.fst) (by simp [pullback.condition])
IsLimit (BinaryFan.mk (pbleg1) (pbleg2))
  := by
    fconstructor
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
      rintro s ⟨⟨l⟩|⟨r⟩⟩
      iterate {apply Over.OverMorphism.ext; simp}
    case uniq =>
      intro s m prf
      apply Over.OverMorphism.ext
      dsimp
      refine (pullback.hom_ext ?h.h₀ ?h.h₁)
      case h.h₀ =>
        simpa [pullback.lift_fst] using (congr_arg CommaMorphism.left (prf ⟨ .right⟩))
      case h.h₁ =>
        simpa [pullback.lift_snd] using (congr_arg CommaMorphism.left (prf ⟨ .left⟩))

def NatIsoOfBaseChangeComposition [HasFiniteWidePullbacks C] {I : C} (f : Over I) : (baseChange f.hom).comp (Over.map f.hom) ≅ MonoidalCategory.tensorLeft f := by
  fapply NatIso.ofComponents
  case app =>
    intro x
    dsimp
    let Q := Limits.prodIsProd f x
    fapply IsLimit.conePointUniqueUpToIso (s := Limits.BinaryFan.mk _ _ ) _ (Q := Q)
    · fapply Over.homMk
      · exact pullback.snd
      · exact rfl
    · fapply Over.homMk
      · exact pullback.fst
      · exact pullback.condition
    · exact (pullbackCompositionIsBinaryProduct _ f x)
  case naturality =>
    intros x y u
    simp
    apply Fan.IsLimit.hom_ext
    case hc =>
      apply limit.isLimit
    case h =>
      intro lr
      match lr with
      | .left  =>
        let projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.left) = (prod.fst (X := f) (Y := y)) := rfl
        rw [projeq]
        simp_rw [assoc]
        simp_rw [prod.map_fst (𝟙 f) u]
        simp
        have commutelimitconex := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x) ⟨ WalkingPair.left⟩
        simp at commutelimitconex
        have commutelimitconey := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f y) (Limits.prodIsProd f y) ⟨ WalkingPair.left⟩
        simp at commutelimitconey
        rw [commutelimitconex , commutelimitconey]
        apply OverMorphism.ext
        · simp
          --unfold pullback.map
          --unfold pbleg1
          --simp
      | .right =>
        let projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.right) = (prod.snd (X := f) (Y := y)) := rfl
        rw [projeq]
        simp_rw [assoc]
        simp_rw [prod.map_snd (𝟙 f) u]
        simp
        have commutelimitconex := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x) ⟨ WalkingPair.right⟩
        simp at commutelimitconex
        have commutelimitconey := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f y) (Limits.prodIsProd f y) ⟨ WalkingPair.right⟩
        simp at commutelimitconey
        rw [commutelimitconey]
        rw [← assoc]
        rw [commutelimitconex]
        apply OverMorphism.ext
        · simp
          --unfold pullback.map
          --unfold pbleg2
          --simp


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
        exact ((LocallyCartesianClosed.adj f.hom).comp (Over.mapAdjunction f.hom))
      case iso =>
        apply NatIsoOfBaseChangeComposition

-- Every locally cartesian closed category with a terminal object is cartesian closed.
-- Note (SH): This is a bit of a hack. We really should not be needing `HasFiniteProducts C`
instance cartesianClosed [HasFiniteWidePullbacks C] [HasFiniteProducts C] [LocallyCartesianClosed C] [HasTerminal C] : CartesianClosed C where
  closed X := {
    rightAdj := sorry
    adj := sorry
  }

-- TODO (SH): The slices of a locally cartesian closed category are locally cartesian closed.

--TODO (SH): We need to prove some basic facts about pushforwards.

namespace Pushforward

variable [LocallyCartesianClosed C]

def idIso (X : C) :  (pushforward (𝟙 X)) ≅ 𝟭 (Over X) := sorry

end Pushforward

end LocallyCartesianClosed
