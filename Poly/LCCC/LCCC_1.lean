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

def pullbackCompositionIsBinaryProduct {I : C} (f x : Over I) :
    let pbleg1 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ f := homMk pullback.snd rfl
    let pbleg2 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ x :=
    Over.homMk (pullback.fst) (by simp [pullback.condition])
    IsLimit (BinaryFan.mk (pbleg1) (pbleg2)) := by
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

def NatIsoOfBaseChangeComposition' [HasFiniteWidePullbacks C] {I : C} (f : Over I) : (baseChange f.hom).comp (Over.map f.hom) ≅ MonoidalCategory.tensorLeft f := by
  fapply NatIso.ofComponents
  case app =>
    intro x
    fapply IsLimit.conePointUniqueUpToIso  (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x)
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
        have projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.left) = (prod.fst (X := f) (Y := y)) := rfl
        rw [projeq]
        simp_rw [assoc, prod.map_fst, comp_id]
        have commutelimitconex := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x) ⟨ WalkingPair.left⟩
        simp at commutelimitconex
        --simp [commutelimitconex]
        have commutelimitconey := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f y) (Limits.prodIsProd f y) ⟨WalkingPair.left⟩
        simp at commutelimitconey
        rw [commutelimitconey, commutelimitconex]
        apply OverMorphism.ext
        simp
      | .right =>
        let projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.right) = (prod.snd (X := f) (Y := y)) := rfl
        rw [projeq]
        simp_rw [assoc, prod.map_snd]
        simp
        have commutelimitconex := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x) ⟨ WalkingPair.right⟩
        simp at commutelimitconex
        have commutelimitconey := IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f y) (Limits.prodIsProd f y) ⟨ WalkingPair.right⟩
        simp at commutelimitconey
        rw [commutelimitconey, ← assoc, commutelimitconex]
        apply OverMorphism.ext
        simp

#check IsLimit.conePointUniqueUpToIso_hom_comp

def NatIsoOfBaseChangeComposition [HasFiniteWidePullbacks C] {I : C} (f : Over I) :
    (baseChange f.hom).comp (Over.map f.hom) ≅ MonoidalCategory.tensorLeft f := by
  fapply NatIso.ofComponents
  case app =>
    intro x
    fapply IsLimit.conePointUniqueUpToIso (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x)
  case naturality =>
    intros x y u
    simp
    apply Fan.IsLimit.hom_ext (limit.isLimit _)
    rintro ⟨ ⟨ ⟩ | ⟨ ⟩ ⟩ -- TODO : does `rintro` too much unfolding compared to `case`?
    · apply OverMorphism.ext
      simp


    · sorry


      have projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.left) = (prod.fst (X := f) (Y := y)) := rfl
      rw [projeq]
      --simp_rw [prod.map_fst (𝟙 f) u]
      --simp
      have commutelimitconex :=
        IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f x) (Limits.prodIsProd f x) ⟨ WalkingPair.left⟩
      simp at commutelimitconex
      have commutelimitconey :=
        IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct _ f y) (Limits.prodIsProd f y) ⟨ WalkingPair.left⟩
      simp at commutelimitconey
      rw [commutelimitconex, commutelimitconey]
      apply OverMorphism.ext
      simp
    · let projeq : (Fan.proj (limit.cone (pair f y)) WalkingPair.right) = (prod.snd (X := f) (Y := y)) := rfl
      rw [projeq]
      simp_rw [assoc, prod.map_snd (𝟙 f) u]
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


class LexLocallyCartesianClosed [HasFiniteWidePullbacks C] where
  over_cc : Π (I : C), CartesianClosed (Over I)

class LexStableColimLocallyCartesianClosed [HasTerminal C] where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance

-- Note (SH): Maybe convenient to include the fact that lcccs have a terminal object?
-- Will see if that is needed. For now, we do not include that in the definition.
-- this is the general definition of a locally cartesian closed category where we do not assume a terminal object in `C`.
class StableColimLocallyCartesianClosed where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance

class StableColimLocallyCartesianClosed' where
  pushforward {X Y : C} (f : X ⟶ Y) : IsLeftAdjoint (baseChange f) := by infer_instance

/-
Relating `StableColimLocallyCartesianClosed` and `LexLocallyCartesianClosed`
Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`, and so `f* : C/B ⥤ (C/B)/f` is 'the same thing' as pulling back
morphisms along `f`.
-/


namespace LexStableColimLocallyCartesianClosed

instance cartesianClosedOfOver [LexStableColimLocallyCartesianClosed C] [HasFiniteWidePullbacks C]
    {I : C} : CartesianClosed (Over I) := by
      refine .mk _ fun f ↦ .mk f (baseChange f.hom ⋙ pushforward f.hom) (ofNatIsoLeft (F := ?functor ) ?adj ?iso )
      case functor =>
        exact (baseChange f.hom ⋙ Over.map f.hom)
      case adj =>
        exact ((adj f.hom).comp (Over.mapAdjunction f.hom))
      case iso =>
        apply NatIsoOfBaseChangeComposition

instance [LexStableColimLocallyCartesianClosed C] [HasFiniteWidePullbacks C] : LexLocallyCartesianClosed C where
  over_cc (I : C) := by infer_instance

-- we should be able to infer all finite limits from pullbacks and terminal which is part of definition of `LexStableColimLocallyCartesianClosed C`.
instance [LexStableColimLocallyCartesianClosed C] :
    haveI : HasFiniteWidePullbacks C := by sorry -- TODO: figure out how we can inline an instance.
    LexLocallyCartesianClosed C where
  over_cc I := by infer_instance

#check hasBinaryProducts_of_hasTerminal_and_pullbacks

attribute [local instance] monoidalOfHasFiniteProducts
-- Every locally cartesian closed category with a terminal object is cartesian closed.
-- Note (SH): This is a bit of a hack. We really should not be needing `HasFiniteProducts C`
-- instance cartesianClosed  [HasPullbacks C] [LocallyCartesianClosed C] [HasTerminal C] :
--     haveI : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
--     haveI : HasFiniteProducts C := by sorry --finiteProductsOfBinaryProducts
--     haveI : MonoidalCategory C := monoidalOfHasFiniteProducts C
--     CartesianClosed C where
--   closed X := {
--     rightAdj := sorry
--     adj := sorry
--   }

-- TODO : seems mathlib does not have (?) an instance for getting `HasFiniteProducts ` from `HasTerminal` and `HasFiniteWidePullbacks`. Worth checking on Zulip
-- Here we need the iso C/1 ≅ C (port it from mathlib)
instance cartesianClosed [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] :
    haveI : HasFiniteProducts C := by sorry
    CartesianClosed C := by sorry


-- Might be useful to have products as pullbacks over terminal.
-- TODO: figure out a way to not include `HasFiniteProducts C`, this is perhaps related to the fact that there is not instance of `HasFiniteProducts C` from `HasTerminal C` and `HasFiniteWidePullbacks C`.
instance cartesianClosed' [HasFiniteWidePullbacks C] [HasFiniteProducts C] [LexStableColimLocallyCartesianClosed C] : CartesianClosed C := by sorry

-- TODO (SH): The slices of a locally cartesian closed category are locally cartesian closed.

--TODO (SH): We need to prove some basic facts about pushforwards.

namespace Pushforward

variable [LocallyCartesianClosed C]

-- ER: Move this to a different namespace that assumes only that basechange exists.
-- ER: We might prefer to reverse directions in the statement but this simplified the proof.
def idPullbackIso (X : C) : 𝟭 (Over X) ≅ (baseChange (𝟙 X)) := asIso ((transferNatTransSelf Adjunction.id (mapAdjunction (𝟙 X))) (mapId X).hom)

def idIso (X : C) :  (pushforward (𝟙 X)) ≅ 𝟭 (Over X) :=
  asIso ((transferNatTransSelf (LocallyCartesianClosed.adj (𝟙 X)) Adjunction.id) (idPullbackIso _ X).hom)

end Pushforward


/- SH: TODO
Every LCCC with reflexive coequalizers is a regular category.
If `C` is locally cartesian closed and has
reflexive coequalizers, then every morphism factors into a regular epic
and monic.
-/
end LocallyCartesianClosed
