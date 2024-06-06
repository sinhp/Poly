/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Awodey, Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.Tactic.ApplyFun

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

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]


-- Some adjunction stuff that is here temporarily


theorem homEquiv_naturality_left_square {F : C ⥤ D} {G : D ⥤ C} {adj : F ⊣ G} {X' X : C} {Y Y' : D}
    (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right]
  exact congrArg (adj.homEquiv X' Y') w

theorem homEquiv_naturality_right_square {F : C ⥤ D} {G : D ⥤ C} {adj : F ⊣ G} {X' X : C} {Y Y' : D}
    (f : X' ⟶ X) (g : X ⟶ G.obj Y') (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm]
  exact congrArg (adj.homEquiv X' Y').symm w

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

def pullbackCompositionIsBinaryProduct [HasPullbacks C] {I : C} (f x : Over I) :
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

def OverBinaryProductIso [HasFiniteWidePullbacks C] {I : C} (f x : Over I) :
    (Over.map f.hom).obj ((baseChange f.hom).obj x) ≅ Limits.prod f x := by
  apply IsLimit.conePointUniqueUpToIso (pullbackCompositionIsBinaryProduct f x) (prodIsProd f x)

def OverBinaryProductIso.symm [HasFiniteWidePullbacks C] {I : C} (f x : Over I) :
    Limits.prod f x ≅ (Over.map f.hom).obj ((baseChange f.hom).obj x) := by
  apply IsLimit.conePointUniqueUpToIso (prodIsProd f x) (pullbackCompositionIsBinaryProduct f x)

def OverBinaryProductIsoLeftInv [HasFiniteWidePullbacks C] {I : C} (f x : Over I) :
    (OverBinaryProductIso f x).hom ≫ (OverBinaryProductIso.symm f x).hom = 𝟙 _ :=
  by exact (Iso.hom_comp_eq_id (OverBinaryProductIso f x)).mpr rfl

def OverBinaryProductIsoRightInv [HasFiniteWidePullbacks C] {I : C} (f x : Over I) :
    (OverBinaryProductIso.symm f x).hom ≫ (OverBinaryProductIso f x).hom = 𝟙 _ :=
  by exact (Iso.hom_comp_eq_id (OverBinaryProductIso.symm f x)).mpr rfl

def OverBinaryProductTriangle_fst [HasFiniteWidePullbacks C] {I : C}
    (f x : Over I) :
    let pbleg1 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ f := homMk pullback.snd rfl
    (OverBinaryProductIso f x).hom ≫ prod.fst = pbleg1 :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct f x) (Limits.prodIsProd f x) ⟨ WalkingPair.left⟩

def OverBinaryProductTriangle_snd [HasFiniteWidePullbacks C] {I : C}
    (f x : Over I) :
    let pbleg2 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ x :=
    Over.homMk (pullback.fst) (by simp [pullback.condition])
    (OverBinaryProductIso f x).hom ≫ prod.snd = pbleg2 :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullbackCompositionIsBinaryProduct f x) (Limits.prodIsProd f x) ⟨ WalkingPair.right⟩

def OverBinaryProductTriangle.symm_fst [HasFiniteWidePullbacks C] {I : C}
    (f x : Over I) :
    let pbleg1 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ f := homMk pullback.snd rfl
    (OverBinaryProductIso.symm f x).hom ≫ pbleg1 = prod.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Limits.prodIsProd f x)
  (pullbackCompositionIsBinaryProduct f x) ⟨ WalkingPair.left⟩

def OverBinaryProductTriangle.symm_snd [HasFiniteWidePullbacks C] {I : C}
    (f x : Over I) :
    let pbleg2 : (Over.map f.hom).obj ((baseChange f.hom).obj x) ⟶ x :=
    Over.homMk (pullback.fst) (by simp [pullback.condition])
    (OverBinaryProductIso.symm f x).hom ≫ pbleg2 = prod.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Limits.prodIsProd f x)
  (pullbackCompositionIsBinaryProduct f x) ⟨ WalkingPair.right⟩

def NatIsoOfBaseChangeComposition [HasFiniteWidePullbacks C] {I : C} (f : Over I) :
    (baseChange f.hom).comp (Over.map f.hom) ≅ MonoidalCategory.tensorLeft f := by
  fapply NatIso.ofComponents
  case app =>
    intro x
    exact OverBinaryProductIso f x
  case naturality =>
    intros x y u
    simp
    ext1
    · simp_rw [assoc, prod.map_fst, comp_id]
      rw [OverBinaryProductTriangle_fst, OverBinaryProductTriangle_fst]
      ext
      simp
    · simp_rw [assoc, prod.map_snd]
      rw [OverBinaryProductTriangle_snd, ← assoc, OverBinaryProductTriangle_snd]
      ext
      simp

variable (C : Type u) [Category.{v} C]

class LexLocallyCartesianClosed [HasFiniteWidePullbacks C] where
  over_cc : Π (I : C), CartesianClosed (Over I)

attribute [instance] LexLocallyCartesianClosed.over_cc

class LexStableColimLocallyCartesianClosed [HasFiniteWidePullbacks C] where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance


-- Note (SH): Maybe convenient to include the fact that lcccs have a terminal object?
-- Will see if that is needed. For now, we do not include that in the definition.
-- this is the general definition of a locally cartesian closed category where we do not assume a terminal object in `C`.
class StableColimLocallyCartesianClosed [HasPullbacks C] where
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj (f : X ⟶ Y) : baseChange f ⊣ pushforward f := by infer_instance

class StableColimLocallyCartesianClosed' [HasPullbacks C] where
  pushforward {X Y : C} (f : X ⟶ Y) : IsLeftAdjoint (baseChange f) := by infer_instance

/-
Relating `StableColimLocallyCartesianClosed` and `LexLocallyCartesianClosed`
Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`, and so `f* : C/B ⥤ (C/B)/f` is 'the same thing' as pulling back
morphisms along `f`.
-/
namespace LexStableColimLocallyCartesianClosed

instance cartesianClosedOfOver
[HasFiniteWidePullbacks C] [LexStableColimLocallyCartesianClosed C] {I : C} :
    CartesianClosed (Over I) := by
  refine .mk _ fun f ↦ .mk f (baseChange f.hom ⋙ pushforward f.hom) (ofNatIsoLeft (F := ?functor ) ?adj ?iso )
  case functor =>
    exact (baseChange f.hom ⋙ Over.map f.hom)
  case adj =>
    exact ((adj f.hom).comp (Over.mapAdjunction f.hom))
  case iso =>
    apply NatIsoOfBaseChangeComposition

instance [HasFiniteWidePullbacks C][LexStableColimLocallyCartesianClosed C] :
    LexLocallyCartesianClosed C where
  over_cc (I : C) := by infer_instance
namespace LexLocallyCartesianClosed

variable {C : Type u} [Category.{v} C]

-- Defining the pushforward functor from the hypothesis that C is LexLocallyCartesianClosed.
def pushforwardCospanLeg1 [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C}
    (f : X ⟶ Y) : (Over.mk (𝟙 Y)) ⟶ ((Over.mk f) ⟹ (Over.mk f)) :=
  CartesianClosed.curry prod.fst

def pushforwardCospanLeg2 [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C}
    (f : X ⟶ Y) (x : Over X) : ((Over.mk f) ⟹ ((Over.map f).obj x)) ⟶ ((Over.mk f) ⟹ (Over.mk f)) :=
  (((exp (Over.mk f)).map) (Over.homMk x.hom))

-- @[simps]
def pushforwardObj [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C} (f : X ⟶ Y) (x : Over X)
    : Over Y :=
  pullback (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x)

def pushforwardCospanLeg2Map [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C}
    (f : X ⟶ Y) (x x' : Over X) (u : x ⟶ x') :
    ((exp (Over.mk f)).obj ((Over.map f).obj x)) ⟶  ((exp (Over.mk f)).obj ((Over.map f).obj x')) :=
  (exp (Over.mk f)).map ((Over.map f).map u)

def pushforwardMap [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C} (f : X ⟶ Y) (x x' : Over X)
    (u : x ⟶ x') : (pushforwardObj f x) ⟶ (pushforwardObj f x') := by
  refine pullback.map (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x) (pushforwardCospanLeg1 f) (pushforwardCospanLeg2 f x') (𝟙 (Over.mk (𝟙 Y))) (pushforwardCospanLeg2Map f x x' u) (𝟙 (Over.mk f ⟹ Over.mk f))
    ?_ ?_
  · unfold pushforwardCospanLeg1
    simp
  · unfold pushforwardCospanLeg2 pushforwardCospanLeg2Map
    simp
    rw [← (exp (Over.mk f)).map_comp]
    congr
    simp only [map_obj_left, mk_left, map_map_left, homMk_left, w]

def pushforwardFunctor [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C} (f : X ⟶ Y) :
    (Over X) ⥤ (Over Y) where
  obj x := pushforwardObj f x
  map u := pushforwardMap f _ _ u
  map_id x := by
    apply pullback.hom_ext
    · unfold pushforwardMap
      simp
    · unfold pushforwardMap pushforwardCospanLeg2Map
      simp
  map_comp := by
    intros x y z u v
    apply pullback.hom_ext
    · unfold pushforwardMap
      simp
    · unfold pushforwardMap pushforwardCospanLeg2Map
      simp

-- The construction of the pushforward adjunction from the hypothesis that C is LexLocallyCartesianClosed.

-- Towards the construction of the transpose of u : f^* y ⟶ x.
def PushforwardObjToLeg [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C]
    {X Y : C} (f : X ⟶ Y) (x : Over X) (y : Over Y) (u : (baseChange f).obj y ⟶ x) :
    y ⟶ Over.mk f ⟹ (Over.map f).obj x :=
  CartesianClosed.curry ((OverBinaryProductIso.symm (Over.mk f) y).hom ≫ (Over.map f).map u)

-- The transpose of u : f^* y ⟶ x.
def PushforwardObjTo [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C]
    {X Y : C} (f : X ⟶ Y) (x : Over X) (y : Over Y) (u : (baseChange f).obj y ⟶ x) :
    y ⟶ (pushforwardFunctor f).obj x := by
  apply pullback.lift ((mkIdTerminal (X := Y)).from y) (PushforwardObjToLeg f x y u)
  apply (CartesianClosed.uncurry_injective (A := Over.mk f))
  unfold pushforwardCospanLeg1 PushforwardObjToLeg
  rw [CartesianClosed.uncurry_natural_left, CartesianClosed.uncurry_curry]
  simp [pushforwardCospanLeg2]
  rw [CartesianClosed.uncurry_natural_right, CartesianClosed.uncurry_curry]
  simp
  have conj : ((Over.map f).map u ≫ (homMk x.hom rfl : (Over.map f).obj x ⟶ Over.mk f)) =
    (homMk ((baseChange f).obj y).hom : (Over.map f).obj ((baseChange f).obj y) ⟶ Over.mk f) :=
      OverMorphism.ext (by aesop_cat)
  rw [conj]
  exact (OverBinaryProductTriangle.symm_fst (Over.mk f) y).symm

-- It's slightly easier to construct the transposed map f^*y ⟶ x from a cone over the pushforward cospan.
def PushforwardObjUP [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C}
    (f : X ⟶ Y) (x : Over X) (y : Over Y) (v : y ⟶ ((Over.mk f) ⟹ ((Over.map f).obj x)))
    (w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f) = v ≫ (pushforwardCospanLeg2 f x)) :
    (baseChange f).obj y ⟶ x := by
  unfold pushforwardCospanLeg2 at w
  unfold pushforwardCospanLeg1 at w
  have cw := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft (Over.mk f)) (adj := exp.adjunction (Over.mk f)) _ _ _ _ w
  unfold CartesianClosed.curry at cw
  simp at cw
  apply_fun CommaMorphism.left at cw
  fapply homMk
  · let vc := (CartesianClosed.uncurry v).left
    let iso := (OverBinaryProductIso (Over.mk f) y).hom.left
    exact (iso ≫ vc)
  · unfold CartesianClosed.uncurry
    dsimp at cw
    simp
    rw [← cw]
    have limeq := OverBinaryProductTriangle_fst (Over.mk f) y
    apply_fun CommaMorphism.left at limeq
    simpa using limeq

-- The heart of the calculation that these constructions are inverses one way around,
-- checking that they recover the same cone leg over the pushforward cospan.
def pushforwardAdjRightInv [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C]
    {X Y : C} (f : X ⟶ Y) (x : Over X) (y : Over Y)
    (v : y ⟶ ((Over.mk f) ⟹ ((Over.map f).obj x)))
    (w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f) = v ≫ (pushforwardCospanLeg2 f x)) : PushforwardObjToLeg f x y (PushforwardObjUP f x y v w) = v := by
  unfold PushforwardObjUP PushforwardObjToLeg
  simp
  apply (CartesianClosed.curry_eq_iff _ v).mpr
  ext
  simp
  rw [← assoc]
  have iso := OverBinaryProductIsoRightInv (Over.mk f) y
  apply_fun (Over.forget Y).map at iso
  rw [(Over.forget Y).map_id, (Over.forget Y).map_comp] at iso
  simp at iso
  rw [iso]
  exact id_comp (CartesianClosed.uncurry v).left

-- Finally the construction of the pushforward adjunction.
def pushforwardAdj [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] {X Y : C} (f : X ⟶ Y) :
    baseChange f ⊣ pushforwardFunctor f :=
  mkOfHomEquiv {
    homEquiv := fun y x =>
      { toFun := PushforwardObjTo f x y
        invFun := by
          intro v
          refine PushforwardObjUP f x y (v ≫ pullback.snd) ?commute
          have w := v ≫= pullback.condition
          have lem : (v ≫ pullback.fst) = mkIdTerminal.from y := IsTerminal.hom_ext mkIdTerminal _ _
          rw [← lem, assoc, assoc, w]
        left_inv := by
          intro u
          unfold PushforwardObjUP PushforwardObjTo PushforwardObjToLeg
          ext
          simp
          rw [← assoc]
          have iso := OverBinaryProductIsoLeftInv (Over.mk f) y
          apply_fun (Over.forget Y).map at iso
          rw [(Over.forget Y).map_id, (Over.forget Y).map_comp] at iso
          simp at iso
          rw [iso, id_comp]
        right_inv := by
          intro v
          apply pullback.hom_ext (IsTerminal.hom_ext mkIdTerminal _ _)
          let w : ((mkIdTerminal (X := Y)).from y) ≫ (pushforwardCospanLeg1 f) = (v ≫ pullback.snd) ≫ (pushforwardCospanLeg2 f x) := by
            have w' := v ≫= pullback.condition
            rw [assoc, ← (IsTerminal.hom_ext mkIdTerminal (v ≫ pullback.fst) (mkIdTerminal.from y)), assoc, w']
          have close := pushforwardAdjRightInv f x y (v ≫ pullback.snd) w
          simp
          unfold PushforwardObjUP PushforwardObjTo PushforwardObjToLeg
          unfold PushforwardObjUP PushforwardObjToLeg at close
          simpa using close
      }
    homEquiv_naturality_left_symm := by
      intros y y' x h v
      unfold PushforwardObjUP
      ext
      simp
      rw [← assoc _ _ (CartesianClosed.uncurry (v ≫ pullback.snd)).left]
      have natiso := (NatIsoOfBaseChangeComposition (Over.mk f)).hom.naturality h
      unfold NatIsoOfBaseChangeComposition at natiso
      apply_fun CommaMorphism.left at natiso
      simp at natiso
      rw [natiso]
      simp
      rw [CartesianClosed.uncurry_natural_left]
      simp only [comp_left, map_obj_left]
    homEquiv_naturality_right := by
      intros y x x' u k
      simp
      unfold PushforwardObjTo
      apply pullback.hom_ext (IsTerminal.hom_ext mkIdTerminal _ _)
      unfold pushforwardFunctor
      rw [pullback.lift_snd]
      simp
      unfold pushforwardMap pullback.map
      rw [pullback.lift_snd, ← assoc, pullback.lift_snd]
      unfold PushforwardObjToLeg pushforwardCospanLeg2Map
      rw [← CartesianClosed.curry_natural_right, assoc, (Over.map f).map_comp]
  }

instance [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] :
    LexStableColimLocallyCartesianClosed C where
  pushforward f := pushforwardFunctor f
  adj f := pushforwardAdj f

namespace Pushforward

variable [HasFiniteWidePullbacks C] [LexStableColimLocallyCartesianClosed C]

-- ER: Move this to a different namespace that assumes only that basechange exists.
-- ER: We might prefer to reverse directions in the statement but this simplified the proof.
def idPullbackIso (X : C) : 𝟭 (Over X) ≅ (baseChange (𝟙 X)) := asIso ((transferNatTransSelf Adjunction.id (mapAdjunction (𝟙 X))) (mapId X).hom)

def idIso (X : C) :  (pushforward (𝟙 X)) ≅ 𝟭 (Over X) :=
  asIso ((transferNatTransSelf (adj (𝟙 X)) Adjunction.id) (idPullbackIso X).hom)

end Pushforward

/- SH: TODO
Every LCCC with reflexive coequalizers is a regular category.
If `C` is locally cartesian closed and has
reflexive coequalizers, then every morphism factors into a regular epic
and monic.
-/
end LexLocallyCartesianClosed

variable (T : C) (h : IsTerminal T)

-- Proof by Markus Himmel (with commentary by Dagur Asgeirsson)
@[simps]
def toOverTerminal : C ⥤ Over T where
  obj X := Over.mk (h.from _)
  map f := Over.homMk f

def equivOverTerminal : C ≌ Over T :=
  CategoryTheory.Equivalence.mk (toOverTerminal _ T h) (Over.forget _)
    (NatIso.ofComponents (fun X => Iso.refl _))
    (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _) (by simpa using h.hom_ext _ _)))

-- Improvements to my version with help from the above, but of course their version is better.
@[simps]
def HasTerminalSlicePromotion [HasTerminal C] : C ⥤ (Over (terminal C)) where
  obj X := Over.mk (terminal.from X)
  map f := Over.homMk f (IsTerminal.hom_ext terminalIsTerminal _ _)

def HasTerminalSliceEquivalence [HasTerminal C] : C ≌ (Over (terminal C))  := by
  apply CategoryTheory.Equivalence.mk (HasTerminalSlicePromotion C) (Over.forget (terminal C))
    (NatIso.ofComponents (fun X => Iso.refl _))
  · fapply NatIso.ofComponents
    · intro X
      fapply Over.isoMk
      · apply Iso.refl _
      · simp
        apply IsTerminal.hom_ext
        exact terminalIsTerminal
    · aesop_cat

-- we should be able to infer all finite limits from pullbacks and terminal which is part of definition of `LexStableColimLocallyCartesianClosed C`.
-- ER: commented out below because I now assume `HasFiniteWidePullbacks C` in the definition of `LexStableColimLocallyCartesianClosed C`
-- instance [LexStableColimLocallyCartesianClosed C] :
--     haveI : HasFiniteWidePullbacks C := by sorry -- TODO: figure out how we can inline an instance.
--     LexLocallyCartesianClosed C where
--   over_cc I := by infer_instance

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
instance cartesianClosed' [HasFiniteWidePullbacks C] [LexLocallyCartesianClosed C] :
    haveI : HasFiniteProducts C := by sorry
    CartesianClosed C := by sorry

-- Might be useful to have products as pullbacks over terminal.
-- TODO: figure out a way to not include `HasFiniteProducts C`, this is perhaps related to the fact that there is not instance of `HasFiniteProducts C` from `HasTerminal C` and `HasFiniteWidePullbacks C`.
instance cartesianClosed [HasFiniteWidePullbacks C] [HasFiniteProducts C] [LexStableColimLocallyCartesianClosed C] :
    CartesianClosed C :=
  cartesianClosedOfEquiv (equivOverTerminal C (terminal C) terminalIsTerminal).symm

-- TODO (SH): The slices of a locally cartesian closed category are locally cartesian closed.

--TODO (SH): We need to prove some basic facts about pushforwards.
