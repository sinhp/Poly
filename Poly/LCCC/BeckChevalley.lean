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

-- Naturality of β implies naturality of whiskering.
@[simp]
theorem WhiskeringNaturality
    (α : F ⟶ G)(β : H ⟶ K) :
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

namespace Over
variable {C : Type u} [Category.{v} C]

@[simp]
theorem eqToHom.left_eq {X Y : C}(f g : X ⟶ Y) (w : f = g) (x : Over X) :
    ((eqToHom (congrArg Over.map w)).app x).left = 𝟙 (x.left) := by
  subst w; rfl

-- NOTE: If this were true, I'd replace map.square by an identity.
theorem map.comp.eq {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) :
    map f ⋙ map g = map (f ≫ g) := by
  fapply Functor.ext
  · dsimp [Over, Over.map]
    intro x
    unfold Comma.mapRight
    simp
  · intros x y u
    simp
    ext
    simp
    sorry
  --   simp_rw [eqToHom.left_eq]
  --   aesop_cat

  --  show ({..} : Comma _ _ ⥤ Comma _ _ ) = {..}

  -- -- congr 2
  -- -- rfl

  -- dsimp [Over, Functor.comp, Over.map]
  -- congr!



section BeckChevalleyUsingIsomorphism1

theorem test {X : C} : (Iso.refl X).hom = 𝟙 X := by exact rfl

--
instance map.square {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k := by
  have fgiso := (mapComp f g).symm
  have hkiso := mapComp h k
  have wiso := eqToIso (congrArg Over.map w)
--  rw [w] at fgiso
  exact (Iso.trans (Iso.trans fgiso wiso) hkiso)

theorem map.comp.left_id {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) (x : Over X) :
    ((mapComp f g).hom.app x).left = 𝟙 (x.left) := by
  unfold mapComp
  simp

theorem map.comp.symm.left_id {X Y Z : C}(f : X ⟶ Y)(g : Y ⟶ Z) (x : Over X) :
    ((mapComp f g).symm.hom.app x).left = 𝟙 (x.left) := by
  unfold mapComp
  simp

-- NOTE: This is one reason why the current definition of map.square is bad.
theorem map.square.app.left_id {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (a : Over W) :
    ((map.square f g h k w).hom.app a).left = 𝟙 (a.left) := by
  unfold map.square
  simp only [comp_obj, map_obj_left, comp_app,
    comp_left]
  simp only [Iso.trans_hom, comp_app, comp_obj, comp_left, map_obj_left, Iso.instTransIso_trans]
  rw [map.comp.left_id]
  simp only [comp_id, comp_left]
  rw [map.comp.symm.left_id]
  simp
  erw [eqToHom.left_eq]


/-- The Beck-Chevalley natural transformation. -/
instance pullback.NatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange h ⋙ Over.map f ⟶ Over.map k ⋙ baseChange g :=
  (mateEquiv (mapAdjunction h) (mapAdjunction g)) ((map.square f g h k w).hom)

/-- Calculating the counit components of mapAdjunction. -/
theorem mapAdjunction.counit.app_pullback.fst  [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (y : Over Y) :
    ((mapAdjunction f).counit.app y).left = pullback.fst := by simp

def pullback.NatTrans.app.map [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).obj ((baseChange h ⋙ map f).obj y) ⟶ (forget X).obj ((map k ⋙ baseChange g).obj y) :=
  pullback.map y.hom h (y.hom ≫ k) g (𝟙 y.left) f k (Eq.symm (id_comp (y.hom ≫ k))) w.symm

-- NOTE: This is another reason why the map.square is bad.
theorem pullback.NatTrans.app_pullback.lift [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((NatTrans f g h k w).app y) = pullback.NatTrans.app.map f g h k w y := by
  dsimp
  ext
  · unfold app.map pullback.map
    simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_id]
    unfold pullback.NatTrans mateEquiv
    dsimp
    unfold pullback.map
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_fst, ← assoc, pullback.lift_fst]
      }
    rw [mapAdjunction.counit.app_pullback.fst, ← assoc, ← assoc, pullback.lift_fst]
    simp only [id_comp, id_obj, const_obj_obj]
    -- uses the sorried lemma here
    rw [map.square.app.left_id]
    simp
  · unfold app.map pullback.map
    simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    unfold pullback.NatTrans mateEquiv
    dsimp
    unfold pullback.map
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_snd, ← assoc, pullback.lift_snd]
      }
    simp only [comp_id, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

-- NB: I seem to have symmetry of HasPullback but not IsPullback
theorem pullback.NatTrans.isPullback.componentIsIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) (y : Over Y) :
    IsIso ((forget X).map ((NatTrans f g h k w).app y)) := by
  rw [pullback.NatTrans.app_pullback.lift f g h k w y]
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

/-- The Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
theorem pullback.NatTrans.isPullback.isIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) :
    IsIso (pullback.NatTrans f g h k w) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro y
  have := pullback.NatTrans.isPullback.componentIsIso f g h k w hyp y
  apply (forget_reflects_iso (X := X)).reflects ((pullback.NatTrans f g h k w).app y)

end BeckChevalleyUsingIsomorphism1

-- NOTE: This is a repeat of the above with a less aesthetic definition of map square that lets me prove the Lemma. Here everything works.
section BeckChevalleyUsingIsomorphism2

instance map.squareALT {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k := by
  fapply NatIso.ofComponents
  · intro a
    refine isoMk ?app.hl ?app.hw
    · simp only [comp_obj, map_obj_left]
      exact (Iso.refl a.left)
    · simp only [comp_obj, map_obj_left, const_obj_obj, id_eq, Iso.refl_hom, map_obj_hom, id_obj,
      assoc, id_comp]
      exact congrArg (CategoryStruct.comp a.hom) (Eq.symm w)
  · aesop_cat

theorem map.squareALT.app.left_id {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (a : Over W) :
    ((map.squareALT f g h k w).hom.app a).left = 𝟙 (a.left) := by
  unfold map.squareALT
  simp


/-- The Beck-Chevalley natural transformation. -/
instance pullback.NatTransALT [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange h ⋙ Over.map f ⟶ Over.map k ⋙ baseChange g :=
  (mateEquiv (mapAdjunction h) (mapAdjunction g)) ((map.squareALT f g h k w).hom)

theorem pullback.NatTrans.app_pullback.liftALT [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((NatTransALT f g h k w).app y) = pullback.NatTrans.app.map f g h k w y := by
  dsimp
  ext
  · unfold app.map pullback.map
    simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_id]
    unfold pullback.NatTransALT mateEquiv
    dsimp
    unfold pullback.map
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_fst, ← assoc, pullback.lift_fst]
      }
    rw [mapAdjunction.counit.app_pullback.fst, ← assoc, ← assoc, pullback.lift_fst]
    simp only [id_comp, id_obj, const_obj_obj]
    rw [map.squareALT.app.left_id]
    simp
  · unfold app.map pullback.map
    simp only [map_obj_left, baseChange_obj_left, id_obj, const_obj_obj, map_obj_hom, comp_id,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    unfold pullback.NatTransALT mateEquiv
    dsimp
    unfold pullback.map
    slice_lhs 2 3 =>
      {
        rw [pullback.lift_snd, ← assoc, pullback.lift_snd]
      }
    simp only [comp_id, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

-- NB: I seem to have symmetry of HasPullback but not IsPullback
theorem pullback.NatTrans.isPullback.componentIsIsoALT [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) (y : Over Y) :
    IsIso ((forget X).map ((NatTransALT f g h k w).app y)) := by
  rw [pullback.NatTrans.app_pullback.liftALT f g h k w y]
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

/-- The Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
theorem pullback.NatTrans.isPullback.isIsoALT [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (hyp : IsLimit (PullbackCone.mk _ _ w.symm)) :
    IsIso (pullback.NatTransALT f g h k w) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro y
  have := pullback.NatTrans.isPullback.componentIsIsoALT f g h k w hyp y
  apply (forget_reflects_iso (X := X)).reflects ((pullback.NatTransALT f g h k w).app y)

end BeckChevalleyUsingIsomorphism2

/-- The missing natural isomorphism between pullback functors. -/
instance pullbackComp [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f := by
  have := conjugateEquiv
            (mapAdjunction (f ≫ g))
            ((mapAdjunction f).comp (mapAdjunction g)) (mapComp f g).symm.hom
  exact
    (asIso
      (conjugateEquiv
        (mapAdjunction (f ≫ g))
        ((mapAdjunction f).comp (mapAdjunction g))
        (mapComp f g).symm.hom))

instance pullback.NatIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange k ⋙ baseChange h ≅ baseChange g ⋙ baseChange f := by
  have orig : map (f ≫ g) ≅ map (h ≫ k)
    := Trans.trans
        (mapComp f g)
        (Trans.trans (map.square f g h k w) (mapComp h k).symm)
  have :=
    (conjugateEquiv_iso
      (mapAdjunction (h ≫ k)) (mapAdjunction (f ≫ g))) orig.hom
  have conjiso : baseChange (h ≫ k) ≅ baseChange (f ≫ g)
    := asIso ((conjugateEquiv
      (mapAdjunction (h ≫ k)) (mapAdjunction (f ≫ g)) ) orig.hom)
  exact (Trans.trans (Trans.trans (pullbackComp h k).symm conjiso)
            (pullbackComp f g))

instance pullback.NatIso' [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange k ⋙ baseChange h ≅ baseChange g ⋙ baseChange f := by
  have fgiso := pullbackComp f g
  have hkiso := (pullbackComp h k).symm
  rw [w] at fgiso
  exact (trans hkiso fgiso)

-- I think this should hold.
theorem pullback.NatIso.eq [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k):
    (pullback.NatIso f g h k w).hom = (pullback.NatIso' f g h k w).hom := by
  unfold pullback.NatIso pullback.NatIso'
  simp
  sorry


theorem pullback.NatIso.app.eq [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (z : Over Z):
    (pullback.NatIso f g h k w).app z = (pullback.NatIso' f g h k w).app z := by
  refine Iso.ext ?w
  unfold pullback.NatIso pullback.NatIso' pullbackComp
  dsimp [conjugateEquiv, mateEquiv]
  simp
  sorry

end Over

namespace LCCC

variable {C : Type u} [Category.{v} C]

variable [HasFiniteWidePullbacks C] (lccc : LCC C)


end LCCC
