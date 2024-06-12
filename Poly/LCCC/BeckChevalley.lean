/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Whiskering

import Poly.LCCC.LCCC

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
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by
  ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

section MissingFromMates

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable {G₁ : A ⥤ C}{G₂ : C ⥤ E}{H₁ : B ⥤ D}{H₂ : D ⥤ F}
variable {L₁ : A ⥤ B}{R₁ : B ⥤ A} {L₂ : C ⥤ D}{R₂ : D ⥤ C}
variable {L₃ : E ⥤ F}{R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

def RightMate :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) → (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) := by
  intro α
  have R₁G₁η₂ := whiskerLeft (R₁ ⋙ G₁) adj₂.unit
  have R₁αR₂ := whiskerRight (whiskerLeft R₁ α) R₂
  have ε₁H₁R₂ := whiskerRight adj₁.counit (H₁ ⋙ R₂)
  exact R₁G₁η₂ ≫ R₁αR₂ ≫ ε₁H₁R₂

def LeftMate :
    (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) → (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) := by
  intro α
  have η₁G₁L₂ := whiskerRight adj₁.unit (G₁ ⋙ L₂)
  have L₁αL₂ := whiskerRight (whiskerLeft L₁ α) L₂
  have H₁R₂ε₂ := whiskerLeft (L₁ ⋙ H₁) adj₂.counit
  exact η₁G₁L₂ ≫ L₁αL₂ ≫ H₁R₂ε₂

def Mates :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) ≃ (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) where
      toFun := by
        intro α
        have R₁G₁η₂ := whiskerLeft (R₁ ⋙ G₁) adj₂.unit
        have R₁αR₂ := whiskerRight (whiskerLeft R₁ α) R₂
        have ε₁H₁R₂ := whiskerRight adj₁.counit (H₁ ⋙ R₂)
        exact R₁G₁η₂ ≫ R₁αR₂ ≫ ε₁H₁R₂
      invFun := by
        intro β
        have η₁G₁L₂ := whiskerRight adj₁.unit (G₁ ⋙ L₂)
        have L₁βL₂ := whiskerRight (whiskerLeft L₁ β) L₂
        have H₁R₂ε₂ := whiskerLeft (L₁ ⋙ H₁) adj₂.counit
        exact η₁G₁L₂ ≫ L₁βL₂ ≫ H₁R₂ε₂
      left_inv := by
        intro α
        dsimp
        simp
        ext
        unfold whiskerRight whiskerLeft
        simp
        rw [← assoc, ← Functor.comp_map, α.naturality]
        simp
        rw [← H₁.map_comp]
        simp
        -- rw [← whiskerRight_twice _ _ adj₁.counit]
        -- rw [← whiskerRight_left _ (whiskerRight adj₁.counit H₁) _, whiskerRight_twice]
        -- have step1 :=
        --   WhiskeringNaturality
        --     ((whiskerLeft L₁ (whiskerRight adj₁.counit H₁)) ≫ (whiskerLeft L₁ (leftUnitor H₁).hom))
        --     adj₂.counit
        -- simp_rw [step1]
        -- simp_rw [WhiskeringNaturality _ adj₂.counit]

-- WhiskeringNaturality α β :
--    (whiskerRight α H) ≫ (whiskerLeft G β)
--        = (whiskerLeft F β) ≫ (whiskerRight α K)
      right_inv := sorry

theorem RightMateEqualsTransferNatTrans
    (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) :
    RightMate adj₁ adj₂ α = (transferNatTrans adj₁ adj₂) α := by
  ext; unfold RightMate transferNatTrans; simp

theorem LeftMateEqualsTransferNatTrans.symm
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) :
    LeftMate adj₁ adj₂ α = (transferNatTrans adj₁ adj₂).symm α := by
  ext; unfold LeftMate transferNatTrans; simp

def LeftAdjointSquare.vcomp :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) → (G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) →
    ((G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ (H₁ ⋙ H₂)) := by
  intros α β
  have αH₂ := whiskerRight α H₂
  have G₁β := whiskerLeft G₁ β
  exact G₁β ≫ αH₂ -- Why does this work? Requires associativity on the boundary.

def RightAdjointSquare.vcomp :
    (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) → (R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) →
    (R₁ ⋙ (G₁ ⋙ G₂) ⟶ (H₁ ⋙ H₂) ⋙ R₃) := by
  intros α β
  have αG₂ := whiskerRight α G₂
  have H₁β := whiskerLeft H₁ β
  exact αG₂ ≫ H₁β -- Why does this work? Requires associativity on the boundary.



theorem Mates.vcomp
  (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁)
  (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
  (transferNatTrans (G := G₁ ⋙ G₂) (H := H₁ ⋙ H₂) adj₁ adj₃) (LeftAdjointSquare.vcomp α β)
    =
  RightAdjointSquare.vcomp
  ( (transferNatTrans (G := G₁) (H := H₁) adj₁ adj₂) α)
  ( (transferNatTrans (G := G₂) (H := H₂) adj₂ adj₃) β)
     := by
  unfold LeftAdjointSquare.vcomp RightAdjointSquare.vcomp transferNatTrans
  simp
  sorry

end MissingFromMates


namespace Over

variable {C : Type u} [Category.{v} C]


instance map.square {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    Over.map f ⋙ Over.map g ≅ Over.map h ⋙ Over.map k := by
  have fgiso := (mapComp f g).symm
  have hkiso := mapComp h k
  rw [w] at fgiso
  exact (trans fgiso hkiso)

-- The Beck-Chevalley natural transformation.
instance pullback.NatTrans [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) :
    baseChange h ⋙ Over.map f ⟶ Over.map k ⋙ baseChange g :=
  (transferNatTrans (G := Over.map f) (H := Over.map k) (mapAdjunction h) (mapAdjunction g)) ((map.square f g h k w).hom)

-- The missing natural isomorphism between pullback functors
instance pullbackComp [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f := by
  have := transferNatTransSelf_iso
            (mapAdjunction (f ≫ g))
            ((mapAdjunction f).comp (mapAdjunction g)) (mapComp f g).symm.hom
  exact
    (asIso
      (transferNatTransSelf
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
    (transferNatTransSelf_iso
      (mapAdjunction (h ≫ k)) (mapAdjunction (f ≫ g))) orig.hom
  have conjiso : baseChange (h ≫ k) ≅ baseChange (f ≫ g)
    := asIso ((transferNatTransSelf
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
    (w : f ≫ g = h ≫ k) (z : Over Z):
    (pullback.NatIso f g h k w).app z = (pullback.NatIso' f g h k w).app z := by
  refine Iso.ext ?w
  unfold pullback.NatIso pullback.NatIso' pullbackComp
  dsimp [transferNatTransSelf, transferNatTrans]
  simp
  sorry

end Over

namespace LCCC

variable {C : Type u} [Category.{v} C]

variable [HasFiniteWidePullbacks C] (lccc : LCC C)


end LCCC
