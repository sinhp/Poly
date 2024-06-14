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

import Mathlib.Tactic.ApplyFun

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
    (whiskerRight α H) ≫ (whiskerLeft G β) = (whiskerLeft F β) ≫ (whiskerRight α K) := by aesop_cat
--   ext; unfold whiskerLeft; simp

end NaturalityOfWhiskering

section ReproveMates

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D]
 [Category.{v₃} E] [Category.{v₄} F]
variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

def RightMate :
    (G ⋙ L₂ ⟶ L₁ ⋙ H₁) → (R₁ ⋙ G ⟶ H₁ ⋙ R₂) := by
  intro α
  have R₁Gη₂ := whiskerLeft (R₁ ⋙ G) adj₂.unit
  have R₁αR₂ := whiskerRight (whiskerLeft R₁ α) R₂
  have ε₁H₁R₂ := whiskerRight adj₁.counit (H₁ ⋙ R₂)
  exact R₁Gη₂ ≫ R₁αR₂ ≫ ε₁H₁R₂

def LeftMate :
    (R₁ ⋙ G ⟶ H₁ ⋙ R₂) → (G ⋙ L₂ ⟶ L₁ ⋙ H₁) := by
  intro α
  have η₁GL₂ := whiskerRight adj₁.unit (G ⋙ L₂)
  have L₁αL₂ := whiskerRight (whiskerLeft L₁ α) L₂
  have H₁R₂ε₂ := whiskerLeft (L₁ ⋙ H₁) adj₂.counit
  exact η₁GL₂ ≫ L₁αL₂ ≫ H₁R₂ε₂

def Mates :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) where
      toFun := by
        intro α
        have R₁Gη₂ := whiskerLeft (R₁ ⋙ G) adj₂.unit
        have R₁αR₂ := whiskerRight (whiskerLeft R₁ α) R₂
        have ε₁HR₂ := whiskerRight adj₁.counit (H ⋙ R₂)
        exact R₁Gη₂ ≫ R₁αR₂ ≫ ε₁HR₂
      invFun := by
        intro β
        have η₁GL₂ := whiskerRight adj₁.unit (G ⋙ L₂)
        have L₁βL₂ := whiskerRight (whiskerLeft L₁ β) L₂
        have HR₂ε₂ := whiskerLeft (L₁ ⋙ H) adj₂.counit
        exact η₁GL₂ ≫ L₁βL₂ ≫ HR₂ε₂
      left_inv := by
        intro α
        ext
        unfold whiskerRight whiskerLeft
        simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc, counit_naturality,
          counit_naturality_assoc, left_triangle_components_assoc]
        rw [← assoc, ← Functor.comp_map, α.naturality, Functor.comp_map, assoc, ← H.map_comp, left_triangle_components, map_id]
        simp only [comp_obj, comp_id] -- Why can't I rewrite instead?

        -- intro α
        -- simp
        -- rw [← whiskerRight_twice _ _ adj₁.counit]
        -- rw [← whiskerRight_left _ (whiskerRight adj₁.counit H) _, whiskerRight_twice]
        -- have step1 :=
        --   WhiskeringNaturality
        --     (whiskerLeft L₁ (whiskerRight adj₁.counit H)) adj₂.counit
        -- have := Functor.id_comp H
        -- rw [Functor.id_comp H] at step1

        -- simp_rw [step1]
        -- simp_rw [WhiskeringNaturality _ adj₂.counit]

-- WhiskeringNaturality α β :
--    (whiskerRight α H) ≫ (whiskerLeft G β)
--        = (whiskerLeft F β) ≫ (whiskerRight α K)
      right_inv := by
        intro β
        ext
        unfold whiskerLeft whiskerRight
        simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc,
          unit_naturality_assoc, right_triangle_components_assoc]
        rw [← assoc, ← Functor.comp_map, assoc, ← β.naturality, ← assoc, Functor.comp_map, ← G.map_comp, right_triangle_components, map_id, id_comp]

theorem RightMateEqualsTransferNatTrans
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    RightMate adj₁ adj₂ α = (transferNatTrans adj₁ adj₂) α := by
  ext; unfold RightMate transferNatTrans; simp

theorem LeftMateEqualsTransferNatTrans.symm
    (α : R₁ ⋙ G ⟶ H ⋙ R₂) :
    LeftMate adj₁ adj₂ α = (transferNatTrans adj₁ adj₂).symm α := by
  ext; unfold LeftMate transferNatTrans; simp

end ReproveMates

section MatesVComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable {G₁ : A ⥤ C}{G₂ : C ⥤ E}{H₁ : B ⥤ D}{H₂ : D ⥤ F}
variable {L₁ : A ⥤ B}{R₁ : B ⥤ A} {L₂ : C ⥤ D}{R₂ : D ⥤ C}
variable {L₃ : E ⥤ F}{R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

def LeftAdjointSquare.vcomp :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) → (G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) →
    ((G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ (H₁ ⋙ H₂)) := fun α β ↦
  (whiskerLeft G₁ β) ≫ (whiskerRight α H₂)

def RightAdjointSquare.vcomp :
    (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) → (R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) →
    (R₁ ⋙ (G₁ ⋙ G₂) ⟶ (H₁ ⋙ H₂) ⋙ R₃) := fun α β ↦
  (whiskerRight α G₂) ≫ (whiskerLeft H₁ β)

theorem Mates.vcomp
  (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁)
  (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
  (Mates (G := G₁ ⋙ G₂) (H := H₁ ⋙ H₂) adj₁ adj₃) (LeftAdjointSquare.vcomp α β)
    =
  RightAdjointSquare.vcomp
  ( (Mates (G := G₁) (H := H₁) adj₁ adj₂) α)
  ( (Mates (G := G₂) (H := H₂) adj₂ adj₃) β)
     := by
  unfold LeftAdjointSquare.vcomp RightAdjointSquare.vcomp Mates
  ext b
  simp
  slice_rhs 1 4 =>
    {
      rw [← assoc, ← assoc]
      rw [← unit_naturality (adj₃)]
    }
  rw [L₃.map_comp, R₃.map_comp]
  slice_rhs 3 4  =>
    { rw [← Functor.comp_map G₂ L₃, ← R₃.map_comp]
      rw [β.naturality]
    }
  rw [L₃.map_comp, R₃.map_comp]
  slice_rhs 3 4 =>
    { rw [← R₃.map_comp, ← Functor.comp_map G₂ L₃, ← assoc]
      rw [β.naturality]
    }
  rw [R₃.map_comp, R₃.map_comp]
  slice_rhs 2 3 =>
    {
      rw [← R₃.map_comp, ← Functor.comp_map G₂ L₃]
      rw [β.naturality]
    }
  slice_rhs 4 5 =>
    {
      rw [← R₃.map_comp, Functor.comp_map L₂ _, ← Functor.comp_map _ L₂, ← H₂.map_comp]
      rw [adj₂.counit.naturality]
    }
  simp
  slice_rhs 4 5 =>
    {
      rw [← R₃.map_comp, ← H₂.map_comp, ← Functor.comp_map _ L₂]
      rw [adj₂.counit.naturality]
    }
  simp
  slice_rhs 3 4 =>
    {
      rw [← R₃.map_comp, ← H₂.map_comp]
      rw [left_triangle_components]
    }
  simp only [map_id, id_comp]

end MatesVComp

section MatesHComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B][Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E][Category.{v₆} F]
variable {G : A ⥤ D}{H : B ⥤ E}{K : C ⥤ F}
variable {L₁ : A ⥤ B}{R₁ : B ⥤ A} {L₂ : D ⥤ E}{R₂ : E ⥤ D}
variable {L₃ : B ⥤ C}{R₃ : C ⥤ B} {L₄ : E ⥤ F}{R₄ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
variable (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

def LeftAdjointSquare.hcomp :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) → (H ⋙ L₄ ⟶ L₃ ⋙ K) →
    (G ⋙ (L₂ ⋙ L₄) ⟶ (L₁ ⋙ L₃) ⋙ K) := fun α β ↦
  (whiskerRight α L₄) ≫ (whiskerLeft L₁ β)

def RightAdjointSquare.hcomp :
    (R₁ ⋙ G ⟶ H ⋙ R₂) → (R₃ ⋙ H ⟶ K ⋙ R₄) →
    ((R₃ ⋙ R₁) ⋙ G ⟶ K ⋙ (R₄ ⋙ R₂)) := fun α β ↦
  (whiskerLeft R₃ α) ≫ (whiskerRight β R₂)

theorem Mates.hcomp
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (β : H ⋙ L₄ ⟶ L₃ ⋙ K) :
    (Mates (G := G) (H := K)
      (adj₁.comp adj₃) (adj₂.comp adj₄)) (LeftAdjointSquare.hcomp α β) =
    RightAdjointSquare.hcomp
      ((Mates adj₁ adj₂) α)
      ((Mates adj₃ adj₄) β) := by
  unfold LeftAdjointSquare.hcomp RightAdjointSquare.hcomp Mates Adjunction.comp
  ext c
  simp
  slice_rhs 3 4 =>
    {
      rw [← R₂.map_comp]
      rw [← unit_naturality (adj₄)]
    }
  slice_rhs 2 3 =>
    {
      rw [← R₂.map_comp, ← assoc]
      rw [← unit_naturality (adj₄)]
    }
  rw [R₂.map_comp, R₂.map_comp]
  slice_rhs 4 5 =>
    {
      rw [← R₂.map_comp, ← R₄.map_comp, ← Functor.comp_map _ L₄]
      rw [β.naturality]
    }
  simp only [comp_obj, Functor.comp_map, map_comp, assoc]

end MatesHComp

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
