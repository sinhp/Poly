/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

import Poly.LCCC.LCCC

/-!
# Beck-Chevalley natural transformations and natural isomorphisms
-/

namespace CategoryTheory

open Category Functor Adjunction Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace Over

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
  (transferNatTrans (G := Over.map f) (H := Over.map k) (mapAdjunction h) (mapAdjunction g)).toFun ((map.square f g h k w).hom)

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
  have orig := Trans.trans
            (mapComp f g)
            (Trans.trans (map.square f g h k w) (mapComp h k).symm)
  have :=
    (transferNatTransSelf_iso
      (mapAdjunction (h ≫ k)) (mapAdjunction (f ≫ g))) orig.hom
  have conjiso := asIso ((transferNatTransSelf
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
  sorry

end Over

namespace LCCC

variable [HasFiniteWidePullbacks C] (lccc : LCC C)


end LCCC
