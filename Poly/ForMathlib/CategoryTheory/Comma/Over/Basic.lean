/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Category.Cat

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {T : Type u₁} [Category.{v₁} T]

namespace Over

/-- `Over.Sigma Y U` a shorthand for `(Over.map Y.hom).obj U`. This is the categoy-theoretic
analogue of `Sigma` for types.
-/
abbrev Sigma {X : T} (Y : Over X) (U : Over (Y.left)) : Over X :=
  (map Y.hom).obj U

namespace Sigma

variable {X : T}

lemma hom {Y : Over X} (Z : Over (Y.left)) : (Sigma Y Z).hom = Z.hom ≫ Y.hom := map_obj_hom

/-- `Σ_ ` is functorial in the second argument. -/
def map {Y : Over X} {Z Z' : Over (Y.left)} (g : Z ⟶ Z') : (Sigma Y Z) ⟶ (Sigma Y Z') :=
  (Over.map Y.hom).map g

lemma map_left {Y : Over X} {Z Z' : Over (Y.left)} {g : Z ⟶ Z'} :
    ((Over.map Y.hom).map g).left = g.left := Over.map_map_left

lemma map_homMk_left {Y : Over X} {Z Z' : Over (Y.left)} {g : Z ⟶ Z'} :
    map g = (Over.homMk g.left : Sigma Y Z ⟶ Sigma Y Z') := by
  rfl

/-- The first projection of the sigma object. -/
@[simps!]
def fst {Y : Over X} (Z : Over (Y.left)) : (Sigma Y Z) ⟶ Y := Over.homMk Z.hom

lemma map_comp_fst {Y : Over X} {Z Z' : Over (Y.left)} (g : Z ⟶ Z') :
    (Over.map Y.hom).map g ≫ fst Z' = fst Z := by
  ext
  simp [Sigma.fst, Over.w]

/-- Promoting a morphism `g : Σ_Y Z ⟶ Σ_Y Z'` in `Over X` with `g ≫ fst Z' = fst Z`
to a morphism `Z ⟶ Z'` in `Over (Y.left)`. -/
def overHomMk {Y : Over X} {Z Z' : Over (Y.left)} (g : Sigma Y Z ⟶ Sigma Y Z')
    (w : g ≫ fst Z' = fst Z := by aesop_cat) : Z ⟶ Z' :=
  Over.homMk g.left (congr_arg CommaMorphism.left w)

end Sigma

end Over

end CategoryTheory
