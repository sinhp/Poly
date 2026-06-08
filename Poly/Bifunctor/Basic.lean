/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Adjunction.Basic

import Poly.ForMathlib.CategoryTheory.NatIso
import Poly.ForMathlib.CategoryTheory.Types

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## Composition of bifunctors -/

namespace CategoryTheory.Functor

variable {𝒞 𝒟' 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟'] [Category 𝒟] [Category ℰ]

/-- Precompose a bifunctor in the second argument.
Note that `G ⋙₂ F ⋙ P = F ⋙ G ⋙₂ P` definitionally. -/
@[simps]
def comp₂ (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map f := whiskerLeft F (P.map f)

@[inherit_doc]
scoped [CategoryTheory] infixr:80 " ⋙₂ " => Functor.comp₂

@[simp]
theorem comp_comp₂ {𝒟'' : Type*} [Category 𝒟'']
    (F : 𝒟'' ⥤ 𝒟') (G : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) :
    (F ⋙ G) ⋙₂ P = F ⋙₂ (G ⋙₂ P) := rfl

/-- Composition with `F,G` ordered like the arguments of `P` is considered `simp`ler. -/
@[simp]
theorem comp₂_comp {𝒞' : Type*} [Category 𝒞']
    (F : 𝒞' ⥤ 𝒞) (G : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) :
    G ⋙₂ (F ⋙ P) = F ⋙ (G ⋙₂ P) := rfl

@[simps!]
def comp₂_iso {F₁ F₂ : 𝒟' ⥤ 𝒟} {P₁ P₂ : 𝒞 ⥤ 𝒟 ⥤ ℰ}
    (i : F₁ ≅ F₂) (j : P₁ ≅ P₂) : F₁ ⋙₂ P₁ ≅ F₂ ⋙₂ P₂ :=
  NatIso.ofComponents₂ (fun C D => (j.app C).app (F₁.obj D) ≪≫ (P₂.obj C).mapIso (i.app D))
    (fun _ _ => by simp [NatTrans.naturality_app_assoc])
    (fun C f => by
      have := congr_arg (P₂.obj C).map (i.hom.naturality f)
      simp only [map_comp] at this
      simp [this])

@[simps!]
def comp₂_isoWhiskerLeft {P₁ P₂ : 𝒞 ⥤ 𝒟 ⥤ ℰ} (F : 𝒟' ⥤ 𝒟) (i : P₁ ≅ P₂) :
    F ⋙₂ P₁ ≅ F ⋙₂ P₂ :=
  comp₂_iso (Iso.refl F) i

@[simps!]
def comp₂_isoWhiskerRight {F₁ F₂ : 𝒟' ⥤ 𝒟} (i : F₁ ≅ F₂) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) :
    F₁ ⋙₂ P ≅ F₂ ⋙₂ P :=
  comp₂_iso i (Iso.refl P)

end CategoryTheory.Functor

/-! ## Natural isomorphisms of bifunctors -/

namespace CategoryTheory
universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {𝒟 : Type*} [Category 𝒟]

namespace coyoneda

theorem comp₂_naturality₂_left (F : 𝒟 ⥤ 𝒞) (P : 𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v)
    (i : F ⋙₂ coyoneda (C := 𝒞) ⟶ P) (X Y : 𝒞) (Z : 𝒟) (f : X ⟶ Y) (g : Y ⟶ F.obj Z) :
    -- The `op`s really are a pain. Why can't they be definitional like in Lean 3 :(
    (i.app <| .op X).app Z (f ≫ g) = (P.map f.op).app Z ((i.app <| .op Y).app Z g) := by
  simpa [Functor.comp₂] using (FunctorToTypes.naturality₂_left _ _ i f.op g)

theorem comp₂_naturality₂_right (F : 𝒟 ⥤ 𝒞) (P : 𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v)
    (i : F ⋙₂ coyoneda (C := 𝒞) ⟶ P) (X : 𝒞) (Y Z : 𝒟) (f : X ⟶ F.obj Y) (g : Y ⟶ Z) :
    (i.app <| .op X).app Z (f ≫ F.map g) = (P.obj <| .op X).map g ((i.app <| .op X).app Y f) := by
  simpa [Functor.comp₂] using (FunctorToTypes.naturality₂_right _ _ i g f)

end coyoneda

namespace Adjunction

variable {𝒟 : Type*} [Category 𝒟]

/-- For `F ⊣ G`, `𝒟(FX, Y) ≅ 𝒞(X, GY)`. -/
def coyoneda_iso {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (A : F ⊣ G) :
    F.op ⋙ coyoneda (C := 𝒟) ≅ G ⋙₂ coyoneda (C := 𝒞) :=
  NatIso.ofComponents₂ (fun C D => Equiv.toIso <| A.homEquiv C.unop D)
    (fun _ σ => by
      ext g
      exact A.homEquiv_naturality_left σ.unop g)
    (fun _ f => by
      ext g
      exact A.homEquiv_naturality_right g f)

end Adjunction
end CategoryTheory
