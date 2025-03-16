/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.NatIso

namespace CategoryTheory.NatIso

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]

/-- Natural isomorphism of bifunctors from naturality in both arguments. -/
def ofComponents₂ {F G : 𝒞 ⥤ 𝒟 ⥤ ℰ}
    (app : ∀ Γ X, (F.obj Γ).obj X ≅ (G.obj Γ).obj X)
    -- binaturality_left?
    (naturality_left : ∀ {Γ Δ : 𝒞} (X : 𝒟) (σ : Γ ⟶ Δ),
      (F.map σ).app X ≫ (app Δ X).hom = (app Γ X).hom ≫ (G.map σ).app X := by aesop_cat)
    (naturality_right : ∀ {X Y : 𝒟} (Γ : 𝒞) (f : X ⟶ Y),
      (F.obj Γ).map f ≫ (app Γ Y).hom = (app Γ X).hom ≫ (G.obj Γ).map f := by aesop_cat) :
    F ≅ G :=
  NatIso.ofComponents
    (fun Γ => NatIso.ofComponents (app Γ) (fun f => by simpa using naturality_right Γ f))
    (fun σ => by ext X : 2; simpa using naturality_left X σ)

end CategoryTheory.NatIso
