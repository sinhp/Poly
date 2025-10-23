/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Poly.UvPoly.Basic
import Poly.Bifunctor.Sigma

noncomputable section

namespace CategoryTheory.UvPoly
open Limits Over ExponentiableMorphism Functor

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {E B : C} (P : UvPoly E B)

/-- Sends `(Γ, X)` to `Σ(b : Γ ⟶ B), 𝒞(pullback b P.p, X)`.
This is equivalent to the type of partial product cones with apex `Γ` over `X`. -/
@[simps! obj_obj map_app]
def partProdsOver : Cᵒᵖ ⥤ C ⥤ Type v :=
  Functor.Sigma
    ((Over.equivalence_Elements B).functor ⋙ (Over.pullback P.p).op ⋙
      (Over.forget E).op ⋙ coyoneda (C := C))

@[simp]
theorem partProdsOver_obj_map {X Y : C} (Γ : Cᵒᵖ) (f : X ⟶ Y) (x : (P.partProdsOver.obj Γ).obj X) :
    (P.partProdsOver.obj Γ).map f x = ⟨x.1, x.2 ≫ f⟩ := by
  dsimp [partProdsOver]
  have : 𝟙 Γ.unop ≫ x.1 = x.1 := by simp
  ext : 1
  . simp
  . dsimp
    rw! (castMode := .all) [this]
    simp

variable [HasTerminal C]

/-- `𝒞(Γ, PₚX) ≅ Σ(b : Γ ⟶ B), 𝒞(b*p, X)` -/
def iso_Sigma (P : UvPoly E B) :
    P.functor ⋙₂ coyoneda (C := C) ≅ P.partProdsOver :=
  calc
    P.functor ⋙₂ coyoneda (C := C) ≅
        (star E ⋙ pushforward P.p) ⋙₂ (Over.forget B ⋙₂ coyoneda (C := C)) :=
      Iso.refl _

    _ ≅ (star E ⋙ pushforward P.p) ⋙₂ Functor.Sigma
        ((equivalence_Elements B).functor ⋙ coyoneda (C := Over B)) :=
      comp₂_isoWhiskerLeft _ (forget_iso_Sigma B)

    _ ≅ Functor.Sigma
        ((equivalence_Elements B).functor ⋙
          star E ⋙₂ pushforward P.p ⋙₂ coyoneda (C := Over B)) :=
      -- Q: better make `comp₂_Sigma` an iso and avoid `eqToIso`?
      eqToIso (by simp [comp₂_Sigma])

    _ ≅ _ :=
      let i :=
        calc
          star E ⋙₂ pushforward P.p ⋙₂ coyoneda (C := Over B) ≅
              star E ⋙₂ (Over.pullback P.p).op ⋙ coyoneda (C := Over E) :=
            comp₂_isoWhiskerLeft (star E) (Adjunction.coyoneda_iso <| adj P.p).symm

          _ ≅ (Over.pullback P.p).op ⋙ star E ⋙₂ coyoneda (C := Over E) :=
            Iso.refl _

          _ ≅ (Over.pullback P.p).op ⋙ (Over.forget E).op ⋙ coyoneda (C := C) :=
            isoWhiskerLeft (Over.pullback P.p).op (Adjunction.coyoneda_iso <| forgetAdjStar E).symm;

      Functor.Sigma.isoCongrRight (isoWhiskerLeft _ i)

def equiv (Γ X : C) : (Γ ⟶ P.functor.obj X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) :=
  Iso.toEquiv <| (P.iso_Sigma.app (.op Γ)).app X

theorem equiv_app (Γ X : C) (be : Γ ⟶ P.functor.obj X) :
    P.equiv Γ X be = (P.iso_Sigma.hom.app <| .op Γ).app X be := by
  dsimp [equiv]

lemma equiv_naturality_left {Δ Γ : C} (σ : Δ ⟶ Γ) (X : C) (be : Γ ⟶ P.functor.obj X) :
    P.equiv Δ X (σ ≫ be) =
      let p := P.equiv Γ X be
      ⟨σ ≫ p.1, pullback.lift (pullback.fst .. ≫ σ) (pullback.snd ..)
        (Category.assoc (obj := C) .. ▸ pullback.condition) ≫ p.2⟩ := by
  conv_lhs => rw [equiv_app, coyoneda.comp₂_naturality₂_left, ← equiv_app]
  simp

-- NOTE(WN): As of Lean 4.25, kernel typechecking time is down to 1s from 10s?!
lemma equiv_naturality_right {Γ X Y : C} (be : Γ ⟶ P.functor.obj X) (f : X ⟶ Y) :
    equiv P Γ Y (be ≫ P.functor.map f) =
      let p := equiv P Γ X be
      ⟨p.1, p.2 ≫ f⟩ := by
  conv_lhs => rw [equiv_app, coyoneda.comp₂_naturality₂_right, ← equiv_app]
  simp

end CategoryTheory.UvPoly
