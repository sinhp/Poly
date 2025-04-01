/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Poly.UvPoly.Basic

noncomputable section

namespace CategoryTheory.UvPoly
open Limits PartialProduct

universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] {E B : C}

/-- Universal property of the polynomial functor. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P @ X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) where
  toFun := P.proj
  invFun u := P.lift (Γ := Γ) (X := X) u.1 u.2
  left_inv f := by
    dsimp
    symm
    fapply partialProd.hom_ext ⟨fan P X, isLimitFan P X⟩
    · simp [partialProd.lift]
      rfl
    · sorry
  right_inv := by
    intro ⟨b, e⟩
    ext
    · simp only [proj_fst, lift_fst]
    · sorry

end CategoryTheory.UvPoly
