/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.Types

namespace CategoryTheory.FunctorToTypes

/-! Repetitive lemmas about bifunctors into `Type`.

Q: Is there a better way?
Mathlib doesn't seem to think so:
see `hom_inv_id_app`, `hom_inv_id_app_app`, `hom_inv_id_app_app_app`.
Can a `simproc` that tries `congr_fun/congr_arg simpLemma` work? -/

universe w
variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F G : 𝒞 ⥤ 𝒟 ⥤ Type w)
  {C₁ C₂ : 𝒞} {D₁ D₂ : 𝒟}

theorem naturality₂_left (σ : F ⟶ G) (f : C₁ ⟶ C₂) (x : (F.obj C₁).obj D₁) :
    (σ.app C₂).app D₁ ((F.map f).app D₁ x) = (G.map f).app D₁ ((σ.app C₁).app D₁ x) :=
  congr_fun (congr_fun (congr_arg NatTrans.app (σ.naturality f)) D₁) x

theorem naturality₂_right (σ : F ⟶ G) (f : D₁ ⟶ D₂) (x : (F.obj C₁).obj D₁) :
    (σ.app C₁).app D₂ ((F.obj C₁).map f x) = (G.obj C₁).map f ((σ.app C₁).app D₁ x) :=
  naturality ..

@[simp]
theorem hom_inv_id_app_app_apply (α : F ≅ G) (C D) (x) :
    (α.inv.app C).app D ((α.hom.app C).app D x) = x :=
  congr_fun (α.hom_inv_id_app_app C D) x

@[simp]
theorem inv_hom_id_app_app_apply (α : F ≅ G) (C D) (x) :
    (α.hom.app C).app D ((α.inv.app C).app D x) = x :=
  congr_fun (α.inv_hom_id_app_app C D) x
