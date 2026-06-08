/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.Types.Basic

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
    (σ.app C₂).app D₁ ((F.map f).app D₁ x) = (G.map f).app D₁ ((σ.app C₁).app D₁ x) := by
  change ((σ.app C₂).app D₁ : _ → _) (((F.map f).app D₁ : _ → _) x) =
    ((G.map f).app D₁ : _ → _) (((σ.app C₁).app D₁ : _ → _) x)
  have h₀ := congrArg NatTrans.app (σ.naturality f)
  have h₁ := congrFun h₀ D₁
  have h₂ := congrArg (fun e : (F.obj C₁).obj D₁ ⟶ (G.obj C₂).obj D₁ => (e : _ → _)) h₁
  exact congrFun h₂ x

theorem naturality₂_right (σ : F ⟶ G) (f : D₁ ⟶ D₂) (x : (F.obj C₁).obj D₁) :
    (σ.app C₁).app D₂ ((F.obj C₁).map f x) = (G.obj C₁).map f ((σ.app C₁).app D₁ x) :=
  NatTrans.naturality_apply (σ.app C₁) f x

@[simp]
theorem hom_inv_id_app_app_apply (α : F ≅ G) (C D) (x) :
    (α.inv.app C).app D ((α.hom.app C).app D x) = x := by
  change ((α.inv.app C).app D : _ → _) (((α.hom.app C).app D : _ → _) x) = x
  have h := congrArg (fun e : (F.obj C).obj D ⟶ (F.obj C).obj D => (e : _ → _))
    (α.hom_inv_id_app_app C D)
  exact congrFun h x

@[simp]
theorem inv_hom_id_app_app_apply (α : F ≅ G) (C D) (x) :
    (α.hom.app C).app D ((α.inv.app C).app D x) = x := by
  change ((α.hom.app C).app D : _ → _) (((α.inv.app C).app D : _ → _) x) = x
  have h := congrArg (fun e : (G.obj C).obj D ⟶ (G.obj C).obj D => (e : _ → _))
    (α.inv_hom_id_app_app C D)
  exact congrFun h x
