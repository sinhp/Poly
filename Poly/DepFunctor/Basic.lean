/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Poly.Util

namespace CategoryTheory

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]

/-! ## Dependent functors -/

/-- A functor into `𝒟` that depends on `F`
in other words `∫F ⥤ 𝒟` where all the `F(Γ)` are discrete,
spelled out in elementary terms.

(In the general case, we would have
`map : ∀ ⦃Γ Δ⦄ ⦃b : F.obj Γ⦄ ⦃c : F.obj Δ⦄
  (σ : Γ ⟶ Δ) (f : F.map σ b ⟶ c), obj b ⟶ obj c`.)

Equivalently, this is a (lax or strict or something) transformation `F ⟶ const 𝒟`. -/
-- NOTE: A more mathlib-ready, general approach might use `∫F ⥤ 𝒟`,
-- and introduce a special-case constructor for discrete `F(Γ)`
-- with an argument for each field of this structure. -/
structure DepFunctor (F : 𝒞 ⥤ Type*) (𝒟 : Type*) [Category 𝒟] where
  obj : ∀ ⦃Γ⦄, F.obj Γ → 𝒟
  -- Forded to avoid `eqToHom` in the axioms.
  map : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ), c = F.map σ b → (obj b ⟶ obj c)
  map_id : ∀ ⦃Γ⦄ b h, map (𝟙 Γ) b b h = 𝟙 (obj b) := by aesop_cat
  /-- **Note about `simp`.**
  The two `map` equalities in the LHS imply the one in the RHS, but not vice-versa.
  This axiom is thus stated in a "packing" rather than an "unpacking" direction,
  so that `simp` can apply it automatically by matching `h₁` and `h₂`.
  However, we do not mark it `simp` globally,
  preferring `map_comp'` whenever it applies. -/
  map_comp : ∀ ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) b c d h₁ h₂,
    map σ b c h₁ ≫ map τ c d h₂ = map (σ ≫ τ) b d (by simp [h₁, h₂]) := by aesop_cat

namespace DepFunctor

attribute [simp] map_id

/-- Specialized variant of `(map_comp ..).symm` that `simp` can match against. -/
@[simp]
theorem map_comp' {F : 𝒞 ⥤ Type*} {G : DepFunctor F 𝒟} ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) b h :
    G.map (σ ≫ τ) b (F.map τ (F.map σ b)) h = G.map σ b (F.map σ b) rfl ≫ G.map τ _ _ rfl :=
  (G.map_comp σ τ ..).symm

@[simps]
def isoLeft.{v} {F₁ F₂ : 𝒞 ⥤ Type v} (G : DepFunctor F₁ 𝒟) (i : F₂ ≅ F₁) : DepFunctor F₂ 𝒟 where
  obj Γ b := G.obj (i.hom.app Γ b)
  map Γ _ σ _ _ eq := G.map σ _ _ (by simp [eq, FunctorToTypes.naturality])
  map_id := by simp
  map_comp := by simp [G.map_comp]

end DepFunctor

@[ext]
structure DepNatTrans {F : 𝒞 ⥤ Type*} (G₁ G₂ : DepFunctor F 𝒟) where
  app : ∀ ⦃Γ⦄ (b : F.obj Γ), G₁.obj b ⟶ G₂.obj b
  naturality : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ) h,
    app b ≫ G₂.map σ b c h = G₁.map σ b c h ≫ app c := by aesop_cat

@[simps]
instance (F : 𝒞 ⥤ Type*) : Category (DepFunctor F 𝒟) where
  Hom := DepNatTrans
  id G := { app := fun _ _ => 𝟙 _ }
  comp η ν := {
    app := fun _ b => η.app b ≫ ν.app b
    naturality := by simp [reassoc_of% η.naturality, ν.naturality]
  }

namespace DepNatTrans

variable {F : 𝒞 ⥤ Type*} {Γ : 𝒞} (b : F.obj Γ)

@[ext]
theorem ext' {G₁ G₂ : DepFunctor F 𝒟} {α β : G₁ ⟶ G₂} (w : α.app = β.app) : α = β :=
  DepNatTrans.ext w

@[simp]
theorem id_app (G₁ : DepFunctor F 𝒟) : (𝟙 G₁ : G₁ ⟶ G₁).app b = 𝟙 (G₁.obj b) := rfl

@[reassoc (attr := simp)]
theorem comp_app {G₁ G₂ G₃ : DepFunctor F 𝒟} (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃) :
    (α ≫ β).app b = α.app b ≫ β.app b := rfl

theorem naturality_app {G₁ G₂ : DepFunctor F (𝒟 ⥤ ℰ)} (α : G₁ ⟶ G₂)
    {Γ Δ : 𝒞} (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ) h (X : 𝒟) :
    (G₁.map σ b c h).app X ≫ (α.app c).app X = (α.app b).app X ≫ (G₂.map σ b c h).app X :=
  (congr_fun (congr_arg NatTrans.app (α.naturality σ b c h)) X).symm

end DepNatTrans

namespace DepNatIso

variable {F : 𝒞 ⥤ Type*} {G₁ G₂ : DepFunctor F 𝒟}

@[reassoc (attr := simp)]
theorem hom_inv_id_app {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) :
    α.hom.app b ≫ α.inv.app b = 𝟙 (G₁.obj b) := by
  simp [← DepNatTrans.comp_app]

@[reassoc (attr := simp)]
theorem inv_hom_id_app {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) :
    α.inv.app b ≫ α.hom.app b = 𝟙 (G₂.obj b) := by
  simp [← DepNatTrans.comp_app]

instance hom_app_isIso {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) : IsIso (α.hom.app b) :=
  ⟨α.inv.app b, by simp⟩

instance inv_app_isIso {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) : IsIso (α.inv.app b) :=
  ⟨α.hom.app b, by simp⟩

def ofComponents
    (app : ∀ {Γ} (b : F.obj Γ), G₁.obj b ≅ G₂.obj b)
    (naturality : ∀ {Γ Δ} (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ) h,
      (app b).hom ≫ G₂.map σ b c h = G₁.map σ b c h ≫ (app c).hom) :
    G₁ ≅ G₂ where
  hom := { app := fun _ b => (app b).hom }
  inv := {
    app := fun _ b => (app b).inv
    naturality := fun _ _ σ b c h => by
      have : (app b).inv ≫ (app b).hom ≫ G₂.map σ b c h ≫ (app c).inv =
             (app b).inv ≫ G₁.map σ b c h ≫ (app c).hom ≫ (app c).inv := by
        simp [reassoc_of% naturality]
      simpa using this.symm
  }

variable {G₁ G₂ : DepFunctor F (Type v)}

@[simp]
theorem hom_inv_id_app_apply {Γ : 𝒞} (α : G₁ ≅ G₂) (X : F.obj Γ) (x) :
    α.inv.app X (α.hom.app X x) = x :=
  congr_fun (hom_inv_id_app α X) x

@[simp]
theorem inv_hom_id_app_apply {Γ : 𝒞} (α : G₁ ≅ G₂) (X : F.obj Γ) (x) :
    α.hom.app X (α.inv.app X x) = x :=
  congr_fun (inv_hom_id_app α X) x

variable {G₁ G₂ : DepFunctor F (𝒟 ⥤ Type v)}

@[simp]
theorem hom_inv_id_app_app_apply {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) (X : 𝒟) (x) :
    (α.inv.app b).app X ((α.hom.app b).app X x) = x :=
  congr_fun (congr_fun (congr_arg NatTrans.app (hom_inv_id_app α b)) X) x

@[simp]
theorem inv_hom_id_app_app_apply {Γ : 𝒞} (α : G₁ ≅ G₂) (b : F.obj Γ) (X : 𝒟) (x) :
    (α.hom.app b).app X ((α.inv.app b).app X x) = x :=
  congr_fun (congr_fun (congr_arg NatTrans.app (inv_hom_id_app α b)) X) x

end DepNatIso
