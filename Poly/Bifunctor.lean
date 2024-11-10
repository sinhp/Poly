import Mathlib.CategoryTheory.Functor.Currying

import Poly.Util
import Poly.Tactic.BanishCasts

/-! # Bifunctors

We define some constructions on bifunctors (aka profunctors),
that is functors in two arguments.

Their utility in Poly is as a tool for packaging and composing natural equivalences.
For example, given `F,H : 𝒞 ⟶ ℰ` and `G,I : 𝒟 ⟶ ℰ`,
```
F(X) ⟶ G(Y)
============
H(X) ⟶ I(Y)
```
would be a natural isomorphism of bifunctors `𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v`
given by `(X,Y) ↦ F(X) ⟶ G(Y)` and `(X, Y) ↦ H(X) ⟶ I(Y)`. -/

namespace CategoryTheory

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]

/-- Natural isomorphism of bifunctors from naturality in both arguments. -/
def NatIso.ofComponents₂ {F G : 𝒞 ⥤ 𝒟 ⥤ ℰ}
    (app : ∀ Γ X, (F.obj Γ).obj X ≅ (G.obj Γ).obj X)
    (naturality_left : ∀ {Γ Δ : 𝒞} (X : 𝒟) (σ : Γ ⟶ Δ),
      (F.map σ).app X ≫ (app Δ X).hom = (app Γ X).hom ≫ (G.map σ).app X := by aesop_cat)
    (naturality_right : ∀ {X Y : 𝒟} (Γ : 𝒞) (f : X ⟶ Y),
      (F.obj Γ).map f ≫ (app Γ Y).hom = (app Γ X).hom ≫ (G.obj Γ).map f := by aesop_cat) :
    F ≅ G :=
  NatIso.ofComponents
    (fun Γ => NatIso.ofComponents (app Γ) (fun f => by simpa using naturality_right Γ f))
    (fun σ => by ext X : 2; simpa using naturality_left X σ)

-- /-- The bifunctor `(Γ, X) ↦ (b : Γ.unop ⟶ B) × (P.obj (Over.mk b) ⟶ X)`. -/
-- @[simps!]
-- def Functor.Sigma_Over.{v} [Category.{v} 𝒟] {B : 𝒞} (P : Over B ⥤ 𝒟) : 𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v :=
--   curry.obj {
--     obj := fun (Γ, X) => (b : Γ.unop ⟶ B) × (P.obj (Over.mk b) ⟶ X)
--     map := fun (σ, f) ⟨b, e⟩ =>
--       ⟨σ.unop ≫ b,
--       P.map (Over.homMk (V := Over.mk b) σ.unop (by simp)) ≫ e ≫ f⟩
--     map_id := fun (Γ, X) => by
--       refine funext fun _ => ?_
--       apply Sigma_hom_ext
--       . simp [eqToHom_map]
--       . dsimp
--         intro h
--         rw [← Over.eqToHom_eq_homMk (eq := h)]
--         simp [eqToHom_map]
--     map_comp := fun {_} {_} {Y} (σ, f) (τ, g) => by
--       refine funext fun ⟨b, e⟩ => ?_
--       apply Sigma_hom_ext
--       . simp
--       . dsimp
--         intro h
--         rw [Over.homMk_comp (U := Over.mk ((τ.unop ≫ σ.unop) ≫ b)) (V := Over.mk (σ.unop ≫ b))
--           (f_comp := by simp) (g_comp := by simp)]
--         generalize_proofs -- I <3 generalize_proofs
--         generalize (τ.unop ≫ σ.unop) ≫ b = x at *
--         cases h
--         simp
--   }

/-- A functor into `𝒟` that depends on `F`. -/
-- TODO: does this correspond to a known construction?
structure DepFunctor (F : 𝒞 ⥤ Type*) (𝒟 : Type*) [Category 𝒟] where
  obj : ∀ ⦃Γ⦄, F.obj Γ → 𝒟
  map : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ), obj b ⟶ obj (F.map σ b)
  map_id : ∀ ⦃Γ⦄ (b : F.obj Γ), map (𝟙 Γ) b = eqToHom (F.map_id _ ▸ rfl)
  map_comp : ∀ ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) (b : F.obj Γ),
    map (σ ≫ τ) b = map σ b ≫ map τ (F.map σ b) ≫ eqToHom (F.map_comp .. ▸ rfl)

attribute [reassoc] DepFunctor.map_comp
attribute [simp] DepFunctor.map_id DepFunctor.map_comp DepFunctor.map_comp_assoc

@[simps]
def DepFunctor.isoLeft.{v} {F₁ F₂ : 𝒞 ⥤ Type v} {𝒟 : Type*} [Category 𝒟]
    (F : DepFunctor F₁ 𝒟) (i : F₂ ≅ F₁) : DepFunctor F₂ 𝒟 where
  obj Γ b := F.obj (i.hom.app Γ b)
  map Γ _ σ b := F.map σ (i.hom.app Γ b) ≫ eqToHom (FunctorToTypes.naturality F₂ F₁ i.hom .. ▸ rfl)
  map_id _ b := by simp
  map_comp _ _ _ σ τ b := by
    slice_rhs 2 3 => rw [← eqToHom_naturality _ (by simp [FunctorToTypes.naturality])]
    simp

structure DepNatTrans {F : 𝒞 ⥤ Type*} {𝒟 : Type*} [Category 𝒟] (G₁ G₂ : DepFunctor F 𝒟) where
  app : ∀ {Γ} (b : F.obj Γ), G₁.obj b ⟶ G₂.obj b
  naturality : ∀ {Γ Δ} (σ : Γ ⟶ Δ) (b : F.obj Γ),
    app b ≫ G₂.map σ b = G₁.map σ b ≫ app (F.map σ b)

attribute [reassoc] DepNatTrans.naturality

instance (F : 𝒞 ⥤ Type*) (𝒟 : Type*) [Category 𝒟] : Category (DepFunctor F 𝒟) where
  Hom := DepNatTrans
  id G := {
    app := fun _ => 𝟙 _
    naturality := by simp
  }
  comp η ν := {
    app := fun b => η.app b ≫ ν.app b
    naturality := by simp [η.naturality_assoc, ν.naturality]
  }
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

-- TODO: characterize isos in the above category as these things
structure DepNatIso (F : 𝒞 ⥤ Type*) {𝒟 : Type*} [Category 𝒟] (G₁ G₂ : DepFunctor F 𝒟) where
  i : ∀ {Γ} (b : F.obj Γ), G₁.obj b ≅ G₂.obj b
  i_naturality : ∀ {Γ Δ} (σ : Γ ⟶ Δ) (b : F.obj Γ),
    (i b).hom ≫ G₂.map σ b = G₁.map σ b ≫ (i (F.map σ b)).hom

/-- Dependent sum over a type-valued functor.
This serves to encapsulate dependent sums that vary naturally in their parameters. -/
@[simps!]
def Functor.Sigma.{v} (F : 𝒞 ⥤ Type v) (G : DepFunctor F (𝒟 ⥤ Type v)) : 𝒞 ⥤ 𝒟 ⥤ Type v :=
  curry.obj {
    obj := fun (Γ, X) => (b : F.obj Γ) × ((G.obj b).obj X)
    map := fun (σ, f) ⟨b, e⟩ =>
      ⟨F.map σ b, (G.map σ b).app _ ((G.obj b).map f e)⟩
    map_id := fun (Γ, X) => by
      dsimp
      refine funext fun ⟨b, e⟩ => ?_
      dsimp at *
      congr! 1 with h
      . simp
      . simp only [FunctorToTypes.map_id_apply, DepFunctor.map_id]
        generalize_proofs
        generalize (eq_lhs% h) = x at *
        cases h
        simp
    map_comp := fun {_} {_} {Y} (σ, f) (τ, g) => by
      refine funext fun ⟨b, e⟩ => ?_
      dsimp at *
      congr! 1 with h
      . simp
      . simp only [FunctorToTypes.map_comp_apply, DepFunctor.map_comp]
        generalize_proofs
        generalize (eq_lhs% h) = x at *
        cases h
        simp [FunctorToTypes.naturality]
  }

-- Not super important, we don't need to treat b as an over-category element ever.
-- @[simps!]
-- def Functor.Sigma_Over'.{v} [Category.{v} 𝒟] {B : 𝒞} (P : Over B ⥤ 𝒟) : 𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v :=
--   Functor.Sigma (yoneda.obj B) (fun b => coyoneda.obj $ Opposite.op $ P.obj $ Over.mk b)
--     (fun σ b => { app := fun _ e => P.map (Over.homMk (V := Over.mk b) σ.unop (by simp)) ≫ e })
--     (fun b => by
--       ext X b
--       simp only [eqToHom_app, coyoneda_obj_obj, yoneda_obj_map, unop_id] at b ⊢
--       generalize_proofs pf1 pf2
--       sorry
--       -- etc
--     )
--     (fun σ τ b => sorry)

def Functor.Sigma.isoCongrLeft.{v} (F₁ F₂ : 𝒞 ⥤ Type v) (G : DepFunctor F₁ (𝒟 ⥤ Type v))
    (i : F₂ ≅ F₁) : Functor.Sigma F₁ G ≅ Functor.Sigma F₂ (G.isoLeft i) :=
  NatIso.ofComponents₂
    (fun Γ X => Equiv.toIso {
      toFun := fun ⟨b, e⟩ => ⟨i.inv.app Γ b, cast (by simp) e⟩
      invFun := fun ⟨b, e⟩ => ⟨i.hom.app Γ b, e⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    })
    (fun X σ => by
      ext ⟨b, e⟩
      simp only [Sigma, DepFunctor.isoLeft_obj, prod_Hom, DepFunctor.isoLeft_map,
        FunctorToTypes.comp, curry_obj_obj_obj, curry_obj_map_app, FunctorToTypes.map_id_apply,
        Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp_apply, eqToHom_app, Sigma.mk.inj_iff,
        FunctorToTypes.naturality, true_and]
      generalize_proofs -- TODO: banish_casts tactic
      have : (i.hom.app _ (F₂.map σ (i.inv.app _ b))) = F₁.map σ b := by
        simp [FunctorToTypes.naturality]
      generalize (eq_lhs% this) = x at *; cases this
      have := FunctorToTypes.inv_hom_id_app_apply _ _ i _ (F₁.map σ b)
      generalize (eq_lhs% this) = x at *; cases this
      have := FunctorToTypes.inv_hom_id_app_apply _ _ i _ b
      generalize (eq_lhs% this) = x at *; cases this
      simp)
    (fun Γ f => by
      ext ⟨b,e⟩
      simp only [Sigma, DepFunctor.isoLeft_obj, prod_Hom, DepFunctor.isoLeft_map,
        FunctorToTypes.comp, curry_obj_obj_obj, curry_obj_obj_map, DepFunctor.map_id, eqToHom_app,
        Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp_apply, Sigma.mk.inj_iff,
        FunctorToTypes.map_id_apply, true_and]
      generalize_proofs
      have : F₁.map (𝟙 Γ) b = b := by simp
      generalize (eq_lhs% this) = x at *; cases this
      have : i.hom.app Γ (i.inv.app Γ b) = b := by simp
      generalize (eq_lhs% this) = x at *; cases this
      have : i.hom.app Γ (F₂.map (𝟙 Γ) (i.inv.app Γ b)) = b :=
        by simp [FunctorToTypes.naturality]
      generalize (eq_lhs% this) = x at *; cases this
      have : F₁.map (𝟙 Γ) b = b := by simp
      generalize (eq_lhs% this) = x at *; cases this
      simp)

def Functor.Sigma.isoCongrRight.{v} (F : 𝒞 ⥤ Type v) (G₁ G₂ : DepFunctor F (𝒟 ⥤ Type v))
    (i : ∀ {Γ} (b : F.obj Γ), G₁.obj b ≅ G₂.obj b)
    (i_naturality : ∀ {Γ Δ} (σ : Γ ⟶ Δ) (b : F.obj Γ),
      (i b).hom ≫ G₂.map σ b = G₁.map σ b ≫ (i (F.map σ b)).hom) :
    Functor.Sigma F G₁ ≅ Functor.Sigma F G₂ :=
  NatIso.ofComponents₂
    (fun Γ X => Equiv.toIso {
      toFun := fun ⟨b, e⟩ => ⟨b, (i b).hom.app X e⟩
      invFun := fun ⟨b, e⟩ => ⟨b, (i b).inv.app X e⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    })
    (fun X σ => by
      ext ⟨b, e⟩
      dsimp
      have := congrFun (congrFun (congrArg NatTrans.app (i_naturality σ b)) X) e
      simp at this
      simp [Sigma, this]
    )
    (fun Γ f => by
      ext ⟨b, e⟩
      simp only [Sigma, prod_Hom, curry_obj_obj_obj, curry_obj_obj_map, DepFunctor.map_id,
        eqToHom_app, Iso.app_hom, Iso.app_inv, Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp_apply,
        Sigma.mk.inj_iff, FunctorToTypes.map_id_apply, heq_eq_eq, true_and]
      generalize_proofs
      have := F.map_id Γ
      generalize (eq_lhs% this) = x at *
      cases this
      simp [FunctorToTypes.naturality])

@[simps]
def bifunctor_comp_snd {𝒟' : Type*} [Category 𝒟'] (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map σ := whiskerLeft F (P.map σ)

end CategoryTheory
