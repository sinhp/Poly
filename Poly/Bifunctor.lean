import Mathlib.CategoryTheory.Functor.Currying

import Poly.Util
import Poly.Tactic.BanishCasts

import SEq.Tactic.DepRewrite

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
given by `(X, Y) ↦ F(X) ⟶ G(Y)` and `(X, Y) ↦ H(X) ⟶ I(Y)`. -/

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

/-! ## Dependent functors -/

/-- A functor into `𝒟` that depends on `F`,
in other words `∫F ⥤ 𝒟` where all the `F(Γ)` are discrete,
spelled out in elementary terms.

(In the general case, we would have
`map : ∀ ⦃Γ Δ⦄ ⦃b : F.obj Γ⦄ ⦃c : F.obj Δ⦄
  (σ : Γ ⟶ Δ) (f : F.map σ b ⟶ c), obj b ⟶ obj c`.)

Equivalently, it is a (lax or strict or something) transformation `F ⟶ const 𝒟`. -/
-- NOTE: A more mathlib-ready, general approach might use `∫F ⥤ 𝒟`,
-- and introduce a special-case constructor for discrete `F(Γ)`
-- with an argument for each field of this structure. -/
structure DepFunctor (F : 𝒞 ⥤ Type*) (𝒟 : Type*) [Category 𝒟] where
  obj : ∀ ⦃Γ⦄, F.obj Γ → 𝒟
  map : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ), obj b ⟶ obj (F.map σ b)
  map_id : ∀ ⦃Γ⦄ (b : F.obj Γ), map (𝟙 Γ) b = eqToHom (F.map_id _ ▸ rfl) := by aesop_cat
  map_comp : ∀ ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) (b : F.obj Γ),
    map (σ ≫ τ) b = map σ b ≫ map τ (F.map σ b) ≫ eqToHom (F.map_comp .. ▸ rfl) := by aesop_cat

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

@[ext]
structure DepNatTrans {F : 𝒞 ⥤ Type*} {𝒟 : Type*} [Category 𝒟] (G₁ G₂ : DepFunctor F 𝒟) where
  app : ∀ ⦃Γ⦄ (b : F.obj Γ), G₁.obj b ⟶ G₂.obj b
  naturality : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ),
    app b ≫ G₂.map σ b = G₁.map σ b ≫ app (F.map σ b) := by aesop_cat

attribute [reassoc] DepNatTrans.naturality

@[simps]
instance (F : 𝒞 ⥤ Type*) (𝒟 : Type*) [Category 𝒟] : Category (DepFunctor F 𝒟) where
  Hom := DepNatTrans
  id G := { app := fun _ _ => 𝟙 _ }
  comp η ν := {
    app := fun _ b => η.app b ≫ ν.app b
    naturality := by simp [η.naturality_assoc, ν.naturality]
  }

namespace DepNatTrans

variable {F : 𝒞 ⥤ Type*} {𝒟 : Type*} [Category 𝒟] {Γ : 𝒞} (b : F.obj Γ)

@[ext]
theorem ext' {G₁ G₂ : DepFunctor F 𝒟} {α β : G₁ ⟶ G₂} (w : α.app = β.app) : α = β :=
  DepNatTrans.ext w

@[simp]
theorem id_app (G₁ : DepFunctor F 𝒟) : (𝟙 G₁ : G₁ ⟶ G₁).app b = 𝟙 (G₁.obj b) := rfl

@[reassoc (attr := simp)]
theorem comp_app {G₁ G₂ G₃ : DepFunctor F 𝒟} (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃) :
    (α ≫ β).app b = α.app b ≫ β.app b := rfl

@[reassoc]
theorem naturality_app {ℰ : Type*} [Category ℰ] {G₁ G₂ : DepFunctor F (𝒟 ⥤ ℰ)} (α : G₁ ⟶ G₂)
    {Γ Δ : 𝒞} (σ : Γ ⟶ Δ) (b : F.obj Γ) (X : 𝒟) :
    (G₁.map σ b).app X ≫ (α.app (F.map σ b)).app X = (α.app b).app X ≫ (G₂.map σ b).app X :=
  (congr_fun (congr_arg NatTrans.app (α.naturality σ b)) X).symm

end DepNatTrans

namespace DepNatIso

variable {F : 𝒞 ⥤ Type*} {𝒟 : Type*} [Category 𝒟] {G₁ G₂ : DepFunctor F 𝒟}

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
    (naturality : ∀ {Γ Δ} (σ : Γ ⟶ Δ) (b : F.obj Γ),
      (app b).hom ≫ G₂.map σ b = G₁.map σ b ≫ (app (F.map σ b)).hom) :
    G₁ ≅ G₂ where
  hom := { app := fun _ b => (app b).hom }
  inv := {
    app := fun _ b => (app b).inv
    naturality := fun _ _ σ b => by
      have : (app b).inv ≫ (app b).hom ≫ G₂.map σ b ≫ (app (F.map σ b)).inv =
             (app b).inv ≫ G₁.map σ b ≫ (app (F.map σ b)).hom ≫ (app (F.map σ b)).inv := by
        simp [reassoc_of% naturality]
      simpa using this.symm
  }

end DepNatIso

/-! ## Dependent sum functors -/


/-- Given functors `F : 𝒞 ⥤ Type v` and `G : ∫F ⥤ 𝒟 ⥤ Type v`,
produce the functor `(X, Y) ↦ (b : F(X)) × G((X, b))(Y)`.
This is a dependent sum that varies naturally in its parameters `X, Y`. -/
@[simps!]
def Functor.Sigma.{v} {F : 𝒞 ⥤ Type v} (G : DepFunctor F (𝒟 ⥤ Type v)) : 𝒞 ⥤ 𝒟 ⥤ Type v :=
  curry.obj {
    obj := fun (Γ, X) => (b : F.obj Γ) × ((G.obj b).obj X)
    map := fun (σ, f) ⟨b, e⟩ =>
      ⟨F.map σ b, (G.map σ b).app _ ((G.obj b).map f e)⟩
    map_id := fun (Γ, X) => by
      refine funext fun ⟨b, e⟩ => ?_
      dsimp
      congr! 1 with h
      . simp
      . simp only [FunctorToTypes.map_id_apply, DepFunctor.map_id]
        rw! [h]
        simp
    map_comp := fun {_} {_} {Y} (σ, f) (τ, g) => by
      refine funext fun ⟨b, e⟩ => ?_
      dsimp
      congr! 1 with h
      . simp
      . simp only [FunctorToTypes.map_comp_apply, DepFunctor.map_comp]
        rw! [h]
        simp [FunctorToTypes.naturality]
  }

def Functor.Sigma.isoCongrLeft.{v} (F₁ F₂ : 𝒞 ⥤ Type v) (G : DepFunctor F₁ (𝒟 ⥤ Type v))
    (i : F₂ ≅ F₁) : Functor.Sigma G ≅ Functor.Sigma (G.isoLeft i) :=
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
      have : (i.hom.app _ (F₂.map σ (i.inv.app _ b))) = F₁.map σ b := by
        simp [FunctorToTypes.naturality]
      rw! (castMode := .all) [this, FunctorToTypes.inv_hom_id_app_apply _ _ i _ (F₁.map σ b),
        FunctorToTypes.inv_hom_id_app_apply _ _ i _ b]
      simp)
    (fun Γ f => by
      ext ⟨b,e⟩
      simp only [Sigma, DepFunctor.isoLeft_obj, prod_Hom, DepFunctor.isoLeft_map,
        FunctorToTypes.comp, curry_obj_obj_obj, curry_obj_obj_map, DepFunctor.map_id, eqToHom_app,
        Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp_apply, Sigma.mk.inj_iff,
        FunctorToTypes.map_id_apply, true_and]
      rw! (castMode := .all) [show F₁.map (𝟙 Γ) b = b by simp,
        show i.hom.app Γ (i.inv.app Γ b) = b by simp,
        show i.hom.app Γ (F₂.map (𝟙 Γ) (i.inv.app Γ b)) = b by simp [FunctorToTypes.naturality],
        show F₁.map (𝟙 Γ) b = b by simp]
      simp)

def Functor.Sigma.isoCongrRight.{v} (F : 𝒞 ⥤ Type v) (G₁ G₂ : DepFunctor F (𝒟 ⥤ Type v))
    (i : G₁ ≅ G₂) :
    Functor.Sigma G₁ ≅ Functor.Sigma G₂ :=
  NatIso.ofComponents₂
    (fun Γ X => Equiv.toIso {
      toFun := fun ⟨b, e⟩ => ⟨b, (i.hom.app b).app X e⟩
      invFun := fun ⟨b, e⟩ => ⟨b, (i.inv.app b).app X e⟩
      left_inv := fun ⟨b, e⟩ => by
        -- simp doesn't finish this. missing simp lemma?
        have := congr_fun (congr_fun (congr_arg NatTrans.app (DepNatIso.hom_inv_id_app i b)) X) e
        simp only [NatTrans.comp_app] at this
        simpa using this
      right_inv := fun ⟨b, e⟩ => by
        have := congr_fun (congr_fun (congr_arg NatTrans.app (DepNatIso.inv_hom_id_app i b)) X) e
        simp only [NatTrans.comp_app] at this
        simpa using this
    })
    (fun X σ => by
      ext ⟨b, e⟩
      have := congr_fun (DepNatTrans.naturality_app i.hom σ b X) e
      dsimp at this
      simp [Sigma, this])
    (fun Γ f => by
      ext ⟨b, e⟩
      simp only [Sigma, prod_Hom, curry_obj_obj_obj, curry_obj_obj_map, DepFunctor.map_id,
        eqToHom_app, Iso.app_hom, Iso.app_inv, Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp_apply,
        Sigma.mk.inj_iff, FunctorToTypes.map_id_apply, heq_eq_eq, true_and]
      rw! [F.map_id Γ]
      simp [FunctorToTypes.naturality])

open Limits in
/-- The functor `(b : Γ ⟶ B) ↦ Hom(dom(b*p), -)`. -/
noncomputable def pullbackDep.{v} {𝒞 : Type*} [Category.{v} 𝒞] [HasPullbacks 𝒞] {E B : 𝒞} (p : E ⟶ B) :
    DepFunctor (yoneda.obj B) (𝒞 ⥤ Type v) where
  obj _ b := coyoneda.obj <| Opposite.op <| pullback b p
  map _ _ σ _ :=
    coyoneda.map <| Quiver.Hom.op <|
      pullback.lift (pullback.fst .. ≫ σ.unop) (pullback.snd ..) (by simp [pullback.condition])
  map_id _ b := by
    dsimp
    rw! [show 𝟙 _ ≫ b = b by simp]
    simp
  map_comp _ _ _ σ τ b := by
    ext
    dsimp
    rw! [show τ.unop ≫ σ.unop ≫ b = (τ.unop ≫ σ.unop) ≫ b by simp]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

@[simps]
def bifunctor_comp_snd {𝒟' : Type*} [Category 𝒟'] (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map σ := whiskerLeft F (P.map σ)

end CategoryTheory
