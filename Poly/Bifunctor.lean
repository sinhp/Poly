import Mathlib.CategoryTheory.Functor.Currying

import Poly.Util

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
  -- Forded to avoid `eqToHom` in the axioms.
  map : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ), c = F.map σ b → (obj b ⟶ obj c)
  map_id : ∀ ⦃Γ⦄ b h, map (𝟙 Γ) b b h = 𝟙 (obj b) := by aesop_cat
  /-- ### `simp`
  The two `map` equalities in the LHS imply the one in the RHS, but not vice-versa.
  This axiom is thus stated in a "packing" rather than an "unpacking" direction,
  so that `simp` can apply it automatically by matching `h₁` and `h₂`.
  However, we do not mark it `simp`;
  instead, a special case in the "unpacking" direction is `simp`. -/
  map_comp : ∀ ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) b c d h₁ h₂,
    map σ b c h₁ ≫ map τ c d h₂ = map (σ ≫ τ) b d (by simp [h₁, h₂]) := by aesop_cat

attribute [simp] DepFunctor.map_id

/-- Specialized variant of `map_comp` that `simp` can match against. -/
@[simp]
theorem DepFunctor.map_comp' {F : 𝒞 ⥤ Type*} {G : DepFunctor F 𝒟}
    ⦃Γ Δ Θ⦄ (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) b h :
    G.map (σ ≫ τ) b (F.map τ (F.map σ b)) h = G.map σ b (F.map σ b) rfl ≫ G.map τ _ _ rfl :=
  (G.map_comp σ τ ..).symm

@[simps]
def DepFunctor.isoLeft.{v} {F₁ F₂ : 𝒞 ⥤ Type v} {𝒟 : Type*} [Category 𝒟]
    (G : DepFunctor F₁ 𝒟) (i : F₂ ≅ F₁) : DepFunctor F₂ 𝒟 where
  obj Γ b := G.obj (i.hom.app Γ b)
  map Γ _ σ _ _ eq := G.map σ _ _ (by simp [eq, FunctorToTypes.naturality])
  map_id := by simp
  map_comp := by simp [G.map_comp]

@[ext]
structure DepNatTrans {F : 𝒞 ⥤ Type*} {𝒟 : Type*} [Category 𝒟] (G₁ G₂ : DepFunctor F 𝒟) where
  app : ∀ ⦃Γ⦄ (b : F.obj Γ), G₁.obj b ⟶ G₂.obj b
  naturality : ∀ ⦃Γ Δ⦄ (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ) h,
    app b ≫ G₂.map σ b c h = G₁.map σ b c h ≫ app c := by aesop_cat

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
    {Γ Δ : 𝒞} (σ : Γ ⟶ Δ) (b : F.obj Γ) (c : F.obj Δ) h (X : 𝒟) :
    (G₁.map σ b c h).app X ≫ (α.app c).app X = (α.app b).app X ≫ (G₂.map σ b c h).app X :=
  (congr_fun (congr_arg NatTrans.app (α.naturality σ b c h)) X).symm

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

/-! ## Dependent sum functors -/

/-- Given functors `F : 𝒞 ⥤ Type v` and `G : ∫F ⥤ 𝒟 ⥤ Type v`,
produce the functor `(X, Y) ↦ (b : F(X)) × G((X, b))(Y)`.
This is a dependent sum that varies naturally in its parameters `X, Y`. -/
@[simps!]
def Functor.Sigma.{v} {F : 𝒞 ⥤ Type v} (G : DepFunctor F (𝒟 ⥤ Type v)) : 𝒞 ⥤ 𝒟 ⥤ Type v := by
  refine curry.obj {
    obj := fun (Γ, X) => (b : F.obj Γ) × ((G.obj b).obj X)
    map := fun (σ, f) ⟨b, e⟩ =>
      ⟨F.map σ b, (G.map σ b _ rfl).app _ ((G.obj b).map f e)⟩
    map_id := ?_
    map_comp := ?_
  } <;> (
    intros
    ext ⟨b, e⟩ : 1
    dsimp
    congr! 1 with h
    . simp
    . rw! [h]; simp [FunctorToTypes.naturality]
  )

def Functor.Sigma.isoCongrLeft.{v} (F₁ F₂ : 𝒞 ⥤ Type v) (G : DepFunctor F₁ (𝒟 ⥤ Type v))
    (i : F₂ ≅ F₁) : Functor.Sigma G ≅ Functor.Sigma (G.isoLeft i) := by
  refine NatIso.ofComponents₂
    (fun Γ X => Equiv.toIso {
      toFun := fun ⟨b, e⟩ => ⟨i.inv.app Γ b, cast (by simp) e⟩
      invFun := fun ⟨b, e⟩ => ⟨i.hom.app Γ b, e⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    }) ?_ ?_ <;> (
      intros
      ext : 1
      dsimp
      apply let h := ?_; Sigma.ext h ?_
      . simp [FunctorToTypes.naturality]
      . dsimp [Sigma] at h ⊢
        rw! [
          ← h,
          FunctorToTypes.inv_hom_id_app_apply,
          FunctorToTypes.inv_hom_id_app_apply,
        ]
        simp
    )

def Functor.Sigma.isoCongrRight.{v} (F : 𝒞 ⥤ Type v) (G₁ G₂ : DepFunctor F (𝒟 ⥤ Type v))
    (i : G₁ ≅ G₂) :
    Functor.Sigma G₁ ≅ Functor.Sigma G₂ :=
  NatIso.ofComponents₂
    (fun Γ X => Equiv.toIso {
      toFun := fun ⟨b, e⟩ => ⟨b, (i.hom.app b).app X e⟩
      invFun := fun ⟨b, e⟩ => ⟨b, (i.inv.app b).app X e⟩
      left_inv := fun ⟨b, e⟩ => by simp
      right_inv := fun ⟨b, e⟩ => by simp
    })
    (fun X σ => by
      ext ⟨b, e⟩
      have := congr_fun (DepNatTrans.naturality_app i.hom σ b _ rfl X) e
      dsimp at this
      simp [Sigma, this])
    (fun Γ f => by
      ext ⟨b, e⟩
      dsimp
      simp only [Sigma, prod_Hom, curry_obj_obj_map, Sigma.mk.injEq, FunctorToTypes.map_id_apply,
        heq_eq_eq, true_and]
      rw! [F.map_id Γ]
      simp [FunctorToTypes.naturality])

open Limits in
/-- The functor `(b : Γ ⟶ B) ↦ Hom(dom(b*p), -)`. -/
noncomputable def pullbackDep.{v} {𝒞 : Type*} [Category.{v} 𝒞] [HasPullbacks 𝒞] {E B : 𝒞} (p : E ⟶ B) :
    DepFunctor (yoneda.obj B) (𝒞 ⥤ Type v) where
  obj _ b := coyoneda.obj <| Opposite.op <| pullback b p
  map _ _ σ _ _ eq :=
    coyoneda.map <| Quiver.Hom.op <|
      pullback.lift (pullback.fst .. ≫ σ.unop) (pullback.snd ..)
        (by rw [eq]; simp [pullback.condition])
  map_id := by simp
  map_comp := by
    intros
    ext : 3
    dsimp
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

@[simps]
def bifunctor_comp_snd {𝒟' : Type*} [Category 𝒟'] (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map σ := whiskerLeft F (P.map σ)

/-- The functor `(g : X ⟶ A) ↦ 𝒞/A(g, f)`. -/
@[simps]
def overDep (A : 𝒞) : DepFunctor (yoneda.obj A) (Over A ⥤ Type) where
  obj _ g := coyoneda.obj <| Opposite.op <| Over.mk g
  map _ _ σ f g eq := coyoneda.map <| Quiver.Hom.op <| Over.homMk σ.unop (by simp [eq])
  map_id := by simp
  map_comp := by
    intros
    ext : 3
    dsimp
    ext : 1
    simp

-- TODO: this in mathlib?
@[simps]
def Over_equiv {A : 𝒞} (X : 𝒞) (f : Over A) : (X ⟶ f.left) ≃ (b : X ⟶ A) × (Over.mk b ⟶ f) where
  toFun g := ⟨g ≫ f.hom, Over.homMk g rfl⟩
  invFun g := g.2.left
  left_inv _ := by simp
  right_inv := fun x => by
    dsimp; congr! 1 with h
    . simp
    . rw! [h]
      simp

/-- `𝒞(X, Over.forget f) ≅ Σ(g: X ⟶ A), 𝒞/A(g, f)` -/
def Over_iso (A : 𝒞) :
    bifunctor_comp_snd (Over.forget A) (coyoneda (C := 𝒞)) ≅ Functor.Sigma (overDep A) := by
  refine NatIso.ofComponents₂ (fun Γ U => Equiv.toIso <| Over_equiv Γ.unop U) ?_ ?_ <;> (
    intros
    dsimp
    ext : 1
    apply let h := ?_; Sigma.ext h ?_
    . simp
    . dsimp at h ⊢
      rw! [h]
      apply heq_of_eq
      ext
      simp
  )

end CategoryTheory
