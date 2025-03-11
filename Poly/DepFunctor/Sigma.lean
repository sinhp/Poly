/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import SEq.Tactic.DepRewrite

import Poly.DepFunctor.Basic
import Poly.ForMathlib.CategoryTheory.NatIso

namespace CategoryTheory

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]

/-! ## Dependent sum functor -/

namespace DepFunctor

/-- Given functors `F : 𝒞 ⥤ Type v` and `G : ∫F ⥤ 𝒟 ⥤ Type v`,
produce the functor `(X, Y) ↦ (b : F(X)) × G((X, b))(Y)`.

This is a dependent sum that varies naturally
in a parameter `X` of the first component,
and a parameter `Y` of the second component.

We use this to package and compose natural equivalences
where one (or both) sides is a dependent sum, e.g.
```
H(X) ⟶ I(Y)
=========================
(b : F(X)) × (G(X, b)(Y))
```
is a natural isomorphism of bifunctors `𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v`
given by `(X, Y) ↦ H(X) ⟶ I(Y)` and `G.Sigma`. -/
@[simps!]
def Sigma.{v} {F : 𝒞 ⥤ Type v} (G : DepFunctor F (𝒟 ⥤ Type v)) : 𝒞 ⥤ 𝒟 ⥤ Type v := by
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

def Sigma.isoCongrLeft.{v} (F₁ F₂ : 𝒞 ⥤ Type v) (G : DepFunctor F₁ (𝒟 ⥤ Type v))
    (i : F₂ ≅ F₁) : G.Sigma ≅ (G.isoLeft i).Sigma := by
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

def Sigma.isoCongrRight.{v} (F : 𝒞 ⥤ Type v) (G₁ G₂ : DepFunctor F (𝒟 ⥤ Type v))
    (i : G₁ ≅ G₂) :
    G₁.Sigma ≅ G₂.Sigma :=
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

end DepFunctor

open Limits in
/-- The functor `(b : Γ ⟶ B) ↦ Hom(dom(b*p), -)`. -/
noncomputable def pullbackDep.{v} {𝒞 : Type*} [Category.{v} 𝒞] [HasPullbacks 𝒞]
    {E B : 𝒞} (p : E ⟶ B) :
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

-- TODO: move elsewhere
@[simps]
def bifunctor_comp_snd {𝒟' : Type*} [Category 𝒟'] (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map σ := whiskerLeft F (P.map σ)

/-- The hom-functor `𝒞/Aᵒᵖ ⥤ 𝒞/A ⥤ Type` given by
`(X, g : X ⟶ A) (Y, f : Y ⟶ A) ↦ 𝒞/A(g, f)`
written as a dependent functor `∫y(A) ⥤ 𝒞/A ⥤ Type`.
This is to express the dependent sum `Σ(g : X ⟶ A), 𝒞/A(g, f)`. -/
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
    bifunctor_comp_snd (Over.forget A) (coyoneda (C := 𝒞)) ≅ (overDep A).Sigma := by
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
