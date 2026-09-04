/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Tactic.DepRewrite

import Poly.ForMathlib.CategoryTheory.Elements
import Poly.ForMathlib.CategoryTheory.Comma.Over.Basic
import Poly.Bifunctor.Basic

/-! ## Dependent sums of functors -/

-- Lean 4.34 tightened the transparency `simp`/`rw` use when matching, which stops them
-- reducing through `Functor.Elements` (a `def` over `Sigma`) and the `TypeCat.Hom` wrapper.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor

universe w v u t s r

variable {𝒞 : Type t} [Category.{u} 𝒞] {𝒟 : Type r} [Category.{s} 𝒟]

/-- Given functors `F : 𝒞 ⥤ Type v` and `G : ∫F ⥤ 𝒟 ⥤ Type v`,
produce the functor `(C, D) ↦ (a : F(C)) × G((C, a))(D)`.

This is a dependent sum that varies naturally
in a parameter `C` of the first component,
and a parameter `D` of the second component.

We use this to package and compose natural equivalences
where one side (or both) is a dependent sum, e.g.
```
H(C) ⟶ I(D)
=========================
(a : F(C)) × (G(C, a)(D))
```
is a natural isomorphism of bifunctors `𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v`
given by `(C, D) ↦ H(C) ⟶ I(D)` and `G.Sigma`. -/
@[simps!]
/- Q: Is it necessary to special-case bifunctors?
(1) General case `G : F.Elements ⥤ Type v` needs
a functor `F'` s.t. `F'.Elements ≅ F.Elements × 𝒟`; very awkward.
(2) General case `F : 𝒞 ⥤ 𝒟`, `G : ∫F ⥤ 𝒟`:
- what conditions are needed on `𝒟` for `∫F` to make sense?
- what about for `ΣF. G : 𝒞 ⥤ 𝒟` to make sense?
- known concrete instances are `𝒟 ∈ {Type, Cat, Grpd}` -/
def Sigma {F : 𝒞 ⥤ Type w} (G : F.Elements ⥤ 𝒟 ⥤ Type v) : 𝒞 ⥤ 𝒟 ⥤ Type (max w v) := by
  refine curry.obj {
    obj := fun (C, D) => (a : F.obj C) × (G.obj ⟨C, a⟩).obj D
    map := fun (f, g) => ↾(fun ⟨a, b⟩ =>
      ⟨F.map f a, (G.map ⟨f, rfl⟩).app _ ((G.obj ⟨_, a⟩).map g b)⟩)
    map_id := ?_
    map_comp := ?_
  }
  -- The objects must be destructured before the `match` on morphisms of `𝒞 × 𝒟` reduces.
  · rintro ⟨X₁, X₂⟩
    ext ⟨a, b⟩ : 3
    dsimp
    congr! 1 with h
    . simp
    . rw! [h]; simp [FunctorToTypes.naturality]
  · rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨Z₁, Z₂⟩ ⟨f₁, f₂⟩ ⟨g₁, g₂⟩
    ext ⟨a, b⟩ : 3
    dsimp
    congr! 1 with h
    . simp
    . rw! [h]; simp [FunctorToTypes.naturality]

def Sigma.isoCongrLeft {F₁ F₂ : 𝒞 ⥤ Type w}
    /- Q: What kind of map `F₂.Elements ⥤ F₁.Elements`
    could `NatTrans.mapElements i.hom` generalize to?
    We need to send `x ∈ F₂(C)` to something in `F₁(C)`;
    so maybe the map has to at least be over `𝒞`. -/
    (G : F₁.Elements ⥤ 𝒟 ⥤ Type v) (i : F₂ ≅ F₁) :
    Sigma (NatTrans.mapElements i.hom ⋙ G) ≅ Sigma G := by
  refine NatIso.ofComponents₂
    (fun C D => Equiv.toIso {
      toFun := fun ⟨a, b⟩ => ⟨i.hom.app C a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨i.inv.app C a, cast (by simp) b⟩
      left_inv := by rintro ⟨_, _⟩; refine Sigma.ext ?_ ?_ <;> simp
      right_inv := by rintro ⟨_, _⟩; refine Sigma.ext ?_ ?_ <;> simp
    }) ?_ ?_ <;> {
      intros
      ext ⟨a, b⟩ : 3
      dsimp [Sigma, Equiv.toIso, NatTrans.mapElements]
      congr! 1 with h
      . simp
      . rw! [← h]; simp
    }

def Sigma.isoCongrRight {F : 𝒞 ⥤ Type w} {G₁ G₂ : F.Elements ⥤ 𝒟 ⥤ Type v} (i : G₁ ≅ G₂) :
    Sigma G₁ ≅ Sigma G₂ := by
  refine NatIso.ofComponents₂
    (fun C D => Equiv.toIso {
      toFun := fun ⟨a, b⟩ => ⟨a, (i.hom.app ⟨C, a⟩).app D b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, (i.inv.app ⟨C, a⟩).app D b⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    }) ?_ ?_ <;> {
      intros
      ext ⟨a, b⟩ : 3
      dsimp [Sigma, Equiv.toIso]
      simp [FunctorToTypes.naturality₂_left, FunctorToTypes.naturality₂_right]
    }

theorem comp₂_Sigma {𝒟' : Type*} [Category 𝒟']
    {F : 𝒞 ⥤ Type w} (G : 𝒟' ⥤ 𝒟) (P : F.Elements ⥤ 𝒟 ⥤ Type v) :
    G ⋙₂ Sigma P = Sigma (G ⋙₂ P) := by
  apply Functor.hext
  . intro C
    apply Functor.hext
    . intro; simp
    . intros
      apply heq_of_eq
      ext ⟨a, b⟩ : 3 <;> dsimp [Sigma]
  . intro X Y f
    have h : (G ⋙₂ Sigma P).map f = (Sigma (G ⋙₂ P)).map f := by
      ext D ⟨a, b⟩ : 5 <;> simp [Sigma]
    exact heq_of_eq h
end CategoryTheory.Functor

/-! ## Over categories -/

namespace CategoryTheory.Over

universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞]

-- Q: is this in mathlib?
@[simps]
def equiv_Sigma {A : 𝒞} (X : 𝒞) (U : Over A) : (X ⟶ U.left) ≃ (b : X ⟶ A) × (Over.mk b ⟶ U) where
  toFun g := ⟨g ≫ U.hom, Over.homMk g rfl⟩
  invFun p := p.snd.left
  left_inv _ := by simp
  right_inv := fun _ => by
    dsimp; congr! 1 with h
    . simp
    . rw! [h]; simp

/-- Bridge between the `Equiv` and the `Type`-category morphism it induces, so that the
`@[simps]` lemmas for `equiv_Sigma` fire under `Equiv.toIso`. -/
@[simp]
lemma equiv_Sigma_toIso_hom_apply {A : 𝒞} (X : 𝒞) (U : Over A) (g : X ⟶ U.left) :
    (ConcreteCategory.hom (equiv_Sigma X U).toIso.hom) g = equiv_Sigma X U g := rfl

@[simps]
def equivalence_Elements (A : 𝒞) : (yoneda.obj A).Elements ≌ (Over A)ᵒᵖ where
  functor := {
    obj := fun x => .op <| Over.mk x.snd
    map := fun f => .op <| Over.homMk f.val.unop (by simpa using f.property)
  }
  inverse := {
    obj := fun U => ⟨.op U.unop.left, U.unop.hom⟩
    map := fun f => ⟨.op f.unop.left, by simp⟩
  }
  unitIso := NatIso.ofComponents Iso.refl (by simp)
  counitIso := NatIso.ofComponents Iso.refl
    -- TODO: `simp` fails to unify `id_comp`/`comp_id`
    (fun f => by simp [Category.comp_id f, Category.id_comp f])

/-- For `X ∈ 𝒞` and `f ∈ 𝒞/A`, `𝒞(X, Over.forget f) ≅ Σ(g: X ⟶ A), 𝒞/A(g, f)`. -/
def forget_iso_Sigma (A : 𝒞) :
    Over.forget A ⋙₂ coyoneda (C := 𝒞) ≅
    Functor.Sigma ((equivalence_Elements A).functor ⋙ coyoneda (C := Over A)) := by
  refine NatIso.ofComponents₂ (fun X U => Equiv.toIso <| equiv_Sigma X.unop U) ?_ ?_
  . intros X Y U f
    ext x : 3
    dsimp [Functor.Sigma, equivalence_Elements, coyoneda]
    congr! 1 with h
    . simp
    . rw! [← h]
      apply heq_of_eq
      ext : 1
      simp
  . intros X Y U f
    ext x : 3
    dsimp [Functor.Sigma, equivalence_Elements, coyoneda]
    congr! 1 with h
    . simp
    . rw! [← h]
      apply heq_of_eq
      ext : 1
      simp

end CategoryTheory.Over
