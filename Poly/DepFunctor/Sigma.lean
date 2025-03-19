/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Tactic.DiscrTreeKey

import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import SEq.Tactic.DepRewrite

import Poly.ForMathlib.CategoryTheory.Elements
import Poly.ForMathlib.CategoryTheory.NatIso
import Poly.ForMathlib.CategoryTheory.Types
import Poly.Util

open private mkKey from Lean.Elab.Tactic.DiscrTreeKey in
open Lean Meta Elab Tactic in
/-- Print the `DiscrTree` key of the current `conv` mode target. -/
macro "discr_tree_key" : conv =>
  `(conv| tactic => run_tac do
    let g ← Conv.getLhs
    logInfo <| ← DiscrTree.keysAsPattern <| ← mkKey g false)

open private mkKey from Lean.Elab.Tactic.DiscrTreeKey in
open Lean Meta Elab Tactic Conv in
/-- Attempt to match the current `conv` mode target
against the LHS of the specified theorem. -/
elab "discr_tree_match" n:ident : conv => do
  let c ← realizeGlobalConstNoOverloadWithInfo n
  let ci ← getConstInfo c
  let e ← Conv.getLhs
  let ciKey ← mkKey ci.type true
  let gKey ← mkKey e false
  logInfo m!"{ciKey.zip gKey |>.map fun (a, b) => m!"{a} := {b}"}"
  logInfo m!"{← DiscrTree.keysAsPattern ciKey} := {← DiscrTree.keysAsPattern gKey}"

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
    map := fun (f, g) ⟨a, b⟩ =>
      ⟨F.map f a, (G.map ⟨f, rfl⟩).app _ ((G.obj ⟨_, a⟩).map g b)⟩
    map_id := ?_
    map_comp := ?_
  } <;> {
    intros
    ext ⟨a, b⟩ : 1
    dsimp
    congr! 1 with h
    . simp
    . rw! [h]; simp [FunctorToTypes.naturality]
  }

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
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun ⟨_, _⟩ => by simp
    }) ?_ ?_ <;> {
      intros
      ext : 1
      dsimp
      apply have h := ?_; Sigma.ext h ?_
      . simp [FunctorToTypes.naturality]
      . dsimp [Sigma] at h ⊢
        rw! [← h]
        simp [NatTrans.mapElements]
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
      ext : 1
      dsimp
      apply have h := ?_; Sigma.ext h ?_
      . simp
      . dsimp [Sigma] at h ⊢
        simp [FunctorToTypes.binaturality_left, FunctorToTypes.binaturality_right]
    }

end CategoryTheory.Functor

/-! ### Profunctor operations -/

namespace CategoryTheory.Functor

variable {𝒞 𝒟' 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟'] [Category 𝒟] [Category ℰ]

/-- Precompose a profunctor in the second argument.
Note that `G ⋙₂ F ⋙ P = F ⋙ G ⋙₂ P` definitionally. -/
@[simps]
def comp₂ (F : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : 𝒞 ⥤ 𝒟' ⥤ ℰ where
  obj Γ := F ⋙ P.obj Γ
  map f := whiskerLeft F (P.map f)

@[inherit_doc]
scoped [CategoryTheory] infixr:80 " ⋙₂ " => Functor.comp₂

@[simp]
theorem comp_comp₂ {𝒟'' : Type*} [Category 𝒟'']
    (F : 𝒟'' ⥤ 𝒟') (G : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) :
    (F ⋙ G) ⋙₂ P = F ⋙₂ (G ⋙₂ P) := by
  rfl

@[simp]
-- Composition with `F,G` ordered like the arguments of `P` is considered 'simplified'.
theorem comp₂_comp {𝒞' : Type*} [Category 𝒞']
    (F : 𝒞' ⥤ 𝒞) (G : 𝒟' ⥤ 𝒟) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) :
    G ⋙₂ (F ⋙ P) = F ⋙ (G ⋙₂ P) := by
  rfl

theorem comp₂_Sigma {F : 𝒞 ⥤ Type w} (G : 𝒟' ⥤ 𝒟) (P : F.Elements ⥤ 𝒟 ⥤ Type v) :
    G ⋙₂ Sigma P = Sigma (G ⋙₂ P) := by
  apply Functor.hext
  . intro C
    apply Functor.hext
    . intro; simp
    . intros
      apply heq_of_eq
      ext : 1
      apply Sigma.ext <;> simp
  . intros
    apply heq_of_eq
    ext : 3
    apply Sigma.ext <;> simp

@[simps!]
def iso₂ {F₁ F₂ : 𝒟' ⥤ 𝒟} {P₁ P₂ : 𝒞 ⥤ 𝒟 ⥤ ℰ}
    (i : F₁ ≅ F₂) (j : P₁ ≅ P₂) : F₁ ⋙₂ P₁ ≅ F₂ ⋙₂ P₂ :=
  NatIso.ofComponents₂ (fun C D => (j.app C).app (F₁.obj D) ≪≫ (P₂.obj C).mapIso (i.app D))
    (fun _ _ => by simp [NatTrans.naturality_app_assoc])
    (fun C f => by
      have := congr_arg (P₂.obj C).map (i.hom.naturality f)
      simp only [map_comp] at this
      simp [this])

@[simps!]
def iso₂WhiskerLeft {P₁ P₂ : 𝒞 ⥤ 𝒟 ⥤ ℰ} (F : 𝒟' ⥤ 𝒟) (i : P₁ ≅ P₂) : F ⋙₂ P₁ ≅ F ⋙₂ P₂ :=
  iso₂ (Iso.refl F) i

@[simps!]
def iso₂WhiskerRight {F₁ F₂ : 𝒟' ⥤ 𝒟} (i : F₁ ≅ F₂) (P : 𝒞 ⥤ 𝒟 ⥤ ℰ) : F₁ ⋙₂ P ≅ F₂ ⋙₂ P :=
  iso₂ i (Iso.refl P)

end CategoryTheory.Functor

/-! ### Natural isomorphisms-/

/-! #### Hom-types -/

namespace CategoryTheory.Functor

universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞]

theorem comp₂_coyoneda_naturality_left {𝒞' : Type*} [Category 𝒞']
    (F : 𝒞' ⥤ 𝒞) (P : 𝒞ᵒᵖ ⥤ 𝒞' ⥤ Type v) (i : F ⋙₂ coyoneda (C := 𝒞) ⟶ P) (X Y : 𝒞) (Z : 𝒞')
    (f : X ⟶ Y) (g : Y ⟶ F.obj Z) :
    -- TODO: the `op`s really are a pain. Why can't they be definitional like in Lean 3 :(
    (i.app <| .op X).app Z (f ≫ g) = (P.map f.op).app Z ((i.app <| .op Y).app Z g) := by
  simp [← FunctorToTypes.binaturality_left]

theorem comp₂_coyoneda_naturality_right {𝒞' : Type*} [Category 𝒞']
    (F : 𝒞' ⥤ 𝒞) (P : 𝒞ᵒᵖ ⥤ 𝒞' ⥤ Type v) (i : F ⋙₂ coyoneda (C := 𝒞) ⟶ P) (X : 𝒞) (Y Z : 𝒞')
    (f : X ⟶ F.obj Y) (g : Y ⟶ Z) :
    (i.app <| .op X).app Z (f ≫ F.map g) = (P.obj <| .op X).map g ((i.app <| .op X).app Y f) := by
  simp [← FunctorToTypes.binaturality_right]

end CategoryTheory.Functor

/-! #### Over -/

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
    ext : 1
    dsimp
    apply have h := ?_; Sigma.ext h ?_
    . simp
    . dsimp at h ⊢
      rw! [h]
      simp
  . intros X Y U f
    ext : 1
    dsimp
    apply have h := ?_; Sigma.ext h ?_
    . simp
    . dsimp at h ⊢
      rw! [h]
      -- simp -- TODO: `homMk f.left ⋯` and `homMk (𝟙 _) ⋯` don't get simplified here
      apply heq_of_eq
      ext : 1
      simp

end CategoryTheory.Over

/-! #### Adjunction -/

namespace CategoryTheory.Adjunction

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

/-- For `F ⊣ G`, `𝒟(FX, Y) ≅ 𝒞(X, GY)`. -/
def homIso {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (A : F ⊣ G) :
    F.op ⋙ coyoneda (C := 𝒟) ≅ G ⋙₂ coyoneda (C := 𝒞) :=
  NatIso.ofComponents₂ (fun C D => Equiv.toIso <| A.homEquiv C.unop D)
    (fun _ _ => by ext : 1; simp [A.homEquiv_naturality_left])
    (fun _ _ => by ext : 1; simp [A.homEquiv_naturality_right])

end CategoryTheory.Adjunction
