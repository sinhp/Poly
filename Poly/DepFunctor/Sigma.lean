/-
Copyright (c) 2025 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import Lean.Elab.Tactic.DiscrTreeKey
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Category

import SEq.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.Elements
import Poly.ForMathlib.CategoryTheory.NatIso
import Poly.ForMathlib.CategoryTheory.Types

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

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

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
def Sigma.{v,u} {F : 𝒞 ⥤ Type v} (G : F.Elements ⥤ 𝒟 ⥤ Type u) : 𝒞 ⥤ 𝒟 ⥤ Type (max v u) := by
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

def Sigma.isoCongrLeft.{v,u} {F₁ F₂ : 𝒞 ⥤ Type v}
    /- Q: What kind of map `F₂.Elements ⥤ F₁.Elements`
    could `NatTrans.mapElements i.hom` generalize to?
    We need to send `x ∈ F₂(C)` to something in `F₁(C)`;
    so maybe the map has to at least be over `𝒞`. -/
    (G : F₁.Elements ⥤ 𝒟 ⥤ Type u) (i : F₂ ≅ F₁) :
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
      apply let h := ?_; Sigma.ext h ?_
      . simp [FunctorToTypes.naturality]
      . dsimp [Sigma] at h ⊢
        rw! [← h]
        simp [NatTrans.mapElements]
    }

def Sigma.isoCongrRight.{v,u} {F : 𝒞 ⥤ Type v} {G₁ G₂ : F.Elements ⥤ 𝒟 ⥤ Type u} (i : G₁ ≅ G₂) :
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
      apply let h := ?_; Sigma.ext h ?_
      . simp
      . dsimp [Sigma] at h ⊢
        simp [FunctorToTypes.binaturality_left, FunctorToTypes.binaturality_right]
    }
