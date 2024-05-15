/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/


import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types

open CategoryTheory Category Functor


/-!
# Polynomial functors

We define the notion of one-variable polynomial functors on the category of sets. The locally cartesian closed structure of sets is implicit in all the constructions.

In LCCCs, instead of workin with a type family we shall work with a bundle `p : E → B`.

The bundle corresponding to a `P : Poly` is the projection
`fst : Σ b : P.B, P.E b → P.B`.

-/


universe u v v₁ v₂ v₃

/-- A polynomial functor `P` is given by a type family `B → Type u`.
`Poly` is the type of polynomial functors is.

Given a polynomial `P` and a type `X` we define a new type `P X`, which is defined as the sigma type `Σ (b : P.B), (P.E b) → X` (mor informally `Σ (b : B), X ^ (E b)`).

An element of `P X` is a pair `⟨b, x⟩`, where `b` is a term of the base type `B` and `x : E b → X`.
-/
structure Poly where
  /-- The base type -/
  B : Type u
  /-- The dependent fibres -/
  E : B → Type u

namespace Poly

instance : Inhabited Poly :=
  ⟨⟨default, default⟩⟩

/-- A monomial functor is a polynomial functor with base type `Unit`. -/
def monomoial (α : Type*) : Poly := ⟨PUnit, fun _ => α⟩

variable (P : Poly.{u}) {X : Type v₁} {Y : Type v₂} {Z : Type v₃}

def Total :=
  Σ b : P.B, P.E b

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (X : Type v) :=
  Σ b : P.B, P.E b → X

instance Total.inhabited [Inhabited P.B] [Inhabited (P.E default)] : Inhabited P.Total :=
  ⟨⟨default, default⟩⟩

instance : CoeFun Poly.{u} (fun _ => Type v → Type (max u v)) where
  coe := Obj

/-- A monomial functor with exponent `α` evaluated at `X` is isomorphic to `α → X`. -/
def monomialEquiv (α : Type*) (X) : monomoial α X ≃ (α → X) where
  toFun := fun ⟨_, f⟩ => f
  invFun := fun f => ⟨PUnit.unit, f⟩
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- Polynomial `P` evaluated at the type `Unit` is isomorphic to the base type of `P`. -/
def baseEquiv : P Unit ≃ P.B where
  toFun := fun ⟨b, _⟩ => b
  invFun := fun b => ⟨b , fun _ => () ⟩
  left_inv := by aesop_cat
  right_inv := by aesop_cat


/-- Applying `P` to a morphism in `Type`. -/
def map (f : X → Y) : P X → P Y :=
  fun ⟨b, x⟩ => ⟨b, f ∘ x⟩

@[simp]
protected theorem map_eq (f : X → Y) (b : P.B) (x : P.E b → X) :
    P.map f ⟨b, x⟩ = ⟨b, f ∘ x⟩ :=
  rfl

@[simp]
theorem fst_map (x : P X) (f : X → Y) : (P.map f x).1 = x.1 := by cases x; rfl

instance Obj.inhabited [Inhabited P.B] [Inhabited X] : Inhabited (P X) :=
  ⟨⟨default, default⟩⟩

@[simp]
protected theorem id_map : ∀ x : P X, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
theorem map_map (f : X → Y) (g : Y → Z) :
    ∀ x : P X, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl



/-- The associated functor of `P : Poly`. -/
def functor : Type u ⥤ Type u where
  obj X := P X
  map {X Y} f := P.map f



variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def Obj.iget [DecidableEq P.B] {X} [Inhabited X] (x : P X) (i : P.Total) : X :=
  if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]
theorem iget_map [DecidableEq P.B] [Inhabited X] [Inhabited Y] (x : P X)
    (f : X → Y) (i : P.Total) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dif_pos, eq_self_iff_true]
  cases x
  rfl

end Poly

/-- Composition of polynomials. -/
def Poly.comp (Q P : Poly.{u}) : Poly.{u} :=
  ⟨Σ b : P.B, P.E b → Q.B, fun ⟨b, c⟩ ↦ Σ e : P.E b, Q.E (c e)⟩

/-
Note to self: The polynomial composition of bundles
`p : E → B`
`q : F → C`
is a bundle
`comp p q : D → A`
where
`A := Σ (b : B), E b → C`
and
`D := Σ (b : B), Σ (c : E b → C), Σ (e : E b), F (c e)`
-/

namespace PolyFunctor

open Poly

variable (P Q : Poly.{u})

/-- Constructor for composition -/
def comp.mk {X : Type} (x : P (Q X)) : Q.comp P X :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun z => (x.2 z.1).2 z.2⟩

/-- Functor composition for polynomial functors in the diagramatic order. -/
def comp.functor : Poly.functor (P.comp Q) ≅ Poly.functor Q ⋙ Poly.functor P where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

example : (Poly.functor Q ⋙ Poly.functor P).obj PUnit = P Q.B := by
  sorry



-- def comp.baseEquiv : (comp P Q) Unit ≃ P Q.B := by




end PolyFunctor
