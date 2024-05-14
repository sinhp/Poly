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
-/


universe u v v₁ v₂ v₃

/-- A polynomial functor `P` is given by a type family `B → Type u`.
Given a type

Given a polynomial `P` and a type `X` we define a new type `P X`, which is defined as the sigma type `Σ (b : P.B), (P.E b) → X` (mor informally `Σ (b : B), X ^ (E b)`).


An element of `P X` is a pair `⟨b, x⟩`, where `b` is a term of the base type `B` and `x : E b → X`. Think of `b` as the shape of the object and `x` as an index to the relevant elements of `X`.
-/
structure PolyFun where
  /-- The base type -/
  B : Type u
  /-- The dependent fibres -/
  E : B → Type u


namespace PolyFun

instance : Inhabited PolyFun :=
  ⟨⟨default, default⟩⟩

variable (P : PolyFun.{u}) {X : Type v₁} {Y : Type v₂} {Z : Type v₃}

-- section
-- variable (P : PolyFun.{u}) (B : Type u) (b : B)
-- scoped notation:50 E "[" b "]" => P.E b
-- end

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (X : Type v) :=
  Σ b : P.B, P.E b → X

instance : CoeFun PolyFun.{u} (fun _ => Type v → Type (max u v)) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
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
protected theorem map_map (f : X → Y) (g : Y → Z) :
    ∀ x : P X, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl


def polyFunctor : Type v ⥤ Type (max u v) where
  obj X := P X
  map {X Y} f := P.map f

def Total :=
  Σ b : P.B, P.E b

instance Total.inhabited [Inhabited P.B] [Inhabited (P.E default)] : Inhabited P.Total :=
  ⟨⟨default, default⟩⟩

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

end PolyFun

/-
Composition of polynomial functors.
-/
namespace PolyFun

/-- Functor composition for polynomial functors -/
def comp (Q P : PolyFun.{u}) : PolyFun.{u} :=
  ⟨Σ b₂ : Q.B, Q.E b₂ → P.B, fun z => Σ u : Q.2 z.1, P.2 (z.2 u)⟩

/-- Constructor for composition -/
def comp.mk (Q P : PolyFun.{u}) {X : Type} (x : Q (P X)) : comp Q P X :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun z => (x.2 z.1).2 z.2⟩



end PolyFun
