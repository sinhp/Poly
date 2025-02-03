/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Wojciech Nawrocki
-/

import Mathlib.CategoryTheory.Closed.Cartesian

import Poly.Basic

/-!
# Exponentiable morphisms in a category

We define *cartesian exponentiable* morphisms,
and prove that if a morphism `f : X ⟶ Y` is cartesian exponentiable
then `f` is exponentiable in the slice category `Over Y`.
In particular, for a morphism `g : I ⟶ Y`,
the exponential `f^* g` is the functor composition `(baseChange g) ⋙ (Over.map g)`.

## Notation

We provide the following notations:

* `Π_ f` is the functor `Over X ⥤ Over Y`.
As such, for an object `X : Over X`, we have `Π_ f X : Over Y`.
-/

noncomputable section

open CategoryTheory Limits Adjunction

variable {C : Type*} [Category C] [HasPullbacks C]

/-- A morphism `f : X ⟶ Y` in a category `C` is *cartesian exponentiable*
if there is a right adjoint to the base-change functor along `f`. -/
class CartesianExponentiable {X Y : C} (f : X ⟶ Y) where
  /-- A functor `C/X ⥤ C/Y` right adjoint to `f*`. -/
  functor : Over X ⥤ Over Y
  adj : Over.pullback f ⊣ functor := by infer_instance

@[inherit_doc]
prefix:90 "Π_ " => CartesianExponentiable.functor

namespace CartesianExponentiable

/-- The identity morphisms `𝟙` are cartesian exponentiable. -/
instance id {I : C} : CartesianExponentiable (𝟙 I) where
  functor := 𝟭 (Over I)
  adj := ofNatIsoLeft (F := 𝟭 _) Adjunction.id (baseChange.id I).symm

instance comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [fexp : CartesianExponentiable f] [gexp : CartesianExponentiable g] :
    CartesianExponentiable (f ≫ g) where
  functor := (Π_ f) ⋙ (Π_ g)
  adj := ofNatIsoLeft (gexp.adj.comp fexp.adj) (baseChange.comp f g).symm

/-- The conjugate isomorphism between pushforward functors. -/
def pushforwardCompIso [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [fexp : CartesianExponentiable f] [gexp : CartesianExponentiable g] :
    fexp.functor ⋙ gexp.functor ≅ (comp f g).functor :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) ((comp f g).adj) (baseChange.comp f g)

-- Noncomputably choose finite products from knowledge of their mere existence.
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

/-- An arrow with a pushforward is exponentiable in the slice category. -/
instance exponentiableOverMk [HasFiniteWidePullbacks C] {I : C} (f : X ⟶ I)
    [CartesianExponentiable f] : Exponentiable (Over.mk f) where
  rightAdj :=  (Δ_ f) ⋙ (Π_ f)
  adj := by
    apply ofNatIsoLeft _ _
    · exact ((Δ_ f) ⋙ (Σ_ f))
    · exact Adjunction.comp CartesianExponentiable.adj (Over.mapPullbackAdj _)
    · exact baseChange.natIsoTensorLeftOverMk f

end CartesianExponentiable
