/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
/-!
# Pentagon distributivity

Given morphims `u : M ⟶ B` and `f : B ⟶ A`, consider the following commutative diagram where
`v = Pi' f u` is the dependent product of `u` along `f`, `w` is the pullback of `v` along `f`,
and `e` is the component of the counit of the adjunction `pullback f ⊣ pushforward f` at `u`:
```
        P ---g--> D
    e / |         |
     M  | w       | v
    u \ |         |
        B ---f--> A
```

We construct a natural isomorphism
`Over.map u ⋙ pushforward f ≅ pullback e ⋙ pushforward g ⋙  Over.map v`
-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans Over ExponentiableMorphism Reindex
  LocallyCartesianClosed

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
  [LocallyCartesianClosed C]

variable {A B M : C} (f : B ⟶ A) (u : M ⟶ B)

abbrev v := Pi' f u

--abbrev P := Limits.pullback f (v f u)  -- not really needed

def g := pullback.fst (v f u) f -- (μ_ (Over.mk f) (Over.mk (v f u))).left  --pullback.fst (@v _ _ _ _ _ _ _ f u) f

/-- This should not be an instance because it's not usually how we want to construct exponentiable morphisms, we'll usually prove all morphims are exponential uniformly
from LocallyCartesianClosed structure.
The instance is inferred from the LocallyCartesianClosed structure, but
we should prove this more generally without assuming the LCCC structure. -/
def exponentiableMorphism : ExponentiableMorphism (g f u) := by infer_instance

namespace ExponentiableMorphism

/-- The pullback of exponentiable morphisms is exponentiable. -/
def pullback {I J K : C} (f : I ⟶ J) (g : K ⟶ J)
    [gexp : ExponentiableMorphism g] :
    ExponentiableMorphism (pullback.fst f g ) where
  functor := sorry
  adj := sorry

end ExponentiableMorphism



def w := pullback.snd (v f u) f

def e := ((ev f).app (Over.mk u)).left -- ev' (Over.mk f) (Over.mk u)

-- use `pushforwardBeckChevalleySquare` to construct this iso.
def pentagonIso : Over.map u ⋙ (pushforward f) ≅
  pullback (e f u) ⋙ (pushforward (g f u)) ⋙ Over.map (v f u)  :=
  sorry

end CategoryTheory
