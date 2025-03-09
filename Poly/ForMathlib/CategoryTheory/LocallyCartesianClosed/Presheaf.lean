/-
Copyv (c) 2025 Sina Hazratpour. All vs reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Awodey, Sina Hazratpour
-/

import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Basic
import Mathlib.CategoryTheory.Closed.FunctorCategory.Basic


noncomputable section

namespace CategoryTheory

open CategoryTheory Limits

universe u v w

abbrev Psh (C : Type u) [Category.{v} C] : Type (max u (v + 1)) := Cᵒᵖ ⥤ Type v

variable {C : Type*} [SmallCategory C] [HasTerminal C]

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

instance cartesianClosedOver {C : Type u} [Category.{max u v} C] (P : Psh C) :
    CartesianClosed (Over P) :=
  cartesianClosedOfEquiv (overEquivPresheafCostructuredArrow P).symm

instance locallyCartesianClosed : LocallyCartesianClosed (Psh C) := by
  infer_instance

instance {X Y : Psh C} (f : X ⟶ Y) : ExponentiableMorphism f := by infer_instance

end CategoryTheory

end
