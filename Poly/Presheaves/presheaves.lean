/-
Preamble copied and modified from LCCC.lean
-/

/-
Here's a plan for this file to show that the category of presheaves on a (small) cat C is LCC:
(1) define the category of presheaves on a (small) cat C and show it is a CCC,
(2) the slice category over any presheaf is presheaves on its category of elements,
(3) infer that every slice of presheaves is a CCC,
(4) use the results from the LCCC development to infer that presheaves is LCC.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Yoneda

-- All the imports below are transitively imported by the above import.
-- import Mathlib.CategoryTheory.Adjunction.Basic
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
-- import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
-- import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
-- import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
-- import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
-- import Mathlib.CategoryTheory.Adjunction.Limits
-- import Mathlib.CategoryTheory.Functor
-- import Mathlib.CategoryTheory.Products.Basic
-- import Mathlib.Data.ULift

/-!
# Presheaves
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

universe v u

variable {C : Type u} [Category.{v} C]
