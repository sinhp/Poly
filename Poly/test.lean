import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian

namespace CategoryTheory

open CategoryTheory Category Limits

#check Closed


-- internal hom `A ⟶[C] -`.
#check ihom


variable {C : Type*} [Category C] [HasFiniteProducts C]


/- LCCC -/

#check Comma

#check Over

#check MonoidalCategory

#check CartesianClosed



class LCCC where
  slice : ∀ I : C, CartesianClosed (Over I)





structure PolyFun where
  E  : C
  B : C
  p : E ⟶ B


-- `Σ b : B, [ E(b) , X ]` needs pushforward along `p` summing along `! : B ⟶ 1`.



-- pushforwad along p


end CategoryTheory
