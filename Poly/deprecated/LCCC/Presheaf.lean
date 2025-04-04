import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
The category of presheaves on a (small) cat C is an LCCC:
(1) the category of presheaves on a (small) cat C is a CCC.
(2) the category of elements of a presheaf P is the comma category (yoneda, P)
(3) the slice of presheaves over P is presheaves on (yoneda, P).
(4) every slice is a CCC by (1).
(5) use the results in the file on LCCCs to infer that presheaves is LCC.
-/

namespace CategoryTheory

universe u v w

open Category Limits Functor Adjunction Over Opposite Equivalence Presheaf

/-!
# 1. Presheaves are a CCC
The category of presheaves on a small category is cartesian closed
-/

noncomputable section

@[simp]
abbrev Psh (C : Type u) [Category.{v} C] : Type (max u (v + 1)) := Cᵒᵖ ⥤ Type v

/-- `Psh C` is cartesian closed when `C` is small
(has hom-types and objects in the same universe). -/
def diagCCC {C : Type u} [Category.{u} C] : CartesianClosed (Psh C) :=
  inferInstance

def presheafCCC {C : Type u} [SmallCategory C] : CartesianClosed (Psh C) :=
  diagCCC

/-!
# 2. The category of elements
The category of elements of a *contravariant* functor P : Cᵒᵖ ⥤ Type is the opposite of the
category of elements of P regarded as a covariant functor P : Cᵒᵖ ⥤ Type.  Thus an object of
`(Elements P)ᵒᵖ` is a pair `(X : C, x : P.obj X)` and a morphism `(X, x) ⟶ (Y, y)` is a
morphism `f : X ⟶ Y` in `C` for which `P.map f` takes `y` back to `x`.
We have an equivalence (Elements P)ᵒᵖ ≌ (yoneda, P).
In MathLib the comma category is called the ``costructured arrow category''.
-/

namespace CategoryOfElements


def equivPsh {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D] (e : C ≌ D) : Psh C ≌ Psh D := by
  apply congrLeft e.op

variable {C : Type u} [Category.{v} C]

def presheafElementsOpIsPshCostructuredArrow (P : Psh C) : Psh (Elements P)ᵒᵖ ≌ Psh (CostructuredArrow yoneda P) :=
  equivPsh (costructuredArrowYonedaEquivalence P)

/-!
# 3. The slice category of presheaves
The slice category (Psh C)/P  is called the "over category" in MathLib and written "Over P".
-/

def overPshIsPshElementsOp {P : Psh C} : Over P ≌ Psh ((Elements P)ᵒᵖ) :=
  Equivalence.trans (overEquivPresheafCostructuredArrow P) (symm <| equivPsh (costructuredArrowYonedaEquivalence P))

/-!
# 4. The slice category Psh(C)/P is a CCC
We transfer the CCC structure across the equivalence (Psh C)/P ≃ Psh((Elements P)ᵒᵖ)
using the following:
def cartesianClosedOfEquiv (e : C ≌ D) [CartesianClosed C] : CartesianClosed D :=
  MonoidalClosed.ofEquiv (e.inverse.toMonoidalFunctorOfHasFiniteProducts) e.symm.toAdjunction
-/

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

def presheafOverCCC {C : Type u} [Category.{max u v} C] (P : Psh C) : CartesianClosed (Over P) :=
  cartesianClosedOfEquiv overPshIsPshElementsOp.symm

def allPresheafOverCCC {C : Type u} [Category.{max u v} C] : Π (P : Psh C), CartesianClosed (Over P) :=
  fun P => (presheafOverCCC P)

end CategoryOfElements

/-!
# 5. Presheaves is an LCCC
Use results in the file on locally cartesian closed categories.
-/

/-!
# Some references

1. Wellfounded trees and dependent polynomial functors.Gambino, Nicola; Hyland, Martin. Types for proofs and programs. International workshop, TYPES 2003, Torino, Italy, 2003. Revised selected papers.. Springer Berlin, 2004. p. 210-225.

2. Tamara Von Glehn. Polynomials and models of type theory. PhD thesis, University of Cambridge, 2015.

3. Joachim Kock. Data types with symmetries and polynomial functors over groupoids. Electronic Notes in Theoretical Computer Science, 286:351–365, 2012. Proceedings of the 28th Conference on the Mathematical Foundations of Programming Semantics (MFPS XXVIII).

4. Jean-Yves Girard. Normal functors, power series and λ-calculus. Ann. Pure Appl. Logic, 37(2):129–177, 1988. doi:10.1016/0168-0072(88)90025-5.

5. David Gepner, Rune Haugseng, and Joachim Kock. 8-Operads as analytic monads. Interna- tional Mathematics Research Notices, 2021.

6. Nicola Gambino and Joachim Kock. Polynomial functors and polynomial monads. Mathematical Proceedings of the Cambridge Philosophical Society, 154(1):153–192, 2013.

7. Marcelo Fiore, Nicola Gambino, Martin Hyland, and Glynn Winskel. The cartesian closed bicategory of generalised species of structures. J. Lond. Math. Soc. (2), 77(1):203–220, 2008.

8. M. Fiore, N. Gambino, M. Hyland, and G. Winskel. Relative pseudomonads, Kleisli bicategories, and substitution monoidal structures. Selecta Mathematica, 24(3):2791–2830, 2018.

9. Steve Awodey and Clive Newstead. Polynomial pseudomonads and dependent type theory, 2018.

10. Steve Awodey, Natural models of homotopy type theory, Mathematical Structures in Computer Science, 28 2 (2016) 241-286, arXiv:1406.3219.

-/
