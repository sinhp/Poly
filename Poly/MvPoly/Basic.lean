/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

-- import Poly.LCCC.BeckChevalley
-- import Poly.LCCC.Basic
-- import Poly.ForMathlib.CategoryTheory.Comma.Over.Basic
-- import Poly.ForMathlib.CategoryTheory.Comma.Over.Pullback
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Basic
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.BeckChevalley
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Distributivity
import Mathlib.CategoryTheory.Extensive
--import Poly.UvPoly

/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`ExponentiableMorphism` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor Adjunction ExponentiableMorphism

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I`,
output variables in `O`, and with arities `E` dependent on `I`. -/
structure MvPoly (I O : C) where
  (E B : C)
  (i : E ⟶ I)
  (p : E ⟶ B)
  (exp : ExponentiableMorphism p := by infer_instance)
  (o : B ⟶ O)

namespace MvPoly

open ExponentiableMorphism

attribute [instance] MvPoly.exp

/-- The identity polynomial in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, ExponentiableMorphism.id, 𝟙 I⟩

instance (I : C) : ExponentiableMorphism ((id I).p) := ExponentiableMorphism.id

-- let's prove that the pullback along `initial.to` is isomorphic to the initial object
example [HasInitial C] {X Y : C} (f : Y ⟶ X) :
    IsPullback (initial.to Y) (𝟙 _) f (initial.to X) where
      w := by aesop
      isLimit' := by
        refine ⟨?_⟩
        sorry

/-- Given an object `X`, The unique map `initial.to X : ⊥_ C ⟶ X ` is exponentiable. -/
instance [HasInitial C] (X : C) : ExponentiableMorphism (initial.to X) := sorry

/-- The constant polynomial in many variables: for this we need the initial object. -/
def const {I O : C} [HasInitial C] (A : C) [HasBinaryProduct O A] : MvPoly I O :=
  ⟨⊥_ C, Limits.prod O A, initial.to I , initial.to _, inferInstance, prod.fst⟩

/-- The monomial polynomial in many variables. -/
def monomial {I O E : C} (i : E ⟶ I) (p : E ⟶ O) [ExponentiableMorphism p]: MvPoly I O :=
  ⟨E, O, i, p, inferInstance, 𝟙 O⟩

/-- The sum of two polynomials in many variables. -/
def sum {I O : C} [HasBinaryCoproducts C] (P Q : MvPoly I O) : MvPoly I O where
  E := P.E ⨿ Q.E
  B := P.B ⨿ Q.B
  i := coprod.desc P.i Q.i
  p := coprod.map P.p Q.p
  exp := by {
    refine { exists_rightAdjoint := by {
      have F : Over (P.E ⨿ Q.E) ⥤ Over (P.B ⨿ Q.B) := sorry
      use F
      haveI : HasBinaryCoproducts (Over (P.E ⨿ Q.E)) := by {
        sorry
      }
      have hf : PreservesPullbacksOfInclusions F := by {
        sorry
      }
      sorry






    }
    }}
  o := coprod.desc P.o Q.o
--#check PreservesPullbacksOfInclusions

--#check PreservesPullbacksOfInclusions.preservesPullbackInl


/-For sums: assuming extensiveness, you can express the slice over
the sum as the product of slices. Then you can calculate pullback
 as the product of two functors, amd then you take the products of their adjoints-/

/-- The product of two polynomials in many variables. -/
def prod {I O : C} [HasBinaryProducts C] [FinitaryExtensive C] (P Q : MvPoly I O) :
    MvPoly I O where
  E := (pullback (P.p ≫ P.o) Q.o) ⨿ (pullback P.o (Q.p ≫ Q.o))
  B := pullback P.o Q.o
  i := coprod.desc (pullback.fst _ _ ≫ P.i) (pullback.snd _ _ ≫ Q.i)
  p := coprod.desc (pullback.map _ _ _ _ P.p (𝟙 _) (𝟙 _)
    (comp_id _) (by rw [comp_id, id_comp]))
    (pullback.map _ _ _ _ (𝟙 _) Q.p (𝟙 _)
    (by rw [comp_id, id_comp]) (comp_id _))
  exp := by {
    refine { exists_rightAdjoint := by {sorry

    }


    }
  } -- by extensivity -- PreservesPullbacksOfInclusions
  o := pullback.fst (P.o) Q.o ≫ P.o

protected def functor {I O : C} (P : MvPoly I O) :
    Over I ⥤ Over O :=
  (Over.pullback P.i) ⋙ (pushforward P.p) ⋙ (Over.map P.o)

variable (I O : C) (P : MvPoly I O)

def apply {I O : C} (P : MvPoly I O) [ExponentiableMorphism P.p] :
  Over I → Over O := (P.functor).obj

/-TODO: write a coercion from `MvPoly` to a functor for evaluation of polynomials at a given
object.-/

def idApplyIso (q : X ⟶ I) : (id I).apply (Over.mk q) ≅ Over.mk q where
  hom := by
    simp [apply]
    exact {
      left := by
        dsimp
        sorry
      right := sorry
      w := sorry
    }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

section Composition

variable {I J K : C} (P : MvPoly I J) (Q : MvPoly J K) [LocallyCartesianClosed C]

open Over

abbrev h : (Limits.pullback P.o Q.i) ⟶ P.B := pullback.fst P.o Q.i

abbrev k := pullback.snd P.o Q.i

abbrev m := pullback.fst P.p (h P Q)

/-- `w` is obtained by applying `pushforward g` to `k`. -/
abbrev w := v Q.p (k P Q)  --(functor Q.p).obj (Over.mk <| k P Q)

abbrev r := pullback.snd P.p (h P Q)

abbrev ε :=  e (Q.p) (k P Q)  -- (ε' P Q).left

def q  :=  g Q.p (k P Q)  --pullback.fst (P.w Q).hom Q.p

/-- This is `p` in the diagram. -/
abbrev p' := pullback.snd (r P Q) (ε P Q)

-- N P Q  ⟶ B' P Q
abbrev n := pullback.fst (r P Q) (ε P Q)

open LocallyCartesianClosed

/-- Functor composition for polynomial functors in the diagrammatic order. -/
def comp (P : MvPoly I J) (Q : MvPoly J K) : MvPoly I K where
  E := pullback (r P Q) (e Q.p (k P Q))
  B := (Pi (Over.mk Q.p) (Over.mk (k P Q))).left
  i := n P Q ≫ m P Q ≫ P.i
  p := p' P Q ≫ q P Q
  exp := ExponentiableMorphism.comp (P.p' Q) (P.q Q)
  o := (w P Q) ≫ Q.o

def comp.functor : P.functor ⋙ Q.functor ≅ (P.comp Q).functor := by
  unfold MvPoly.functor
  unfold comp
  apply Iso.trans
  calc _ ≅ Over.pullback P.i ⋙ pushforward P.p ⋙ (Over.pullback (P.h Q) ⋙
  Over.map (P.k Q)) ⋙ pushforward Q.p ⋙ Over.map Q.o := ?_
       _ ≅ Over.pullback P.i ⋙ pushforward P.p ⋙ Over.pullback (P.h Q) ⋙
           (Over.pullback (e Q.p (P.k Q)) ⋙ pushforward (g Q.p (P.k Q)) ⋙
            Over.map (v Q.p (P.k Q))) ⋙ Over.map Q.o := ?_
       _ ≅ Over.pullback P.i ⋙ (Over.pullback (P.m Q) ⋙ pushforward (r P Q)) ⋙
           (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o := ?_
       (Over.pullback P.i ⋙ (Over.pullback (P.m Q) ⋙ pushforward (r P Q)) ⋙
           (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o) ≅ _ := ?_
       (Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ Over.pullback (P.n Q))
   ⋙ (pushforward (P.p' Q) ⋙ pushforward (P.q Q)) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅ _ := ?_
       (Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ Over.pullback (P.n Q))
    ⋙ pushforward (P.p' Q ≫ P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅ _ := ?_

  · let hA' := (IsPullback.of_hasPullback P.o Q.i).flip
    apply Iso.symm
    letI := pullbackMapTwoSquare_of_isPullback_isIso hA'
    let this := asIso (pullbackMapTwoSquare (P.k Q) (P.h Q) Q.i P.o hA'.toCommSq)
    exact isoWhiskerLeft (Over.pullback P.i) <| isoWhiskerLeft (pushforward P.p) <| isoWhiskerRight this <| _
  · exact isoWhiskerLeft (Over.pullback P.i) <| isoWhiskerLeft (pushforward P.p)
      <| isoWhiskerLeft (Over.pullback (P.h Q)) <| isoWhiskerRight (pentagonIso Q.p (P.k Q)) <| (Over.map Q.o)

  · let hpb := (IsPullback.of_hasPullback P.p (pullback.fst P.o Q.i))
    have (hpb : IsPullback (P.m Q) (P.r Q) P.p (P.h Q)) :
       Over.pullback P.i ⋙ (pushforward P.p ⋙ Over.pullback (P.h Q)) ⋙
       (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o ≅
       Over.pullback P.i ⋙ (Over.pullback (P.m Q) ⋙ pushforward (r P Q)) ⋙
       (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o := by
       {exact isoWhiskerLeft _ <| isoWhiskerRight (pushforwardPullbackIsoSquare hpb) <| _}
    exact this hpb
  · let hpb : IsPullback (P.n Q) (P.p' Q) (P.r Q) (P.ε Q) := (IsPullback.of_hasPullback (r P Q) (ε P Q))
    have (hpb : IsPullback (P.n Q) (P.p' Q) (P.r Q) (P.ε Q)) :
       Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ (pushforward (r P Q) ⋙ Over.pullback (P.ε Q))
        ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅
       Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ (Over.pullback (P.n Q) ⋙ pushforward (p' P Q))
       ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o := by {
          apply isoWhiskerLeft _ <| isoWhiskerLeft _ <| _
          apply isoWhiskerRight
          exact pushforwardPullbackIsoSquare hpb}
    exact this hpb
  · apply isoWhiskerLeft _ <| isoWhiskerRight _ <| _; apply Iso.symm;
    exact pushforwardCompIso (P.p' Q) (P.q Q)
  · have : Over.pullback ((P.n Q ≫ P.m Q) ≫ P.i) ≅
       Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ Over.pullback (P.n Q) := by
      apply Iso.trans (pullbackComp ((P.n Q) ≫ (P.m Q)) P.i)
      apply isoWhiskerLeft _ <| (pullbackComp (P.n Q) (P.m Q))
    exact isoWhiskerRight (this).symm ((pushforward (P.p' Q ≫ P.q Q)) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o)
  simp only [assoc]
  exact isoWhiskerLeft _ <| isoWhiskerLeft _ (mapComp (P.w Q) Q.o).symm

end Composition






end MvPoly
#exit
namespace UvPoly

/-Note (SH): Alternatively, we can define the functor associated to a single variable polynomial in
terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials
to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.-/
def toMvPoly (P : UvPoly E B) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨E, B, terminal.from E, P.p, P.exp, terminal.from B⟩

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B`. -/
def proj' (P : UvPoly E B) (X : Over (⊤_ C)) :
  ((Π_ P.p).obj ((Over.pullback (terminal.from E)).obj X)).left ⟶ B :=
  ((Over.pullback (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

def auxFunctor (P : UvPoly E B) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor P.toMvPoly

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`.
Alternatively we can give a direct definition of `functor` in terms of exponentials. -/
def functor' (P : UvPoly E B) : C ⥤ C :=  equivOverTerminal.functor ⋙ P.auxFunctor ⋙ equivOverTerminal.inverse

def functorIsoFunctor' [HasBinaryProducts C] (P : UvPoly E B) : P.functor ≅ P.functor' := by
  unfold functor' auxFunctor functor MvPoly.functor toMvPoly
  simp
  sorry

end UvPoly

end CategroyTheory

end
