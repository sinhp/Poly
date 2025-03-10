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

import Poly.UvPoly

/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`ExponentiableMorphism` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

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
  ⟨⊥_ C, prod O A, initial.to I , initial.to _, inferInstance, prod.fst⟩

/-- The monomial polynomial in many variables. -/
def monomial {I O E : C} (i : E ⟶ I) (p : E ⟶ O) [ExponentiableMorphism p]: MvPoly I O :=
  ⟨E, O, i, p, inferInstance, 𝟙 O⟩

/-- The sum of two polynomials in many variables. -/
def sum {I O : C} [HasBinaryCoproducts C] (P Q : MvPoly I O) : MvPoly I O where
  E := P.E ⨿ Q.E
  B := P.B ⨿ Q.B
  i := coprod.desc P.i Q.i
  p := coprod.map P.p Q.p
  exp := sorry  -- prove that the sum of exponentiables is exponentiable.
  o := coprod.desc P.o Q.o

/-- The product of two polynomials in many variables. -/
def prod {I O : C} [HasBinaryProducts C] (P Q : MvPoly I O) : MvPoly I O := sorry

protected def functor {I O : C} (P : MvPoly I O) :
    Over I ⥤ Over O :=
  (Over.pullback P.i) ⋙ (pushforward P.p) ⋙ (Over.map P.o)

variable (I O : C) (P : MvPoly I O)

def apply {I O : C} (P : MvPoly I O) [ExponentiableMorphism P.p] : Over I → Over O := (P.functor).obj

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

/-- Σv Πg (∆u Σt) ΠP.p ∆s ≅ Σv Πg (Σk ∆h) ΠP.p ∆s -/
def first_step_BCh_iso (hA' : IsPullback (P.k Q) (P.h Q) Q.i P.o) :
  Over.pullback P.i ⋙ pushforward P.p ⋙ (Over.pullback (P.h Q) ⋙
  Over.map (P.k Q)) ⋙ pushforward Q.p ⋙ Over.map Q.o ≅
  Over.pullback P.i ⋙ pushforward P.p ⋙
  (Over.map P.o ⋙ Over.pullback Q.i) ⋙ pushforward Q.p ⋙ Over.map Q.o := by
  letI := pullbackBeckChevalleySquare_of_isPullback_isIso hA'
  let this := asIso (pullbackBeckChevalleySquare (P.k Q) (P.h Q) Q.i P.o _)
  exact isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight this <| _

/-- Σv (Σw Πq) ∆ε (∆h ΠP.p) ∆s ≅ Σv (Πg Σk) ∆h Πf ∆s -/
def half_of_3rd_step_distrib_law (hpb : IsPullback (P.m Q) (P.r Q) P.p (P.h Q)) :
    Over.pullback P.i ⋙ (pushforward P.p ⋙ Over.pullback (P.h Q)) ⋙
    (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o ≅
    Over.pullback P.i ⋙ (Over.pullback (P.m Q) ⋙ pushforward (r P Q)) ⋙
    (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o := by
  letI := (pushforwardBeckChevalleySquare_of_isPullback_isIso hpb)
  let this := asIso ((pushforwardBeckChevalleySquare (P.m Q) (P.r Q) (P.p) (P.h Q) hpb.toCommSq))
  exact isoWhiskerLeft _ <| isoWhiskerRight this <| _

/-- ΣQ.o Σw Πq (∆ε Πr) ∆m ΔP.i ≅ ΣQ.o Σw Πq (Πp' ∆n) ∆m ΔP.i -/
def second_half__distrib_law (hpb : IsPullback (P.n Q) (P.p' Q) (P.r Q) (P.ε Q)) :
  Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ (pushforward (r P Q) ⋙ Over.pullback (P.ε Q))
  ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅
  Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ (Over.pullback (P.n Q) ⋙ pushforward (p' P Q))
  ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o := by
  letI := (pushforwardBeckChevalleySquare_of_isPullback_isIso hpb)
  let this := asIso (pushforwardBeckChevalleySquare (P.n Q) (P.p' Q) (r P Q) (P.ε Q) hpb.toCommSq)
  exact isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight this _

def comp.functor : P.functor ⋙ Q.functor ≅ (P.comp Q).functor := by
  unfold MvPoly.functor
  unfold comp
  apply Iso.trans
  calc _ ≅ Over.pullback P.i ⋙ pushforward P.p ⋙ (Over.pullback (P.h Q) ⋙
  Over.map (P.k Q)) ⋙ pushforward Q.p ⋙ Over.map Q.o := ?_
       _ ≅ Over.pullback P.i ⋙ pushforward P.p ⋙ Over.pullback (P.h Q) ⋙
           (Over.pullback (e Q.p (P.k Q)) ⋙ pushforward (g Q.p (P.k Q)) ⋙
            Over.map (v Q.p (P.k Q))) ⋙ Over.map Q.o := ?_
       _ ≅ (Over.pullback P.i ⋙ (Over.pullback (P.m Q) ⋙ pushforward (r P Q)) ⋙
           (Over.pullback (P.ε Q) ⋙ pushforward (P.q Q) ⋙ Over.map (P.w Q)) ⋙ Over.map Q.o) := ?_
       _ ≅ _ := ?_
       (Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ Over.pullback (P.n Q))
   ⋙ (pushforward (P.p' Q) ⋙ pushforward (P.q Q)) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅ _ := ?_
       (Over.pullback P.i ⋙ Over.pullback (P.m Q) ⋙ Over.pullback (P.n Q))
    ⋙ pushforward (P.p' Q ≫ P.q Q) ⋙ Over.map (P.w Q) ⋙ Over.map Q.o ≅ _ := ?_

  · let hA' := ((IsPullback.of_hasPullback P.o Q.i).flip)
    apply Iso.symm
    letI := pullbackBeckChevalleySquare_of_isPullback_isIso hA'
    let this := asIso (pullbackBeckChevalleySquare (P.k Q) (P.h Q) Q.i P.o _)
    exact isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight this <| _
  · exact isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight (pentagonIso Q.p (P.k Q)) <| _

  · let hpb := (IsPullback.of_hasPullback P.p (pullback.fst P.o Q.i))

    exact (half_of_3rd_step_distrib_law P Q hpb)

  · let hpb := (IsPullback.of_hasPullback (r P Q) (ε P Q))
    exact (second_half__distrib_law P Q hpb)

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



end
