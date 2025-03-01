/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.LCCC.BeckChevalley
import Poly.LCCC.Basic

/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`CartesianExponentiable` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasPullbacks C] [  HasFiniteWidePullbacks C] [LCC C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I`,
output variables in `O`, and with arities `E` dependent on `I`. -/
structure MvPoly (I O : C) where
  (E B : C)
  (i : E ⟶ I)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)
  (o : B ⟶ O)

namespace MvPoly

open CartesianExponentiable

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

attribute [instance] MvPoly.exp

/-- The identity polynomial in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, CartesianExponentiable.id, 𝟙 I⟩

instance (I : C) : CartesianExponentiable ((id I).p) := CartesianExponentiable.id



-- let's prove that the pullback along `initial.to` is isomorphic to the initial object
example [HasInitial C] {X Y : C} (f : Y ⟶ X) :
    IsPullback (initial.to Y) (𝟙 _) f (initial.to X) where
      w := by aesop
      isLimit' := by
        refine ⟨?_⟩
        sorry


/-- Given an object `X`, The unique map `initial.to X : ⊥_ C ⟶ X ` is exponentiable. -/
instance [HasInitial C] (X : C) : CartesianExponentiable (initial.to X) where
  functor := {
    obj := sorry
    map := sorry
  }
  adj := sorry


/-- The constant polynomial in many variables: for this we need the initial object. -/
def const {I O : C} [HasInitial C] (A : C) [HasBinaryProduct O A] : MvPoly I O :=
  ⟨⊥_ C, prod O A, initial.to I , initial.to _, inferInstance, prod.fst⟩

/-- The monomial polynomial in many variables. -/
def monomial {I O E : C} (i : E ⟶ I) (p : E ⟶ O) [CartesianExponentiable p]: MvPoly I O :=
  ⟨E, O, i, p, inferInstance, 𝟙 O⟩

/-- The sum of two polynomials in many variables. -/
def sum {I O : C} [HasBinaryCoproducts C] (P Q : MvPoly I O) : MvPoly I O where
  E := P.E ⨿ Q.E
  B := P.B ⨿ Q.B
  i := coprod.desc P.i Q.i
  p := coprod.map P.p Q.p
  exp := {
    functor := sorry  -- prove that the sum of exponentiables is exponentiable.
    adj := sorry
  }
  o := coprod.desc P.o Q.o

/-- The product of two polynomials in many variables. -/
def prod {I O : C} [HasBinaryProducts C] (P Q : MvPoly I O) : MvPoly I O :=
  sorry

def functor {I O : C} (P : MvPoly I O) :
    Over I ⥤ Over O :=
  (Δ_ P.i) ⋙ (Π_ P.p) ⋙ (Σ_ P.o)

variable (I O : C) (P : MvPoly I O)

def apply {I O : C} (P : MvPoly I O) [CartesianExponentiable P.p] : Over I → Over O := (P.functor).obj

/-TODO: write a coercion from `MvPoly` to a functor for evaluation of polynomials at a given
object.-/

def id_apply (q : X ⟶ I) : (id I).apply (Over.mk q) ≅ Over.mk q where
  hom := by
    simp [apply]
    simp [functor]
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

-- TODO: examples monomials, linear polynomials, 1/1-X, ...

-- TODO: The set of connected components of el(P) is in bijection with the set P(1) ≅ A

section Composition

variable {I J K : C}

variable (P : MvPoly I J) (Q : MvPoly J K)

open CategoryTheory.Over

def pullback_counit :
  (Δ_ Q.p).obj ((Π_ Q.p).obj (.mk <| pullback.snd P.o Q.i)) ⟶
    (.mk <| pullback.snd P.o Q.i) := adj.counit.app _

-- MK : Will golf all that later - keeping notation from the paper for now
abbrev t := P.o

abbrev u := Q.i

--Might not give the same pullback as Δ
def A' : C := pullback (t P) (u Q)

abbrev h : A' P Q ⟶ P.B := by {apply pullback.fst}

abbrev k : A' P Q ⟶ Q.E := by {apply pullback.snd}

def sq_I_comm : h P Q ≫ P.o = k P Q ≫ u Q := pullback.condition

abbrev f := P.p

def B' : C := pullback (f P) (h P Q)

abbrev m : B' P Q ⟶ P.E := by {apply pullback.fst}

--check which pullbacks typeclass is the right one
--since Δ is not the same as pullback in general

/-- `w` is obtained by applying `Π_g` to `k`. -/
def w : Over Q.B := (Π_ Q.p).obj (Over.mk <| k P Q)

def g := Q.p

/-- D' is the pullback of M along g -/
def D' : C := ((Δ_ Q.g).obj (w P Q)).left

def ε' : (Δ_ Q.f).obj (P.w Q) ⟶ (.mk <| k P Q) := adj.counit.app (.mk <| k P Q)

abbrev r : B' P Q ⟶ A' P Q := by {apply pullback.snd}

def sq_III_comm : (m P Q) ≫ (f P) = (r P Q) ≫ (h P Q) := pullback.condition

def ε : D' P Q ⟶ A' P Q  := (ε' P Q).left

def N : C := pullback (r P Q) (ε P Q)

--need to exploit how Δ f is defined
def q : D' P Q ⟶ (w P Q).left := pullback.fst (P.w Q).hom Q.p

/-- This is `p` in the diagram. -/
abbrev p' : N P Q ⟶ D' P Q := by {apply pullback.snd}

abbrev n : N P Q  ⟶ B' P Q := by {apply pullback.fst}

def sq_IV_comm : (n P Q) ≫ (r P Q) = (p' P Q) ≫ (ε P Q) := pullback.condition

instance : CartesianExponentiable (P.q Q) := sorry

instance : CartesianExponentiable (P.p' Q) := sorry

/-- Functor composition for polynomial functors in the diagrammatic order. -/
def comp (P : MvPoly I J) (Q : MvPoly J K) : MvPoly I K where
  E := pullback (r P Q) (ε P Q)
  B := (P.w Q).left
  i := n P Q ≫ m P Q ≫ P.i
  p := p' P Q ≫ q P Q
  exp := CartesianExponentiable.comp (P.p' Q) (P.q Q)
  o := (w P Q).hom ≫ Q.o

def v := Q.o

def BCIso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
    IsIso (pullbackBeckChevalleyNatTrans (P.k Q) Q.u (P.h Q) P.t (pullback.condition).symm) :=
  pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso (P.k Q) (Q.u) (P.h Q) (P.t) hA'

def first_BCh_iso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
    Δ_ P.h Q ⋙ Σ_ P.k Q ≅ Σ_ P.o ⋙ Δ_ Q.i where
  hom := pullbackBeckChevalleyNatTrans (P.k Q) (Q.u) (P.h Q) (P.t) (pullback.condition).symm
  inv := Classical.choose ((BCIso P Q hA').out)
  hom_inv_id := (Classical.choose_spec (BCIso P Q hA').out).left
  inv_hom_id := (Classical.choose_spec (BCIso P Q hA').out).right

def s := P.i

def first_step_BCh_iso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
    Δ_ P.i ⋙ Π_ P.p ⋙ (Σ_ P.o ⋙ Δ_ Q.i) ⋙ Π_ Q.p ⋙ Σ_ Q.o ≅
      Δ_ P.i ⋙ Π_ P.p ⋙ (Δ_ P.h Q ⋙ Σ_ P.k Q) ⋙ Π_ Q.p ⋙ Σ_ Q.o  := by {
  apply isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight _ <| _
  exact (first_BCh_iso P Q hA').symm}

instance CEp' : CartesianExponentiable (p' P Q) := sorry

instance CEr : CartesianExponentiable (r P Q) := sorry

def bciii_Iso (hpb : IsPullback (P.m Q) (r P Q) (P.p) (P.h Q)) :
  IsIso (pushforwardBeckChevalleyNatTrans (P.m Q) (P.p) (r P Q) (P.h Q)
    pullback.condition P.exp (P.CEr Q)) := by {
  apply pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso
  exact hpb}

def BCiii (hpb : IsPullback (P.m Q) (r P Q) (P.p) (P.h Q)) :
    Π_ (P.p) ⋙ Δ_ P.h Q ≅ Δ_ P.m Q ⋙ Π_ (r P Q) where
  hom := (pushforwardBeckChevalleyNatTrans (P.m Q) (P.p) (r P Q) (P.h Q)
    pullback.condition P.exp (P.CEr Q))
  inv := Classical.choose ((bciii_Iso P Q hpb).out)
  hom_inv_id := (Classical.choose_spec (bciii_Iso P Q hpb).out).left
  inv_hom_id := (Classical.choose_spec (bciii_Iso P Q hpb).out).right

instance : CartesianExponentiable (P.q Q) := sorry

def half_of_3rd_step_distrib_law (hpb : IsPullback (P.m Q) (P.r Q) P.p (P.h Q)) :
    Δ_ P.i ⋙ (Π_ P.p ⋙ Δ_ P.h Q) ⋙ (Δ_ P.ε Q ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o ≅
    Δ_ P.i ⋙ (Δ_ P.m Q ⋙ Π_ (r P Q)) ⋙ (Δ_ P.ε Q ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o := by {
  apply isoWhiskerLeft _ <| isoWhiskerRight _ <| _
  exact P.BCiii Q hpb}

def bciv_Iso (hpb : IsPullback (P.n Q) (p' P Q) (r P Q) (P.ε Q)) :
  IsIso (pushforwardBeckChevalleyNatTrans (P.n Q) (r P Q) (p' P Q)  (P.ε Q)
    pullback.condition (P.CEr Q) (P.CEp' Q)) := by {
  apply pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso
  exact hpb}

def BCiv (hpb : IsPullback (P.n Q) (p' P Q) (r P Q) (P.ε Q)) :
    Π_ (r P Q) ⋙ Δ_ P.ε Q ≅ Δ_ P.n Q ⋙ Π_ (p' P Q) where
  hom := (pushforwardBeckChevalleyNatTrans (P.n Q) (r P Q) (p' P Q) (P.ε Q)
    pullback.condition (P.CEr Q) (P.CEp' Q))
  inv := Classical.choose (bciv_Iso P Q hpb).out
  hom_inv_id := (Classical.choose_spec (bciv_Iso P Q hpb).out).left
  inv_hom_id := (Classical.choose_spec (bciv_Iso P Q hpb).out).right

def second_half__distrib_law
    (hpb' : IsPullback (P.n Q) (P.p' Q) (P.r Q) (P.ε Q)) :
  Δ_ P.i ⋙ Δ_ P.m Q ⋙ (Π_ (r P Q) ⋙ Δ_ P.ε Q) ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o ≅
  Δ_ P.i ⋙ Δ_ P.m Q ⋙ (Δ_ P.n Q ⋙ Π_ (p' P Q)) ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o := by {
  apply isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight _ <| _
  exact BCiv P Q hpb'}

instance : CartesianExponentiable (P.h Q) := sorry

section distrib_diagram

variable {C' : Type*} [Category C'] [HasPullbacks C']
  (A B C : C') (u : C ⟶ B) (f : B ⟶ A) [CartesianExponentiable f]

def Mbar : Over A := (Π_ f).obj <| Over.mk u

def M : C' := (Mbar A B C u f).left

def v' : M A B C u f ⟶ A := (Mbar A B C u f).hom

def N' : C' := ((Δ_ f).obj <| Over.mk (v' A B C u f)).left

def w' : N' A B C u f ⟶  B := pullback.snd _ _

def g' : N' A B C u f ⟶ M A B C u f := pullback.fst _ _

def H_pull_back_square : g' A B C u f ≫ v' A B C u f = w' A B C u f ≫ f := pullback.condition

def ε1 : ((Δ_ f).obj ((Π_ f).obj (Over.mk <| u))) ⟶ (.mk <| u) := adj.counit.app (.mk <| u)

def e : N' A B C u f ⟶ C := (ε1 A B C u f).left

instance : CartesianExponentiable (g' A B C u f) := sorry

def from_distrib_diagram_4_page_5_map :
  Σ_ u ⋙ Π_ f ⟶ (Δ_ (e A B C u f) ⋙ Π_ (g' A B C u f ) ⋙ Σ_ (v' A B C u f)) := sorry

def from_distrib_diagram_4_page_5_IsIso :
  IsIso (from_distrib_diagram_4_page_5_map A B C u f) := sorry

/-- We need to construct this iso (challenge) -/
def from_distrib_diagram_4_page_5_iso :
  Σ_ u ⋙ Π_ f ≅ (Δ_ (e A B C u f) ⋙ Π_ (g' A B C u f ) ⋙ Σ_ (v' A B C u f)) := sorry

end distrib_diagram

instance : CartesianExponentiable (P.k Q) := sorry

def second_step_distrib_law :
    Δ_ P.i ⋙ Π_ P.p ⋙ Δ_ P.h Q ⋙ (Σ_ P.k Q ⋙ Π_ Q.p) ⋙ Σ_ Q.o ≅
    Δ_ P.i ⋙ Π_ P.p ⋙ Δ_ P.h Q ⋙ (Δ_ P.ε Q ⋙ Π_ (q P Q) ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o := by {
  apply isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerLeft _ <| isoWhiskerRight _ <| _
  sorry
  --exact from_distrib_diagram_4_page_5_iso P Q
  }

def comp.functor : P.functor ⋙ Q.functor ≅ (P.comp Q).functor := by {
  unfold MvPoly.functor
  apply Iso.trans (first_step_BCh_iso P Q (IsPullback.flip (IsPullback.of_hasPullback P.o Q.i)))
  apply Iso.trans (second_step_distrib_law P Q)
  apply Iso.trans (half_of_3rd_step_distrib_law P Q
    (IsPullback.of_hasPullback P.f (pullback.fst P.t Q.u)))
  apply Iso.trans (second_half__distrib_law P Q (IsPullback.of_hasPullback _ _))
  --pseudo-functoriality
  have hdelta1 : Δ_ (P.m Q ≫ P.i) ≅ Δ_ P.i ⋙ Δ_ P.m Q := by {apply pullbackComp}
  have hdelta2 : Δ_ ((P.n Q ≫ P.m Q) ≫ P.i) ≅ Δ_ P.i ⋙ Δ_ P.m Q ⋙ Δ_ P.n Q := by {
    simp only [assoc]
    sorry}
  unfold comp
  simp only [const_obj_obj]
  have iso1 : (Δ_ P.i ⋙ Δ_ P.m Q ⋙ Δ_ P.n Q)
   ⋙ (Π_ P.p' Q ⋙ Π_ P.q Q) ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o ≅
    (Δ_ P.i ⋙ Δ_ P.m Q ⋙ Δ_ P.n Q)
   ⋙ Π_ (P.p' Q ≫ P.q Q) ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o := by
    apply isoWhiskerRight; exact Iso.refl _
  apply Iso.trans iso1
  have iso2 : (Δ_ P.i ⋙ Δ_ P.m Q ⋙ Δ_ P.n Q) ⋙ Π_ (P.p' Q ≫ P.q Q) ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o ≅
      Δ_ ((P.n Q ≫ P.m Q) ≫ P.i) ⋙ Π_ (P.p' Q ≫ P.q Q) ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o :=
    isoWhiskerRight hdelta2.symm _
  apply Iso.trans iso2
  simp only [assoc]
  apply isoWhiskerLeft
  sorry
  --apply isoWhiskerLeft
  --apply mapCompIso
  }

end Composition

end MvPoly

end
