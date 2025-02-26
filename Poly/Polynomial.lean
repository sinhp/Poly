/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.LCCC.BeckChevalley

/-!
## References

* [Steve Awodey, Natural models of homotopy type theory][Awodey2017]
-/

/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`CartesianExponentiable` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- `P : MvPoly I O` is a multivariable polynomial with input variables in `I`,
output variables in `O`, and with arities `E` dependent on `I`. -/
structure MvPoly (I O : C) :=
  (E B : C)
  (i : E ⟶ I)
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)
  (o : B ⟶ O)

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly (E B : C) :=
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)

namespace MvPoly

open CartesianExponentiable

variable {C : Type*} [Category C] [HasPullbacks C] [HasTerminal C] [HasFiniteWidePullbacks C]

attribute [instance] MvPoly.exp

attribute [instance] UvPoly.exp

/-- The identity polynomial in many variables. -/
@[simps!]
def id (I : C) : MvPoly I I := ⟨I, I, 𝟙 I, 𝟙 I, CartesianExponentiable.id, 𝟙 I⟩

instance (I : C) : CartesianExponentiable ((id I).p) := CartesianExponentiable.id

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
def D' : C := ((Δ_ Q.p).obj (w P Q)).left

def ε' : (Δ_ Q.f).obj (P.w Q) ⟶ (.mk <| k P Q) := adj.counit.app (.mk <| k P Q)

abbrev r : B' P Q ⟶ A' P Q := by {apply pullback.snd}

def sq_III_comm : (m P Q) ≫ (f P) = (r P Q) ≫ (h P Q) := pullback.condition

def ε : D' P Q ⟶ A' P Q  := (ε' P Q).left

def N : C  := pullback (r P Q) (ε P Q)

--need to exploit how Δ f is defined
def q : D' P Q ⟶ (w P Q).left := (pullback.fst (P.w Q).hom Q.p)

/-- This is `p` in the diagram. -/
abbrev p' : N P Q ⟶ D' P Q := by {apply pullback.snd}

abbrev n : N P Q  ⟶ B' P Q := by {apply pullback.fst}

def sq_IV_comm : (n P Q) ≫ (r P Q) = (p' P Q) ≫ (ε P Q) := pullback.condition

/-- Functor composition for polynomial functors in the diagrammatic order. -/
def comp (P : MvPoly I J) (Q : MvPoly J K) : MvPoly I K where
  E := pullback (r P Q) (ε P Q) -- N
  B := (P.w Q).left --M
  i := n P Q ≫ m P Q ≫ P.i
  p := p' P Q ≫ q P Q
  exp := sorry
  o := (w P Q).hom ≫ Q.o

def v := Q.o

def BCIso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
IsIso (pullbackBeckChevalleyNatTrans (P.k Q) Q.u (P.h Q) P.t ((sq_I_comm P Q).symm))
  := pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso (P.k Q) (Q.u) (P.h Q) (P.t) hA'

/-- Δ_ h ⋙ Σ_ k ≅ Σ_ t ⋙ Δ_ u -/
def first_BCh_iso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
    Δ_ P.h Q ⋙ Σ_ P.k Q ≅ Σ_ P.o ⋙ Δ_ Q.i where
  hom := pullbackBeckChevalleyNatTrans (P.k Q) (Q.u) (P.h Q) (P.t) ((sq_I_comm P Q).symm)
  inv := Classical.choose ((BCIso P Q hA').out)
  hom_inv_id := (Classical.choose_spec (BCIso P Q hA').out).left
  inv_hom_id := (Classical.choose_spec (BCIso P Q hA').out).right

def s := P.i

/--Σv Πg ∆u Σt Πf ∆s ≅ Σv Πg Σk ∆h Πf ∆s-/
def first_step_prop_1_12_BCh_iso (hA' : IsPullback (P.k Q) (P.h Q) Q.u P.t) :
  Δ_ P.i ⋙ Π_ P.p ⋙ (Σ_ P.o ⋙ Δ_ Q.i) ⋙ Π_ Q.p ⋙ Σ_ Q.o
  ≅ Δ_ P.i ⋙ Π_ P.p ⋙ (Δ_ P.h Q ⋙ Σ_ P.k Q) ⋙ Π_ Q.p ⋙ Σ_ Q.o  := by {
  have : Δ_ P.h Q ⋙ Σ_ P.k Q ≅ Σ_ P.o ⋙ Δ_ Q.i := first_BCh_iso P Q hA'
  apply isoWhiskerLeft
  apply isoWhiskerLeft
  apply isoWhiskerRight
  exact (first_BCh_iso P Q hA').symm}

instance CEp' : CartesianExponentiable (p' P Q) := sorry

instance CEr : CartesianExponentiable (r P Q) := sorry

def bciii_Iso (hpb : IsPullback (P.m Q) (r P Q) (P.p) (P.h Q)) :
   IsIso (pushforwardBeckChevalleyNatTrans (P.m Q) (P.p) (r P Q) (P.h Q)
    (sq_III_comm P Q) P.exp (P.CEr Q)) := by {
    apply pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso
    exact hpb}

def BCiii (hpb : IsPullback (P.m Q) (r P Q) (P.p) (P.h Q)) :
     Π_ (P.p) ⋙ Δ_ P.h Q ≅ Δ_ P.m Q ⋙ Π_ (r P Q) where
  hom := (pushforwardBeckChevalleyNatTrans (P.m Q) (P.p) (r P Q) (P.h Q)
    (sq_III_comm P Q) P.exp (P.CEr Q))
  inv := Classical.choose ((bciii_Iso P Q hpb).out)
  hom_inv_id := (Classical.choose_spec (bciii_Iso P Q hpb).out).left
  inv_hom_id := (Classical.choose_spec (bciii_Iso P Q hpb).out).right

instance : CartesianExponentiable (P.q Q) := sorry

def half_of_3rd_step_prop_1_12_distrib_law (hpb : IsPullback (P.m Q) (P.r Q) P.p (P.h Q)) :
  Δ_ P.i ⋙ (Π_ P.p ⋙ Δ_ P.h Q) ⋙ (Δ_ P.ε Q ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o ≅
  Δ_ P.i ⋙ (Δ_ P.m Q ⋙ Π_ (r P Q)) ⋙
    (Δ_ P.ε Q ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o := by {
  have : Π_ (P.p) ⋙ Δ_ P.h Q ≅ Δ_ P.m Q ⋙ Π_ (r P Q) := P.BCiii Q hpb
  apply isoWhiskerLeft
  apply isoWhiskerRight
  exact P.BCiii Q hpb}

def bciv_Iso (hpb : IsPullback (P.n Q) (p' P Q) (r P Q) (P.ε Q)) :
   IsIso (pushforwardBeckChevalleyNatTrans (P.n Q) (r P Q) (p' P Q)  (P.ε Q)
    (sq_IV_comm P Q) (P.CEr Q) (P.CEp' Q)) := by {
  apply pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso
  exact hpb}

def BCiv (hpb : IsPullback (P.n Q) (p' P Q) (r P Q) (P.ε Q)) :
  Π_ (r P Q) ⋙ Δ_ P.ε Q ≅ Δ_ P.n Q ⋙ Π_ (p' P Q) where
  hom := (pushforwardBeckChevalleyNatTrans (P.n Q) (r P Q) (p' P Q)  (P.ε Q)
    (sq_IV_comm P Q) (P.CEr Q) (P.CEp' Q))
  inv := Classical.choose ((bciv_Iso P Q hpb).out)
  hom_inv_id := (Classical.choose_spec (bciv_Iso P Q hpb).out).left
  inv_hom_id := (Classical.choose_spec (bciv_Iso P Q hpb).out).right

def second_half_of_3rd_step_prop_1_12_distrib_law
    (hpb' : IsPullback (P.n Q) (P.p' Q) (P.r Q) (P.ε Q)) :
  Δ_ P.i ⋙ Δ_ P.m Q ⋙ (Π_ (r P Q) ⋙ Δ_ P.ε Q) ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o≅
  Δ_ P.i ⋙ Δ_ P.m Q ⋙ (Δ_ P.n Q ⋙ Π_ (p' P Q)) ⋙ Π_ P.q Q ⋙ Σ_ (P.w Q).hom ⋙ Σ_ Q.o := by {
  have : (Π_ (r P Q) ⋙ Δ_ P.ε Q) ≅ Δ_ P.n Q ⋙ Π_ (p' P Q) := BCiv P Q hpb'
  apply isoWhiskerLeft
  apply isoWhiskerLeft
  apply isoWhiskerRight
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

def foo : Σ_ u ⋙ Π_ f ≅ (Δ_ (e A B C u f) ⋙ Π_ (g' A B C u f ) ⋙ Σ_ (v' A B C u f)) := sorry

end distrib_diagram

--might need to construct this
def from_distrib_diagram_4_page_5 :
 Σ_ (P.k Q) ⋙ Π_ (Q.p) ≅ (Δ_ P.ε Q ⋙ Π_ (q P Q) ⋙ Σ_ (P.w Q).hom):= sorry

def from_BC_iii (hpbIII : IsPullback (P.m Q) (P.r Q) P.p (P.h Q)) :
  Π_ (P.p) ⋙ Δ_ P.h Q ≅ Δ_ P.m Q ⋙ Π_ (r P Q) := BCiii P Q hpbIII

/-- Σv Πg Σk ∆h Πf ∆s ≅ Σv Σw Πq ∆ε ∆h Πf ∆s-/
def second_step_prop_1_12_distrib_law :
  Δ_ P.i ⋙ Π_ P.p ⋙ Δ_ P.h Q ⋙ (Σ_ P.k Q ⋙ Π_ Q.p) ⋙ Σ_ Q.o ≅
  Δ_ P.i ⋙ Π_ P.p ⋙ Δ_ P.h Q ⋙ (Δ_ P.ε Q ⋙ Π_ (q P Q) ⋙ Σ_ (P.w Q).hom) ⋙ Σ_ Q.o := by {
  apply isoWhiskerLeft
  apply isoWhiskerLeft
  apply isoWhiskerLeft
  apply isoWhiskerRight
  exact from_distrib_diagram_4_page_5 P Q}

def comp.functor : P.functor ⋙ Q.functor ≅ (P.comp Q).functor := by {
  unfold MvPoly.functor
  apply Iso.trans
  exact first_step_prop_1_12_BCh_iso P Q (IsPullback.flip (IsPullback.of_hasPullback P.o Q.i))
  apply Iso.trans
  exact second_step_prop_1_12_distrib_law P Q
  apply Iso.trans
  exact half_of_3rd_step_prop_1_12_distrib_law P Q
    (IsPullback.of_hasPullback P.f (pullback.fst P.t Q.u))
  apply Iso.trans
  exact second_half_of_3rd_step_prop_1_12_distrib_law P Q (IsPullback.of_hasPullback _ _)
  --pseudo-functoriality
  have hdelta1 : Δ_ (P.m Q ≫ P.i) ≅ Δ_ P.i ⋙ Δ_ P.m Q := by {
    apply pullbackComp}
  have hdelta2 : Δ_ ((P.n Q ≫ P.m Q) ≫ P.i) ≅ (Δ_ P.i ⋙ Δ_ P.m Q) ⋙ Δ_ P.n Q := sorry
  unfold comp
  simp only [const_obj_obj]
  have hPi :  Π_ P.p' Q ⋙ Π_ P.q Q ≅ Π_ (P.p' Q ≫ P.q Q) := by {
    apply pushforwardCompIso}
  change (Δ_ P.i ⋙ Δ_ P.m Q ⋙ Δ_ P.n Q) ⋙ (Π_ P.p' Q ⋙
   Π_ P.q Q) ⋙ (Σ_ (P.w Q).hom ⋙ Σ_ Q.o) ≅ _
  have hSigma : (Σ_ (P.w Q).hom ⋙ Σ_ Q.o) ≅ Σ_ ((P.w Q).hom ≫ Q.o) := by{
     apply mapCompIso}
  aesop_cat}

end Composition

end MvPoly

namespace UvPoly

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : HasBinaryProducts C :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks C

variable {E B : C}

/-- The constant polynomial in many variables: for this we need the initial object -/
def const [HasInitial C] (S : C) : UvPoly (⊥_ C) S := ⟨initial.to S, inferInstance⟩

def smul [HasBinaryProducts C] (S : C) (P : UvPoly E B) : UvPoly (S ⨯ E) (S ⨯ B) :=
  ⟨prod.map (𝟙 S) P.p, sorry⟩

/-- The product of two polynomials in a single variable. -/
def prod (P : UvPoly E B) (Q : UvPoly E' B') [HasBinaryCoproducts C]:
    UvPoly ((E ⨯ B') ⨿ (B ⨯ E')) (B ⨯ B') where
  p := coprod.desc (prod.map P.p (𝟙 B')) (prod.map (𝟙 B) Q.p)
  exp := sorry -- perhaps we need extra assumptions on `C` to prove this, e.g. `C` is lextensive?

/-- For a category `C` with binary products, `P.functor : C ⥤ C` is the functor associated
to a single variable polynomial `P : UvPoly E B`. -/
def functor [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C :=
    (Δ_ E) ⋙ (Π_ P.p) ⋙ (Σ_ B)

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

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def proj (P : UvPoly E B) (X : C) : P.functor.obj X ⟶ B :=
  ((Δ_ E ⋙ Π_ P.p).obj X).hom

@[simp, reassoc (attr := simp)]
lemma map_proj {X Y : C} (P : UvPoly E B) (f : X ⟶ Y) : P.functor.map f ≫ P.proj Y = P.proj X := by
  simp [proj, functor]

/-- Essentially star is just the pushforward Beck-Chevalley natural transformation associated to
the square defined by `g`, but you have to compose with various natural isomorphisms. -/
def star (P : UvPoly E B) (Q : UvPoly F B) (g : E ⟶ F) (h : P.p = g ≫ Q.p) :
    Q.functor ⟶ P.functor := by
  unfold functor
  have hsquare : g ≫ Q.p = P.p ≫ 𝟙 _ := by simpa [comp_id] using h.symm
  have bc := pushforwardBeckChevalleyNatTrans g Q.p P.p (𝟙 _) hsquare Q.exp P.exp
  exact whiskerRight ((whiskerLeft (Δ_ F) ((whiskerLeft (Π_ Q.p)
    (baseChange.id B).symm.hom) ≫ bc)) ≫ (whiskerRight (baseChange.mapStarIso g).inv (Π_ P.p)))
      (Over.forget B)

variable (B)
/-- The identity polynomial functor in single variable. -/
@[simps!]
def id : UvPoly B B := ⟨𝟙 B, by infer_instance⟩

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `B × X`. -/
def id_apply (X : C) : (id B).functor.obj X ≅ B ⨯ X where
  hom := 𝟙 (B ⨯ X)
  inv := 𝟙 (B ⨯ X)

variable {B}

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'`
and `b : B ⟶ B'` such that the diagram
```
  E ---P.p--> B
  |           |
  e           b
  |           |
  v           v
  E' --Q.p--> B'
```
is a pullback square. -/
structure Hom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') where
  e : E ⟶ E'
  b : B ⟶ B'
  is_pullback : IsPullback P.p e b Q.p

namespace Hom

open IsPullback

-- baseChange.isLimitPullbackConeId _
def id (P : UvPoly E B) : Hom P P := ⟨𝟙 E, 𝟙 B, ⟨by aesop, ⟨ sorry ⟩⟩⟩

def comp {E' B' E'' B'' : C} {P : UvPoly E B} {Q : UvPoly E' B'} {R : UvPoly E'' B''}
    (f : Hom P Q) (g : Hom Q R) : Hom P R where
  e := f.e ≫ g.e
  b := f.b ≫ g.b
  is_pullback := paste_vert f.is_pullback g.is_pullback

end Hom

/-- Bundling up the the polynomials over different bases to form the underlying type of the
category of polynomials. -/
structure Total (C : Type*) [Category C] [HasPullbacks C] where
  (E B : C)
  (poly : UvPoly E B)

def Total.of (P : UvPoly E B) : Total C := ⟨E, B, P⟩

end UvPoly

open UvPoly

/-- The category of polynomial functors in a single variable. -/
instance : Category (UvPoly.Total C) where
  Hom P Q := UvPoly.Hom P.poly Q.poly
  id P := UvPoly.Hom.id P.poly
  comp := UvPoly.Hom.comp
  id_comp := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  comp_id := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  assoc := by
    simp [UvPoly.Hom.comp]

def Total.ofHom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') (α : P.Hom Q) :
    Total.of P ⟶ Total.of Q where
  e := α.e
  b := α.b
  is_pullback := α.is_pullback

namespace UvPoly

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : SMul C (Total C) where
  smul S P := Total.of (smul S P.poly)

/-- Scaling a polynomial `P` by an object `S` is isomorphic to the product of `const S` and the
polynomial `P`. -/
@[simps!]
def smul_eq_prod_const [HasBinaryCoproducts C] [HasInitial C] (S : C) (P : Total C) :
    S • P ≅ Total.of ((const S).prod P.poly) where
      hom := sorry
      inv := sorry
      hom_inv_id := sorry
      inv_hom_id := sorry

variable {E B : C}

def polyPair {Γ X : C} (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) :
    Σ b : Γ ⟶ B, pullback b P.p ⟶ X :=
  let b := be ≫ P.proj X
  let be' : Over.mk b ⟶ (Δ_ E ⋙ Π_ P.p).obj X := Over.homMk be
  let be'' := (P.exp.adj.homEquiv _ _).symm be'
  let be''' : pullback b P.p ⟶ E ⨯ X := be''.left
  ⟨b, be''' ≫ prod.snd⟩

def pairPoly {Γ X : C} (P : UvPoly E B) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P.functor.obj X :=
  let pbE := (Δ_ P.p).obj (Over.mk b)
  let eE : pbE ⟶ (Δ_ E).obj X := (Over.forgetAdjStar E).homEquiv _ _ e
  (P.exp.adj.homEquiv _ _ eE).left

/-! ## Generic pullback -/

/--
The UP of polynomial functors is mediated by a "generic pullback" [Awodey2017, p. 10, fig. 6].

```
     X
     ^
     | u₂
   genPb ---------------> E
 fst | ┘                  | p
     v                    v
P.functor.obj X --------> B
                P.proj X
```
-/

def genPb (P : UvPoly E B) (X : C) : C :=
  pullback (P.proj X) P.p

def genPb.fst (P : UvPoly E B) (X : C) : P.genPb X ⟶ P.functor.obj X :=
  pullback.fst (f := P.proj X) (g := P.p)

def genPb.u₂ (P : UvPoly E B) (X : C) : P.genPb X ⟶ X :=
  have : P.proj X = (P.polyPair <| 𝟙 <| P.functor.obj X).fst :=
    by simp [polyPair]
  (pullback.congrHom this rfl).hom ≫ (P.polyPair <| 𝟙 <| P.functor.obj X).snd

/-- The second component of `polyPair` is a comparison map of pullbacks composed with `genPb.u₂`. -/
theorem genPb.polyPair_snd_eq_comp_u₂' {Γ X : C} (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) :
    (P.polyPair be).snd = pullback.map (P.polyPair be).fst P.p (P.proj X) P.p be (𝟙 _) (𝟙 _) (by simp [polyPair]) (by simp) ≫
                          u₂ P X := by
  simp only [polyPair, u₂, homEquiv_counit, comp_left, ← assoc]
  congr 2
  aesop_cat

/-- Universal property of the polynomial functor. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) where
  toFun := P.polyPair
  invFun := fun ⟨b, e⟩ => P.pairPoly b e
  left_inv be := by
    simp_rw [polyPair, pairPoly, ← forgetAdjStar.homEquiv_symm]
    simp
  right_inv := by
    intro ⟨b, e⟩
    dsimp [polyPair, pairPoly]
    have := Over.forgetAdjStar.homEquiv (X := (Δ_ P.p).obj (Over.mk b)) (f := e)
    simp at this
    rw [this]
    set pairHat := P.exp.adj.homEquiv _ _ _
    congr! with h
    · simpa [-w] using pairHat.w
    · -- We deal with HEq/dependency by precomposing with an iso
      let i : Over.mk (pairHat.left ≫ P.proj X) ≅ Over.mk b :=
        Over.isoMk (Iso.refl _) (by simp [h])
      rw [
        show homMk _ _ = i.hom ≫ pairHat by ext; simp [i],
        show _ ≫ prod.snd = (pullback.congrHom h rfl).hom ≫ e by (
          simp only [pullback_obj_left,
          mk_left, mk_hom, star_obj_left, pullback_obj_hom, const_obj_obj, BinaryFan.mk_pt,
          BinaryFan.π_app_left, BinaryFan.mk_fst, id_eq, homEquiv_unit, id_obj, comp_obj,
          homEquiv_counit, map_comp, assoc, counit_naturality, left_triangle_components_assoc,
          comp_left, pullback_map_left, eqToHom_left, eqToHom_refl, homMk_left, prod.comp_lift,
          limit.lift_π, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_id,
          BinaryFan.π_app_right, BinaryFan.mk_snd, pullback.congrHom_hom, pairHat]
          congr 1
          ext <;> simp [i])
      ]
      generalize (hasPullbackHorizPaste .. : HasPullback (pairHat.left ≫ P.proj X) P.p) = pf
      generalize pairHat.left ≫ _ = x at h pf
      cases h
      simp [pullback.congrHom]

/-- `UvPoly.equiv` is natural in `Γ`. -/
lemma equiv_naturality_left {Δ Γ : C} (σ : Δ ⟶ Γ) (P : UvPoly E B) (X : C) (be : Γ ⟶ P.functor.obj X) :
    equiv P Δ X (σ ≫ be) = let ⟨b, e⟩ := equiv P Γ X be
                           ⟨σ ≫ b, pullback.lift (pullback.fst .. ≫ σ) (pullback.snd ..)
                                     (assoc (obj := C) .. ▸ pullback.condition) ≫ e⟩ := by
  dsimp
  congr! with h
  . simp [polyPair, pairPoly]
  . set g := _ ≫ (P.polyPair be).snd
    rw [(_ : (P.polyPair (σ ≫ be)).snd = (pullback.congrHom h rfl).hom ≫ g)]
    · generalize (P.polyPair (σ ≫ be)).fst = x at h
      cases h
      simp
    · simp only [polyPair, comp_obj, homEquiv_counit, id_obj, comp_left, pullback_obj_left,
      mk_left, mk_hom, star_obj_left, pullback_map_left, homMk_left, pullback.congrHom_hom, ←
      assoc, g]
      congr 2
      ext <;> simp

/-- `UvPoly.equiv` is natural in `X`. -/
lemma equiv_naturality_right {Γ X Y : C}
    (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) (f : X ⟶ Y) :
    equiv P Γ Y (be ≫ P.functor.map f) =
      let ⟨b, e⟩ := equiv P Γ X be
      ⟨b, e ≫ f⟩ := by
  dsimp
  congr! 1 with h
  . simp [polyPair]
  . set g := (P.polyPair be).snd ≫ f
    rw [(_ : (P.polyPair (be ≫ P.functor.map f)).snd = (pullback.congrHom h rfl).hom ≫ g)]
    · generalize (P.polyPair (be ≫ P.functor.map f)).fst = x at h
      cases h
      simp
    · dsimp only [polyPair, g]
      rw [homMk_comp (f_comp := by simp [proj, functor]) (g_comp := by simp [functor])]
      simp only [UvPoly.functor, Functor.comp_map, forget_map, left_homMk,
        homEquiv_naturality_right_symm, comp_left, assoc]
      rw [show ((Δ_ E).map f).left ≫ prod.snd = prod.snd ≫ f by simp]
      simp only [← assoc]
      congr 2
      simp only [comp_obj, forget_obj, star_obj_left, homEquiv_counit, id_obj, comp_left,
        pullback_obj_left, mk_left, mk_hom, pullback_map_left, Over.homMk_left,
        pullback.congrHom_hom, ← assoc]
      congr 1
      ext <;> simp

def foo [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Over.map P.poly.p) ⋙ (Over.map f.b) ≅ (Over.map f.e) ⋙ (Over.map Q.poly.p) :=
  mapSquareIso _ _ _ _ (f.is_pullback.w)

def bar [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Δ_ f.e) ⋙ (Σ_ P.poly.p) ≅ (Σ_ Q.poly.p) ⋙ (Δ_ f.b) := by
  set l := pullbackBeckChevalleyNatTrans P.poly.p f.b f.e Q.poly.p (f.is_pullback.w)
  have : IsIso l :=
    (pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso P.poly.p f.b f.e Q.poly.p f.is_pullback)
  exact asIso l

def bar' [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Δ_ P.poly.p) ⋙ (Σ_ f.e) ≅ (Σ_ f.b) ⋙ (Δ_ Q.poly.p) := by
  sorry

/-- A map of polynomials induces a natural transformation between their associated functors. -/
def naturality [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    P.poly.functor ⟶ Q.poly.functor := by
  sorry


def comp [HasPullbacks C] [HasTerminal C]
    {E B D C : C} (P : UvPoly E B) (Q : UvPoly D C) : UvPoly (pullback Q.p (genPb.u₂ P C)) (P.functor.obj C) :=
   {
     p :=  (pullback.snd Q.p (genPb.u₂ P C)) ≫  (genPb.fst P C)
     exp := by sorry
   }


end UvPoly

end
