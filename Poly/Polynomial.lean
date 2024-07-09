/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
--import Mathlib.CategoryTheory.Category.Limit
import Poly.Exponentiable
import Poly.LCCC.BeckChevalley
-- import Poly.LCCC.Basic

/-!
# Polynomial Functor


-- TODO: there are various `sorry`-carrying proofs in below which require instances of `CartesianExponentiable`
for various construcitons on morphisms. They need to be defined in `Poly.Exponentiable`.
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
def const {I O : C} [HasInitial C] (A : C) [HasBinaryProduct O A] : MvPoly I O := ⟨⊥_ C, prod O A, initial.to I , initial.to _, inferInstance, prod.fst⟩

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

def apply [CartesianExponentiable P.p] : Over I → Over O := (P.functor).obj

-- TODO: write a coercion from `MvPoly` to a functor for evalutation of polynomials at a given object.

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

variable {I}

variable {J K : C}

variable (P : MvPoly I J) (Q : MvPoly J K)

-- the auxiliary pullback square with `P.o`, `Q.i`
def pullback_fst :
    pullback (P.o) (Q.i) ⟶ P.B :=
  pullback.fst

def pullback_snd :
    pullback (P.o) (Q.i) ⟶ Q.E :=
  pullback.snd

-- def pullback_fst_pb

def pullback_counit :
    (Δ_ Q.p).obj  ((Π_ Q.p).obj (Over.mk <| pullback_snd P Q)) ⟶ (Over.mk <| pullback_snd P Q) :=
  adj.counit.app _

def comp (P: MvPoly I J) (Q : MvPoly J K) : MvPoly I K := sorry

end Composition

end MvPoly

namespace UvPoly

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : HasBinaryProducts C := by sorry --infer_instance --not working; we should get this from `HasTerminal` and `HasPullbacks`?

variable {E B : C}

/-- The constant polynomial in many variables: for this we need the initial object. -/
def const [HasInitial C] (S : C) : UvPoly (⊥_ C) S := ⟨initial.to S, inferInstance⟩

def smul [HasBinaryProducts C] (S : C) (P : UvPoly E B) : UvPoly (S ⨯ E) (S ⨯ B) :=
  ⟨prod.map (𝟙 S) P.p, sorry⟩

/-- The product of two polynomials in a single variable. -/
def prod (P : UvPoly E B) (Q : UvPoly E' B') [HasBinaryCoproducts C]: UvPoly ((E ⨯ B') ⨿ (B ⨯ E')) (B ⨯ B') where
  p := coprod.desc (prod.map P.p (𝟙 B')) (prod.map (𝟙 B) Q.p)
  exp := sorry -- perhaps we need extra assumptions on `C` to prove this, e.g. `C` is lextensive?

/-- For a category `C` with binary products, `P.functor : C ⥤ C` is the functor associated
to a single variable polynomial `P : UvPoly E B`. -/
def functor [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C :=
    (Δ_ E) ⋙ (Π_ P.p) ⋙ (Σ_ B)

-- Note (SH): Alternatively, we can define the functor associated to a single variable polyonimal in terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.
def toMvPoly (P : UvPoly E B) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨E, B, terminal.from E, P.p, P.exp, terminal.from B⟩

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B`. -/
def proj' (P : UvPoly E B) (X : Over (⊤_ C)) :
  ((Π_ P.p).obj ((baseChange (terminal.from E)).obj X)).left ⟶ B :=
  ((baseChange (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

def auxFunctor (P : UvPoly E B) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor P.toMvPoly

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`. Alternatively we can give a direct definition of `functor` in terms of exponetials. -/
def functor' (P : UvPoly E B) : C ⥤ C :=  equivOverTerminal.functor ⋙  P.auxFunctor ⋙ equivOverTerminal.inverse

def functorIsoFunctor' [HasBinaryProducts C] (P : UvPoly E B) : P.functor ≅ P.functor' := by
  unfold functor' auxFunctor functor MvPoly.functor toMvPoly
  simp
  sorry

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def proj (P : UvPoly E B) (X : C) : (functor P).obj X ⟶ B :=
  ((Δ_ E ⋙ Π_ P.p).obj X).hom

/-- Essentially star is just the pushforward Beck-Chevalley natural transformation associated to the square defined by `g`, but you have to compose with various natural isomorphisms. -/
def star (P : UvPoly E B) (Q : UvPoly F B) (g : E ⟶ F) (h : P.p = g ≫ Q.p) :
    Q.functor ⟶ P.functor := by
  unfold functor
  have hsquare : g ≫ Q.p = P.p ≫ 𝟙 _ := by simpa [comp_id] using h.symm
  have bc := pushforwardBeckChevalleyNatTrans g Q.p P.p (𝟙 _) hsquare Q.exp P.exp
  exact whiskerRight ((whiskerLeft (Δ_ F) ((whiskerLeft (Π_ Q.p) (baseChange.id B).symm.hom) ≫ bc)) ≫ (whiskerRight (baseChange.mapStarIso g).inv (Π_ P.p))) (Over.forget B)

/-- Evaluating a single variable polynomial at an object `X` -/
def apply (P : UvPoly E B) (X : C) : C := P.functor.obj X

variable (B)
/-- The identity polynomial functor in single variable. -/
@[simps!]
def id : UvPoly B B := ⟨𝟙 B, by infer_instance⟩

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `B × X`. -/
def id_apply (X : C) : (id B).apply X ≅ B ⨯ X where
  hom := 𝟙 (B ⨯ X)
  inv := 𝟙 (B ⨯ X)

variable {B}

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'` and `b : B ⟶ B'` such that the diagram
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

def comp {E' B' E'' B'' : C} {P : UvPoly E B} {Q : UvPoly E' B'} {R : UvPoly E'' B''} (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  e := f.e ≫ g.e
  b := f.b ≫ g.b
  is_pullback := paste_vert f.is_pullback g.is_pullback

end Hom

/-- Bundling up the the polynomials over different bases to form the underlying type of the category of polynomials. -/
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

instance : SMul C (Total C) where
  smul S P := Total.of (smul S P.poly)

/-- Scaling a polynomial `P` by an object `S` is isomorphic to the product of `const S` and the polynomial `P`. -/
@[simps!]
def smul_eq_prod_const [HasBinaryCoproducts C] [HasInitial C] (S : C) (P : Total C) :
    S • P ≅ Total.of ((const S).prod P.poly) where
      hom := sorry
      inv := sorry
      hom_inv_id := sorry
      inv_hom_id := sorry

def polyPair (P : UvPoly E B) (Γ : C) (X : C) (be : Γ ⟶ P.functor.obj X) :
    Σ b : Γ ⟶ B, pullback b P.p ⟶ X :=
  let b := be ≫ P.proj X
  let be' : Over.mk b ⟶ (Δ_ E ⋙ Π_ P.p).obj X := Over.homMk be
  let be'' := (P.exp.adj.homEquiv _ _).symm be'
  let be''' : pullback b P.p ⟶ E ⨯ X := be''.left
  ⟨b, be''' ≫ prod.snd⟩

def pairPoly (P : UvPoly E B) (Γ : C) (X : C) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P.functor.obj X :=
  let pbE := (Δ_ P.p).obj (Over.mk b)
  let eE : pbE ⟶ (Δ_ E).obj X := (Over.forgetAdjStar E).homEquiv _ _ e
  (P.exp.adj.homEquiv _ _ eE).left

/-- Universal property of the polynomial functor. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ Σ b : Γ ⟶ B, pullback b P.p ⟶ X where
  toFun := polyPair P Γ X
  invFun := fun ⟨b, e⟩ => pairPoly P Γ X b e
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
      rw [show homMk _ _ = eqToHom (by rw [h]) ≫ pairHat by ext; simp,
        show _ ≫ prod.snd = (pullback.congrHom h rfl).hom ≫ e by simp [pairHat]]
      generalize pairHat.left ≫ _ = x at h
      cases h
      simp [pullback.congrHom]

/-- `UvPoly.equiv` is natural in `Γ`. -/
lemma equiv_naturality {Δ Γ : C} (σ : Δ ⟶ Γ) (P : UvPoly E B) (X : C) (be : Γ ⟶ P.functor.obj X) :
    equiv P Δ X (σ ≫ be) = let ⟨b, e⟩ := equiv P Γ X be
                           ⟨σ ≫ b, pullback.lift (pullback.fst ≫ σ) pullback.snd
                                     (assoc (obj := C) .. ▸ pullback.condition) ≫ e⟩ := by
  dsimp
  congr! with h
  . simp [polyPair, pairPoly]
  . set g := _ ≫ (P.polyPair Γ X be).snd
    rw [(_ : (P.polyPair Δ X (σ ≫ be)).snd = (pullback.congrHom h rfl).hom ≫ g)]
    · generalize (P.polyPair Δ X (σ ≫ be)).fst = x at h
      cases h
      simp
    · simp [g, polyPair, ← assoc]
      congr 2
      ext <;> simp

def foo [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Over.map P.poly.p) ⋙ (Over.map f.b) ≅ (Over.map f.e) ⋙ (Over.map Q.poly.p) := by
  apply mapSquareIso
  rw [f.is_pullback.w]

def bar [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    ( Δ_ f.e) ⋙ ( Σ_ P.poly.p) ≅ ( Σ_ Q.poly.p) ⋙ ( Δ_ f.b) := by
  set l := pullbackBeckChevalleyNatTrans P.poly.p f.b f.e Q.poly.p (f.is_pullback.w)
  have : IsIso l := (pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso P.poly.p f.b f.e Q.poly.p f.is_pullback)
  exact asIso l

def bar' [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Δ_ P.poly.p) ⋙ (Σ_ f.e) ≅ (Σ_ f.b) ⋙ (Δ_ Q.poly.p) := by
  sorry

/-- A map of polynomials induces a natural transformation between their associated functors. -/
def naturality [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    P.poly.functor ⟶ Q.poly.functor := by
  sorry

end UvPoly

end
