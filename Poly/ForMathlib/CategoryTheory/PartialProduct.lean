/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.EqToHom

/-! ## Partial Products
A partial product is a simultaneous generalization of a product and an exponential object.

A partial product of an object `X` over a morphism `s : E ⟶ B` is is an object `P` together
with morphisms `fst : P —> A` and `snd : pullback fst s —> X`  which is universal among
such data.
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor


variable {C : Type*} [Category C] [HasPullbacks C]

namespace PartialProduct

variable {E B : C} (s : E ⟶ B) (X : C)

/--
A partial product cone over an object `X : C` and a morphism `s : E ⟶ B` is an object `pt : C`
together with morphisms `Fan.fst : pt —> B` and `Fan.snd : pullback Fan.fst s —> X`.

```
          X
          ^
  Fan.snd |
          |
          • --------------->   pt
          |                    |
          |        (pb)        | Fan.fst
          v                    v
          E ---------------->  B
                    s
```
-/
structure Fan where
  {pt : C}
  fst : pt ⟶ B
  snd : pullback fst s ⟶ X

theorem Fan.fst_mk {pt : C} (f : pt ⟶ B) (g : pullback f s ⟶ X) :
    Fan.fst (Fan.mk f g) = f := by
  rfl

variable {s X}

@[simp]
def comparison {P} {c : Fan s X} (f : P ⟶ c.pt) : pullback (f ≫ c.fst) s ⟶ pullback c.fst s :=
  pullback.map (f ≫ c.fst) s (c.fst) s f (𝟙 E) (𝟙 B) (by aesop) (by aesop)

@[simp]
def pullbackMap {c' c : Fan s X} (f : c'.pt ⟶ c.pt)
    (_ : f ≫ c.fst = c'.fst := by aesop_cat) :
    pullback c'.fst s ⟶ pullback c.fst s :=
  -- simp_rw [← h]
  -- exact pullbackPreComp f
  pullback.map c'.fst s c.fst s f (𝟙 E) (𝟙 B) (by aesop) (by aesop)

@[simp]
theorem pullbackMap_comparison {P} {c : Fan s X} (f : P ⟶ c.pt) :
    pullbackMap (c' := Fan.mk (f ≫ c.fst) (comparison f ≫ c.snd)) (c := c) f = comparison f := by
  rfl

/-- A map to the apex of a partial product cone induces a partial product cone by precomposition. -/
@[simps]
def Fan.extend (c : Fan s X) {A : C} (f : A ⟶ c.pt) : Fan s X where
  pt := A
  fst := f ≫ c.fst
  snd := (pullback.map _ _ _ _ f (𝟙 E) (𝟙 B) (by simp) (by aesop)) ≫ c.snd

structure Fan.Hom (c c' : Fan s X) where
  hom : c.pt ⟶ c'.pt
  w_left : hom ≫ c'.fst = c.fst := by aesop_cat
  w_right : pullbackMap hom ≫ c'.snd = c.snd := by
    aesop_cat

attribute [reassoc (attr := simp)] Fan.Hom.w_left Fan.Hom.w_right

  @[simps]
  instance category : Category (Fan s X) where
    Hom := Fan.Hom
    id c := ⟨𝟙 c.pt, by aesop_cat, by aesop_cat⟩
    comp {X Y Z} f g := ⟨f.hom ≫ g.hom, by simp [g.w_left, f.w_left], by sorry
      --have := pullback.map_comp (i₁:= 𝟙 E ) (j₁:= 𝟙 E ) (i₂:= f.hom) (j₂:= g.hom) (i₃:= 𝟙 B) (j₃ := 𝟙 B)
      -- have : 𝟙 E ≫ 𝟙 E = 𝟙 E := by simp
      -- rw [← this]
      -- try rw [← comp_id (𝟙 B)]
      -- simp [← pullback.map_comp (i₁:= 𝟙) ]
    ⟩
    id_comp f := by sorry --aesop_cat
    comp_id f := by sorry --aesop_cat
    assoc f g h := by sorry --aesop_cat

@[ext]
theorem Fan.Hom.ext {c c' : Fan s X} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

/-- Constructs an isomorphism of `PartialProduct.Fan`s out of an isomorphism of the apexes
that commutes with the projections. -/
def Fan.ext {c c' : Fan s X} (e : c.pt ≅ c'.pt)
    (h₁ : e.hom ≫ c'.fst = c.fst)
    (h₂ : pullbackMap e.hom ≫ c'.snd = c.snd) :
    c ≅ c' where
  hom := ⟨e.hom, h₁, h₂⟩
  inv := ⟨e.inv, by simp [Iso.inv_comp_eq, h₁] , by sorry⟩

structure IsLimit (cone : Fan s X) where
  /-- There is a morphism from any cone apex to `cone.pt` -/
  lift : ∀ c : Fan s X, c.pt ⟶ cone.pt
  /-- For any cone `c`, the morphism `lift c` followed by the first project `cone.fst` is equal
  to `c.fst`. -/
  fac_left : ∀ (c : Fan s X), lift c ≫ cone.fst = c.fst := by aesop_cat
  /-- For any cone `c`, the pullback pullbackMap of the cones followed by the second project
  `cone.snd` is equal to `c.snd` -/
  fac_right : ∀ (c : Fan s X),
    pullbackMap (lift c) ≫ cone.snd = c.snd := by
    aesop_cat
  /-- `lift c` is the unique such map  -/
  uniq : ∀ (c : Fan s X) (m : c.pt ⟶ cone.pt) (_ : m ≫ cone.fst = c.fst)
    (_ : pullbackMap m ≫ cone.snd = c.snd), m = lift c := by aesop_cat

variable (s X)

/--
A partial product of an object `X` over a morphism `s : E ⟶ B` is the universal partial product cone
over `X` and `s`.
-/
structure LimitFan where
  /-- The cone itself -/
  cone : Fan s X
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

/-- `HasPartialProduct s X` represents the mere existence of a partial product cone over
`s` and `X`. -/
class HasPartialProduct : Prop where mk' ::
  /-- There is some universal partial product cone over `s` and `X`. -/
  exists_partial_product : Nonempty <| LimitFan s X

instance HasPartialProduct.mk (l : LimitFan s X) : HasPartialProduct s X :=
  ⟨Nonempty.intro l⟩

def getLimitFan [HasPartialProduct s X] : LimitFan s X :=
  Classical.choice <| HasPartialProduct.exists_partial_product

end PartialProduct

open PartialProduct MonoidalCategory

variable {E B : C} (s : E ⟶ B) (X : C)

noncomputable abbrev partialProd [HasPartialProduct s X] : C :=
  (getLimitFan s X).cone.pt

/-- An arbitrary choice of limit cone for a functor. -/
def partialProd.cone [HasPartialProduct s X] : Fan s X :=
  (getLimitFan s X).cone

/-- Evidence that the arbitrary choice of cone provided by `limit.cone F` is a limit cone. -/
def partialProd.isLimit [HasPartialProduct s X] : IsLimit (partialProd.cone s X) :=
  (getLimitFan s X).isLimit

/-- The projection map to the first component of the partial product. -/
noncomputable abbrev partialProd.fst [HasPartialProduct s X] : partialProd s X ⟶ B :=
  Fan.fst <| partialProd.cone s X

noncomputable abbrev partialProd.snd [HasPartialProduct s X] :
    pullback (partialProd.fst s X) s ⟶ X :=
  Fan.snd <| partialProd.cone s X

variable {s X}

@[ext 1100]
theorem partialProd.hom_ext [HasPartialProduct s X] {f g : W ⟶ partialProd s X}
    (h₁ : f ≫ partialProd.fst s X = g ≫ partialProd.fst s X)
    (h₂ : comparison f ≫ partialProd.snd s X =
    eqToHom (by simp_rw [h₁]) ≫ comparison g ≫ partialProd.snd s X) :
    f = g := by
  sorry

/-- If the partial product of `s` and `X` exists, then every pair of morphisms `f : W ⟶ B` and
`g : pullback f s ⟶ X` induces a morphism `W ⟶ partialProd s X`. -/
abbrev partialProd.lift {W} [HasPartialProduct s X]
    (f : W ⟶ B) (g : pullback f s ⟶ X) : W ⟶ partialProd s X :=
  ((partialProd.isLimit s X)).lift (Fan.mk f g)

@[reassoc, simp]
theorem partialProd.lift_fst {W} [HasPartialProduct s X] (f : W ⟶ B) (g : pullback f s ⟶ X) :
    partialProd.lift f g ≫ partialProd.fst s X = f :=
  ((partialProd.isLimit s X)).fac_left (Fan.mk f g)

@[reassoc]
theorem partialProd.lift_snd {W} [HasPartialProduct s X] (f : W ⟶ B) (g : pullback f s ⟶ X) :
    (pullbackMap (partialProd.lift f g) _) ≫ (partialProd.snd s X) = g :=
  ((partialProd.isLimit s X)).fac_right (Fan.mk f g)

/-- The partial product of `X` and the identity morphism `𝟙 : B ⟶ B` is the exponential object
`B ⨯ X`. -/
instance hasPartialProduct.id [HasBinaryProduct B X] : HasPartialProduct (𝟙 B) X := by sorry

def partialProd.id [HasBinaryProduct B X] : partialProd (𝟙 B) X ≅ B ⨯ X := sorry

instance hasPartialProduct.prod [HasTerminal C] [HasBinaryProduct B X] :
    HasPartialProduct (terminal.from B) X := by
  sorry

attribute [local instance] CategoryTheory.ChosenFiniteProducts.ofFiniteProducts

def partialProd.prod [HasFiniteProducts C] [Exponentiable X] :
    partialProd (terminal.from B) X ≅ X ⟹ B := by
  sorry
