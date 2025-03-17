/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Poly.ForMathlib.CategoryTheory.Comma.Over.Pullback
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

open CategoryTheory Category Limits Functor Over


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

def Fan.over (c : Fan s X) : Over B := Over.mk c.fst

def Fan.overPullbackToStar (c : Fan s X) [HasBinaryProducts C] :
    (Over.pullback s).obj c.over ⟶ (Over.star E).obj X :=
  (forgetAdjStar E).homEquiv _ _ c.snd

@[reassoc (attr := simp)]
theorem Fan.overPullbackToStar_snd {c : Fan s X} [HasBinaryProducts C] :
    (Fan.overPullbackToStar c).left ≫ prod.snd = c.snd := by
  simp [Fan.overPullbackToStar, Adjunction.homEquiv, forgetAdjStar.unit_app]

-- note: the reason we use `(Over.pullback s).map` instead of `pullback.map` is that
-- we want to readily use lemmas about the adjunction `pullback s ⊣ pushforward s` in `UvPoly`.
def comparison {P} {c : Fan s X} (f : P ⟶ c.pt) : pullback (f ≫ c.fst) s ⟶ pullback c.fst s :=
  (Over.pullback s |>.map (homMk f (by simp) : Over.mk (f ≫ c.fst) ⟶ Over.mk c.fst)).left

theorem comparison_pullback.map {P} {c : Fan s X} {f : P ⟶ c.pt} :
    comparison f = pullback.map (f ≫ c.fst) s (c.fst) s f (𝟙 E) (𝟙 B) (by aesop) (by aesop) := by
  simp [comparison, pullback.map]

def pullbackMap {c' c : Fan s X} (f : c'.pt ⟶ c.pt)
    (h : f ≫ c.fst = c'.fst := by aesop_cat) :
    pullback c'.fst s ⟶ pullback c.fst s := by
  simpa using  ((Over.pullback s).map (Over.homMk f h : Over.mk (c'.fst) ⟶ Over.mk c.fst)).left

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
    id c := ⟨𝟙 c.pt, by aesop_cat, by simp [pullbackMap]⟩
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

end PartialProduct

open PartialProduct

variable {E B : C} {s : E ⟶ B} {X : C}

abbrev partialProd (c : LimitFan s X) : C :=
  c.cone.pt

abbrev partialProd.cone (c : LimitFan s X) : Fan s X :=
  c.cone

abbrev partialProd.isLimit (c : LimitFan s X) : IsLimit (partialProd.cone c) :=
  c.isLimit

abbrev partialProd.fst (c : LimitFan s X) : partialProd c ⟶ B :=
  Fan.fst <| partialProd.cone c

abbrev partialProd.snd (c : LimitFan s X) :
    pullback (partialProd.fst c) s ⟶ X :=
  Fan.snd <| partialProd.cone c

/-- If the partial product of `s` and `X` exists, then every pair of morphisms `f : W ⟶ B` and
`g : pullback f s ⟶ X` induces a morphism `W ⟶ partialProd s X`. -/
abbrev partialProd.lift {W} (c : LimitFan s X)
    (f : W ⟶ B) (g : pullback f s ⟶ X) : W ⟶ partialProd c :=
  ((partialProd.isLimit c)).lift (Fan.mk f g)

@[reassoc, simp]
theorem partialProd.lift_fst {W} {c : LimitFan s X} (f : W ⟶ B) (g : pullback f s ⟶ X) :
    partialProd.lift c f g ≫ partialProd.fst c = f :=
  ((partialProd.isLimit c)).fac_left (Fan.mk f g)

@[reassoc]
theorem partialProd.lift_snd {W} (c : LimitFan s X) (f : W ⟶ B) (g : pullback f s ⟶ X) :
    (comparison (partialProd.lift c f g)) ≫ (partialProd.snd c) =
    (pullback.congrHom (partialProd.lift_fst f g) rfl).hom ≫ g := by
  let h := ((partialProd.isLimit c)).fac_right (Fan.mk f g)
  rw [← pullbackMap_comparison]
  simp [pullbackMap, pullback.map]
  sorry

variable (s) (X)

/-- `HasPartialProduct s X` represents the mere existence of a partial product cone over
`s` and `X`. -/
class HasPartialProduct : Prop where mk' ::
  /-- There is some universal partial product cone over `s` and `X`. -/
  exists_partial_product : Nonempty <| LimitFan s X

namespace HasPartialProduct

instance mk (c : LimitFan s X) : HasPartialProduct s X :=
  ⟨Nonempty.intro c⟩

def getLimitFan [HasPartialProduct s X] : LimitFan s X :=
  Classical.choice <| HasPartialProduct.exists_partial_product

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

-- note that @[ext] does not work becasue h₂ depends on h₁.
theorem partialProd.hom_ext {W : C} [HasPartialProduct s X] {f g : W ⟶ partialProd s X}
    (h₁ : f ≫ partialProd.fst s X = g ≫ partialProd.fst s X)
    (h₂ : comparison f ≫ partialProd.snd s X =
    (pullback.congrHom h₁ rfl).hom ≫ comparison g ≫ partialProd.snd s X) :
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
    (comparison (partialProd.lift f g)) ≫ (partialProd.snd s X) =
    (pullback.congrHom (partialProd.lift_fst f g) rfl).hom ≫ g := by
  let h := ((partialProd.isLimit s X)).fac_right (Fan.mk f g)
  rw [← pullbackMap_comparison]
  sorry

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

end HasPartialProduct
