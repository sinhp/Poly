/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Poly.ForMathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.EqToHom

/-! ## Partial Products
A partial product is a simultaneous generalization of a product and an exponential object.

A partial product of an object `X` over a morphism `s : E ⟶ B` is is an object `P` together
with morphisms `fst : P —> A` and `snd : pullback fst s —> X`  which is universal among
such data.
-/

-- Lean 4.34 tightened the transparency `simp`/`rw` use when matching, which breaks goals
-- stated through reducible wrappers (`pullback.lift`/`pullback.fst`, `Over.Hom`).
-- Mathlib sets the same option throughout its own `Over`/pullback files.
set_option backward.isDefEq.respectTransparency false

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
    Fan.fst (Fan.mk f g) = f := rfl

variable {s X}

def Fan.over (c : Fan s X) : Over B := Over.mk c.fst

def Fan.overPullbackToStar [HasBinaryProducts C] (c : Fan s X)  :
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
    (_ : f ≫ c.fst = c'.fst := by aesop_cat) :
    pullback c'.fst s ⟶ pullback c.fst s :=
  ((Over.pullback s).map (Over.homMk f (by aesop) : Over.mk (c'.fst) ⟶ Over.mk c.fst)).left

theorem pullbackMap_comparison {P} {c : Fan s X} (f : P ⟶ c.pt) :
    pullbackMap (c' := Fan.mk (f ≫ c.fst) (comparison f ≫ c.snd)) (c := c) f = comparison f := rfl

/-- A map to the apex of a partial product cone induces a partial product cone by precomposition. -/
@[simps]
def Fan.extend (c : Fan s X) {A : C} (f : A ⟶ c.pt) : Fan s X where
  pt := A
  fst := f ≫ c.fst
  snd := (pullback.map _ _ _ _ f (𝟙 E) (𝟙 B) (by simp) (by aesop)) ≫ c.snd

@[ext]
structure Fan.Hom (c c' : Fan s X) where
  hom : c.pt ⟶ c'.pt
  w_left : hom ≫ c'.fst = c.fst := by aesop_cat
  w_right : pullbackMap hom ≫ c'.snd = c.snd := by aesop_cat

attribute [reassoc (attr := simp)] Fan.Hom.w_left Fan.Hom.w_right

-- TODO: this is taking ages to check since 4.28.0-rc1.
set_option maxHeartbeats 0 in
@[simps]
instance : Category (Fan s X) where
  Hom := Fan.Hom
  id c := ⟨𝟙 c.pt, by simp, by simp [pullbackMap]⟩
  comp {X Y Z} f g := ⟨f.hom ≫ g.hom, by simp [g.w_left, f.w_left], by
    rw [← f.w_right, ← g.w_right]
    simp_rw [← Category.assoc]
    congr 1
    ext <;> simp [pullbackMap]
  ⟩
  id_comp f := by dsimp; ext; simp
  comp_id f := by dsimp; ext; simp
  assoc f g h := by dsimp; ext; simp

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
  fac_left : ∀ c : Fan s X, lift c ≫ cone.fst = c.fst := by aesop_cat
  /-- For any cone `c`, the pullback pullbackMap of the cones followed by the second project
  `cone.snd` is equal to `c.snd` -/
  fac_right : ∀ c : Fan s X,
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

def overPullbackToStar [HasBinaryProducts C] {W} (f : W ⟶ B) (g : pullback f s ⟶ X) :
    (Over.pullback s).obj (Over.mk f) ⟶ (Over.star E).obj X :=
  Fan.overPullbackToStar <| Fan.mk f g

theorem overPullbackToStar_prod_snd [HasBinaryProducts C]
    {W} {f : W ⟶ B} {g : pullback f s ⟶ X} :
    (overPullbackToStar f g).left ≫ prod.snd = g := by
  simp only [overPullbackToStar, Fan.overPullbackToStar, Fan.over]
  simp only [forgetAdjStar.homEquiv_left_lift]
  aesop

abbrev partialProd (c : LimitFan s X) : C := c.cone.pt

abbrev partialProd.cone (c : LimitFan s X) : Fan s X := c.cone

abbrev partialProd.isLimit (c : LimitFan s X) : IsLimit (cone c) := c.isLimit

abbrev partialProd.fst (c : LimitFan s X) : partialProd c ⟶ B := (cone c).fst

abbrev partialProd.snd (c : LimitFan s X) : pullback (fst c) s ⟶ X := (cone c).snd

/-- If the partial product of `s` and `X` exists, then every pair of morphisms `f : W ⟶ B` and
`g : pullback f s ⟶ X` induces a morphism `W ⟶ partialProd s X`. -/
abbrev partialProd.lift {W} (c : LimitFan s X)
    (f : W ⟶ B) (g : pullback f s ⟶ X) : W ⟶ partialProd c :=
  (isLimit c).lift (Fan.mk f g)

@[reassoc, simp]
theorem partialProd.lift_fst {W} {c : LimitFan s X} (f : W ⟶ B) (g : pullback f s ⟶ X) :
    lift c f g ≫ fst c = f :=
  (isLimit c).fac_left (Fan.mk f g)

@[reassoc]
theorem partialProd.lift_snd {W} (c : LimitFan s X) (f : W ⟶ B) (g : pullback f s ⟶ X) :
    comparison (partialProd.lift c f g) ≫ snd c =
    (pullback.congrHom (partialProd.lift_fst f g) rfl).hom ≫ g := by
  conv_rhs => arg 2; exact ((isLimit c).fac_right (Fan.mk f g)).symm
  rw [← pullbackMap_comparison]
  rw [← Category.assoc]; congr 1
  ext <;> simp [pullbackMap]

-- theorem hom_lift (h : IsLimit t) {W : C} (m : W ⟶ t.pt) :
--     m = h.lift { pt := W, π := { app := fun b => m ≫ t.π.app b } } :=
--   h.uniq { pt := W, π := { app := fun b => m ≫ t.π.app b } } m fun _ => rfl

theorem partialProd.hom_ext {W : C} (c : LimitFan s X) {f g : W ⟶ partialProd c}
    (h₁ : f ≫ fst c = g ≫ fst c)
    (h₂ : comparison f ≫ snd c = (pullback.congrHom h₁ rfl).hom ≫ comparison g ≫ snd c) :
    f = g := by
  let f' : Fan s X := { pt := W, fst := f ≫ fst c, snd := comparison f ≫ snd c }
  cases c.isLimit.uniq f' g (by simp [h₁, f']) <| by
    refine .trans ?_ h₂.symm
    rw [← Category.assoc]; congr 1
    ext <;> simp [pullbackMap, comparison, f']
  exact c.isLimit.uniq f' f rfl rfl
