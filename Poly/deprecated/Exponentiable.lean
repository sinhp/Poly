/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian
-- import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Tactic.ApplyFun
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

-- import Poly.Basic -- some isos in here
-- import Poly.TempMates

/-!
# Expontentiable morphisms in a category

We say that a morphism `f : X ⟶ Y` in a category `C` has pushforward if there is
a right adjoint to the base-change functor along `f`.
The type `Pushforward f` is a structure containing `functor : Over X ⥤ Over Y` and
a witness `adj : baseChange f ⊣ functor`.

We prove that if a morphism `f : X ⟶ Y` has pushforwards then `f` is exponentiable in the
slice category `Over Y`.
In particular, for a morphism `g : X ⟶ I` the exponential `f^* g` is the functor composition
`(baseChange g) ⋙ (Over.map g)`.

## Notation

We provide the following notations:

* `Π_ f` is the functor `pushforward f : Over J ⥤ Over I`. As such, for an object
`X : Over J`, we have `Π_f X : Over I`

### Diagrams

```

                      .fst
        pullback p f ------> X
          |                  |
          |                  | p
    .snd  |                  |
          v                  v
          J   ---------->    I
                    f
```

Using the notation above, we have
* `hom_eq_pullback_snd` proves that `(Δ_ f Over.mk p).hom` is `pullback.snd`
* `natIsoTensorLeft` proves that `Δ_ f` ⋙ `Σ_ f` is isomorphic to the product functor `f × _` in the
slice category `Over I`. See
We shall prove that

-/

noncomputable section

open CategoryTheory Category MonoidalCategory Limits Functor Adjunction IsConnected Over

namespace baseChange

variable {C : Type*} [Category C] [HasPullbacks C]

@[inherit_doc]
prefix:90 "Σ_ " => Over.map

@[inherit_doc]
prefix:90 "Σ_ " => Over.forget

@[inherit_doc]
prefix:90 "Δ_ " => baseChange

@[inherit_doc]
prefix:90 "Δ_ " => Over.star

example (I J X : C) (f : J ⟶ I) (p : X ⟶ I) :
    pullback p f ⟶ X := by
  exact pullback.fst


/-- For an arrow `f : J ⟶ I` and an object `X : Over I`, the base-change of `X` along `f` is
`pullback.snd`. -/
lemma hom_eq_pullback_snd {I J : C} (f : J ⟶ I) (X : Over I):
    ((Δ_ f).obj X).hom = pullback.snd := rfl

example {I : C} (f : J ⟶ I) (p : X ⟶ I) :
    ((Δ_ f).obj (Over.mk p)).hom = pullback.snd := rfl

/-- For objects `X` and `Y` in `Over I`, the base-change of `X` along `Y.hom` is
equal to `pullback.snd : pullback X.hom Y.hom ⟶ Y.left` -/
example {I : C} (X Y : Over I) :
    ((Δ_ Y.hom).obj X).hom = pullback.snd := rfl

-- /-- The base-change of `Y` along `X` is `pullback.snd (f:= Y.hom) (g:= X.hom)` -/
-- lemma hom_eq_pullback_snd' [HasPullbacks C] {I : C} (X Y : Over I) :
--     ((Δ_ X.hom).obj Y).hom = pullback.snd := by
--   rfl


-- lemma baseChang_pullback_snd' [HasPullbacks C] {I : C} (X Y : Over I) :
--     (Δ_ Y.hom |>.obj X).hom =  pullback.snd := by
--   rfl

-- @[ext]
-- lemma Over.obj_ext {X Y : Over I}
--   (h : X.left = Y.left)
--   (h' : X.hom = h ▸ Y.hom) : X = Y := by
--   obtain ⟨ x, ⟨⟩, f ⟩ := X
--   obtain ⟨ y, ⟨⟩, g ⟩ := Y
--   cases h
--   cases h'
--   rfl

lemma Over.star_eq_Over.mk_prod_fst [HasBinaryProducts C] [HasTerminal C] (I : C) (X : C) :
    (Over.star I).obj X = Over.mk (prod.fst : I ⨯ X ⟶ I) := by
  simp [Over.star, Over.mk]

/-- The base-change along `terminal.from` ER: Changed statement from an equality to an isomorphism.
Proof of commutativity is stuck because of the rewrite. Perhaps I can do this another way? -/
def terminal_from [HasBinaryProducts C] [HasTerminal C] (I : C) (X : Over (⊤_ C)) :
    (Δ_ (terminal.from I)).obj X ≅ (Over.star I).obj (X.left) := by
  unfold baseChange Over.star
  fapply Over.isoMk
  · simp only [id_obj, const_obj_obj, mk_left, comp_obj, coalgebraToOver_obj, Comonad.cofree_obj_A,
    prodComonad_obj, Comonad.cofree_obj_a, prodComonad_δ_app, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_left, BinaryFan.mk_fst]
    have := prodIsoPullback I X.left
    have lem := terminal.hom_ext X.hom (terminal.from X.left)
    rw [← lem] at this
    exact pullbackSymmetry X.hom (terminal.from I) ≪≫ this.symm
  · simp; sorry

-- Over.star -- Δ_ (prod.snd (X:= B) (Y:= E))

-- example {f : X ⟶ Z} [inst : HasPullback f (𝟙 Z)] :
--   @pullback.snd _ _ X Z Z f (𝟙 Z) ≅ f := by
--   sorry

-- example {f : X ⟶ Z} [inst : HasPullback (𝟙 Z) f] :
--   @pullback.snd _ _ X X Z (𝟙 Z) f ≅ f := by
--   sorry

def isLimitPullbackConeId {I J : C} (f : J ⟶ I) :
    IsLimit (PullbackCone.mk (W := J) (fst:= 𝟙 J) (snd := f) (eq:= by simp) :
      PullbackCone f (𝟙 I)) := by
  apply PullbackCone.IsLimit.mk
  · aesop
  · intro s
    rw [← comp_id s.snd]
    exact s.condition
  · aesop_cat


-- ER: it's a mate:
def id (I : C) : Δ_ (𝟙 I) ≅ 𝟭 _ := by
  refine conjugateIsoEquiv (mapAdjunction (𝟙 I)) Adjunction.id (mapId I).symm

namespace overMap

variable [HasFiniteWidePullbacks C] {I : C}

attribute [local instance] monoidalOfHasFiniteProducts

@[simps!]
def swapIso {X Y : Over I} :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ≅ (Σ_ Y.hom).obj ((Δ_ Y.hom).obj X)  := by
  fapply Over.isoMk
  · apply pullbackSymmetry
  · simp [pullback.condition]

@[simp]
lemma swap_eq_hom {X Y : Over I} :
    ((Σ_ X.hom).obj ((Δ_ X.hom).obj Y)).hom =
      (pullbackSymmetry _ _).hom ≫ ((Σ_ Y.hom).obj ((Δ_ Y.hom).obj X)).hom  := by
  simp only [const_obj_obj, id_obj, map_obj_left, baseChange_obj_left, map_obj_hom,
    baseChange_obj_hom, pullbackSymmetry_hom_comp_snd_assoc]
  exact pullback.condition.symm

/-- The base-change of `Y` along `X` is `pullback.fst (f:= Y.hom) (g:= X.hom)` -/
@[simp]
def projLeft (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ X :=
  Over.homMk (pullback.snd) (by simp [baseChange.hom_eq_pullback_snd])

@[simp]
def projRight (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ⟶ Y :=
  Over.homMk (pullback.fst) (by simp [pullback.condition])

lemma projRight_counit {X Y : Over I} :
    projRight X Y = (Over.mapAdjunction X.hom).counit.app Y := by
  simp_all only [const_obj_obj, id_obj, mapAdjunction_counit_app]
  rfl

local notation "π_ "   => projLeft

local notation "μ_ "   => projRight

-- pullbackCompositionIsBinaryProduct
/-- Compsotion after base change gives the binary product in slices.-/
def isBinaryProduct (X Y : Over I) :
    IsLimit (BinaryFan.mk (π_ X Y) (μ_ X Y)) := by
  fapply IsLimit.mk
  · intro s
    fapply Over.homMk
    apply pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop_cat)
    simp
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;> simp
  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [pullback.lift_fst, pullback.lift_snd]
    · apply congr_arg CommaMorphism.left (h ⟨ .right⟩)
    · apply congr_arg CommaMorphism.left (h ⟨ .left⟩)

/-- The object `(Σ_ X.hom) ((Δ_ X.hom) Y)` is isomorphic to the binary product `X × Y` in the slice
category. -/
@[simps!]
def isoProd (X Y : Over I) :
    (Σ_ X.hom).obj ((Δ_ X.hom).obj Y) ≅ Limits.prod X Y := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProduct X Y) (prodIsProd X Y)

def isoProdmk (f : J ⟶ I) (Y : Over I) :
    (Σ_ f).obj ((Δ_ f).obj Y) ≅ Limits.prod (Over.mk f) Y := by
  apply isoProd (Over.mk f) Y

@[simp]
lemma isoProd_comp_fst (X Y : Over I) :
    (isoProd X Y).hom ≫ prod.fst = (π_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct X Y) (Limits.prodIsProd X Y) ⟨.left⟩

@[simp]
lemma isoProdmk_comp_fst (f : J ⟶ I) (Y : Over I) :
    (isoProdmk f Y).hom ≫ prod.fst = (π_ (Over.mk f) Y) :=
  isoProd_comp_fst (Over.mk f) Y

@[simp]
lemma isoProd_comp_snd {X Y : Over I}  :
    (isoProd X Y).hom ≫ prod.snd = (μ_ X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isBinaryProduct X Y) (Limits.prodIsProd X Y) ⟨.right⟩

-- NatOverProdIso
/-- The functor composition `(baseChange X.hom) ⋙ (Over.map X.hom)` is naturally isomorphic
to the left tensor product functor `X × _` -/
def natIsoTensorLeft {I : C} (X : Over I) :
    (Δ_ X.hom) ⋙ (Σ_ X.hom) ≅ tensorLeft X := by
  fapply NatIso.ofComponents
  · intro Y
    apply isoProd
  · intro Y Z f
    simp
    ext1 <;> simp_rw [assoc]
    · simp_rw [prod.map_fst, comp_id]
      iterate rw [isoProd_comp_fst]
      ext
      simp
    · simp_rw [prod.map_snd]
      iterate rw [isoProd_comp_snd, ← assoc, isoProd_comp_snd]
      ext
      simp

def natIsoTensorLeftOverMk {I J : C} (f : J ⟶ I) :
    (Δ_ f) ⋙ (Σ_ f) ≅ tensorLeft (Over.mk f) := by
  apply natIsoTensorLeft (Over.mk f)

end overMap

end baseChange

open baseChange.overMap

variable {C : Type*} [Category C] [HasPullbacks C]

class CartesianExponentiable {X Y : C} (f : X ⟶ Y) where
  /-- A functor `C/X ⥤ C/Y` right adjoint to `f*`. -/
  functor : Over X ⥤ Over Y
  adj : baseChange f ⊣ functor := by infer_instance

@[inherit_doc]
prefix:90 "Π_ " => CartesianExponentiable.functor

namespace CartesianExponentiable

variable {C : Type*} [Category C] [HasPullbacks C]

attribute [local instance] monoidalOfHasFiniteProducts

/-- The identity morphisms `𝟙` are exponentiable. -/
instance id {I : C} : CartesianExponentiable (𝟙 I) where
  functor := 𝟭 (Over I)
  adj := by
    fapply ofNatIsoLeft (F:= 𝟭 _) ?adj (baseChange.id I).symm
    exact Adjunction.id

instance comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [fexp : CartesianExponentiable f] [gexp : CartesianExponentiable g] :
    CartesianExponentiable (f ≫ g) where
  functor := (Π_ f) ⋙ (Π_ g)
  adj := ofNatIsoLeft (gexp.adj.comp fexp.adj) (pullbackCompIso f g).symm

/-- The conjugate isomorphism between pushforward functors. -/
def pushforwardCompIso [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [fexp : CartesianExponentiable f] [gexp : CartesianExponentiable g] :
    fexp.functor ⋙ gexp.functor ≅ (comp f g).functor :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) ((comp f g).adj) (pullbackCompIso f g)

/-- An arrow with a pushforward is exponentiable in the slice category. -/
instance exponentiableOverMk [HasFiniteWidePullbacks C] {I : C} (f : X ⟶ I)
    [CartesianExponentiable f] : Exponentiable (Over.mk f) where
  rightAdj :=  (Δ_ f) ⋙ (Π_ f)
  adj := by
    fapply ofNatIsoLeft
    fapply (Δ_ f) ⋙ (Σ_ f)
    · apply Adjunction.comp
      · exact CartesianExponentiable.adj
      · apply Over.mapAdjunction
    · exact natIsoTensorLeftOverMk f

end CartesianExponentiable
