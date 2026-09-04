/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Poly.ForMathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The section functor as a right adjoint to the star functor

We show that if `C` is cartesian closed then `star I : C ⥤ Over I`
has a right adjoint `sectionsFunctor` whose object part is the object of sections
of `X` over `I`.


-/

-- Lean 4.34 tightened the transparency `simp`/`rw` use when matching, which breaks goals
-- stated through reducible wrappers (`pullback.lift`/`pullback.fst`, `Over.Hom`).
-- Mathlib sets the same option throughout its own `Over`/pullback files.
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory CartesianClosed Adjunction Over

variable {C : Type u₁} [Category.{v₁} C]

attribute [local instance] hasBinaryProducts_of_hasTerminal_and_pullbacks
attribute [local instance] hasFiniteProducts_of_has_binary_and_terminal
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts

section

variable [HasFiniteProducts C]

/-- The isomorphism between `X ⨯ Y` and `X ⊗ Y` for objects `X` and `Y` in `C`.
This is tautological by the definition of the cartesian monoidal structure on `C`.
This isomorphism provides an interface between `prod.fst` and `CartesianMonoidalCategory.fst`
as well as between `prod.map` and `tensorHom`. -/
def prodIsoTensorObj (X Y : C) : X ⨯ Y ≅ X ⊗ Y := Iso.refl _

@[reassoc (attr := simp)]
theorem prodIsoTensorObj_inv_fst {X Y : C} :
    (prodIsoTensorObj X Y).inv ≫ prod.fst = fst X Y :=
  Category.id_comp _

@[reassoc (attr := simp)]
theorem prodIsoTensorObj_inv_snd {X Y : C} :
    (prodIsoTensorObj X Y).inv ≫ prod.snd = snd X Y :=
  Category.id_comp _

@[reassoc (attr := simp)]
theorem prodIsoTensorObj_hom_fst {X Y : C} :
    (prodIsoTensorObj X Y).hom ≫ fst X Y = prod.fst :=
  Category.id_comp _

@[reassoc (attr := simp)]
theorem prodIsoTensorObj_hom_snd {X Y : C} :
    (prodIsoTensorObj X Y).hom ≫ snd X Y = prod.snd :=
  Category.id_comp _

@[reassoc (attr := simp)]
theorem prodMap_comp_prodIsoTensorObj_hom {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prodIsoTensorObj _ _).hom = (prodIsoTensorObj _ _).hom ≫ (f ⊗ₘ g) := by
  apply hom_ext <;> simp

end

variable [HasTerminal C] [HasPullbacks C]

variable (I : C) [Closed I]

/-- The first leg of a cospan constructing a pullback diagram in `C` used to define `sections` . -/
def curryId : ⊤_ C ⟶ (I ⟹ I) :=
  MonoidalClosed.curry (fst I (⊤_ C))

variable {I}

namespace Over

/-- Given `X : Over I`, `sectionsObj X` is the object of sections of `X` defined by the following
pullback diagram:

```
 sections X -->  I ⟹ X
   |               |
   |               |
   v               v
  ⊤_ C    ---->  I ⟹ I
```-/
abbrev sectionsObj (X : Over I) : C :=
  Limits.pullback (curryId I) ((ihom I).map X.hom)

/-- The functoriality of `sectionsObj`. -/
def sectionsMap {X X' : Over I} (u : X ⟶ X') :
    sectionsObj X ⟶ sectionsObj X' := by
  fapply pullback.map
  · exact 𝟙 _
  · exact (ihom I).map u.left
  · exact 𝟙 _
  · simp only [comp_id, id_comp]
  · simp only [comp_id, ← Functor.map_comp, w]

@[simp]
lemma sectionsMap_id {X : Over I} : sectionsMap (𝟙 X) = 𝟙 _ := by
  apply pullback.hom_ext
  · aesop
  · simp [sectionsMap]

@[simp]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  apply pullback.hom_ext
  · aesop
  · simp [sectionsMap]

variable (I)

/-- The functor mapping an object `X` in `C` to the object of sections of `X` over `I`. -/
@[simps]
def sections :
    Over I ⥤ C where
  obj X := sectionsObj X
  map u := sectionsMap u

variable {I}

/-- An auxiliary morphism used to define the currying of a morphism in `Over I` to a morphism
in `C`. See `sectionsCurry`. -/
def sectionsCurryAux {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    A ⟶ (I ⟹ X.left) :=
  MonoidalClosed.curry (u.left)

/-- The currying operation `Hom ((star I).obj A) X → Hom A (I ⟹ X.left)`. -/
def sectionsCurry {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    A ⟶ (sections I).obj X := by
  apply pullback.lift (terminal.from A)
    (MonoidalClosed.curry ((prodIsoTensorObj _ _).inv ≫ u.left))
    (MonoidalClosed.uncurry_injective _)
  rw [MonoidalClosed.uncurry_natural_left]
  simp [curryId, MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_curry]

/-- The uncurrying operation `Hom A (section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (star I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd ..
  have w : terminal.from A ≫ (curryId I) = v₂ ≫ (ihom I).map X.hom := by
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
    simp [v₂, pullback.condition]
  dsimp [curryId] at w
  have w' := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft I)
    (adj := ihom.adjunction I) _ _ _ _ w
  simp [MonoidalClosed.curry] at w'
  refine Over.homMk ((prodIsoTensorObj I A).hom ≫ MonoidalClosed.uncurry v₂) ?_
  · dsimp [MonoidalClosed.uncurry] at *
    rw [Category.assoc, ← w']
    simp [star_obj_hom]

@[simp]
theorem sections_curry_uncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  dsimp [sectionsCurry, sectionsUncurry]
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd _ _
  apply pullback.hom_ext
  · simp
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
  · simp

@[simp]
theorem sections_uncurry_curry {X : Over I} {A : C} {u : (star I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  dsimp [sectionsCurry, sectionsUncurry]
  ext
  simp

/-- An auxiliary definition which is used to define the adjunction between the star functor
and the sections functor. See starSectionsAdjunction`. -/
def coreHomEquiv : CoreHomEquiv (star I) (sections I) where
  homEquiv A X := {
    toFun := sectionsCurry
    invFun := sectionsUncurry
    left_inv {u} := sections_uncurry_curry
    right_inv {v} := sections_curry_uncurry
  }
  homEquiv_naturality_left_symm := by
    intro A' A X g v
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    simp only [star_map]
    rw [← Over.homMk_comp]  -- note: in a newer version of mathlib this is `Over.homMk_eta`
    congr 1
    simp [MonoidalClosed.uncurry_natural_left]
  homEquiv_naturality_right := by
    intro A X' X u g
    dsimp [sectionsCurry, sectionsUncurry, curryId]
    apply pullback.hom_ext (IsTerminal.hom_ext terminalIsTerminal _ _)
    simp [sectionsMap, curryId]
    rw [← MonoidalClosed.curry_natural_right, Category.assoc]

variable (I)

/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def starSectionsAdj : star I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquiv

end Over

end CategoryTheory
