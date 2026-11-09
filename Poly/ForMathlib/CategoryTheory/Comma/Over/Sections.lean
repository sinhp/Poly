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
  · simp [sectionsMap, pullback.map]

@[simp]
lemma sectionsMap_comp {X X' X'' : Over I} (u : X ⟶ X') (v : X' ⟶ X'') :
    sectionsMap (u ≫ v) = sectionsMap u ≫ sectionsMap v := by
  unfold sectionsMap
  rw [pullback.map_comp]
  simp only [id_comp, Functor.map_comp, Over.comp_left]

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
  have hu : u.left ≫ X.hom = prod.fst := (Over.w u).trans (prod.lift_fst ..)
  calc
    fst I A = (prodIsoTensorObj I A).inv ≫ prod.fst := prodIsoTensorObj_inv_fst.symm
    _ = (prodIsoTensorObj I A).inv ≫ (u.left ≫ X.hom) :=
      congrArg (fun k : I ⨯ A ⟶ I => (prodIsoTensorObj I A).inv ≫ k) hu.symm
    _ = ((prodIsoTensorObj I A).inv ≫ u.left) ≫ X.hom := (Category.assoc _ _ _).symm

/-- The uncurrying operation `Hom A (section X) → Hom ((star I).obj A) X`. -/
def sectionsUncurry {X : Over I} {A : C} (v : A ⟶ (sections I).obj X) :
    (star I).obj A ⟶ X := by
  let v₂ : A ⟶ (I ⟹ X.left) := v ≫ pullback.snd ..
  have w : terminal.from A ≫ (curryId I) = v₂ ≫ (ihom I).map X.hom := by
    rw [IsTerminal.hom_ext terminalIsTerminal (terminal.from A ) (v ≫ (pullback.fst ..))]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => v ≫ k)
        (pullback.condition (f := curryId I) (g := (ihom I).map X.hom))).trans
          (Category.assoc _ _ _).symm)
  dsimp [curryId] at w
  have w' := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft I)
    (adj := ihom.adjunction I) _ _ _ _ w
  simp [MonoidalClosed.curry] at w'
  refine Over.homMk ((prodIsoTensorObj I A).hom ≫ MonoidalClosed.uncurry v₂) ?_
  · dsimp [MonoidalClosed.uncurry] at *
    change ((prodIsoTensorObj I A).hom ≫ ((ihom.adjunction I).homEquiv A X.left).symm v₂) ≫
      X.hom = prod.lift prod.fst (𝟙 (I ⨯ A)) ≫ prod.fst
    rw [Category.assoc, ← w', prodIsoTensorObj_hom_fst, prod.lift_fst]

private theorem sectionsCurry_snd {X : Over I} {A : C} (u : (star I).obj A ⟶ X) :
    sectionsCurry u ≫ pullback.snd (curryId I) ((ihom I).map X.hom) =
      MonoidalClosed.curry ((prodIsoTensorObj I A).inv ≫ u.left) :=
  pullback.lift_snd ..

private theorem sectionsMap_snd {X X' : Over I} (u : X ⟶ X') :
    sectionsMap u ≫ pullback.snd (curryId I) ((ihom I).map X'.hom) =
      pullback.snd (curryId I) ((ihom I).map X.hom) ≫ (ihom I).map u.left :=
  pullback.lift_snd ..

@[simp]
theorem sections_curry_uncurry {X : Over I} {A : C} {v : A ⟶ (sections I).obj X} :
    sectionsCurry (sectionsUncurry v) = v := by
  apply pullback.hom_ext
  · exact terminalIsTerminal.hom_ext _ _
  · calc
      sectionsCurry (sectionsUncurry v) ≫ pullback.snd _ _ =
          MonoidalClosed.curry ((prodIsoTensorObj I A).inv ≫ (sectionsUncurry v).left) :=
        sectionsCurry_snd _
      _ = MonoidalClosed.curry ((prodIsoTensorObj I A).inv ≫ (prodIsoTensorObj I A).hom ≫
          MonoidalClosed.uncurry (v ≫ pullback.snd _ _)) := rfl
      _ = v ≫ pullback.snd _ _ :=
        (congrArg MonoidalClosed.curry (Iso.inv_hom_id_assoc _ _)).trans
          (MonoidalClosed.curry_uncurry _)

@[simp]
theorem sections_uncurry_curry {X : Over I} {A : C} {u : (star I).obj A ⟶ X} :
    sectionsUncurry (sectionsCurry u) = u := by
  apply Over.OverMorphism.ext
  exact (congrArg (fun k => (prodIsoTensorObj I A).hom ≫ MonoidalClosed.uncurry k)
    (sectionsCurry_snd u)).trans
      ((congrArg (fun k => (prodIsoTensorObj I A).hom ≫ k)
        (MonoidalClosed.uncurry_curry _)).trans (Iso.hom_inv_id_assoc _ _))

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
    let v₂ : A ⟶ I ⟹ X.left := v ≫ pullback.snd _ _
    have h : (prodIsoTensorObj I A').hom ≫ MonoidalClosed.uncurry (g ≫ v₂) =
        prod.map (𝟙 I) g ≫ (prodIsoTensorObj I A).hom ≫ MonoidalClosed.uncurry v₂ := by
      rw [MonoidalClosed.uncurry_natural_left, ← Category.assoc, ← id_tensorHom,
        ← prodMap_comp_prodIsoTensorObj_hom, Category.assoc]
    apply Over.OverMorphism.ext
    exact (congrArg (fun k => (prodIsoTensorObj I A').hom ≫ MonoidalClosed.uncurry k)
      (Category.assoc g v (pullback.snd _ _))).trans h
  homEquiv_naturality_right := by
    intro A X' X u g
    apply pullback.hom_ext (IsTerminal.hom_ext terminalIsTerminal _ _)
    calc
      sectionsCurry (u ≫ g) ≫ pullback.snd _ _ =
          MonoidalClosed.curry ((prodIsoTensorObj I A).inv ≫ (u ≫ g).left) :=
        sectionsCurry_snd _
      _ = MonoidalClosed.curry (((prodIsoTensorObj I A).inv ≫ u.left) ≫ g.left) :=
        congrArg MonoidalClosed.curry (Category.assoc _ _ _).symm
      _ = MonoidalClosed.curry ((prodIsoTensorObj I A).inv ≫ u.left) ≫ (ihom I).map g.left :=
        MonoidalClosed.curry_natural_right _ _
      _ = (sectionsCurry u ≫ pullback.snd _ _) ≫ (ihom I).map g.left :=
        congrArg (fun k => k ≫ (ihom I).map g.left) (sectionsCurry_snd u).symm
      _ = sectionsCurry u ≫ (pullback.snd _ _ ≫ (ihom I).map g.left) := Category.assoc _ _ _
      _ = sectionsCurry u ≫ (sectionsMap g ≫ pullback.snd _ _) :=
        congrArg (fun k => sectionsCurry u ≫ k) (sectionsMap_snd g).symm
      _ = (sectionsCurry u ≫ sectionsMap g) ≫ pullback.snd _ _ := (Category.assoc _ _ _).symm

variable (I)

/-- The adjunction between the star functor and the sections functor. -/
@[simps! unit_app counit_app]
def starSectionsAdj : star I ⊣ sections I :=
  .mkOfHomEquiv coreHomEquiv

end Over

end CategoryTheory
