/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Monad.Products
import Poly.ForMathlib.CategoryTheory.Comma.Over.Basic
import Poly.ForMathlib.CategoryTheory.NatTrans
import Poly.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits Comonad MonoidalCategory CartesianMonoidalCategory

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts

variable {C : Type u₁} [Category.{v₁} C]

namespace Over

theorem isCartesian_mapPullbackAdj_counit [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    NatTrans.IsCartesian (Over.mapPullbackAdj f).counit := by
  intro A B U
  apply IsPullback.of_right
    (h₁₂ := Over.homMk (V := Over.mk f) (pullback.snd B.hom f) <| by simp)
    (v₁₃ := Over.mkIdTerminal.from _)
    (h₂₂ := Over.mkIdTerminal.from _)
  case p =>
    ext
    simp
    exact pullback.lift_fst ..
  . apply (Over.forget Y).reflect_isPullback
    convert (IsPullback.of_hasPullback A.hom f).flip using 1 <;> simp
    exact pullback.lift_snd ..
  . apply (Over.forget Y).reflect_isPullback
    convert (IsPullback.of_hasPullback B.hom f).flip using 1 <;> simp

/-- The reindexing of `Z : Over X` along `Y : Over X`, defined by pulling back `Z` along
`Y.hom : Y.left ⟶ X`. -/
abbrev Reindex [HasPullbacks C] {X : C} (Y : Over X) (Z : Over X) : Over Y.left :=
  (Over.pullback Y.hom).obj Z

namespace Reindex

variable [HasPullbacks C] {X : C}

lemma hom {Y : Over X} {Z : Over X} :
    (Reindex Y Z).hom = pullback.snd Z.hom Y.hom := rfl

/-- `Reindex` is symmetric in its first and second arguments up to an isomorphism. -/
def symmetryObjIso (Y Z : Over X) :
    (Reindex Y Z).left ≅ (Reindex Z Y).left := pullbackSymmetry _ _

/-- The reindexed sum of `Z` along `Y` is isomorphic to the reindexed sum of `Y` along `Z` in the
category `Over X`. -/
@[simps!]
def sigmaSymmetryIso (Y Z : Over X) :
  Sigma Y (Reindex Y Z) ≅ Sigma Z (Reindex Z Y) := by
  apply Over.isoMk _ _
  · exact pullbackSymmetry ..
  · simp [pullback.condition]

lemma symmetry_hom {Y Z : Over X} :
    (pullback.snd Z.hom Y.hom) ≫ Y.hom =
    (pullbackSymmetry _ _).hom ≫ (pullback.snd Y.hom Z.hom) ≫ Z.hom  := by
  simp [← pullback.condition]

/-- The first projection out of the reindexed sigma object. -/
def fstProj (Y Z : Over X) : Sigma Y (Reindex Y Z) ⟶ Y :=
  Over.homMk (pullback.snd Z.hom Y.hom) (by simp)

lemma fstProj_sigma_fst (Y Z : Over X) : fstProj Y Z = Sigma.fst (Reindex Y Z) := rfl

/-- The second projection out of the reindexed sigma object. -/
def sndProj (Y Z : Over X) : Sigma Y (Reindex Y Z) ⟶ Z :=
  Over.homMk (pullback.fst Z.hom Y.hom) (by simp [pullback.condition])

/-- The notation for the first projection of the reindexed sigma object. -/
scoped notation " π_ " => fstProj

/-- The notation for the second projection of the reindexed sigma object. -/
scoped notation " μ_ " => sndProj

lemma counit_app_pullback_fst {Y Z : Over X} :
    μ_ Y Z = (mapPullbackAdj Y.hom).counit.app Z := by
  simp [mapPullbackAdj_counit_app]
  rfl

lemma counit_app_pullback_snd {Y Z : Over X} :
    π_ Y Z = (sigmaSymmetryIso Y Z).hom ≫ (mapPullbackAdj Z.hom).counit.app Y := by
  aesop

@[simp]
lemma counit_app_pullback_snd_eq_homMk {Y Z : Over X} :
    π_ Y Z = (homMk (Reindex Y Z).hom : (Sigma Y (Reindex Y Z)) ⟶ Y) :=
  OverMorphism.ext (by aesop)

end Reindex

section BinaryProduct

open Over.Sigma Reindex

variable [HasFiniteWidePullbacks C] {X : C}

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
def isBinaryProductSigmaReindex (Y Z : Over X) :
    IsLimit <| BinaryFan.mk (P:= Sigma Y (Reindex Y Z)) (π_ Y Z) (μ_ Y Z) := by
  refine IsLimit.mk (?lift) ?fac ?uniq
  · intro s
    fapply Over.homMk
    · exact pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop)
    · change pullback.lift _ _ _ ≫ pullback.snd Z.hom Y.hom ≫ Y.hom = s.pt.hom
      rw [pullback.lift_snd_assoc]
      exact Over.w _
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext
    · exact pullback.lift_snd ..
    · exact pullback.lift_fst ..
  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change m.left ≫ pullback.fst Z.hom Y.hom = pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst]
      exact congr_arg CommaMorphism.left (h ⟨ .right⟩)
    · change m.left ≫ pullback.snd Z.hom Y.hom = pullback.lift _ _ _ ≫ pullback.snd _ _
      rw [pullback.lift_snd]
      exact congr_arg CommaMorphism.left (h ⟨ .left ⟩)

/-- The object `(Sigma Y) (Reindex Y Z)` is isomorphic to the binary product `Y × Z`
in `Over X`. -/
@[simps!]
def sigmaReindexIsoProd (Y Z : Over X) :
    (Sigma Y) (Reindex Y Z) ≅ Limits.prod Y Z := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProductSigmaReindex Y Z) (prodIsProd Y Z)

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the `(map f).obj ((pullback f).obj Y)`
is isomorphic to the binary product of `(Over.mk f)` and `Y`. -/
def sigmaReindexIsoProdMk {Y : C} (f : Y ⟶ X) (Z : Over X) :
    (map f).obj ((pullback f).obj Z) ≅ Limits.prod (Over.mk f) Z :=
  sigmaReindexIsoProd (Over.mk f) _

lemma sigmaReindexIsoProd_hom_comp_fst {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ fst Y Z = (π_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.left⟩

lemma sigmaReindexIsoProd_hom_comp_snd {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ snd Y Z = (μ_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.right⟩

end BinaryProduct

end Over

section TensorLeft

open Over CategoryTheory.Functor

variable [HasFiniteWidePullbacks C] {X : C}

/-- The pull-push composition `(Over.pullback Y.hom) ⋙ (Over.map Y.hom)` is naturally isomorphic
to the left tensor product functor `Y × _` in `Over X`-/
def Over.sigmaReindexNatIsoTensorLeft (Y : Over X) :
    (pullback Y.hom) ⋙ (map Y.hom) ≅ tensorLeft Y := by
  fapply NatIso.ofComponents
  · intro Z
    exact sigmaReindexIsoProd Y Z
  · intro Z Z' f
    have hm : Y ◁ f = Limits.prod.map (𝟙 Y) f := by
      ext1
      · simp only [whiskerLeft_fst]
        exact (Category.comp_id _).symm.trans (Limits.prod.map_fst (𝟙 Y) f).symm
      · simp only [whiskerLeft_snd]
        exact (Limits.prod.map_snd (𝟙 Y) f).symm
    change (map Y.hom).map ((pullback Y.hom).map f) ≫ (sigmaReindexIsoProd Y Z').hom =
      (sigmaReindexIsoProd Y Z).hom ≫ Y ◁ f
    rw [hm]
    change (map Y.hom).map ((pullback Y.hom).map f) ≫ (sigmaReindexIsoProd Y Z').hom =
      (sigmaReindexIsoProd Y Z).hom ≫ Limits.prod.map (𝟙 Y) f
    have hf (Z : Over X) : (sigmaReindexIsoProd Y Z).hom ≫ Limits.prod.fst =
        Reindex.fstProj Y Z := sigmaReindexIsoProd_hom_comp_fst
    have hs (Z : Over X) : (sigmaReindexIsoProd Y Z).hom ≫ Limits.prod.snd =
        Reindex.sndProj Y Z := sigmaReindexIsoProd_hom_comp_snd
    apply Limits.prod.hom_ext
    · simp only [assoc, hf, Limits.prod.map_fst, Category.comp_id]
      apply Over.OverMorphism.ext
      simp
      exact pullback.lift_snd ..
    · rw [assoc, hs, assoc, Limits.prod.map_snd, ← assoc, hs]
      apply Over.OverMorphism.ext
      simp [Reindex.sndProj]
      exact pullback.lift_fst ..

lemma Over.sigmaReindexNatIsoTensorLeft_hom_app
    {Y : Over X} (Z : Over X) :
    (Over.sigmaReindexNatIsoTensorLeft Y).hom.app Z = (sigmaReindexIsoProd Y Z).hom := by
  aesop

end TensorLeft

variable (C)

/-- The functor from `C` to `Over (⊤_ C)` which sends `X : C` to `terminal.from X`. -/
@[simps! obj_left obj_hom map_left]
def Functor.toOverTerminal [HasTerminal C] : C ⥤ Over (⊤_ C) where
  obj X := Over.mk (terminal.from X)
  map {X Y} f := Over.homMk f

/-- The slice category over the terminal object is equivalent to the original category. -/
def equivOverTerminal [HasTerminal C] : Over (⊤_ C) ≌ C :=
  CategoryTheory.Equivalence.mk (Over.forget _) (Functor.toOverTerminal C)
    (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _)) (by
      intro X Y f
      ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      simp))
    (NatIso.ofComponents (fun X => Iso.refl _) (by
      intro X Y f
      change f ≫ 𝟙 _ = 𝟙 _ ≫ f
      simp))

namespace Over

open CartesianMonoidalCategory

variable {C}

private theorem star_obj_hom_eq_fst [HasBinaryProducts C] (I X : C) :
    ((star I).obj X).hom = prod.fst :=
  prod.lift_fst ..

lemma star_map [HasBinaryProducts C] {X : C} {Y Z : C} (f : Y ⟶ Z) :
    (star X).map f = Over.homMk (prod.map (𝟙 X) f) (by
      change prod.map (𝟙 X) f ≫ ((star X).obj Z).hom = ((star X).obj Y).hom
      rw [star_obj_hom_eq_fst, star_obj_hom_eq_fst]
      exact (prod.map_fst _ _).trans (Category.comp_id _)) := by
  apply Over.OverMorphism.ext
  exact star_map_left X f

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C]  (X : C) : (forget X).IsLeftAdjoint  :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts

lemma whiskerLeftProdMapId [HasFiniteLimits C] {X : C} {A A' : C} {g : A ⟶ A'} :
    X ◁ g = prod.map (𝟙 X) g := by
  ext
  · simp only [whiskerLeft_fst]
    exact (Category.comp_id _).symm.trans (prod.map_fst (𝟙 X) g).symm
  · simp only [whiskerLeft_snd]
    exact (prod.map_snd (𝟙 X) g).symm

def starForgetIsoTensorLeft [HasFiniteLimits C] (X : C) :
    (Over.star X ⋙ forget X) ≅ tensorLeft X := by
  fapply NatIso.ofComponents
  · intro Z
    exact Iso.refl _
  · intro Z Z' f
    change prod.map (𝟙 X) f ≫ 𝟙 _ = 𝟙 _ ≫ X ◁ f
    rw [whiskerLeftProdMapId]
    change prod.map (𝟙 X) f ≫ 𝟙 (X ⨯ Z') = 𝟙 (X ⨯ Z) ≫ prod.map (𝟙 X) f
    simp

namespace forgetAdjStar

variable [HasBinaryProducts C]

@[simp]
theorem unit_app {I : C} (X : Over I): (forgetAdjStar I).unit.app X =
    Over.homMk (prod.lift X.hom (𝟙 X.left)) (by
      change prod.lift X.hom (𝟙 X.left) ≫ ((star I).obj X.left).hom = X.hom
      rw [star_obj_hom_eq_fst]
      exact prod.lift_fst ..) := by
  apply Over.OverMorphism.ext
  exact Over.forgetAdjStar_unit_app_left I X

@[simp]
theorem counit_app {I : C} (X : C) :
    ((forgetAdjStar I).counit.app X) = prod.snd := by
  exact Over.forgetAdjStar_counit_app I X

@[simp]
theorem homEquiv_homMk_lift {I : C} {X : Over I} {A : C} {f : X.left ⟶ A} :
    ((forgetAdjStar I).homEquiv X A) f =
    Over.homMk (prod.lift X.hom f) (by
      rw [star_obj_hom_eq_fst]
      exact prod.lift_fst ..) := by
  rw [Adjunction.homEquiv_unit, unit_app]
  apply Over.OverMorphism.ext
  change prod.lift _ (𝟙 _) ≫ prod.map (𝟙 I) f = prod.lift _ f
  rw [prod.lift_map]
  simp

@[simp]
theorem homEquiv_left_lift {I : C} {X : Over I} {A : C} {f : X.left ⟶ A} :
    (((forgetAdjStar I).homEquiv X A) f).left =
    prod.lift X.hom f := by
  simp_rw [homEquiv_homMk_lift]
  rfl

theorem homEquiv_lift' {X I : C} {u : X ⟶ I} {A : C} {f : X ⟶ A} :
    ((forgetAdjStar I).homEquiv (.mk u) A) f =
    Over.homMk (prod.lift u f) (by
      rw [star_obj_hom_eq_fst]
      exact prod.lift_fst ..) := by
  rw [Adjunction.homEquiv_unit, unit_app]
  apply Over.OverMorphism.ext
  change prod.lift _ (𝟙 _) ≫ prod.map (𝟙 I) f = prod.lift _ f
  rw [prod.lift_map]
  simp

@[simp]
theorem homEquiv_symm_left_snd {I : C} {X : Over I} {A : C} {f : X ⟶ (Over.star I).obj A} :
     ((forgetAdjStar I).homEquiv X A).symm f = f.left ≫ prod.snd := by
   rw [Adjunction.homEquiv_counit, counit_app]
   simp

end forgetAdjStar

end Over

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A right adjoint to the forward functor of an equivalence is naturally isomorphic to the
inverse functor of the equivalence. -/
def equivalenceRightAdjointIsoInverse (e : D ≌ C) (R : C ⥤ D) (adj : e.functor ⊣ R) :
    R ≅ e.inverse :=
  conjugateIsoEquiv adj (e.toAdjunction) (Iso.refl _)

end Adjunction

namespace Over

/-- `star (⊤_ C) : C ⥤ Over (⊤_ C)` is naturally isomorphic to `Functor.toOverTerminal C`. -/
def starIsoToOverTerminal [HasTerminal C] [HasBinaryProducts C] :
    star (⊤_ C) ≅ Functor.toOverTerminal C := by
  apply Adjunction.equivalenceRightAdjointIsoInverse
    (equivOverTerminal C) (star (⊤_ C)) (forgetAdjStar (⊤_ C))

variable {C}

/-- The functor `Over.pullback f : Over Y ⥤ Over X` is naturally isomorphic to
`Over.star : Over Y ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over X`. -/
def starIteratedSliceForwardIsoPullback [HasFiniteWidePullbacks C]
    {X Y : C} (f : X ⟶ Y) : star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjStar _))
  (mapPullbackAdj f) (eqToIso (iteratedSliceBackward_forget (Over.mk f)))

end Over

end CategoryTheory
