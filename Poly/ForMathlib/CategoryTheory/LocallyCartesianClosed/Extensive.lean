import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Exponentiable maps and finite coproducts

This file proves that pulling back along the coprojections of a binary coproduct is jointly
fully faithful in a finitary extensive category. It follows that a coproduct of exponentiable
maps is exponentiable.

## Main results

* `isLeftAdjoint_of_jointly_fullyFaithful`: construct a right adjoint from jointly fully faithful
  functors and right adjoints to their composites.
* `pullback_inl_inr_bijective`: pulling back along coprojections is jointly fully faithful.
* `coprod_desc_exponentiable`: a coproduct of exponentiable maps is exponentiable.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe u v

section General

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]

/-- If `E₁, E₂` are jointly fully faithful and `L ⋙ E₁`, `L ⋙ E₂` are left adjoints
(and the source has binary products), then `L` is a left adjoint: its right adjoint
sends `Y` to `R₁ (E₁ Y) ⨯ R₂ (E₂ Y)`. -/
theorem isLeftAdjoint_of_jointly_fullyFaithful [HasBinaryProducts C]
    (L : C ⥤ D) (E₁ : D ⥤ D₁) (E₂ : D ⥤ D₂)
    (hE : ∀ {Y Y' : D}, Function.Bijective (fun φ : Y ⟶ Y' => (E₁.map φ, E₂.map φ)))
    [(L ⋙ E₁).IsLeftAdjoint] [(L ⋙ E₂).IsLeftAdjoint] : L.IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  ext Y
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  rw [Functor.rightAdjointObjIsDefined_iff]
  let adj₁ := Adjunction.ofIsLeftAdjoint (L ⋙ E₁)
  let adj₂ := Adjunction.ofIsLeftAdjoint (L ⋙ E₂)
  let e : ∀ X : C, (L.obj X ⟶ Y) ≃ (E₁.obj (L.obj X) ⟶ E₁.obj Y) × (E₂.obj (L.obj X) ⟶ E₂.obj Y) :=
    fun _ => Equiv.ofBijective _ hE
  have key : ∀ (X : C) (a : E₁.obj (L.obj X) ⟶ E₁.obj Y) (b : E₂.obj (L.obj X) ⟶ E₂.obj Y),
      E₁.map ((e X).symm (a, b)) = a ∧ E₂.map ((e X).symm (a, b)) = b :=
    fun X a b => Prod.mk.inj ((e X).apply_symm_apply (a, b))
  refine Functor.RepresentableBy.isRepresentable (Y :=
    (Functor.rightAdjoint (L ⋙ E₁)).obj (E₁.obj Y) ⨯
      (Functor.rightAdjoint (L ⋙ E₂)).obj (E₂.obj Y))
    { homEquiv := fun {X} =>
        { toFun := fun u => (e X).symm
            ((adj₁.homEquiv _ _).symm (u ≫ prod.fst), (adj₂.homEquiv _ _).symm (u ≫ prod.snd))
          invFun := fun φ => prod.lift (adj₁.homEquiv _ _ (E₁.map φ))
            (adj₂.homEquiv _ _ (E₂.map φ))
          left_inv := fun u => by
            apply prod.hom_ext
            · rw [prod.lift_fst, (key _ _ _).1, Equiv.apply_symm_apply]
            · rw [prod.lift_snd, (key _ _ _).2, Equiv.apply_symm_apply]
          right_inv := fun φ => by
            apply (e X).injective
            refine Prod.ext ?_ ?_
            · change E₁.map _ = E₁.map φ
              rw [(key _ _ _).1, prod.lift_fst, Equiv.symm_apply_apply]
            · change E₂.map _ = E₂.map φ
              rw [(key _ _ _).2, prod.lift_snd, Equiv.symm_apply_apply] }
      homEquiv_comp := fun {X X'} f u => by
        apply (e X).injective
        refine Prod.ext ?_ ?_
        · change E₁.map _ = E₁.map (L.map f ≫ _)
          dsimp only [Equiv.coe_fn_mk]
          rw [(key _ _ _).1, Functor.map_comp, (key _ _ _).1, Category.assoc]
          exact adj₁.homEquiv_naturality_left_symm f _
        · change E₂.map _ = E₂.map (L.map f ≫ _)
          dsimp only [Equiv.coe_fn_mk]
          rw [(key _ _ _).2, Functor.map_comp, (key _ _ _).2, Category.assoc]
          exact adj₂.homEquiv_naturality_left_symm f _ }

end General

section Extensive

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [FinitaryExtensive C]

/-- In an extensive category, an object over `A ⨿ B` is the coproduct of its pullbacks
along the two coprojections. -/
def isColimitPullbackCoprodInlInr {A B : C} (Y : Over (A ⨿ B)) :
    IsColimit (BinaryCofan.mk (pullback.fst Y.hom (coprod.inl : A ⟶ A ⨿ B))
      (pullback.fst Y.hom (coprod.inr : B ⟶ A ⨿ B))) :=
  (((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.van_kampen' _ (coprodIsCoprod A B))
    (BinaryCofan.mk (pullback.fst Y.hom (coprod.inl : A ⟶ A ⨿ B))
      (pullback.fst Y.hom (coprod.inr : B ⟶ A ⨿ B)))
    (pullback.snd _ _) (pullback.snd _ _) Y.hom pullback.condition.symm
    pullback.condition.symm).mpr
    ⟨IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩).some

omit [HasFiniteLimits C] in
/-- Pulling back along the two coprojections is jointly fully faithful. -/
theorem pullback_inl_inr_bijective {A B : C} {Y Y' : Over (A ⨿ B)} :
    Function.Bijective (fun φ : Y ⟶ Y' =>
      ((Over.pullback (coprod.inl : A ⟶ A ⨿ B)).map φ,
        (Over.pullback (coprod.inr : B ⟶ A ⨿ B)).map φ)) := by
  have hc := isColimitPullbackCoprodInlInr Y
  constructor
  · intro φ ψ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    ext
    apply BinaryCofan.IsColimit.hom_ext hc
    · have := congrArg (fun χ => χ.left ≫ pullback.fst _ _) h₁
      simpa [pullback.lift_fst, pullback.lift_snd] using this
    · have := congrArg (fun χ => χ.left ≫ pullback.fst _ _) h₂
      simpa [pullback.lift_fst, pullback.lift_snd] using this
  · rintro ⟨a, b⟩
    obtain ⟨l, hl₁, hl₂⟩ := BinaryCofan.IsColimit.desc' hc
      (a.left ≫ pullback.fst _ _) (b.left ≫ pullback.fst _ _)
    have hw : l ≫ Y'.hom = Y.hom := by
      apply BinaryCofan.IsColimit.hom_ext hc
      · have ha := Over.w a
        simp only [Over.pullback_obj_left, Over.pullback_obj_hom] at ha
        simp only [BinaryCofan.mk_inl] at hl₁ ⊢
        rw [reassoc_of% hl₁, pullback.condition, ← Category.assoc, ha,
          pullback.condition]
      · have hb := Over.w b
        simp only [Over.pullback_obj_left, Over.pullback_obj_hom] at hb
        simp only [BinaryCofan.mk_inr] at hl₂ ⊢
        rw [reassoc_of% hl₂, pullback.condition, ← Category.assoc, hb,
          pullback.condition]
    refine ⟨Over.homMk l hw, Prod.ext ?_ ?_⟩
    · ext
      apply pullback.hom_ext
      · simpa [pullback.lift_fst, pullback.lift_snd] using hl₁
      · simpa [pullback.lift_fst, pullback.lift_snd] using (Over.w a).symm
    · ext
      apply pullback.hom_ext
      · simpa [pullback.lift_fst, pullback.lift_snd] using hl₂
      · simpa [pullback.lift_fst, pullback.lift_snd] using (Over.w b).symm

end Extensive

/-- In a finitary extensive category with finite limits, if `f : A ⟶ S` and `g : B ⟶ S`
are exponentiable (pullback along them has a right adjoint), then so is
`coprod.desc f g : A ⨿ B ⟶ S`. -/
theorem coprod_desc_exponentiable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    [FinitaryExtensive C] {A B S : C} (f : A ⟶ S) (g : B ⟶ S)
    [Functor.IsLeftAdjoint (Over.pullback f)] [Functor.IsLeftAdjoint (Over.pullback g)] :
    Functor.IsLeftAdjoint (Over.pullback (coprod.desc f g)) := by
  have h₁' : (Over.pullback (coprod.inl ≫ coprod.desc f g)).IsLeftAdjoint := by
    simp only [coprod.inl_desc]; infer_instance
  have h₂' : (Over.pullback (coprod.inr ≫ coprod.desc f g)).IsLeftAdjoint := by
    simp only [coprod.inr_desc]; infer_instance
  have h₁ : (Over.pullback (coprod.desc f g) ⋙ Over.pullback coprod.inl).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (Over.pullbackComp _ _)
  have h₂ : (Over.pullback (coprod.desc f g) ⋙ Over.pullback coprod.inr).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (Over.pullbackComp _ _)
  exact isLeftAdjoint_of_jointly_fullyFaithful _ _ _ pullback_inl_inr_bijective

end CategoryTheory
