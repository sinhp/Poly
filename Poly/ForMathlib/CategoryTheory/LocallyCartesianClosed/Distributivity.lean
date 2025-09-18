/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Opposites
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Basic
import Poly.ForMathlib.CategoryTheory.NatTrans
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.BeckChevalley

/-!
# Pentagon distributivity

Given morphims `u : M ⟶ B` and `f : B ⟶ A`, consider the following commutative diagram where
`v = Pi' f u` is the dependent product of `u` along `f`, `w` is the pullback of `v` along `f`,
and `e` is the component of the counit of the adjunction `pullback f ⊣ pushforward f` at `u`:
```
        P ---g--> D
    e / |         |
     M  | w       | v
    u \ |         |
        B ---f--> A
```

We construct a natural isomorphism
`Over.map u ⋙ pushforward f ≅ pullback e ⋙ pushforward g ⋙  Over.map v`
-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans Over ExponentiableMorphism Reindex
  LocallyCartesianClosed

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
  [LocallyCartesianClosed C]

variable {A B M : C} (f : B ⟶ A) (u : M ⟶ B)

abbrev v := Pi' f u

abbrev P := Limits.pullback f (v f u)  -- not really needed

def g := pullback.fst (v f u) f -- (μ_ (Over.mk f) (Over.mk (v f u))).left  --pullback.fst (@v _ _ _ _ _ _ _ f u) f

/-- This should not be an instance because it's not usually how we want to construct
exponentiable morphisms, we'll usually prove all morphims are exponential uniformly
from LocallyCartesianClosed structure.
The instance is inferred from the LocallyCartesianClosed structure, but
we should prove this more generally without assuming the LCCC structure. -/
def exponentiableMorphism : ExponentiableMorphism (g f u) := by infer_instance

namespace ExponentiableMorphism

structure IsCoequalizer {C} [Category C] {A B L : C} (f g : A ⟶ B) {L} (π : B ⟶ L) : Prop where
  w : f ≫ π = g ≫ π
  isColimit : Nonempty (IsColimit (Cofork.ofπ π w))

def CategoryTheory.Adjunction.cofork {C D} [Category C] [Category D]
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) :
    Cofork (whiskerLeft (U ⋙ F) adj.counit) (whiskerRight adj.counit (U ⋙ F)) :=
  .ofπ adj.counit (whiskerLeft_comp_whiskerRight adj.counit adj.counit)

def CategoryTheory.Adjunction.fork {C D} [Category C] [Category D]
    {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) :
    Fork (whiskerLeft (F ⋙ U) adj.unit) (whiskerRight adj.unit (F ⋙ U)) :=
  .ofι adj.unit (whiskerLeft_comp_whiskerRight adj.unit adj.unit).symm

theorem associator_eq_id {C D E E'} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : Functor.associator F G H = Iso.refl (F ⋙ G ⋙ H) := rfl

theorem whiskerRight_left' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K = whiskerLeft F (whiskerRight α K) := rfl

theorem id_whiskerLeft' {C D} [Category C] [Category D] {G H : C ⥤ D} (α : G ⟶ H) :
    whiskerLeft (𝟭 C) α = α := rfl

theorem id_whiskerRight' {C D} [Category C] [Category D] {G H : C ⥤ D} (α : G ⟶ H) :
    whiskerRight α (𝟭 D) = α := rfl

theorem whiskerLeft_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) = whiskerLeft (F ⋙ G) α := rfl

theorem whiskerRight_twice' {C D E B} [Category C] [Category D] [Category E] [Category B]
    {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G = whiskerRight α (F ⋙ G) := rfl

abbrev Cofork.π' {C} [Category C] {X Y : C} {f g : X ⟶ Y} (s : Cofork f g) : Y ⟶ s.pt := s.π

def parallelPairComp {C D} [Category C] [Category D] {X Y : C} {f g : X ⟶ Y} (F : C ⥤ D) :
    parallelPair f g ⋙ F ≅ parallelPair (F.map f) (F.map g) := diagramIsoParallelPair _

def preservesCoequalizer {C D} [Category C] [Category D] {X Y : C} {f g : X ⟶ Y}
    {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) (F : C ⥤ D)
    (H : IsColimit (Cofork.ofπ π w)) [PreservesColimit (parallelPair f g) F] :
    IsColimit (Cofork.ofπ (f := F.map f) (g := F.map g) (F.map π)
      (by rw [← map_comp, w, map_comp])) := by
  have := isColimitOfPreserves F H
  let iso : parallelPair f g ⋙ F ≅ parallelPair (F.map f) (F.map g) := diagramIsoParallelPair _
  refine (IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence iso.symm)).symm this
    |>.ofIsoColimit (Cofork.ext (Iso.refl _) ?_)
  simp [Cocones.precompose, Cofork.π, iso]

-- theorem whiskeringLeft_preservesEpi {C D E} [Category C] [Category D] [Category E] (F : C ⥤ D)
--     : ((whiskeringLeft C D E).obj F).PreservesEpimorphisms := by
--   refine ⟨fun {G G'} f ⟨hf⟩ => ⟨fun {K} g h eq => ?_⟩⟩
--   ext X
--   replace eq := congr(($eq).app X)
--   dsimp at g h eq
--   exact hf _ _ eq



--   have := isColimitOfPreserves F H
--   let iso : parallelPair f g ⋙ F ≅ parallelPair (F.map f) (F.map g) := diagramIsoParallelPair _
--   refine (IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence iso.symm)).symm this
--     |>.ofIsoColimit (Cofork.ext (Iso.refl _) ?_)
--   simp [Cocones.precompose, Cofork.π, iso]

-- instance evaluation_preservesColimit
--     {C : Type u} [Category.{v} C] {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
--     (F : J ⥤ K ⥤ C) (k : K) :
--     PreservesColimit F ((evaluation K C).obj k) := by
--   refine ⟨fun h' => ⟨fun s => ?_, ?_, ?_⟩⟩
--   · simp
--     have := s.ι.app; simp at this
--     -- have := h'.desc precompose
--     have := h'.desc ⟨_, fun x => by
--       have := s.ι.app x
--       dsimp at this

--       simp, _⟩
  -- let X : (k : K) → ColimitCocone (F.flip.obj k) := fun k => getColimitCocone (F.flip.obj k)
  -- preservesColimit_of_preserves_colimit_cocone (combinedIsColimit _ X) <|
    -- IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F X k).symm

-- instance whiskeringLeft_preservesColimit
--     {C : Type u₁} [Category.{v₁} C]
--     {D : Type u₂} [Category.{v₂} D]
--     {E : Type u₃} [Category.{v₃} E]
--     (J : Type u) [Category.{v} J]
--     (K : J ⥤ E ⥤ D) (F : C ⥤ E)
--     -- [∀ (k : E), HasColimit (K.flip.obj k)]
--     :
--     PreservesColimit K ((whiskeringLeft C E D).obj F) :=
--   ⟨fun c {hc} => ⟨by
--     apply evaluationJointlyReflectsColimits
--     intro Y
--     change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
--     have := evaluation_preservesColimit K (F.obj Y)
--     exact isColimitOfPreserves _ hc⟩⟩

attribute [-simp] whiskerLeft_twice whiskerRight_twice in
def adjointTriangle {B C A : Type*} [Category B] [Category C] [Category A] [HasCoequalizers A]
    {U : B ⥤ C} {F : C ⥤ B} (adj1 : F ⊣ U)
    {R : A ⥤ B} {F' : C ⥤ A} (adj2 : F' ⊣ R ⋙ U)
    (H : IsColimit adj1.cofork) : (L : B ⥤ A) × (L ⊣ R) := by
  let θ : F ⟶ F' ⋙ R := ((mateEquiv adj2 adj1).symm (.mk _ R (𝟭 _) _ (𝟙 _))).natTrans
  let α : U ⋙ F ⋙ U ⋙ F' ⟶ U ⋙ F' := whiskerRight adj1.counit (U ⋙ F')
  let β : U ⋙ F ⋙ U ⋙ F' ⟶ U ⋙ F' :=
    whiskerLeft U (whiskerRight θ (U ⋙ F')) ≫ whiskerLeft (U ⋙ F') adj2.counit
  let L := coequalizer α β; use L
  let π : _ ⟶ L := coequalizer.π ..
  have eq : α ≫ π = β ≫ π := coequalizer.condition ..
  have : whiskerLeft (R ⋙ U) θ ≫ whiskerRight adj2.counit R = whiskerLeft R adj1.counit := by
    ext X; simp [θ]
    have := adj2.right_triangle_components X; dsimp at this
    rw [← counit_naturality, ← map_comp_assoc, this]; simp
  let preserves : IsColimit (Cofork.ofπ
      (f := whiskerLeft R α) (g := whiskerLeft R β) (whiskerLeft R π) _) :=
    preservesCoequalizer π eq ((whiskeringLeft A B A).obj R) (coequalizerIsCoequalizer ..)
  let iso Y : (coequalizer α β).obj Y ≅ coequalizer (α.app Y) (β.app Y) :=
    letI J := _
    (colimitObjIsoColimitCompEvaluation (parallelPair α β) Y : _ ≅ colimit J).trans <|
    colim.mapIso (diagramIsoParallelPair J)
  refine
    let η := H.desc (Cofork.ofπ (P := L ⋙ R) (whiskerLeft U θ ≫ whiskerRight π R) ?_)
    let ε := preserves.desc (Cofork.ofπ adj2.counit ?_)
    have η_cond : adj1.counit ≫ η = U.whiskerLeft θ ≫ whiskerRight π R := Cofork.IsColimit.π_desc H
    have ε_cond : R.whiskerLeft π ≫ ε = adj2.counit := Cofork.IsColimit.π_desc preserves
    .mkOfUnitCounit {
      unit := η, counit := ε, left_triangle := (?_ : _ = 𝟙 _), right_triangle := (?_ : _ = 𝟙 _) }
  · replace eq := congr(whiskerLeft (U ⋙ F ⋙ U) θ ≫ whiskerRight $eq R)
    simp [α, β] at eq
    conv_rhs at eq =>
      conv => enter [2,1]; apply whiskerRight_left'
      rw [← whiskerLeft_twice', ← whiskerLeft_twice', ← whiskerLeft_comp_assoc]
      conv => enter [1,2]; apply whiskerLeft_comp_whiskerRight
      rw [whiskerLeft_comp_assoc];
      conv =>
        arg 2
        rw [whiskerRight_left', ← whiskerLeft_twice', ← whiskerLeft_twice']
        rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
        enter [1,2,2]; rw [whiskerLeft_twice', this]
      rw [← whiskerLeft_comp_assoc]
      conv => enter [1,2]; apply (whiskerLeft_comp_whiskerRight ..).symm
      rw [id_whiskerRight', whiskerLeft_comp_assoc, whiskerLeft_twice']
    rw [← eq, ← whiskerRight_twice', whiskerRight_twice']
    apply whiskerLeft_comp_whiskerRight_assoc
  · simp [α, β]; rw [← whiskerRight_left', ← this]
    rw [whiskerRight_comp_assoc, whiskerRight_left', whiskerLeft_twice']; congr 1
    exact (whiskerLeft_comp_whiskerRight adj2.counit adj2.counit).symm
  · simp [associator_eq_id]
    conv_lhs => arg 2; apply id_comp
    have _ : Epi π := (Cofork.IsColimit.epi (coequalizerIsCoequalizer α β) :)
    have _ : Epi (whiskerRight adj1.counit (U ⋙ F')) := by
      refine SplitEpi.epi ⟨whiskerRight (whiskerLeft U adj1.unit) F', ?_⟩
      rw [← whiskerRight_twice', ← whiskerRight_comp, adj1.right_triangle]
      apply whiskerRight_id
    rw [← cancel_epi π, ← cancel_epi (whiskerRight adj1.counit (U ⋙ F'))]
    conv_rhs => arg 2; apply comp_id
    have := whiskerLeft_comp_whiskerRight adj1.counit π
    rw [id_whiskerLeft'] at this; rw [← reassoc_of% this]; clear this
    rw [← whiskerRight_comp_assoc, η_cond, whiskerRight_comp_assoc,
      whiskerRight_left', ← whiskerLeft_twice', ← whiskerLeft_comp_assoc,
      whiskerLeft_comp_whiskerRight, whiskerLeft_comp_assoc, whiskerLeft_twice']
    conv_lhs => arg 2; apply reassoc_of% whiskerLeft_comp_whiskerRight
    rw [← whiskerLeft_twice', ← whiskerLeft_comp, ε_cond]
    conv_lhs => arg 2; apply (whiskerLeft_comp_whiskerRight π adj2.counit).symm
    rw [id_whiskerRight', ← assoc]; exact eq.symm
  · simp [associator_eq_id]
    suffices _ : Epi (R.whiskerLeft adj1.counit) by
      refine (cancel_epi (R.whiskerLeft adj1.counit)).1 ?_
      rw [← whiskerLeft_comp_assoc, η_cond, whiskerLeft_comp_assoc, whiskerLeft_twice',
        ← whiskerRight_left', ← whiskerRight_comp, ε_cond, this, comp_id]
    -- have := adj1.left_triangle
    -- refine SplitEpi.epi ⟨_, _⟩
    refine ⟨fun {Z} (f₁ f₂ : R ⟶ _) eq => ?_⟩
    -- let X : HasCoequalizers B := sorry
    -- have (k : B) : HasColimit
    --    ((parallelPair ((U ⋙ F).whiskerLeft adj1.counit)
    --     (whiskerRight adj1.counit (U ⋙ F))).flip.obj k) := by
    --   let α' := (U ⋙ F).whiskerLeft adj1.counit
    --   let β' := whiskerRight adj1.counit (U ⋙ F)
    --   let K : Cofork α' β' := adj1.cofork
    --   have : α' ≫ adj1.counit = β' ≫ adj1.counit := K.condition
    --   change IsColimit K at H
    --   dsimp [Cofork] at K
    --   let iso := diagramIsoParallelPair ((parallelPair α' β').flip.obj k)
    --   let Q : Cocone (parallelPair (α'.app k) (β'.app k)) :=
    --     Cofork.ofπ (adj1.counit.app k) (by rw [← comp_app, this, comp_app])
    --   refine ⟨_, (IsColimit.ofCoconeEquiv (c := Q) (Cocones.precomposeEquivalence iso)).symm ?_⟩
    --   have := H
    --   refine Cofork.IsColimit.mk _ (fun s => (H.desc s).app k) _ _
    --   #exit
    --   simp [Cocones.precompose, iso]
    -- stop
    -- have := preservesCoequalizer _ _ ((whiskeringLeft A B B).obj R) H
    have : Epi adj1.counit := Cofork.IsColimit.epi H
    have := @this.1
    have := congr(R.whiskerLeft (U.whiskerLeft adj1.unit) ≫ whiskerRight $eq U)
    simp at this
    rw [whiskerRight_left', ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
      adj1.right_triangle, whiskerLeft_id', id_comp, id_comp] at this
    suffices _ : U.Faithful from faithful_whiskeringRight_obj.1 this
    refine ⟨fun {X Y} f g eq => ?_⟩
    sorry

def coadjointTriangle {C D E : Type*} [Category C] [Category D] [Category E] [HasEqualizers E]
    {L : C ⥤ D} {R : D ⥤ C} (adj1 : L ⊣ R)
    {L' : E ⥤ C} {R' : D ⥤ E} (adj2 : L' ⋙ L ⊣ R')
    (H : IsLimit adj1.fork) : (R₁ : C ⥤ E) × (L' ⊣ R₁) := by
  suffices Hop : IsColimit adj1.op.cofork from
    have ⟨L, hL⟩ := adjointTriangle adj1.op adj2.op (R := L'.op) Hop
    ⟨L.unop, hL.unop⟩
  refine Cofork.IsColimit.mk' _ fun s => ?_
  let π : s.pt.unop ⟶ L ⋙ R := NatTrans.unop s.π
  let l := Fork.IsLimit.lift H π (congrArg NatTrans.unop s.condition)
  refine have eq := Fork.IsLimit.lift_ι' ..; ⟨NatTrans.op l, congrArg NatTrans.op eq, ?_⟩
  refine fun {m} h => congrArg NatTrans.op (?_ : NatTrans.unop m = _)
  exact Fork.IsLimit.hom_ext H ((congrArg NatTrans.unop h).trans eq.symm)

def mapPullbackAdjComonadic {C} [Category C] [HasPullbacks C] {A B : C} (F : A ⟶ B) :
    IsLimit (CategoryTheory.Adjunction.fork (mapPullbackAdj F)) := by
  refine Fork.IsLimit.mk' _ fun s => ?_
  dsimp [CategoryTheory.Adjunction.fork]
  let ι : s.pt ⟶ Over.map F ⋙ Over.pullback F := Fork.ι s
  have w : ι ≫ _ = ι ≫ _ := Fork.condition s
  refine ⟨⟨fun X => ?_, fun X Y f => ?_⟩, ?_, ?_⟩
  · simp
    let X1 := X.left
    let X2 : X1 ⟶ A := X.hom
    refine Over.homMk ((ι.app X).left ≫ pullback.fst ..) ?_
    have := congr((($w).app X).left ≫ pullback.fst .. ≫ pullback.snd ..); simp at this ⊢
    rw [← this]; simpa using (ι.app X).w
  · ext; simp
    have := congr($(ι.naturality f).left ≫ pullback.fst ..); simpa [-naturality]
  · ext X; simp; ext <;> simp; · rfl
    simpa using congr((($w.symm).app X).left ≫ pullback.fst .. ≫ pullback.snd ..)
  · intro m H; ext X
    simpa using congr((($H).app X).left ≫ pullback.fst ..)

/-- The pullback of exponentiable morphisms is exponentiable. -/
theorem of_isPullback {C' : Type u} [Category.{v} C'] [HasPullbacks C'] [HasTerminal C']
  {P I J K : C'} {fst : P ⟶ I} {snd : P ⟶ K} {f : I ⟶ J} {g : K ⟶ J}
    (H : IsPullback fst snd f g) [ExponentiableMorphism g] : ExponentiableMorphism fst := by
  refine ⟨⟨_, ⟨coadjointTriangle (mapPullbackAdj snd)
    ((mapPullbackAdj f).comp (adj g) |>.ofNatIsoLeft (pullbackMapIsoSquare H.flip).symm) ?_ |>.2⟩⟩⟩
  apply mapPullbackAdjComonadic

end ExponentiableMorphism

def w := pullback.snd (v f u) f

def e := ((ev f).app (Over.mk u)).left -- ev' (Over.mk f) (Over.mk u)

/- On the way to prove `pentagonIso`.
We show that the pasting of the 2-cells in below is an isomorphism.
```
        Δe         Πg
    C/M ----> C/P ----> C/D
    |          |         |
 Σu |   ↙      | Σw  ≅   | Σv
    v          v         v
    C/B ---- C/B ----> C/A
                   f
```
1. To do this we first prove that that the left cell is cartesian.
2. Then we observe the right cell is cartesian since it is an iso.
3. So the pasting is also cartesian.
4. The component of this 2-cell at the terminal object is an iso,
  so the 2-cell is an iso.
-/

def cellLeftTriangle : e f u ≫ u = w f u := by
  unfold e w v
  have := ((ev f).app (Over.mk u)).w
  aesop_cat

def cellLeft : pullback (e f u) ⋙ map (w f u) ⟶ map u :=
  pullbackMapTriangle _ _ _ (cellLeftTriangle f u)

lemma isCartesian_cellLeft : IsCartesian (cellLeft f u) := by
  unfold IsCartesian
  simp only [id_obj, mk_left, comp_obj, pullback_obj_left, Functor.comp_map]
  unfold cellLeft
  intros i j f'
  have α := pullbackMapTriangle (w f u) (e f u)
  simp only [id_obj, mk_left] at α u
  sorry

def cellRightCommSq : CommSq (g f u) (w f u) (v f u) f :=
  IsPullback.toCommSq (IsPullback.of_hasPullback _ _)

def cellRight' : pushforward (g f u) ⋙ map (v f u)
  ≅ map (w f u) ⋙ pushforward f := sorry

lemma isCartesian_cellRight' : IsCartesian (cellRight' f u).hom :=
  isCartesian_of_isIso ((cellRight' f u).hom)

def pasteCell1 : pullback (e f u) ⋙ pushforward (g f u) ⋙ map (v f u) ⟶
  pullback (e f u) ⋙ map (w f u) ⋙ pushforward f := by
  apply whiskerLeft
  exact (cellRight' f u).hom

def pasteCell2 : (pullback (e f u) ⋙ map (w f u)) ⋙ pushforward f
   ⟶ (map u) ⋙ pushforward f := by
  apply whiskerRight
  exact cellLeft f u

def pasteCell := pasteCell1 f u ≫ pasteCell2 f u

def paste : IsCartesian (pasteCell f u) := by
  apply IsCartesian.comp
  · unfold pasteCell1
    apply (isCartesian_cellRight' f u).whiskerLeft
  · unfold pasteCell2
    apply (isCartesian_cellLeft f u).whiskerRight

-- use `pushforwardPullbackTwoSquare` to construct this iso.
def pentagonIso : map u ⋙ pushforward f ≅
  pullback (e f u) ⋙ pushforward (g f u) ⋙ map (v f u) := by
  have := isCartesian_of_isPullback_to_terminal (pasteCell f u)
  letI : IsIso ((pasteCell f u).app (⊤_ Over ((𝟭 (Over B)).obj (Over.mk u)).left)) := sorry
  have := isIso_of_isCartesian (pasteCell f u) (paste f u)
  exact (asIso (pasteCell f u)).symm

end CategoryTheory
