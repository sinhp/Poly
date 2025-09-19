/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.Adjunction.Lifting.Right
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

instance mapPullbackAdj_regularMono {C} [Category C] [HasPullbacks C] {A B : C} (F : A ⟶ B)
    (X : Over A) : RegularMono ((mapPullbackAdj F).unit.app X) := by
  let FU := Over.map F ⋙ Over.pullback F
  set η := (mapPullbackAdj F).unit
  have := congr($((whiskerLeft_comp_whiskerRight η η)).app X)
  refine ⟨_, _, _, this, Fork.IsLimit.mk' _ fun s => ?_⟩
  have hi := (Fork.ι s).w; simp at hi
  have w := congr($(Fork.condition s).left ≫ pullback.fst .. ≫ pullback.snd ..); simp [η] at w
  refine ⟨homMk (s.ι.left ≫ pullback.fst ..) (by simp [w, hi]), ?_, ?_⟩
  · ext; simp; ext <;> simp [η]; rw [w]
  · intro m H; ext; simpa [η] using congr(($H).left ≫ pullback.fst ..)

/-- The pullback of exponentiable morphisms is exponentiable. -/
theorem of_isPullback {C' : Type u} [Category.{v} C'] [HasPullbacks C'] [HasTerminal C']
  {P I J K : C'} {fst : P ⟶ I} {snd : P ⟶ K} {f : I ⟶ J} {g : K ⟶ J}
    (H : IsPullback fst snd f g) [ExponentiableMorphism g] : ExponentiableMorphism fst :=
  have : IsLeftAdjoint _ :=
    ⟨_, ⟨(mapPullbackAdj f).comp (adj g) |>.ofNatIsoLeft (pullbackMapIsoSquare H.flip).symm⟩⟩
  isLeftAdjoint_triangle_lift (Over.pullback fst) (mapPullbackAdj snd)

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
