/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.LCCC.BeckChevalley
import Poly.MvPolynomial


/-!
# Polynomial Functor

-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`CartesianExponentiable` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

open CategoryTheory Category Limits Functor Adjunction Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly (E B : C) where
  (p : E ⟶ B)
  (exp : CartesianExponentiable p := by infer_instance)

attribute [instance] UvPoly.exp

namespace UvPoly

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : HasBinaryProducts C :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks C

variable {E B : C}

/-- The constant polynomial in many variables: for this we need the initial object -/
def const [HasInitial C] (S : C) : UvPoly (⊥_ C) S := ⟨initial.to S, inferInstance⟩

def smul [HasBinaryProducts C] (S : C) (P : UvPoly E B) : UvPoly (S ⨯ E) (S ⨯ B) :=
  ⟨prod.map (𝟙 S) P.p, sorry⟩

/-- The product of two polynomials in a single variable. -/
def prod (P : UvPoly E B) (Q : UvPoly E' B') [HasBinaryCoproducts C]:
    UvPoly ((E ⨯ B') ⨿ (B ⨯ E')) (B ⨯ B') where
  p := coprod.desc (prod.map P.p (𝟙 B')) (prod.map (𝟙 B) Q.p)
  exp := sorry -- perhaps we need extra assumptions on `C` to prove this, e.g. `C` is lextensive?

/-- For a category `C` with binary products, `P.functor : C ⥤ C` is the functor associated
to a single variable polynomial `P : UvPoly E B`. -/
def functor [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C :=
    (Δ_ E) ⋙ (Π_ P.p) ⋙ (Σ_ B)

/-Note (SH): Alternatively, we can define the functor associated to a single variable polynomial in
terms of `MvPoly.functor` and then reduce the proofs of statements about single variable polynomials
to the multivariable case using the equivalence between `Over (⊤_ C)` and `C`.-/
def toMvPoly (P : UvPoly E B) : MvPoly (⊤_ C) (⊤_ C) :=
  ⟨E, B, terminal.from E, P.p, P.exp, terminal.from B⟩

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B`. -/
def proj' (P : UvPoly E B) (X : Over (⊤_ C)) :
  ((Π_ P.p).obj ((Over.pullback (terminal.from E)).obj X)).left ⟶ B :=
  ((Over.pullback (terminal.from _) ⋙ (Π_ P.p)).obj X).hom

def auxFunctor (P : UvPoly E B) : Over (⊤_ C)  ⥤ Over (⊤_ C) := MvPoly.functor P.toMvPoly

/-- We use the equivalence between `Over (⊤_ C)` and `C` to get `functor : C ⥤ C`.
Alternatively we can give a direct definition of `functor` in terms of exponentials. -/
def functor' (P : UvPoly E B) : C ⥤ C :=  equivOverTerminal.functor ⋙ P.auxFunctor ⋙ equivOverTerminal.inverse

def functorIsoFunctor' [HasBinaryProducts C] (P : UvPoly E B) : P.functor ≅ P.functor' := by
  unfold functor' auxFunctor functor MvPoly.functor toMvPoly
  simp
  sorry

/-- The projection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def proj (P : UvPoly E B) (X : C) : P.functor.obj X ⟶ B :=
  ((Δ_ E ⋙ Π_ P.p).obj X).hom

@[simp, reassoc (attr := simp)]
lemma map_proj {X Y : C} (P : UvPoly E B) (f : X ⟶ Y) : P.functor.map f ≫ P.proj Y = P.proj X := by
  simp [proj, functor]

/-- Essentially star is just the pushforward Beck-Chevalley natural transformation associated to
the square defined by `g`, but you have to compose with various natural isomorphisms. -/
def star (P : UvPoly E B) (Q : UvPoly F B) (g : E ⟶ F) (h : P.p = g ≫ Q.p) :
    Q.functor ⟶ P.functor := by
  unfold functor
  have hsquare : g ≫ Q.p = P.p ≫ 𝟙 _ := by simpa [comp_id] using h.symm
  have bc := pushforwardBeckChevalleyNatTrans g Q.p P.p (𝟙 _) hsquare Q.exp P.exp
  exact whiskerRight ((whiskerLeft (Δ_ F) ((whiskerLeft (Π_ Q.p)
    (baseChange.id B).symm.hom) ≫ bc)) ≫ (whiskerRight (baseChange.mapStarIso g).inv (Π_ P.p)))
      (Over.forget B)

variable (B)
/-- The identity polynomial functor in single variable. -/
@[simps!]
def id : UvPoly B B := ⟨𝟙 B, by infer_instance⟩

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `B × X`. -/
def id_apply (X : C) : (id B).functor.obj X ≅ B ⨯ X where
  hom := 𝟙 (B ⨯ X)
  inv := 𝟙 (B ⨯ X)

variable {B}

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'`
and `b : B ⟶ B'` such that the diagram
```
  E ---P.p--> B
  |           |
  e           b
  |           |
  v           v
  E' --Q.p--> B'
```
is a pullback square. -/
structure Hom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') where
  e : E ⟶ E'
  b : B ⟶ B'
  is_pullback : IsPullback P.p e b Q.p

namespace Hom

open IsPullback

-- baseChange.isLimitPullbackConeId _
def id (P : UvPoly E B) : Hom P P := ⟨𝟙 E, 𝟙 B, ⟨by aesop, ⟨ sorry ⟩⟩⟩

def comp {E' B' E'' B'' : C} {P : UvPoly E B} {Q : UvPoly E' B'} {R : UvPoly E'' B''}
    (f : Hom P Q) (g : Hom Q R) : Hom P R where
  e := f.e ≫ g.e
  b := f.b ≫ g.b
  is_pullback := paste_vert f.is_pullback g.is_pullback

end Hom

/-- Bundling up the the polynomials over different bases to form the underlying type of the
category of polynomials. -/
structure Total (C : Type*) [Category C] [HasPullbacks C] where
  (E B : C)
  (poly : UvPoly E B)

def Total.of (P : UvPoly E B) : Total C := ⟨E, B, P⟩

end UvPoly

open UvPoly

/-- The category of polynomial functors in a single variable. -/
instance : Category (UvPoly.Total C) where
  Hom P Q := UvPoly.Hom P.poly Q.poly
  id P := UvPoly.Hom.id P.poly
  comp := UvPoly.Hom.comp
  id_comp := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  comp_id := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
  assoc := by
    simp [UvPoly.Hom.comp]

def Total.ofHom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') (α : P.Hom Q) :
    Total.of P ⟶ Total.of Q where
  e := α.e
  b := α.b
  is_pullback := α.is_pullback

namespace UvPoly

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : SMul C (Total C) where
  smul S P := Total.of (smul S P.poly)

/-- Scaling a polynomial `P` by an object `S` is isomorphic to the product of `const S` and the
polynomial `P`. -/
@[simps!]
def smul_eq_prod_const [HasBinaryCoproducts C] [HasInitial C] (S : C) (P : Total C) :
    S • P ≅ Total.of ((const S).prod P.poly) where
      hom := sorry
      inv := sorry
      hom_inv_id := sorry
      inv_hom_id := sorry

variable {E B : C}

def polyPair {Γ X : C} (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) :
    Σ b : Γ ⟶ B, pullback b P.p ⟶ X :=
  let b := be ≫ P.proj X
  let be' : Over.mk b ⟶ (Δ_ E ⋙ Π_ P.p).obj X := Over.homMk be
  let be'' := (P.exp.adj.homEquiv _ _).symm be'
  let be''' : pullback b P.p ⟶ E ⨯ X := be''.left
  ⟨b, be''' ≫ prod.snd⟩

def pairPoly {Γ X : C} (P : UvPoly E B) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P.functor.obj X :=
  let pbE := (Δ_ P.p).obj (Over.mk b)
  let eE : pbE ⟶ (Δ_ E).obj X := (Over.forgetAdjStar E).homEquiv _ _ e
  (P.exp.adj.homEquiv _ _ eE).left

/-! ## Generic pullback -/

/--
The UP of polynomial functors is mediated by a "generic pullback" [Awodey2017, p. 10, fig. 6].

```
     X
     ^
     | u₂
   genPb ---------------> E
 fst | ┘                  | p
     v                    v
P.functor.obj X --------> B
                P.proj X
```
-/
def genPb (P : UvPoly E B) (X : C) : C :=
  pullback (P.proj X) P.p

def genPb.fst (P : UvPoly E B) (X : C) : P.genPb X ⟶ P.functor.obj X :=
  pullback.fst (f := P.proj X) (g := P.p)

def genPb.u₂ (P : UvPoly E B) (X : C) : P.genPb X ⟶ X :=
  have : P.proj X = (P.polyPair <| 𝟙 <| P.functor.obj X).fst :=
    by simp [polyPair]
  (pullback.congrHom this rfl).hom ≫ (P.polyPair <| 𝟙 <| P.functor.obj X).snd

/-- The second component of `polyPair` is a comparison map of pullbacks composed with `genPb.u₂`. -/
theorem genPb.polyPair_snd_eq_comp_u₂' {Γ X : C} (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) :
    (P.polyPair be).snd = pullback.map (P.polyPair be).fst P.p (P.proj X) P.p be (𝟙 _) (𝟙 _) (by simp [polyPair]) (by simp) ≫
                          u₂ P X := by
  simp only [polyPair, u₂, homEquiv_counit, comp_left, ← assoc]
  congr 2
  aesop_cat

/-- Universal property of the polynomial functor. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) where
  toFun := P.polyPair
  invFun := fun ⟨b, e⟩ => P.pairPoly b e
  left_inv be := by
    simp_rw [polyPair, pairPoly, ← forgetAdjStar.homEquiv_symm]
    simp
  right_inv := by
    intro ⟨b, e⟩
    dsimp [polyPair, pairPoly]
    have := Over.forgetAdjStar.homEquiv (X := (Δ_ P.p).obj (Over.mk b)) (f := e)
    simp at this
    rw [this]
    set pairHat := P.exp.adj.homEquiv _ _ _
    congr! with h
    · simpa [-w] using pairHat.w
    · -- We deal with HEq/dependency by precomposing with an iso
      let i : Over.mk (pairHat.left ≫ P.proj X) ≅ Over.mk b :=
        Over.isoMk (Iso.refl _) (by simp [h])
      rw [
        show homMk _ _ = i.hom ≫ pairHat by ext; simp [i],
        show _ ≫ prod.snd = (pullback.congrHom h rfl).hom ≫ e by (
          simp only [pullback_obj_left,
          mk_left, mk_hom, star_obj_left, pullback_obj_hom, const_obj_obj, BinaryFan.mk_pt,
          BinaryFan.π_app_left, BinaryFan.mk_fst, id_eq, homEquiv_unit, id_obj, comp_obj,
          homEquiv_counit, map_comp, assoc, counit_naturality, left_triangle_components_assoc,
          comp_left, pullback_map_left, eqToHom_left, eqToHom_refl, homMk_left, prod.comp_lift,
          limit.lift_π, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app, comp_id,
          BinaryFan.π_app_right, BinaryFan.mk_snd, pullback.congrHom_hom, pairHat]
          congr 1
          ext <;> simp [i])
      ]
      generalize (hasPullbackHorizPaste .. : HasPullback (pairHat.left ≫ P.proj X) P.p) = pf
      generalize pairHat.left ≫ _ = x at h pf
      cases h
      simp [pullback.congrHom]

/-- `UvPoly.equiv` is natural in `Γ`. -/
lemma equiv_naturality_left {Δ Γ : C} (σ : Δ ⟶ Γ) (P : UvPoly E B) (X : C) (be : Γ ⟶ P.functor.obj X) :
    equiv P Δ X (σ ≫ be) = let ⟨b, e⟩ := equiv P Γ X be
                           ⟨σ ≫ b, pullback.lift (pullback.fst .. ≫ σ) (pullback.snd ..)
                                     (assoc (obj := C) .. ▸ pullback.condition) ≫ e⟩ := by
  dsimp
  congr! with h
  . simp [polyPair, pairPoly]
  . set g := _ ≫ (P.polyPair be).snd
    rw [(_ : (P.polyPair (σ ≫ be)).snd = (pullback.congrHom h rfl).hom ≫ g)]
    · generalize (P.polyPair (σ ≫ be)).fst = x at h
      cases h
      simp
    · simp only [polyPair, comp_obj, homEquiv_counit, id_obj, comp_left, pullback_obj_left,
      mk_left, mk_hom, star_obj_left, pullback_map_left, homMk_left, pullback.congrHom_hom, ←
      assoc, g]
      congr 2
      ext <;> simp

/-- `UvPoly.equiv` is natural in `X`. -/
lemma equiv_naturality_right {Γ X Y : C}
    (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) (f : X ⟶ Y) :
    equiv P Γ Y (be ≫ P.functor.map f) =
      let ⟨b, e⟩ := equiv P Γ X be
      ⟨b, e ≫ f⟩ := by
  dsimp
  congr! 1 with h
  . simp [polyPair]
  . set g := (P.polyPair be).snd ≫ f
    rw [(_ : (P.polyPair (be ≫ P.functor.map f)).snd = (pullback.congrHom h rfl).hom ≫ g)]
    · generalize (P.polyPair (be ≫ P.functor.map f)).fst = x at h
      cases h
      simp
    · dsimp only [polyPair, g]
      rw [homMk_comp (f_comp := by simp [proj, functor]) (g_comp := by simp [functor])]
      simp only [UvPoly.functor, Functor.comp_map, forget_map, left_homMk,
        homEquiv_naturality_right_symm, comp_left, assoc]
      rw [show ((Δ_ E).map f).left ≫ prod.snd = prod.snd ≫ f by simp]
      simp only [← assoc]
      congr 2
      simp only [comp_obj, forget_obj, star_obj_left, homEquiv_counit, id_obj, comp_left,
        pullback_obj_left, mk_left, mk_hom, pullback_map_left, Over.homMk_left,
        pullback.congrHom_hom, ← assoc]
      congr 1
      ext <;> simp

def foo [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Over.map P.poly.p) ⋙ (Over.map f.b) ≅ (Over.map f.e) ⋙ (Over.map Q.poly.p) :=
  mapSquareIso _ _ _ _ (f.is_pullback.w)

def bar [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Δ_ f.e) ⋙ (Σ_ P.poly.p) ≅ (Σ_ Q.poly.p) ⋙ (Δ_ f.b) := by
  set l := pullbackBeckChevalleyNatTrans P.poly.p f.b f.e Q.poly.p (f.is_pullback.w)
  have : IsIso l :=
    (pullbackBeckChevalleyNatTrans_of_IsPullback_is_iso P.poly.p f.b f.e Q.poly.p f.is_pullback)
  exact asIso l

def bar' [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    (Δ_ P.poly.p) ⋙ (Σ_ f.e) ≅ (Σ_ f.b) ⋙ (Δ_ Q.poly.p) := by
  sorry

/-- A map of polynomials induces a natural transformation between their associated functors. -/
def naturality [HasBinaryProducts C] {P Q : UvPoly.Total C} (f : P ⟶ Q) :
    P.poly.functor ⟶ Q.poly.functor := by
  sorry


def comp [HasPullbacks C] [HasTerminal C]
    {E B D C : C} (P : UvPoly E B) (Q : UvPoly D C) : UvPoly (pullback Q.p (genPb.u₂ P C)) (P.functor.obj C) :=
   {
     p :=  (pullback.snd Q.p (genPb.u₂ P C)) ≫  (genPb.fst P C)
     exp := by sorry
   }

/-- The associated functor of the composition of two polynomials is isomorphic to the composition of the associated functors. -/
def compFunctorIso [HasPullbacks C] [HasTerminal C]
    {E B D C : C} (P : UvPoly E B) (Q : UvPoly D C) :
    P.functor ⋙ Q.functor ≅ (comp P Q).functor := by
  sorry

end UvPoly

end
