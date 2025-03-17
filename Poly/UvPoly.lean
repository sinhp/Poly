/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.BeckChevalley -- LCCC.BeckChevalley
import Mathlib.CategoryTheory.Functor.TwoSquare
import Poly.ForMathlib.CategoryTheory.PartialProduct

/-!
# Polynomial Functor

The Universal property of polynomial functors is mediated through the partial product diagram
in below.
```
     X
     ^
     |
     |
     • -------fst-----> P @ X
     |                    |
     |        (pb)        | P.fstProj X
     v                    v
     E ---------------->  B
              P.p
```
-- TODO: there are various `sorry`-carrying proofs in below which require instances of
`ExponentiableMorphism` for various constructions on morphisms. They need to be defined in
`Poly.Exponentiable`.
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor Adjunction Over ExponentiableMorphism
  LocallyCartesianClosed

variable {C : Type*} [Category C] [HasPullbacks C]

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure UvPoly (E B : C) where
  (p : E ⟶ B)
  (exp : ExponentiableMorphism p := by infer_instance)

attribute [instance] UvPoly.exp

namespace UvPoly

open TwoSquare

variable {C : Type*} [Category C] [HasTerminal C] [HasPullbacks C]

instance : HasBinaryProducts C :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks C

variable {E B : C}

/-- The constant polynomial in many variables: for this we need the initial object -/
def const [HasInitial C] (S : C) : UvPoly (⊥_ C) S := ⟨initial.to S, sorry⟩

def smul [HasBinaryProducts C] (S : C) (P : UvPoly E B) : UvPoly (S ⨯ E) (S ⨯ B) :=
  ⟨prod.map (𝟙 S) P.p, sorry⟩

/-- The product of two polynomials in a single variable. -/
def prod {E' B'} (P : UvPoly E B) (Q : UvPoly E' B') [HasBinaryCoproducts C]:
    UvPoly ((E ⨯ B') ⨿ (B ⨯ E')) (B ⨯ B') where
  p := coprod.desc (prod.map P.p (𝟙 B')) (prod.map (𝟙 B) Q.p)
  exp := sorry -- perhaps we need extra assumptions on `C` to prove this, e.g. `C` is lextensive?

/-- For a category `C` with binary products, `P.functor : C ⥤ C` is the functor associated
to a single variable polynomial `P : UvPoly E B`. -/
def functor [HasBinaryProducts C] (P : UvPoly E B) : C ⥤ C :=
  Over.star E ⋙ pushforward P.p ⋙ forget B

/-- The evaluation function of a polynomial `P` at an object `X`. -/
def apply (P : UvPoly E B) : C → C := (P.functor).obj

@[inherit_doc]
infix:90 " @ " => UvPoly.apply

variable (B)

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id : UvPoly B B := ⟨𝟙 B, by infer_instance⟩

/-- The functor associated to the identity polynomial is isomorphic to the identity functor. -/
def idIso : (UvPoly.id B).functor ≅ star B ⋙ forget B :=
  isoWhiskerRight (isoWhiskerLeft _ (pushforwardIdIso B)) (forget B)

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `B × X`. -/
def idApplyIso (X : C) : (id B) @ X ≅ B ⨯ X := sorry

variable {B}

/-- The fstProjection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
@[simp]
def fstProj (P : UvPoly E B) (X : C) : P @ X ⟶ B :=
  ((Over.star E ⋙ pushforward P.p).obj X).hom

@[simp, reassoc (attr := simp)]
lemma map_fstProj {X Y : C} (P : UvPoly E B) (f : X ⟶ Y) :
    P.functor.map f ≫ P.fstProj Y = P.fstProj X := by
  simp [fstProj, functor]

/-- A vertical map `ρ : P.p ⟶ Q.p` of polynomials (i.e. a commutative triangle)
```
    ρ
E ----> F
 \     /
  \   /
   \ /
    B
```
induces a natural transformation `Q.functor ⟶ P.functor ` obtained by pasting the following 2-cells
```
              Q.p
C --- >  C/F ----> C/B -----> C
|         |          |        |
|   ↙     | ρ*  ≅    |   =    |
|         v          v        |
C --- >  C/E ---->  C/B ----> C
              P.p
```
-/
def verticalNatTrans {F : C} (P : UvPoly E B) (Q : UvPoly F B) (ρ : E ⟶ F) (h : P.p = ρ ≫ Q.p) :
    Q.functor ⟶ P.functor := by
  have sq : CommSq ρ P.p Q.p (𝟙 _) := by simp [h]
  let cellLeft := (Over.starPullbackIsoStar ρ).hom
  let cellMid := (pushforwardPullbackTwoSquare ρ P.p Q.p (𝟙 _) sq)
  let cellLeftMidPasted := TwoSquare.whiskerRight (cellLeft ≫ₕ cellMid) (Over.pullbackId).inv
  simpa using (cellLeftMidPasted ≫ₕ (vId (forget B)))

/-- A cartesian map of polynomials
```
           P.p
      E -------->  B
      |            |
   φ  |            | δ
      v            v
      F -------->  D
           Q.p
```
induces a natural transformation between their associated functors obtained by pasting the following
2-cells
```
              Q.p
C --- >  C/F ----> C/D -----> C
|         |          |        |
|   ↗     | φ*  ≅    | δ* ↗   |
|         v          v        |
C --- >  C/E ---->  C/B ----> C
              P.p
```
-/
def cartesianNaturalTrans {D F : C}[HasBinaryProducts C] (P : UvPoly E B) (Q : UvPoly F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p φ δ Q.p) :
    P.functor ⟶ Q.functor := by
  have sq : CommSq φ P.p Q.p δ := pb.toCommSq.flip
  let cellLeft : TwoSquare (𝟭 C) (Over.star F) (Over.star E) (pullback φ) :=
    (Over.starPullbackIsoStar φ).inv
  let cellMid :  TwoSquare (pullback φ) (pushforward Q.p) (pushforward P.p) (pullback δ) :=
    (pushforwardPullbackIsoSquare pb.flip).inv
  let cellRight : TwoSquare (pullback δ) (forget D) (forget B) (𝟭 C) :=
    pullbackForgetTwoSquare δ
  simpa using cellLeft ≫ᵥ cellMid ≫ᵥ cellRight

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'`
and `b : B ⟶ B'` such that the diagram
```
      E -- P.p ->  B
      ^            |
   ρ  |            |
      |     ψ      |
      Pb --------> B
      |            |
   φ  |            | δ
      v            v
      F -- Q.p ->  D
```
is a pullback square. -/
structure Hom {F D : C} (P : UvPoly E B) (Q : UvPoly F D) where
  Pb : C
  δ : B ⟶ D
  φ : Pb ⟶ F
  ψ : Pb ⟶ B
  ρ : Pb ⟶ E
  is_pb : IsPullback ψ φ δ Q.p
  w : ρ ≫ P.p = ψ

namespace Hom

open IsPullback

/-- The identity morphism in the category of polynomials. -/
def id (P : UvPoly E B) : Hom P P := ⟨E, 𝟙 B, 𝟙 _ , P.p , 𝟙 _, IsPullback.of_id_snd, by simp⟩

-- def vertCartExchange

/-- The composition of morphisms in the category of polynomials. -/
def comp {E B F D N M : C} {P : UvPoly E B} {Q : UvPoly F D} {R : UvPoly N M}
    (f : Hom P Q) (g : Hom Q R) : Hom P R := sorry

end Hom

/-- Bundling up the the polynomials over different bases to form the underlying type of the
category of polynomials. -/
structure Total (C : Type*) [Category C] [HasPullbacks C] where
  {E B : C}
  (poly : UvPoly E B)

def Total.of (P : UvPoly E B) : Total C := Total.mk P

end UvPoly

open UvPoly

/-- The category of polynomial functors in a single variable. -/
instance : Category (UvPoly.Total C) where
  Hom P Q := UvPoly.Hom P.poly Q.poly
  id P := UvPoly.Hom.id P.poly
  comp := UvPoly.Hom.comp
  id_comp := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
    sorry
  comp_id := by
    simp [UvPoly.Hom.id, UvPoly.Hom.comp]
    sorry
  assoc := by
    simp [UvPoly.Hom.comp]

def Total.ofHom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') (α : P.Hom Q) :
    Total.of P ⟶ Total.of Q := sorry

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

namespace PartialProduct

open PartialProduct

/-- The counit of the adjunction `pullback P.p ⊣ pushforward P.p` evaluated `(star E).obj X`. -/
def ε (P : UvPoly E B) (X : C) : pullback (P.fstProj X) P.p ⟶ E ⨯ X :=
  ((ev P.p).app ((star E).obj X)).left

/-- The partial product fan associated to a polynomial `P : UvPoly E B` and an object `X : C`. -/
@[simps]
def fan (P : UvPoly E B) (X : C) : Fan P.p X where
  pt := P @ X
  fst := P.fstProj X
  snd := (ε P X) ≫ ((forgetAdjStar E).counit).app X   -- (ε P X) ≫ prod.snd

-- used to be called `pairPoly`
@[simp]
def liftAux {Γ X : C} (P : UvPoly E B) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P @ X :=
  let b' : Over E := (Over.pullback P.p).obj (.mk b)
  let econj : b' ⟶ (star E).obj X := (forgetAdjStar E).homEquiv b' X e
  (adj P.p |>.homEquiv _ _ econj).left

-- theorem lifAux_conj

/--
`P.PartialProduct.fan` is in fact a limit fan; this provides the univeral mapping property of the
polynomial functor.
-/
def isLimitFan (P : UvPoly E B) (X : C) : IsLimit (fan P X) where
  lift c := (pushforwardCurry (Fan.mk c.fst c.snd).overPullbackToStar).left
  -- (P.exp.adj.homEquiv _ _ (Fan.mk c.fst c.snd).overPullbackToStar).left
  -- liftAux P c.fst c.snd
  fac_left := by aesop_cat
  fac_right := by
    intro c
    simp only [fan,pullbackMap, ev, ← assoc, ε]
    simp only [pushforwardCurry]
    --simp only [← homEquiv_counit]
    rw [← comp_left]
    sorry
    --simp only [Fan.overPullbackToStar_snd]

    -- rw [← comp_left]
    -- simp_rw [← homEquiv_counit]
  uniq := sorry

end PartialProduct

open PartialProduct

abbrev lift {Γ X : C} (P : UvPoly E B) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P @ X :=
  partialProd.lift ⟨fan P X, isLimitFan P X⟩ b e

-- formerly polyPair
def proj {Γ X : C} (P : UvPoly E B) (f : Γ ⟶ P @ X) :
    Σ b : Γ ⟶ B, pullback b P.p ⟶ X :=
  ⟨f ≫ P.fstProj X, fan P X |>.extend f |>.snd⟩

variable {Γ X : C} (P : UvPoly E B)


#check Over.pullback

#check Over.comp_left

#exit

/-- The second component of `polyPair` is a comparison map of pullbacks composed with `genPb.u₂`. -/
theorem polyPair_snd_eq_comp_u₂' {Γ X : C} (P : UvPoly E B) (be : Γ ⟶ P.functor.obj X) :
    (P.polyPair be).snd = pullback.map (P.polyPair be).fst P.p (P.fstProj X) P.p be (𝟙 _) (𝟙 _) (by simp [polyPair]) (by simp) ≫ (ev P X) := by
  simp only [polyPair, ev, homEquiv_counit, Over.comp_left, ← assoc]
  congr 2
  sorry --aesop_cat


/-- Universal property of the polynomial functor. -/
@[simps]
def equiv (P : UvPoly E B) (Γ : C) (X : C) :
    (Γ ⟶ P.functor.obj X) ≃ (b : Γ ⟶ B) × (pullback b P.p ⟶ X) where
  toFun := P.polyPair
  invFun := fun ⟨b, e⟩ => P.PartialProduct.liftAux b e
  left_inv be := by
    simp_rw [polyPair, liftAux, ← forgetAdjStar.homEquiv_symm]
    simp
  right_inv := by
    intro ⟨b, e⟩
    dsimp [polyPair, liftAux]
    have := Over.forgetAdjStar.homEquiv (X := (Over.pullback P.p).obj (Over.mk b)) (f := e)
    simp at this
    rw [this]
    set pairHat := P.exp.adj.homEquiv _ _ _
    congr! with h
    · simpa [-w] using pairHat.w
    · -- We deal with HEq/dependency by precomposing with an iso
      let i : Over.mk (pairHat.left ≫ P.fstProj X) ≅ Over.mk b :=
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
      generalize (hasPullbackHorizPaste .. : HasPullback (pairHat.left ≫ P.fstProj X) P.p) = pf
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
  . simp [polyPair, partialProduct.liftAux]
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
      rw [homMk_comp (w_f := by simp [fstProj, functor]) (w_g := by simp [functor])]
      simp only [UvPoly.functor, Functor.comp_map, forget_map, homMk_eta,
        homEquiv_naturality_right_symm, comp_left, assoc]
      admit
      --rw [show ((Over.pullback E).map f).left ≫ prod.snd = prod.snd ≫ f by simp]
      -- simp only [← assoc]
      -- congr 2
      -- simp only [comp_obj, forget_obj, star_obj_left, homEquiv_counit, id_obj, comp_left,
      --   pullback_obj_left, mk_left, mk_hom, pullback_map_left, Over.homMk_left,
      --   pullback.congrHom_hom, ← assoc]
      -- congr 1
      -- ext <;> simp

/-- The domain of the composition of two polynomials. See `UvPoly.comp`. -/
def compDom {E B D A : C} (P : UvPoly E B) (Q : UvPoly D A) :=
  pullback Q.p (genericPullback.ev P A)

/-- The codomain of the composition of two polynomials. See `UvPoly.comp`. -/
def compCod {E B D A : C} (P : UvPoly E B) (_ : UvPoly D A) :=
  P.functor.obj A

@[simps!]
def comp [HasPullbacks C] [HasTerminal C]
    {E B D A : C} (P : UvPoly E B) (Q : UvPoly D A) : UvPoly (compDom P Q) (compCod P Q) :=
   {
     p :=  (pullback.snd Q.p (genericPullback.ev P A)) ≫ (genericPullback.fst P A)
     exp := by sorry
   }

/-- The associated functor of the composition of two polynomials is isomorphic to the composition of the associated functors. -/
def compFunctorIso [HasPullbacks C] [HasTerminal C]
    {E B D C : C} (P : UvPoly E B) (Q : UvPoly D C) :
    P.functor ⋙ Q.functor ≅ (comp P Q).functor := by
  sorry

instance monoidal [HasPullbacks C] [HasTerminal C] : MonoidalCategory (UvPoly.Total C) where
  tensorObj X Y := ⟨comp X.poly Y.poly⟩
  whiskerLeft X Y₁ Y₂ := sorry
  whiskerRight := sorry
  tensorUnit := sorry
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry

end UvPoly






end CategoryTheory

end
