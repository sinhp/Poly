import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Comma.Over

/-! Miscellaneous results that don't fit anywhere else. -/

namespace CategoryTheory

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]

/-! ## Pullbacks -/

@[simp]
lemma Limits.pullback.lift_fst_snd {X Y Z : 𝒞} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (eq) :
    pullback.lift (pullback.fst f g) (pullback.snd f g) eq = 𝟙 (pullback f g) := by
  ext <;> simp

/-! ## `eqToHom` -/

/-- Note: if possible,
it's best to immediately rewrite `eqToHom` to an isomorphism
whose data is not defined by destructing an equality
in the second premise of this lemma. -/
-- If only there was a LiftIsos typeclass to do this for us!
lemma Sigma_hom_ext {X Y : 𝒞} {Z : 𝒟} (P : (X ⟶ Y) → 𝒟)
    (p q : (f : X ⟶ Y) × (P f ⟶ Z))
    (fst_eq : p.fst = q.fst)
    (snd_eq : (h : p.fst = q.fst) → p.snd = eqToHom (h ▸ rfl) ≫ q.snd) :
    p = q := by
  let ⟨b, e⟩ := p
  let ⟨c, f⟩ := q
  cases fst_eq
  simp at snd_eq
  simp [snd_eq]

lemma Limits.pullback.eqToHom_eq_map {X Y Z : 𝒞}
    (f₁ f₂ : X ⟶ Z) (g₁ g₂ : Y ⟶ Z) [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (f_eq : f₁ = f₂) (g_eq : g₁ = g₂) :
    eqToHom (by cases f_eq; cases g_eq; rfl) =
      pullback.map f₁ g₁ f₂ g₂ (𝟙 X) (𝟙 Y) (𝟙 Z) (by simp [f_eq]) (by simp [g_eq]) := by
  cases f_eq; cases g_eq; simp

lemma IsPullback.eqToHom_eq_lift {P' P X Y Z : 𝒞}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (pb : IsPullback fst snd f g) (eq : P' = P) :
    eqToHom eq =
      pb.lift (eqToHom eq ≫ fst) (eqToHom eq ≫ snd) (by simp [pb.w]) := by
  cases eq; apply pb.hom_ext <;> simp

lemma Over.eqToHom_eq_homMk {E B : 𝒞} (f g : E ⟶ B) (eq : f = g)  :
    eqToHom (show (Over.mk f) = (Over.mk g) from eq ▸ rfl) =
      Over.homMk (𝟙 E) (by simp [eq]) := by
  cases eq; rfl

/-! ## Over categories -/

namespace Over

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
lemma homMk_comp {B : 𝒞} {U V W : Over B} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left)
    (fg_comp f_comp g_comp) :
    homMk (f ≫ g) fg_comp = homMk (V := V) f f_comp ≫ homMk (U := V) g g_comp :=
  rfl

@[simp]
lemma left_homMk {B : 𝒞} {U V : Over B} (f : U ⟶ V) (h) :
    homMk f.left h = f :=
  rfl

@[simp]
lemma homMk_id {B : 𝒞} {U : Over B} (h) : homMk (𝟙 U.left) h = 𝟙 U :=
  rfl

-- -- Probably bad as a simp lemma?
-- lemma homMk_id' {E B : 𝒞} {f g : E ⟶ B} (h) :
--     homMk (U := Over.mk f) (V := Over.mk g) (𝟙 E) h =
--       (Over.isoMk (Iso.refl E) (by simpa using h)).hom := by
--   ext; simp

end Over
end CategoryTheory
