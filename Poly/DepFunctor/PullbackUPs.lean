import Poly.DepFunctor.Sigma

/-! ### Three ways to state the UP of pullbacks -/

open CategoryTheory Functor Limits

universe v u
variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {X Y Z : 𝒞} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

/-! #### 1. Current approach -/

noncomputable def pullbackHomEquiv (W : 𝒞) :
    (W ⟶ pullback f g) ≃ (i : W ⟶ X) × (j : W ⟶ Y) ×' i ≫ f = j ≫ g where
  toFun h := ⟨h ≫ pullback.fst f g, h ≫ pullback.snd f g, by simp[pullback.condition]⟩
  invFun x := pullback.lift x.1 x.2.1 x.2.2
  left_inv _ := pullback.hom_ext (by simp) (by simp)
  right_inv := by rintro ⟨_,_,_⟩; congr!; simp; simp

-- Issue: this kind of naturality statement does not easily compose
-- when equivalences are chained, e.g. using `Equiv.sigmaCongrLeft`.
theorem naturality_left {W W' : 𝒞} (h : W ⟶ W') (k : W' ⟶ pullback f g) :
    let p := pullbackHomEquiv f g W' k
    pullbackHomEquiv f g W (h ≫ k) = ⟨h ≫ p.1, h ≫ p.2.1, by simp [p.2.2]⟩ := by
  dsimp [pullbackHomEquiv]
  congr! 1 with h
  . simp
  . rw! [h]; simp

/-! #### 2. Natural iso. of cone functors -/

/-- Sends `W` to the type of cones on the cospan `👉f👉👈g👈` with apex `W`,
i.e., tuples `(i : W ⟶ X) × (j : W ⟶ Y) ×' (i ≫ f = j ≫ g)`. -/
def pullbackCones : 𝒞ᵒᵖ ⥤ Type v :=
  (cospan f g).cones

omit [HasPullback f g] in
@[simp]
theorem PullbackCone.eta' (c : PullbackCone f g) : PullbackCone.mk c.fst c.snd c.condition = c := by
  dsimp [PullbackCone.mk]
  congr 2
  ext i : 1
  rcases i with _ | ⟨_ | _⟩ <;> simp

omit [HasPullback f g] in
theorem PullbackCone.mk_comp_π {W' : 𝒞} (h : W' ⟶ W) (i : W ⟶ X) (j : W ⟶ Y)
    (eq : (h ≫ i) ≫ f = (h ≫ j) ≫ g) eq' :
    (PullbackCone.mk (h ≫ i) (h ≫ j) eq).π = (const _).map h ≫ (PullbackCone.mk i j eq').π := by
  ext i : 2
  dsimp
  rcases i with _ | ⟨_ | _⟩ <;> simp

/-- We can also define `pullbackCones` using `PullbackCone`, but storing the apex
- bumps up the universe level; and
- forces the use of `eqToHom`. -/
def pullbackCones' : 𝒞ᵒᵖ ⥤ Type (max v u) where
  obj W := { c : PullbackCone f g // W.unop = c.pt }
  map f := fun ⟨c, eq⟩ => ⟨
    PullbackCone.mk
      (f.unop ≫ eqToHom eq ≫ c.fst)
      (f.unop ≫ eqToHom eq ≫ c.snd)
      (by rw! (castMode := .all) [eq]; simp [c.condition]),
    rfl⟩
  map_id _ := by dsimp; ext ⟨_, eq⟩ : 2; rw! [eq]; simp
  map_comp _ _ := by ext : 1; simp

-- This composes more directly than `naturality_left` above.
noncomputable def pullbackConesIso : yoneda.obj (pullback f g) ≅ pullbackCones f g :=
  NatIso.ofComponents
    (fun W => Equiv.toIso {
      toFun h :=
        (PullbackCone.mk
          (h ≫ pullback.fst f g) (h ≫ pullback.snd f g) (by simp [pullback.condition])).π
      invFun c :=
        let c' : PullbackCone f g := ⟨W.unop, c⟩
        pullback.lift c'.fst c'.snd c'.condition
      left_inv _ := by
        dsimp
        ext : 1 <;> simp [PullbackCone.fst, PullbackCone.snd]
      right_inv π := by
        -- Nasty proof because there is good API for `PullbackCone`,
        -- but not for `pullbackCones`.
        dsimp [PullbackCone.mk]
        congr 1 with i
        have := π.naturality (WidePullbackShape.Hom.term .left)
        dsimp at this
        rcases i with _ | ⟨_ | _⟩ <;> simp [PullbackCone.fst, ← this]
    })
    (fun _ => by
      ext : 1
      dsimp
      rw [PullbackCone.mk_comp_π (eq' := by simp [pullback.condition]),
        PullbackCone.mk_comp_π (eq' := by simp [pullback.condition])]
      simp [pullbackCones, Functor.cones])

/-! #### 3. Equivalence with category of cones

I didn't finish constructing this approach as it seems very awkward. -/

@[simps]
def PullbackCone.mkHom {W : 𝒞} (i₁ : W' ⟶ X) (j₁ : W' ⟶ Y) (i₂ : W ⟶ X) (j₂ : W ⟶ Y)
    (eq₁ : i₁ ≫ f = j₁ ≫ g) (eq₂ : i₂ ≫ f = j₂ ≫ g)
    (h : W' ⟶ W) (w_i : h ≫ i₂ = i₁) (w_j : h ≫ j₂ = j₁) :
    PullbackCone.mk i₁ j₁ eq₁ ⟶ PullbackCone.mk i₂ j₂ eq₂ where
  hom := h
  w := by rintro (_ | ⟨_ | _⟩) <;> simp [reassoc_of% w_i, w_i, w_j]

noncomputable def pullbackIso : Over (pullback f g) ≌ PullbackCone f g where
  functor := {
    obj U := PullbackCone.mk (U.hom ≫ pullback.fst f g) (U.hom ≫ pullback.snd f g)
      (by simp [pullback.condition])
    map t := PullbackCone.mkHom f g (h := t.left) (w_i := by simp [t.w]) (w_j := by simp [t.w]) ..
    map_id := by intros; ext : 1; simp
    map_comp := by intros; ext : 1; simp
  }
  inverse := {
    obj c := Over.mk (pullback.lift c.fst c.snd c.condition)
    map t := Over.homMk t.hom (by dsimp; ext <;> simp)
    map_id := by intros; ext : 1; simp
    map_comp := by intros; ext : 1; simp
  }
  unitIso := NatIso.ofComponents (fun X => eqToIso sorry) sorry
  counitIso := NatIso.ofComponents (fun X => eqToIso sorry) sorry
  functor_unitIso_comp := sorry
