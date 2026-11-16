import StringDiagrams.Super.BoxProduct
import StringDiagrams.Super.PiCat
import StringDiagrams.Super.Superalgebra


-- @@ L5-39 verbatim
/-!
# The monoidal category `(SCat, ⊠)`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Example 1.2: the product `A ⊠ B` of supercategories (`BoxProd`, in
`StringDiagrams.Super.BoxProduct`) is functorial in superfunctors, `F ⊠ G : A ⊠ B → A' ⊠ B'`,
`(λ, μ) ↦ (F λ, G μ)`, `f ⊗ g ↦ F f ⊗ G g`.

## Main definitions

* `BoxProd.map F G : Superfunctor k (BoxProd k C D) (BoxProd k C' D')`: the superfunctor
  `F ⊠ G`, with `BoxProd.map_id` (`id ⊠ id = id`) and `BoxProd.map_comp`
  (`(F ≫ F') ⊠ (G ≫ G') = (F ⊠ G) ≫ (F' ⊠ G')`).
* `BoxUnit k`: the unit supercategory `I` (one object, endomorphism superalgebra `k` in even
  parity), with its object in an arbitrary universe.
* `BoxProd.assoc C D E : (C ⊠ D) ⊠ E → C ⊠ (D ⊠ E)`, `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)`, with inverse
  `BoxProd.assocInv` (`assoc_comp_assocInv`, `assocInv_comp_assoc`), natural in the three
  arguments (`map_map_comp_assoc`).
* `BoxProd.lunit C : I ⊠ C → C`, `r ⊗ f ↦ r f`, and `BoxProd.runit C : C ⊠ I → C`,
  `f ⊗ r ↦ r f`, with inverses `lunitInv`, `runitInv` (`f ↦ 1 ⊗ f`, `f ↦ f ⊗ 1`), natural
  (`map_comp_lunit`, `map_comp_runit`).

* `BoxProd.pentagon`, `BoxProd.triangle`: the pentagon and triangle identities, as equalities
  of superfunctors.
* `SCat.instMonoidalCategory`: **the monoidal category `(SCat, ⊠, I)`** of supercategories and
  superfunctors (Brundan–Ellis, after Example 1.2 and before Definition 2.1), with
  `A ⊗ B := A ⊠ B`, `F ⊗ G := F ⊠ G`, unit `I` and the coherence isomorphisms above
  (`SCat.associator_hom_eq_assoc`, `SCat.leftUnitor_hom_eq_lunit`, …).

The coherence maps are isomorphisms of supercategories (superfunctors with inverse
superfunctors); the paper calls them "obvious". The morphism modules of all supercategories
involved live in the universe of `k`, as for `BoxProd`; accordingly the monoidal structure is on
`SCat.{u, u, w} k` for `k : Type u` (supercategories with objects in `Type w` and morphism modules
in `Type u`), and its unit is `BoxUnit.{w} k`.
-/


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-43 verbatim
namespace StringDiagrams


-- @@ L45-45 verbatim
open CategoryTheory Supercategory TensorProduct


-- @@ L47-47 verbatim
universe w u w₁ w₂ w₃ w₄ w₅ w₆


-- @@ L49-49 verbatim
variable {k : Type u} [CommRing k]


-- @@ L51-51 verbatim
namespace Supercategory.Superfunctor


-- @@ L53-57 verbatim
variable {A : Type w₁} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {E : Type w₂} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (obj : A → E) (hom : ∀ X Y : A, (X ⟶ Y) →ₗ[k] (obj X ⟶ obj Y))
  (map_id : ∀ X, hom X X (𝟙 X) = 𝟙 (obj X))
  (map_comp : ∀ {X Y Z : A} (x : X ⟶ Y) (y : Y ⟶ Z), hom X Z (x ≫ y) = hom X Y x ≫ hom Y Z y)


-- @@ L59-66 verbatim
/-- The functor given by an object map and linear maps on morphism modules preserving
identities and composition. -/
@[simps]
def functorOfLinearMaps : A ⥤ E where
  obj := obj
  map {X Y} x := hom X Y x
  map_id := map_id
  map_comp := map_comp


-- @@ L68-69 verbatim
instance : (functorOfLinearMaps obj hom map_id map_comp).Additive where
  map_add {X Y x y} := (hom X Y).map_add x y


-- @@ L71-72 verbatim
instance : (functorOfLinearMaps obj hom map_id map_comp).Linear k where
  map_smul {X Y} x r := (hom X Y).map_smul r x


-- @@ L74-80 verbatim
/-- The superfunctor given by an object map and parity-preserving linear maps on morphism
superspaces preserving identities and composition. -/
def ofLinearMaps
    (map_mem : ∀ {X Y : A} {p : ZMod 2} {x : X ⟶ Y}, x ∈ parity (R := k) X Y p →
      hom X Y x ∈ parity (R := k) (obj X) (obj Y) p) : Superfunctor k A E where
  toFunctor := functorOfLinearMaps obj hom map_id map_comp
  isSuperfunctor := ⟨map_mem⟩


-- @@ L82-88 verbatim
/-- A linear map on morphism superspaces commuting with the parity projections preserves
parities. -/
theorem mem_parity_of_proj {X Y : A} {X' Y' : E} (φ : (X ⟶ Y) →ₗ[k] (X' ⟶ Y'))
    (h : ∀ (p : ZMod 2) (x : X ⟶ Y), φ (proj k p x) = proj k p (φ x)) {p : ZMod 2} {x : X ⟶ Y}
    (hx : x ∈ parity (R := k) X Y p) : φ x ∈ parity (R := k) X' Y' p := by
  rw [mem_iff_proj] at hx ⊢
  rw [← h, hx]


-- @@ L90-97 verbatim
/-- A linear map sending a homogeneous `x` to a morphism of the same parity commutes with the
parity projections at `x`. -/
theorem map_proj_of_mem {X Y : A} {X' Y' : E} (φ : (X ⟶ Y) →ₗ[k] (X' ⟶ Y')) {q : ZMod 2}
    {x : X ⟶ Y} (hx : x ∈ parity (R := k) X Y q) (hφ : φ x ∈ parity (R := k) X' Y' q)
    (p : ZMod 2) : φ (proj k p x) = proj k p (φ x) := by
  by_cases h : q = p
  · subst h; rw [proj_of_mem hx, proj_of_mem hφ]
  · rw [proj_of_mem_ne hx h, proj_of_mem_ne hφ h, map_zero]


-- @@ L99-99 verbatim
end Supercategory.Superfunctor


-- @@ L101-101 verbatim
/-! ## The unit supercategory -/


-- @@ L103-108 verbatim
/-- **Brundan–Ellis, after Example 1.2.** The unit supercategory `I`: one object, with
endomorphism superalgebra `k` concentrated in even parity. This is the supercategory
`UnitSupercat k` of `StringDiagrams.Super.Superalgebra`, with its object in an arbitrary
universe `w` (so that it is an object of `SCat` in every universe). -/
@[nolint unusedArguments]
def BoxUnit (k : Type u) [CommRing k] : Type w := PUnit.{w + 1}


-- @@ L110-110 verbatim
namespace BoxUnit


-- @@ L112-113 verbatim
/-- The only object. -/
def star : BoxUnit.{w, u} k := PUnit.unit


-- @@ L115-121 verbatim
instance : Category.{u} (BoxUnit.{w, u} k) where
  Hom _ _ := k
  id _ := (1 : k)
  comp f g := (g : k) * f
  id_comp f := mul_one (f : k)
  comp_id f := one_mul (f : k)
  assoc f g h := (mul_assoc (h : k) g f).symm


-- @@ L123-126 verbatim
instance : Preadditive (BoxUnit.{w, u} k) where
  homGroup _ _ := inferInstanceAs (AddCommGroup k)
  add_comp _ _ _ f f' g := mul_add (g : k) f f'
  comp_add _ _ _ f g g' := add_mul (g : k) g' f


-- @@ L128-131 verbatim
instance : Linear k (BoxUnit.{w, u} k) where
  homModule _ _ := inferInstanceAs (Module k k)
  smul_comp _ _ _ r f g := mul_smul_comm r (g : k) f
  comp_smul _ _ _ f r g := smul_mul_assoc r (g : k) f


-- @@ L133-138 verbatim
instance : Supercategory k (BoxUnit.{w, u} k) where
  parity _ _ p := trivialGrading k p
  isInternal _ _ := isInternal_trivialGrading
  id_mem _ := by rw [trivialGrading_zero]; trivial
  comp_mem {_ _ _ p q f g} hf hg := by
    rw [add_comm]; exact SetLike.GradedMul.mul_mem (A := trivialGrading k) hg hf


-- @@ L140-141 verbatim
theorem comp_eq {X Y Z : BoxUnit.{w, u} k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : k) = (g : k) * (f : k) := rfl


-- @@ L143-143 verbatim
theorem id_eq (X : BoxUnit.{w, u} k) : (𝟙 X : k) = 1 := rfl


-- @@ L145-148 verbatim
/-- Every morphism of `I` is even. -/
theorem mem_parity_zero {X Y : BoxUnit.{w, u} k} (f : X ⟶ Y) : f ∈ parity (R := k) X Y 0 := by
  change (f : k) ∈ trivialGrading k 0
  rw [trivialGrading_zero]; trivial


-- @@ L150-150 verbatim
end BoxUnit


-- @@ L152-152 verbatim
namespace BoxProd


-- @@ L154-159 verbatim
variable {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  {C' : Type w₃} [Category.{u} C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  {D' : Type w₄} [Category.{u} D'] [Preadditive D'] [Linear k D'] [Supercategory k D']
  {C'' : Type w₅} [Category.{u} C''] [Preadditive C''] [Linear k C''] [Supercategory k C'']
  {D'' : Type w₆} [Category.{u} D''] [Preadditive D''] [Linear k D''] [Supercategory k D'']


-- @@ L161-161 verbatim
/-! ## Superfunctors out of `C ⊠ D` -/


-- @@ L163-170 verbatim
/-- Induction on the morphisms `(X₁, X₂) ⟶ (Y₁, Y₂)` of `C ⊠ D`, with homogeneous generators
`f ⊗ g`. -/
theorem induction_on_tmulHom {X Y : BoxProd k C D} {P : (X ⟶ Y) → Prop} (x : X ⟶ Y)
    (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd),
      f ∈ parity (R := k) X.fst Y.fst p → g ∈ parity (R := k) X.snd Y.snd q → P (tmulHom f g))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  induction_on_homogeneous (P := P) x zero tmul add



-- @@ L173-185 verbatim
/-- Superfunctors out of `C ⊠ D` agreeing on objects and on the morphisms `f ⊗ g` are equal. -/
theorem superfunctor_ext {E : Type w₃} [Category.{u} E] [Preadditive E] [Linear k E]
    [Supercategory k E] {Φ Ψ : Superfunctor k (BoxProd k C D) E}
    (hobj : ∀ X, Φ.obj X = Ψ.obj X)
    (hmap : ∀ (X Y : BoxProd k C D) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd),
      Φ.map (tmulHom f g) ≍ Ψ.map (tmulHom f g)) :
    Φ = Ψ := by
  refine Superfunctor.ext (CategoryTheory.Functor.ext hobj fun X Y x => ?_)
  induction x using induction_on_tmulHom with
  | zero => simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  | tmul _ _ f g _ _ => exact (conj_eqToHom_iff_heq _ _ (hobj X) (hobj Y)).2 (hmap X Y f g)
  | add x y hx hy =>
    rw [Functor.map_add, Functor.map_add, hx, hy, Preadditive.add_comp, Preadditive.comp_add]


-- @@ L187-191 verbatim
/-- `f ⊗ g` has parity `|f| + |g|`. -/
theorem tmulHom_mem_parity {X Y : BoxProd k C D} {p q : ZMod 2} {f : X.fst ⟶ Y.fst}
    {g : X.snd ⟶ Y.snd} (hf : f ∈ parity (R := k) X.fst Y.fst p)
    (hg : g ∈ parity (R := k) X.snd Y.snd q) : tmulHom f g ∈ parity (R := k) X Y (p + q) :=
  tmul_mem_parity hf hg


-- @@ L193-195 verbatim
theorem tmulHom_zero_left {X Y : BoxProd k C D} (g : X.snd ⟶ Y.snd) :
    tmulHom (0 : X.fst ⟶ Y.fst) g = 0 :=
  zero_tmul _ _


-- @@ L197-199 verbatim
theorem tmulHom_zero_right {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) :
    tmulHom f (0 : X.snd ⟶ Y.snd) = 0 :=
  tmul_zero _ _


-- @@ L201-203 verbatim
theorem tmulHom_zsmul_left {X Y : BoxProd k C D} (n : ℤ) (f : X.fst ⟶ Y.fst)
    (g : X.snd ⟶ Y.snd) : tmulHom (n • f) g = n • tmulHom f g := by
  rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k, tmulHom_smul_left]


-- @@ L205-207 verbatim
theorem tmulHom_zsmul_right {X Y : BoxProd k C D} (n : ℤ) (f : X.fst ⟶ Y.fst)
    (g : X.snd ⟶ Y.snd) : tmulHom f (n • g) = n • tmulHom f g := by
  rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k, tmulHom_smul_right]


-- @@ L209-209 verbatim
/-! ## `F ⊠ G` -/


-- @@ L211-211 verbatim
section Map


-- @@ L213-213 verbatim
variable (F : Superfunctor k C C') (G : Superfunctor k D D')


-- @@ L215-216 verbatim
/-- The objects `(F λ, G μ)` of `C' ⊠ D'`. -/
abbrev mapObj (X : BoxProd k C D) : BoxProd k C' D' := ⟨F.obj X.fst, G.obj X.snd⟩


-- @@ L218-220 verbatim
/-- The linear map `f ⊗ g ↦ F f ⊗ G g` on morphism superspaces. -/
def mapHom (X Y : BoxProd k C D) : (X ⟶ Y) →ₗ[k] (mapObj F G X ⟶ mapObj F G Y) :=
  TensorProduct.map (F.toFunctor.mapLinearMap k) (G.toFunctor.mapLinearMap k)


-- @@ L222-223 verbatim
theorem mapHom_tmul {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    mapHom F G X Y (tmulHom f g) = tmulHom (F.map f) (G.map g) := rfl


-- @@ L225-237 verbatim
theorem mapHom_comp {X Y Z : BoxProd k C D} (x : X ⟶ Y) (y : Y ⟶ Z) :
    mapHom F G X Z (x ≫ y) = mapHom F G X Y x ≫ mapHom F G Y Z y := by
  induction x using induction_on_tmulHom with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b f g hf hg =>
    induction y using induction_on_tmulHom with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d h l hh hl =>
      rw [mapHom_tmul, mapHom_tmul, tmulHom_comp_tmulHom hf g h hl,
        tmulHom_comp_tmulHom (F.map_mem hf) _ _ (G.map_mem hl), map_zsmul, mapHom_tmul]
      simp only [Superfunctor.map, Functor.map_comp]


-- @@ L239-247 verbatim
theorem mapHom_proj {X Y : BoxProd k C D} (p : ZMod 2) (x : X ⟶ Y) :
    mapHom F G X Y (proj k p x) = proj k p (mapHom F G X Y x) := by
  induction x using induction_on_tmulHom with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b f g hf hg =>
    refine Superfunctor.map_proj_of_mem _ (tmulHom_mem_parity hf hg) ?_ p
    rw [mapHom_tmul]
    exact tmulHom_mem_parity (X := mapObj F G X) (Y := mapObj F G Y) (F.map_mem hf) (G.map_mem hg)


-- @@ L249-258 verbatim
/-- **Brundan–Ellis, after Example 1.2.** The superfunctor `F ⊠ G : C ⊠ D → C' ⊠ D'`,
`(λ, μ) ↦ (F λ, G μ)`, `f ⊗ g ↦ F f ⊗ G g`. -/
def map : Superfunctor k (BoxProd k C D) (BoxProd k C' D') :=
  Superfunctor.ofLinearMaps (mapObj F G) (mapHom F G)
    (fun X => by
      change mapHom F G X X (tmulHom (𝟙 X.fst) (𝟙 X.snd)) = tmulHom (𝟙 _) (𝟙 _)
      rw [mapHom_tmul, Superfunctor.map, Superfunctor.map, F.toFunctor.map_id,
        G.toFunctor.map_id])
    (fun x y => mapHom_comp F G x y)
    (Superfunctor.mem_parity_of_proj _ fun p x => mapHom_proj F G p x)


-- @@ L260-261 verbatim
@[simp] theorem map_obj (X : BoxProd k C D) : (map F G).obj X = ⟨F.obj X.fst, G.obj X.snd⟩ :=
  rfl


-- @@ L263-263 verbatim
theorem map_map {X Y : BoxProd k C D} (x : X ⟶ Y) : (map F G).map x = mapHom F G X Y x := rfl


-- @@ L265-266 verbatim
@[simp] theorem map_tmulHom {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    (map F G).map (tmulHom f g) = tmulHom (F.map f) (G.map g) := rfl


-- @@ L268-268 verbatim
end Map


-- @@ L270-272 verbatim
/-- **Brundan–Ellis, after Example 1.2.** `id ⊠ id = id`. -/
theorem map_id : map (Superfunctor.id k C) (Superfunctor.id k D) = Superfunctor.id k _ :=
  superfunctor_ext (fun _ => rfl) fun _ _ _ _ => HEq.rfl


-- @@ L274-279 verbatim
/-- **Brundan–Ellis, after Example 1.2.** `⊠` is compatible with composition of
superfunctors: `(F ≫ F') ⊠ (G ≫ G') = (F ⊠ G) ≫ (F' ⊠ G')`. -/
theorem map_comp (F : Superfunctor k C C') (F' : Superfunctor k C' C'')
    (G : Superfunctor k D D') (G' : Superfunctor k D' D'') :
    map (F.comp F') (G.comp G') = (map F G).comp (map F' G') :=
  superfunctor_ext (fun _ => rfl) fun _ _ _ _ => HEq.rfl


-- @@ L281-281 verbatim
/-! ## The associator `(C ⊠ D) ⊠ E ≅ C ⊠ (D ⊠ E)` -/


-- @@ L283-283 verbatim
section Assoc


-- @@ L285-286 verbatim
variable {E : Type w₅} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {E' : Type w₆} [Category.{u} E'] [Preadditive E'] [Linear k E'] [Supercategory k E']


-- @@ L288-304 verbatim
/-- Induction on `Hom(((X₁, X₂), X₃), ((Y₁, Y₂), Y₃))` with homogeneous generators
`(f ⊗ g) ⊗ h`. -/
theorem induction_on_homogeneous₃ {X Y : BoxProd k (BoxProd k C D) E} {P : (X ⟶ Y) → Prop}
    (x : X ⟶ Y) (zero : P 0)
    (tmul : ∀ (a b c : ZMod 2) (f : X.fst.fst ⟶ Y.fst.fst) (g : X.fst.snd ⟶ Y.fst.snd)
      (h : X.snd ⟶ Y.snd), f ∈ parity (R := k) _ _ a → g ∈ parity (R := k) _ _ b →
      h ∈ parity (R := k) _ _ c → P (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using induction_on_tmulHom with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul p c y h hy hh =>
    clear hy
    induction y using induction_on_tmulHom with
    | zero => convert zero using 1; exact zero_tmul _ _
    | add y y' h₁ h₂ => convert add _ _ h₁ h₂ using 1; exact add_tmul _ _ _
    | tmul a b f g hf hg => exact tmul a b c f g h hf hg hh


-- @@ L306-322 verbatim
/-- Induction on `Hom((X₁, (X₂, X₃)), (Y₁, (Y₂, Y₃)))` with homogeneous generators
`f ⊗ (g ⊗ h)`. -/
theorem induction_on_homogeneous₃' {X Y : BoxProd k C (BoxProd k D E)} {P : (X ⟶ Y) → Prop}
    (x : X ⟶ Y) (zero : P 0)
    (tmul : ∀ (a b c : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd.fst ⟶ Y.snd.fst)
      (h : X.snd.snd ⟶ Y.snd.snd), f ∈ parity (R := k) _ _ a → g ∈ parity (R := k) _ _ b →
      h ∈ parity (R := k) _ _ c → P (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using induction_on_tmulHom with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul a p f y hf hy =>
    clear hy
    induction y using induction_on_tmulHom with
    | zero => convert zero using 1; exact tmul_zero _ _
    | add y y' h₁ h₂ => convert add _ _ h₁ h₂ using 1; exact tmul_add _ _ _
    | tmul b c g h hg hh => exact tmul a b c f g h hf hg hh


-- @@ L324-327 verbatim
variable (C D E) in
/-- The objects `(λ, (μ, ν))` of `C ⊠ (D ⊠ E)`. -/
abbrev assocObj (X : BoxProd k (BoxProd k C D) E) : BoxProd k C (BoxProd k D E) :=
  ⟨X.fst.fst, ⟨X.fst.snd, X.snd⟩⟩


-- @@ L329-332 verbatim
variable (C D E) in
/-- The objects `((λ, μ), ν)` of `(C ⊠ D) ⊠ E`. -/
abbrev assocInvObj (X : BoxProd k C (BoxProd k D E)) : BoxProd k (BoxProd k C D) E :=
  ⟨⟨X.fst, X.snd.fst⟩, X.snd.snd⟩


-- @@ L334-338 verbatim
/-- `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)` on morphism superspaces. -/
def assocHom (X Y : BoxProd k (BoxProd k C D) E) :
    (X ⟶ Y) →ₗ[k] (assocObj C D E X ⟶ assocObj C D E Y) :=
  (TensorProduct.assoc k (X.fst.fst ⟶ Y.fst.fst) (X.fst.snd ⟶ Y.fst.snd)
    (X.snd ⟶ Y.snd)).toLinearMap


-- @@ L340-344 verbatim
/-- `f ⊗ (g ⊗ h) ↦ (f ⊗ g) ⊗ h` on morphism superspaces. -/
def assocInvHom (X Y : BoxProd k C (BoxProd k D E)) :
    (X ⟶ Y) →ₗ[k] (assocInvObj C D E X ⟶ assocInvObj C D E Y) :=
  (TensorProduct.assoc k (X.fst ⟶ Y.fst) (X.snd.fst ⟶ Y.snd.fst)
    (X.snd.snd ⟶ Y.snd.snd)).symm.toLinearMap


-- @@ L346-351 verbatim
theorem assocHom_tmul {X Y : BoxProd k (BoxProd k C D) E} (f : X.fst.fst ⟶ Y.fst.fst)
    (g : X.fst.snd ⟶ Y.fst.snd) (h : X.snd ⟶ Y.snd) :
    assocHom X Y (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h) =
      tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y) f
        (tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd) g h) :=
  TensorProduct.assoc_tmul f g h


-- @@ L353-357 verbatim
theorem assocInvHom_tmul {X Y : BoxProd k C (BoxProd k D E)} (f : X.fst ⟶ Y.fst)
    (g : X.snd.fst ⟶ Y.snd.fst) (h : X.snd.snd ⟶ Y.snd.snd) :
    assocInvHom X Y (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)) =
      tmulHom (tmulHom (X := (assocInvObj C D E X).fst) (Y := (assocInvObj C D E Y).fst) f g) h :=
  TensorProduct.assoc_symm_tmul f g h


-- @@ L359-361 verbatim
theorem assocHom_assocInvHom {X Y : BoxProd k C (BoxProd k D E)} (x : X ⟶ Y) :
    assocHom (assocInvObj C D E X) (assocInvObj C D E Y) (assocInvHom X Y x) = x :=
  (TensorProduct.assoc k _ _ _).apply_symm_apply x


-- @@ L363-365 verbatim
theorem assocInvHom_assocHom {X Y : BoxProd k (BoxProd k C D) E} (x : X ⟶ Y) :
    assocInvHom (assocObj C D E X) (assocObj C D E Y) (assocHom X Y x) = x :=
  (TensorProduct.assoc k _ _ _).symm_apply_apply x


-- @@ L367-370 verbatim
theorem assocInvHom_assocHom' {X Y : BoxProd k C (BoxProd k D E)}
    (x : assocInvObj C D E X ⟶ assocInvObj C D E Y) :
    assocInvHom X Y (assocHom (assocInvObj C D E X) (assocInvObj C D E Y) x) = x :=
  (TensorProduct.assoc k _ _ _).symm_apply_apply x


-- @@ L372-378 verbatim
/-- `(f ⊗ g) ⊗ h` has parity `|f| + |g| + |h|`. -/
theorem tmul_tmul_mem_parity {X Y : BoxProd k (BoxProd k C D) E} {a b c : ZMod 2}
    {f : X.fst.fst ⟶ Y.fst.fst} {g : X.fst.snd ⟶ Y.fst.snd} {h : X.snd ⟶ Y.snd}
    (hf : f ∈ parity (R := k) _ _ a) (hg : g ∈ parity (R := k) _ _ b)
    (hh : h ∈ parity (R := k) _ _ c) :
    tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h ∈ parity (R := k) X Y (a + b + c) :=
  tmul_mem_parity (tmul_mem_parity (X := X.fst) (Y := Y.fst) hf hg) hh


-- @@ L380-387 verbatim
/-- `f ⊗ (g ⊗ h)` has parity `|f| + |g| + |h|`. -/
theorem tmul_tmul_mem_parity' {X Y : BoxProd k C (BoxProd k D E)} {a b c : ZMod 2}
    {f : X.fst ⟶ Y.fst} {g : X.snd.fst ⟶ Y.snd.fst} {h : X.snd.snd ⟶ Y.snd.snd}
    (hf : f ∈ parity (R := k) _ _ a) (hg : g ∈ parity (R := k) _ _ b)
    (hh : h ∈ parity (R := k) _ _ c) :
    tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h) ∈
      parity (R := k) X Y (a + b + c) := by
  rw [add_assoc]; exact tmul_mem_parity hf (tmul_mem_parity (X := X.snd) (Y := Y.snd) hg hh)


-- @@ L389-408 verbatim
theorem assocHom_comp {X Y Z : BoxProd k (BoxProd k C D) E} (x : X ⟶ Y) (y : Y ⟶ Z) :
    assocHom X Z (x ≫ y) = assocHom X Y x ≫ assocHom Y Z y := by
  induction x using induction_on_homogeneous₃ with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b c f g h hf hg hh =>
    induction y using induction_on_homogeneous₃ with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul a' b' c' f' g' h' hf' hg' hh' =>
      rw [tmulHom_comp_tmulHom (tmulHom_mem_parity (X := X.fst) (Y := Y.fst) hf hg) _ _ hh',
        tmulHom_comp_tmulHom hf _ _ hg', assocHom_tmul, assocHom_tmul,
        tmulHom_comp_tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y)
          (Z := assocObj C D E Z) hf _ _ (tmulHom_mem_parity (X := (assocObj C D E Y).snd) (Y := (assocObj C D E Z).snd) hg' hh'),
        tmulHom_comp_tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd)
          (Z := (assocObj C D E Z).snd) hg _ _ hh']
      rw [tmulHom_zsmul_left, map_zsmul, map_zsmul, assocHom_tmul, tmulHom_zsmul_right, smul_smul,
        smul_smul, koszulSign_add_left, koszulSign_add_right]
      congr 1
      ring


-- @@ L410-418 verbatim
theorem assocHom_proj {X Y : BoxProd k (BoxProd k C D) E} (p : ZMod 2) (x : X ⟶ Y) :
    assocHom X Y (proj k p x) = proj k p (assocHom X Y x) := by
  induction x using induction_on_homogeneous₃ with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b c f g h hf hg hh =>
    refine Superfunctor.map_proj_of_mem _ (tmul_tmul_mem_parity hf hg hh) ?_ p
    rw [assocHom_tmul]
    exact tmul_tmul_mem_parity' hf hg hh


-- @@ L420-424 verbatim
theorem assocInvHom_comp {X Y Z : BoxProd k C (BoxProd k D E)} (x : X ⟶ Y) (y : Y ⟶ Z) :
    assocInvHom X Z (x ≫ y) = assocInvHom X Y x ≫ assocInvHom Y Z y := by
  have h := assocHom_comp (assocInvHom X Y x) (assocInvHom Y Z y)
  rw [assocHom_assocInvHom, assocHom_assocInvHom] at h
  rw [← h, assocInvHom_assocHom']


-- @@ L426-430 verbatim
theorem assocInvHom_proj {X Y : BoxProd k C (BoxProd k D E)} (p : ZMod 2) (x : X ⟶ Y) :
    assocInvHom X Y (proj k p x) = proj k p (assocInvHom X Y x) := by
  have h := assocHom_proj p (assocInvHom X Y x)
  rw [assocHom_assocInvHom] at h
  rw [← h, assocInvHom_assocHom']


-- @@ L432-438 verbatim
variable (C D E) in
/-- **Brundan–Ellis, after Example 1.2.** The associator superfunctor
`(C ⊠ D) ⊠ E → C ⊠ (D ⊠ E)`, `((λ, μ), ν) ↦ (λ, (μ, ν))`, `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)`. -/
def assoc : Superfunctor k (BoxProd k (BoxProd k C D) E) (BoxProd k C (BoxProd k D E)) :=
  Superfunctor.ofLinearMaps (assocObj C D E) assocHom
    (fun X => assocHom_tmul (𝟙 X.fst.fst) (𝟙 X.fst.snd) (𝟙 X.snd)) assocHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => assocHom_proj p x)


-- @@ L440-445 verbatim
variable (C D E) in
/-- The inverse `C ⊠ (D ⊠ E) → (C ⊠ D) ⊠ E` of the associator. -/
def assocInv : Superfunctor k (BoxProd k C (BoxProd k D E)) (BoxProd k (BoxProd k C D) E) :=
  Superfunctor.ofLinearMaps (assocInvObj C D E) assocInvHom
    (fun X => assocInvHom_tmul (𝟙 X.fst) (𝟙 X.snd.fst) (𝟙 X.snd.snd)) assocInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => assocInvHom_proj p x)


-- @@ L447-448 verbatim
@[simp] theorem assoc_obj (X : BoxProd k (BoxProd k C D) E) :
    (assoc C D E).obj X = ⟨X.fst.fst, ⟨X.fst.snd, X.snd⟩⟩ := rfl


-- @@ L450-451 verbatim
@[simp] theorem assocInv_obj (X : BoxProd k C (BoxProd k D E)) :
    (assocInv C D E).obj X = ⟨⟨X.fst, X.snd.fst⟩, X.snd.snd⟩ := rfl


-- @@ L453-458 verbatim
@[simp] theorem assoc_map_tmulHom {X Y : BoxProd k (BoxProd k C D) E}
    (f : X.fst.fst ⟶ Y.fst.fst) (g : X.fst.snd ⟶ Y.fst.snd) (h : X.snd ⟶ Y.snd) :
    (assoc C D E).map (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h) =
      tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y) f
        (tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd) g h) :=
  assocHom_tmul f g h


-- @@ L460-464 verbatim
@[simp] theorem assocInv_map_tmulHom {X Y : BoxProd k C (BoxProd k D E)}
    (f : X.fst ⟶ Y.fst) (g : X.snd.fst ⟶ Y.snd.fst) (h : X.snd.snd ⟶ Y.snd.snd) :
    (assocInv C D E).map (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)) =
      tmulHom (tmulHom (X := (assocInvObj C D E X).fst) (Y := (assocInvObj C D E Y).fst) f g) h :=
  assocInvHom_tmul f g h


-- @@ L466-469 verbatim
/-- The associator is an isomorphism of supercategories: `α ≫ α⁻¹ = id`. -/
theorem assoc_comp_assocInv : (assoc C D E).comp (assocInv C D E) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (assocInvHom_assocHom x))


-- @@ L471-474 verbatim
/-- The associator is an isomorphism of supercategories: `α⁻¹ ≫ α = id`. -/
theorem assocInv_comp_assoc : (assocInv C D E).comp (assoc C D E) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (assocHom_assocInvHom x))


-- @@ L476-485 verbatim
/-- **Naturality of the associator**: `((F ⊠ G) ⊠ H) ≫ α = α ≫ (F ⊠ (G ⊠ H))`. -/
theorem map_map_comp_assoc (F : Superfunctor k C C') (G : Superfunctor k D D')
    (H : Superfunctor k E E') :
    (map (map F G) H).comp (assoc C' D' E') = (assoc C D E).comp (map F (map G H)) := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change assocHom _ _ (mapHom (map F G) H X Y x) = mapHom F (map G H) _ _ (assocHom X Y x)
  induction x using induction_on_homogeneous₃ with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]; rfl
  | tmul a b c f g h _ _ _ => rfl


-- @@ L487-487 verbatim
end Assoc


-- @@ L489-489 verbatim
/-! ## The unitors `I ⊠ C ≅ C` and `C ⊠ I ≅ C` -/


-- @@ L491-491 verbatim
section Unitors


-- @@ L493-495 verbatim
/-- The linear map `r ⊗ f ↦ r f` on morphism superspaces of `I ⊠ C`. -/
def lunitHom (X Y : BoxProd k (BoxUnit.{w, u} k) C) : (X ⟶ Y) →ₗ[k] (X.snd ⟶ Y.snd) :=
  (TensorProduct.lid k (X.snd ⟶ Y.snd)).toLinearMap


-- @@ L497-500 verbatim
/-- The linear map `f ↦ 1 ⊗ f` on morphism superspaces of `C`. -/
def lunitInvHom (X Y : C) :
    (X ⟶ Y) →ₗ[k] ((⟨BoxUnit.star, X⟩ : BoxProd k (BoxUnit.{w, u} k) C) ⟶ ⟨BoxUnit.star, Y⟩) :=
  (TensorProduct.lid k (X ⟶ Y)).symm.toLinearMap


-- @@ L502-504 verbatim
/-- The linear map `f ⊗ r ↦ r f` on morphism superspaces of `C ⊠ I`. -/
def runitHom (X Y : BoxProd k C (BoxUnit.{w, u} k)) : (X ⟶ Y) →ₗ[k] (X.fst ⟶ Y.fst) :=
  (TensorProduct.rid k (X.fst ⟶ Y.fst)).toLinearMap


-- @@ L506-509 verbatim
/-- The linear map `f ↦ f ⊗ 1` on morphism superspaces of `C`. -/
def runitInvHom (X Y : C) :
    (X ⟶ Y) →ₗ[k] ((⟨X, BoxUnit.star⟩ : BoxProd k C (BoxUnit.{w, u} k)) ⟶ ⟨Y, BoxUnit.star⟩) :=
  (TensorProduct.rid k (X ⟶ Y)).symm.toLinearMap


-- @@ L511-513 verbatim
theorem lunitHom_tmul {X Y : BoxProd k (BoxUnit.{w, u} k) C} (r : X.fst ⟶ Y.fst)
    (f : X.snd ⟶ Y.snd) : lunitHom X Y (tmulHom r f) = (r : k) • f :=
  TensorProduct.lid_tmul f r


-- @@ L515-517 verbatim
theorem lunitInvHom_apply {X Y : C} (f : X ⟶ Y) :
    lunitInvHom.{w} (k := k) X Y f = tmulHom (X := ⟨BoxUnit.star, X⟩) (Y := ⟨BoxUnit.star, Y⟩) (1 : k) f :=
  TensorProduct.lid_symm_apply f


-- @@ L519-521 verbatim
theorem runitHom_tmul {X Y : BoxProd k C (BoxUnit.{w, u} k)} (f : X.fst ⟶ Y.fst)
    (r : X.snd ⟶ Y.snd) : runitHom X Y (tmulHom f r) = (r : k) • f :=
  TensorProduct.rid_tmul f r


-- @@ L523-525 verbatim
theorem runitInvHom_apply {X Y : C} (f : X ⟶ Y) :
    runitInvHom.{w} (k := k) X Y f = tmulHom (X := ⟨X, BoxUnit.star⟩) (Y := ⟨Y, BoxUnit.star⟩) f (1 : k) :=
  TensorProduct.rid_symm_apply f


-- @@ L527-528 verbatim
theorem lunitHom_lunitInvHom {X Y : C} (f : X ⟶ Y) : lunitHom _ _ (lunitInvHom.{w} (k := k) X Y f) = f :=
  (TensorProduct.lid k (X ⟶ Y)).apply_symm_apply f


-- @@ L530-533 verbatim
theorem lunitInvHom_lunitHom' {X Y : C}
    (x : (⟨BoxUnit.star, X⟩ : BoxProd k (BoxUnit.{w, u} k) C) ⟶ ⟨BoxUnit.star, Y⟩) :
    lunitInvHom X Y (lunitHom _ _ x) = x :=
  (TensorProduct.lid k (X ⟶ Y)).symm_apply_apply x


-- @@ L535-537 verbatim
theorem lunitInvHom_lunitHom {X Y : BoxProd k (BoxUnit.{w, u} k) C} (x : X ⟶ Y) :
    lunitInvHom X.snd Y.snd (lunitHom X Y x) = x :=
  (TensorProduct.lid k (X.snd ⟶ Y.snd)).symm_apply_apply x


-- @@ L539-540 verbatim
theorem runitHom_runitInvHom {X Y : C} (f : X ⟶ Y) : runitHom _ _ (runitInvHom.{w} (k := k) X Y f) = f :=
  (TensorProduct.rid k (X ⟶ Y)).apply_symm_apply f


-- @@ L542-545 verbatim
theorem runitInvHom_runitHom' {X Y : C}
    (x : (⟨X, BoxUnit.star⟩ : BoxProd k C (BoxUnit.{w, u} k)) ⟶ ⟨Y, BoxUnit.star⟩) :
    runitInvHom X Y (runitHom _ _ x) = x :=
  (TensorProduct.rid k (X ⟶ Y)).symm_apply_apply x


-- @@ L547-549 verbatim
theorem runitInvHom_runitHom {X Y : BoxProd k C (BoxUnit.{w, u} k)} (x : X ⟶ Y) :
    runitInvHom X.fst Y.fst (runitHom X Y x) = x :=
  (TensorProduct.rid k (X.fst ⟶ Y.fst)).symm_apply_apply x


-- @@ L551-563 verbatim
theorem lunitHom_comp {X Y Z : BoxProd k (BoxUnit.{w, u} k) C} (x : X ⟶ Y) (y : Y ⟶ Z) :
    lunitHom X Z (x ≫ y) = lunitHom X Y x ≫ lunitHom Y Z y := by
  induction x using induction_on_tmulHom with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b r f _ _ =>
    induction y using induction_on_tmulHom with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d s g _ hg =>
      rw [tmulHom_comp_tmulHom (BoxUnit.mem_parity_zero r) f s hg,
        koszulSign_zero_left, one_smul, lunitHom_tmul, lunitHom_tmul, lunitHom_tmul,
        Linear.smul_comp, Linear.comp_smul, smul_smul, BoxUnit.comp_eq, mul_comm]


-- @@ L565-577 verbatim
theorem runitHom_comp {X Y Z : BoxProd k C (BoxUnit.{w, u} k)} (x : X ⟶ Y) (y : Y ⟶ Z) :
    runitHom X Z (x ≫ y) = runitHom X Y x ≫ runitHom Y Z y := by
  induction x using induction_on_tmulHom with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b f r hf _ =>
    induction y using induction_on_tmulHom with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d g s _ _ =>
      rw [tmulHom_comp_tmulHom hf r g (BoxUnit.mem_parity_zero s),
        koszulSign_zero_right, one_smul, runitHom_tmul, runitHom_tmul, runitHom_tmul,
        Linear.smul_comp, Linear.comp_smul, smul_smul, BoxUnit.comp_eq, mul_comm]


-- @@ L579-589 verbatim
theorem lunitHom_proj {X Y : BoxProd k (BoxUnit.{w, u} k) C} (p : ZMod 2) (x : X ⟶ Y) :
    lunitHom X Y (proj k p x) = proj k p (lunitHom X Y x) := by
  induction x using induction_on_tmulHom with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b r f _ hf =>
    have h := tmulHom_mem_parity (X := X) (Y := Y) (BoxUnit.mem_parity_zero r) hf
    rw [zero_add] at h
    refine Superfunctor.map_proj_of_mem _ h ?_ p
    rw [lunitHom_tmul]
    exact Submodule.smul_mem _ _ hf


-- @@ L591-601 verbatim
theorem runitHom_proj {X Y : BoxProd k C (BoxUnit.{w, u} k)} (p : ZMod 2) (x : X ⟶ Y) :
    runitHom X Y (proj k p x) = proj k p (runitHom X Y x) := by
  induction x using induction_on_tmulHom with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b f r hf _ =>
    have h := tmulHom_mem_parity (X := X) (Y := Y) hf (BoxUnit.mem_parity_zero r)
    rw [add_zero] at h
    refine Superfunctor.map_proj_of_mem _ h ?_ p
    rw [runitHom_tmul]
    exact Submodule.smul_mem _ _ hf


-- @@ L603-607 verbatim
theorem lunitInvHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lunitInvHom.{w} (k := k) X Z (f ≫ g) = lunitInvHom X Y f ≫ lunitInvHom Y Z g := by
  have h := lunitHom_comp (lunitInvHom.{w} (k := k) X Y f) (lunitInvHom Y Z g)
  rw [lunitHom_lunitInvHom, lunitHom_lunitInvHom] at h
  rw [← h, lunitInvHom_lunitHom']


-- @@ L609-613 verbatim
theorem runitInvHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    runitInvHom.{w} (k := k) X Z (f ≫ g) = runitInvHom X Y f ≫ runitInvHom Y Z g := by
  have h := runitHom_comp (runitInvHom.{w} (k := k) X Y f) (runitInvHom Y Z g)
  rw [runitHom_runitInvHom, runitHom_runitInvHom] at h
  rw [← h, runitInvHom_runitHom']


-- @@ L615-619 verbatim
theorem lunitInvHom_proj {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    lunitInvHom.{w} (k := k) X Y (proj k p f) = proj k p (lunitInvHom X Y f) := by
  have h := lunitHom_proj p (lunitInvHom.{w} (k := k) X Y f)
  rw [lunitHom_lunitInvHom] at h
  rw [← h, lunitInvHom_lunitHom']


-- @@ L621-625 verbatim
theorem runitInvHom_proj {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    runitInvHom.{w} (k := k) X Y (proj k p f) = proj k p (runitInvHom X Y f) := by
  have h := runitHom_proj p (runitInvHom.{w} (k := k) X Y f)
  rw [runitHom_runitInvHom] at h
  rw [← h, runitInvHom_runitHom']


-- @@ L627-633 verbatim
variable (C) in
/-- **Brundan–Ellis, after Example 1.2.** The left unitor `I ⊠ C → C`, `(⋆, λ) ↦ λ`,
`r ⊗ f ↦ r f`. -/
def lunit : Superfunctor k (BoxProd k (BoxUnit.{w, u} k) C) C :=
  Superfunctor.ofLinearMaps (fun X => X.snd) lunitHom
    (fun X => (lunitHom_tmul (𝟙 X.fst) (𝟙 X.snd)).trans (one_smul k _)) lunitHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => lunitHom_proj p x)


-- @@ L635-640 verbatim
variable (C) in
/-- The inverse `C → I ⊠ C`, `λ ↦ (⋆, λ)`, `f ↦ 1 ⊗ f`, of the left unitor. -/
def lunitInv : Superfunctor k C (BoxProd k (BoxUnit.{w, u} k) C) :=
  Superfunctor.ofLinearMaps (fun X => ⟨BoxUnit.star, X⟩) lunitInvHom.{w}
    (fun X => lunitInvHom_apply (𝟙 X)) lunitInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => lunitInvHom_proj.{w} p x)


-- @@ L642-648 verbatim
variable (C) in
/-- **Brundan–Ellis, after Example 1.2.** The right unitor `C ⊠ I → C`, `(λ, ⋆) ↦ λ`,
`f ⊗ r ↦ r f`. -/
def runit : Superfunctor k (BoxProd k C (BoxUnit.{w, u} k)) C :=
  Superfunctor.ofLinearMaps (fun X => X.fst) runitHom
    (fun X => (runitHom_tmul (𝟙 X.fst) (𝟙 X.snd)).trans (one_smul k _)) runitHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => runitHom_proj p x)


-- @@ L650-655 verbatim
variable (C) in
/-- The inverse `C → C ⊠ I`, `λ ↦ (λ, ⋆)`, `f ↦ f ⊗ 1`, of the right unitor. -/
def runitInv : Superfunctor k C (BoxProd k C (BoxUnit.{w, u} k)) :=
  Superfunctor.ofLinearMaps (fun X => ⟨X, BoxUnit.star⟩) runitInvHom.{w}
    (fun X => runitInvHom_apply (𝟙 X)) runitInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => runitInvHom_proj.{w} p x)


-- @@ L657-659 verbatim
@[simp] theorem lunit_map_tmulHom {X Y : BoxProd k (BoxUnit.{w, u} k) C} (r : X.fst ⟶ Y.fst)
    (f : X.snd ⟶ Y.snd) : (lunit C).map (tmulHom r f) = (r : k) • f :=
  lunitHom_tmul r f


-- @@ L661-663 verbatim
@[simp] theorem runit_map_tmulHom {X Y : BoxProd k C (BoxUnit.{w, u} k)} (f : X.fst ⟶ Y.fst)
    (r : X.snd ⟶ Y.snd) : (runit C).map (tmulHom f r) = (r : k) • f :=
  runitHom_tmul f r


-- @@ L665-668 verbatim
/-- The left unitor is an isomorphism of supercategories: `λ ≫ λ⁻¹ = id`. -/
theorem lunit_comp_lunitInv : (lunit.{w} C).comp (lunitInv C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (lunitInvHom_lunitHom x))


-- @@ L670-673 verbatim
/-- The left unitor is an isomorphism of supercategories: `λ⁻¹ ≫ λ = id`. -/
theorem lunitInv_comp_lunit : (lunitInv.{w} C).comp (lunit C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (lunitHom_lunitInvHom x))


-- @@ L675-678 verbatim
/-- The right unitor is an isomorphism of supercategories: `ρ ≫ ρ⁻¹ = id`. -/
theorem runit_comp_runitInv : (runit.{w} C).comp (runitInv C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (runitInvHom_runitHom x))


-- @@ L680-683 verbatim
/-- The right unitor is an isomorphism of supercategories: `ρ⁻¹ ≫ ρ = id`. -/
theorem runitInv_comp_runit : (runitInv.{w} C).comp (runit C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (runitHom_runitInvHom x))


-- @@ L685-696 verbatim
/-- **Naturality of the left unitor**: `(id_I ⊠ F) ≫ λ = λ ≫ F`. -/
theorem map_comp_lunit (F : Superfunctor k C C') :
    (map (Superfunctor.id k (BoxUnit.{w, u} k)) F).comp (lunit C') = (lunit C).comp F := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change lunitHom _ _ (mapHom _ F X Y x) = F.map (lunitHom X Y x)
  induction x using induction_on_tmulHom with
  | zero => rw [map_zero, map_zero, map_zero]; exact (F.toFunctor.map_zero _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]; exact (F.toFunctor.map_add).symm
  | tmul a b r f _ _ =>
    rw [mapHom_tmul, lunitHom_tmul, lunitHom_tmul]
    exact (F.toFunctor.map_smul _ _).symm


-- @@ L698-709 verbatim
/-- **Naturality of the right unitor**: `(F ⊠ id_I) ≫ ρ = ρ ≫ F`. -/
theorem map_comp_runit (F : Superfunctor k C C') :
    (map F (Superfunctor.id k (BoxUnit.{w, u} k))).comp (runit C') = (runit C).comp F := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change runitHom _ _ (mapHom F _ X Y x) = F.map (runitHom X Y x)
  induction x using induction_on_tmulHom with
  | zero => rw [map_zero, map_zero, map_zero]; exact (F.toFunctor.map_zero _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]; exact (F.toFunctor.map_add).symm
  | tmul a b f r _ _ =>
    rw [mapHom_tmul, runitHom_tmul, runitHom_tmul]
    exact (F.toFunctor.map_smul _ _).symm


-- @@ L711-711 verbatim
end Unitors


-- @@ L713-713 verbatim
/-! ## Coherence -/


-- @@ L715-715 verbatim
section Coherence


-- @@ L717-718 verbatim
variable {E : Type w₅} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {E' : Type w₆} [Category.{u} E'] [Preadditive E'] [Linear k E'] [Supercategory k E']


-- @@ L720-739 verbatim
/-- **The pentagon identity** for the associators of `⊠`:
`(α ⊠ id) ≫ α ≫ (id ⊠ α) = α ≫ α` as superfunctors `((C ⊠ D) ⊠ E) ⊠ E' → C ⊠ (D ⊠ (E ⊠ E'))`. -/
theorem pentagon :
    (map (assoc C D E) (Superfunctor.id k E')).comp
        ((assoc C (BoxProd k D E) E').comp (map (Superfunctor.id k C) (assoc D E E'))) =
      (assoc (BoxProd k C D) E E').comp (assoc C D (BoxProd k E E')) := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  induction x using induction_on_homogeneous₃ with
  | zero => rw [Functor.map_zero, Functor.map_zero]; rfl
  | add x y hx hy => rw [Functor.map_add, Functor.map_add, hx, hy]; rfl
  | tmul a b c f g h hf _ _ =>
    clear hf
    induction f using induction_on_tmulHom with
    | zero =>
      have h0 : tmulHom (tmulHom (X := X.fst) (Y := Y.fst) (0 : X.fst.fst ⟶ Y.fst.fst) g) h = 0 := by
        rw [tmulHom_zero_left, tmulHom_zero_left]
      rw [h0, Functor.map_zero, Functor.map_zero]; rfl
    | add f f' h₁ h₂ =>
      rw [tmulHom_add_left, tmulHom_add_left, Functor.map_add, Functor.map_add, h₁, h₂]; rfl
    | tmul _ _ _ _ _ _ => rfl


-- @@ L741-756 verbatim
/-- **The triangle identity** for the associator and unitors of `⊠`:
`α ≫ (id ⊠ λ) = ρ ⊠ id` as superfunctors `(C ⊠ I) ⊠ D → C ⊠ D`. -/
theorem triangle :
    (assoc C (BoxUnit.{w, u} k) D).comp (map (Superfunctor.id k C) (lunit D)) =
      map (runit C) (Superfunctor.id k D) := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  induction x using induction_on_homogeneous₃ with
  | zero => rw [Functor.map_zero, Functor.map_zero]; rfl
  | add x y hx hy => rw [Functor.map_add, Functor.map_add, hx, hy]; rfl
  | tmul a b c f r g _ _ _ =>
    change tmulHom (X := ⟨X.fst.fst, X.snd⟩) (Y := ⟨Y.fst.fst, Y.snd⟩) f
        (lunitHom (⟨X.fst.snd, X.snd⟩ : BoxProd k (BoxUnit.{w, u} k) D) ⟨Y.fst.snd, Y.snd⟩
          (tmulHom (X := ⟨X.fst.snd, X.snd⟩) (Y := ⟨Y.fst.snd, Y.snd⟩) r g)) =
      tmulHom (X := ⟨X.fst.fst, X.snd⟩) (Y := ⟨Y.fst.fst, Y.snd⟩)
        (runitHom X.fst Y.fst (tmulHom (X := X.fst) (Y := Y.fst) f r)) g
    rw [lunitHom_tmul, runitHom_tmul, tmulHom_smul_left, tmulHom_smul_right]


-- @@ L758-758 verbatim
end Coherence


-- @@ L760-760 verbatim
end BoxProd


-- @@ L762-762 verbatim
/-! ## The monoidal category `SCat` -/


-- @@ L764-764 verbatim
namespace SCat


-- @@ L766-766 verbatim
open MonoidalCategory


-- @@ L768-784 verbatim
/-- The data of the monoidal structure `⊠` on the category `SCat` of supercategories (with
morphism modules in the universe of `k`) and superfunctors: `A ⊗ B := A ⊠ B`,
`F ⊗ G := F ⊠ G`, unit `I`, and the associator and unitors of `BoxProd`, which are
isomorphisms of supercategories. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SCat.{u, u, w} k) where
  tensorObj A B := SCat.of k (BoxProd k A B)
  whiskerLeft A _ _ G := BoxProd.map (Superfunctor.id k A) G
  whiskerRight F B := BoxProd.map F (Superfunctor.id k B)
  tensorHom F G := BoxProd.map F G
  tensorUnit := SCat.of k (BoxUnit.{w, u} k)
  associator A B C :=
    ⟨BoxProd.assoc A B C, BoxProd.assocInv A B C, BoxProd.assoc_comp_assocInv,
      BoxProd.assocInv_comp_assoc⟩
  leftUnitor A := ⟨BoxProd.lunit A, BoxProd.lunitInv A, BoxProd.lunit_comp_lunitInv,
    BoxProd.lunitInv_comp_lunit⟩
  rightUnitor A := ⟨BoxProd.runit A, BoxProd.runitInv A, BoxProd.runit_comp_runitInv,
    BoxProd.runitInv_comp_runit⟩


-- @@ L786-786 verbatim
theorem tensorObj_def (A B : SCat.{u, u, w} k) : A ⊗ B = SCat.of k (BoxProd k A B) := rfl


-- @@ L788-789 verbatim
theorem tensorHom_def' {A B A' B' : SCat.{u, u, w} k} (F : A ⟶ A') (G : B ⟶ B') :
    F ⊗ₘ G = BoxProd.map F G := rfl


-- @@ L791-791 verbatim
theorem tensorUnit_def : 𝟙_ (SCat.{u, u, w} k) = SCat.of k (BoxUnit.{w, u} k) := rfl


-- @@ L793-794 verbatim
@[simp] theorem associator_hom_eq_assoc (A B C : SCat.{u, u, w} k) :
    (α_ A B C).hom = BoxProd.assoc A B C := rfl


-- @@ L796-797 verbatim
@[simp] theorem associator_inv_eq_assocInv (A B C : SCat.{u, u, w} k) :
    (α_ A B C).inv = BoxProd.assocInv A B C := rfl


-- @@ L799-799 verbatim
@[simp] theorem leftUnitor_hom_eq_lunit (A : SCat.{u, u, w} k) : (λ_ A).hom = BoxProd.lunit A := rfl


-- @@ L801-801 verbatim
@[simp] theorem leftUnitor_inv_eq_lunitInv (A : SCat.{u, u, w} k) : (λ_ A).inv = BoxProd.lunitInv A := rfl


-- @@ L803-803 verbatim
@[simp] theorem rightUnitor_hom_eq_runit (A : SCat.{u, u, w} k) : (ρ_ A).hom = BoxProd.runit A := rfl


-- @@ L805-806 verbatim
@[simp] theorem rightUnitor_inv_eq_runitInv (A : SCat.{u, u, w} k) :
    (ρ_ A).inv = BoxProd.runitInv A := rfl


-- @@ L808-828 verbatim
/-- The pentagon identity in `SCat` (`BoxProd.pentagon`, restated for the monoidal structure;
the proof is repeated since unifying the two statements is slow). -/
theorem pentagon' (W X Y Z : SCat.{u, u, w} k) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun A B x => heq_of_eq ?_)
  induction x using BoxProd.induction_on_homogeneous₃ with
  | zero => rw [Functor.map_zero, Functor.map_zero]; rfl
  | add x y hx hy => rw [Functor.map_add, Functor.map_add, hx, hy]; rfl
  | tmul a b c f g h hf _ _ =>
    clear hf
    induction f using BoxProd.induction_on_tmulHom with
    | zero =>
      have h0 : BoxProd.tmulHom (BoxProd.tmulHom (X := A.fst) (Y := B.fst)
          (0 : A.fst.fst ⟶ B.fst.fst) g) h = 0 := by
        rw [BoxProd.tmulHom_zero_left, BoxProd.tmulHom_zero_left]
      rw [h0, Functor.map_zero, Functor.map_zero]; rfl
    | add f f' h₁ h₂ =>
      rw [BoxProd.tmulHom_add_left, BoxProd.tmulHom_add_left, Functor.map_add, Functor.map_add,
        h₁, h₂]; rfl
    | tmul _ _ _ _ _ _ => rfl


-- @@ L830-845 verbatim
/-- The triangle identity in `SCat` (`BoxProd.triangle`, restated for the monoidal structure). -/
theorem triangle' (X Y : SCat.{u, u, w} k) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun A B x => heq_of_eq ?_)
  induction x using BoxProd.induction_on_homogeneous₃ with
  | zero => rw [Functor.map_zero, Functor.map_zero]; rfl
  | add x y hx hy => rw [Functor.map_add, Functor.map_add, hx, hy]; rfl
  | tmul a b c f r g _ _ _ =>
    change BoxProd.tmulHom (X := ⟨A.fst.fst, A.snd⟩) (Y := ⟨B.fst.fst, B.snd⟩) f
        (BoxProd.lunitHom (⟨A.fst.snd, A.snd⟩ : BoxProd k (BoxUnit.{w, u} k) Y)
          ⟨B.fst.snd, B.snd⟩
          (BoxProd.tmulHom (X := ⟨A.fst.snd, A.snd⟩) (Y := ⟨B.fst.snd, B.snd⟩) r g)) =
      BoxProd.tmulHom (X := ⟨A.fst.fst, A.snd⟩) (Y := ⟨B.fst.fst, B.snd⟩)
        (BoxProd.runitHom A.fst B.fst (BoxProd.tmulHom (X := A.fst) (Y := B.fst) f r)) g
    rw [BoxProd.lunitHom_tmul, BoxProd.runitHom_tmul, BoxProd.tmulHom_smul_left,
      BoxProd.tmulHom_smul_right]


-- @@ L847-859 verbatim
/-- **Brundan–Ellis, after Example 1.2.** `⊠` makes the category `SCat` of supercategories
(with morphism modules in the universe of `k`) and superfunctors into a monoidal category. -/
instance instMonoidalCategory : MonoidalCategory (SCat.{u, u, w} k) where
  tensorHom_def F G := BoxProd.map_comp F (Superfunctor.id k _) (Superfunctor.id k _) G
  id_tensorHom_id _ _ := BoxProd.map_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := (BoxProd.map_comp f₁ g₁ f₂ g₂).symm
  whiskerLeft_id _ _ := BoxProd.map_id
  id_whiskerRight _ _ := BoxProd.map_id
  associator_naturality f₁ f₂ f₃ := BoxProd.map_map_comp_assoc f₁ f₂ f₃
  leftUnitor_naturality f := BoxProd.map_comp_lunit f
  rightUnitor_naturality f := BoxProd.map_comp_runit f
  pentagon := pentagon'
  triangle := triangle'


-- @@ L861-861 verbatim
end SCat


-- @@ L863-863 verbatim
end StringDiagrams


-- @@ L865-865 verbatim
end
