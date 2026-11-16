import StringDiagrams.Super.BicategoryOfHcomp
import StringDiagrams.Super.SKar
import StringDiagrams.Super.QPiTwoCategory


-- @@ L5-32 verbatim
/-!
# The idempotent completion of a bicategory

For a bicategory `B`, the *idempotent completion* `KarBicat B` has the same objects, the hom
categories `Karoubi (a ⟶ b)` (Mathlib's idempotent completion: pairs `(f, e)` of a 1-morphism
and an idempotent 2-endomorphism `e` of it), horizontal composition
`(f, e) ≫ (g, e') = (f ≫ g, e ▷ g ≫ f ◁ e')`, and the coherence isomorphisms of `B` composed
with the idempotents. It is a bicategory (`KarBicat.instBicategory`), preadditive and
`R`-linear when `B` is, and its hom categories have finite biproducts when those of `B` do.

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (the
end of the section), a Π-2-category structure (Definition 5.2) and a `(Q, Π)`-2-category
structure (Definition 6.14) on `B` extend to `KarBicat B` (`KarBicat.instPiTwoCategory`,
`KarBicat.instQPiTwoCategory`), with `π_λ`, `q_λ`, `q_λ⁻¹` the images of those of `B` and
`β`, `γ`, `ξ`, `ii`, `jj` composed with the idempotents. Together with the additive envelope
(`StringDiagrams.Super.MatBicategory`) this gives the additive Karoubi envelope of a 2-category
(`StringDiagrams.Super.KarBicategory`).

## Implementation

A 2-morphism `(f, e) ⟶ (f', e')` of `KarBicat B` is a 2-morphism `η : f ⟶ f'` of `B` with
`η = e ≫ η ≫ e'`. The coherence 2-morphisms are of the form `Karoubi.mkHom c h = c ≫ e'` for a
2-morphism `c : f ⟶ f'` of `B` commuting with the idempotents (`h : e ≫ c = c ≫ e'`); these are
closed under composition and whiskering (`Karoubi.mkHom_comp_mkHom`, `KarBicat.whiskerLeft_mkHom`,
`KarBicat.mkHom_whiskerRight`), which reduces the coherence axioms to those of `B`.

Compositions of 1-morphisms are written in diagrammatic order.
-/


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace StringDiagrams


-- @@ L38-38 verbatim
open CategoryTheory Bicategory Idempotents


-- @@ L40-40 verbatim
universe w v u w₁


-- @@ L42-42 verbatim
/-! ## Morphisms of `Karoubi C` from morphisms commuting with the idempotents -/


-- @@ L44-44 verbatim
namespace Karoubi


-- @@ L46-46 verbatim
variable {C : Type u} [Category.{v} C]


-- @@ L48-50 verbatim
/-- The morphism `(X, p) ⟶ (Y, q)` given by `c ≫ q` for `c : X ⟶ Y` with `p ≫ c = c ≫ q`. -/
def mkHom {P Q : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) : P ⟶ Q :=
  ⟨c ≫ Q.p, by rw [Category.assoc, Q.idem, ← Category.assoc, h, Category.assoc, Q.idem]⟩


-- @@ L52-53 verbatim
@[simp] theorem mkHom_f {P Q : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) :
    (mkHom c h).f = c ≫ Q.p := rfl


-- @@ L55-57 verbatim
theorem mkHom_congr {P Q : Karoubi C} {c c' : P.X ⟶ Q.X} (h : P.p ≫ c = c ≫ Q.p)
    (h' : P.p ≫ c' = c' ≫ Q.p) (e : c = c') : mkHom c h = mkHom c' h' := by
  subst e; rfl


-- @@ L59-64 verbatim
theorem mkHom_comp_mkHom {P Q S : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p)
    (c' : Q.X ⟶ S.X) (h' : Q.p ≫ c' = c' ≫ S.p) :
    mkHom c h ≫ mkHom c' h' = mkHom (c ≫ c') (by rw [reassoc_of% h, h', Category.assoc]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, mkHom_f, Category.assoc]
    rw [reassoc_of% h', S.idem])


-- @@ L66-68 verbatim
theorem mkHom_comp_f {P Q S : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) (ψ : Q ⟶ S) :
    (mkHom c h ≫ ψ).f = c ≫ ψ.f := by
  rw [Idempotents.Karoubi.comp_f, mkHom_f, Category.assoc, Idempotents.Karoubi.p_comp]


-- @@ L70-72 verbatim
theorem comp_mkHom_f {P Q S : Karoubi C} (ψ : P ⟶ Q) (c : Q.X ⟶ S.X) (h : Q.p ≫ c = c ≫ S.p) :
    (ψ ≫ mkHom c h).f = ψ.f ≫ c ≫ S.p := by
  rw [Idempotents.Karoubi.comp_f, mkHom_f]


-- @@ L74-75 verbatim
theorem id_eq_mkHom (P : Karoubi C) : 𝟙 P = mkHom (𝟙 P.X) (by simp) :=
  Idempotents.Karoubi.hom_ext _ _ (by simp)


-- @@ L77-79 verbatim
theorem comm_inv {P Q : Karoubi C} (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) :
    Q.p ≫ e.inv = e.inv ≫ P.p := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]


-- @@ L81-92 verbatim
/-- The isomorphism `(X, p) ≅ (Y, q)` given by an isomorphism `e : X ≅ Y` with
`p ≫ e = e ≫ q`. -/
@[simps]
def mkIso {P Q : Karoubi C} (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q where
  hom := mkHom e.hom h
  inv := mkHom e.inv (comm_inv e h)
  hom_inv_id := by
    rw [mkHom_comp_mkHom]
    exact (mkHom_congr _ _ (Iso.hom_inv_id e)).trans (id_eq_mkHom P).symm
  inv_hom_id := by
    rw [mkHom_comp_mkHom]
    exact (mkHom_congr _ _ (Iso.inv_hom_id e)).trans (id_eq_mkHom Q).symm


-- @@ L94-94 verbatim
end Karoubi


-- @@ L96-96 verbatim
/-! ## The idempotent completion of a bicategory -/


-- @@ L98-103 verbatim
/-- The idempotent completion of a bicategory: the same objects, with hom categories the
idempotent completions `Karoubi (a ⟶ b)`. -/
@[ext]
structure KarBicat (B : Type u) where
  /-- The object of `B`. -/
  obj : B


-- @@ L105-105 verbatim
namespace KarBicat


-- @@ L107-107 verbatim
open Karoubi


-- @@ L109-112 verbatim
/-! ### The construction

The category structure and the hom categories are local instances during the construction of
the bicategory; afterwards they are only accessed through `Bicategory (KarBicat B)`. -/


-- @@ L114-114 verbatim
section Construction


-- @@ L116-116 verbatim
variable {B : Type u} [Bicategory.{w, v} B]


-- @@ L118-123 verbatim
/-- The category structure: 1-morphisms `(f, e)` with `e` an idempotent 2-endomorphism of `f`,
composed by `(f, e) ≫ (g, e') = (f ≫ g, e ▷ g ≫ f ◁ e')`. -/
@[reducible] def categoryStruct : CategoryStruct (KarBicat B) where
  Hom a b := Karoubi (a.obj ⟶ b.obj)
  id a := ⟨𝟙 a.obj, 𝟙 _, by simp⟩
  comp P Q := ⟨P.X ≫ Q.X, hcomp₂ P.p Q.p, by rw [← hcomp₂_comp, P.idem, Q.idem]⟩


-- @@ L125-125 verbatim
attribute [local instance] categoryStruct


-- @@ L127-129 verbatim
/-- The hom categories `Karoubi (a ⟶ b)`. -/
@[reducible] def homCategory (a b : KarBicat B) : Category (a ⟶ b) :=
  inferInstanceAs (Category (Karoubi (a.obj ⟶ b.obj)))


-- @@ L131-131 verbatim
attribute [local instance] homCategory


-- @@ L133-133 verbatim
variable {a b c d : KarBicat B}


-- @@ L135-139 verbatim
/-- Horizontal composition of 2-morphisms: the horizontal composite in `B`. -/
def hcomp {P P' : a ⟶ b} {Q Q' : b ⟶ c} (η : P ⟶ P') (θ : Q ⟶ Q') : P ≫ Q ⟶ P' ≫ Q' :=
  ⟨hcomp₂ η.f θ.f, by
    show hcomp₂ P.p Q.p ≫ hcomp₂ η.f θ.f ≫ hcomp₂ P'.p Q'.p = hcomp₂ η.f θ.f
    rw [← hcomp₂_comp, ← hcomp₂_comp, η.comm, θ.comm]⟩


-- @@ L141-142 verbatim
theorem hcomp_f' {P P' : a ⟶ b} {Q Q' : b ⟶ c} (η : P ⟶ P') (θ : Q ⟶ Q') :
    (hcomp η θ).f = hcomp₂ η.f θ.f := rfl


-- @@ L144-144 verbatim
theorem hcomp_id_id (P : a ⟶ b) (Q : b ⟶ c) : hcomp (𝟙 P) (𝟙 Q) = 𝟙 (P ≫ Q) := rfl


-- @@ L146-149 verbatim
theorem hcomp_comp {P₁ P₂ P₃ : a ⟶ b} {Q₁ Q₂ Q₃ : b ⟶ c} (η₁ : P₁ ⟶ P₂) (θ₁ : Q₁ ⟶ Q₂)
    (η₂ : P₂ ⟶ P₃) (θ₂ : Q₂ ⟶ Q₃) :
    hcomp (η₁ ≫ η₂) (θ₁ ≫ θ₂) = hcomp η₁ θ₁ ≫ hcomp η₂ θ₂ :=
  Idempotents.Karoubi.hom_ext _ _ (hcomp₂_comp _ _ _ _)


-- @@ L151-158 verbatim
theorem hcomp_mkHom_id' {P P' : a ⟶ b} (φ : P.X ⟶ P'.X) (h : P.p ≫ φ = φ ≫ P'.p) (Q : b ⟶ c) :
    hcomp (mkHom φ h) (𝟙 Q) = mkHom (φ ▷ Q.X) (by
      show hcomp₂ P.p Q.p ≫ φ ▷ Q.X = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
      rw [← hcomp₂_id_right φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ (φ ≫ P'.p) Q.p = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
    simp only [hcomp₂, comp_whiskerRight, Category.assoc])


-- @@ L160-168 verbatim
theorem hcomp_id_mkHom' (P : a ⟶ b) {Q Q' : b ⟶ c} (φ : Q.X ⟶ Q'.X) (h : Q.p ≫ φ = φ ≫ Q'.p) :
    hcomp (𝟙 P) (mkHom φ h) = mkHom (P.X ◁ φ) (by
      show hcomp₂ P.p Q.p ≫ P.X ◁ φ = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
      rw [← hcomp₂_id_left P.X φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ P.p (φ ≫ Q'.p) = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
    simp only [hcomp₂, Bicategory.whiskerLeft_comp]
    rw [whisker_exchange_assoc])


-- @@ L170-172 verbatim
theorem assoc_comm (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    ((P ≫ Q) ≫ S).p ≫ (α_ P.X Q.X S.X).hom = (α_ P.X Q.X S.X).hom ≫ (P ≫ Q ≫ S).p :=
  hcomp₂_hcomp₂_associator P.p Q.p S.p


-- @@ L174-176 verbatim
theorem assoc_inv_comm (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (P ≫ Q ≫ S).p ≫ (α_ P.X Q.X S.X).inv = (α_ P.X Q.X S.X).inv ≫ ((P ≫ Q) ≫ S).p :=
  hcomp₂_hcomp₂_associator_inv P.p Q.p S.p


-- @@ L178-180 verbatim
theorem leftUnitor_comm (P : a ⟶ b) : (𝟙 a ≫ P).p ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p := by
  show hcomp₂ (𝟙 (𝟙 a.obj)) P.p ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p
  rw [hcomp₂_id_left, leftUnitor_naturality]


-- @@ L182-185 verbatim
theorem leftUnitor_inv_comm (P : a ⟶ b) :
    P.p ≫ (λ_ P.X).inv = (λ_ P.X).inv ≫ (𝟙 a ≫ P).p := by
  show P.p ≫ (λ_ P.X).inv = (λ_ P.X).inv ≫ hcomp₂ (𝟙 (𝟙 a.obj)) P.p
  rw [hcomp₂_id_left, leftUnitor_inv_naturality]


-- @@ L187-189 verbatim
theorem rightUnitor_comm (P : a ⟶ b) : (P ≫ 𝟙 b).p ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p := by
  show hcomp₂ P.p (𝟙 (𝟙 b.obj)) ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p
  rw [hcomp₂_id_right, rightUnitor_naturality]


-- @@ L191-194 verbatim
theorem rightUnitor_inv_comm (P : a ⟶ b) :
    P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ (P ≫ 𝟙 b).p := by
  show P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ hcomp₂ P.p (𝟙 (𝟙 b.obj))
  rw [hcomp₂_id_right, rightUnitor_inv_naturality]


-- @@ L196-198 verbatim
/-- The associator. -/
def associator (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) : (P ≫ Q) ≫ S ≅ P ≫ Q ≫ S :=
  mkIso (α_ P.X Q.X S.X) (assoc_comm P Q S)


-- @@ L200-201 verbatim
/-- The left unitor. -/
def leftUnitor (P : a ⟶ b) : 𝟙 a ≫ P ≅ P := mkIso (λ_ P.X) (leftUnitor_comm P)


-- @@ L203-204 verbatim
/-- The right unitor. -/
def rightUnitor (P : a ⟶ b) : P ≫ 𝟙 b ≅ P := mkIso (ρ_ P.X) (rightUnitor_comm P)


-- @@ L206-207 verbatim
theorem associator_hom' (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (associator P Q S).hom = mkHom (α_ P.X Q.X S.X).hom (assoc_comm P Q S) := rfl


-- @@ L209-210 verbatim
theorem leftUnitor_hom' (P : a ⟶ b) :
    (leftUnitor P).hom = mkHom (λ_ P.X).hom (leftUnitor_comm P) := rfl


-- @@ L212-213 verbatim
theorem rightUnitor_hom' (P : a ⟶ b) :
    (rightUnitor P).hom = mkHom (ρ_ P.X).hom (rightUnitor_comm P) := rfl


-- @@ L215-242 verbatim
/-- **The idempotent completion of a bicategory is a bicategory.** -/
@[reducible] instance instBicategory : Bicategory (KarBicat B) :=
  Bicategory.ofHcomp hcomp associator leftUnitor rightUnitor hcomp_id_id
    (fun η η' θ θ' => hcomp_comp η θ η' θ')
    (fun η θ ι => Idempotents.Karoubi.hom_ext _ _ (by
      rw [associator_hom', associator_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f', hcomp_f',
        hcomp_f', hcomp_f', ← Category.assoc, hcomp₂_hcomp₂_associator, Category.assoc]
      exact congrArg _ (Idempotents.Karoubi.comp_p (hcomp η (hcomp θ ι)))))
    (fun η => Idempotents.Karoubi.hom_ext _ _ (by
      rw [leftUnitor_hom', leftUnitor_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f']
      change hcomp₂ (𝟙 (𝟙 _)) η.f ≫ _ = _
      rw [hcomp₂_id_left, ← Category.assoc, leftUnitor_naturality, Category.assoc,
        Idempotents.Karoubi.comp_p]))
    (fun η => Idempotents.Karoubi.hom_ext _ _ (by
      rw [rightUnitor_hom', rightUnitor_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f']
      change hcomp₂ η.f (𝟙 (𝟙 _)) ≫ _ = _
      rw [hcomp₂_id_right, ← Category.assoc, rightUnitor_naturality, Category.assoc,
        Idempotents.Karoubi.comp_p]))
    (fun P Q S T => by
      rw [associator_hom', associator_hom', associator_hom', associator_hom', associator_hom',
        hcomp_mkHom_id', hcomp_id_mkHom', mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
      refine mkHom_congr _ _ ?_
      exact Bicategory.pentagon _ _ _ _)
    (fun P Q => by
      rw [associator_hom', leftUnitor_hom', rightUnitor_hom', hcomp_mkHom_id', hcomp_id_mkHom',
        mkHom_comp_mkHom]
      refine mkHom_congr _ _ ?_
      exact Bicategory.triangle _ _)


-- @@ L244-244 verbatim
end Construction


-- @@ L246-246 verbatim
/-! ### The bicategory -/


-- @@ L248-248 verbatim
section Basic


-- @@ L250-250 verbatim
variable {B : Type u} [Bicategory.{w, v} B]


-- @@ L252-253 verbatim
/-- A 1-morphism of `B` with the identity idempotent. -/
abbrev of {a b : B} (f : a ⟶ b) : (⟨a⟩ : KarBicat B) ⟶ ⟨b⟩ := ⟨f, 𝟙 f, by simp⟩


-- @@ L255-255 verbatim
@[simp] theorem of_X {a b : B} (f : a ⟶ b) : (of f).X = f := rfl


-- @@ L257-257 verbatim
@[simp] theorem of_p {a b : B} (f : a ⟶ b) : (of f).p = 𝟙 f := rfl


-- @@ L259-259 verbatim
theorem id_eq (a : KarBicat B) : 𝟙 a = of (𝟙 a.obj) := rfl


-- @@ L261-261 verbatim
@[simp] theorem id_X (a : KarBicat B) : (𝟙 a : a ⟶ a).X = 𝟙 a.obj := rfl


-- @@ L263-263 verbatim
@[simp] theorem id_p (a : KarBicat B) : (𝟙 a : a ⟶ a).p = 𝟙 (𝟙 a.obj) := rfl


-- @@ L265-266 verbatim
@[simp] theorem comp_X {a b c : KarBicat B} (P : a ⟶ b) (Q : b ⟶ c) : (P ≫ Q).X = P.X ≫ Q.X :=
  rfl


-- @@ L268-269 verbatim
@[simp] theorem comp_p {a b c : KarBicat B} (P : a ⟶ b) (Q : b ⟶ c) :
    (P ≫ Q).p = hcomp₂ P.p Q.p := rfl


-- @@ L271-271 verbatim
variable {a b c d : KarBicat B}


-- @@ L273-273 verbatim
@[simp] theorem comp_f {P Q S : a ⟶ b} (η : P ⟶ Q) (θ : Q ⟶ S) : (η ≫ θ).f = η.f ≫ θ.f := rfl


-- @@ L275-275 verbatim
@[simp] theorem id_f (P : a ⟶ b) : (𝟙 P : P ⟶ P).f = P.p := rfl


-- @@ L277-278 verbatim
@[simp] theorem whiskerLeft_f (P : a ⟶ b) {Q Q' : b ⟶ c} (θ : Q ⟶ Q') :
    (P ◁ θ).f = hcomp₂ P.p θ.f := rfl


-- @@ L280-281 verbatim
@[simp] theorem whiskerRight_f {P P' : a ⟶ b} (η : P ⟶ P') (Q : b ⟶ c) :
    (η ▷ Q).f = hcomp₂ η.f Q.p := rfl


-- @@ L283-283 verbatim
/-! The lemmas on `Karoubi.mkHom`, restated for the hom categories of `KarBicat B`. -/


-- @@ L285-288 verbatim
theorem mkHom_comp_mkHom {P Q S : a ⟶ b} (φ : P.X ⟶ Q.X) (h : P.p ≫ φ = φ ≫ Q.p)
    (φ' : Q.X ⟶ S.X) (h' : Q.p ≫ φ' = φ' ≫ S.p) :
    mkHom φ h ≫ mkHom φ' h' = mkHom (φ ≫ φ') (by rw [reassoc_of% h, h', Category.assoc]) :=
  Karoubi.mkHom_comp_mkHom φ h φ' h'


-- @@ L290-292 verbatim
theorem mkHom_comp_f {P Q S : a ⟶ b} (φ : P.X ⟶ Q.X) (h : P.p ≫ φ = φ ≫ Q.p) (ψ : Q ⟶ S) :
    (mkHom φ h ≫ ψ).f = φ ≫ ψ.f :=
  Karoubi.mkHom_comp_f φ h ψ


-- @@ L294-296 verbatim
theorem comp_mkHom_f {P Q S : a ⟶ b} (ψ : P ⟶ Q) (φ : Q.X ⟶ S.X) (h : Q.p ≫ φ = φ ≫ S.p) :
    (ψ ≫ mkHom φ h).f = ψ.f ≫ φ ≫ S.p :=
  Karoubi.comp_mkHom_f ψ φ h


-- @@ L298-299 verbatim
theorem id_eq_mkHom (P : a ⟶ b) : 𝟙 P = mkHom (𝟙 P.X) (by simp) :=
  Karoubi.id_eq_mkHom P


-- @@ L301-303 verbatim
theorem mkHom_congr {P Q : a ⟶ b} {φ φ' : P.X ⟶ Q.X} (h : P.p ≫ φ = φ ≫ Q.p)
    (h' : P.p ≫ φ' = φ' ≫ Q.p) (e : φ = φ') : mkHom φ h = mkHom φ' h' :=
  Karoubi.mkHom_congr h h' e


-- @@ L305-306 verbatim
theorem associator_hom_eq (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (α_ P Q S).hom = mkHom (α_ P.X Q.X S.X).hom (assoc_comm P Q S) := rfl


-- @@ L308-309 verbatim
theorem associator_inv_eq (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (α_ P Q S).inv = mkHom (α_ P.X Q.X S.X).inv (assoc_inv_comm P Q S) := rfl


-- @@ L311-311 verbatim
theorem leftUnitor_hom_eq (P : a ⟶ b) : (λ_ P).hom = mkHom (λ_ P.X).hom (leftUnitor_comm P) := rfl


-- @@ L313-314 verbatim
theorem leftUnitor_inv_eq (P : a ⟶ b) :
    (λ_ P).inv = mkHom (λ_ P.X).inv (leftUnitor_inv_comm P) := rfl


-- @@ L316-317 verbatim
theorem rightUnitor_hom_eq (P : a ⟶ b) :
    (ρ_ P).hom = mkHom (ρ_ P.X).hom (rightUnitor_comm P) := rfl


-- @@ L319-320 verbatim
theorem rightUnitor_inv_eq (P : a ⟶ b) :
    (ρ_ P).inv = mkHom (ρ_ P.X).inv (rightUnitor_inv_comm P) := rfl


-- @@ L322-327 verbatim
theorem whiskerLeft_mkHom (P : a ⟶ b) {Q Q' : b ⟶ c} (φ : Q.X ⟶ Q'.X) (h : Q.p ≫ φ = φ ≫ Q'.p) :
    P ◁ mkHom φ h = mkHom (P.X ◁ φ) (by
      show hcomp₂ P.p Q.p ≫ P.X ◁ φ = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
      rw [← hcomp₂_id_left P.X φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  hcomp_id_mkHom' P φ h


-- @@ L329-334 verbatim
theorem mkHom_whiskerRight {P P' : a ⟶ b} (φ : P.X ⟶ P'.X) (h : P.p ≫ φ = φ ≫ P'.p) (Q : b ⟶ c) :
    mkHom φ h ▷ Q = mkHom (φ ▷ Q.X) (by
      show hcomp₂ P.p Q.p ≫ φ ▷ Q.X = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
      rw [← hcomp₂_id_right φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  hcomp_mkHom_id' φ h Q


-- @@ L336-336 verbatim
end Basic


-- @@ L338-338 verbatim
/-! ## Preadditive and linear structure -/


-- @@ L340-340 verbatim
section Preadditive


-- @@ L342-342 verbatim
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]


-- @@ L344-345 verbatim
instance (a b : KarBicat B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Karoubi (a.obj ⟶ b.obj)))


-- @@ L347-347 verbatim
variable {a b : KarBicat B}


-- @@ L349-349 verbatim
@[simp] theorem add_f {P Q : a ⟶ b} (η θ : P ⟶ Q) : (η + θ).f = η.f + θ.f := rfl


-- @@ L351-351 verbatim
@[simp] theorem neg_f {P Q : a ⟶ b} (η : P ⟶ Q) : (-η).f = -η.f := rfl


-- @@ L353-353 verbatim
@[simp] theorem zero_f {P Q : a ⟶ b} : (0 : P ⟶ Q).f = 0 := rfl


-- @@ L355-355 verbatim
variable [PreadditiveBicategory B]


-- @@ L357-361 verbatim
instance instPreadditiveBicategory : PreadditiveBicategory (KarBicat B) where
  whiskerLeft_add P _ _ η θ := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, PreadditiveBicategory.whiskerLeft_add, Preadditive.comp_add])
  add_whiskerRight η θ Q := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, PreadditiveBicategory.add_whiskerRight, Preadditive.add_comp])


-- @@ L363-365 verbatim
instance [∀ a b : B, Limits.HasFiniteBiproducts (a ⟶ b)] (a b : KarBicat B) :
    Limits.HasFiniteBiproducts (a ⟶ b) :=
  inferInstanceAs (Limits.HasFiniteBiproducts (Karoubi (a.obj ⟶ b.obj)))


-- @@ L367-369 verbatim
instance [∀ a b : B, Limits.HasFiniteBiproducts (a ⟶ b)] (a b : KarBicat B) :
    Limits.HasBinaryBiproducts (a ⟶ b) :=
  inferInstanceAs (Limits.HasBinaryBiproducts (Karoubi (a.obj ⟶ b.obj)))


-- @@ L371-372 verbatim
instance (a b : KarBicat B) : IsIdempotentComplete (a ⟶ b) :=
  inferInstanceAs (IsIdempotentComplete (Karoubi (a.obj ⟶ b.obj)))


-- @@ L374-374 verbatim
variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]


-- @@ L376-377 verbatim
instance (a b : KarBicat B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Karoubi (a.obj ⟶ b.obj)))


-- @@ L379-380 verbatim
omit [PreadditiveBicategory B] [LinearBicategory R B] in
@[simp] theorem smul_f {P Q : a ⟶ b} (r : R) (η : P ⟶ Q) : (r • η).f = r • η.f := rfl


-- @@ L382-386 verbatim
instance instLinearBicategory : LinearBicategory R (KarBicat B) where
  whiskerLeft_smul P _ _ r η := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, LinearBicategory.whiskerLeft_smul, Linear.comp_smul])
  smul_whiskerRight r η Q := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, LinearBicategory.smul_whiskerRight, Linear.smul_comp])


-- @@ L388-388 verbatim
end Preadditive


-- @@ L390-390 verbatim
/-! ## Π-2-categories and `(Q, Π)`-2-categories -/


-- @@ L392-392 verbatim
section Pi


-- @@ L394-394 verbatim
variable {B : Type u} [Bicategory.{w, v} B] {a b c d : KarBicat B}


-- @@ L396-401 verbatim
theorem braid_comm {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (P ≫ of q).p ≫ (e P.X).hom = (e P.X).hom ≫ (of q' ≫ P).p := by
  show hcomp₂ P.p (𝟙 q) ≫ (e P.X).hom = (e P.X).hom ≫ hcomp₂ (𝟙 q') P.p
  rw [hcomp₂_id_right, hcomp₂_id_left, he]


-- @@ L403-409 verbatim
/-- The isomorphism `P ≫ q ≅ q' ≫ P` of the idempotent completion determined by natural
isomorphisms `f ≫ q ≅ q' ≫ f` in `B` (for `q = π`, `q'` etc.). -/
def braidIso {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    P ≫ of q ≅ of q' ≫ P :=
  mkIso (e P.X) (braid_comm P e he)


-- @@ L411-414 verbatim
theorem braidIso_hom {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (braidIso P e he).hom = mkHom (e P.X).hom (braid_comm P e he) := rfl


-- @@ L416-421 verbatim
theorem braidIso_inv {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (braidIso P e he).inv =
      mkHom (e P.X).inv (comm_inv (P := P ≫ of q) (Q := of q' ≫ P) (e P.X) (braid_comm P e he)) :=
  rfl


-- @@ L423-435 verbatim
/-- The naturality of `braidIso` with respect to 2-morphisms, from the naturality in `B`. -/
theorem braidIso_naturality {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj}
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom)
    {P P' : a ⟶ b} (η : P ⟶ P') :
    (braidIso P e he).hom ≫ of q' ◁ η = η ▷ of q ≫ (braidIso P' e he).hom := by
  apply Idempotents.Karoubi.hom_ext
  rw [braidIso_hom, braidIso_hom, mkHom_comp_f, comp_mkHom_f, whiskerLeft_f, whiskerRight_f,
    comp_p, of_p, of_p]
  simp only [hcomp₂, Bicategory.id_whiskerRight, Category.id_comp, Bicategory.whiskerLeft_id,
    Category.comp_id]
  conv_lhs => rw [← Idempotents.Karoubi.comp_p η]
  rw [Bicategory.whiskerLeft_comp, ← Category.assoc, he, Category.assoc]


-- @@ L437-440 verbatim
theorem unit_comm {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (of q ≫ of q').p ≫ e.hom = e.hom ≫ (𝟙 a : a ⟶ a).p := by
  show hcomp₂ (𝟙 q) (𝟙 q') ≫ e.hom = e.hom ≫ 𝟙 (𝟙 a.obj)
  rw [hcomp₂_id_id, Category.id_comp, Category.comp_id]


-- @@ L442-444 verbatim
/-- The isomorphism `of q ≫ of q' ≅ 𝟙 a` determined by `q ≫ q' ≅ 𝟙`. -/
def unitIso {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) : of q ≫ of q' ≅ 𝟙 a :=
  mkIso e (unit_comm e)


-- @@ L446-447 verbatim
theorem unitIso_hom {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (unitIso e).hom = mkHom e.hom (unit_comm e) := rfl


-- @@ L449-451 verbatim
theorem unitIso_inv {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (unitIso e).inv = mkHom e.inv (comm_inv (P := of q ≫ of q') (Q := 𝟙 a) e (unit_comm e)) :=
  rfl


-- @@ L453-453 verbatim
end Pi


-- @@ L455-455 verbatim
section PiInstance


-- @@ L457-459 verbatim
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)]
  [LinearBicategory R B] [PiTwoCategory R B] {a b c d : KarBicat B}


-- @@ L461-461 verbatim
local notation "𝛑" => PiTwoCategory.pi (R := R)

-- @@ L462-462 verbatim
local notation "𝛃" => PiTwoCategory.β (R := R)

-- @@ L463-463 verbatim
local notation "𝛏" => PiTwoCategory.ξ (R := R)


-- @@ L465-467 verbatim
/-- The isomorphism `β_P : P ≫ π_b ≅ π_a ≫ P` of the idempotent completion. -/
def βIso (P : a ⟶ b) : P ≫ of (𝛑 b.obj) ≅ of (𝛑 a.obj) ≫ P :=
  braidIso P 𝛃 (fun η => PiTwoCategory.β_naturality η)


-- @@ L469-471 verbatim
theorem βIso_hom (P : a ⟶ b) :
    (βIso P).hom = mkHom (𝛃 P.X).hom (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η)) :=
  rfl


-- @@ L473-475 verbatim
theorem βIso_inv (P : a ⟶ b) :
    (βIso P).inv = mkHom (𝛃 P.X).inv (comm_inv (P := P ≫ of (𝛑 b.obj)) (Q := of (𝛑 a.obj) ≫ P)
      (𝛃 P.X) (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η))) := rfl


-- @@ L477-479 verbatim
theorem βIso_naturality {P P' : a ⟶ b} (η : P ⟶ P') :
    (βIso P).hom ≫ of (𝛑 a.obj) ◁ η = η ▷ of (𝛑 b.obj) ≫ (βIso P').hom :=
  braidIso_naturality 𝛃 (fun η => PiTwoCategory.β_naturality η) η


-- @@ L481-488 verbatim
theorem βIso_comp (P : a ⟶ b) (Q : b ⟶ c) :
    (βIso (P ≫ Q)).hom = (α_ P Q (of (𝛑 c.obj))).hom ≫ P ◁ (βIso Q).hom ≫
      (α_ P (of (𝛑 b.obj)) Q).inv ≫ (βIso P).hom ▷ Q ≫ (α_ (of (𝛑 a.obj)) P Q).hom := by
  simp only [βIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_mkHom,
    mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.β_comp (R := R) P.X Q.X


-- @@ L490-495 verbatim
theorem βIso_id (a : KarBicat B) :
    (βIso (𝟙 a)).hom = (λ_ (of (𝛑 a.obj))).hom ≫ (ρ_ (of (𝛑 a.obj))).inv := by
  simp only [βIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq]
  rw [mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.β_id (R := R) a.obj


-- @@ L497-501 verbatim
theorem βIso_pi (a : KarBicat B) : (βIso (of (𝛑 a.obj))).hom = -𝟙 _ := by
  apply Idempotents.Karoubi.hom_ext
  rw [βIso_hom, mkHom_f, neg_f, id_f]
  simp only [comp_p, comp_X, of_X, hcomp₂_id_id, Category.comp_id]
  exact PiTwoCategory.β_pi (R := R) a.obj


-- @@ L503-513 verbatim
theorem ξ_comm_aux (P : a ⟶ b) :
    P ◁ (unitIso (𝛏 b.obj)).hom ≫ (ρ_ P).hom ≫ (λ_ P).inv ≫ (unitIso (𝛏 a.obj)).inv ▷ P =
      (α_ P (of (𝛑 b.obj)) (of (𝛑 b.obj))).inv ≫ (βIso P).hom ▷ of (𝛑 b.obj) ≫
        (α_ (of (𝛑 a.obj)) P (of (𝛑 b.obj))).hom ≫ of (𝛑 a.obj) ◁ (βIso P).hom ≫
        (α_ (of (𝛑 a.obj)) (of (𝛑 a.obj)) P).inv := by
  simp only [βIso_hom, unitIso_hom, unitIso_inv, associator_hom_eq, associator_inv_eq,
    leftUnitor_inv_eq, rightUnitor_hom_eq, whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
    mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.ξ_comm (R := R) P.X


-- @@ L515-525 verbatim
/-- **Brundan–Ellis, §6.** The idempotent completion of a Π-2-category is a Π-2-category, with
`π_λ` the image of `π_λ` and `β`, `ξ` composed with the idempotents. -/
instance instPiTwoCategory : PiTwoCategory R (KarBicat B) where
  pi a := of (𝛑 a.obj)
  β P := βIso P
  β_naturality η := βIso_naturality η
  β_comp P Q := βIso_comp P Q
  β_id a := βIso_id a
  β_pi a := βIso_pi a
  ξ a := unitIso (𝛏 a.obj)
  ξ_comm P := ξ_comm_aux P


-- @@ L527-527 verbatim
@[simp] theorem pi_eq (a : KarBicat B) : 𝛑 a = of (𝛑 a.obj) := rfl


-- @@ L529-529 verbatim
theorem β_eq (P : a ⟶ b) : 𝛃 P = βIso P := rfl


-- @@ L531-532 verbatim
theorem β_hom_eq (P : a ⟶ b) :
    (𝛃 P).hom = mkHom (𝛃 P.X).hom (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η)) := rfl


-- @@ L534-536 verbatim
theorem β_inv_eq (P : a ⟶ b) :
    (𝛃 P).inv = mkHom (𝛃 P.X).inv (comm_inv (P := P ≫ of (𝛑 b.obj)) (Q := of (𝛑 a.obj) ≫ P)
      (𝛃 P.X) (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η))) := rfl


-- @@ L538-538 verbatim
theorem ξ_eq (a : KarBicat B) : 𝛏 a = unitIso (𝛏 a.obj) := rfl


-- @@ L540-540 verbatim
theorem ξ_hom_eq (a : KarBicat B) : (𝛏 a).hom = mkHom (𝛏 a.obj).hom (unit_comm (𝛏 a.obj)) := rfl


-- @@ L542-542 verbatim
end PiInstance


-- @@ L544-544 verbatim
section QPiInstance


-- @@ L546-548 verbatim
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)]
  [LinearBicategory R B] [QPiTwoCategory R B] {a b c d : KarBicat B}


-- @@ L550-550 verbatim
local notation "𝛑" => PiTwoCategory.pi (R := R)

-- @@ L551-551 verbatim
local notation "𝛃" => PiTwoCategory.β (R := R)

-- @@ L552-552 verbatim
local notation "𝐪" => QPiTwoCategory.q (R := R)

-- @@ L553-553 verbatim
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)

-- @@ L554-554 verbatim
local notation "𝛄" => QPiTwoCategory.γ (R := R)


-- @@ L556-558 verbatim
/-- The isomorphism `γ_P : P ≫ q_b ≅ q_a ≫ P` of the idempotent completion. -/
def γIso (P : a ⟶ b) : P ≫ of (𝐪 b.obj) ≅ of (𝐪 a.obj) ≫ P :=
  braidIso P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)


-- @@ L560-562 verbatim
theorem γIso_hom (P : a ⟶ b) :
    (γIso P).hom = mkHom (𝛄 P.X).hom (braid_comm P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)) :=
  rfl


-- @@ L564-566 verbatim
theorem γIso_naturality {P P' : a ⟶ b} (η : P ⟶ P') :
    (γIso P).hom ≫ of (𝐪 a.obj) ◁ η = η ▷ of (𝐪 b.obj) ≫ (γIso P').hom :=
  braidIso_naturality 𝛄 (fun η => QPiTwoCategory.γ_naturality η) η


-- @@ L568-575 verbatim
theorem γIso_comp (P : a ⟶ b) (Q : b ⟶ c) :
    (γIso (P ≫ Q)).hom = (α_ P Q (of (𝐪 c.obj))).hom ≫ P ◁ (γIso Q).hom ≫
      (α_ P (of (𝐪 b.obj)) Q).inv ≫ (γIso P).hom ▷ Q ≫ (α_ (of (𝐪 a.obj)) P Q).hom := by
  simp only [γIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_mkHom,
    mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_comp (R := R) P.X Q.X


-- @@ L577-582 verbatim
theorem γIso_id (a : KarBicat B) :
    (γIso (𝟙 a)).hom = (λ_ (of (𝐪 a.obj))).hom ≫ (ρ_ (of (𝐪 a.obj))).inv := by
  simp only [γIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq]
  rw [mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_id (R := R) a.obj


-- @@ L584-587 verbatim
theorem γIso_q (a : KarBicat B) : (γIso (of (𝐪 a.obj))).hom = 𝟙 _ := by
  rw [γIso_hom, id_eq_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_q (R := R) a.obj


-- @@ L589-592 verbatim
theorem γIso_pi (a : KarBicat B) : (γIso (of (𝛑 a.obj))).hom = (βIso (of (𝐪 a.obj))).inv := by
  rw [γIso_hom, βIso_inv]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_pi (R := R) a.obj


-- @@ L594-603 verbatim
theorem q_ii_aux (a : KarBicat B) :
    (unitIso (QPiTwoCategory.ii (R := R) a.obj)).hom ▷ of (𝐪 a.obj) ≫ (λ_ (of (𝐪 a.obj))).hom =
      (α_ (of (𝐪 a.obj)) (of (𝐪⁻¹ a.obj)) (of (𝐪 a.obj))).hom ≫
        of (𝐪 a.obj) ◁ (unitIso (QPiTwoCategory.jj (R := R) a.obj)).hom ≫
        (ρ_ (of (𝐪 a.obj))).hom := by
  simp only [unitIso_hom, associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
    whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.q_ii (R := R) a.obj


-- @@ L605-615 verbatim
theorem ii_qinv_aux (a : KarBicat B) :
    of (𝐪⁻¹ a.obj) ◁ (unitIso (QPiTwoCategory.ii (R := R) a.obj)).hom ≫
        (ρ_ (of (𝐪⁻¹ a.obj))).hom =
      (α_ (of (𝐪⁻¹ a.obj)) (of (𝐪 a.obj)) (of (𝐪⁻¹ a.obj))).inv ≫
        (unitIso (QPiTwoCategory.jj (R := R) a.obj)).hom ▷ of (𝐪⁻¹ a.obj) ≫
        (λ_ (of (𝐪⁻¹ a.obj))).hom := by
  simp only [unitIso_hom, associator_inv_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
    whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.ii_qinv (R := R) a.obj


-- @@ L617-632 verbatim
/-- **Brundan–Ellis, §6.** The idempotent completion of a `(Q, Π)`-2-category is a
`(Q, Π)`-2-category, with `q_λ`, `q_λ⁻¹` the images of those of `B` and `γ`, `ii`, `jj` composed
with the idempotents. -/
instance instQPiTwoCategory : QPiTwoCategory R (KarBicat B) where
  q a := of (𝐪 a.obj)
  qinv a := of (𝐪⁻¹ a.obj)
  γ P := γIso P
  γ_naturality η := γIso_naturality η
  γ_comp P Q := γIso_comp P Q
  γ_id a := γIso_id a
  γ_q a := γIso_q a
  γ_pi a := γIso_pi a
  ii a := unitIso (QPiTwoCategory.ii (R := R) a.obj)
  jj a := unitIso (QPiTwoCategory.jj (R := R) a.obj)
  q_ii a := q_ii_aux a
  ii_qinv a := ii_qinv_aux a


-- @@ L634-634 verbatim
@[simp] theorem q_eq (a : KarBicat B) : 𝐪 a = of (𝐪 a.obj) := rfl


-- @@ L636-636 verbatim
@[simp] theorem qinv_eq (a : KarBicat B) : 𝐪⁻¹ a = of (𝐪⁻¹ a.obj) := rfl


-- @@ L638-638 verbatim
theorem γ_eq (P : a ⟶ b) : 𝛄 P = γIso P := rfl


-- @@ L640-642 verbatim
theorem γ_hom_eq (P : a ⟶ b) :
    (𝛄 P).hom = mkHom (𝛄 P.X).hom (braid_comm P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)) :=
  rfl


-- @@ L644-645 verbatim
theorem ii_eq (a : KarBicat B) :
    QPiTwoCategory.ii (R := R) a = unitIso (QPiTwoCategory.ii (R := R) a.obj) := rfl


-- @@ L647-648 verbatim
theorem jj_eq (a : KarBicat B) :
    QPiTwoCategory.jj (R := R) a = unitIso (QPiTwoCategory.jj (R := R) a.obj) := rfl


-- @@ L650-650 verbatim
end QPiInstance



-- @@ L653-653 verbatim
end KarBicat


-- @@ L655-655 verbatim
end StringDiagrams


-- @@ L657-657 verbatim
end
