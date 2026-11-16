import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate


-- @@ L3-32 verbatim
/-!
# Biadjunctions in bicategories

A *biadjunction* (ambidextrous adjunction) between 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` of
a bicategory is a pair of adjunctions `f ⊣ g` and `g ⊣ f` (Mathlib's `Bicategory.Adjunction`).

For 2-morphisms `α : f ⟶ f'` between 1-morphisms carrying biadjunctions `P : f ⊣⊢ g` and
`P' : f' ⊣⊢ g'` there are two mates `g' ⟶ g`:

* the *right mate* `rightMate P P' α`, the conjugate of `α` with respect to the adjunctions
  `f ⊣ g`, `f' ⊣ g'` (Mathlib's `conjugateEquiv`); in string diagrams, `α` rotated using the
  unit of `f' ⊣ g'` and the counit of `f ⊣ g`;
* the *left mate* `leftMate P P' α`, the inverse conjugate of `α` with respect to the
  adjunctions `g ⊣ f`, `g' ⊣ f'`; in string diagrams, `α` rotated in the opposite direction.

Both are bijections. `α` is *cyclic* (`IsCyclic P P' α`) if its two mates agree. In a monoidal
category (a bicategory with one object) whose objects have chosen right duals, the right mate
of `α` with respect to the right duals is Mathlib's `rightAdjointMate`; similarly for left
mates (see `StringDiagrams.Biadjunction.Monoidal`).

## Main definitions

* `Biadjunction f g` (notation `f ⊣⊢ g`, scoped in `StringDiagrams`), with fields
  `left : f ⊣ g` and `right : g ⊣ f`.
* `Biadjunction.id`, `Biadjunction.comp`, `Biadjunction.symm`.
* `Biadjunction.rightMate`, `Biadjunction.leftMate` (equivalences
  `(f ⟶ f') ≃ (g' ⟶ g)`), `Biadjunction.doubleMate` (the composite of the right mate and the
  inverse of the left mate, `(f ⟶ f') → (f ⟶ f')`: rotation by a full turn).
* `Biadjunction.IsCyclic`.
-/


-- @@ L34-34 verbatim
namespace StringDiagrams


-- @@ L36-36 verbatim
open CategoryTheory Bicategory


-- @@ L38-38 verbatim
universe w v u


-- @@ L40-40 verbatim
variable {B : Type u} [Bicategory.{w, v} B]


-- @@ L42-49 verbatim
/-- A biadjunction (ambidextrous adjunction) between `f : a ⟶ b` and `g : b ⟶ a`: an
adjunction `f ⊣ g` together with an adjunction `g ⊣ f`. No compatibility between the two is
required. -/
structure Biadjunction {a b : B} (f : a ⟶ b) (g : b ⟶ a) where
  /-- The adjunction exhibiting `f` as a left adjoint of `g`. -/
  left : f ⊣ g
  /-- The adjunction exhibiting `f` as a right adjoint of `g`. -/
  right : g ⊣ f


-- @@ L51-51 verbatim
@[inherit_doc] scoped infixr:15 " ⊣⊢ " => Biadjunction


-- @@ L53-53 verbatim
namespace Biadjunction


-- @@ L55-55 verbatim
variable {a b c d : B}


-- @@ L57-61 verbatim
/-- The biadjunction obtained by exchanging the roles of `f` and `g`. -/
@[simps]
def symm {f : a ⟶ b} {g : b ⟶ a} (P : f ⊣⊢ g) : g ⊣⊢ f where
  left := P.right
  right := P.left


-- @@ L63-64 verbatim
@[simp]
theorem symm_symm {f : a ⟶ b} {g : b ⟶ a} (P : f ⊣⊢ g) : P.symm.symm = P := rfl


-- @@ L66-70 verbatim
/-- The identity biadjunction `𝟙 a ⊣⊢ 𝟙 a`, built from `Adjunction.id`. -/
@[simps]
def id (a : B) : 𝟙 a ⊣⊢ 𝟙 a where
  left := Adjunction.id a
  right := Adjunction.id a


-- @@ L72-72 verbatim
instance : Inhabited (𝟙 a ⊣⊢ 𝟙 a) := ⟨id a⟩


-- @@ L74-79 verbatim
/-- Composition of biadjunctions: `f₁ ≫ f₂ ⊣⊢ g₂ ≫ g₁`, built from `Adjunction.comp`. -/
@[simps]
def comp {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b} (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) :
    f₁ ≫ f₂ ⊣⊢ g₂ ≫ g₁ where
  left := P.left.comp Q.left
  right := Q.right.comp P.right


-- @@ L81-82 verbatim
@[simp]
theorem symm_id (a : B) : (id a).symm = id a := rfl


-- @@ L84-86 verbatim
@[simp]
theorem symm_comp {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) : (P.comp Q).symm = Q.symm.comp P.symm := rfl


-- @@ L88-88 verbatim
/-! ## Mates -/


-- @@ L90-90 verbatim
section Mates


-- @@ L92-92 verbatim
variable {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ a}


-- @@ L94-97 verbatim
/-- The right mate of `α : f ⟶ f'`: its conjugate `g' ⟶ g` with respect to the adjunctions
`f ⊣ g` and `f' ⊣ g'` (Mathlib's `conjugateEquiv`). -/
def rightMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ (g' ⟶ g) :=
  conjugateEquiv P'.left P.left


-- @@ L99-102 verbatim
/-- The left mate of `α : f ⟶ f'`: the 2-morphism `g' ⟶ g` whose conjugate with respect to
the adjunctions `g ⊣ f` and `g' ⊣ f'` is `α`. -/
def leftMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ (g' ⟶ g) :=
  (conjugateEquiv P.right P'.right).symm


-- @@ L104-108 verbatim
theorem rightMate_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P P' α =
      (ρ_ _).inv ≫ g' ◁ P.left.unit ≫ g' ◁ α ▷ g ≫ (α_ _ _ _).inv ≫
        P'.left.counit ▷ g ≫ (λ_ _).hom :=
  conjugateEquiv_apply' _ _ α


-- @@ L110-114 verbatim
theorem leftMate_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P P' α =
      (λ_ _).inv ≫ P.right.unit ▷ g' ≫ (α_ _ _ _).hom ≫ g ◁ α ▷ g' ≫
        g ◁ P'.right.counit ≫ (ρ_ _).hom :=
  conjugateEquiv_symm_apply' _ _ α


-- @@ L116-120 verbatim
/-- The mate of a 2-morphism taken twice in the same rotational direction, returning to
`f ⟶ f'`: the inverse left mate of the right mate. In string diagrams, rotation by a full
turn. -/
def doubleMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') : f ⟶ f' :=
  (leftMate P P').symm (rightMate P P' α)


-- @@ L122-125 verbatim
/-- A 2-morphism `α : f ⟶ f'` is cyclic with respect to biadjunctions `P : f ⊣⊢ g` and
`P' : f' ⊣⊢ g'` if its right and left mates agree. -/
def IsCyclic (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') : Prop :=
  rightMate P P' α = leftMate P P' α


-- @@ L127-129 verbatim
theorem isCyclic_iff_doubleMate_eq (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    IsCyclic P P' α ↔ doubleMate P P' α = α := by
  rw [IsCyclic, doubleMate, Equiv.symm_apply_eq, eq_comm]


-- @@ L131-131 verbatim
end Mates


-- @@ L133-133 verbatim
/-! ## Traces -/


-- @@ L135-135 verbatim
section Traces


-- @@ L137-137 verbatim
variable {f f' : a ⟶ b} {g g' : b ⟶ a}


-- @@ L139-143 verbatim
/-- The right trace of `α : f ⟶ f`: the closed diagram in `𝟙 a ⟶ 𝟙 a` obtained by closing
the strand of `α` to the right, `η ≫ α ▷ g ≫ ε'`, with `η` the unit of `f ⊣ g` and `ε'` the
counit of `g ⊣ f`. -/
def rightTrace (P : f ⊣⊢ g) (α : f ⟶ f) : 𝟙 a ⟶ 𝟙 a :=
  P.left.unit ≫ α ▷ g ≫ P.right.counit


-- @@ L145-149 verbatim
/-- The left trace of `α : f ⟶ f`: the closed diagram in `𝟙 b ⟶ 𝟙 b` obtained by closing
the strand of `α` to the left, `η' ≫ g ◁ α ≫ ε`, with `η'` the unit of `g ⊣ f` and `ε` the
counit of `f ⊣ g`. -/
def leftTrace (P : f ⊣⊢ g) (α : f ⟶ f) : 𝟙 b ⟶ 𝟙 b :=
  P.right.unit ≫ g ◁ α ≫ P.left.counit


-- @@ L151-151 verbatim
end Traces


-- @@ L153-153 verbatim
end Biadjunction


-- @@ L155-155 verbatim
end StringDiagrams
