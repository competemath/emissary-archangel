import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas


-- @@ L3-3 verbatim
set_option Elab.async false


-- @@ L5-5 verbatim
section MEGA_KwLRThirdAddFormulas_lean

-- @@ L6-6 verbatim
set_option autoImplicit false

-- @@ L7-7 verbatim
set_option maxHeartbeats 800000

-- @@ L8-8 verbatim
set_option linter.unusedSimpArgs false


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open MvPolynomial WeierstrassCurve


-- @@ L14-14 verbatim
namespace WeierstrassProjModel


-- @@ L16-16 verbatim
universe u


-- @@ L18-18 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L20-20 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

-- @@ L21-21 verbatim
local notation "Xl" i => (X (Sum.inl i) : P₆)

-- @@ L22-22 verbatim
local notation "Xr" i => (X (Sum.inr i) : P₆)

-- @@ L23-23 verbatim
local notation "WP₁" => kw_lrAdd_WP₁ W

-- @@ L24-24 verbatim
local notation "WP₂" => kw_lrAdd_WP₂ W


-- @@ L26-26 verbatim
local notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)


-- @@ L28-55 verbatim
def kw_lrThird_X : P₆ :=
  C (-W.a₁*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (-W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-W.a₁*W.a₃ - W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) - W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 1)
    + C (-(2:R)*W.a₄) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((1:R)) * (Xl 0)*(Xl 1)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₃^ (2 : ℕ) - (3:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C (-(2:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(2:R)*W.a₁*W.a₃^ (2 : ℕ) - (6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₃^ (2 : ℕ) - (6:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((1:R)) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁*W.a₃ - W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(6:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (-W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₃*W.a₄ - W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₂*W.a₆ + W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (-(3:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₃^ (3 : ℕ) - (6:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₃*W.a₄ - W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₂*W.a₆ + W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - W.a₂*W.a₃^ (3 : ℕ) - (4:R)*W.a₂*W.a₃*W.a₆ + W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L57-75 verbatim
def kw_lrThird_Y : P₆ :=
  C (-W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (9:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₂*W.a₆ - W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₂*W.a₄ + (9:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)*W.a₁^ (2 : ℕ)*W.a₆ - (4:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (12:R)*W.a₂*W.a₆ - (4:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) - (3:R)*W.a₁*W.a₃*W.a₆ + W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (4:R)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₂*W.a₄^ (2 : ℕ) - W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C ((1:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₂*W.a₆ - W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁*W.a₂*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₃*W.a₆ + W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (4:R)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₂*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₄*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (4:R)*W.a₂*W.a₄*W.a₆ - W.a₃^ (4 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₆ - W.a₄^ (3 : ℕ) - (9:R)*W.a₆^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L77-104 verbatim
def kw_lrThird_Z : P₆ :=
  C ((3:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((3:R)) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (3 : ℕ) + (2:R)*W.a₁*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (2 : ℕ) + W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((2:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁*W.a₃ + W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₂) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₃ + (2:R)*W.a₁*W.a₄ + (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C ((1:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₂) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((1:R)) * (Xl 1)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₃^ (2 : ℕ) + (3:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₂*W.a₃) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁*W.a₃^ (2 : ℕ) + (2:R)*W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₃^ (2 : ℕ) + (3:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₃^ (3 : ℕ) + (3:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L106-112 verbatim
theorem kw_lrThird_X_isHomogeneous : (kw_lrThird_X W).IsHomogeneous 4 := by
  unfold kw_lrThird_X
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L114-120 verbatim
theorem kw_lrThird_Y_isHomogeneous : (kw_lrThird_Y W).IsHomogeneous 4 := by
  unfold kw_lrThird_Y
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L122-128 verbatim
theorem kw_lrThird_Z_isHomogeneous : (kw_lrThird_Z W).IsHomogeneous 4 := by
  unfold kw_lrThird_Z
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L130-130 verbatim
section Minors


-- @@ L132-161 verbatim
def kw_lrThird_pXZ : P₆ :=
  C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ) + W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃ + W.a₁*W.a₂*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-(4:R)*W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃ - W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C ((4:R)*W.a₁^ (3 : ℕ) + W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-(4:R)*W.a₁^ (2 : ℕ)*W.a₄ - W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (9:R)*W.a₆) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((4:R)*W.a₁^ (2 : ℕ) + W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((4:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₆ - W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₂*W.a₆ - W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₂ + (6:R)*W.a₁*W.a₃ - W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + W.a₁*W.a₂^ (3 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) - W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)) * (Xl 2)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂ + (6:R)*W.a₃) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (4:R)*W.a₁^ (3 : ℕ)*W.a₃ - W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃ - W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (9:R)*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₄ - (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄^ (2 : ℕ) - W.a₂*W.a₃*W.a₄ + (3:R)*W.a₃^ (3 : ℕ) + (9:R)*W.a₃*W.a₆) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (2 : ℕ) + W.a₂) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄ + (2:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (4:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (2:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₂*W.a₆ - W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₆ - W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄*W.a₆ + W.a₂*W.a₃^ (3 : ℕ) + (3:R)*W.a₂*W.a₃*W.a₆ - W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)


-- @@ L163-182 verbatim
def kw_lrThird_qXZ : P₆ :=
  C (-(6:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂ - (9:R)*W.a₁*W.a₃ + W.a₂^ (2 : ℕ) - (3:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₃ + W.a₂^ (2 : ℕ) - (3:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₄ - (6:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ + W.a₂^ (2 : ℕ)*W.a₃ - (3:R)*W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C (-(5:R)*W.a₁^ (3 : ℕ) - (2:R)*W.a₁*W.a₂ - (6:R)*W.a₃) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ) - W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (5:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ + W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (9:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₄ + W.a₂*W.a₄ - (3:R)*W.a₃^ (2 : ℕ) - (9:R)*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + (4:R)*W.a₁*W.a₄^ (2 : ℕ) + W.a₂*W.a₃*W.a₄ - (3:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-(4:R)*W.a₁^ (2 : ℕ) - W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (2 : ℕ) - W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (8:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (4:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₂*W.a₆ + W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (W.a₁*W.a₃*W.a₄ - W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₂*W.a₆ + W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₆ + W.a₁*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₄*W.a₆ - W.a₂*W.a₃^ (3 : ℕ) - (3:R)*W.a₂*W.a₃*W.a₆ + W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)


-- @@ L184-217 verbatim
def kw_lrThird_pYZ : P₆ :=
  C (-(9:R)*W.a₁) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₂ - (9:R)*W.a₁*W.a₃ + (3:R)*W.a₂^ (2 : ℕ) - (9:R)*W.a₄) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(9:R)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(6:R)*W.a₁^ (3 : ℕ) - (6:R)*W.a₁*W.a₂ - (9:R)*W.a₃) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₃ + W.a₂^ (3 : ℕ) - (9:R)*W.a₃^ (2 : ℕ) - (27:R)*W.a₆) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(6:R)*W.a₁^ (2 : ℕ) - (6:R)*W.a₂) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (5 : ℕ) - (2:R)*W.a₁^ (3 : ℕ)*W.a₂ - (6:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) - (6:R)*W.a₂*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₆ + (3:R)*W.a₁*W.a₃*W.a₄ + W.a₂^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₃^ (2 : ℕ) - (18:R)*W.a₂*W.a₆ + (3:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ) - (2:R)*W.a₁^ (2 : ℕ)*W.a₂ - W.a₂^ (2 : ℕ)) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₂^ (2 : ℕ)*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + W.a₁*W.a₂*W.a₃*W.a₄ - W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₂^ (2 : ℕ)*W.a₆ + W.a₂*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C ((9:R)*W.a₁) * (Xl 1)*(Xr 0)^ (4 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ) + (12:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(12:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (4:R)*W.a₁*W.a₂^ (2 : ℕ) + (6:R)*W.a₁*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(12:R)*W.a₁) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-(4:R)*W.a₁^ (4 : ℕ) - (4:R)*W.a₁^ (2 : ℕ)*W.a₂ - (12:R)*W.a₁*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₄ + (4:R)*W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ)) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ) - (4:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ)*W.a₃ - (4:R)*W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) + W.a₁*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₂ + (9:R)*W.a₁*W.a₃ - (3:R)*W.a₂^ (2 : ℕ) + (9:R)*W.a₄) * (Xl 2)*(Xr 0)^ (4 : ℕ)
    + C (-(3:R)*W.a₁*W.a₂) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃ - (4:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₄ + (9:R)*W.a₁*W.a₂*W.a₃ - (3:R)*W.a₂^ (3 : ℕ) + (9:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₂) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (3 : ℕ)*W.a₂ - (12:R)*W.a₁^ (2 : ℕ)*W.a₃ + (2:R)*W.a₁*W.a₂^ (2 : ℕ) - (12:R)*W.a₁*W.a₄ - (3:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) + (4:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁*W.a₃*W.a₄ - W.a₂^ (4 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ - (3:R)*W.a₂*W.a₃^ (2 : ℕ) - (9:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂ - (12:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (12:R)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (5 : ℕ)*W.a₂ - (4:R)*W.a₁^ (4 : ℕ)*W.a₃ + (2:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (4:R)*W.a₁^ (3 : ℕ)*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + W.a₁*W.a₂^ (3 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₄ - (12:R)*W.a₁*W.a₃^ (2 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ - (12:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₄ + (4:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + (4:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (5:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (3:R)*W.a₁*W.a₃^ (3 : ℕ) - W.a₂^ (3 : ℕ)*W.a₄ - W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (5:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (4:R)*W.a₁^ (3 : ℕ)*W.a₃ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (4:R)*W.a₁^ (2 : ℕ)*W.a₄ - (4:R)*W.a₁*W.a₂*W.a₃ + W.a₂^ (3 : ℕ) - (4:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₃ - (4:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - (4:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) + W.a₂^ (3 : ℕ)*W.a₃ - (4:R)*W.a₂*W.a₃*W.a₄) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ - W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (2:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - W.a₂^ (3 : ℕ)*W.a₆ - W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + W.a₄^ (3 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)


-- @@ L219-240 verbatim
def kw_lrThird_qYZ : P₆ :=
  C ((9:R)) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 0)
    + C ((6:R)*W.a₁^ (2 : ℕ) + (3:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ + (9:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C (W.a₁^ (5 : ℕ) - (2:R)*W.a₁^ (3 : ℕ)*W.a₂ + (9:R)*W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₂^ (2 : ℕ) + (6:R)*W.a₁*W.a₄ + (3:R)*W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (9:R)*W.a₂*W.a₄ + (9:R)*W.a₃^ (2 : ℕ) + (27:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) - W.a₁^ (4 : ℕ)*W.a₄ - (4:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (4:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₁*W.a₃*W.a₄ + W.a₂^ (4 : ℕ) - (5:R)*W.a₂^ (2 : ℕ)*W.a₄ + (3:R)*W.a₂*W.a₃^ (2 : ℕ) + (9:R)*W.a₂*W.a₆ + (3:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C ((12:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C ((5:R)*W.a₁^ (4 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂ + (6:R)*W.a₁*W.a₃ + W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (-(2:R)*W.a₁^ (3 : ℕ)*W.a₂ + (12:R)*W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₁*W.a₂^ (2 : ℕ) + (6:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (5 : ℕ)*W.a₂ + (5:R)*W.a₁^ (4 : ℕ)*W.a₃ - (2:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (6:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆ + W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (12:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ + (6:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ - (12:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₄ - (5:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - (5:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (5:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₃^ (3 : ℕ) + (9:R)*W.a₁*W.a₃*W.a₆ + W.a₂^ (3 : ℕ)*W.a₄ + W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₂^ (2 : ℕ)*W.a₆ - (5:R)*W.a₂*W.a₄^ (2 : ℕ) + (3:R)*W.a₃^ (2 : ℕ)*W.a₄ + (9:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((9:R)*W.a₁) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 0)
    + C ((4:R)*W.a₁^ (3 : ℕ) + (4:R)*W.a₁*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂ + (18:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (9:R)*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (8:R)*W.a₁^ (3 : ℕ)*W.a₃ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (4:R)*W.a₁^ (2 : ℕ)*W.a₄ + (8:R)*W.a₁*W.a₂*W.a₃ - W.a₂^ (3 : ℕ) + (4:R)*W.a₂*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (9:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₃ + (4:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (5:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - W.a₁*W.a₄^ (2 : ℕ) - W.a₂^ (3 : ℕ)*W.a₃ + (4:R)*W.a₂*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁*W.a₂*W.a₃*W.a₄ - (9:R)*W.a₁*W.a₃*W.a₆ + W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₂*W.a₄^ (2 : ℕ) - (9:R)*W.a₄*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (2:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + W.a₂^ (3 : ℕ)*W.a₆ + W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - W.a₄^ (3 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)


-- @@ L242-252 verbatim
theorem kw_lrThird_minor_XZ :
    kw_lrThird_X W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_X W
      = kw_lrThird_pXZ W * WP₁ + kw_lrThird_qXZ W * WP₂ := by
  simp only [kw_lrThird_X, kw_lrThird_Z, kw_lrThird_pXZ, kw_lrThird_qXZ,
    kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


-- @@ L254-259 verbatim
theorem kw_lrThird_minor_XZ_mem_span :
    kw_lrThird_X W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_X W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrThird_minor_XZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


-- @@ L261-271 verbatim
theorem kw_lrThird_minor_YZ :
    kw_lrThird_Y W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_Y W
      = kw_lrThird_pYZ W * WP₁ + kw_lrThird_qYZ W * WP₂ := by
  simp only [kw_lrThird_Y, kw_lrThird_Z, kw_lrThird_pYZ, kw_lrThird_qYZ,
    kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


-- @@ L273-278 verbatim
theorem kw_lrThird_minor_YZ_mem_span :
    kw_lrThird_Y W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_Y W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrThird_minor_YZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


-- @@ L280-280 verbatim
end Minors


-- @@ L282-282 verbatim
section Diag


-- @@ L284-288 verbatim
theorem kw_lrThird_X_diag : δ (kw_lrThird_X W) = kw_lrSym_dblX W := by
  simp only [kw_lrThird_X, kw_lrSym_dblX,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring


-- @@ L290-294 verbatim
theorem kw_lrThird_Y_diag : δ (kw_lrThird_Y W) = kw_lrSym_dblY W := by
  simp only [kw_lrThird_Y, kw_lrSym_dblY,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring


-- @@ L296-300 verbatim
theorem kw_lrThird_Z_diag : δ (kw_lrThird_Z W) = kw_lrSym_dblZ W := by
  simp only [kw_lrThird_Z, kw_lrSym_dblZ,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring


-- @@ L302-302 verbatim
end Diag


-- @@ L304-304 verbatim
end WeierstrassProjModel


-- @@ L306-306 verbatim
end


-- @@ L308-308 verbatim
end MEGA_KwLRThirdAddFormulas_lean
