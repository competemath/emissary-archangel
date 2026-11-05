import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Span


-- @@ L6-6 verbatim
set_option Elab.async false


-- @@ L8-8 verbatim
section MEGA_KwLRChordAddFormulas_lean

-- @@ L9-9 verbatim
set_option autoImplicit false

-- @@ L10-10 verbatim
set_option maxHeartbeats 3200000

-- @@ L11-11 verbatim
set_option linter.unusedSimpArgs false


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open MvPolynomial WeierstrassCurve


-- @@ L17-17 verbatim
namespace WeierstrassProjModel


-- @@ L19-19 verbatim
universe u


-- @@ L21-21 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L23-23 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R


-- @@ L25-25 verbatim
local notation "P₈" => MvPolynomial ((Fin 3 ⊕ Fin 3) ⊕ Fin 2) R


-- @@ L27-27 verbatim
local notation "Xl" i => (X (Sum.inl i) : P₆)


-- @@ L29-29 verbatim
local notation "Xr" i => (X (Sum.inr i) : P₆)


-- @@ L31-31 verbatim
def kw_lrAdd_WP₁ : P₆ := rename Sum.inl W.toProjective.polynomial


-- @@ L33-33 verbatim
def kw_lrAdd_WP₂ : P₆ := rename Sum.inr W.toProjective.polynomial


-- @@ L35-35 verbatim
local notation "WP₁" => kw_lrAdd_WP₁ W

-- @@ L36-36 verbatim
local notation "WP₂" => kw_lrAdd_WP₂ W


-- @@ L38-38 verbatim
local notation "ι" => (rename (Sum.inl : (Fin 3 ⊕ Fin 3) → (Fin 3 ⊕ Fin 3) ⊕ Fin 2) : P₆ →ₐ[R] P₈)


-- @@ L40-40 verbatim
local notation "𝓈" => (X (Sum.inr 0) : P₈)

-- @@ L41-41 verbatim
local notation "𝓉" => (X (Sum.inr 1) : P₈)


-- @@ L43-49 verbatim
def kw_lrAdd_c₂₁ : P₆ :=
  - C (3:R) * (Xl 0)^2 * (Xr 0) + (Xl 1)^2 * (Xr 2) + C (2:R) * (Xl 1) * (Xr 1) * (Xl 2)
    - C (3:R) * C W.a₆ * (Xl 2)^2 * (Xr 2)
    + C W.a₁ * ((Xl 0)*(Xl 1)*(Xr 2) + (Xl 0)*(Xr 1)*(Xl 2) + (Xr 0)*(Xl 1)*(Xl 2))
    - C W.a₂ * ((Xl 0)^2*(Xr 2) + C (2:R)*(Xl 0)*(Xr 0)*(Xl 2))
    + C W.a₃ * (C (2:R)*(Xl 1)*(Xl 2)*(Xr 2) + (Xr 1)*(Xl 2)^2)
    - C W.a₄ * (C (2:R)*(Xl 0)*(Xl 2)*(Xr 2) + (Xr 0)*(Xl 2)^2)


-- @@ L51-57 verbatim
def kw_lrAdd_c₁₂ : P₆ :=
  - C (3:R) * (Xl 0) * (Xr 0)^2 + C (2:R)*(Xl 1)*(Xr 1)*(Xr 2) + (Xr 1)^2*(Xl 2)
    - C (3:R) * C W.a₆ * (Xl 2)*(Xr 2)^2
    + C W.a₁ * ((Xl 0)*(Xr 1)*(Xr 2) + (Xr 0)*(Xl 1)*(Xr 2) + (Xr 0)*(Xr 1)*(Xl 2))
    - C W.a₂ * (C (2:R)*(Xl 0)*(Xr 0)*(Xr 2) + (Xr 0)^2*(Xl 2))
    + C W.a₃ * ((Xl 1)*(Xr 2)^2 + C (2:R)*(Xr 1)*(Xl 2)*(Xr 2))
    - C W.a₄ * ((Xl 0)*(Xr 2)^2 + C (2:R)*(Xr 0)*(Xl 2)*(Xr 2))


-- @@ L59-59 verbatim
local notation "c₂₁" => kw_lrAdd_c₂₁ W

-- @@ L60-60 verbatim
local notation "c₁₂" => kw_lrAdd_c₁₂ W


-- @@ L62-62 verbatim
def kw_lrAdd_starX : P₆ := c₁₂ * (Xl 0) - c₂₁ * (Xr 0)


-- @@ L64-64 verbatim
def kw_lrAdd_starY : P₆ := c₁₂ * (Xl 1) - c₂₁ * (Xr 1)


-- @@ L66-66 verbatim
def kw_lrAdd_starZ : P₆ := c₁₂ * (Xl 2) - c₂₁ * (Xr 2)


-- @@ L68-68 verbatim
def kw_lrAdd_X : P₆ := kw_lrAdd_starX W


-- @@ L70-71 verbatim
def kw_lrAdd_Y : P₆ :=
  -(kw_lrAdd_starY W) - C W.a₁ * kw_lrAdd_starX W - C W.a₃ * kw_lrAdd_starZ W


-- @@ L73-73 verbatim
def kw_lrAdd_Z : P₆ := kw_lrAdd_starZ W


-- @@ L75-77 verbatim
theorem kw_lrAdd_isHomog_C_mul {σ : Type*} {n : ℕ} (r : R)
    {q : MvPolynomial σ R} (hq : q.IsHomogeneous n) : (C r * q).IsHomogeneous n :=
  Nat.zero_add n ▸ (isHomogeneous_C _ r).mul hq


-- @@ L79-90 verbatim
theorem kw_lrAdd_c₂₁_isHomogeneous : (c₂₁).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₂₁

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_


-- @@ L92-103 verbatim
theorem kw_lrAdd_c₁₂_isHomogeneous : (c₁₂).IsHomogeneous 3 := by
  unfold kw_lrAdd_c₁₂

  repeat' first
    | with_reducible apply IsHomogeneous.add | with_reducible apply IsHomogeneous.sub
    | with_reducible apply IsHomogeneous.neg
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible exact isHomogeneous_X _ _
    | with_reducible exact (isHomogeneous_X _ _).pow _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)
    | with_reducible refine kw_lrAdd_isHomog_C_mul _ ?_


-- @@ L105-108 verbatim
theorem kw_lrAdd_X_isHomogeneous : (kw_lrAdd_X W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 0) - (c₂₁) * (Xr 0)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))


-- @@ L110-113 verbatim
theorem kw_lrAdd_Z_isHomogeneous : (kw_lrAdd_Z W).IsHomogeneous 4 := by
  show ((c₁₂) * (Xl 2) - (c₂₁) * (Xr 2)).IsHomogeneous 4
  exact ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
    ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))


-- @@ L115-122 verbatim
theorem kw_lrAdd_Y_isHomogeneous : (kw_lrAdd_Y W).IsHomogeneous 4 := by
  unfold kw_lrAdd_Y
  have hX : (kw_lrAdd_starX W).IsHomogeneous 4 := kw_lrAdd_X_isHomogeneous W
  have hZ : (kw_lrAdd_starZ W).IsHomogeneous 4 := kw_lrAdd_Z_isHomogeneous W
  have hY : (kw_lrAdd_starY W).IsHomogeneous 4 :=
    ((kw_lrAdd_c₁₂_isHomogeneous W).mul (isHomogeneous_X _ _)).sub
      ((kw_lrAdd_c₂₁_isHomogeneous W).mul (isHomogeneous_X _ _))
  exact (hY.neg.sub ((isHomogeneous_C _ _).mul hX)).sub ((isHomogeneous_C _ _).mul hZ)


-- @@ L124-124 verbatim
section OnCurve


-- @@ L126-127 verbatim
noncomputable def kw_lrAdd_spec : P₈ →ₐ[R] P₆ :=
  aeval (Sum.elim X ![c₁₂, -c₂₁])


-- @@ L129-129 verbatim
local notation "σ" => kw_lrAdd_spec W


-- @@ L131-134 verbatim
theorem kw_lrAdd_spec_rename (p : P₆) : σ (ι p) = p := by
  show aeval (Sum.elim X ![c₁₂, -c₂₁]) (rename Sum.inl p) = p
  rw [aeval_rename, Sum.elim_comp_inl]
  exact congrFun (congrArg DFunLike.coe aeval_X_left) p


-- @@ L136-137 verbatim
theorem kw_lrAdd_spec_s : σ 𝓈 = c₁₂ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_zero]


-- @@ L139-140 verbatim
theorem kw_lrAdd_spec_t : σ 𝓉 = -c₂₁ := by
  simp only [kw_lrAdd_spec, aeval_X, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero]


-- @@ L142-150 verbatim
theorem kw_lrAdd_chordCubic :
    aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial
      = 𝓈^3 * ι WP₁ + 𝓈^2 * 𝓉 * ι c₂₁ + 𝓈 * 𝓉^2 * ι c₁₂ + 𝓉^3 * ι WP₂ := by
  simp only [kw_lrAdd_WP₁, kw_lrAdd_WP₂, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
  ring


-- @@ L152-160 verbatim
theorem kw_lrAdd_negInvariant {S : Type u} [CommRing S] [Algebra R S] (x y z : S) :
    aeval ![x, -y - algebraMap R S W.a₁ * x - algebraMap R S W.a₃ * z, z]
        W.toProjective.polynomial
      = aeval ![x, y, z] W.toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring


-- @@ L162-186 verbatim
theorem kw_lrAdd_star_onCurve :
    aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by

  have hcomp : (σ).comp (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)))
      = (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          : MvPolynomial (Fin 3) R →ₐ[R] P₆) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp only [AlgHom.comp_apply, map_add, map_mul, aeval_X, Fin.isValue,
        kw_lrAdd_spec_rename, kw_lrAdd_spec_s, kw_lrAdd_spec_t,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons,
        kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, neg_mul, ← sub_eq_add_neg] <;>
      rfl
  rw [show (aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
        : MvPolynomial (Fin 3) R →ₐ[R] P₆) W.toProjective.polynomial
      = σ (aeval (fun i => 𝓈 * ι (Xl i) + 𝓉 * ι (Xr i)) W.toProjective.polynomial)
    from by rw [← AlgHom.comp_apply, hcomp], kw_lrAdd_chordCubic]

  simp only [map_add, map_mul, map_pow, kw_lrAdd_spec_rename,
    kw_lrAdd_spec_s, kw_lrAdd_spec_t]
  ring


-- @@ L188-198 verbatim
theorem kw_lrAdd_onCurve :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = c₁₂^3 * WP₁ - c₂₁^3 * WP₂ := by
  have hneg : aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      = aeval ![kw_lrAdd_starX W, kw_lrAdd_starY W, kw_lrAdd_starZ W]
          W.toProjective.polynomial := by
    have := kw_lrAdd_negInvariant W (S := P₆)
      (kw_lrAdd_starX W) (kw_lrAdd_starY W) (kw_lrAdd_starZ W)
    simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, algebraMap_eq] at this ⊢
    exact this
  rw [hneg, kw_lrAdd_star_onCurve]


-- @@ L200-205 verbatim
theorem kw_lrAdd_onCurve_mem_span :
    aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W] W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrAdd_onCurve]
  exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


-- @@ L207-207 verbatim
end OnCurve


-- @@ L209-209 verbatim
end WeierstrassProjModel


-- @@ L211-211 verbatim
end


-- @@ L213-213 verbatim
end MEGA_KwLRChordAddFormulas_lean


-- @@ L215-215 verbatim
section MEGA_KwLRSymAddFormulas_lean

-- @@ L216-216 verbatim
set_option autoImplicit false

-- @@ L217-217 verbatim
set_option maxHeartbeats 6400000

-- @@ L218-218 verbatim
set_option linter.unusedSimpArgs false


-- @@ L220-220 verbatim
noncomputable section


-- @@ L222-222 verbatim
open MvPolynomial WeierstrassCurve


-- @@ L224-224 verbatim
namespace WeierstrassProjModel


-- @@ L226-226 verbatim
universe u


-- @@ L228-228 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L230-230 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

-- @@ L231-231 verbatim
local notation "Xl" i => (X (Sum.inl i) : P₆)

-- @@ L232-232 verbatim
local notation "Xr" i => (X (Sum.inr i) : P₆)

-- @@ L233-233 verbatim
local notation "WP₁" => kw_lrAdd_WP₁ W

-- @@ L234-234 verbatim
local notation "WP₂" => kw_lrAdd_WP₂ W


-- @@ L236-236 verbatim
local notation "τ" => (rename (Sum.swap : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3) : P₆ →ₐ[R] P₆)


-- @@ L238-238 verbatim
local notation "δ" => (aeval (Sum.elim X X) : P₆ →ₐ[R] MvPolynomial (Fin 3) R)


-- @@ L240-270 verbatim
def kw_lrSym_X : P₆ :=
  C (-(2:R)*W.a₁*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(2:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((4:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 1)
    + C (-(4:R)*W.a₄) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 0)*(Xl 1)*(Xr 1)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xr 1)*(Xr 2)
    + C (-W.a₃^ (2 : ℕ) - (6:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C (-(4:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(4:R)*W.a₁*W.a₃^ (2 : ℕ) - (12:R)*W.a₁*W.a₆ - (4:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 0)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C (-(2:R)*W.a₃^ (2 : ℕ) - (12:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 1)
    + C (-(2:R)*W.a₃^ (2 : ℕ) - (12:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (-W.a₃^ (2 : ℕ) - (6:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (8:R)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L272-298 verbatim
def kw_lrSym_Y : P₆ :=
  C (-(2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)*(Xl 1)*(Xr 1)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((12:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂*W.a₃^ (2 : ℕ) + (24:R)*W.a₂*W.a₆ - (8:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁*W.a₄ - W.a₂*W.a₃) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)*W.a₁*W.a₆ - (2:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 1)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₆ - W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (8:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (8:R)*W.a₂*W.a₄*W.a₆ - (2:R)*W.a₃^ (4 : ℕ) - (12:R)*W.a₃^ (2 : ℕ)*W.a₆ - (2:R)*W.a₄^ (3 : ℕ) - (18:R)*W.a₆^ (2 : ℕ)) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L300-330 verbatim
def kw_lrSym_Z : P₆ :=
  C ((6:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((6:R)) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₄ + W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 0)*(Xl 1)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (4:R)*W.a₂) * (Xl 0)*(Xl 1)*(Xr 0)*(Xr 2)
    + C ((2:R)*W.a₁) * (Xl 0)*(Xl 1)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 0)*(Xl 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (4:R)*W.a₂) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((4:R)*W.a₁^ (2 : ℕ)*W.a₃ + (4:R)*W.a₁*W.a₄ + (4:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 2)*(Xr 0)*(Xr 2)
    + C (W.a₁) * (Xl 0)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C ((4:R)*W.a₁*W.a₃ + (4:R)*W.a₄) * (Xl 0)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁) * (Xl 1)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 1)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₃) * (Xl 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xl 2)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 1)
    + C ((4:R)*W.a₁*W.a₃ + (4:R)*W.a₄) * (Xl 1)*(Xl 2)*(Xr 0)*(Xr 2)
    + C ((2:R)) * (Xl 1)*(Xl 2)*(Xr 1)^ (2 : ℕ)
    + C ((4:R)*W.a₃) * (Xl 1)*(Xl 2)*(Xr 1)*(Xr 2)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (Xl 1)*(Xl 2)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₄ + W.a₂*W.a₃) * (Xl 2)^ (2 : ℕ)*(Xr 0)^ (2 : ℕ)
    + C ((2:R)*W.a₁*W.a₃ + (2:R)*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 1)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (Xl 2)^ (2 : ℕ)*(Xr 0)*(Xr 2)
    + C (W.a₃) * (Xl 2)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((2:R)*W.a₃^ (3 : ℕ) + (6:R)*W.a₃*W.a₆) * (Xl 2)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)


-- @@ L332-338 verbatim
theorem kw_lrSym_X_isHomogeneous : (kw_lrSym_X W).IsHomogeneous 4 := by
  unfold kw_lrSym_X
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L340-346 verbatim
theorem kw_lrSym_Y_isHomogeneous : (kw_lrSym_Y W).IsHomogeneous 4 := by
  unfold kw_lrSym_Y
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L348-354 verbatim
theorem kw_lrSym_Z_isHomogeneous : (kw_lrSym_Z W).IsHomogeneous 4 := by
  unfold kw_lrSym_Z
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


-- @@ L356-356 verbatim
section OnCurve


-- @@ L358-358 verbatim
end OnCurve


-- @@ L360-360 verbatim
section Minors


-- @@ L362-391 verbatim
def kw_lrSym_pXZ : P₆ :=
  C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ) + W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃ + W.a₁*W.a₂*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((6:R)*W.a₁) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-(5:R)*W.a₁^ (2 : ℕ)*W.a₂ + (6:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C ((5:R)*W.a₁^ (3 : ℕ) + (2:R)*W.a₁*W.a₂ + (6:R)*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-(5:R)*W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ)*W.a₃ + (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((9:R)*W.a₁) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ + (15:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - W.a₁^ (3 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + W.a₁*W.a₂^ (3 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 2)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (12:R)*W.a₃) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃ - W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (12:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - (4:R)*W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₃^ (3 : ℕ) + (18:R)*W.a₃*W.a₆) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (7:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄ + (4:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄*W.a₆ + (2:R)*W.a₂*W.a₃^ (3 : ℕ) + (6:R)*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)


-- @@ L393-420 verbatim
def kw_lrSym_qXZ : P₆ :=
  C (-(9:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C (-(6:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ) + (4:R)*W.a₁^ (2 : ℕ)*W.a₂ - (15:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂ - (6:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ - (6:R)*W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C (-(6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ - (12:R)*W.a₃) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (3 : ℕ) - (2:R)*W.a₁*W.a₂ - (6:R)*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ - (12:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₄ + (2:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + (4:R)*W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₃^ (3 : ℕ) - (18:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-(5:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ) - W.a₁*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (10:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (4:R)*W.a₂*W.a₃) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃ - W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁*W.a₃*W.a₄ - (4:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C ((2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₄*W.a₆ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (6:R)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)


-- @@ L422-461 verbatim
def kw_lrSym_pXY : P₆ :=
  C (-(6:R)*W.a₁*W.a₂) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (6:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (6:R)*W.a₂*W.a₄) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (2 : ℕ) - (6:R)*W.a₂) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (6:R)*W.a₂*W.a₃) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - (9:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₃^ (2 : ℕ) - (18:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C (W.a₁^ (4 : ℕ) - W.a₁^ (2 : ℕ)*W.a₂ - (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (3 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃ - (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (3:R)*W.a₁*W.a₃^ (3 : ℕ) - (9:R)*W.a₁*W.a₃*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (4:R)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₄ - (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 0)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₄) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃*W.a₄) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ + (3:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₄*W.a₆ + (2:R)*W.a₄^ (3 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C ((6:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 0)^ (4 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (6:R)*W.a₁^ (2 : ℕ)*W.a₃ + (5:R)*W.a₁*W.a₂^ (2 : ℕ) + (9:R)*W.a₁*W.a₄) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C ((9:R)*W.a₁) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ) - (10:R)*W.a₁^ (2 : ℕ)*W.a₂ + (9:R)*W.a₁*W.a₃ - (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (11:R)*W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C ((6:R)) * (Xl 1)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C ((6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ + (6:R)*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-(2:R)*W.a₁^ (3 : ℕ)*W.a₃ - (11:R)*W.a₁^ (2 : ℕ)*W.a₄ - (5:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₂*W.a₆ + (5:R)*W.a₁*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C ((5:R)*W.a₁^ (2 : ℕ) + (2:R)*W.a₂) * (Xl 1)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₃ - (6:R)*W.a₁*W.a₄ + (2:R)*W.a₂*W.a₃) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ - (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + (6:R)*W.a₁*W.a₄*W.a₆) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (6:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (6:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 0)^ (4 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (6:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (9:R)*W.a₁*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) + (6:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - (2:R)*W.a₂^ (4 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁*W.a₃ - (6:R)*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (2:R)*W.a₁^ (3 : ℕ)*W.a₄ - (10:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁*W.a₂^ (3 : ℕ) - (11:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₃^ (2 : ℕ) - (18:R)*W.a₁*W.a₆ - (6:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - (4:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - W.a₁*W.a₂^ (3 : ℕ)*W.a₃ + (16:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (9:R)*W.a₁*W.a₃^ (3 : ℕ) - (27:R)*W.a₁*W.a₃*W.a₆ - (4:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (14:R)*W.a₂*W.a₄^ (2 : ℕ) - (12:R)*W.a₃^ (2 : ℕ)*W.a₄ - (36:R)*W.a₄*W.a₆) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (2:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (2 : ℕ)*W.a₄ - (7:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (8:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (3 : ℕ)*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - (14:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₁*W.a₂*W.a₆ - (9:R)*W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₃ - (8:R)*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₃^ (3 : ℕ) - (18:R)*W.a₃*W.a₆) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (6:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ + (12:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (6:R)*W.a₂*W.a₄*W.a₆ - (6:R)*W.a₃^ (4 : ℕ) - (36:R)*W.a₃^ (2 : ℕ)*W.a₆ + (8:R)*W.a₄^ (3 : ℕ) - (54:R)*W.a₆^ (2 : ℕ)) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₆ - (6:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (3 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + W.a₁*W.a₂^ (2 : ℕ)*W.a₆ - (9:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁*W.a₄*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (3 : ℕ) - (6:R)*W.a₂*W.a₃*W.a₆ - (6:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₆ + (2:R)*W.a₁*W.a₃^ (3 : ℕ)*W.a₄ + (15:R)*W.a₁*W.a₃*W.a₄*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄*W.a₆ - (2:R)*W.a₂*W.a₃^ (4 : ℕ) - (12:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₆ - (18:R)*W.a₂*W.a₆^ (2 : ℕ) + (2:R)*W.a₃^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (12:R)*W.a₄^ (2 : ℕ)*W.a₆) * (Xl 2)*(Xr 2)^ (4 : ℕ)


-- @@ L463-495 verbatim
def kw_lrSym_qXY : P₆ :=
  C (-(3:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 0)
    + C (-(9:R)*W.a₁) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 1)
    + C ((3:R)*W.a₁*W.a₃ + (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄ + (6:R)*W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C (-W.a₁^ (4 : ℕ) + (4:R)*W.a₁^ (2 : ℕ)*W.a₂ - (9:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) - (6:R)*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₃ + (2:R)*W.a₁^ (3 : ℕ)*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (4:R)*W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (18:R)*W.a₁*W.a₆ + (6:R)*W.a₃*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) - (4:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (7:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (9:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (4 : ℕ) - (10:R)*W.a₂^ (2 : ℕ)*W.a₄ + (6:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - W.a₁*W.a₂^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + W.a₁*W.a₂^ (3 : ℕ)*W.a₃ - (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (9:R)*W.a₁*W.a₃^ (3 : ℕ) + (27:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (8:R)*W.a₂*W.a₄^ (2 : ℕ) + (12:R)*W.a₃^ (2 : ℕ)*W.a₄ + (36:R)*W.a₄*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-(3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 0)
    + C (-(6:R)) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ) + (7:R)*W.a₁^ (2 : ℕ)*W.a₂ + (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(6:R)*W.a₁^ (3 : ℕ) - (3:R)*W.a₁*W.a₂ - (6:R)*W.a₃) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₃ + (8:R)*W.a₁^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ + (6:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₃ - (2:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + (3:R)*W.a₁^ (3 : ℕ)*W.a₄ + (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁*W.a₂^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₄ - (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (4:R)*W.a₁^ (3 : ℕ)*W.a₃ + W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂*W.a₄ - (6:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (8:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - (2:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁*W.a₂*W.a₆ + (2:R)*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₃^ (3 : ℕ) + (18:R)*W.a₃*W.a₆) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (9:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (3:R)*W.a₁*W.a₃^ (3 : ℕ) + (9:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (10:R)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (2 : ℕ)*W.a₄ + (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₄ + (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + (4:R)*W.a₁*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₄ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (12:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (4 : ℕ) + (36:R)*W.a₃^ (2 : ℕ)*W.a₆ - (8:R)*W.a₄^ (3 : ℕ) + (54:R)*W.a₆^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ) + (5:R)*W.a₁*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 0)
    + C (-(5:R)*W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 1)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (6:R)*W.a₁*W.a₄) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₄ + (12:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (8:R)*W.a₂*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₂ - (8:R)*W.a₁^ (2 : ℕ)*W.a₃ + W.a₁*W.a₂^ (2 : ℕ) - (3:R)*W.a₁*W.a₄ - (2:R)*W.a₂*W.a₃) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (8:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (15:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₄ + (2:R)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (6:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₃ + (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃ - W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (6:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃*W.a₄ + (5:R)*W.a₁^ (2 : ℕ)*W.a₃^ (3 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁*W.a₄*W.a₆ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃*W.a₄ + (2:R)*W.a₂*W.a₃^ (3 : ℕ) + (6:R)*W.a₂*W.a₃*W.a₆ + (6:R)*W.a₃*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((2:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (3:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₆ - W.a₁*W.a₂^ (2 : ℕ)*W.a₆ + (3:R)*W.a₁*W.a₄*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (W.a₁^ (3 : ℕ)*W.a₂*W.a₃*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₆ + W.a₁*W.a₂^ (2 : ℕ)*W.a₃*W.a₆ - (2:R)*W.a₁*W.a₃^ (3 : ℕ)*W.a₄ - (15:R)*W.a₁*W.a₃*W.a₄*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₂*W.a₃^ (4 : ℕ) + (12:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₆ + (18:R)*W.a₂*W.a₆^ (2 : ℕ) - (2:R)*W.a₃^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (12:R)*W.a₄^ (2 : ℕ)*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 2)


-- @@ L497-532 verbatim
def kw_lrSym_pYZ : P₆ :=
  C (-(18:R)*W.a₁) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C ((6:R)*W.a₁^ (2 : ℕ)*W.a₂ - (18:R)*W.a₁*W.a₃ + (6:R)*W.a₂^ (2 : ℕ) - (18:R)*W.a₄) * (Xl 0)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(18:R)) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-(9:R)*W.a₁^ (3 : ℕ) - (12:R)*W.a₁*W.a₂ - (18:R)*W.a₃) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₄ - (6:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (18:R)*W.a₃^ (2 : ℕ) - (54:R)*W.a₆) * (Xl 0)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(9:R)*W.a₁^ (2 : ℕ) - (12:R)*W.a₂) * (Xl 0)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (5 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₂ - (9:R)*W.a₁^ (2 : ℕ)*W.a₃ - (2:R)*W.a₁*W.a₂^ (2 : ℕ) - (12:R)*W.a₂*W.a₃) * (Xl 0)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₆ + (6:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₄ - (12:R)*W.a₂*W.a₃^ (2 : ℕ) - (36:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂ - (2:R)*W.a₂^ (2 : ℕ)) * (Xl 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃) * (Xl 0)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (6:R)*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xr 2)^ (4 : ℕ)
    + C ((18:R)*W.a₁) * (Xl 1)*(Xr 0)^ (4 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ) + (24:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(21:R)*W.a₁^ (2 : ℕ)) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₂ - (3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (7:R)*W.a₁*W.a₂^ (2 : ℕ) + (15:R)*W.a₁*W.a₄) * (Xl 1)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(21:R)*W.a₁) * (Xl 1)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (-(4:R)*W.a₁^ (4 : ℕ) - (7:R)*W.a₁^ (2 : ℕ)*W.a₂ - (21:R)*W.a₁*W.a₃) * (Xl 1)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C ((4:R)*W.a₁^ (3 : ℕ)*W.a₄ + (7:R)*W.a₁*W.a₂*W.a₄ - (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 1)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ) - (7:R)*W.a₁*W.a₂) * (Xl 1)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(4:R)*W.a₁^ (3 : ℕ)*W.a₃ - (7:R)*W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C ((3:R)*W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ)) * (Xl 1)*(Xr 2)^ (4 : ℕ)
    + C (-(6:R)*W.a₁^ (2 : ℕ)*W.a₂ + (18:R)*W.a₁*W.a₃ - (6:R)*W.a₂^ (2 : ℕ) + (18:R)*W.a₄) * (Xl 2)*(Xr 0)^ (4 : ℕ)
    + C (-(3:R)*W.a₁^ (3 : ℕ) - (6:R)*W.a₁*W.a₂) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 1)
    + C (-(6:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (18:R)*W.a₁*W.a₂*W.a₃ - (6:R)*W.a₂^ (3 : ℕ) + (18:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 0)^ (3 : ℕ)*(Xr 2)
    + C (-(6:R)*W.a₁^ (2 : ℕ) - (6:R)*W.a₂) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)^ (2 : ℕ)
    + C (-W.a₁^ (5 : ℕ) + (4:R)*W.a₁^ (3 : ℕ)*W.a₂ - (30:R)*W.a₁^ (2 : ℕ)*W.a₃ + (5:R)*W.a₁*W.a₂^ (2 : ℕ) - (27:R)*W.a₁*W.a₄ - (6:R)*W.a₂*W.a₃) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 1)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (4 : ℕ)*W.a₄ + (5:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ - (9:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₆ + (8:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂^ (4 : ℕ) + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ - (6:R)*W.a₂*W.a₃^ (2 : ℕ) - (18:R)*W.a₂*W.a₆ + (12:R)*W.a₄^ (2 : ℕ)) * (Xl 2)*(Xr 0)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (-(3:R)*W.a₁) * (Xl 2)*(Xr 0)*(Xr 1)^ (3 : ℕ)
    + C (-(2:R)*W.a₁^ (4 : ℕ) + (2:R)*W.a₁^ (2 : ℕ)*W.a₂ - (27:R)*W.a₁*W.a₃ + (4:R)*W.a₂^ (2 : ℕ) - (24:R)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (5 : ℕ)*W.a₂ - (6:R)*W.a₁^ (4 : ℕ)*W.a₃ + (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) - (4:R)*W.a₁^ (3 : ℕ)*W.a₄ - (5:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (2:R)*W.a₁*W.a₂^ (3 : ℕ) - (7:R)*W.a₁*W.a₂*W.a₄ - (27:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ + (4:R)*W.a₂^ (2 : ℕ)*W.a₃ - (24:R)*W.a₃*W.a₄) * (Xl 2)*(Xr 0)*(Xr 1)*(Xr 2)^ (2 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₄ + (6:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ - W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) - (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ + (6:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) + (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (6:R)*W.a₁*W.a₃^ (3 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₄ - (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) - (12:R)*W.a₂^ (2 : ℕ)*W.a₆ + (10:R)*W.a₂*W.a₄^ (2 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₄) * (Xl 2)*(Xr 0)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (3 : ℕ) - W.a₁*W.a₂) * (Xl 2)*(Xr 1)^ (3 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₂ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (5:R)*W.a₁^ (2 : ℕ)*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃ + (2:R)*W.a₂^ (3 : ℕ) - (8:R)*W.a₂*W.a₄) * (Xl 2)*(Xr 1)^ (2 : ℕ)*(Xr 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₃ - (5:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ - (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₃ - (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 2)*(Xr 1)*(Xr 2)^ (3 : ℕ)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₆ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ - (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)*(Xr 2)^ (4 : ℕ)


-- @@ L534-563 verbatim
def kw_lrSym_qYZ : P₆ :=
  C ((18:R)) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 0)
    + C ((6:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (Xl 0)^ (2 : ℕ)*(Xl 1)^ (2 : ℕ)*(Xr 2)
    + C ((9:R)*W.a₁^ (3 : ℕ) - (6:R)*W.a₁*W.a₂ + (18:R)*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 0)
    + C ((3:R)*W.a₁^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 1)
    + C (W.a₁^ (5 : ℕ) - W.a₁^ (3 : ℕ)*W.a₂ + (12:R)*W.a₁^ (2 : ℕ)*W.a₃ - (5:R)*W.a₁*W.a₂^ (2 : ℕ) + (9:R)*W.a₁*W.a₄ + (6:R)*W.a₂*W.a₃) * (Xl 0)^ (2 : ℕ)*(Xl 1)*(Xl 2)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (3:R)*W.a₁^ (3 : ℕ)*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₄ - (12:R)*W.a₁*W.a₂*W.a₃ + (4:R)*W.a₂^ (3 : ℕ) - (18:R)*W.a₂*W.a₄ + (18:R)*W.a₃^ (2 : ℕ) + (54:R)*W.a₆) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₂ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃ - W.a₁*W.a₂^ (2 : ℕ) + (3:R)*W.a₁*W.a₄) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂^ (2 : ℕ) - W.a₁^ (4 : ℕ)*W.a₄ - (5:R)*W.a₁^ (3 : ℕ)*W.a₂*W.a₃ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (3 : ℕ) - (8:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (9:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (8:R)*W.a₁*W.a₂^ (2 : ℕ)*W.a₃ + (12:R)*W.a₁*W.a₃*W.a₄ + (2:R)*W.a₂^ (4 : ℕ) - (10:R)*W.a₂^ (2 : ℕ)*W.a₄ + (6:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ + (6:R)*W.a₄^ (2 : ℕ)) * (Xl 0)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (3 : ℕ)*(Xr 2)
    + C ((27:R)*W.a₁^ (2 : ℕ) + (12:R)*W.a₂) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 0)
    + C ((3:R)*W.a₁) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 1)
    + C ((5:R)*W.a₁^ (4 : ℕ) + (10:R)*W.a₁^ (2 : ℕ)*W.a₂ + (9:R)*W.a₁*W.a₃ + (2:R)*W.a₂^ (2 : ℕ) + (6:R)*W.a₄) * (Xl 0)*(Xl 1)^ (2 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (5 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₂ + (27:R)*W.a₁^ (2 : ℕ)*W.a₃ - (4:R)*W.a₁*W.a₂^ (2 : ℕ) + (12:R)*W.a₂*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (4 : ℕ) + W.a₁^ (2 : ℕ)*W.a₂ + (3:R)*W.a₁*W.a₃) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (5 : ℕ)*W.a₂ + (6:R)*W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (3 : ℕ)*W.a₂^ (2 : ℕ) + W.a₁^ (3 : ℕ)*W.a₄ + (11:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ - (2:R)*W.a₁*W.a₂^ (3 : ℕ) + W.a₁*W.a₂*W.a₄ + (9:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃ + (6:R)*W.a₃*W.a₄) * (Xl 0)*(Xl 1)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (-W.a₁^ (4 : ℕ)*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (24:R)*W.a₁*W.a₃*W.a₄ + (4:R)*W.a₂^ (2 : ℕ)*W.a₄ + (12:R)*W.a₂*W.a₃^ (2 : ℕ) + (36:R)*W.a₂*W.a₆ - (24:R)*W.a₄^ (2 : ℕ)) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (-W.a₁^ (3 : ℕ)*W.a₄ - W.a₁*W.a₂*W.a₄ + (3:R)*W.a₁*W.a₃^ (2 : ℕ) + (9:R)*W.a₁*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₄ - (6:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - (6:R)*W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (10:R)*W.a₁*W.a₂*W.a₃*W.a₄ + (6:R)*W.a₁*W.a₃^ (3 : ℕ) + (18:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (3 : ℕ)*W.a₄ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (6:R)*W.a₂^ (2 : ℕ)*W.a₆ - (10:R)*W.a₂*W.a₄^ (2 : ℕ) + (6:R)*W.a₃^ (2 : ℕ)*W.a₄ + (18:R)*W.a₄*W.a₆) * (Xl 0)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C ((18:R)*W.a₁) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 0)
    + C ((4:R)*W.a₁^ (3 : ℕ) + (7:R)*W.a₁*W.a₂) * (Xl 1)^ (3 : ℕ)*(Xl 2)*(Xr 2)
    + C (W.a₁^ (4 : ℕ) - (3:R)*W.a₁^ (2 : ℕ)*W.a₂ + (36:R)*W.a₁*W.a₃ - (4:R)*W.a₂^ (2 : ℕ) + (18:R)*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ) + W.a₁*W.a₂) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂ + (9:R)*W.a₁^ (3 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ) + (5:R)*W.a₁^ (2 : ℕ)*W.a₄ + (15:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂^ (3 : ℕ) + (8:R)*W.a₂*W.a₄) * (Xl 1)^ (2 : ℕ)*(Xl 2)^ (2 : ℕ)*(Xr 2)
    + C (W.a₁^ (4 : ℕ)*W.a₃ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₃ + (18:R)*W.a₁*W.a₃^ (2 : ℕ) - (18:R)*W.a₁*W.a₆ - (4:R)*W.a₂^ (2 : ℕ)*W.a₃ + (18:R)*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 0)
    + C (W.a₁^ (3 : ℕ)*W.a₃ + W.a₁*W.a₂*W.a₃) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 1)
    + C (-W.a₁^ (4 : ℕ)*W.a₂*W.a₃ + (5:R)*W.a₁^ (3 : ℕ)*W.a₃^ (2 : ℕ) - (3:R)*W.a₁^ (3 : ℕ)*W.a₆ - (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₃ + (4:R)*W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + (9:R)*W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₂^ (3 : ℕ)*W.a₃ + (8:R)*W.a₂*W.a₃*W.a₄) * (Xl 1)*(Xl 2)^ (3 : ℕ)*(Xr 2)
    + C (-W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (9:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - (18:R)*W.a₁*W.a₃*W.a₆ + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (12:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (18:R)*W.a₄*W.a₆) * (Xl 2)^ (4 : ℕ)*(Xr 0)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 1)
    + C (W.a₁^ (4 : ℕ)*W.a₂*W.a₆ - (3:R)*W.a₁^ (3 : ℕ)*W.a₃*W.a₆ + (3:R)*W.a₁^ (2 : ℕ)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ - (3:R)*W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + (2:R)*W.a₁*W.a₂*W.a₃^ (3 : ℕ) - (4:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + (2:R)*W.a₂^ (3 : ℕ)*W.a₆ + (2:R)*W.a₂*W.a₃^ (2 : ℕ)*W.a₄ - (2:R)*W.a₄^ (3 : ℕ)) * (Xl 2)^ (4 : ℕ)*(Xr 2)


-- @@ L565-574 verbatim
theorem kw_lrSym_minor_XZ :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      = kw_lrSym_pXZ W * WP₁ + kw_lrSym_qXZ W * WP₂ := by
  simp only [kw_lrSym_X, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pXZ, kw_lrSym_qXZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


-- @@ L576-581 verbatim
theorem kw_lrSym_minor_XZ_mem_span :
    kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_XZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


-- @@ L583-592 verbatim
theorem kw_lrSym_minor_YZ :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      = kw_lrSym_pYZ W * WP₁ + kw_lrSym_qYZ W * WP₂ := by
  simp only [kw_lrSym_Y, kw_lrSym_Z, kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrSym_pYZ, kw_lrSym_qYZ, kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


-- @@ L594-599 verbatim
theorem kw_lrSym_minor_YZ_mem_span :
    kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrSym_minor_YZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


-- @@ L601-601 verbatim
end Minors


-- @@ L603-603 verbatim
section Diag


-- @@ L605-617 verbatim
def kw_lrSym_dblX : MvPolynomial (Fin 3) R :=
  C (-W.a₁*W.a₂) * (X 0)^ (4 : ℕ)
    + C (W.a₁^ (2 : ℕ) - (2:R)*W.a₂) * (X 0)^ (3 : ℕ)*(X 1)
    + C (-W.a₁^ (2 : ℕ)*W.a₃ - (3:R)*W.a₁*W.a₄ - W.a₂*W.a₃) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁) * (X 0)^ (2 : ℕ)*(X 1)^ (2 : ℕ)
    + C (-(6:R)*W.a₄) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C (-(3:R)*W.a₁*W.a₃^ (2 : ℕ) - (9:R)*W.a₁*W.a₆ - (3:R)*W.a₃*W.a₄) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((2:R)) * (X 0)*(X 1)^ (3 : ℕ)
    + C ((3:R)*W.a₃) * (X 0)*(X 1)^ (2 : ℕ)*(X 2)
    + C (-(3:R)*W.a₃^ (2 : ℕ) - (18:R)*W.a₆) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C (-W.a₁^ (3 : ℕ)*W.a₆ + W.a₁^ (2 : ℕ)*W.a₃*W.a₄ - W.a₁*W.a₂*W.a₃^ (2 : ℕ) - (4:R)*W.a₁*W.a₂*W.a₆ + W.a₁*W.a₄^ (2 : ℕ) - (2:R)*W.a₃^ (3 : ℕ) - (9:R)*W.a₃*W.a₆) * (X 0)*(X 2)^ (3 : ℕ)
    + C (-(2:R)*W.a₁^ (2 : ℕ)*W.a₆ + (2:R)*W.a₁*W.a₃*W.a₄ - (2:R)*W.a₂*W.a₃^ (2 : ℕ) - (8:R)*W.a₂*W.a₆ + (2:R)*W.a₄^ (2 : ℕ)) * (X 1)*(X 2)^ (3 : ℕ)
    + C (-W.a₁^ (2 : ℕ)*W.a₃*W.a₆ + W.a₁*W.a₃^ (2 : ℕ)*W.a₄ - W.a₂*W.a₃^ (3 : ℕ) - (4:R)*W.a₂*W.a₃*W.a₆ + W.a₃*W.a₄^ (2 : ℕ)) * (X 2)^ (4 : ℕ)


-- @@ L619-631 verbatim
def kw_lrSym_dblY : MvPolynomial (Fin 3) R :=
  C (-W.a₂^ (2 : ℕ) + (3:R)*W.a₄) * (X 0)^ (4 : ℕ)
    + C (W.a₁*W.a₂ - (3:R)*W.a₃) * (X 0)^ (3 : ℕ)*(X 1)
    + C (W.a₁^ (2 : ℕ)*W.a₄ - (2:R)*W.a₁*W.a₂*W.a₃ - (2:R)*W.a₂*W.a₄ + (3:R)*W.a₃^ (2 : ℕ) + (18:R)*W.a₆) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁*W.a₄ - (3:R)*W.a₂*W.a₃) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C ((9:R)*W.a₁^ (2 : ℕ)*W.a₆ - (6:R)*W.a₁*W.a₃*W.a₄ + (3:R)*W.a₂*W.a₃^ (2 : ℕ) + (18:R)*W.a₂*W.a₆ - (6:R)*W.a₄^ (2 : ℕ)) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C (W.a₁) * (X 0)*(X 1)^ (3 : ℕ)
    + C ((9:R)*W.a₁*W.a₆ - (3:R)*W.a₃*W.a₄) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C (W.a₁^ (4 : ℕ)*W.a₆ - W.a₁^ (3 : ℕ)*W.a₃*W.a₄ + W.a₁^ (2 : ℕ)*W.a₂*W.a₃^ (2 : ℕ) + (6:R)*W.a₁^ (2 : ℕ)*W.a₂*W.a₆ - W.a₁^ (2 : ℕ)*W.a₄^ (2 : ℕ) - (2:R)*W.a₁*W.a₂*W.a₃*W.a₄ - W.a₁*W.a₃^ (3 : ℕ) + (2:R)*W.a₂^ (2 : ℕ)*W.a₃^ (2 : ℕ) + (8:R)*W.a₂^ (2 : ℕ)*W.a₆ - (2:R)*W.a₂*W.a₄^ (2 : ℕ) - (3:R)*W.a₃^ (2 : ℕ)*W.a₄ - (6:R)*W.a₄*W.a₆) * (X 0)*(X 2)^ (3 : ℕ)
    + C ((1:R)) * (X 1)^ (4 : ℕ)
    + C (W.a₃) * (X 1)^ (3 : ℕ)*(X 2)
    + C (W.a₁^ (3 : ℕ)*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃*W.a₄ + W.a₁*W.a₂*W.a₃^ (2 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₆ - W.a₁*W.a₄^ (2 : ℕ) - W.a₃^ (3 : ℕ) - (3:R)*W.a₃*W.a₆) * (X 1)*(X 2)^ (3 : ℕ)
    + C (W.a₁^ (3 : ℕ)*W.a₃*W.a₆ - W.a₁^ (2 : ℕ)*W.a₃^ (2 : ℕ)*W.a₄ + W.a₁^ (2 : ℕ)*W.a₄*W.a₆ + W.a₁*W.a₂*W.a₃^ (3 : ℕ) + (4:R)*W.a₁*W.a₂*W.a₃*W.a₆ - (2:R)*W.a₁*W.a₃*W.a₄^ (2 : ℕ) + W.a₂*W.a₃^ (2 : ℕ)*W.a₄ + (4:R)*W.a₂*W.a₄*W.a₆ - W.a₃^ (4 : ℕ) - (6:R)*W.a₃^ (2 : ℕ)*W.a₆ - W.a₄^ (3 : ℕ) - (9:R)*W.a₆^ (2 : ℕ)) * (X 2)^ (4 : ℕ)


-- @@ L633-645 verbatim
def kw_lrSym_dblZ : MvPolynomial (Fin 3) R :=
  C ((3:R)*W.a₁) * (X 0)^ (4 : ℕ)
    + C ((6:R)) * (X 0)^ (3 : ℕ)*(X 1)
    + C (W.a₁^ (3 : ℕ) + (3:R)*W.a₁*W.a₂ + (3:R)*W.a₃) * (X 0)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₁^ (2 : ℕ) + (6:R)*W.a₂) * (X 0)^ (2 : ℕ)*(X 1)*(X 2)
    + C ((3:R)*W.a₁^ (2 : ℕ)*W.a₃ + (3:R)*W.a₁*W.a₄ + (3:R)*W.a₂*W.a₃) * (X 0)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁) * (X 0)*(X 1)^ (2 : ℕ)*(X 2)
    + C ((6:R)*W.a₁*W.a₃ + (6:R)*W.a₄) * (X 0)*(X 1)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₁*W.a₃^ (2 : ℕ) + (3:R)*W.a₁*W.a₆ + (3:R)*W.a₃*W.a₄) * (X 0)*(X 2)^ (3 : ℕ)
    + C ((2:R)) * (X 1)^ (3 : ℕ)*(X 2)
    + C ((3:R)*W.a₃) * (X 1)^ (2 : ℕ)*(X 2)^ (2 : ℕ)
    + C ((3:R)*W.a₃^ (2 : ℕ) + (6:R)*W.a₆) * (X 1)*(X 2)^ (3 : ℕ)
    + C (W.a₃^ (3 : ℕ) + (3:R)*W.a₃*W.a₆) * (X 2)^ (4 : ℕ)


-- @@ L647-647 verbatim
end Diag


-- @@ L649-649 verbatim
end WeierstrassProjModel


-- @@ L651-651 verbatim
end


-- @@ L653-653 verbatim
end MEGA_KwLRSymAddFormulas_lean
