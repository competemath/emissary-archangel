import OAI.Analysis.Unitarizability.Model
import OAI.Analysis.Unitarizability.Cocycle
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.lpHolder


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
/-! Bounded Hilbert sums and triangular representations. -/

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace Dixmier

-- @@ L11-11 verbatim
namespace Triangular

-- @@ L12-12 verbatim
variable {G H : Type*} [Group G]

-- @@ L13-13 verbatim
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- @@ L14-14 verbatim
abbrev Double (H : Type*) := WithLp 2 (H × H)


-- @@ L16-18 verbatim
def inl : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)


-- @@ L20-22 verbatim
def inr : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)


-- @@ L24-24 verbatim
@[simp] theorem inl_apply (x : H) : inl x = WithLp.toLp 2 (x,0) := rfl

-- @@ L25-25 verbatim
@[simp] theorem inr_apply (x : H) : inr x = WithLp.toLp 2 (0,x) := rfl

-- @@ L26-26 verbatim
@[simp] theorem inl_norm (x : H) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 H H x

-- @@ L27-27 verbatim
@[simp] theorem inr_norm (x : H) : ‖inr x‖ = ‖x‖ := WithLp.norm_toLp_snd 2 H H x


-- @@ L29-31 verbatim
def diagonal (U : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  inl.comp (U.comp (WithLp.fstL 2 ℂ H H)) +
    inr.comp (U.comp (WithLp.sndL 2 ℂ H H))


-- @@ L33-34 verbatim
@[simp] theorem diagonal_fst (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).fst = U x.fst := by simp [diagonal, inl, inr]

-- @@ L35-36 verbatim
@[simp] theorem diagonal_snd (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).snd = U x.snd := by simp [diagonal, inl, inr]


-- @@ L38-39 verbatim
def operator (U D : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal U + inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))


-- @@ L41-42 verbatim
@[simp] theorem operator_fst (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).fst = U x.fst + D (U x.snd) := by simp [operator, inl]

-- @@ L43-44 verbatim
@[simp] theorem operator_snd (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).snd = U x.snd := by simp [operator, inl]


-- @@ L46-50 verbatim
theorem diagonal_norm_map (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : Double H) :
    ‖diagonal U x‖ = ‖x‖ := by
  have h : ‖diagonal U x‖^2 = ‖x‖^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, diagonal_fst, diagonal_snd, hU]
  nlinarith [norm_nonneg (diagonal U x), norm_nonneg x]


-- @@ L52-68 verbatim
theorem operator_norm_le (U D : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    ‖operator U D‖ ≤ 1 + ‖D‖ := by
  have hd : ‖diagonal U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [diagonal_norm_map U hU]
  have hn : ‖inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    change ‖inl (D (U x.snd))‖ ≤ ‖D‖ * ‖x‖
    rw [inl_norm]
    calc
      ‖D (U x.snd)‖ ≤ ‖D‖ * ‖U x.snd‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x.snd‖ := by rw [hU]
      _ ≤ ‖D‖ * ‖x‖ := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H x) (norm_nonneg D)
  exact (norm_add_le (diagonal U) (inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H))))).trans
    (add_le_add hd hn)


-- @@ L70-72 verbatim
@[simp] theorem inv_apply (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g⁻¹ (U g x) = x := by
  have h : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h


-- @@ L74-93 verbatim
def representation (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h)) :
    G →* (Double H →L[ℂ] Double H) where
  toFun g := operator (U g) (D g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [h1]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change (operator (U (g*h)) (D (g*h)) x).fst =
        (operator (U g) (D g) (operator (U h) (D h) x)).fst
      simp only [operator_fst, operator_snd, map_mul, hD, conjugate,
        add_apply, mul_apply_eq_comp, map_add, inv_apply]
      abel
    · simp [map_mul, mul_apply_eq_comp]


-- @@ L95-99 verbatim
theorem representation_bound (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) {κ : ℝ} (hb : ∀ g, ‖D g‖ ≤ κ) (g : G) :
    ‖representation U D h1 hD g‖ ≤ 1 + κ :=
  (operator_norm_le (U g) (D g) (hU g)).trans (add_le_add (le_refl _) (hb g))


-- @@ L101-101 verbatim
end Triangular

-- @@ L102-102 verbatim
end Dixmier


-- @@ L104-104 verbatim
end


-- @@ L106-106 verbatim
end OAI
