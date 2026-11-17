import TubalTensor.Modules.DotProduct
import TubalTensor.Modules.TensorMatrix
import TubalTensor.Prerequisites.SVD
import TubalTensor.RingStructure.WeakInverse


-- @@ L6-14 verbatim
/-!
  TubalTensor/SVD/HilbertAlgebra.lean
  Proposition 70, Proposition 71.

  The Hilbert algebra structure: when M = DW (D real invertible diagonal,
  W unitary), the Frobenius inner product satisfies
    ⟨a ⋆_M x, y⟩_F = ⟨x, a* ⋆_M y⟩_F   (Prop 37, for tubes)
    ⟨A ⋆_M X, Y⟩_F = ⟨X, Aᴴ ⋆_M Y⟩_F   (Prop 38, for tensors)
-/


-- @@ L16-16 verbatim
namespace TubalTensor


-- @@ L18-18 verbatim
open BigOperators Matrix Complex Classical


-- @@ L20-20 verbatim
variable {n : ℕ} {td : TubalData n} {m p : ℕ}


-- @@ L22-22 verbatim
/-! ## Frobenius inner product -/


-- @@ L24-26 verbatim
/-- Real Frobenius inner product for tubes: ⟨a, b⟩_F = ∑_k a_k b_k. -/
noncomputable def tubeFrobInner (a b : KM n td) : ℝ :=
  ∑ k : Fin n, KM.toFun a k * KM.toFun b k


-- @@ L28-30 verbatim
/-- Real Frobenius inner product for oriented matrices: ⟨U, V⟩_F = ∑_i ⟨U_i, V_i⟩_F. -/
noncomputable def omFrobInner (U V : Fin m → KM n td) : ℝ :=
  ∑ i : Fin m, tubeFrobInner (U i) (V i)


-- @@ L32-32 verbatim
/-! ## IsDiagUnitary: M = DW for real invertible diagonal D and unitary W -/


-- @@ L34-38 verbatim
/-- M is a product of a real invertible diagonal and a unitary matrix. -/
def IsDiagUnitary (td : TubalData n) : Prop :=
  ∃ (D : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ),
    (∀ i, D i ≠ 0) ∧ IsUnitary W ∧
    td.M = Matrix.diagonal (fun i => (D i : ℂ)) * W


-- @@ L40-50 verbatim
/-! ## Prop 37: Hilbert algebra identity for tubes

  Proof strategy: both sides equal Re(∑_k D_k conj(α_k) conj(ξ_k) η_k)
  where α = Wa, ξ = Wx, η = Wy and M = DW.

  Key steps:
  1. ∑ u_k v_k = Re(∑ conj((Wu)_k)(Wv)_k) for real u, v  (Parseval for unitaries)
  2. W(a⋆x) at component k = D_k (Wa)_k (Wx)_k
  3. W(a*⋆y) at component k = D_k conj((Wa)_k) (Wy)_k
  4. Both Hermitian products give the same sum.
-/


-- @@ L52-93 verbatim
/-- Parseval bilinear: for unitary W, ∑_k conj((Wf)_k)(Wg)_k = ∑_k conj(f_k) g_k. -/
private theorem parseval_bilinear {n' : ℕ}
    (W : Matrix (Fin n') (Fin n') ℂ) (hW : IsUnitary W) (f g : Fin n' → ℂ) :
    ∑ k, starRingEnd ℂ ((W *ᵥ f) k) * ((W *ᵥ g) k) =
    ∑ k, starRingEnd ℂ (f k) * (g k) := by
  -- ∑_k conj(W_kj) * W_kl = (Wᴴ * W)_jl = δ_jl
  have hWHW : ∀ j l : Fin n',
      ∑ k, starRingEnd ℂ (W k j) * W k l = if j = l then 1 else 0 := by
    intro j l
    -- (Wᴴ * W)_{jl} = (1)_{jl}
    have h := congr_fun (congr_fun hW j) l
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at h
    -- h : ∑ k, star (W k j) * W k l = if j = l then 1 else 0
    -- We need: ∑ k, starRingEnd ℂ (W k j) * W k l = if j = l then 1 else 0
    -- These are the same since star = starRingEnd ℂ for Complex
    exact h
  -- Expand mulVec into sums
  simp only [Matrix.mulVec, dotProduct]
  -- LHS: ∑_k conj(∑_j W_kj f_j) * (∑_l W_kl g_l)
  -- Distribute conj over sum and expand products
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  -- Now: ∑_k ∑_j ∑_l conj(W_kj) * conj(f_j) * (W_kl * g_l)
  -- Rearrange to: ∑_j ∑_l (conj(f_j) * g_l) * ∑_k conj(W_kj) * W_kl
  -- Use ∑_k conj(W_kj) * W_kl = δ_jl, then collapse
  -- Step 1: swap outer sum to get ∑_j as outermost
  rw [Finset.sum_comm]
  congr 1; funext j
  -- Goal: ∑_k ∑_l conj(W_kj) * conj(f_j) * (W_kl * g_l) = conj(f_j) * g_j
  -- Step 2: swap to ∑_l ∑_k
  rw [Finset.sum_comm]
  -- Goal: ∑_l ∑_k conj(W_kj) * conj(f_j) * (W_kl * g_l) = conj(f_j) * g_j
  -- Step 3: In the inner sum over k, factor out conj(f_j) * g_l (which are constant in k)
  -- summand = conj(f_j) * g_l * (conj(W_kj) * W_kl) as a function of k
  -- But we need to show this is = g_l * conj(f_j) * (conj(W_kj) * W_kl)
  -- Step 3: Rewrite inner sum: ∑_k expr(k) = conj(f_j) * g_l * (∑_k conj(W_kj) * W_kl)
  have step3 : ∀ l : Fin n',
    ∑ k, starRingEnd ℂ (W k j) * starRingEnd ℂ (f j) * (W k l * g l) =
    starRingEnd ℂ (f j) * g l * (∑ k, starRingEnd ℂ (W k j) * W k l) := by
    intro l; rw [Finset.mul_sum]; congr 1; funext k; ring
  simp_rw [step3]
  simp_rw [hWHW]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]


-- @@ L95-203 verbatim
/-- **Proposition 70.** Suppose M = DW for some invertible real diagonal D and
    unitary W. Then for every a, x, y ∈ K_M we have
    ⟨a ⋆_M x, y⟩_F = ⟨x, a* ⋆_M y⟩_F. -/
theorem hilbert_algebra_tube (hDU : IsDiagUnitary td)
    (a x y : KM n td) :
    tubeFrobInner (a * x) y = tubeFrobInner x (star a * y) := by
  obtain ⟨D, W, hDnz, hW, hM⟩ := hDU
  -- Notation: a' = toComplex a, etc.
  set a' := toComplex (KM.toFun a)
  set x' := toComplex (KM.toFun x)
  set y' := toComplex (KM.toFun y)
  -- The ℂ-diagonal: D_ℂ i = (D i : ℂ)
  set Dc : Fin n → ℂ := fun i => (D i : ℂ)
  -- Complex product: toComplex(a * x) = starMC td a' x'
  have h_ax : toComplex (KM.toFun (a * x)) = starMC td a' x' := by
    change toComplex (starM td (KM.toFun a) (KM.toFun x)) = _
    exact starM_eq_starMC td _ _
  -- Complex star product: toComplex(star a * y) = starMC td (starConjC td a') y'
  have h_say : toComplex (KM.toFun (star a * y)) =
      starMC td (starConjC td a') y' := by
    change toComplex (starM td (starConjM td (KM.toFun a)) (KM.toFun y)) = _
    rw [starM_eq_starMC, starConjM_eq_starConjC]
  -- Both sides are real inner products ∑_k u_k v_k
  -- We express them as Re(∑_k conj((W u')_k) * (W v')_k) via Parseval.
  -- Step 1: tubeFrobInner u v = Re(∑_k conj((W toComplex u)_k) * (W toComplex v)_k)
  -- First, tubeFrobInner u v = ∑_k u_k v_k = Re(∑_k (u_k : ℂ) * (v_k : ℂ))
  have frob_eq_re : ∀ u v : KM n td,
      (tubeFrobInner u v : ℂ) =
      ∑ k, starRingEnd ℂ ((W *ᵥ toComplex (KM.toFun u)) k) *
        ((W *ᵥ toComplex (KM.toFun v)) k) := by
    intro u v
    unfold tubeFrobInner
    push_cast
    -- ∑_k (u_k : ℂ) * (v_k : ℂ) = ∑_k conj(u_k : ℂ) * (v_k : ℂ) since u, v are real
    conv_lhs =>
      arg 2; ext k
      rw [show (KM.toFun u k : ℂ) = toComplex (KM.toFun u) k from by simp,
          show (KM.toFun v k : ℂ) = toComplex (KM.toFun v) k from by simp,
          show toComplex (KM.toFun u) k = starRingEnd ℂ (toComplex (KM.toFun u) k)
            from by simp [toComplex_apply, Complex.conj_ofReal]]
    exact (parseval_bilinear W hW _ _).symm
  -- Cast to ℂ: it suffices to show the complex versions are equal
  suffices h : (tubeFrobInner (a * x) y : ℂ) = (tubeFrobInner x (star a * y) : ℂ) from
    Complex.ofReal_injective h
  rw [frob_eq_re, frob_eq_re]
  -- Key identity: diag(Dc) * (W * M_inv) = 1
  have hDW_Minv : diagonal Dc * (W * td.M_inv) = 1 := by
    rw [← Matrix.mul_assoc, ← hM]; exact td.hM_right_inv
  -- (M *ᵥ v)_k = Dc_k * (W *ᵥ v)_k since M = diag(Dc) * W
  have hM_mulVec : ∀ v : Fin n → ℂ, ∀ k : Fin n,
      (td.M *ᵥ v) k = Dc k * (W *ᵥ v) k := by
    intro v k
    rw [hM, show (diagonal Dc * W) *ᵥ v = diagonal Dc *ᵥ (W *ᵥ v) from
      by rw [← mulVec_mulVec], mulVec_diagonal]
  -- (W *ᵥ (M_inv *ᵥ v))_k = (Dc k)⁻¹ * v_k
  have hW_applyMinv : ∀ v : Fin n → ℂ, ∀ k : Fin n,
      (W *ᵥ (td.M_inv *ᵥ v)) k = (Dc k)⁻¹ * v k := by
    intro v k
    have hDc_ne : Dc k ≠ 0 := Complex.ofReal_ne_zero.mpr (hDnz k)
    have h1 : diagonal Dc *ᵥ ((W * td.M_inv) *ᵥ v) = v := by
      rw [mulVec_mulVec, hDW_Minv, one_mulVec]
    have h2 := congr_fun h1 k; rw [mulVec_diagonal] at h2
    rw [mulVec_mulVec, ← h2, ← mul_assoc, inv_mul_cancel₀ hDc_ne, one_mul]
  -- Set up abbreviations for W-applied vectors
  set α := W *ᵥ a'  -- α_k = (Wa')_k
  set ξ := W *ᵥ x'  -- ξ_k = (Wx')_k
  set η := W *ᵥ y'  -- η_k = (Wy')_k
  -- The key: both sides equal ∑_k Dc_k * conj(α_k) * conj(ξ_k) * η_k
  -- It suffices to show each summand matches
  congr 1; funext k
  -- Compute LHS summand
  -- conj((W *ᵥ toComplex(a*x))_k) * (W *ᵥ y')_k
  rw [h_ax, h_say]
  -- LHS: starMC td a' x' = M⁻¹(Ma' ∘ₕ Mx')
  -- W *ᵥ (starMC td a' x') = (W * M_inv) *ᵥ (Ma' ∘ₕ Mx')
  -- = diag(Dc⁻¹) *ᵥ (Ma' ∘ₕ Mx')
  have hW_ax : (W *ᵥ starMC td a' x') k = (Dc k)⁻¹ * (td.applyM a' k * td.applyM x' k) := by
    show (W *ᵥ (td.M_inv *ᵥ (td.applyM a' ∘ₕ td.applyM x'))) k = _
    rw [hW_applyMinv, vecHadamard_apply]
  -- RHS: starMC td (starConjC td a') y' = M⁻¹(M(starConjC td a') ∘ₕ My')
  -- By applyM_starConjC: M(starConjC td a') = vecConj(Ma')
  -- W *ᵥ (starMC td (starConjC td a') y') = diag(Dc⁻¹) *ᵥ (vecConj(Ma') ∘ₕ My')
  have hW_say : (W *ᵥ starMC td (starConjC td a') y') k =
      (Dc k)⁻¹ * (starRingEnd ℂ (td.applyM a' k) * td.applyM y' k) := by
    -- First simplify starMC td (starConjC td a') y':
    -- = applyMinv(applyM(starConjC td a') ∘ₕ applyM y')
    -- applyM(starConjC td a') = vecConj(applyM a') by applyM_starConjC
    have hsc : td.applyM (starConjC td a') = vecConj (td.applyM a') :=
      applyM_starConjC td a'
    show (W *ᵥ (td.M_inv *ᵥ (td.applyM (starConjC td a') ∘ₕ td.applyM y'))) k = _
    rw [hW_applyMinv, vecHadamard_apply, hsc, vecConj_apply]
  -- Now substitute into the goal
  rw [hW_ax, hW_say]
  -- Expand applyM at component k using M = diag(Dc) * W:
  -- (td.applyM a')_k = Dc_k * α_k, etc.
  rw [show td.applyM a' k = Dc k * α k from hM_mulVec a' k,
      show td.applyM x' k = Dc k * ξ k from hM_mulVec x' k,
      show td.applyM y' k = Dc k * η k from hM_mulVec y' k]
  -- Now simplify: Dc is real, so conj(Dc k) = Dc k
  have hDc_conj : starRingEnd ℂ (Dc k) = Dc k := by
    simp [Dc, Complex.conj_ofReal]
  have hDc_ne : Dc k ≠ 0 := Complex.ofReal_ne_zero.mpr (hDnz k)
  -- LHS: conj((Dc k)⁻¹ * (Dc k * α k * (Dc k * ξ k))) * η k
  -- RHS: conj(ξ k) * ((Dc k)⁻¹ * (conj(Dc k * α k) * (Dc k * η k)))
  -- Both reduce to Dc k * conj(α k) * conj(ξ k) * η k
  simp only [map_mul, hDc_conj, map_inv₀]
  -- After simp, both sides should be equal by ring_nf or ring
  -- If not, we need to cancel (Dc k)⁻¹ * Dc k = 1
  ring


-- @@ L205-205 verbatim
/-! ## Prop 38: Hilbert algebra identity for tensors -/


-- @@ L207-215 verbatim
/-- tubeFrobInner is linear in the first argument over ⋆_M-sums. -/
private theorem tubeFrobInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → KM n td) (b : KM n td) :
    tubeFrobInner (∑ i ∈ s, f i) b = ∑ i ∈ s, tubeFrobInner (f i) b := by
  unfold tubeFrobInner
  rw [Finset.sum_comm]
  congr 1; funext k
  rw [show KM.toFun (∑ i ∈ s, f i) k = ∑ i ∈ s, KM.toFun (f i) k from
    Finset.sum_apply k s (fun i => KM.toFun (f i))]
  rw [Finset.sum_mul]


-- @@ L217-225 verbatim
/-- tubeFrobInner is linear in the second argument over ⋆_M-sums. -/
private theorem tubeFrobInner_sum_right {ι : Type*} (s : Finset ι) (a : KM n td) (f : ι → KM n td) :
    tubeFrobInner a (∑ i ∈ s, f i) = ∑ i ∈ s, tubeFrobInner a (f i) := by
  unfold tubeFrobInner
  rw [Finset.sum_comm]
  congr 1; funext k
  rw [show KM.toFun (∑ i ∈ s, f i) k = ∑ i ∈ s, KM.toFun (f i) k from
    Finset.sum_apply k s (fun i => KM.toFun (f i))]
  rw [Finset.mul_sum]


-- @@ L227-242 verbatim
/-- **Proposition 71.** Suppose M = DW. For every A ∈ K_M^{m×p}, X ∈ K_M^p,
    Y ∈ K_M^m, we have ⟨A ⋆_M X, Y⟩_F = ⟨X, Aᴴ ⋆_M Y⟩_F. -/
theorem hilbert_algebra_tensor (hDU : IsDiagUnitary td)
    (A : TubalMatrix m p n td) (X : Fin p → KM n td) (Y : Fin m → KM n td) :
    omFrobInner (A.mulVec X) Y = omFrobInner X (Aᴴ.mulVec Y) := by
  unfold omFrobInner
  -- LHS: ∑_i ⟨(AX)_i, Y_i⟩ where (AX)_i = ∑_j A_{ij} * X_j
  simp only [mulVec, dotProduct]
  -- Distribute inner product over sum in first argument
  simp_rw [tubeFrobInner_sum_left]
  -- ∑_i ∑_j ⟨A_{ij} * X_j, Y_i⟩ = ∑_j ∑_i ⟨A_{ij} * X_j, Y_i⟩
  rw [Finset.sum_comm]
  -- Apply Prop 37: ⟨A_{ij} * X_j, Y_i⟩ = ⟨X_j, (A_{ij})* * Y_i⟩
  simp_rw [hilbert_algebra_tube hDU]
  -- Fold the inner sum back and match conjTranspose
  simp_rw [← tubeFrobInner_sum_right, conjTranspose_apply]


-- @@ L244-244 verbatim
end TubalTensor
