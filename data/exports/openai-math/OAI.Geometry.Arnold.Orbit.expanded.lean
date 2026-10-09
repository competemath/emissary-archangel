import OAI.Geometry.Arnold.Differentiation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators ContDiff

-- @@ L7-7 verbatim
open MeasureTheory Set Filter

-- @@ L8-8 verbatim
open scoped Matrix.Norms.Operator


-- @@ L10-10 verbatim
namespace ArnoldCounterexample


-- @@ L12-12 verbatim
namespace CriticalBound

-- @@ L13-13 verbatim
open Matrix


-- @@ L15-16 verbatim
/-- Complexification of a real matrix, with the actual complex-linear action. -/
def complexMat (A : RM) : Matrix (Fin 5) (Fin 5) ℂ := A.map Complex.ofReal


-- @@ L18-18 verbatim
def act (A : RM) (z : CV) : CV := (complexMat A).mulVec z


-- @@ L20-22 verbatim
lemma complexMat_mul (A B : RM) : complexMat (A * B) = complexMat A * complexMat B := by
  ext i j
  simp [complexMat, Matrix.mul_apply]


-- @@ L24-26 verbatim
lemma complexMat_star (A : RM) : complexMat (star A) = star (complexMat A) := by
  ext i j
  simp [complexMat, Matrix.star_apply]


-- @@ L28-30 verbatim
lemma complexMat_one : complexMat 1 = 1 := by
  ext i j
  simp [complexMat, Matrix.one_apply, apply_ite Complex.ofReal]


-- @@ L32-33 verbatim
lemma act_mul (A B : RM) (z : CV) : act (A * B) z = act A (act B z) := by
  simp [act, complexMat_mul, Matrix.mulVec_mulVec]


-- @@ L35-36 verbatim
lemma act_smul (A : RM) (a : ℂ) (z : CV) : act A (a • z) = a • act A z := by
  exact Matrix.mulVec_smul _ _ _


-- @@ L38-40 verbatim
lemma act_sub_left (A B : RM) (z : CV) : act (A - B) z = act A z - act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]


-- @@ L42-50 verbatim
lemma act_preserves_hermitian (A : O5) (z w : CV) :
    star (act A z) ⬝ᵥ act A w = star z ⬝ᵥ w := by
  have hA : star (complexMat A) * complexMat A = 1 := by
    rw [← complexMat_star, ← complexMat_mul, A.property.1, complexMat_one]
  calc
    star (act A z) ⬝ᵥ act A w = (star z ᵥ* star (complexMat A)) ⬝ᵥ (complexMat A *ᵥ w) := by
      simp only [act, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    _ = star z ⬝ᵥ (star (complexMat A) *ᵥ (complexMat A *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = star z ⬝ᵥ w := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]


-- @@ L52-54 verbatim
lemma omega_act (A : O5) (v w : CV) : omega (act A v) (act A w) = omega v w := by
  unfold omega
  exact congrArg (fun a : ℂ ↦ 2 * a.im) (act_preserves_hermitian A v w)


-- @@ L56-57 verbatim
/-- Elementary skew matrix rotating the `(a,b)` coordinate plane. -/
def rotGen (a b : Fin 5) : RM := Matrix.single b a 1 - Matrix.single a b 1


-- @@ L59-61 verbatim
lemma rotGen_skew (a b : Fin 5) : star (rotGen a b) = -rotGen a b := by
  ext i j
  simp [rotGen, Matrix.star_apply, Matrix.single_apply, sub_eq_add_neg, and_comm]


-- @@ L63-72 verbatim
lemma rotGen_act (a b : Fin 5) (z : CV) :
    act (rotGen a b) z = Pi.single b (z a) - Pi.single a (z b) := by
  change (complexMat (Matrix.single b a 1 - Matrix.single a b 1)).mulVec z = _
  have h : complexMat (Matrix.single b a 1 - Matrix.single a b 1) =
      Matrix.single b a (1 : ℂ) - Matrix.single a b 1 := by
    ext i j
    simp [complexMat, Matrix.single_apply, apply_ite Complex.ofReal]
  rw [h, Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  ext i
  simp [Function.update_apply, Pi.single_apply, eq_comm]


-- @@ L74-74 verbatim
end CriticalBound

-- @@ L75-75 verbatim
end ArnoldCounterexample


-- @@ L77-77 verbatim
namespace ArnoldCounterexample.CriticalBound


-- @@ L79-79 verbatim
noncomputable def baseScale : ℝ := Real.sqrt (1 / 2)


-- @@ L81-81 verbatim
lemma baseScale_sq : baseScale ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)


-- @@ L83-83 verbatim
lemma baseScale_pos : 0 < baseScale := Real.sqrt_pos.2 (by norm_num)


-- @@ L85-85 verbatim
def base : CV := ![(baseScale : ℂ), baseScale * Complex.I, 0, 0, 0]


-- @@ L87-92 verbatim
lemma base_unit : IsUnitQuadric base := by
  constructor
  · simp [normSquared, base, Fin.sum_univ_succ, Complex.normSq_mul,
      Complex.normSq_ofReal, ← sq, baseScale_sq]
    norm_num
  · simp [quadricPolynomial, base, Fin.sum_univ_succ, mul_pow, Complex.I_sq]


-- @@ L94-95 verbatim
def generators : Fin 6 → RM :=
  ![rotGen 0 2, rotGen 1 2, rotGen 0 3, rotGen 1 3, rotGen 0 4, rotGen 1 4]


-- @@ L97-100 verbatim
def velocities : Fin 6 → CV :=
  ![Pi.single 2 (baseScale : ℂ), Pi.single 2 (baseScale * Complex.I),
    Pi.single 3 (baseScale : ℂ), Pi.single 3 (baseScale * Complex.I),
    Pi.single 4 (baseScale : ℂ), Pi.single 4 (baseScale * Complex.I)]


-- @@ L102-103 verbatim
lemma generators_skew (i : Fin 6) : star (generators i) = -generators i := by
  fin_cases i <;> exact rotGen_skew _ _


-- @@ L105-106 verbatim
lemma generators_base (i : Fin 6) : act (generators i) base = velocities i := by
  fin_cases i <;> simp [generators, velocities, rotGen_act, base]


-- @@ L108-114 verbatim
def bracketCoefficient : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0]


-- @@ L116-123 verbatim
lemma generators_bracket_base (i j : Fin 6) :
    act (generators i * generators j - generators j * generators i) base =
      (bracketCoefficient i j : ℂ) • (Complex.I • base) := by
  rw [act_sub_left, act_mul, act_mul, generators_base, generators_base]
  fin_cases i <;> fin_cases j <;>
    ext k <;> fin_cases k <;>
    simp [generators, velocities, rotGen_act, bracketCoefficient, base,
      ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]


-- @@ L125-125 verbatim
end ArnoldCounterexample.CriticalBound


-- @@ L127-127 verbatim
namespace ArnoldCounterexample.CriticalBound


-- @@ L129-131 verbatim
lemma act_add_left (A B : RM) (z : CV) : act (A + B) z = act A z + act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]


-- @@ L133-137 verbatim
lemma act_real_smul_left (c : ℝ) (A : RM) (z : CV) :
    act (c • A) z = c • act A z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
    Complex.real_smul]


-- @@ L139-140 verbatim
local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace


-- @@ L142-146 verbatim
/-- The orbit map at the literal unit isotropic vector, extended linearly. -/
def orbitProjection : RM →L[ℝ] CV :=
  ({ toFun := fun A ↦ act A base
     map_add' := fun A B ↦ act_add_left A B base
     map_smul' := fun c A ↦ act_real_smul_left c A base } : RM →ₗ[ℝ] CV).toContinuousLinearMap


-- @@ L148-148 verbatim
@[simp] lemma orbitProjection_apply (A : RM) : orbitProjection A = act A base := rfl


-- @@ L150-152 verbatim
lemma act_star (A : RM) (z : CV) : act A (star z) = star (act A z) := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct]


-- @@ L154-156 verbatim
lemma act_preserves_bilinear (A : O5) (z w : CV) :
    act A z ⬝ᵥ act A w = z ⬝ᵥ w := by
  simpa only [act_star, star_star] using act_preserves_hermitian A (star z) w


-- @@ L158-160 verbatim
lemma act_preserves_quadricPolynomial (A : O5) (z : CV) :
    quadricPolynomial (act A z) = quadricPolynomial z := by
  simpa only [quadricPolynomial, dotProduct, pow_two] using act_preserves_bilinear A z z


-- @@ L162-163 verbatim
lemma normSquared_eq_re (z : CV) : normSquared z = (star z ⬝ᵥ z).re := by
  simp [normSquared, dotProduct, Complex.normSq, Complex.mul_re]


-- @@ L165-167 verbatim
lemma act_preserves_normSquared (A : O5) (z : CV) :
    normSquared (act A z) = normSquared z := by
  rw [normSquared_eq_re, normSquared_eq_re, act_preserves_hermitian]


-- @@ L169-171 verbatim
lemma act_unit (A : O5) (z : UnitQuadric) : IsUnitQuadric (act A z) := by
  exact ⟨(act_preserves_normSquared A z).trans z.property.1,
    (act_preserves_quadricPolynomial A z).trans z.property.2⟩


-- @@ L173-174 verbatim
lemma orbitProjection_unit (A : O5) : IsUnitQuadric (orbitProjection A) :=
  act_unit A ⟨base, base_unit⟩


-- @@ L176-179 verbatim
/-- A basic form annihilates the genuine circle-fiber direction. -/
def IsBasic {n : ℕ} (η : CV → CV [⋀^Fin (n + 1)]→L[ℝ] ℝ) : Prop :=
  ∀ z : UnitQuadric, ∀ a : ℝ, ∀ v : Fin n → CV,
    η z (Matrix.vecCons ((a : ℂ) • (Complex.I • (z : CV))) v) = 0


-- @@ L181-215 verbatim
/-- Stokes evaluation for basic 5-forms on Q^3, proved by Haar integration
rather than assuming a manifold integration or cohomology theorem. -/
theorem integral_extDeriv_basic_eq_zero
    (η : CV → CV [⋀^Fin 5]→L[ℝ] ℝ) (hη : ContDiff ℝ ∞ η) (hbasic : IsBasic η) :
    ∫ A : O5, extDeriv η (orbitProjection A) (fun i ↦ act A (velocities i)) ∂haar = 0 := by
  let W : RM → MatForm 5 := fun A ↦ (η (orbitProjection A)).compContinuousLinearMap orbitProjection
  have hW : ContDiff ℝ ∞ W := by
    let : TopologicalSpace RM :=
      (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let P : (CV [⋀^Fin 5]→L[ℝ] ℝ) →L[ℝ] MatForm 5 :=
      (ContinuousAlternatingMap.compContinuousLinearMapₗ (ι := Fin 5) (N := ℝ)
        orbitProjection).mkContinuous (‖orbitProjection‖ ^ 5) (by
          intro θ
          simpa only [ContinuousAlternatingMap.compContinuousLinearMapₗ,
            LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_fin, mul_comm] using
            θ.norm_compContinuousLinearMap_le orbitProjection)
    exact P.contDiff.comp (hη.comp orbitProjection.contDiff)
  have hv (A : O5) (i j : Fin 5) :
      W A (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
        generators j.succ * generators i.castSucc))
        (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0 := by
    change η (orbitProjection A) (orbitProjection ∘ _) = 0
    simp only [Matrix.vecCons, Fin.comp_cons]
    simp only [orbitProjection_apply, act_mul, generators_bracket_base, act_smul]
    exact hbasic ⟨orbitProjection A, orbitProjection_unit A⟩ _ _
  have hz := integral_extDeriv_rightMul_eq_zero W hW generators generators_skew hv
  convert! hz using 1
  congr 1
  funext A
  have hp := extDeriv_pullback (hη.differentiable (by simp) (orbitProjection A))
    (orbitProjection.contDiff.contDiffAt : ContDiffAt ℝ 2 orbitProjection (A : RM)) (by simp)
  simp only [ContinuousLinearMap.fderiv] at hp
  have heval := congrArg (fun f : MatForm 6 ↦ f (fun i ↦ (A : RM) * generators i)) hp
  simpa only [W, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, orbitProjection_apply, act_mul, generators_base] using heval.symm


-- @@ L217-217 verbatim
end ArnoldCounterexample.CriticalBound


-- @@ L219-219 verbatim
end


-- @@ L221-221 verbatim
end OAI
