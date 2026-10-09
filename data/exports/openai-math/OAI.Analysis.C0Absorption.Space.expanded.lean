import OAI.Analysis.C0Absorption.Shift


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology NormedSpace

-- @@ L12-12 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L14-17 verbatim
def baseRepresentation (γ : Label) : GeneratedRepresentation concreteBases γ where
  operations := []
  ordered := by simp
  budget := by simpa only [List.map_nil,List.sum_nil] using half_pos (concreteBases.ell_pos (concreteBases.band γ))


-- @@ L19-22 verbatim
theorem baseRepresentation_value (γ : Label) : (baseRepresentation γ).value=correction γ := by
  funext s
  change correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s
  exact correctionBase_restrict γ s


-- @@ L24-25 verbatim
theorem correction_mem_TClass (γ : Label) : correction γ∈TClass concreteBases 0 :=
  ⟨γ,baseRepresentation γ,Nat.zero_le _,(baseRepresentation_value γ).symm⟩


-- @@ L27-27 verbatim
def correctionDualBound : ℝ≥0 := Classical.choose (TClass_pairing_bound concreteBases 0)


-- @@ L29-31 verbatim
theorem correction_pairing_bound (γ : Label) (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    |pairing C0Ball (correction γ) m|≤correctionDualBound*‖m‖ :=
  Classical.choose_spec (TClass_pairing_bound concreteBases 0) (correction γ) (correction_mem_TClass γ) m


-- @@ L33-34 verbatim
def moleculeCorrection : Molecule C0Ball →ₗ[ℝ] BlockC0 :=
  (Finsupp.linearCombination ℝ correctionC0).comp (MoleculeSpace C0Ball).subtype


-- @@ L36-45 verbatim
theorem moleculeCorrection_apply (m : Molecule C0Ball) (γ : Label) :
    moleculeCorrection m γ=pairing C0Ball (correction γ) m := by
  classical
  simp only [moleculeCorrection,pairing,LinearMap.comp_apply,Submodule.subtype_apply,
    Finsupp.linearCombination_apply,Finsupp.sum]
  induction (m.val.support) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,ih,correctionC0_apply]


-- @@ L47-54 verbatim
def initialCorrection : PreSpace (sourceClasses concreteBases) c0Origin →L[ℝ] BlockC0 :=
  (show PreSpace (sourceClasses concreteBases) c0Origin →ₗ[ℝ] BlockC0 from by unfold PreSpace; exact moleculeCorrection).mkContinuous
    correctionDualBound (fun m => by
      apply cfun_norm_le _ (mul_nonneg correctionDualBound.coe_nonneg (norm_nonneg m))
      intro γ
      change |moleculeCorrection m γ|≤_
      exact (congrArg abs (moleculeCorrection_apply (show Molecule C0Ball from m) γ)).le.trans
        (correction_pairing_bound γ m))


-- @@ L56-57 verbatim
def correctionQ : ConcreteSpace →L[ℝ] BlockC0 :=
  initialCorrection.extend (toTestSpace (sourceClasses concreteBases) c0Origin)


-- @@ L59-62 verbatim
theorem correctionQ_coe (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    correctionQ (toTestSpace (sourceClasses concreteBases) c0Origin m)=moleculeCorrection m :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) m


-- @@ L64-66 verbatim
theorem correctionC0_zero : correctionC0 c0Origin=0 := by
  ext γ
  exact correction_zero γ


-- @@ L68-73 verbatim
theorem correctionQ_zeta (s : C0Ball) :
    correctionQ (zeta (sourceClasses concreteBases) c0Origin s)=correctionC0 s := by
  rw [zeta,correctionQ_coe]
  change moleculeCorrection (molecule s c0Origin)=correctionC0 s
  simp only [moleculeCorrection,molecule,LinearMap.comp_apply,Submodule.subtype_apply,map_sub,
    Finsupp.linearCombination_single,one_smul,correctionC0_zero,sub_zero]


-- @@ L75-75 verbatim
def concreteLift : C0 → ConcreteSpace := radialLift (zeta (sourceClasses concreteBases) c0Origin)


-- @@ L77-78 verbatim
theorem concreteLift_lipschitz : LipschitzWith 3 concreteLift :=
  radialLift_lipschitz _ (zeta_lipschitz _ _) (zeta_base _ _)


-- @@ L80-80 verbatim
theorem concreteLift_zero : concreteLift 0=0 := radialLift_zero _


-- @@ L82-83 verbatim
theorem concreteLift_homogeneous {r : ℝ} (hr : 0≤r) (x : C0) : concreteLift (r • x)=r • concreteLift x :=
  radialLift_homogeneous _ hr x


-- @@ L85-91 verbatim
theorem correctionQ_concreteLift (x : C0) : correctionQ (concreteLift x)=recomputedShift x-inputBlocks x := by
  rw [concreteLift,radialLift,map_smul,correctionQ_zeta]
  change ‖x‖ • (frozenCorrectionL (stateWeights (normalizedBall x)) (normalize x))=_
  rw [← map_smul,norm_smul_normalize]
  change frozenCorrectionL (stateWeights (normalizedBall x)) x=
    (inputBlocks x+frozenCorrectionL (stateWeights (normalizedBall x)) x)-inputBlocks x
  abel


-- @@ L93-93 verbatim
end

-- @@ L94-94 verbatim
end C0Absorption


-- @@ L96-96 verbatim
end OAI
