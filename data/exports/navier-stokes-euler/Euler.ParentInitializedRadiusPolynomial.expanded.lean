import Euler.PacketSourceRadiusPolynomial
import Euler.ParentPacketJoinedInput
import Euler.ParentCorrectionCostEnvelope
import Euler.PacketJoinedCoefficientBudgets


-- @@ L6-7 verbatim
/-! Polynomial control of the literal canonical initialized radius built from
the parent fields. The boundary coefficient remains an explicit scalar input. -/


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
namespace EulerParentInitializedRadius


-- @@ L13-14 verbatim
open EulerPacketRadiusPolynomial EulerPacketSourceRadius EulerParentCorrectionCost
  EulerParentCoefficientPolynomial EulerPolynomialCost EulerPacketParentPhysicalBudgets EulerPacketTerminalDatum


-- @@ L16-18 verbatim
def inputEnvelope (X : ℝ) : ℝ :=
  let a := parentConstant period*X^parentPower period
  1+X+a+3*a^3*X


-- @@ L20-23 verbatim
def inputPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let a := Polynomial.C (parentConstant period)*X^parentPower period
  1+X+a+3*a^3*X


-- @@ L25-27 verbatim
theorem inputPolynomial_eval (X : ℝ) : inputPolynomial.eval X=inputEnvelope X := by
  simp only [inputPolynomial,inputEnvelope,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]


-- @@ L29-57 verbatim
theorem inputEnvelope_bounds (K X : ℝ) (hK : 1 ≤ K) (hKX : K ≤ X) :
    1 ≤ inputEnvelope X ∧ X ≤ inputEnvelope X ∧
    leafEnvelope K ≤ inputEnvelope X ∧ parentEnvelope period K ≤ inputEnvelope X ∧
    ∀ Cp : ℝ, 0 ≤ Cp → Cp ≤ X → physicalCost K Cp ≤ inputEnvelope X := by
  have hK0 := zero_le_one.trans hK
  have hX0 := hK0.trans hKX
  let a := parentConstant period*X^parentPower period
  have ha0 : 0 ≤ a := mul_nonneg (parentConstant_pos period).le (pow_nonneg hX0 _)
  have hp : parentEnvelope period K ≤ a :=
    (parentEnvelope_power period K hK).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0 hKX _) (parentConstant_pos period).le)
  have hl : leafEnvelope K ≤ a := (parentEnvelope_bounds period K hK0).2.1.trans hp
  have hf : EulerPacketParentLabelBounds.frameAmplitude K ≤ a := (leaf_bounds K hK0).2.2.2.1.trans hl
  have ha : a ≤ inputEnvelope X := by
    change a ≤ 1+X+a+3*a^3*X
    nlinarith only [hX0,mul_nonneg (pow_nonneg ha0 3) hX0]
  refine ⟨?_,?_,hl.trans ha,hp.trans ha,?_⟩
  · change 1 ≤ 1+X+a+3*a^3*X
    nlinarith only [hX0,ha0,mul_nonneg (pow_nonneg ha0 3) hX0]
  · change X ≤ 1+X+a+3*a^3*X
    nlinarith only [ha0,mul_nonneg (pow_nonneg ha0 3) hX0]
  · intro Cp hCp hCpX
    have hprod : physicalCost K Cp ≤ 3*a^3*X := by
      unfold physicalCost
      gcongr
      exact EulerPacketParentLabelBounds.frameAmplitude_nonneg K
    apply hprod.trans
    change 3*a^3*X ≤ 1+X+a+3*a^3*X
    linarith only [hX0,ha0]


-- @@ L59-59 verbatim
def sourceEnvelope (X : ℝ) : ℝ := sourceRadiusEnvelope (inputEnvelope X)


-- @@ L61-61 verbatim
def sourcePolynomial : Polynomial ℝ := sourceRadiusPolynomial.comp inputPolynomial


-- @@ L63-65 verbatim
theorem sourcePolynomial_eval (X : ℝ) : sourcePolynomial.eval X=sourceEnvelope X := by
  simp only [sourcePolynomial,sourceEnvelope,Polynomial.eval_comp,
    sourceRadiusPolynomial_eval,inputPolynomial_eval]


-- @@ L67-67 verbatim
def sourceConstant : ℝ := coefficientCost sourcePolynomial

-- @@ L68-68 verbatim
def sourcePower : ℕ := sourcePolynomial.natDegree


-- @@ L70-70 verbatim
theorem sourceConstant_pos : 0 < sourceConstant := coefficientCost_pos _


-- @@ L72-75 verbatim
theorem sourceEnvelope_power (X : ℝ) (hX : 1 ≤ X) :
    sourceEnvelope X ≤ sourceConstant*X^sourcePower := by
  rw [← sourcePolynomial_eval]
  exact (le_abs_self _).trans (eval_bound sourcePolynomial X hX)


-- @@ L77-77 verbatim
def parameterSize (K Ti TiTotal Cp B δ N : ℝ) : ℝ := 1+K+Ti+TiTotal+Cp+B+δ⁻¹+N


-- @@ L79-88 verbatim
theorem parameterSize_bounds (K Ti TiTotal Cp B δ N : ℝ)
    (hK : 0 ≤ K) (hTi : 0 ≤ Ti) (hTiTotal : 0 ≤ TiTotal) (hCp : 0 ≤ Cp)
    (hB : 0 ≤ B) (hδ : 0 < δ) (hN : 0 ≤ N) :
    1 ≤ parameterSize K Ti TiTotal Cp B δ N ∧ K ≤ parameterSize K Ti TiTotal Cp B δ N ∧
    Ti ≤ parameterSize K Ti TiTotal Cp B δ N ∧ TiTotal ≤ parameterSize K Ti TiTotal Cp B δ N ∧
    Cp ≤ parameterSize K Ti TiTotal Cp B δ N ∧ B ≤ parameterSize K Ti TiTotal Cp B δ N ∧
    δ⁻¹ ≤ parameterSize K Ti TiTotal Cp B δ N ∧ N ≤ parameterSize K Ti TiTotal Cp B δ N := by
  have hi := (inv_pos.mpr hδ).le
  unfold parameterSize
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩


-- @@ L90-90 verbatim
def fullEnvelope (X : ℝ) : ℝ := radiusEnvelope (sourceEnvelope X)


-- @@ L92-93 verbatim
def fullPolynomial : Polynomial ℝ :=
  radiusPolynomial.comp (sourceRadiusPolynomial.comp inputPolynomial)


-- @@ L95-97 verbatim
theorem fullPolynomial_eval (X : ℝ) : fullPolynomial.eval X=fullEnvelope X := by
  simp only [fullPolynomial,fullEnvelope,sourceEnvelope,Polynomial.eval_comp,radiusPolynomial_eval,
    sourceRadiusPolynomial_eval,inputPolynomial_eval]


-- @@ L99-99 verbatim
def fullConstant : ℝ := coefficientCost fullPolynomial

-- @@ L100-100 verbatim
def fullPower : ℕ := fullPolynomial.natDegree


-- @@ L102-102 verbatim
theorem fullConstant_pos : 0 < fullConstant := coefficientCost_pos _


-- @@ L104-107 verbatim
theorem fullEnvelope_power (X : ℝ) (hX : 1 ≤ X) :
    fullEnvelope X ≤ fullConstant*X^fullPower := by
  rw [← fullPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound fullPolynomial X hX)


-- @@ L109-109 verbatim
end EulerParentInitializedRadius


-- @@ L111-111 verbatim
namespace EulerParentPacketFrames.LabelData


-- @@ L113-117 verbatim
open Set EulerSmoothLimit EulerGevrey EulerMeanCoefficients EulerMeanBoundary
  EulerMeanHarmonic EulerPacketParentLabelBounds EulerParentCoefficientPolynomial
  EulerParentCorrectionCost EulerPacketSourceRadius EulerParentInitializedRadius
  EulerPacketRadiusPolynomial EulerPacketTerminalDatum EulerPacketCylinderField
  EulerPacketSourcePropagator EulerTransversePacketProvider EulerTimeIntervalRestriction


-- @@ L119-130 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (Ti Cp : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) (hCp : 0 ≤ Cp)
  (g : C(Icc (0 : ℝ) (G.T-τ),ℝ)) (hg : ∀ t, 0 < g t)
  (hg0 : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
  (hphysical : PhysicalGrowth ((G.transverseData m hm R S hS).tail τ hτ.le hτT)
    EulerPacketParentPhysicalBudgets.halfBall g Cp)
  (TiTotal : ℝ) (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)


-- @@ L132-133 verbatim
local notation "J" => L.joinedInputs H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
  g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal

-- @@ L134-135 verbatim
local notation "BC" => joinedCoefficientBudget period (G.meanData H) (G.transverseData m hm R S hS)
  rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) (JoinedInputs.normal J)


-- @@ L137-138 verbatim
def canonicalInitializedRadius (δ : ℝ) (ξ : U) : ℝ :=
  initializedRadius (J).mean (J).linear (J).normal BC δ ξ


-- @@ L140-218 verbatim
theorem joined_radius_primitives (δ : ℝ) (ξ : U) (X : ℝ)
    (hKX : L.K ≤ X) (hTiX : Ti ≤ X) (hTiTotalX : TiTotal ≤ X)
    (hCpX : Cp ≤ X) (hLX : H.L ≤ X) (hδX : δ⁻¹ ≤ X) (hξX : ‖ξ‖ ≤ X) :
    RadiusPrimitives (J).mean (J).linear (J).normal BC δ ξ (sourceRadiusEnvelope (inputEnvelope X)) := by
  let W := inputEnvelope X
  let V := sourceRadiusEnvelope W
  have hK0 := zero_le_one.trans L.K_one
  have hb := inputEnvelope_bounds L.K X L.K_one hKX
  have hW : 1 ≤ W := hb.1
  have hW0 := zero_le_one.trans hW
  have hXV : X ≤ V := hb.2.1.trans (le_sourceRadiusEnvelope W hW0)
  have hWV : W ≤ V := le_sourceRadiusEnvelope W hW0
  have hLV : leafEnvelope L.K ≤ V := hb.2.2.1.trans hWV
  have hPW : EulerPacketParentPhysicalBudgets.physicalCost L.K Cp ≤ W := hb.2.2.2.2 Cp hCp hCpX
  have hPV := hPW.trans hWV
  obtain ⟨hl1,hr,hgK,hf,hh,hn,hni,hnr,hgram,hri,hi⟩ := leaf_bounds L.K hK0
  have hLW : leafEnvelope L.K ≤ W := hb.2.2.1
  have hTi0 : 0 ≤ Ti := (inv_nonneg.mpr hτ.le).trans hTi
  have hTiTotal0 : 0 ≤ TiTotal := (inv_nonneg.mpr G.T_pos.le).trans hTiTotal
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  have hjoin : EulerPacketParentTransverseCosts.radius 6 τ (G.T-τ) Ti
      (coefficientRadius L.K) (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K)
      (EulerPacketParentPhysicalBudgets.physicalCost L.K Cp) ≤ V :=
    joined_radius_le τ (G.T-τ) Ti (coefficientRadius L.K) (frameAmplitude L.K)
      (gradientAmplitude L.K) (gradientAmplitude L.K)
      (EulerPacketParentPhysicalBudgets.physicalCost L.K Cp) W hW hτ.le hτ1
      (sub_pos.mpr hτT).le (by linarith) hTi0 (hTiX.trans hb.2.1)
      (coefficientRadius_nonneg L.K) (hr.trans hLW) (frameAmplitude_nonneg L.K) (hf.trans hLW)
      (gradientAmplitude_nonneg L.K) (hgK.trans hLW) (gradientAmplitude_nonneg L.K)
      (EulerPacketParentPhysicalBudgets.physicalCost_nonneg L.K Cp hCp) hPW
      (hh.trans hLW) (hi.trans hLW) (hgram.trans hLW) (hri.trans hLW)
  have hmean : EulerPacketParentMeanBudget.radius 6 G.T TiTotal (coefficientRadius L.K)
      (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L ≤ V :=
    mean_radius_le G.T TiTotal (coefficientRadius L.K) (frameAmplitude L.K)
      (gradientAmplitude L.K) (gradientAmplitude L.K) H.L W hW G.T_pos.le hT1 hTiTotal0
      (hTiTotalX.trans hb.2.1) (coefficientRadius_nonneg L.K) (hr.trans hLW)
      (frameAmplitude_nonneg L.K) (hf.trans hLW) (gradientAmplitude_nonneg L.K) (hgK.trans hLW)
      (gradientAmplitude_nonneg L.K) hL0 (hLX.trans hb.2.1) (hh.trans hLW) (hi.trans hLW) (hgram.trans hLW)
  have hJR : (J).linear.R ≤ V := by
    change max _ (max _ _) ≤ V
    exact max_le hjoin (max_le (hnr.trans hLV) hmean)
  have hci : ((G.transverseData m hm R S hS).initial τ hτ hτT.le).frameLower⁻¹ ≤ V := by
    apply (frameLower_inv_le _ L.K hK0 ?_ ?_).trans hLV
    · intro t x
      exact G.frame_det (initialInclusion G.T τ hτT.le t) x
    · intro t x
      have hf0 := (J).linear.frame_bound 0 (initialInclusion G.T τ hτT.le t) x
      have he : (J).linear.C₀=frameAmplitude L.K := rfl
      change ‖(G.transverseData m hm R S hS).F.field (initialInclusion G.T τ hτT.le t) x‖ ≤ frameAmplitude L.K
      simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
        Nat.cast_one,pow_zero,mul_one,one_pow,he] using hf0
  have hBC := (BC).parent_primitive_bound L.K hK0 hr hn
  change RadiusPrimitives (J).mean (J).linear (J).normal BC δ ξ V
  exact {
    one := hW.trans hWV
    total_time := hT1
    mean_time := hT1
    history_inverse_time := hTi.trans (hTiX.trans hXV)
    mean_inverse_time := hTiTotal.trans (hTiTotalX.trans hXV)
    history_gram := hci
    original_joined := hJR
    original_mean := hJR
    joined_radius := hr.trans hLV
    joined_frame := hf.trans hLV
    joined_first := hgK.trans hLV
    joined_curvature := hh.trans hLV
    joined_propagator := hPV
    joined_inverse := hri.trans hLV
    normal_radius := hr.trans hLV
    normal_amplitude := hn.trans hLV
    normal_inverse := hni.trans hLV
    mean_radius := hr.trans hLV
    mean_frame := hf.trans hLV
    mean_first := hgK.trans hLV
    mean_forcing := hW.trans hWV
    coefficient_radius := hr.trans hLV
    coefficient_cost := hBC.2.trans (hb.2.2.2.1.trans hWV)
    delta_inverse := hδX.trans hXV
    terminal := hξX.trans hXV }


-- @@ L220-230 verbatim
theorem canonicalInitializedRadius_power (δ : ℝ) (hδ : 0 < δ) (ξ : U) (X : ℝ)
    (hKX : L.K ≤ X) (hTiX : Ti ≤ X) (hTiTotalX : TiTotal ≤ X)
    (hCpX : Cp ≤ X) (hLX : H.L ≤ X) (hδX : δ⁻¹ ≤ X) (hξX : ‖ξ‖ ≤ X) :
    L.canonicalInitializedRadius H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
      g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal δ ξ ≤ fullConstant*X^fullPower := by
  have hp := L.joined_radius_primitives H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
    g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal δ ξ X
    hKX hTiX hTiTotalX hCpX hLX hδX hξX
  exact (initializedRadius_le_envelope (J).mean (J).linear (J).normal BC δ ξ
    (sourceRadiusEnvelope (inputEnvelope X)) hδ hp).trans
      (fullEnvelope_power X (L.K_one.trans hKX))


-- @@ L232-242 verbatim
theorem joined_radius_primitive_polynomial (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    let X := parameterSize L.K Ti TiTotal Cp H.L δ ‖ξ‖
    RadiusPrimitives (J).mean (J).linear (J).normal BC δ ξ (sourceEnvelope X) ∧
      sourceEnvelope X ≤ sourceConstant*X^sourcePower := by
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨h1,hK,hI,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K Ti TiTotal Cp H.L δ ‖ξ‖
    (zero_le_one.trans L.K_one) ((inv_pos.mpr hτ).le.trans hTi)
    ((inv_pos.mpr G.T_pos).le.trans hTiTotal) hCp hL0 hδ (norm_nonneg ξ)
  exact ⟨L.joined_radius_primitives H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
    g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal δ ξ _ hK hI hIT hC hB hD hN,
    sourceEnvelope_power _ h1⟩


-- @@ L244-253 verbatim
theorem canonicalInitializedRadius_polynomial (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    L.canonicalInitializedRadius H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
      g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal δ ξ ≤
        fullConstant*(parameterSize L.K Ti TiTotal Cp H.L δ ‖ξ‖)^fullPower := by
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨_,hK,hI,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K Ti TiTotal Cp H.L δ ‖ξ‖
    (zero_le_one.trans L.K_one) ((inv_pos.mpr hτ).le.trans hTi)
    ((inv_pos.mpr G.T_pos).le.trans hTiTotal) hCp hL0 hδ (norm_nonneg ξ)
  exact L.canonicalInitializedRadius_power H m hm R S hS τ hτ hτT Ti Cp hτ1 hTi hCp
    g hg hg0 Ω hΩ hΩo hsub hΩball hphysical TiTotal hT1 hTiTotal δ hδ ξ _ hK hI hIT hC hB hD hN


-- @@ L255-255 verbatim
end EulerParentPacketFrames.LabelData
