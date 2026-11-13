import Submission.StandardSaddleSourceParam
import Submission.StandardBirthFrameClass


-- @@ L4-10 verbatim
/-!
# Winding coordinates for the explicit Cassini saddle frames

This file supplies continuous real angle lifts for the planar normal along the
two incoming Cassini ovals and the outgoing oval.  These are the analytic input
for the final saddle splice calculation.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
set_option maxHeartbeats 1600000


-- @@ L16-16 verbatim
namespace Submission

-- @@ L17-17 verbatim
namespace StandardSaddle


-- @@ L19-19 verbatim
open Set Function Topology InnerProductSpace

-- @@ L20-20 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L22-22 verbatim
variable (m : ℕ)


-- @@ L24-24 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L26-26 verbatim
/-! ## Elementary angle coordinates in the open right half-plane -/


-- @@ L28-48 verbatim
theorem cos_arctan_div {u v : ℝ} (hu : 0 < u) :
    Real.cos (Real.arctan (v / u)) =
      u / Real.sqrt (u ^ 2 + v ^ 2) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hsum : 0 < u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg v]
  have haux : 0 < 1 + (v / u) ^ 2 := by positivity
  have hsqrtAux : 0 ≤ Real.sqrt (1 + (v / u) ^ 2) := Real.sqrt_nonneg _
  have hsqrtSum : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
  have hquotNonneg : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) / u :=
    div_nonneg hsqrtSum hu.le
  have hsqAux : Real.sqrt (1 + (v / u) ^ 2) ^ 2 =
      1 + (v / u) ^ 2 := Real.sq_sqrt haux.le
  have hsqQuot : (Real.sqrt (u ^ 2 + v ^ 2) / u) ^ 2 =
      1 + (v / u) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hsum.le]
    field_simp [hu0]
  have hsqrtEq : Real.sqrt (1 + (v / u) ^ 2) =
      Real.sqrt (u ^ 2 + v ^ 2) / u := by
    nlinarith
  rw [Real.cos_arctan, hsqrtEq]
  field_simp [hu0, (Real.sqrt_pos.2 hsum).ne']


-- @@ L50-70 verbatim
theorem sin_arctan_div {u v : ℝ} (hu : 0 < u) :
    Real.sin (Real.arctan (v / u)) =
      v / Real.sqrt (u ^ 2 + v ^ 2) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hsum : 0 < u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg v]
  have haux : 0 < 1 + (v / u) ^ 2 := by positivity
  have hsqrtAux : 0 ≤ Real.sqrt (1 + (v / u) ^ 2) := Real.sqrt_nonneg _
  have hsqrtSum : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
  have hquotNonneg : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) / u :=
    div_nonneg hsqrtSum hu.le
  have hsqAux : Real.sqrt (1 + (v / u) ^ 2) ^ 2 =
      1 + (v / u) ^ 2 := Real.sq_sqrt haux.le
  have hsqQuot : (Real.sqrt (u ^ 2 + v ^ 2) / u) ^ 2 =
      1 + (v / u) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hsum.le]
    field_simp [hu0]
  have hsqrtEq : Real.sqrt (1 + (v / u) ^ 2) =
      Real.sqrt (u ^ 2 + v ^ 2) / u := by
    nlinarith
  rw [Real.sin_arctan, hsqrtEq]
  field_simp [hu0, (Real.sqrt_pos.2 hsum).ne']


-- @@ L72-72 verbatim
/-! ## Constancy of the intrinsic tangent-orientation sign -/


-- @@ L74-93 verbatim
theorem continuous_nonzero_pos_iff_zero {d : ℝ → ℝ}
    (hd : Continuous d) (hne : ∀ t, d t ≠ 0) (t : ℝ) :
    0 < d t ↔ 0 < d 0 := by
  constructor
  · intro ht
    by_contra hzero
    have hd0neg : d 0 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hzero) (hne 0)
    have hmem : (0 : ℝ) ∈ Set.Icc (d 0) (d t) :=
      ⟨hd0neg.le, ht.le⟩
    obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hd hmem
    exact hne s hs
  · intro hzero
    by_contra ht
    have hdtneg : d t < 0 :=
      lt_of_le_of_ne (le_of_not_gt ht) (hne t)
    have hmem : (0 : ℝ) ∈ Set.Icc (d t) (d 0) :=
      ⟨hdtneg.le, hzero.le⟩
    obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hd hmem
    exact hne s hs


-- @@ L95-97 verbatim
theorem continuous_planarTangent : Continuous (planarTangent m) := by
  unfold planarTangent normalFirst normalSecond radiusSq
  fun_prop


-- @@ L99-103 verbatim
/-- Polynomial, unnormalized determinant used to choose the tangent direction.
Unlike the normalized tangent, this function is continuous on the whole
ambient Euclidean space. -/
def endpointOrientationRaw (a : ℝ) (x : E) : ℝ :=
  crossDet (fun i => gradVec (levelMap m a) i x) (planarTangent m x)


-- @@ L105-117 verbatim
theorem continuous_endpointOrientationRaw (a : ℝ) :
    Continuous (endpointOrientationRaw m a) := by
  unfold endpointOrientationRaw crossDet
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp only [crossRows, Matrix.of_apply, Fin.cons_zero]
    exact (EuclideanSpace.proj j : E →L[ℝ] ℝ).continuous.comp
      (continuous_planarTangent m)
  · simp only [crossRows, Matrix.of_apply, Fin.cons_succ]
    exact (EuclideanSpace.proj j : E →L[ℝ] ℝ).continuous.comp
      (contDiff_gradVec (levelMap m a) (contDiff_levelMap m a) i).continuous


-- @@ L119-129 verbatim
theorem endpointOrientationRaw_ne_zero_of_endpoint
    {a : ℝ} {x : E} (hreg : x ∈ regularSet (levelMap m a))
    (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    endpointOrientationRaw m a x ≠ 0 := by
  intro hzero
  have hunit := crossDet_unitPlanarTangent_ne_zero m hreg hx ha
  apply hunit
  rw [unitPlanarTangent, crossDet_smul]
  change ‖planarTangent m x‖⁻¹ * endpointOrientationRaw m a x = 0
  rw [hzero, mul_zero]


-- @@ L131-165 verbatim
theorem tangentOrientationSign_eq_of_curve
    (a : ℝ) (p : ℝ → E) (hpcont : Continuous p)
    (hp : ∀ t, levelMap m a (p t) = 0)
    (hreg : ∀ t, p t ∈ regularSet (levelMap m a))
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) (t : ℝ) :
    tangentOrientationSign m a (p t) =
      tangentOrientationSign m a (p 0) := by
  let d : ℝ → ℝ := fun s => endpointOrientationRaw m a (p s)
  have hd : Continuous d :=
    (continuous_endpointOrientationRaw m a).comp hpcont
  have hdne : ∀ s, d s ≠ 0 := fun s =>
    endpointOrientationRaw_ne_zero_of_endpoint m (hreg s) (hp s) ha
  have hraw := continuous_nonzero_pos_iff_zero hd hdne t
  have hunitPos : ∀ s,
      0 < crossDet (fun i => gradVec (levelMap m a) i (p s))
          (unitPlanarTangent m (p s)) ↔ 0 < d s := by
    intro s
    rw [unitPlanarTangent, crossDet_smul]
    change 0 < ‖planarTangent m (p s)‖⁻¹ * d s ↔ 0 < d s
    rw [mul_pos_iff_of_pos_left]
    exact inv_pos.mpr (norm_pos_iff.mpr
      (planarTangent_ne_zero_of_endpoint m (hp s) ha))
  have hpos :
      (0 < crossDet (fun i => gradVec (levelMap m a) i (p t))
          (unitPlanarTangent m (p t))) ↔
        0 < crossDet (fun i => gradVec (levelMap m a) i (p 0))
          (unitPlanarTangent m (p 0)) := by
    rw [hunitPos t, hunitPos 0]
    exact hraw
  unfold tangentOrientationSign
  by_cases ht : 0 < crossDet
      (fun i => gradVec (levelMap m a) i (p t))
      (unitPlanarTangent m (p t))
  · rw [if_pos ht, if_pos (hpos.mp ht)]
  · rw [if_neg ht, if_neg (fun h0 => ht (hpos.mpr h0))]


-- @@ L167-167 verbatim
/-! ## A reusable planar-angle frame -/


-- @@ L169-171 verbatim
def anglePlanarNormal (phi : ℝ) : E :=
  Real.cos phi • EuclideanSpace.single (planeFirst m) 1 +
    Real.sin phi • EuclideanSpace.single (planeSecond m) 1


-- @@ L173-175 verbatim
def anglePlanarTangent (phi : ℝ) : E :=
  (-Real.sin phi) • EuclideanSpace.single (planeFirst m) 1 +
    Real.cos phi • EuclideanSpace.single (planeSecond m) 1


-- @@ L177-203 verbatim
theorem anglePlanarTangent_rotation (phi psi : ℝ) :
    anglePlanarTangent m psi =
      Real.cos (psi - phi) • anglePlanarTangent m phi -
        Real.sin (psi - phi) • anglePlanarNormal m phi := by
  apply (WithLp.equiv 2 _).injective
  funext j
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  by_cases hjA : j = planeFirst m
  · subst j
    simp [anglePlanarTangent, anglePlanarNormal, Real.cos_sub, Real.sin_sub,
      hAB]
    have hmul := congrArg (fun z : ℝ => Real.sin psi * z)
      (Real.cos_sq_add_sin_sq phi)
    ring_nf at hmul ⊢
    linarith
  · by_cases hjB : j = planeSecond m
    · subst j
      simp [anglePlanarTangent, anglePlanarNormal, Real.cos_sub, Real.sin_sub,
        hAB.symm]
      have hmul := congrArg (fun z : ℝ => Real.cos psi * z)
        (Real.cos_sq_add_sin_sq phi)
      ring_nf at hmul ⊢
      linarith
    · simp [anglePlanarTangent, anglePlanarNormal, hjA, hjB]


-- @@ L205-231 verbatim
theorem anglePlanarNormal_rotation (phi psi : ℝ) :
    anglePlanarNormal m psi =
      Real.sin (psi - phi) • anglePlanarTangent m phi +
        Real.cos (psi - phi) • anglePlanarNormal m phi := by
  apply (WithLp.equiv 2 _).injective
  funext j
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  by_cases hjA : j = planeFirst m
  · subst j
    simp [anglePlanarTangent, anglePlanarNormal, Real.cos_sub, Real.sin_sub,
      hAB]
    have hmul := congrArg (fun z : ℝ => Real.cos psi * z)
      (Real.cos_sq_add_sin_sq phi)
    ring_nf at hmul ⊢
    linarith
  · by_cases hjB : j = planeSecond m
    · subst j
      simp [anglePlanarTangent, anglePlanarNormal, Real.cos_sub, Real.sin_sub,
        hAB.symm]
      have hmul := congrArg (fun z : ℝ => Real.sin psi * z)
        (Real.cos_sq_add_sin_sq phi)
      ring_nf at hmul ⊢
      linarith
    · simp [anglePlanarTangent, anglePlanarNormal, hjA, hjB]


-- @@ L233-274 verbatim
theorem unitPlanarNormal_eq_anglePlanarNormal {x : E} {phi : ℝ}
    (hfirst : unitPlanarNormal m x (planeFirst m) = Real.cos phi)
    (hsecond : unitPlanarNormal m x (planeSecond m) = Real.sin phi) :
    unitPlanarNormal m x = anglePlanarNormal m phi := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
      change unitPlanarNormal m x (planeSecond m) =
        anglePlanarNormal m phi (planeSecond m)
      rw [hsecond]
      have hBA : planeSecond m ≠ planeFirst m := by
        intro h
        have := congrArg Fin.val h
        simp [planeFirst, planeSecond] at this
      simp [anglePlanarNormal, hBA]
  | cast i =>
      induction i using Fin.lastCases with
      | last =>
          change unitPlanarNormal m x (planeFirst m) =
            anglePlanarNormal m phi (planeFirst m)
          rw [hfirst]
          have hAB : planeFirst m ≠ planeSecond m := by
            intro h
            have := congrArg Fin.val h
            simp [planeFirst, planeSecond] at this
          simp [anglePlanarNormal, hAB]
      | cast j =>
          change unitPlanarNormal m x j.castSucc.castSucc =
            anglePlanarNormal m phi j.castSucc.castSucc
          rw [unitPlanarNormal]
          have hjA : j.castSucc.castSucc ≠ planeFirst m := by
            intro h
            have := congrArg Fin.val h
            simp [planeFirst] at this
            omega
          have hjB : j.castSucc.castSucc ≠ planeSecond m := by
            intro h
            have := congrArg Fin.val h
            simp [planeSecond] at this
            omega
          simp [anglePlanarNormal, planarNormal_apply_transverse, hjA, hjB]


-- @@ L276-283 verbatim
theorem unitPlanarTangent_apply_planeFirst (x : E) :
    unitPlanarTangent m x (planeFirst m) =
      -unitPlanarNormal m x (planeSecond m) := by
  rw [unitPlanarTangent, unitPlanarNormal,
    norm_planarTangent_eq_norm_planarNormal,
    PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    planarTangent_apply_planeFirst, planarNormal_apply_planeSecond]
  ring


-- @@ L285-291 verbatim
theorem unitPlanarTangent_apply_planeSecond (x : E) :
    unitPlanarTangent m x (planeSecond m) =
      unitPlanarNormal m x (planeFirst m) := by
  rw [unitPlanarTangent, unitPlanarNormal,
    norm_planarTangent_eq_norm_planarNormal,
    PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    planarTangent_apply_planeSecond, planarNormal_apply_planeFirst]


-- @@ L293-333 verbatim
theorem unitPlanarTangent_eq_anglePlanarTangent {x : E} {phi : ℝ}
    (hnormal : unitPlanarNormal m x = anglePlanarNormal m phi) :
    unitPlanarTangent m x = anglePlanarTangent m phi := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
      change unitPlanarTangent m x (planeSecond m) =
        anglePlanarTangent m phi (planeSecond m)
      rw [unitPlanarTangent_apply_planeSecond, hnormal]
      have hBA : planeSecond m ≠ planeFirst m := by
        intro h
        have := congrArg Fin.val h
        simp [planeFirst, planeSecond] at this
      simp [anglePlanarTangent, anglePlanarNormal, hBA]
  | cast i =>
      induction i using Fin.lastCases with
      | last =>
          change unitPlanarTangent m x (planeFirst m) =
            anglePlanarTangent m phi (planeFirst m)
          rw [unitPlanarTangent_apply_planeFirst, hnormal]
          have hAB : planeFirst m ≠ planeSecond m := by
            intro h
            have := congrArg Fin.val h
            simp [planeFirst, planeSecond] at this
          simp [anglePlanarTangent, anglePlanarNormal, hAB]
      | cast j =>
          change unitPlanarTangent m x j.castSucc.castSucc =
            anglePlanarTangent m phi j.castSucc.castSucc
          rw [unitPlanarTangent]
          have hjA : j.castSucc.castSucc ≠ planeFirst m := by
            intro h
            have := congrArg Fin.val h
            simp [planeFirst] at this
            omega
          have hjB : j.castSucc.castSucc ≠ planeSecond m := by
            intro h
            have := congrArg Fin.val h
            simp [planeSecond] at this
            omega
          simp [anglePlanarTangent, planarTangent_apply_transverse, hjA, hjB]


-- @@ L335-358 verbatim
theorem orientedUnitPlanarTangent_rotation_of_angle
    {a : ℝ} {x y : E} {phi psi : ℝ}
    (hnormalX : unitPlanarNormal m x = anglePlanarNormal m phi)
    (hnormalY : unitPlanarNormal m y = anglePlanarNormal m psi)
    (hsign : tangentOrientationSign m a y =
      tangentOrientationSign m a x) :
    orientedUnitPlanarTangent m a y =
      Real.cos (tangentOrientationSign m a x * (psi - phi)) •
          orientedUnitPlanarTangent m a x -
        Real.sin (tangentOrientationSign m a x * (psi - phi)) •
          unitPlanarNormal m x := by
  have htangentX := unitPlanarTangent_eq_anglePlanarTangent m hnormalX
  have htangentY := unitPlanarTangent_eq_anglePlanarTangent m hnormalY
  rw [orientedUnitPlanarTangent, orientedUnitPlanarTangent,
    htangentX, htangentY, hnormalX, hsign]
  rcases tangentOrientationSign_eq_one_or_neg_one m a x with hs | hs
  · rw [hs]
    norm_num
    exact anglePlanarTangent_rotation m phi psi
  · rw [hs]
    simp only [neg_mul, one_mul, Real.cos_neg, Real.sin_neg, neg_smul,
      one_smul, sub_eq_add_neg, neg_neg]
    rw [anglePlanarTangent_rotation m phi psi]
    module


-- @@ L360-378 verbatim
theorem unitPlanarNormal_rotation_of_angle
    {a : ℝ} {x y : E} {phi psi : ℝ}
    (hnormalX : unitPlanarNormal m x = anglePlanarNormal m phi)
    (hnormalY : unitPlanarNormal m y = anglePlanarNormal m psi) :
    unitPlanarNormal m y =
      Real.sin (tangentOrientationSign m a x * (psi - phi)) •
          (tangentOrientationSign m a x • unitPlanarTangent m x) +
        Real.cos (tangentOrientationSign m a x * (psi - phi)) •
          unitPlanarNormal m x := by
  have htangentX := unitPlanarTangent_eq_anglePlanarTangent m hnormalX
  rw [hnormalX, hnormalY, htangentX]
  rcases tangentOrientationSign_eq_one_or_neg_one m a x with hs | hs
  · rw [hs]
    norm_num
    exact anglePlanarNormal_rotation m phi psi
  · rw [hs]
    simp only [neg_mul, one_mul, Real.sin_neg, Real.cos_neg, neg_smul,
      one_smul, smul_neg, neg_neg]
    exact anglePlanarNormal_rotation m phi psi


-- @@ L380-392 verbatim
theorem endpointUnitFrame_middle_eq (a : ℝ) (x y : E)
    {i : Fin (m + 3)} (hi0 : i ≠ 0)
    (hilast : i ≠ Fin.last (m + 2)) :
    endpointUnitFrame m a x i = endpointUnitFrame m a y i := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
  induction k using Fin.lastCases with
  | last =>
      exfalso
      apply hilast
      apply Fin.ext
      simp
  | cast k =>
      simp [endpointUnitFrame, endpointNormalUnit]


-- @@ L394-396 verbatim
@[simp] theorem endpointUnitFrame_zero (a : ℝ) (x : E) :
    endpointUnitFrame m a x 0 = orientedUnitPlanarTangent m a x := by
  simp [endpointUnitFrame]


-- @@ L398-429 verbatim
theorem rowsMatrix_endpointUnitFrame_rotation_of_angle
    {a : ℝ} {x y : E} {phi psi : ℝ}
    (hnormalX : unitPlanarNormal m x = anglePlanarNormal m phi)
    (hnormalY : unitPlanarNormal m y = anglePlanarNormal m psi)
    (hsign : tangentOrientationSign m a y =
      tangentOrientationSign m a x) :
    rowsMatrix (endpointUnitFrame m a y) =
      twistMat m (tangentOrientationSign m a x * (psi - phi)) *
        rowsMatrix (endpointUnitFrame m a x) := by
  ext i j
  rw [StandardBirth.twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [rowsMatrix, Matrix.of_apply, endpointUnitFrame_zero]
    rw [endpointUnitFrame_last]
    have hrot := congrArg (fun v : E => v j)
      (orientedUnitPlanarTangent_rotation_of_angle m
        hnormalX hnormalY hsign)
    simpa [sub_eq_add_neg] using hrot
  · rw [if_neg hi0]
    by_cases hilast : i = Fin.last (m + 2)
    · subst i
      rw [if_pos rfl]
      simp only [rowsMatrix, Matrix.of_apply, endpointUnitFrame_last]
      have hrot := congrArg (fun v : E => v j)
        (unitPlanarNormal_rotation_of_angle m (a := a) hnormalX hnormalY)
      simpa [endpointUnitFrame_zero, orientedUnitPlanarTangent] using hrot
    · rw [if_neg hilast]
      simp only [rowsMatrix, Matrix.of_apply]
      exact congrArg (fun v : E => v j)
        (endpointUnitFrame_middle_eq m a y x hi0 hilast)


-- @@ L431-431 verbatim
/-! ## Incoming normal angle -/


-- @@ L433-436 verbatim
/-- The preferred square root lies in the open right half-plane, so its angle
has the globally continuous principal lift `arctan (v/u)`. -/
def sourcePointAngle (theta : ℝ) : ℝ :=
  Real.arctan (sourceRootSecond theta / sourceRootFirst theta)


-- @@ L438-439 verbatim
def sourceNormalAngle (theta : ℝ) : ℝ :=
  theta - sourcePointAngle theta


-- @@ L441-445 verbatim
theorem continuous_sourcePointAngle : Continuous sourcePointAngle := by
  unfold sourcePointAngle
  exact Real.continuous_arctan.comp
    (continuous_sourceRootSecond.div continuous_sourceRootFirst
      (fun theta => (sourceRootFirst_pos theta).ne'))


-- @@ L447-448 verbatim
theorem continuous_sourceNormalAngle : Continuous sourceNormalAngle := by
  exact continuous_id.sub continuous_sourcePointAngle


-- @@ L450-455 verbatim
theorem sourceRoot_normSq (theta : ℝ) :
    sourceRootFirst theta ^ 2 + sourceRootSecond theta ^ 2 =
      sourceRadicandNorm theta := by
  have hsub := sourceRoot_sq_sub_sq theta
  have hfirst := sourceRootFirst_sq theta
  nlinarith


-- @@ L457-461 verbatim
theorem sourcePointAngle_cos (theta : ℝ) :
    Real.cos (sourcePointAngle theta) =
      sourceRootFirst theta / Real.sqrt (sourceRadicandNorm theta) := by
  rw [sourcePointAngle, cos_arctan_div (sourceRootFirst_pos theta),
    sourceRoot_normSq]


-- @@ L463-467 verbatim
theorem sourcePointAngle_sin (theta : ℝ) :
    Real.sin (sourcePointAngle theta) =
      sourceRootSecond theta / Real.sqrt (sourceRadicandNorm theta) := by
  rw [sourcePointAngle, sin_arctan_div (sourceRootFirst_pos theta),
    sourceRoot_normSq]


-- @@ L469-476 verbatim
theorem sourceNormalAngle_cos (theta : ℝ) :
    Real.cos (sourceNormalAngle theta) =
      (sourceRootFirst theta * Real.cos theta +
        sourceRootSecond theta * Real.sin theta) /
          Real.sqrt (sourceRadicandNorm theta) := by
  rw [sourceNormalAngle, Real.cos_sub, sourcePointAngle_cos,
    sourcePointAngle_sin]
  ring


-- @@ L478-485 verbatim
theorem sourceNormalAngle_sin (theta : ℝ) :
    Real.sin (sourceNormalAngle theta) =
      (sourceRootFirst theta * Real.sin theta -
        sourceRootSecond theta * Real.cos theta) /
          Real.sqrt (sourceRadicandNorm theta) := by
  rw [sourceNormalAngle, Real.sin_sub, sourcePointAngle_cos,
    sourcePointAngle_sin]
  ring


-- @@ L487-499 verbatim
theorem sourceNormalAngle_two_pi :
    sourceNormalAngle (2 * Real.pi) = sourceNormalAngle 0 + 2 * Real.pi := by
  have hrootFirst : sourceRootFirst (2 * Real.pi) = sourceRootFirst 0 := by
    unfold sourceRootFirst sourceRadicandNorm sourceRadicandFirst
      sourceRadicandSecond
    simp [Real.cos_two_pi, Real.sin_two_pi]
  have hrootSecond : sourceRootSecond (2 * Real.pi) = sourceRootSecond 0 := by
    unfold sourceRootSecond sourceRadicandSecond
    rw [hrootFirst]
    simp [Real.sin_two_pi]
  unfold sourceNormalAngle sourcePointAngle
  rw [hrootFirst, hrootSecond]
  ring


-- @@ L501-522 verbatim
/-- The incoming planar normal coefficients factor through the lifted normal
angle with a positive radial scale. -/
theorem normalFirst_sourcePointRight (theta : ℝ) :
    normalFirst m (sourcePointRight m theta) =
      4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) *
        Real.cos (sourceNormalAngle theta) := by
  rw [normalFirst, sourcePointRight_apply_planeFirst]
  have hradius : radiusSq m (sourcePointRight m theta) =
      sourceRadicandNorm theta := by
    simp [radiusSq, sourceRoot_normSq]
  rw [hradius, sourceNormalAngle_cos]
  have hsqrt0 : Real.sqrt (sourceRadicandNorm theta) ≠ 0 :=
    (Real.sqrt_pos.2 (sourceRadicandNorm_pos theta)).ne'
  have hfirst := sourceRoot_sq_sub_sq theta
  have hsecond := two_mul_sourceRootFirst_mul_sourceRootSecond theta
  have hnorm := sourceRoot_normSq theta
  unfold sourceRadicandFirst at hfirst
  unfold sourceRadicandSecond at hsecond
  field_simp [hsqrt0]
  linear_combination
    sourceRootFirst theta * hfirst +
      sourceRootSecond theta * hsecond - sourceRootFirst theta * hnorm


-- @@ L524-543 verbatim
theorem normalSecond_sourcePointRight (theta : ℝ) :
    normalSecond m (sourcePointRight m theta) =
      4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) *
        Real.sin (sourceNormalAngle theta) := by
  rw [normalSecond, sourcePointRight_apply_planeSecond]
  have hradius : radiusSq m (sourcePointRight m theta) =
      sourceRadicandNorm theta := by
    simp [radiusSq, sourceRoot_normSq]
  rw [hradius, sourceNormalAngle_sin]
  have hsqrt0 : Real.sqrt (sourceRadicandNorm theta) ≠ 0 :=
    (Real.sqrt_pos.2 (sourceRadicandNorm_pos theta)).ne'
  have hfirst := sourceRoot_sq_sub_sq theta
  have hsecond := two_mul_sourceRootFirst_mul_sourceRootSecond theta
  have hnorm := sourceRoot_normSq theta
  unfold sourceRadicandFirst at hfirst
  unfold sourceRadicandSecond at hsecond
  field_simp [hsqrt0]
  linear_combination
    sourceRootFirst theta * hsecond -
      sourceRootSecond theta * hfirst - sourceRootSecond theta * hnorm


-- @@ L545-567 verbatim
theorem norm_planarNormal_sourcePointRight (theta : ℝ) :
    ‖planarNormal m (sourcePointRight m theta)‖ =
      4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) := by
  let K := 4 * sourceScale * Real.sqrt (sourceRadicandNorm theta)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) sourceScale_pos)
      (Real.sqrt_pos.2 (sourceRadicandNorm_pos theta))
  have hsq : ‖planarNormal m (sourcePointRight m theta)‖ ^ 2 = K ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      inner_planarNormal_self,
      normalFirst_sourcePointRight, normalSecond_sourcePointRight]
    calc
      (4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) *
              Real.cos (sourceNormalAngle theta)) ^ 2 +
            (4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) *
              Real.sin (sourceNormalAngle theta)) ^ 2 =
          K ^ 2 * (Real.cos (sourceNormalAngle theta) ^ 2 +
            Real.sin (sourceNormalAngle theta) ^ 2) := by
              dsimp [K]
              ring
      _ = K ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  nlinarith [norm_nonneg (planarNormal m (sourcePointRight m theta))]


-- @@ L569-578 verbatim
theorem unitPlanarNormal_sourcePointRight_planeFirst (theta : ℝ) :
    unitPlanarNormal m (sourcePointRight m theta) (planeFirst m) =
      Real.cos (sourceNormalAngle theta) := by
  rw [unitPlanarNormal, PiLp.smul_apply, smul_eq_mul,
    planarNormal_apply_planeFirst]
  rw [norm_planarNormal_sourcePointRight, normalFirst_sourcePointRight]
  have hK : 4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) sourceScale_pos.ne')
      (Real.sqrt_pos.2 (sourceRadicandNorm_pos theta)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]


-- @@ L580-589 verbatim
theorem unitPlanarNormal_sourcePointRight_planeSecond (theta : ℝ) :
    unitPlanarNormal m (sourcePointRight m theta) (planeSecond m) =
      Real.sin (sourceNormalAngle theta) := by
  rw [unitPlanarNormal, PiLp.smul_apply, smul_eq_mul,
    planarNormal_apply_planeSecond]
  rw [norm_planarNormal_sourcePointRight, normalSecond_sourcePointRight]
  have hK : 4 * sourceScale * Real.sqrt (sourceRadicandNorm theta) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) sourceScale_pos.ne')
      (Real.sqrt_pos.2 (sourceRadicandNorm_pos theta)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]


-- @@ L591-596 verbatim
theorem unitPlanarNormal_sourcePointRight_eq_angle (theta : ℝ) :
    unitPlanarNormal m (sourcePointRight m theta) =
      anglePlanarNormal m (sourceNormalAngle theta) :=
  unitPlanarNormal_eq_anglePlanarNormal m
    (unitPlanarNormal_sourcePointRight_planeFirst m theta)
    (unitPlanarNormal_sourcePointRight_planeSecond m theta)


-- @@ L598-601 verbatim
/-- The left oval has the same normal winding, shifted by the constant phase
`pi`. -/
def sourceLeftNormalAngle (theta : ℝ) : ℝ :=
  sourceNormalAngle theta + Real.pi


-- @@ L603-604 verbatim
theorem continuous_sourceLeftNormalAngle : Continuous sourceLeftNormalAngle := by
  exact continuous_sourceNormalAngle.add continuous_const


-- @@ L606-611 verbatim
theorem sourceLeftNormalAngle_two_pi :
    sourceLeftNormalAngle (2 * Real.pi) =
      sourceLeftNormalAngle 0 + 2 * Real.pi := by
  rw [sourceLeftNormalAngle, sourceLeftNormalAngle,
    sourceNormalAngle_two_pi]
  ring


-- @@ L613-624 verbatim
theorem sourceRight_tangentOrientationSign_eq_zero (theta : ℝ) :
    tangentOrientationSign m (-1 / 2)
        (sourcePointRight m theta) =
      tangentOrientationSign m (-1 / 2) (sourcePointRight m 0) := by
  apply tangentOrientationSign_eq_of_curve m (-1 / 2)
      (sourcePointRight m) (continuous_sourcePointRight m) _ _ (Or.inl rfl)
  · intro t
    exact sourcePointRight_mem_source_fiber m t
  · intro t
    simpa only [sourceFLS] using
      (sourceFLS m).fiber_subset_regularSet
        (sourcePointRight_mem_source_fiber m t)


-- @@ L626-637 verbatim
theorem sourceLeft_tangentOrientationSign_eq_zero (theta : ℝ) :
    tangentOrientationSign m (-1 / 2)
        (sourcePointLeft m theta) =
      tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0) := by
  apply tangentOrientationSign_eq_of_curve m (-1 / 2)
      (sourcePointLeft m) (continuous_sourcePointLeft m) _ _ (Or.inl rfl)
  · intro t
    exact sourcePointLeft_mem_source_fiber m t
  · intro t
    simpa only [sourceFLS] using
      (sourceFLS m).fiber_subset_regularSet
        (sourcePointLeft_mem_source_fiber m t)


-- @@ L639-650 verbatim
theorem rowsMatrix_sourcePointRight_endpointUnitFrame_rotation (theta : ℝ) :
    rowsMatrix (endpointUnitFrame m (-1 / 2)
        (sourcePointRight m theta)) =
      twistMat m
          (tangentOrientationSign m (-1 / 2) (sourcePointRight m 0) *
            (sourceNormalAngle theta - sourceNormalAngle 0)) *
        rowsMatrix (endpointUnitFrame m (-1 / 2)
          (sourcePointRight m 0)) := by
  exact rowsMatrix_endpointUnitFrame_rotation_of_angle m
    (unitPlanarNormal_sourcePointRight_eq_angle m 0)
    (unitPlanarNormal_sourcePointRight_eq_angle m theta)
    (sourceRight_tangentOrientationSign_eq_zero m theta)


-- @@ L652-653 verbatim
theorem radiusSq_neg (x : E) : radiusSq m (-x) = radiusSq m x := by
  simp [radiusSq]


-- @@ L655-662 verbatim
theorem planarNormal_neg (x : E) :
    planarNormal m (-x) = -planarNormal m x := by
  have hfirst : normalFirst m (-x) = -normalFirst m x := by
    simp [normalFirst, radiusSq_neg]
  have hsecond : normalSecond m (-x) = -normalSecond m x := by
    simp [normalSecond, radiusSq_neg]
  simp [planarNormal, hfirst, hsecond]
  exact add_comm _ _


-- @@ L664-667 verbatim
theorem unitPlanarNormal_neg (x : E) :
    unitPlanarNormal m (-x) = -unitPlanarNormal m x := by
  rw [unitPlanarNormal, unitPlanarNormal, planarNormal_neg, norm_neg]
  exact smul_neg _ _


-- @@ L669-675 verbatim
theorem unitPlanarNormal_sourcePointLeft_planeFirst (theta : ℝ) :
    unitPlanarNormal m (sourcePointLeft m theta) (planeFirst m) =
      Real.cos (sourceLeftNormalAngle theta) := by
  rw [sourcePointLeft, unitPlanarNormal_neg]
  change -unitPlanarNormal m (sourcePointRight m theta) (planeFirst m) = _
  rw [unitPlanarNormal_sourcePointRight_planeFirst,
    sourceLeftNormalAngle, Real.cos_add_pi]


-- @@ L677-683 verbatim
theorem unitPlanarNormal_sourcePointLeft_planeSecond (theta : ℝ) :
    unitPlanarNormal m (sourcePointLeft m theta) (planeSecond m) =
      Real.sin (sourceLeftNormalAngle theta) := by
  rw [sourcePointLeft, unitPlanarNormal_neg]
  change -unitPlanarNormal m (sourcePointRight m theta) (planeSecond m) = _
  rw [unitPlanarNormal_sourcePointRight_planeSecond,
    sourceLeftNormalAngle, Real.sin_add_pi]


-- @@ L685-690 verbatim
theorem unitPlanarNormal_sourcePointLeft_eq_angle (theta : ℝ) :
    unitPlanarNormal m (sourcePointLeft m theta) =
      anglePlanarNormal m (sourceLeftNormalAngle theta) :=
  unitPlanarNormal_eq_anglePlanarNormal m
    (unitPlanarNormal_sourcePointLeft_planeFirst m theta)
    (unitPlanarNormal_sourcePointLeft_planeSecond m theta)


-- @@ L692-703 verbatim
theorem rowsMatrix_sourcePointLeft_endpointUnitFrame_rotation (theta : ℝ) :
    rowsMatrix (endpointUnitFrame m (-1 / 2)
        (sourcePointLeft m theta)) =
      twistMat m
          (tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0) *
            (sourceLeftNormalAngle theta - sourceLeftNormalAngle 0)) *
        rowsMatrix (endpointUnitFrame m (-1 / 2)
          (sourcePointLeft m 0)) := by
  exact rowsMatrix_endpointUnitFrame_rotation_of_angle m
    (unitPlanarNormal_sourcePointLeft_eq_angle m 0)
    (unitPlanarNormal_sourcePointLeft_eq_angle m theta)
    (sourceLeft_tangentOrientationSign_eq_zero m theta)


-- @@ L705-705 verbatim
/-! ## Outgoing normal angle -/


-- @@ L707-710 verbatim
/-- Positive real part of the residual factor in
`z² - 1 = exp(2i theta) (targetOffsetFirst + i targetOffsetSecond)`. -/
def targetOffsetFirst (theta : ℝ) : ℝ :=
  Real.sqrt (Real.cos (2 * theta) ^ 2 + 1 / 2)


-- @@ L712-713 verbatim
def targetOffsetSecond (theta : ℝ) : ℝ :=
  Real.sin (2 * theta)


-- @@ L715-716 verbatim
def targetOffsetNorm (theta : ℝ) : ℝ :=
  Real.sqrt (targetOffsetFirst theta ^ 2 + targetOffsetSecond theta ^ 2)


-- @@ L718-721 verbatim
theorem targetOffsetFirst_pos (theta : ℝ) : 0 < targetOffsetFirst theta := by
  unfold targetOffsetFirst
  apply Real.sqrt_pos.2
  positivity


-- @@ L723-727 verbatim
theorem targetOffsetNorm_pos (theta : ℝ) : 0 < targetOffsetNorm theta := by
  unfold targetOffsetNorm
  apply Real.sqrt_pos.2
  have hfirst := targetOffsetFirst_pos theta
  nlinarith [sq_nonneg (targetOffsetSecond theta)]


-- @@ L729-730 verbatim
def targetPhaseOffset (theta : ℝ) : ℝ :=
  Real.arctan (targetOffsetSecond theta / targetOffsetFirst theta)


-- @@ L732-733 verbatim
def targetNormalAngle (theta : ℝ) : ℝ :=
  theta + targetPhaseOffset theta


-- @@ L735-737 verbatim
theorem continuous_targetOffsetFirst : Continuous targetOffsetFirst := by
  unfold targetOffsetFirst
  fun_prop


-- @@ L739-741 verbatim
theorem continuous_targetOffsetSecond : Continuous targetOffsetSecond := by
  unfold targetOffsetSecond
  fun_prop


-- @@ L743-747 verbatim
theorem continuous_targetPhaseOffset : Continuous targetPhaseOffset := by
  unfold targetPhaseOffset
  exact Real.continuous_arctan.comp
    (continuous_targetOffsetSecond.div continuous_targetOffsetFirst
      (fun theta => (targetOffsetFirst_pos theta).ne'))


-- @@ L749-750 verbatim
theorem continuous_targetNormalAngle : Continuous targetNormalAngle := by
  exact continuous_id.add continuous_targetPhaseOffset


-- @@ L752-757 verbatim
theorem targetPhaseOffset_cos (theta : ℝ) :
    Real.cos (targetPhaseOffset theta) =
      targetOffsetFirst theta / targetOffsetNorm theta := by
  rw [targetPhaseOffset,
    cos_arctan_div (targetOffsetFirst_pos theta)]
  rfl


-- @@ L759-764 verbatim
theorem targetPhaseOffset_sin (theta : ℝ) :
    Real.sin (targetPhaseOffset theta) =
      targetOffsetSecond theta / targetOffsetNorm theta := by
  rw [targetPhaseOffset,
    sin_arctan_div (targetOffsetFirst_pos theta)]
  rfl


-- @@ L766-773 verbatim
theorem targetNormalAngle_cos (theta : ℝ) :
    Real.cos (targetNormalAngle theta) =
      (targetOffsetFirst theta * Real.cos theta -
        targetOffsetSecond theta * Real.sin theta) /
          targetOffsetNorm theta := by
  rw [targetNormalAngle, Real.cos_add, targetPhaseOffset_cos,
    targetPhaseOffset_sin]
  ring


-- @@ L775-782 verbatim
theorem targetNormalAngle_sin (theta : ℝ) :
    Real.sin (targetNormalAngle theta) =
      (targetOffsetFirst theta * Real.sin theta +
        targetOffsetSecond theta * Real.cos theta) /
          targetOffsetNorm theta := by
  rw [targetNormalAngle, Real.sin_add, targetPhaseOffset_cos,
    targetPhaseOffset_sin]
  ring


-- @@ L784-792 verbatim
theorem targetOffsetFirst_two_pi :
    targetOffsetFirst (2 * Real.pi) = targetOffsetFirst 0 := by
  unfold targetOffsetFirst
  have hcos : Real.cos (2 * (2 * Real.pi)) = Real.cos (2 * 0) := by
    have harg : 2 * (2 * Real.pi) = (2 : ℕ) * (2 * Real.pi) := by
      norm_num
    rw [harg, Real.cos_nat_mul_two_pi]
    norm_num
  rw [hcos]


-- @@ L794-803 verbatim
theorem targetOffsetSecond_two_pi :
    targetOffsetSecond (2 * Real.pi) = targetOffsetSecond 0 := by
  unfold targetOffsetSecond
  have hsin : Real.sin (2 * (2 * Real.pi)) = Real.sin (2 * 0) := by
    have harg : 2 * (2 * Real.pi) = (4 : ℤ) * Real.pi := by
      push_cast
      ring
    rw [harg, Real.sin_int_mul_pi]
    norm_num
  exact hsin


-- @@ L805-809 verbatim
theorem targetNormalAngle_two_pi :
    targetNormalAngle (2 * Real.pi) = targetNormalAngle 0 + 2 * Real.pi := by
  unfold targetNormalAngle targetPhaseOffset
  rw [targetOffsetFirst_two_pi, targetOffsetSecond_two_pi]
  ring


-- @@ L811-821 verbatim
theorem target_tangentOrientationSign_eq_zero (theta : ℝ) :
    tangentOrientationSign m (1 / 2) (targetPoint m theta) =
      tangentOrientationSign m (1 / 2) (targetPoint m 0) := by
  apply tangentOrientationSign_eq_of_curve m (1 / 2)
      (targetPoint m) (continuous_targetPoint m) _ _ (Or.inr rfl)
  · intro t
    exact targetPoint_mem_target_fiber m t
  · intro t
    simpa only [targetFLS] using
      (targetFLS m).fiber_subset_regularSet
        (targetPoint_mem_target_fiber m t)


-- @@ L823-835 verbatim
theorem normalFirst_targetPoint (theta : ℝ) :
    normalFirst m (targetPoint m theta) =
      4 * targetRadius theta * targetOffsetNorm theta *
        Real.cos (targetNormalAngle theta) := by
  rw [normalFirst, targetPoint_apply_planeFirst,
    radiusSq_targetPoint, targetNormalAngle_cos]
  have hnorm0 : targetOffsetNorm theta ≠ 0 :=
    (targetOffsetNorm_pos theta).ne'
  field_simp [hnorm0]
  unfold targetRadiusSq targetOffsetFirst targetOffsetSecond
  rw [Real.cos_two_mul', Real.sin_two_mul]
  linear_combination
    targetRadius theta * Real.cos theta * Real.cos_sq_add_sin_sq theta


-- @@ L837-849 verbatim
theorem normalSecond_targetPoint (theta : ℝ) :
    normalSecond m (targetPoint m theta) =
      4 * targetRadius theta * targetOffsetNorm theta *
        Real.sin (targetNormalAngle theta) := by
  rw [normalSecond, targetPoint_apply_planeSecond,
    radiusSq_targetPoint, targetNormalAngle_sin]
  have hnorm0 : targetOffsetNorm theta ≠ 0 :=
    (targetOffsetNorm_pos theta).ne'
  field_simp [hnorm0]
  unfold targetRadiusSq targetOffsetFirst targetOffsetSecond
  rw [Real.cos_two_mul', Real.sin_two_mul]
  linear_combination
    -(targetRadius theta * Real.sin theta) * Real.cos_sq_add_sin_sq theta


-- @@ L851-873 verbatim
theorem norm_planarNormal_targetPoint (theta : ℝ) :
    ‖planarNormal m (targetPoint m theta)‖ =
      4 * targetRadius theta * targetOffsetNorm theta := by
  let K := 4 * targetRadius theta * targetOffsetNorm theta
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) (targetRadius_pos theta))
      (targetOffsetNorm_pos theta)
  have hsq : ‖planarNormal m (targetPoint m theta)‖ ^ 2 = K ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      inner_planarNormal_self,
      normalFirst_targetPoint, normalSecond_targetPoint]
    calc
      (4 * targetRadius theta * targetOffsetNorm theta *
              Real.cos (targetNormalAngle theta)) ^ 2 +
            (4 * targetRadius theta * targetOffsetNorm theta *
              Real.sin (targetNormalAngle theta)) ^ 2 =
          K ^ 2 * (Real.cos (targetNormalAngle theta) ^ 2 +
            Real.sin (targetNormalAngle theta) ^ 2) := by
              dsimp [K]
              ring
      _ = K ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  nlinarith [norm_nonneg (planarNormal m (targetPoint m theta))]


-- @@ L875-884 verbatim
theorem unitPlanarNormal_targetPoint_planeFirst (theta : ℝ) :
    unitPlanarNormal m (targetPoint m theta) (planeFirst m) =
      Real.cos (targetNormalAngle theta) := by
  rw [unitPlanarNormal, PiLp.smul_apply, smul_eq_mul,
    planarNormal_apply_planeFirst]
  rw [norm_planarNormal_targetPoint, normalFirst_targetPoint]
  have hK : 4 * targetRadius theta * targetOffsetNorm theta ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (targetRadius_pos theta).ne')
      (targetOffsetNorm_pos theta).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]


-- @@ L886-895 verbatim
theorem unitPlanarNormal_targetPoint_planeSecond (theta : ℝ) :
    unitPlanarNormal m (targetPoint m theta) (planeSecond m) =
      Real.sin (targetNormalAngle theta) := by
  rw [unitPlanarNormal, PiLp.smul_apply, smul_eq_mul,
    planarNormal_apply_planeSecond]
  rw [norm_planarNormal_targetPoint, normalSecond_targetPoint]
  have hK : 4 * targetRadius theta * targetOffsetNorm theta ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (targetRadius_pos theta).ne')
      (targetOffsetNorm_pos theta).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]


-- @@ L897-902 verbatim
theorem unitPlanarNormal_targetPoint_eq_angle (theta : ℝ) :
    unitPlanarNormal m (targetPoint m theta) =
      anglePlanarNormal m (targetNormalAngle theta) :=
  unitPlanarNormal_eq_anglePlanarNormal m
    (unitPlanarNormal_targetPoint_planeFirst m theta)
    (unitPlanarNormal_targetPoint_planeSecond m theta)


-- @@ L904-913 verbatim
theorem rowsMatrix_targetPoint_endpointUnitFrame_rotation (theta : ℝ) :
    rowsMatrix (endpointUnitFrame m (1 / 2) (targetPoint m theta)) =
      twistMat m
          (tangentOrientationSign m (1 / 2) (targetPoint m 0) *
            (targetNormalAngle theta - targetNormalAngle 0)) *
        rowsMatrix (endpointUnitFrame m (1 / 2) (targetPoint m 0)) := by
  exact rowsMatrix_endpointUnitFrame_rotation_of_angle m
    (unitPlanarNormal_targetPoint_eq_angle m 0)
    (unitPlanarNormal_targetPoint_eq_angle m theta)
    (target_tangentOrientationSign_eq_zero m theta)


-- @@ L915-915 verbatim
/-! ## The three signed one-turn row-plane loops -/


-- @@ L917-918 verbatim
def endpointFrameWinding (sigma : ℝ) : ℤ :=
  if sigma = 1 then 1 else -1


-- @@ L920-926 verbatim
theorem endpointFrameWinding_cast {sigma : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    ((endpointFrameWinding sigma : ℤ) : ℝ) = sigma := by
  rcases hsigma with rfl | rfl
  · simp [endpointFrameWinding]
  · rw [endpointFrameWinding, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    norm_num


-- @@ L928-935 verbatim
theorem endpointFrameWinding_mod_two {sigma : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    (endpointFrameWinding sigma : ZMod 2) = 1 := by
  rcases hsigma with rfl | rfl
  · simp [endpointFrameWinding]
  · rw [endpointFrameWinding, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    change (-1 : ZMod 2) = 1
    decide


-- @@ L937-945 verbatim
def sourceRightFrameAngle : C(I, ℝ) where
  toFun u :=
    tangentOrientationSign m (-1 / 2) (sourcePointRight m 0) *
      (sourceNormalAngle (2 * Real.pi * (u : ℝ)) -
        sourceNormalAngle 0)
  continuous_toFun := by
    exact continuous_const.mul
      ((continuous_sourceNormalAngle.comp
        (continuous_const.mul continuous_subtype_val)).sub continuous_const)


-- @@ L947-955 verbatim
def sourceLeftFrameAngle : C(I, ℝ) where
  toFun u :=
    tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0) *
      (sourceLeftNormalAngle (2 * Real.pi * (u : ℝ)) -
        sourceLeftNormalAngle 0)
  continuous_toFun := by
    exact continuous_const.mul
      ((continuous_sourceLeftNormalAngle.comp
        (continuous_const.mul continuous_subtype_val)).sub continuous_const)


-- @@ L957-965 verbatim
def targetFrameAngle : C(I, ℝ) where
  toFun u :=
    tangentOrientationSign m (1 / 2) (targetPoint m 0) *
      (targetNormalAngle (2 * Real.pi * (u : ℝ)) -
        targetNormalAngle 0)
  continuous_toFun := by
    exact continuous_const.mul
      ((continuous_targetNormalAngle.comp
        (continuous_const.mul continuous_subtype_val)).sub continuous_const)


-- @@ L967-983 verbatim
theorem sourceRightFrameAngle_closed :
    sourceRightFrameAngle m 1 = sourceRightFrameAngle m 0 +
      2 * Real.pi * endpointFrameWinding
        (tangentOrientationSign m (-1 / 2) (sourcePointRight m 0)) := by
  let sigma := tangentOrientationSign m (-1 / 2) (sourcePointRight m 0)
  have hsigma := tangentOrientationSign_eq_one_or_neg_one m (-1 / 2)
    (sourcePointRight m 0)
  have hcast := endpointFrameWinding_cast hsigma
  change sigma * (sourceNormalAngle (2 * Real.pi * (1 : ℝ)) -
      sourceNormalAngle 0) =
    sigma * (sourceNormalAngle (2 * Real.pi * (0 : ℝ)) -
      sourceNormalAngle 0) +
      2 * Real.pi * ((endpointFrameWinding sigma : ℤ) : ℝ)
  norm_num
  rw [sourceNormalAngle_two_pi]
  rw [hcast]
  ring


-- @@ L985-1001 verbatim
theorem sourceLeftFrameAngle_closed :
    sourceLeftFrameAngle m 1 = sourceLeftFrameAngle m 0 +
      2 * Real.pi * endpointFrameWinding
        (tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0)) := by
  let sigma := tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0)
  have hsigma := tangentOrientationSign_eq_one_or_neg_one m (-1 / 2)
    (sourcePointLeft m 0)
  have hcast := endpointFrameWinding_cast hsigma
  change sigma * (sourceLeftNormalAngle (2 * Real.pi * (1 : ℝ)) -
      sourceLeftNormalAngle 0) =
    sigma * (sourceLeftNormalAngle (2 * Real.pi * (0 : ℝ)) -
      sourceLeftNormalAngle 0) +
      2 * Real.pi * ((endpointFrameWinding sigma : ℤ) : ℝ)
  norm_num
  rw [sourceLeftNormalAngle_two_pi]
  rw [hcast]
  ring


-- @@ L1003-1019 verbatim
theorem targetFrameAngle_closed :
    targetFrameAngle m 1 = targetFrameAngle m 0 +
      2 * Real.pi * endpointFrameWinding
        (tangentOrientationSign m (1 / 2) (targetPoint m 0)) := by
  let sigma := tangentOrientationSign m (1 / 2) (targetPoint m 0)
  have hsigma := tangentOrientationSign_eq_one_or_neg_one m (1 / 2)
    (targetPoint m 0)
  have hcast := endpointFrameWinding_cast hsigma
  change sigma * (targetNormalAngle (2 * Real.pi * (1 : ℝ)) -
      targetNormalAngle 0) =
    sigma * (targetNormalAngle (2 * Real.pi * (0 : ℝ)) -
      targetNormalAngle 0) +
      2 * Real.pi * ((endpointFrameWinding sigma : ℤ) : ℝ)
  norm_num
  rw [targetNormalAngle_two_pi]
  rw [hcast]
  ring


-- @@ L1021-1025 verbatim
def sourceRightSO2AngleLoop : SO2AngleLoop where
  angle := sourceRightFrameAngle m
  winding := endpointFrameWinding
    (tangentOrientationSign m (-1 / 2) (sourcePointRight m 0))
  angle_closed := sourceRightFrameAngle_closed m


-- @@ L1027-1031 verbatim
def sourceLeftSO2AngleLoop : SO2AngleLoop where
  angle := sourceLeftFrameAngle m
  winding := endpointFrameWinding
    (tangentOrientationSign m (-1 / 2) (sourcePointLeft m 0))
  angle_closed := sourceLeftFrameAngle_closed m


-- @@ L1033-1037 verbatim
def targetSO2AngleLoop : SO2AngleLoop where
  angle := targetFrameAngle m
  winding := endpointFrameWinding
    (tangentOrientationSign m (1 / 2) (targetPoint m 0))
  angle_closed := targetFrameAngle_closed m


-- @@ L1039-1043 verbatim
theorem sourceRightSO2AngleLoop_winding_mod_two :
    ((sourceRightSO2AngleLoop m).winding : ZMod 2) = 1 :=
  endpointFrameWinding_mod_two
    (tangentOrientationSign_eq_one_or_neg_one m (-1 / 2)
      (sourcePointRight m 0))


-- @@ L1045-1049 verbatim
theorem sourceLeftSO2AngleLoop_winding_mod_two :
    ((sourceLeftSO2AngleLoop m).winding : ZMod 2) = 1 :=
  endpointFrameWinding_mod_two
    (tangentOrientationSign_eq_one_or_neg_one m (-1 / 2)
      (sourcePointLeft m 0))


-- @@ L1051-1055 verbatim
theorem targetSO2AngleLoop_winding_mod_two :
    ((targetSO2AngleLoop m).winding : ZMod 2) = 1 :=
  endpointFrameWinding_mod_two
    (tangentOrientationSign_eq_one_or_neg_one m (1 / 2)
      (targetPoint m 0))


-- @@ L1057-1059 verbatim
def endpointPlaneLoop (L : SO2AngleLoop) : C(I, SOGroup (m + 3)) :=
  (ContinuousMap.const I (swapRotSO m) * L.frame (m + 3)) *
    ContinuousMap.const I (swapRotSO m)⁻¹


-- @@ L1061-1065 verbatim
theorem endpointPlaneLoop_closed (L : SO2AngleLoop) :
    endpointPlaneLoop m L 0 = endpointPlaneLoop m L 1 := by
  simp only [endpointPlaneLoop, ContinuousMap.mul_apply,
    ContinuousMap.const_apply]
  rw [L.frame_closed]


-- @@ L1067-1073 verbatim
theorem endpointPlaneLoop_coe (L : SO2AngleLoop) (u : I) :
    (endpointPlaneLoop m L u : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      twistMat m (L.angle u) := by
  change swapRotMat m * rotBlock (m + 3) (L.angle u) *
      (swapRotMat m)ᵀ = _
  rw [rotBlock_eq_rotAmbient]
  rfl


-- @@ L1075-1086 verbatim
theorem loopClassZ2_endpointPlaneLoop (L : SO2AngleLoop) :
    loopClassZ2 (endpointPlaneLoop m L) (endpointPlaneLoop_closed m L) =
      (L.winding : ZMod 2) := by
  have hdim : 3 ≤ m + 3 := by omega
  have hbase := L.loopClassZ2_frame hdim
  have hconj := loopClassZ2_const_conj (swapRotSO m)
    (L.frame (m + 3)) (L.frame_closed (m + 3))
  calc
    loopClassZ2 (endpointPlaneLoop m L) (endpointPlaneLoop_closed m L) =
        loopClassZ2 (L.frame (m + 3)) (L.frame_closed (m + 3)) := by
          simpa only [endpointPlaneLoop] using hconj
    _ = (L.winding : ZMod 2) := hbase


-- @@ L1088-1088 verbatim
/-! ## Identification with the intrinsic Cassini frame loops -/


-- @@ L1090-1109 verbatim
theorem sourceRight_paramFrameLoop_eq_plane_mul_const
    (V : TamedField (sourceFLS m)) :
    (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop =
      endpointPlaneLoop m (sourceRightSO2AngleLoop m) *
        ContinuousMap.const I
          ((sourceRightSimpleClosedOrbitParam m V).paramFrameLoop 0) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [sourceRight_paramFrameLoop_apply]
  change rowsMatrix (endpointUnitFrame m (-1 / 2)
      (sourcePointRight m (2 * Real.pi * (u : ℝ)))) =
    (endpointPlaneLoop m (sourceRightSO2AngleLoop m) u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
      ((sourceRightSimpleClosedOrbitParam m V).paramFrameLoop 0 :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [endpointPlaneLoop_coe, sourceRight_paramFrameLoop_apply]
  simp only [Set.Icc.coe_zero, mul_zero]
  rw [rowsMatrix_sourcePointRight_endpointUnitFrame_rotation]
  rfl


-- @@ L1111-1133 verbatim
theorem sourceRight_paramFrameClass_eq_one
    (V : TamedField (sourceFLS m)) :
    loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed = 1 := by
  let P := sourceRightSimpleClosedOrbitParam m V
  let L := sourceRightSO2AngleLoop m
  let R := endpointPlaneLoop m L * ContinuousMap.const I (P.paramFrameLoop 0)
  have hRclosed : R 0 = R 1 := by
    change endpointPlaneLoop m L 0 * P.paramFrameLoop 0 =
      endpointPlaneLoop m L 1 * P.paramFrameLoop 0
    rw [endpointPlaneLoop_closed]
  have heq : P.paramFrameLoop = R :=
    sourceRight_paramFrameLoop_eq_plane_mul_const m V
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) := by
      exact loopClassZ2_mul_const_right (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) (P.paramFrameLoop 0)
    _ = (L.winding : ZMod 2) := loopClassZ2_endpointPlaneLoop m L
    _ = 1 := sourceRightSO2AngleLoop_winding_mod_two m


-- @@ L1135-1154 verbatim
theorem sourceLeft_paramFrameLoop_eq_plane_mul_const
    (V : TamedField (sourceFLS m)) :
    (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop =
      endpointPlaneLoop m (sourceLeftSO2AngleLoop m) *
        ContinuousMap.const I
          ((sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop 0) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [sourceLeft_paramFrameLoop_apply]
  change rowsMatrix (endpointUnitFrame m (-1 / 2)
      (sourcePointLeft m (2 * Real.pi * (u : ℝ)))) =
    (endpointPlaneLoop m (sourceLeftSO2AngleLoop m) u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
      ((sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop 0 :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [endpointPlaneLoop_coe, sourceLeft_paramFrameLoop_apply]
  simp only [Set.Icc.coe_zero, mul_zero]
  rw [rowsMatrix_sourcePointLeft_endpointUnitFrame_rotation]
  rfl


-- @@ L1156-1178 verbatim
theorem sourceLeft_paramFrameClass_eq_one
    (V : TamedField (sourceFLS m)) :
    loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed = 1 := by
  let P := sourceLeftSimpleClosedOrbitParam m V
  let L := sourceLeftSO2AngleLoop m
  let R := endpointPlaneLoop m L * ContinuousMap.const I (P.paramFrameLoop 0)
  have hRclosed : R 0 = R 1 := by
    change endpointPlaneLoop m L 0 * P.paramFrameLoop 0 =
      endpointPlaneLoop m L 1 * P.paramFrameLoop 0
    rw [endpointPlaneLoop_closed]
  have heq : P.paramFrameLoop = R :=
    sourceLeft_paramFrameLoop_eq_plane_mul_const m V
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) := by
      exact loopClassZ2_mul_const_right (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) (P.paramFrameLoop 0)
    _ = (L.winding : ZMod 2) := loopClassZ2_endpointPlaneLoop m L
    _ = 1 := sourceLeftSO2AngleLoop_winding_mod_two m


-- @@ L1180-1199 verbatim
theorem target_paramFrameLoop_eq_plane_mul_const
    (V : TamedField (targetFLS m)) :
    (targetSimpleClosedOrbitParam m V).paramFrameLoop =
      endpointPlaneLoop m (targetSO2AngleLoop m) *
        ContinuousMap.const I
          ((targetSimpleClosedOrbitParam m V).paramFrameLoop 0) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [target_paramFrameLoop_apply]
  change rowsMatrix (endpointUnitFrame m (1 / 2)
      (targetPoint m (2 * Real.pi * (u : ℝ)))) =
    (endpointPlaneLoop m (targetSO2AngleLoop m) u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
      ((targetSimpleClosedOrbitParam m V).paramFrameLoop 0 :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [endpointPlaneLoop_coe, target_paramFrameLoop_apply]
  simp only [Set.Icc.coe_zero, mul_zero]
  rw [rowsMatrix_targetPoint_endpointUnitFrame_rotation]
  rfl


-- @@ L1201-1223 verbatim
theorem target_paramFrameClass_eq_one
    (V : TamedField (targetFLS m)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m V).paramFrameLoop
        (targetSimpleClosedOrbitParam m V).paramFrameLoop_closed = 1 := by
  let P := targetSimpleClosedOrbitParam m V
  let L := targetSO2AngleLoop m
  let R := endpointPlaneLoop m L * ContinuousMap.const I (P.paramFrameLoop 0)
  have hRclosed : R 0 = R 1 := by
    change endpointPlaneLoop m L 0 * P.paramFrameLoop 0 =
      endpointPlaneLoop m L 1 * P.paramFrameLoop 0
    rw [endpointPlaneLoop_closed]
  have heq : P.paramFrameLoop = R :=
    target_paramFrameLoop_eq_plane_mul_const m V
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) := by
      exact loopClassZ2_mul_const_right (endpointPlaneLoop m L)
        (endpointPlaneLoop_closed m L) (P.paramFrameLoop 0)
    _ = (L.winding : ZMod 2) := loopClassZ2_endpointPlaneLoop m L
    _ = 1 := targetSO2AngleLoop_winding_mod_two m


-- @@ L1225-1238 verbatim
/-- The literal Cassini saddle satisfies the required mod-two splice identity.
Each of its three endpoint frame loops makes one signed turn. -/
theorem cassini_saddle_frame_class_splice
    (Vsource : TamedField (sourceFLS m))
    (Vtarget : TamedField (targetFLS m)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m Vtarget).paramFrameLoop
        (targetSimpleClosedOrbitParam m Vtarget).paramFrameLoop_closed =
      loopClassZ2 (sourceRightSimpleClosedOrbitParam m Vsource).paramFrameLoop
          (sourceRightSimpleClosedOrbitParam m Vsource).paramFrameLoop_closed +
        loopClassZ2 (sourceLeftSimpleClosedOrbitParam m Vsource).paramFrameLoop
          (sourceLeftSimpleClosedOrbitParam m Vsource).paramFrameLoop_closed + 1 := by
  rw [target_paramFrameClass_eq_one, sourceRight_paramFrameClass_eq_one,
    sourceLeft_paramFrameClass_eq_one]
  decide


-- @@ L1240-1245 verbatim
theorem sourceSign_positiveDelta_eq_zero
    (V : TamedField (sourceFLS m)) :
    (sourceSign m).positiveDelta = 0 := by
  rw [sourceSign_positiveDelta_eq_paramFrameClass_sum m V,
    sourceRight_paramFrameClass_eq_one, sourceLeft_paramFrameClass_eq_one]
  decide


-- @@ L1247-1252 verbatim
theorem targetSign_positiveDelta_eq_zero
    (V : TamedField (targetFLS m)) :
    (targetSign m).positiveDelta = 0 := by
  rw [targetSign_positiveDelta_eq_paramFrameClass_add_one m V,
    target_paramFrameClass_eq_one]
  decide


-- @@ L1254-1259 verbatim
theorem standardSaddle_positiveDelta_eq
    (Vsource : TamedField (sourceFLS m))
    (Vtarget : TamedField (targetFLS m)) :
    (sourceSign m).positiveDelta = (targetSign m).positiveDelta := by
  rw [sourceSign_positiveDelta_eq_zero m Vsource,
    targetSign_positiveDelta_eq_zero m Vtarget]


-- @@ L1261-1261 verbatim
end StandardSaddle

-- @@ L1262-1262 verbatim
end Submission
