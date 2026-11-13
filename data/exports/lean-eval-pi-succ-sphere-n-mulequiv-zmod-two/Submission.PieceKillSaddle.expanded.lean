import Mathlib
import Submission.PieceKillCore


-- @@ L4-19 verbatim
/-!
# The pants-target-to-birth-circle comparison

The `saddleTargetKill` interface of `StandardCircleMoveKit.PieceKillInput` asks
for a spatially flat signed cobordism from the outgoing presentation of the
compact Hopf pair of pants (harmonized onto the common compact background) to
the compact birth circle.

`CompactHopfPairPantsFrameLedger.homotopy` is already an exact fixed-fiber
homotopy of defining maps from the *reflected* compact tube to that pants
target.  Reversing it (`revHomotopy`) and postcomposing with the background
harmonization gives a flat connector from the harmonized pants target to the
harmonized reflected tube; the reflected tube is in turn literally of the
tube form `PieceKill.level P 0` for the parameter pack `reflParams`, whose
transverse row signs record the single reflected output row.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 2400000


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace Submission

-- @@ L27-27 verbatim
namespace PieceKill


-- @@ L29-29 verbatim
open Set Function Metric

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L32-32 verbatim
/-! ## Reversing a homotopy of defining maps -/


-- @@ L34-38 verbatim
theorem homotopy_fiber_eq_source {n : ℕ} {X₀ X₁ : FramedLevelSet n}
    (D : DefiningMapHomotopy X₀ X₁) : X₁.fiber = X₀.fiber := by
  have h := D.fiber_eq 1 zero_le_one le_rfl
  rw [D.H_one] at h
  exact h


-- @@ L40-69 verbatim
/-- A homotopy of defining maps run backwards. -/
def revHomotopy {n : ℕ} {X₀ X₁ : FramedLevelSet n}
    (D : DefiningMapHomotopy X₀ X₁) : DefiningMapHomotopy X₁ X₀ where
  H := fun s => D.H (1 - s)
  smooth := by
    have h : ContDiff ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
          (((1 : ℝ) - p.1, p.2) :
            ℝ × EuclideanSpace ℝ (Fin (n + 1)))) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    exact D.smooth.comp h
  H_zero := by
    show D.H (1 - 0) = X₁.g
    rw [sub_zero]
    exact D.H_one
  H_one := by
    show D.H (1 - 1) = X₀.g
    rw [sub_self]
    exact D.H_zero
  fiber_eq := by
    intro s hs0 hs1
    show {x | D.H (1 - s) x = 0} = X₁.fiber
    rw [D.fiber_eq (1 - s) (by linarith) (by linarith)]
    exact (homotopy_fiber_eq_source D).symm
  regular := by
    intro s hs0 hs1 x hx
    show Function.Surjective (fderiv ℝ (D.H (1 - s)) x)
    apply D.regular (1 - s) (by linarith) (by linarith)
    rw [← homotopy_fiber_eq_source D]
    exact hx


-- @@ L71-71 verbatim
variable (m : ℕ)


-- @@ L73-73 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L74-74 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L76-76 verbatim
/-! ## The Hopf-pair background harmonization -/


-- @@ L78-84 verbatim
/-- The codomain automorphism harmonizing the Hopf-pair background onto the
common compact background. -/
def hopfEquiv (hm : 0 < m) : F ≃L[ℝ] F :=
  backgroundEquiv (CompactHopfPairConfiguration.background m hm)
    (ConcreteConfigurationMorseReduction.compactBackground m)
    (CompactHopfPairConfiguration.background_ne_zero m hm)
    (CompactBirth.background_ne_zero (m + 1))


-- @@ L86-89 verbatim
theorem hopfEquiv_background (hm : 0 < m) :
    hopfEquiv m hm (CompactHopfPairConfiguration.background m hm) =
      ConcreteConfigurationMorseReduction.compactBackground m :=
  backgroundEquiv_apply _ _ _ _


-- @@ L91-95 verbatim
theorem hopfBackground_apply (hm : 0 < m) (i : Fin (m + 2)) :
    CompactHopfPairConfiguration.background m hm i =
      if i = 0 then 1 else 0 := by
  rw [CompactHopfPairPantsFrameLedger.hopf_background_eq_tube_background m hm]
  exact tube_background_apply m i


-- @@ L97-102 verbatim
theorem hopfSwap_apply (hm : 0 < m) (g : F) (i : Fin (m + 2)) :
    hopfEquiv m hm g i =
      if i = 0 then g (Fin.last (m + 1))
      else if i = Fin.last (m + 1) then g 0 else g i :=
  backgroundEquiv_swap_apply (k := m) _ _ (hopfBackground_apply m hm)
    (compactBackground_apply m) _ _ g i


-- @@ L104-104 verbatim
/-! ## The reflected output row -/


-- @@ L106-107 verbatim
theorem reflectionIndex_val (hm : 0 < m) :
    (CompactHopfPairPantsFrameLedger.reflectionIndex m hm : ℕ) = 2 := rfl


-- @@ L109-110 verbatim
theorem val_castSucc (i : Fin (m + 1)) :
    ((i.castSucc : Fin (m + 2)) : ℕ) = (i : ℕ) := rfl


-- @@ L112-114 verbatim
/-- The codomain sign pattern of the reflected tube. -/
def reflSign (hm : 0 < m) (j : Fin (m + 2)) : ℝ :=
  if j = CompactHopfPairPantsFrameLedger.reflectionIndex m hm then -1 else 1


-- @@ L116-126 verbatim
theorem coordinateReflection_apply_mul (hm : 0 < m) (w : F)
    (j : Fin (m + 2)) :
    coordinateReflection
        (CompactHopfPairPantsFrameLedger.reflectionIndex m hm) w j =
      reflSign m hm j * w j := by
  rw [coordinateReflection_apply, reflSign]
  by_cases h : j = CompactHopfPairPantsFrameLedger.reflectionIndex m hm
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring


-- @@ L128-135 verbatim
theorem reflSign_zero (hm : 0 < m) : reflSign m hm 0 = 1 := by
  have h : (0 : Fin (m + 2)) ≠
      CompactHopfPairPantsFrameLedger.reflectionIndex m hm := by
    intro hc
    have hv := congrArg Fin.val hc
    rw [Fin.val_zero, reflectionIndex_val m hm] at hv
    omega
  rw [reflSign, if_neg h]


-- @@ L137-137 verbatim
/-! ## The parameter pack of the reflected tube -/


-- @@ L139-141 verbatim
/-- Row signs of the harmonized reflected tube. -/
def etaR : Fin (m + 1) → ℝ :=
  fun i => if (if (i : ℕ) = 0 then m + 1 else (i : ℕ)) = 2 then -1 else 1


-- @@ L143-147 verbatim
theorem etaR_eq_one_or (i : Fin (m + 1)) : etaR m i = 1 ∨ etaR m i = -1 := by
  simp only [etaR]
  by_cases h : (if (i : ℕ) = 0 then m + 1 else (i : ℕ)) = 2
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)


-- @@ L149-183 verbatim
theorem etaR_prod (hm : 0 < m) : ∏ j, etaR m j = -1 := by
  obtain ⟨j₀, hj₀val, hj₀other⟩ : ∃ j : Fin (m + 1),
      (if ((j : ℕ) = 0) then m + 1 else (j : ℕ)) = 2 ∧
        ∀ b : Fin (m + 1), b ≠ j →
          ¬ ((if ((b : ℕ) = 0) then m + 1 else (b : ℕ)) = 2) := by
    by_cases hm1 : m = 1
    · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
      · show (if ((0 : ℕ) = 0) then m + 1 else (0 : ℕ)) = 2
        rw [if_pos rfl, hm1]
      · intro b hb
        have hbv : (b : ℕ) ≠ 0 := by
          intro h
          exact hb (Fin.ext (by rw [h]))
        rw [if_neg hbv]
        have hlt := b.isLt
        omega
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · show (if ((2 : ℕ) = 0) then m + 1 else (2 : ℕ)) = 2
        rw [if_neg (by omega : ¬ ((2 : ℕ) = 0))]
      · intro b hb
        by_cases hb0 : (b : ℕ) = 0
        · rw [if_pos hb0]
          omega
        · rw [if_neg hb0]
          intro hcon
          exact hb (Fin.ext hcon)
  have hsingle : ∏ j, etaR m j = etaR m j₀ :=
    Finset.prod_eq_single j₀
      (fun b _ hb => by
        simp only [etaR]
        exact if_neg (hj₀other b hb))
      (fun h => absurd (Finset.mem_univ j₀) h)
  rw [hsingle]
  simp only [etaR]
  exact if_pos hj₀val


-- @@ L185-196 verbatim
/-- The parameter pack realizing the harmonized reflected tube. -/
def reflParams (hm : 0 < m) : Params m where
  eta := etaR m
  eps := (-1) ^ (m + 1)
  heta := fun j => etaR_eq_one_or m j
  heps := by
    rcases Nat.even_or_odd (m + 1) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  hprod := by
    rw [etaR_prod m hm, pow_succ]
    ring


-- @@ L198-199 verbatim
@[simp] theorem reflParams_eta (hm : 0 < m) (i : Fin (m + 1)) :
    (reflParams m hm).eta i = etaR m i := rfl


-- @@ L201-204 verbatim
theorem etaR_apply (i : Fin (m + 1)) :
    etaR m i =
      if (if (i : ℕ) = 0 then m + 1 else (i : ℕ)) = 2 then (-1 : ℝ) else 1 :=
  rfl


-- @@ L206-207 verbatim
theorem etaR_zero_apply : etaR m 0 = if m + 1 = 2 then (-1 : ℝ) else 1 := by
  simp [etaR_apply]


-- @@ L209-214 verbatim
theorem etaR_castSucc_apply (i : Fin (m + 1)) (hi : i ≠ 0) :
    etaR m i = if (i : ℕ) = 2 then (-1 : ℝ) else 1 := by
  have hiv : (i : ℕ) ≠ 0 := by
    intro h
    exact hi (Fin.ext (by rw [h, Fin.val_zero]))
  rw [etaR_apply, if_neg hiv]


-- @@ L216-232 verbatim
theorem etaR_eq_reflSign_last (hm : 0 < m) :
    etaR m 0 = reflSign m hm (Fin.last (m + 1)) := by
  have hcond : (Fin.last (m + 1) : Fin (m + 2)) =
      CompactHopfPairPantsFrameLedger.reflectionIndex m hm ↔ m + 1 = 2 := by
    constructor
    · intro hc
      have hv := congrArg Fin.val hc
      rw [Fin.val_last, reflectionIndex_val m hm] at hv
      exact hv
    · intro hc
      apply Fin.ext
      rw [Fin.val_last, reflectionIndex_val m hm]
      exact hc
  rw [etaR_zero_apply, reflSign]
  by_cases h : m + 1 = 2
  · rw [if_pos h, if_pos (hcond.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hcond.mp hc))]


-- @@ L234-250 verbatim
theorem etaR_eq_reflSign_castSucc (hm : 0 < m) (i : Fin (m + 1)) (hi : i ≠ 0) :
    etaR m i = reflSign m hm i.castSucc := by
  have hcond : (i.castSucc : Fin (m + 2)) =
      CompactHopfPairPantsFrameLedger.reflectionIndex m hm ↔ (i : ℕ) = 2 := by
    constructor
    · intro hc
      have hv := congrArg Fin.val hc
      rw [val_castSucc m i, reflectionIndex_val m hm] at hv
      exact hv
    · intro hc
      apply Fin.ext
      rw [val_castSucc m i, reflectionIndex_val m hm]
      exact hc
  rw [etaR_castSucc_apply m i hi, reflSign]
  by_cases h : (i : ℕ) = 2
  · rw [if_pos h, if_pos (hcond.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hcond.mp hc))]


-- @@ L252-252 verbatim
/-! ## The harmonized reflected tube is of tube form -/


-- @@ L254-259 verbatim
theorem reflTube_g_eq (hm : 0 < m) (x : E) :
    ((CompactHopfPairPantsFrameLedger.reflectedTubeFLS m hm).codomainEquiv
        (hopfEquiv m hm)).g x =
      hopfEquiv m hm (coordinateReflection
        (CompactHopfPairPantsFrameLedger.reflectionIndex m hm)
        (CompactTubeConfiguration.levelMap m x)) := rfl


-- @@ L261-294 verbatim
theorem reflTube_g_eq_level (hm : 0 < m) (x : E) :
    ((CompactHopfPairPantsFrameLedger.reflectedTubeFLS m hm).codomainEquiv
        (hopfEquiv m hm)).g x = level m (reflParams m hm) 0 x := by
  apply PiLp.ext
  intro i
  rw [reflTube_g_eq m hm x, hopfSwap_apply m hm]
  induction i using Fin.lastCases with
  | last =>
      rw [if_neg (last_ne_zero_F m), if_pos rfl,
        coordinateReflection_apply_mul m hm, reflSign_zero m hm, one_mul,
        CompactTubeConfiguration.levelMap_apply_zero m x,
        level_zero_apply_last m (reflParams m hm) hm x]
  | cast j =>
      have hjl : (j.castSucc : Fin (m + 2)) ≠ Fin.last (m + 1) :=
        (Fin.castSucc_lt_last j).ne
      rw [level_zero_apply_castSucc m (reflParams m hm) hm x j,
        reflParams_eta m hm]
      by_cases hj0 : j = 0
      · subst hj0
        rw [Fin.castSucc_zero, if_pos rfl, coordinateReflection_apply_mul m hm,
          CompactTubeConfiguration.levelMap_apply_ne_zero m x
            (last_ne_zero_F m),
          if_pos rfl, last_succ_eq_iB, etaR_eq_reflSign_last m hm]
        ring
      · have hjne0 : (j.castSucc : Fin (m + 2)) ≠ 0 := by
          intro h
          apply hj0
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa using hv
        rw [if_neg hjne0, if_neg hjl, coordinateReflection_apply_mul m hm,
          CompactTubeConfiguration.levelMap_apply_ne_zero m x hjne0,
          if_neg hj0, etaR_eq_reflSign_castSucc m hm j hj0]
        ring


-- @@ L296-296 verbatim
/-! ## The reversed pants comparison -/


-- @@ L298-303 verbatim
/-- The pants comparison homotopy, run from the pants target back to the
reflected tube. -/
def pantsRev (hm : 0 < m) :
    DefiningMapHomotopy (CompactHopfPairPants.targetFLS m hm)
      (CompactHopfPairPantsFrameLedger.reflectedTubeFLS m hm) :=
  revHomotopy (CompactHopfPairPantsFrameLedger.homotopy m hm)


-- @@ L305-311 verbatim
/-- The sign label of the harmonized reflected tube reached from the pants
target. -/
def midSign (hm : 0 < m) :
    FiberSign ((CompactHopfPairPantsFrameLedger.reflectedTubeFLS m hm).codomainEquiv
      (hopfEquiv m hm)) :=
  ((CompactHopfPairPantsFrameLedger.pantsTargetSign m hm).restrict
    (pantsRev m hm).fiber_subset).codomainEquiv (hopfEquiv m hm)


-- @@ L313-321 verbatim
/-- The harmonized reversed pants comparison. -/
def pantsRevCob (hm : 0 < m) :
    SignedFramedLevelCobordism
      ((CompactHopfPairPantsFrameLedger.pantsTargetSign m hm).codomainEquiv
        (hopfEquiv m hm))
      (midSign m hm) :=
  ((pantsRev m hm).signedCobordism
    (CompactHopfPairPantsFrameLedger.pantsTargetSign m hm)).codomainEquiv
    (hopfEquiv m hm)


-- @@ L323-343 verbatim
theorem pantsRevCob_flat (hm : 0 < m) :
    (pantsRevCob m hm).SpatialFlatOutside
      (ConcreteConfigurationMorseReduction.compactBackground m) 0 2 := by
  have hbase : ((pantsRev m hm).signedCobordism
      (CompactHopfPairPantsFrameLedger.pantsTargetSign m hm)).SpatialFlatOutside
      (CompactHopfPairConfiguration.background m hm) 0 2 := by
    intro v hv
    have hnorm : (2 : ℝ) ≤ ‖initCLM (m + 3) v‖ := by
      simpa [dist_zero_right] using hv
    have h4 : (4 : ℝ) ≤ CompactBirth.normSq (initCLM (m + 3) v) := by
      rw [CompactBirth.normSq_eq_norm_sq]
      nlinarith
    show CompactHopfPairPantsFrameLedger.comparisonMap m hm
      (1 - normRamp (vertC v)) (initCLM (m + 3) v) =
      CompactHopfPairConfiguration.background m hm
    rw [CompactHopfPairPantsFrameLedger.comparisonMap,
      CompactBirth.cutoff_eq_one h4]
    simp
  have h := SignedFramedLevelCobordism.SpatialFlatOutside.codomainEquiv hbase
    (hopfEquiv m hm)
  rwa [hopfEquiv_background m hm] at h


-- @@ L345-345 verbatim
/-! ## The saddle-target kill -/


-- @@ L347-357 verbatim
/-- The comparison cobordism killing the harmonized pants target. -/
def saddleKillCob (hm : 0 < m) :
    SignedFramedLevelCobordism
      (CompactHopfPairPantsFrameLedger.zeroPairSaddleModel m hm).target.sign
      (CompactBirth.targetSign (m + 1)) :=
  StandardCircleMoveKit.retype
    ((pantsRevCob m hm).trans
      (signedCob m (reflParams m hm) (midSign m hm) (fun _ => rfl)
        (reflTube_g_eq_level m hm)))
    (CompactHopfPairPantsFrameLedger.zeroPairSaddleModel m hm).target.sign
    (CompactBirth.targetSign (m + 1)) rfl rfl (fun _ => rfl) (fun _ => rfl)


-- @@ L359-368 verbatim
theorem saddleKillCob_flat (hm : 0 < m) :
    (saddleKillCob m hm).SpatialFlatOutside
      (ConcreteConfigurationMorseReduction.compactBackground m) 0 (5 / 2) := by
  have h := StandardCircleMoveKit.spatialFlatOutside_trans
    (pantsRevCob_flat m hm)
    (signedCob_flat m (reflParams m hm) (midSign m hm) (fun _ => rfl)
      (reflTube_g_eq_level m hm))
  have h' := StandardCircleMoveKit.spatialFlatOutside_mono_radius h
    (by norm_num : max (2 : ℝ) (5 / 2) ≤ (5 / 2 : ℝ))
  exact StandardCircleMoveKit.retype_flat h'


-- @@ L370-377 verbatim
/-- The `saddleTargetKill` field of `PieceKillInput`. -/
theorem exists_saddleTargetKill (hm : 0 < m) :
    ∃ C : SignedFramedLevelCobordism
      (CompactHopfPairPantsFrameLedger.zeroPairSaddleModel m hm).target.sign
      (CompactBirth.targetSign (m + 1)),
      C.SpatialFlatOutside
        (ConcreteConfigurationMorseReduction.compactBackground m) 0 (5 / 2) :=
  ⟨saddleKillCob m hm, saddleKillCob_flat m hm⟩


-- @@ L379-379 verbatim
end PieceKill

-- @@ L380-380 verbatim
end Submission

