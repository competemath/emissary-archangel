import Submission.CompactHopfPairPants
import Submission.CompactHopfPairFrameLedger
import Submission.ConcreteZeroPairSaddle
import Submission.PTEndpointRegularSlabAdapter
import Submission.PTEndpointLedgerStability


-- @@ L7-24 verbatim
/-!
# Frame ledger and concrete consumer for the compact Hopf pair of pants

The outgoing endpoint of `CompactHopfPairPants` is the standard coordinate
circle, but its two distinguished normal rows are the position-dependent
matrix

`[[2 + x₀, x₁], [x₁, -(2 + x₀)]]`.

We compare it with the already computed compact tube after reflecting its
second distinguished output row.  The interpolation matrix

`[[p,q],[q,-p]]`, `p = 1 + s(1+x₀)`, `q = sx₁`,

is invertible on the common zero circle.  This gives an exact fixed-fiber
defining-map homotopy and transports the tube's existing singleton ledger
`[1]` to the pair-of-pants target.
-/


-- @@ L26-26 verbatim
set_option autoImplicit false


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Submission

-- @@ L31-31 verbatim
namespace CompactHopfPairPantsFrameLedger


-- @@ L33-33 verbatim
open Set Function Metric InnerProductSpace

-- @@ L34-34 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L36-36 verbatim
variable (m : ℕ) (hm : 0 < m)


-- @@ L38-38 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L39-39 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L41-44 verbatim
/-- The output row reflected in the standard tube comparison. -/
def reflectionIndex (_hm : 0 < m) : Fin (m + 2) := ⟨2, by
  clear hm
  omega⟩


-- @@ L46-49 verbatim
/-- Standard compact tube with output row two reflected. -/
def reflectedTubeFLS : FramedLevelSet (m + 2) :=
  (CompactTubeConfiguration.X m).codomainEquiv
    (coordinateReflection (reflectionIndex m hm))


-- @@ L51-53 verbatim
/-- The reflected tube tamed field. -/
def reflectedTubeField : TamedField (reflectedTubeFLS m hm) :=
  (CompactTubeConfiguration.field m).coordinateReflection (reflectionIndex m hm)


-- @@ L55-58 verbatim
/-- Radial equation interpolating from the tube's two-plane norm to the
ambient norm used by the pants endpoint. -/
def comparisonNormSq (s : ℝ) (x : E) : ℝ :=
  radSq x + s * (CompactBirth.normSq x - radSq x)


-- @@ L60-61 verbatim
/-- First entry of the interpolating normal block. -/
def comparisonP (s : ℝ) (x : E) : ℝ := 1 + s * (1 + x 0)


-- @@ L63-64 verbatim
/-- Off-diagonal entry of the interpolating normal block. -/
def comparisonQ (s : ℝ) (x : E) : ℝ := s * x 1


-- @@ L66-72 verbatim
/-- Uncompactified fixed-circle interpolation. -/
def comparisonCore (s : ℝ) (x : E) : F :=
  WithLp.toLp 2 fun i =>
    if i = 0 then (comparisonNormSq m s x - 1) / 2
    else if i = 1 then comparisonP m s x * x 2 + comparisonQ m s x * x 3
    else if i = 2 then comparisonQ m s x * x 2 - comparisonP m s x * x 3
    else x i.succ


-- @@ L74-76 verbatim
@[simp] lemma comparisonCore_apply_zero (s : ℝ) (x : E) :
    comparisonCore m s x 0 = (comparisonNormSq m s x - 1) / 2 := by
  simp [comparisonCore]


-- @@ L78-81 verbatim
@[simp] lemma comparisonCore_apply_one (s : ℝ) (x : E) :
    comparisonCore m s x 1 =
      comparisonP m s x * x 2 + comparisonQ m s x * x 3 := by
  simp [comparisonCore]


-- @@ L83-94 verbatim
lemma comparisonCore_apply_two (hm' : 0 < m) (s : ℝ) (x : E) :
    comparisonCore m s x 2 =
      comparisonQ m s x * x 2 - comparisonP m s x * x 3 := by
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at this
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at this
  simp [comparisonCore, h20, h21]


-- @@ L96-99 verbatim
lemma comparisonCore_apply_tail (s : ℝ) (x : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    comparisonCore m s x i = x i.succ := by
  simp [comparisonCore, hi0, hi1, hi2]


-- @@ L101-105 verbatim
/-- Compactification of the comparison through the common row-zero
background. -/
def comparisonMap (s : ℝ) (x : E) : F :=
  (1 - CompactBirth.cutoff x) • comparisonCore m s x +
    CompactBirth.cutoff x • CompactHopfPairConfiguration.background m hm


-- @@ L107-137 verbatim
lemma comparisonMap_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × E => comparisonMap m hm p.1 p.2) := by
  have hcore : ContDiff ℝ ∞
      (fun p : ℝ × E => comparisonCore m p.1 p.2) := by
    rw [contDiff_piLp]
    intro i
    by_cases hi0 : i = 0
    · subst i
      simp only [comparisonCore_apply_zero]
      unfold comparisonNormSq
      exact (((contDiff_radSq (m := m)).comp contDiff_snd).add
        (contDiff_fst.mul
          ((CompactBirth.contDiff_normSq.comp contDiff_snd).sub
            ((contDiff_radSq (m := m)).comp contDiff_snd)))).sub
              contDiff_const |>.div_const 2
    · by_cases hi1 : i = 1
      · subst i
        simp only [comparisonCore_apply_one]
        unfold comparisonP comparisonQ
        fun_prop
      · by_cases hi2 : i = 2
        · subst i
          simp only [comparisonCore_apply_two m hm]
          unfold comparisonP comparisonQ
          fun_prop
        · simp only [comparisonCore_apply_tail m _ _ hi0 hi1 hi2]
          fun_prop
  unfold comparisonMap
  exact ((contDiff_const.sub (CompactBirth.contDiff_cutoff.comp contDiff_snd)).smul
      hcore).add
    ((CompactBirth.contDiff_cutoff.comp contDiff_snd).smul contDiff_const)


-- @@ L139-140 verbatim
@[simp] lemma comparisonNormSq_zero (x : E) :
    comparisonNormSq m 0 x = radSq x := by simp [comparisonNormSq]


-- @@ L142-144 verbatim
@[simp] lemma comparisonNormSq_one (x : E) :
    comparisonNormSq m 1 x = CompactBirth.normSq x := by
  simp [comparisonNormSq]


-- @@ L146-147 verbatim
@[simp] lemma comparisonP_zero (x : E) : comparisonP m 0 x = 1 := by
  simp [comparisonP]


-- @@ L149-150 verbatim
@[simp] lemma comparisonQ_zero (x : E) : comparisonQ m 0 x = 0 := by
  simp [comparisonQ]


-- @@ L152-154 verbatim
@[simp] lemma comparisonP_one (x : E) : comparisonP m 1 x = 2 + x 0 := by
  simp [comparisonP]
  ring


-- @@ L156-157 verbatim
@[simp] lemma comparisonQ_one (x : E) : comparisonQ m 1 x = x 1 := by
  simp [comparisonQ]


-- @@ L159-169 verbatim
/-- All maps in this comparison use the same row-zero background. -/
lemma hopf_background_eq_tube_background :
    CompactHopfPairConfiguration.background m hm =
      CompactTubeConfiguration.background m := by
  apply PiLp.ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp
  · simp [CompactHopfPairConfiguration.background_apply_ne_zero m hm hi,
      CompactTubeConfiguration.background_apply_ne_zero m hi]


-- @@ L171-219 verbatim
lemma comparisonCore_zero (x : E) :
    comparisonCore m 0 x =
      coordinateReflection (reflectionIndex m hm)
        (CompactTubeConfiguration.coreMap m x) := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    have h0r : (0 : Fin (m + 2)) ≠ reflectionIndex m hm := by
      intro h
      have hv := congrArg Fin.val h
      simp [reflectionIndex] at hv
    rw [coordinateReflection_apply_ne _ _ h0r]
    simp
  · by_cases hi1 : i = 1
    · subst i
      have h1r : (1 : Fin (m + 2)) ≠ reflectionIndex m hm := by
        intro h
        have hv := congrArg Fin.val h
        simp [reflectionIndex, Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
      rw [coordinateReflection_apply_ne _ _ h1r]
      simp
    · by_cases hi2 : i = 2
      · subst i
        have h2r : (2 : Fin (m + 2)) = reflectionIndex m hm := by
          apply Fin.ext
          simp [reflectionIndex, Nat.mod_eq_of_lt (by omega : 2 < m + 2)]
        rw [← h2r, coordinateReflection_apply_same]
        have h20 : (2 : Fin (m + 2)) ≠ 0 := by
          intro h
          have hv := congrArg Fin.val h
          simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
        rw [CompactTubeConfiguration.coreMap_apply_ne_zero m x h20]
        rw [comparisonCore_apply_two m hm]
        simp only [comparisonP_zero,
          comparisonQ_zero, zero_mul, one_mul, zero_sub, neg_inj]
        apply congrArg (fun j : Fin (m + 3) => x j)
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
        all_goals exact hm
      · have hir : i ≠ reflectionIndex m hm := by
          intro h
          apply hi2
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa [reflectionIndex, Nat.mod_eq_of_lt (by omega : 2 < m + 2)] using hv
        rw [coordinateReflection_apply_ne _ _ hir]
        rw [comparisonCore_apply_tail m 0 x hi0 hi1 hi2,
          CompactTubeConfiguration.coreMap_apply_ne_zero m x hi0]


-- @@ L221-234 verbatim
lemma coordinateReflection_tube_background :
    coordinateReflection (reflectionIndex m hm)
        (CompactTubeConfiguration.background m) =
      CompactTubeConfiguration.background m := by
  apply PiLp.ext
  intro i
  by_cases hir : i = reflectionIndex m hm
  · rw [hir, coordinateReflection_apply_same]
    have hr0 : reflectionIndex m hm ≠ (0 : Fin (m + 2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp [reflectionIndex] at hv
    simp [CompactTubeConfiguration.background_apply_ne_zero m hr0]
  · rw [coordinateReflection_apply_ne _ _ hir]


-- @@ L236-244 verbatim
lemma comparisonMap_zero : comparisonMap m hm 0 = (reflectedTubeFLS m hm).g := by
  funext x
  change comparisonMap m hm 0 x =
    coordinateReflection (reflectionIndex m hm)
      (CompactTubeConfiguration.levelMap m x)
  rw [comparisonMap, CompactTubeConfiguration.levelMap,
    comparisonCore_zero m hm x, hopf_background_eq_tube_background m hm]
  rw [map_add, map_smul, map_smul,
    coordinateReflection_tube_background m hm]


-- @@ L246-265 verbatim
lemma comparisonCore_one (x : E) :
    comparisonCore m 1 x = CompactHopfPairPants.coreMap m hm 2 0 x := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    simp
  · by_cases hi1 : i = 1
    · subst i
      simp [CompactHopfPairPants.pairRe,
        CompactHopfPairConfiguration.hopfRe]
      ring
    · by_cases hi2 : i = 2
      · subst i
        simp [comparisonCore_apply_two m hm,
          CompactHopfPairPants.pairIm,
          CompactHopfPairConfiguration.hopfIm]
        ring
      · rw [comparisonCore_apply_tail m 1 x hi0 hi1 hi2,
          CompactHopfPairPants.coreMap_apply_tail m hm 2 0 x hi0 hi1 hi2]


-- @@ L267-273 verbatim
lemma comparisonMap_one :
    comparisonMap m hm 1 = (CompactHopfPairPants.targetFLS m hm).g := by
  funext x
  change comparisonMap m hm 1 x =
    CompactHopfPairPants.levelMap m hm 2 0 x
  rw [comparisonMap, CompactHopfPairPants.levelMap,
    comparisonCore_one m hm x]


-- @@ L275-275 verbatim
/-! ## Exact common zero fiber -/


-- @@ L277-282 verbatim
@[simp] lemma comparisonMap_apply_zero (s : ℝ) (x : E) :
    comparisonMap m hm s x 0 =
      (1 - CompactBirth.cutoff x) *
          ((comparisonNormSq m s x - 1) / 2) +
        CompactBirth.cutoff x := by
  simp [comparisonMap]


-- @@ L284-288 verbatim
@[simp] lemma comparisonMap_apply_one (s : ℝ) (x : E) :
    comparisonMap m hm s x 1 =
      (1 - CompactBirth.cutoff x) *
        (comparisonP m s x * x 2 + comparisonQ m s x * x 3) := by
  simp [comparisonMap]


-- @@ L290-301 verbatim
lemma comparisonMap_apply_two (s : ℝ) (x : E) :
    comparisonMap m hm s x 2 =
      (1 - CompactBirth.cutoff x) *
        (comparisonQ m s x * x 2 - comparisonP m s x * x 3) := by
  rw [comparisonMap]
  simp only [PiLp.add_apply, PiLp.smul_apply, comparisonCore_apply_two m hm]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  rw [CompactHopfPairConfiguration.background_apply_ne_zero m hm h20]
  ring


-- @@ L303-311 verbatim
lemma comparisonMap_apply_tail (s : ℝ) (x : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    comparisonMap m hm s x i =
      (1 - CompactBirth.cutoff x) * x i.succ := by
  rw [comparisonMap]
  simp only [PiLp.add_apply, PiLp.smul_apply,
    comparisonCore_apply_tail m s x hi0 hi1 hi2]
  rw [CompactHopfPairConfiguration.background_apply_ne_zero m hm hi0]
  ring


-- @@ L313-322 verbatim
lemma cutoff_lt_one_of_comparisonMap_eq_zero {s : ℝ} {x : E}
    (hx : comparisonMap m hm s x = 0) : CompactBirth.cutoff x < 1 := by
  have h0 := congrArg (fun q : F => q 0) hx
  rw [comparisonMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  have hc1 := CompactBirth.cutoff_le_one x
  apply lt_of_le_of_ne hc1
  intro hc
  rw [hc] at h0
  norm_num at h0


-- @@ L324-336 verbatim
lemma comparisonNormSq_le_one_of_comparisonMap_eq_zero {s : ℝ} {x : E}
    (hx : comparisonMap m hm s x = 0) : comparisonNormSq m s x ≤ 1 := by
  have h0 := congrArg (fun q : F => q 0) hx
  rw [comparisonMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  have hc_lt := cutoff_lt_one_of_comparisonMap_eq_zero m hm hx
  have hc0 := CompactBirth.cutoff_nonneg x
  by_contra hn
  have hrad : 0 < (comparisonNormSq m s x - 1) / 2 := by linarith
  have hprod : 0 < (1 - CompactBirth.cutoff x) *
      ((comparisonNormSq m s x - 1) / 2) :=
    mul_pos (sub_pos.mpr hc_lt) hrad
  linarith


-- @@ L338-344 verbatim
lemma radSq_le_comparisonNormSq (s : ℝ) (hs0 : 0 ≤ s) (x : E) :
    radSq x ≤ comparisonNormSq m s x := by
  have htail : 0 ≤ CompactBirth.normSq x - radSq x := by
    rw [sub_nonneg, CompactBirth.normSq_eq_norm_sq]
    exact radSq_le_normSq x
  unfold comparisonNormSq
  exact le_add_of_nonneg_right (mul_nonneg hs0 htail)


-- @@ L346-356 verbatim
lemma comparisonP_pos_of_comparisonMap_eq_zero {s : ℝ} (hs0 : 0 ≤ s)
    {x : E} (hx : comparisonMap m hm s x = 0) :
    0 < comparisonP m s x := by
  have hQ := comparisonNormSq_le_one_of_comparisonMap_eq_zero m hm hx
  have hrs := radSq_le_comparisonNormSq m s hs0 x
  have hx0sq : x 0 ^ 2 ≤ 1 := by
    unfold radSq at hrs
    nlinarith [sq_nonneg (x 1)]
  have hx0 : -1 ≤ x 0 := by nlinarith
  unfold comparisonP
  nlinarith


-- @@ L358-393 verbatim
lemma pair_coordinates_eq_zero_of_comparisonMap_eq_zero {s : ℝ}
    (hs0 : 0 ≤ s) {x : E} (hx : comparisonMap m hm s x = 0) :
    x 2 = 0 ∧ x 3 = 0 := by
  have hc_lt := cutoff_lt_one_of_comparisonMap_eq_zero m hm hx
  have hfac : 1 - CompactBirth.cutoff x ≠ 0 := ne_of_gt (sub_pos.mpr hc_lt)
  have h1 := congrArg (fun q : F => q 1) hx
  rw [comparisonMap_apply_one] at h1
  simp only [PiLp.zero_apply] at h1
  have hA : comparisonP m s x * x 2 + comparisonQ m s x * x 3 = 0 :=
    (mul_eq_zero.mp h1).resolve_left hfac
  have h2 := congrArg (fun q : F => q 2) hx
  rw [comparisonMap_apply_two] at h2
  simp only [PiLp.zero_apply] at h2
  have hB : comparisonQ m s x * x 2 - comparisonP m s x * x 3 = 0 :=
    (mul_eq_zero.mp h2).resolve_left hfac
  have hp := comparisonP_pos_of_comparisonMap_eq_zero m hm hs0 hx
  have hden : 0 < comparisonP m s x ^ 2 + comparisonQ m s x ^ 2 := by
    nlinarith [sq_nonneg (comparisonQ m s x)]
  have hx2prod :
      (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2) * x 2 = 0 := by
    calc
      _ = comparisonP m s x *
            (comparisonP m s x * x 2 + comparisonQ m s x * x 3) +
          comparisonQ m s x *
            (comparisonQ m s x * x 2 - comparisonP m s x * x 3) := by ring
      _ = 0 := by rw [hA, hB]; ring
  have hx3prod :
      (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2) * x 3 = 0 := by
    calc
      _ = comparisonQ m s x *
            (comparisonP m s x * x 2 + comparisonQ m s x * x 3) -
          comparisonP m s x *
            (comparisonQ m s x * x 2 - comparisonP m s x * x 3) := by ring
      _ = 0 := by rw [hA, hB]; ring
  exact ⟨(mul_eq_zero.mp hx2prod).resolve_left (ne_of_gt hden),
    (mul_eq_zero.mp hx3prod).resolve_left (ne_of_gt hden)⟩


-- @@ L395-420 verbatim
lemma transverse_eq_zero_of_comparisonMap_eq_zero {s : ℝ}
    (hs0 : 0 ≤ s) {x : E} (hx : comparisonMap m hm s x = 0)
    {i : Fin (m + 2)} (hi : i ≠ 0) : x i.succ = 0 := by
  by_cases hi1 : i = 1
  · subst i
    have hz := (pair_coordinates_eq_zero_of_comparisonMap_eq_zero m hm hs0 hx).1
    simpa using hz
  · by_cases hi2 : i = 2
    · subst i
      have hz := (pair_coordinates_eq_zero_of_comparisonMap_eq_zero m hm hs0 hx).2
      let j3 : Fin (m + 3) := ⟨3, by omega⟩
      have hj : (2 : Fin (m + 2)).succ = j3 := by
        apply Fin.ext
        simp [j3, Nat.mod_eq_of_lt (by omega : 2 < m + 2)]
      rw [hj]
      change x j3 = 0
      convert hz using 1
      apply congrArg (fun j : Fin (m + 3) => x j)
      apply Fin.ext
      simp [j3, Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
    · have hout := congrArg (fun q : F => q i) hx
      rw [comparisonMap_apply_tail m hm s x hi hi1 hi2] at hout
      simp only [PiLp.zero_apply] at hout
      exact (mul_eq_zero.mp hout).resolve_left
        (sub_ne_zero.mpr
          (cutoff_lt_one_of_comparisonMap_eq_zero m hm hx).ne')


-- @@ L422-435 verbatim
lemma normSq_eq_radSq_of_comparisonMap_eq_zero {s : ℝ}
    (hs0 : 0 ≤ s) {x : E} (hx : comparisonMap m hm s x = 0) :
    CompactBirth.normSq x = radSq x := by
  unfold CompactBirth.normSq radSq
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  have htail : ∀ i : Fin (m + 1), x i.succ.succ ^ 2 = 0 := by
    intro i
    let j : Fin (m + 2) := i.succ
    have hj : j ≠ 0 := Fin.succ_ne_zero i
    have hz : x j.succ = 0 :=
      transverse_eq_zero_of_comparisonMap_eq_zero m hm hs0 hx hj
    simpa [j, hz]
  simp only [htail, Finset.sum_const_zero, add_zero]


-- @@ L437-512 verbatim
theorem comparisonMap_eq_zero_iff_standardCircle (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : E) :
    comparisonMap m hm s x = 0 ↔ x ∈ standardCircle := by
  constructor
  · intro hx
    have hnorm := normSq_eq_radSq_of_comparisonMap_eq_zero m hm hs0 hx
    have hQ := comparisonNormSq_le_one_of_comparisonMap_eq_zero m hm hx
    have hrs : radSq x ≤ 1 := by
      unfold comparisonNormSq at hQ
      rw [hnorm] at hQ
      simpa using hQ
    have hc : CompactBirth.cutoff x = 0 := by
      apply CompactBirth.cutoff_eq_zero
      rw [hnorm]
      linarith
    have h0 := congrArg (fun q : F => q 0) hx
    rw [comparisonMap_apply_zero, hc] at h0
    simp only [sub_zero, one_mul, zero_add, PiLp.zero_apply] at h0
    have hrs1 : radSq x = 1 := by
      unfold comparisonNormSq at h0
      rw [hnorm] at h0
      simpa using (show radSq x = 1 by linarith)
    apply (CompactTubeConfiguration.levelMap_eq_zero_iff_standardCircle m x).mp
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [CompactTubeConfiguration.levelMap, hc, hrs1]
    · simp [CompactTubeConfiguration.levelMap, hc,
        CompactTubeConfiguration.coreMap_apply_ne_zero m x hi,
        transverse_eq_zero_of_comparisonMap_eq_zero m hm hs0 hx hi]
  · intro hx
    obtain ⟨theta, rfl⟩ := hx
    have hnorm : CompactBirth.normSq (circleAt (m := m) theta) = 1 := by
      rw [CompactBirth.normSq_eq_norm_sq, norm_circleAt, one_pow]
    have hc : CompactBirth.cutoff (circleAt (m := m) theta) = 0 :=
      CompactBirth.cutoff_eq_zero (by rw [hnorm]; norm_num)
    have hx2 : circleAt (m := m) theta 2 = 0 := by
      apply circleAt_apply_other theta
      · intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
      · intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
    have hx3 : circleAt (m := m) theta 3 = 0 := by
      apply circleAt_apply_other theta
      · intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
      · intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
    rw [comparisonMap, hc]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    apply PiLp.ext
    intro i
    by_cases hi0 : i = 0
    · subst i
      simp [comparisonCore, comparisonNormSq, hnorm, radSq_circleAt]
    · by_cases hi1 : i = 1
      · subst i
        rw [comparisonCore_apply_one, hx2, hx3]
        simp
      · by_cases hi2 : i = 2
        · subst i
          rw [comparisonCore_apply_two m hm]
          rw [hx2, hx3]
          simp
        · rw [comparisonCore_apply_tail m s _ hi0 hi1 hi2]
          apply circleAt_apply_other theta
          · exact Fin.succ_ne_zero i
          · intro h
            apply hi0
            apply Fin.succ_injective
            simpa using h


-- @@ L514-514 verbatim
/-! ## Regularity of the comparison family -/


-- @@ L516-541 verbatim
lemma contDiff_comparisonCore (hm' : 0 < m) (s : ℝ) :
    ContDiff ℝ ∞ (comparisonCore m s) := by
  -- Use the already established polynomial component proof directly; the
  -- compactification is not involved here.
  rw [contDiff_piLp]
  intro i
  by_cases hi0 : i = 0
  · subst i
    simp only [comparisonCore_apply_zero]
    unfold comparisonNormSq
    exact ((contDiff_radSq (m := m)).add
      (contDiff_const.mul
        (CompactBirth.contDiff_normSq.sub (contDiff_radSq (m := m))))).sub
          contDiff_const |>.div_const 2
  · by_cases hi1 : i = 1
    · subst i
      simp only [comparisonCore_apply_one]
      unfold comparisonP comparisonQ
      fun_prop
    · by_cases hi2 : i = 2
      · subst i
        simp only [comparisonCore_apply_two m hm']
        unfold comparisonP comparisonQ
        fun_prop
      · simp only [comparisonCore_apply_tail m s _ hi0 hi1 hi2]
        exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff


-- @@ L543-554 verbatim
private lemma fderiv_coord_apply
    (G : E → F) (hG : ContDiff ℝ ∞ G)
    (i : Fin (m + 2)) (x h : E) :
    fderiv ℝ (fun q => G q i) x h = fderiv ℝ G x h i := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj i
  have hG' : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => G q i)
      (outProj.comp (fderiv ℝ G x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (G x) i).comp x hG'
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hcomp.fderiv
  simpa [outProj] using happ


-- @@ L556-589 verbatim
lemma fderiv_comparisonCore_apply_one (hm' : 0 < m) (s : ℝ) (x h : E) :
    fderiv ℝ (comparisonCore m s) x h 1 =
      s * h 0 * x 2 + comparisonP m s x * h 2 +
        s * h 1 * x 3 + comparisonQ m s x * h 3 := by
  rw [← fderiv_coord_apply m (comparisonCore m s)
    (contDiff_comparisonCore m hm' s) 1 x h]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := h2.add
    ((((h0.mul h2).add h2).add (h1.mul h3)).const_mul s)
  have hevent : (fun q : E =>
      q 2 + s * (q 0 * q 2 + q 2 + q 1 * q 3)) =ᶠ[nhds x]
      ((fun q : E => q 2) + fun q =>
        s * (q 0 * q 2 + q 2 + q 1 * q 3)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hd' := hd.congr_of_eventuallyEq hevent
  have hfun : (fun q : E => comparisonCore m s q 1) = fun q =>
      q 2 + s * (q 0 * q 2 + q 2 + q 1 * q 3) := by
    funext q
    rw [comparisonCore_apply_one]
    simp [comparisonP, comparisonQ]
    ring
  rw [hfun]
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd'.fderiv
  simp [p0, p1, p2, p3] at happ
  rw [happ]
  unfold comparisonP comparisonQ
  ring


-- @@ L591-624 verbatim
lemma fderiv_comparisonCore_apply_two (hm' : 0 < m) (s : ℝ) (x h : E) :
    fderiv ℝ (comparisonCore m s) x h 2 =
      s * h 1 * x 2 + comparisonQ m s x * h 2 -
        s * h 0 * x 3 - comparisonP m s x * h 3 := by
  rw [← fderiv_coord_apply m (comparisonCore m s)
    (contDiff_comparisonCore m hm' s) 2 x h]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := h3.neg.add
    ((((h1.mul h2).sub (h0.mul h3)).sub h3).const_mul s)
  have hevent : (fun q : E =>
      -q 3 + s * (q 1 * q 2 - q 0 * q 3 - q 3)) =ᶠ[nhds x]
      ((- fun q : E => q 3) + fun q =>
        s * (q 1 * q 2 - q 0 * q 3 - q 3)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hd' := hd.congr_of_eventuallyEq hevent
  have hfun : (fun q : E => comparisonCore m s q 2) = fun q =>
      -q 3 + s * (q 1 * q 2 - q 0 * q 3 - q 3) := by
    funext q
    rw [comparisonCore_apply_two m hm']
    simp [comparisonP, comparisonQ]
    ring
  rw [hfun]
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd'.fderiv
  simp [p0, p1, p2, p3] at happ
  rw [happ]
  unfold comparisonP comparisonQ
  ring


-- @@ L626-636 verbatim
lemma fderiv_comparisonCore_apply_tail (hm' : 0 < m) (s : ℝ) (x h : E)
    {i : Fin (m + 2)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    fderiv ℝ (comparisonCore m s) x h i = h i.succ := by
  rw [← fderiv_coord_apply m (comparisonCore m s)
    (contDiff_comparisonCore m hm' s) i x h]
  have hfun : (fun q : E => comparisonCore m s q i) = fun q => q i.succ := by
    funext q
    exact comparisonCore_apply_tail m s q hi0 hi1 hi2
  rw [hfun]
  exact congrArg (fun L : E →L[ℝ] ℝ => L h)
    (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).hasFDerivAt.fderiv


-- @@ L638-657 verbatim
lemma fderiv_radialCore_apply (x h : E) :
    fderiv ℝ (fun q : E => (radSq q - 1) / 2) x h =
      x 0 * h 0 + x 1 * h 1 := by
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have hd := (((h0.pow 2).add (h1.pow 2)).sub_const 1).const_mul (1 / 2 : ℝ)
  have hfun : (fun q : E => (radSq q - 1) / 2) = fun q =>
      (1 / 2 : ℝ) * (q 0 ^ 2 + q 1 ^ 2 - 1) := by
    funext q
    simp [radSq]
    ring
  rw [hfun]
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd.fderiv
  calc
    _ = (1 / 2 : ℝ) * (2 * x 0 * h 0) +
        (1 / 2 : ℝ) * (2 * x 1 * h 1) := by
      simpa [p0, p1] using happ
    _ = x 0 * h 0 + x 1 * h 1 := by ring


-- @@ L659-728 verbatim
lemma fderiv_comparisonCore_apply_zero_of_standardCircle
    (hm' : 0 < m) (s : ℝ) {x : E} (hx : x ∈ standardCircle) (h : E) :
    fderiv ℝ (comparisonCore m s) x h 0 = ⟪x, h⟫_ℝ := by
  rw [← fderiv_coord_apply m (comparisonCore m s)
    (contDiff_comparisonCore m hm' s) 0 x h]
  have hfun : (fun q : E => comparisonCore m s q 0) = fun q =>
      (1 - s) * ((radSq q - 1) / 2) +
        s * (CompactHopfPairPants.coreMap m hm' 2 0 q 0) := by
    funext q
    simp [comparisonNormSq]
    ring
  rw [hfun]
  let radial : E → ℝ := fun q => (radSq q - 1) / 2
  let targetRow : E → ℝ := fun q =>
    CompactHopfPairPants.coreMap m hm' 2 0 q 0
  have hradDiff : DifferentiableAt ℝ radial x :=
    (((contDiff_radSq (m := m)).sub contDiff_const).div_const 2).differentiable
      infty_ne_zero x
  have htargetDiff : DifferentiableAt ℝ targetRow x :=
    ((EuclideanSpace.proj 0 : F →L[ℝ] ℝ).contDiff.comp
      (CompactHopfPairPants.contDiff_coreMap m hm' 2 0)).differentiable
        infty_ne_zero x
  have hd := (hradDiff.hasFDerivAt.const_mul (1 - s)).add
    (htargetDiff.hasFDerivAt.const_mul s)
  have hevent :
      (fun q : E => (1 - s) * radial q + s * targetRow q) =ᶠ[nhds x]
        ((fun q : E => (1 - s) * radial q) + fun q => s * targetRow q) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hd' := hd.congr_of_eventuallyEq hevent
  have hdval := congrArg (fun L : E →L[ℝ] ℝ => L h) hd'.fderiv
  have hderiv :
      fderiv ℝ (fun q : E => (1 - s) * radial q + s * targetRow q) x h =
        (1 - s) * fderiv ℝ radial x h +
          s * fderiv ℝ targetRow x h := by
    simpa using hdval
  rw [show (fun q : E =>
      (1 - s) * ((radSq q - 1) / 2) +
        s * CompactHopfPairPants.coreMap m hm' 2 0 q 0) =
      (fun q : E => (1 - s) * radial q + s * targetRow q) by rfl]
  rw [hderiv]
  have htarget : fderiv ℝ targetRow x h = ⟪x, h⟫_ℝ := by
    rw [fderiv_coord_apply m (CompactHopfPairPants.coreMap m hm' 2 0)
      (CompactHopfPairPants.contDiff_coreMap m hm' 2 0)]
    exact CompactHopfPairPants.fderiv_target_coreMap_apply_zero m hm' x h
  have hrad := fderiv_radialCore_apply m x h
  have hradInner : x 0 * h 0 + x 1 * h 1 = ⟪x, h⟫_ℝ := by
    obtain ⟨theta, rfl⟩ := hx
    rw [PiLp.inner_apply]
    have hsum : ∑ j : Fin (m + 3),
        ⟪circleAt (m := m) theta j, h j⟫_ℝ =
          circleAt (m := m) theta 0 * h 0 +
            circleAt (m := m) theta 1 * h 1 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have htail : ∀ j : Fin (m + 1),
          ⟪circleAt (m := m) theta j.succ.succ,
            h j.succ.succ⟫_ℝ = 0 := by
        intro j
        rw [circleAt_apply_other theta]
        · simp [RCLike.inner_apply]
        · exact Fin.succ_ne_zero _
        · intro hj
          have hv := congrArg Fin.val hj
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
      simp only [Fin.succ_zero_eq_one, htail, Finset.sum_const_zero, add_zero]
      simp [RCLike.inner_apply]
      ring
    exact hsum.symm
  rw [htarget, hrad, hradInner]
  ring


-- @@ L730-740 verbatim
/-- Explicit right inverse for the comparison differential on its fixed
circle. -/
def comparisonPreimage (s : ℝ) (x : E) (y : F) : E :=
  let S := comparisonP m s x ^ 2 + comparisonQ m s x ^ 2
  WithLp.toLp 2 <| Fin.cases (x 0 * y 0) fun i =>
    if i = 0 then x 1 * y 0
    else if i = 1 then
      (comparisonP m s x * y 1 + comparisonQ m s x * y 2) / S
    else if i = 2 then
      (comparisonQ m s x * y 1 - comparisonP m s x * y 2) / S
    else y i


-- @@ L742-744 verbatim
@[simp] lemma comparisonPreimage_apply_zero (s : ℝ) (x : E) (y : F) :
    comparisonPreimage m s x y 0 = x 0 * y 0 := by
  simp [comparisonPreimage]


-- @@ L746-757 verbatim
@[simp] lemma comparisonPreimage_apply_succ (s : ℝ) (x : E) (y : F)
    (i : Fin (m + 2)) :
    comparisonPreimage m s x y i.succ =
      if i = 0 then x 1 * y 0
      else if i = 1 then
        (comparisonP m s x * y 1 + comparisonQ m s x * y 2) /
          (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2)
      else if i = 2 then
        (comparisonQ m s x * y 1 - comparisonP m s x * y 2) /
          (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2)
      else y i := by
  simp [comparisonPreimage]


-- @@ L759-769 verbatim
@[simp] lemma comparisonPreimage_apply_one (s : ℝ) (x : E) (y : F) :
    comparisonPreimage m s x y 1 = x 1 * y 0 := by
  have h1 : (1 : Fin (m + 3)) = (0 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp
  calc
    comparisonPreimage m s x y 1 =
        comparisonPreimage m s x y (0 : Fin (m + 2)).succ :=
      congrArg (fun j => comparisonPreimage m s x y j) h1
    _ = _ := by
      simpa using comparisonPreimage_apply_succ m s x y (0 : Fin (m + 2))


-- @@ L771-790 verbatim
@[simp] lemma comparisonPreimage_apply_two (hm' : 0 < m)
    (s : ℝ) (x : E) (y : F) :
    comparisonPreimage m s x y 2 =
      (comparisonP m s x * y 1 + comparisonQ m s x * y 2) /
        (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2) := by
  have h2 : (2 : Fin (m + 3)) = (1 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    comparisonPreimage m s x y 2 =
        comparisonPreimage m s x y (1 : Fin (m + 2)).succ :=
      congrArg (fun j => comparisonPreimage m s x y j) h2
    _ = _ := by
      simpa [h10] using
        comparisonPreimage_apply_succ m s x y (1 : Fin (m + 2))


-- @@ L792-815 verbatim
@[simp] lemma comparisonPreimage_apply_three (hm' : 0 < m)
    (s : ℝ) (x : E) (y : F) :
    comparisonPreimage m s x y 3 =
      (comparisonQ m s x * y 1 - comparisonP m s x * y 2) /
        (comparisonP m s x ^ 2 + comparisonQ m s x ^ 2) := by
  have h3 : (3 : Fin (m + 3)) = (2 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  calc
    comparisonPreimage m s x y 3 =
        comparisonPreimage m s x y (2 : Fin (m + 2)).succ :=
      congrArg (fun j => comparisonPreimage m s x y j) h3
    _ = _ := by
      simpa [h20, h21] using
        comparisonPreimage_apply_succ m s x y (2 : Fin (m + 2))


-- @@ L817-820 verbatim
lemma comparisonPreimage_apply_tail (s : ℝ) (x : E) (y : F)
    {i : Fin (m + 2)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    comparisonPreimage m s x y i.succ = y i := by
  simp [comparisonPreimage, hi0, hi1, hi2]


-- @@ L822-826 verbatim
private lemma inner_eq_sum_local (x h : E) :
    ⟪x, h⟫_ℝ = ∑ j, x j * h j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [RCLike.inner_apply, mul_comm]


-- @@ L828-835 verbatim
lemma comparison_denominator_pos (hm' : 0 < m)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : E} (hx : x ∈ standardCircle) :
    0 < comparisonP m s x ^ 2 + comparisonQ m s x ^ 2 := by
  have hzero :=
    (comparisonMap_eq_zero_iff_standardCircle m hm' s hs0 hs1 x).mpr hx
  have hp := comparisonP_pos_of_comparisonMap_eq_zero m hm' hs0 hzero
  nlinarith [sq_nonneg (comparisonQ m s x)]


-- @@ L837-862 verbatim
lemma inner_comparisonPreimage (s : ℝ) {x : E}
    (hx : x ∈ standardCircle) (y : F) :
    ⟪x, comparisonPreimage m s x y⟫_ℝ = y 0 := by
  obtain ⟨theta, rfl⟩ := hx
  rw [inner_eq_sum_local]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, comparisonPreimage_apply_zero,
    comparisonPreimage_apply_one]
  have htail : ∀ j : Fin (m + 1),
      circleAt (m := m) theta j.succ.succ *
        comparisonPreimage m s (circleAt theta) y j.succ.succ = 0 := by
    intro j
    rw [circleAt_apply_other theta]
    · ring
    · exact Fin.succ_ne_zero _
    · intro hj
      have hv := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
  simp only [htail, Finset.sum_const_zero, add_zero]
  rw [circleAt_apply_zero, circleAt_apply_one]
  calc
    Real.cos theta * (Real.cos theta * y 0) +
        Real.sin theta * (Real.sin theta * y 0) =
      (Real.sin theta ^ 2 + Real.cos theta ^ 2) * y 0 := by ring
    _ = y 0 := by rw [Real.sin_sq_add_cos_sq, one_mul]


-- @@ L864-895 verbatim
lemma fderiv_comparisonCore_comparisonPreimage
    (hm' : 0 < m) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : E} (hx : x ∈ standardCircle) (y : F) :
    fderiv ℝ (comparisonCore m s) x (comparisonPreimage m s x y) = y := by
  have hzero :=
    (comparisonMap_eq_zero_iff_standardCircle m hm' s hs0 hs1 x).mpr hx
  have hu := pair_coordinates_eq_zero_of_comparisonMap_eq_zero m hm' hs0 hzero
  have hden := comparison_denominator_pos m hm' s hs0 hs1 hx
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_comparisonCore_apply_zero_of_standardCircle m hm' s hx,
      inner_comparisonPreimage m s hx y]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_comparisonCore_apply_one m hm']
      simp only [comparisonPreimage_apply_zero, comparisonPreimage_apply_one,
        comparisonPreimage_apply_two m hm', comparisonPreimage_apply_three m hm',
        hu.1, hu.2, mul_zero, zero_mul, zero_add]
      field_simp
      ring
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_comparisonCore_apply_two m hm']
        simp only [comparisonPreimage_apply_zero, comparisonPreimage_apply_one,
          comparisonPreimage_apply_two m hm', comparisonPreimage_apply_three m hm',
          hu.1, hu.2, mul_zero, zero_mul, zero_add, sub_zero]
        field_simp
        ring
      · rw [fderiv_comparisonCore_apply_tail m hm' s x _ hi0 hi1 hi2,
          comparisonPreimage_apply_tail m s x y hi0 hi1 hi2]


-- @@ L897-903 verbatim
theorem surjective_fderiv_comparisonCore_of_standardCircle
    (hm' : 0 < m) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {x : E} (hx : x ∈ standardCircle) :
    Function.Surjective (fderiv ℝ (comparisonCore m s) x) := by
  intro y
  exact ⟨comparisonPreimage m s x y,
    fderiv_comparisonCore_comparisonPreimage m hm' s hs0 hs1 hx y⟩


-- @@ L905-912 verbatim
lemma comparisonMap_eventuallyEq_core (s : ℝ) {x : E}
    (hx : CompactBirth.normSq x < 2) :
    comparisonMap m hm s =ᶠ[nhds x] comparisonCore m s := by
  have hopen : IsOpen {z : E | CompactBirth.normSq z < 2} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => by
    rw [comparisonMap, CompactBirth.cutoff_eq_zero hz.le]
    simp


-- @@ L914-926 verbatim
theorem surjective_fderiv_comparisonMap_of_eq_zero
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {x : E}
    (hx : comparisonMap m hm s x = 0) :
    Function.Surjective (fderiv ℝ (comparisonMap m hm s) x) := by
  have hcircle :=
    (comparisonMap_eq_zero_iff_standardCircle m hm s hs0 hs1 x).mp hx
  have hnorm : CompactBirth.normSq x < 2 := by
    obtain ⟨theta, rfl⟩ := hcircle
    rw [CompactBirth.normSq_eq_norm_sq, norm_circleAt, one_pow]
    norm_num
  rw [(comparisonMap_eventuallyEq_core m hm s hnorm).fderiv_eq]
  exact surjective_fderiv_comparisonCore_of_standardCircle
    m hm s hs0 hs1 hcircle


-- @@ L928-931 verbatim
lemma reflectedTube_fiber_eq_standardCircle :
    (reflectedTubeFLS m hm).fiber = standardCircle := by
  rw [reflectedTubeFLS, FramedLevelSet.fiber_codomainEquiv,
    CompactTubeConfiguration.X_fiber]


-- @@ L933-954 verbatim
/-- Exact fixed-fiber homotopy from the reflected compact tube to the outgoing
presentation of the compact pair of pants. -/
def homotopy : DefiningMapHomotopy
    (reflectedTubeFLS m hm) (CompactHopfPairPants.targetFLS m hm) where
  H := comparisonMap m hm
  smooth := comparisonMap_smooth m hm
  H_zero := comparisonMap_zero m hm
  H_one := comparisonMap_one m hm
  fiber_eq := by
    intro s hs0 hs1
    ext x
    change comparisonMap m hm s x = 0 ↔ x ∈ (reflectedTubeFLS m hm).fiber
    rw [comparisonMap_eq_zero_iff_standardCircle m hm s hs0 hs1,
      reflectedTube_fiber_eq_standardCircle m hm]
  regular := by
    intro s hs0 hs1 x hx
    have hcircle : x ∈ standardCircle := by
      rw [← reflectedTube_fiber_eq_standardCircle m hm]
      exact hx
    have hzero :=
      (comparisonMap_eq_zero_iff_standardCircle m hm s hs0 hs1 x).mpr hcircle
    exact surjective_fderiv_comparisonMap_of_eq_zero m hm s hs0 hs1 hzero


-- @@ L956-956 verbatim
/-! ## Transport of the known singleton frame ledger -/


-- @@ L958-962 verbatim
lemma allPositive_selects_orbit {X : FramedLevelSet (m + 2)}
    (V : TamedField X) (O : V.OrbitIndex) :
    (O : Set E) ∈ (FiberSign.allPositive X).positiveOrbitCollection V := by
  rw [(FiberSign.allPositive X).mem_positiveOrbitCollection_iff V O]
  simp


-- @@ L964-973 verbatim
lemma tube_allPositive_ledger :
    (FiberSign.allPositive (CompactTubeConfiguration.X m)).positiveFrameLedger
      (CompactTubeConfiguration.field m) = [(1 : ZMod 2)] := by
  have hsign := FiberSign.positiveFrameLedger_eq_allPositive_of_pos
    (CompactTubeConfiguration.positiveSign m)
    (CompactTubeConfiguration.field m) (by
      intro x hx
      simp [CompactTubeConfiguration.positiveSign])
  rw [← hsign]
  exact CompactTubeConfiguration.positiveFrameLedger_eq_single_one m


-- @@ L975-1010 verbatim
theorem reflectedTube_positiveFrameLedger_eq_single_one :
    (FiberSign.allPositive (reflectedTubeFLS m hm)).positiveFrameLedger
      (reflectedTubeField m hm) = [(1 : ZMod 2)] := by
  let V := CompactTubeConfiguration.field m
  let W := reflectedTubeField m hm
  let T := V.coordinateReflectionDeltaTransport (reflectionIndex m hm)
  let Tselected : V.SelectedDeltaTransport W
      ((FiberSign.allPositive (CompactTubeConfiguration.X m)).positiveOrbitCollection V)
      ((FiberSign.allPositive (reflectedTubeFLS m hm)).positiveOrbitCollection W) :=
    TamedField.SelectedDeltaTransport.ofDeltaTransport T (by
      intro O
      constructor <;> intro _
      · exact allPositive_selects_orbit m W (T.orbitEquiv O)
      · exact allPositive_selects_orbit m V O)
  have hp := TamedField.SelectedDeltaTransport.selectedFrameLedger_perm V W Tselected
  have hsource := tube_allPositive_ledger m
  change ((FiberSign.allPositive
      (CompactTubeConfiguration.X m)).positiveFrameLedger V).Perm
    ((FiberSign.allPositive
      (reflectedTubeFLS m hm)).positiveFrameLedger W) at hp
  dsimp [V, W] at hp
  rw [hsource] at hp
  have hcount := hp.length_eq
  have hall : ∀ z ∈
      (FiberSign.allPositive (reflectedTubeFLS m hm)).positiveFrameLedger W,
      z = (1 : ZMod 2) := by
    intro z hz
    have hzsrc : z ∈ [(1 : ZMod 2)] := hp.mem_iff.mpr hz
    simpa using hzsrc
  calc
    (FiberSign.allPositive (reflectedTubeFLS m hm)).positiveFrameLedger W =
        List.replicate
          ((FiberSign.allPositive
            (reflectedTubeFLS m hm)).positiveFrameLedger W).length 1 :=
      List.eq_replicate_length.mpr hall
    _ = [(1 : ZMod 2)] := by rw [← hcount]; rfl


-- @@ L1012-1013 verbatim
def reflectedTubeSign : FiberSign (reflectedTubeFLS m hm) :=
  FiberSign.allPositive (reflectedTubeFLS m hm)


-- @@ L1015-1016 verbatim
def pantsTargetSign : FiberSign (CompactHopfPairPants.targetFLS m hm) :=
  FiberSign.allPositive (CompactHopfPairPants.targetFLS m hm)


-- @@ L1018-1023 verbatim
def endpointConnector : SignedFramedLevelCobordism
    (reflectedTubeSign m hm) (pantsTargetSign m hm) :=
  signedEndpointConnectorOfDefiningMapHomotopy (homotopy m hm)
    (reflectedTubeSign m hm) (pantsTargetSign m hm) (by
      intro x hx
      simp [reflectedTubeSign, pantsTargetSign, FiberSign.restrict])


-- @@ L1025-1030 verbatim
theorem endpointConnector_regularSlab :
    regularSlab (endpointConnector m hm).cobordism.G 0 1 := by
  exact signedEndpointConnectorOfDefiningMapHomotopy_regularSlab
    (homotopy m hm) (reflectedTubeSign m hm) (pantsTargetSign m hm) (by
      intro x hx
      simp [reflectedTubeSign, pantsTargetSign, FiberSign.restrict])


-- @@ L1032-1033 verbatim
def targetField : TamedField (CompactHopfPairPants.targetFLS m hm) :=
  (CompactHopfPairPants.targetFLS m hm).exists_tamedField.some


-- @@ L1035-1041 verbatim
theorem target_positiveFrameLedger_eq_single_one :
    (FiberSign.allPositive
      (CompactHopfPairPants.targetFLS m hm)).positiveFrameLedger
        (targetField m hm) = [(1 : ZMod 2)] := by
  exact (endpointConnector m hm).target_positiveFrameLedger_eq_single_one_of_regularSlab
    (endpointConnector_regularSlab m hm) (reflectedTubeField m hm)
      (targetField m hm) (reflectedTube_positiveFrameLedger_eq_single_one m hm)


-- @@ L1043-1043 verbatim
/-! ## Source ledger and common-background packaging -/


-- @@ L1045-1046 verbatim
def sourceField : TamedField (CompactHopfPairPants.sourceFLS m hm) :=
  (CompactHopfPairPants.sourceFLS m hm).exists_tamedField.some


-- @@ L1048-1056 verbatim
theorem source_positiveFrameLedger_eq_pair_zero :
    (FiberSign.allPositive
      (CompactHopfPairPants.sourceFLS m hm)).positiveFrameLedger
        (sourceField m hm) = [(0 : ZMod 2), 0] := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  subst m
  simpa [CompactHopfPairPants.sourceFLS] using
    (CompactHopfPairConfiguration.positiveFrameLedger_eq_pair_zero
      k (sourceField (k + 1) hm))


-- @@ L1058-1077 verbatim
theorem allPositive_backgroundTransport_ledger_perm
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    ((FiberSign.allPositive X).positiveFrameLedger V).Perm
      ((FiberSign.allPositive
          (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
        (V.backgroundTransport c₁ c₂ h₁ h₂)) := by
  let W := V.backgroundTransport c₁ c₂ h₁ h₂
  let T := V.backgroundDeltaTransport c₁ c₂ h₁ h₂
  let Tselected : V.SelectedDeltaTransport W
      ((FiberSign.allPositive X).positiveOrbitCollection V)
      ((FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveOrbitCollection W) :=
    TamedField.SelectedDeltaTransport.ofDeltaTransport T (by
      intro O
      constructor <;> intro _
      · exact allPositive_selects_orbit m W (T.orbitEquiv O)
      · exact allPositive_selects_orbit m V O)
  exact TamedField.SelectedDeltaTransport.selectedFrameLedger_perm V W Tselected


-- @@ L1079-1107 verbatim
theorem backgroundTransport_ledger_eq_pair_zero
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hledger : (FiberSign.allPositive X).positiveFrameLedger V =
      [(0 : ZMod 2), 0]) :
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
      (V.backgroundTransport c₁ c₂ h₁ h₂) = [(0 : ZMod 2), 0] := by
  have hp := allPositive_backgroundTransport_ledger_perm m V c₁ c₂ h₁ h₂
  rw [hledger] at hp
  have hcount := hp.length_eq
  have hall : ∀ z ∈
      (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂), z = (0 : ZMod 2) := by
    intro z hz
    have hzsrc : z ∈ [(0 : ZMod 2), 0] := hp.mem_iff.mpr hz
    simpa using hzsrc
  calc
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂) =
        List.replicate
          ((FiberSign.allPositive
            (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
              (V.backgroundTransport c₁ c₂ h₁ h₂)).length 0 :=
      List.eq_replicate_length.mpr hall
    _ = [(0 : ZMod 2), 0] := by rw [← hcount]; rfl


-- @@ L1109-1137 verbatim
theorem backgroundTransport_ledger_eq_single_one
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hledger : (FiberSign.allPositive X).positiveFrameLedger V =
      [(1 : ZMod 2)]) :
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
      (V.backgroundTransport c₁ c₂ h₁ h₂) = [(1 : ZMod 2)] := by
  have hp := allPositive_backgroundTransport_ledger_perm m V c₁ c₂ h₁ h₂
  rw [hledger] at hp
  have hcount := hp.length_eq
  have hall : ∀ z ∈
      (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂), z = (1 : ZMod 2) := by
    intro z hz
    have hzsrc : z ∈ [(1 : ZMod 2)] := hp.mem_iff.mpr hz
    simpa using hzsrc
  calc
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂) =
        List.replicate
          ((FiberSign.allPositive
            (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
              (V.backgroundTransport c₁ c₂ h₁ h₂)).length 1 :=
      List.eq_replicate_length.mpr hall
    _ = [(1 : ZMod 2)] := by rw [← hcount]; rfl


-- @@ L1139-1146 verbatim
theorem pants_spatialFlatOutside :
    (CompactHopfPairPants.cobordism m hm).SpatialFlatOutside
      (CompactHopfPairConfiguration.background m hm) 0 2 := by
  intro v hv
  change CompactHopfPairPants.eventMap m hm v =
    CompactHopfPairConfiguration.background m hm
  apply CompactHopfPairPants.eventMap_flatOutside m hm
  simpa [dist_zero_right] using hv


-- @@ L1148-1177 verbatim
/-- The compact Hopf pair of pants, postcomposed so that its value at spatial
infinity is the common compact-birth background used by the finite reducer. -/
def unsignedZeroPairSaddleCore :
    ConcreteConfigurationMorseReduction.UnsignedZeroPairSaddleCore m := by
  let c₁ : EuclideanSpace ℝ (Fin (m + 2)) :=
    CompactHopfPairConfiguration.background m hm
  let c₂ : EuclideanSpace ℝ (Fin (m + 2)) :=
    ConcreteConfigurationMorseReduction.compactBackground m
  have hc₁ : c₁ ≠ 0 := CompactHopfPairConfiguration.background_ne_zero m hm
  have hc₂ : c₂ ≠ 0 := CompactBirth.background_ne_zero (m + 1)
  let e := backgroundEquiv c₁ c₂ hc₁ hc₂
  refine {
    cobordism := (CompactHopfPairPants.cobordism m hm).codomainEquiv e
    sourceField := (sourceField m hm).backgroundTransport c₁ c₂ hc₁ hc₂
    targetField := (targetField m hm).backgroundTransport c₁ c₂ hc₁ hc₂
    sourceLedger := ?_
    targetLedger := ?_
    center := 0
    radius := 2
    radius_nonneg := by norm_num
    flatOutside := ?_ }
  · exact backgroundTransport_ledger_eq_pair_zero m (sourceField m hm)
      c₁ c₂ hc₁ hc₂ (source_positiveFrameLedger_eq_pair_zero m hm)
  · exact backgroundTransport_ledger_eq_single_one m (targetField m hm)
      c₁ c₂ hc₁ hc₂ (target_positiveFrameLedger_eq_single_one m hm)
  · have hflat' := FramedLevelCobordism.SpatialFlatOutside.codomainEquiv
      (pants_spatialFlatOutside m hm) e
    have hec : e c₁ = c₂ := backgroundEquiv_apply c₁ c₂ hc₁ hc₂
    rw [hec] at hflat'
    exact hflat'


-- @@ L1179-1183 verbatim
/-- Direct concrete consumer required by the deterministic finite Morse
reducer. -/
def zeroPairSaddleModel :
    ConcreteConfigurationMorseReduction.ZeroPairSaddleModel m :=
  (unsignedZeroPairSaddleCore m hm).toZeroPairSaddleModel


-- @@ L1185-1187 verbatim
theorem nonempty_zeroPairSaddleModel (hm' : 0 < m) :
    Nonempty (ConcreteConfigurationMorseReduction.ZeroPairSaddleModel m) :=
  ⟨zeroPairSaddleModel m hm'⟩


-- @@ L1189-1189 verbatim
end CompactHopfPairPantsFrameLedger

-- @@ L1190-1190 verbatim
end Submission
