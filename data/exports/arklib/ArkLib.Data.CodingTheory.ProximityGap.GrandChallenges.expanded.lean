/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.Errors
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ListDecodability


-- @@ L12-27 verbatim
/-!
# Proximity grand challenges

This file expresses the mutual-correlated-agreement and list-decoding challenges as boundary
problems on the integer agreement grid. A boundary answer is safe at `k / n` and unsafe at
`(k + 1) / n`; an endpoint answer certifies safety at every grid point through radius one.

The mutual-correlated-agreement challenge uses `CoreDefinitions.mcaError` with
`AffineLineGenerator F`. The prize specializations use Reed--Solomon codes at the exact rates
`1/2`, `1/4`, `1/8`, and `1/16`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace ProximityGap


-- @@ L33-33 verbatim
open scoped NNReal

-- @@ L34-34 verbatim
open CoreDefinitions


-- @@ L36-36 verbatim
/-! ## The integer-agreement grid -/


-- @@ L38-40 verbatim
/-- Grid point `k / n` in `ℝ≥0`, where `n := |ι|`. -/
noncomputable def gridPt {ι : Type} [Fintype ι] (k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (Fintype.card ι : ℝ≥0)


-- @@ L42-47 verbatim
/-- `k ≤ n` puts the grid point in the closed unit interval. -/
theorem gridPt_le_one {ι : Type} [Fintype ι] [Nonempty ι] {k : ℕ}
    (hk : k ≤ Fintype.card ι) : gridPt (ι := ι) k ≤ 1 := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  rw [gridPt, div_le_one hn]
  exact_mod_cast hk


-- @@ L49-53 verbatim
/-- Monotonicity of the agreement grid. -/
theorem gridPt_mono {ι : Type} [Fintype ι] {k k' : ℕ} (h : k ≤ k') :
    gridPt (ι := ι) k ≤ gridPt (ι := ι) k' := by
  unfold gridPt
  gcongr


-- @@ L55-59 verbatim
/-- Cancelling the positive grid denominator in `ℝ≥0`. -/
theorem gridPt_mul_card {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) :
    gridPt (ι := ι) k * (Fintype.card ι : ℝ≥0) = (k : ℝ≥0) := by
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [gridPt, div_mul_cancel₀ _ hn]


-- @@ L61-64 verbatim
/-- Real-valued version of `gridPt_mul_card`. -/
theorem gridPt_coe_mul_card {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) :
    (gridPt (ι := ι) k : ℝ) * (Fintype.card ι : ℝ) = (k : ℝ) := by
  exact_mod_cast gridPt_mul_card (ι := ι) k


-- @@ L66-71 verbatim
/-- Affine-line MCA is monotone along the integer-agreement grid. -/
theorem mcaError_gridPt_mono {F ι : Type} [Field F] [Fintype F]
    [Fintype ι] [Nonempty ι] (C : LinearCode ι F) {k k' : ℕ} (h : k ≤ k') :
    mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k' : ℝ) :=
  mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast gridPt_mono h)


-- @@ L73-73 verbatim
/-! ## Logical challenge predicates -/


-- @@ L75-84 verbatim
/-- An adjacent affine-line MCA crossing, or safety at every grid point through radius one. -/
def grandMcaChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  (∃ k : ℕ, k < Fintype.card ι ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal) ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (k + 1) : ℝ) >
        (ε_star : ENNReal)) ∨
    ∀ k : ℕ, k ≤ Fintype.card ι →
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal)


-- @@ L86-97 verbatim
/-- An adjacent list-size crossing, or safety at every grid point through radius one. -/
def grandListDecodingChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  (∃ k : ℕ, k < Fintype.card ι ∧
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal) ∧
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) (k + 1) : ℝ) : ENNReal) >
        (ε_star : ENNReal) * (Fintype.card F : ENNReal)) ∨
    ∀ k : ℕ, k ≤ Fintype.card ι →
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal)


-- @@ L99-99 verbatim
/-! ## Prize constants and smooth Reed--Solomon specializations -/


-- @@ L101-102 verbatim
/-- The `j`th prize rate, one of `1/2`, `1/4`, `1/8`, and `1/16`. -/
def prizeRate (j : Fin 4) : ℚ≥0 := 1 / 2 ^ (j.val + 1)


-- @@ L104-105 verbatim
/-- The prize error threshold `2⁻¹²⁸`. -/
def prizeThreshold : ℚ≥0 := 1 / 2 ^ (128 : ℕ)


-- @@ L107-108 verbatim
/-- Denominator of the `j`th prize rate. -/
def prizeDenominator (j : Fin 4) : ℕ := 2 ^ (j.val + 1)


-- @@ L110-112 verbatim
/-- Exact message length for the `j`th prize rate. -/
def prizeDimension {ι : Type} [Fintype ι] (j : Fin 4) : ℕ :=
  Fintype.card ι / prizeDenominator j


-- @@ L114-117 verbatim
/-- Domain-size conditions under which all four prize rates are exact. -/
structure PrizeDomainAdmissible (ι : Type) [Fintype ι] : Prop where
  /-- Every prize denominator through `16` fits in the evaluation domain. -/
  card_ge : 16 ≤ Fintype.card ι
  
-- @@ L118-119 verbatim
/-- Every prize denominator divides the evaluation-domain size. -/
  denominator_dvd : ∀ j : Fin 4, prizeDenominator j ∣ Fintype.card ι


-- @@ L121-121 verbatim
namespace GrandChallenges


-- @@ L123-124 verbatim
variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]


-- @@ L126-138 verbatim
omit [Fintype F] [Nonempty ι] in
/-- A smooth evaluation domain of length at least `16` is prize-domain admissible. -/
theorem PrizeDomainAdmissible.of_smooth (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (hcard : 16 ≤ Fintype.card ι) : PrizeDomainAdmissible ι := by
  refine ⟨hcard, fun j => ?_⟩
  obtain ⟨k, hk⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := domain)
  rw [hk]
  apply Nat.pow_dvd_pow
  have hj : j.val + 1 ≤ 4 := by omega
  have hk4 : 4 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
    simpa [hk] using hcard
  exact hj.trans hk4


-- @@ L140-143 verbatim
/-- The affine-line MCA challenge for a Reed--Solomon code over a smooth domain. -/
def grandMcaChallengeRs (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandMcaChallenge (ReedSolomon.code domain k) ε_star


-- @@ L145-148 verbatim
/-- The list-decoding challenge for a Reed--Solomon code over a smooth domain. -/
def grandListDecodingChallengeRs (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k m : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star


-- @@ L150-165 verbatim
omit [Fintype F] [DecidableEq F] [Nonempty ι] in
/-- The code selected by `prizeDimension` has exactly the advertised prize rate. -/
theorem prizeCode_rate_eq (domain : ι ↪ F) (h : PrizeDomainAdmissible ι) (j : Fin 4) :
    LinearCode.rate (ReedSolomon.code domain (prizeDimension (ι := ι) j)) = prizeRate j := by
  unfold prizeDimension
  rw [ReedSolomon.rateOfLinearCode_eq_div (Nat.div_le_self _ _)]
  unfold prizeRate
  have hdpos : 0 < prizeDenominator j := by
    simp [prizeDenominator]
  rw [Nat.cast_div (h.denominator_dvd j) (by exact_mod_cast hdpos.ne')]
  unfold prizeDenominator
  have hn : (Fintype.card ι : ℚ≥0) ≠ 0 := by
    have hcard := h.card_ge
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  field_simp [hn]
  norm_cast


-- @@ L167-170 verbatim
/-- The affine-line MCA challenge at every prize rate. -/
def mcaPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Prop :=
  PrizeDomainAdmissible ι ∧ ∀ j : Fin 4,
    grandMcaChallengeRs domain (prizeDimension (ι := ι) j) (prizeThreshold : ℝ≥0)


-- @@ L172-176 verbatim
/-- The list-decoding challenge at every prize rate for a nonempty interleaving width. -/
def listDecodingPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] (m : ℕ) : Prop :=
  0 < m ∧ PrizeDomainAdmissible ι ∧ ∀ j : Fin 4,
    grandListDecodingChallengeRs domain
      (prizeDimension (ι := ι) j) m (prizeThreshold : ℝ≥0)


-- @@ L178-178 verbatim
/-! ## Mutual correlated agreement boundary data -/


-- @@ L180-181 verbatim
/-- An adjacent affine-line MCA boundary. -/
structure GrandMcaResolution (C : LinearCode ι F) (ε_star : ℝ≥0) where
  
-- @@ L182-183 verbatim
/-- Boundary grid index. -/
  kStar : ℕ
  
-- @@ L184-185 verbatim
/-- Both adjacent grid points lie in `[0,1]`. -/
  lt_card : kStar < Fintype.card ι
  
-- @@ L186-188 verbatim
/-- The error bound is safe at `kStar / n`. -/
  below : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) kStar : ℝ) ≤
    (ε_star : ENNReal)
  
-- @@ L189-191 verbatim
/-- The error bound is unsafe at `(kStar + 1) / n`. -/
  above : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (kStar + 1) : ℝ) >
    (ε_star : ENNReal)


-- @@ L193-194 verbatim
/-- A radius where the affine-line MCA error is within the threshold. -/
structure McaLowerWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  
-- @@ L195-196 verbatim
/-- Certified radius. -/
  δ : ℝ≥0
  
-- @@ L197-198 verbatim
/-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  
-- @@ L199-200 verbatim
/-- The affine-line MCA error is within the threshold. -/
  bound : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)


-- @@ L202-203 verbatim
/-- A radius where the affine-line MCA error exceeds the threshold. -/
structure McaUpperWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  
-- @@ L204-205 verbatim
/-- Certified radius. -/
  δ : ℝ≥0
  
-- @@ L206-207 verbatim
/-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  
-- @@ L208-209 verbatim
/-- The affine-line MCA error exceeds the threshold. -/
  exceeds : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)


-- @@ L211-211 verbatim
namespace GrandMcaResolution


-- @@ L213-213 verbatim
variable {C : LinearCode ι F} {ε_star : ℝ≥0}


-- @@ L215-220 verbatim
omit [DecidableEq F] [Nonempty ι] in
/-- Below the safe grid point, the MCA bound remains safe. -/
theorem le_of_gridPt (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) :=
  le_trans (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ)) R.below


-- @@ L222-228 verbatim
omit [DecidableEq F] [Nonempty ι] in
/-- At or above the adjacent unsafe point, the MCA bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal) :=
  lt_of_lt_of_le R.above
    (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ))


-- @@ L230-250 verbatim
omit [DecidableEq F] in
/-- Exact safe half of the boundary cell. -/
theorem le_of_lt_next (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ < gridPt (ι := ι) (R.kStar + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hfloor : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ ≤ R.kStar := by
    have hltNN : δ * (Fintype.card ι : ℝ≥0) < ((R.kStar + 1 : ℕ) : ℝ≥0) := by
      have h := hδ
      rw [gridPt, lt_div_iff₀ hn] at h
      exact_mod_cast h
    have hlt : (δ : ℝ) * (Fintype.card ι : ℝ) < (R.kStar + 1 : ℕ) := by
      exact_mod_cast hltNN
    have := (Nat.floor_lt (by positivity)).mpr hlt
    omega
  let j := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊
  have hgrid : ⌊(gridPt (ι := ι) j : ℝ) * (Fintype.card ι : ℝ)⌋₊ = j := by
    rw [gridPt_coe_mul_card]
    exact Nat.floor_natCast _
  rw [mcaError_eq_of_floor_eq (AffineLineGenerator F) C (by positivity) (by positivity) hgrid.symm]
  exact le_trans (mcaError_gridPt_mono C hfloor) R.below


-- @@ L252-260 verbatim
omit [DecidableEq F] in
/-- The MCA sublevel set is exactly the right-open interval ending at the unsafe grid point. -/
theorem sublevel_iff (R : GrandMcaResolution C ε_star) {δ : ℝ≥0} :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) ↔
      δ < gridPt (ι := ι) (R.kStar + 1) := by
  refine ⟨fun hle => ?_, R.le_of_lt_next⟩
  by_contra hge
  push Not at hge
  exact absurd hle (not_le.mpr (R.gt_of_gridPt hge))


-- @@ L262-272 verbatim
omit [DecidableEq F] in
/-- The adjacent-grid MCA boundary index is unique. -/
theorem kStar_unique (R R' : GrandMcaResolution C ε_star) : R.kStar = R'.kStar := by
  rcases lt_trichotomy R.kStar R'.kStar with h | h | h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R.kStar + 1 ≤ R'.kStar)) R'.below)
      (not_le.mpr R.above)
  · exact h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R'.kStar + 1 ≤ R.kStar)) R.below)
      (not_le.mpr R'.above)


-- @@ L274-277 verbatim
/-- A resolution supplies a safe one-sided witness. -/
noncomputable def toLowerWitness (R : GrandMcaResolution C ε_star) :
    McaLowerWitness C ε_star :=
  ⟨gridPt (ι := ι) R.kStar, gridPt_le_one (le_of_lt R.lt_card), R.below⟩


-- @@ L279-282 verbatim
/-- A resolution supplies an unsafe one-sided witness. -/
noncomputable def toUpperWitness (R : GrandMcaResolution C ε_star) :
    McaUpperWitness C ε_star :=
  ⟨gridPt (ι := ι) (R.kStar + 1), gridPt_le_one (Nat.succ_le_iff.mpr R.lt_card), R.above⟩


-- @@ L284-284 verbatim
end GrandMcaResolution


-- @@ L286-289 verbatim
/-- An adjacent affine-line MCA boundary satisfies the logical challenge. -/
theorem GrandMcaResolution.to_challenge {C : LinearCode ι F} {ε_star : ℝ≥0}
    (R : GrandMcaResolution C ε_star) : grandMcaChallenge C ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩


-- @@ L291-292 verbatim
/-- An affine-line MCA answer: either an adjacent boundary or an endpoint certificate. -/
inductive GrandMcaAnswer (C : LinearCode ι F) (ε_star : ℝ≥0) : Type where
  
-- @@ L293-294 verbatim
/-- An adjacent-boundary answer. -/
  | boundary (R : GrandMcaResolution C ε_star)
  
-- @@ L295-299 verbatim
/-- Safety at every grid point through radius one. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
          (ε_star : ENNReal))


-- @@ L301-306 verbatim
/-- An affine-line MCA answer satisfies the logical challenge. -/
theorem GrandMcaAnswer.to_challenge {C : LinearCode ι F} {ε_star : ℝ≥0}
    (A : GrandMcaAnswer C ε_star) : grandMcaChallenge C ε_star := by
  cases A with
  | boundary R => exact R.to_challenge
  | allGood h => exact Or.inr h


-- @@ L308-309 verbatim
/-- An affine-line MCA answer at each prize rate. -/
structure McaPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Type where
  
-- @@ L310-311 verbatim
/-- The evaluation domain realizes all four prize rates exactly. -/
  admissible : PrizeDomainAdmissible ι
  
-- @@ L312-316 verbatim
/-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandMcaAnswer
      (ReedSolomon.code domain (prizeDimension (ι := ι) j))
      (prizeThreshold : ℝ≥0)


-- @@ L318-321 verbatim
/-- Per-rate affine-line MCA answers satisfy the prize proposition. -/
theorem McaPrizeResolution.to_prize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    (R : McaPrizeResolution domain) : mcaPrize domain :=
  ⟨R.admissible, fun j => (R.answer j).to_challenge⟩


-- @@ L323-330 verbatim
omit [DecidableEq F] [Nonempty ι] in
/-- A safe witness lies strictly below the unsafe edge of every resolution. -/
theorem McaLowerWitness.lt_boundary {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : McaLowerWitness C ε_star) (R : GrandMcaResolution C ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))


-- @@ L332-339 verbatim
omit [DecidableEq F] [Nonempty ι] in
/-- An unsafe witness lies strictly above the safe edge of every resolution. -/
theorem McaUpperWitness.boundary_lt {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : McaUpperWitness C ε_star) (R : GrandMcaResolution C ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)


-- @@ L341-345 verbatim
/-- An affine-line MCA upper bound at a unit-interval radius gives a safe witness. -/
def McaLowerWitness.ofLe {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)) :
    McaLowerWitness C ε_star := ⟨δ, hδ, h⟩


-- @@ L347-350 verbatim
/-- An affine-line MCA lower bound at a unit-interval radius gives an unsafe witness. -/
def McaUpperWitness.ofGt {C : LinearCode ι F} {ε_star δ : ℝ≥0} (hδ : δ ≤ 1)
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)) :
    McaUpperWitness C ε_star := ⟨δ, hδ, h⟩


-- @@ L352-358 verbatim
open Classical in
/-- A correlated-agreement lower bound at a unit-interval radius gives an unsafe MCA witness. -/
def McaUpperWitness.ofEpsCaGt {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ > (ε_star : ENNReal)) :
    McaUpperWitness C ε_star :=
  ⟨δ, hδ, lt_of_lt_of_le h (epsCa_le_mcaError_affineLine C δ)⟩


-- @@ L360-360 verbatim
/-! ## List-decoding boundary carriers -/


-- @@ L362-363 verbatim
/-- A full list-decoding resolution on adjacent grid points. -/
structure GrandListResolution (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  
-- @@ L364-365 verbatim
/-- Boundary grid index. -/
  kStar : ℕ
  
-- @@ L366-367 verbatim
/-- Both adjacent grid points lie in `[0,1]`. -/
  lt_card : kStar < Fintype.card ι
  
-- @@ L368-370 verbatim
/-- The list-size bound is safe at `kStar / n`. -/
  below : (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) kStar : ℝ) : ENNReal) ≤
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
  
-- @@ L371-373 verbatim
/-- The list-size bound is unsafe at `(kStar + 1) / n`. -/
  above : (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) (kStar + 1) : ℝ) : ENNReal) >
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)


-- @@ L375-376 verbatim
/-- One-sided safe list-size witness. -/
structure ListLowerWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  
-- @@ L377-378 verbatim
/-- Certified radius. -/
  δ : ℝ≥0
  
-- @@ L379-380 verbatim
/-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  
-- @@ L381-383 verbatim
/-- The list-size bound is safe. -/
  bound : (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)


-- @@ L385-386 verbatim
/-- One-sided unsafe list-size witness. -/
structure ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  
-- @@ L387-388 verbatim
/-- Certified radius. -/
  δ : ℝ≥0
  
-- @@ L389-390 verbatim
/-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  
-- @@ L391-393 verbatim
/-- The list-size bound is unsafe. -/
  exceeds : (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)


-- @@ L395-401 verbatim
omit [Field F] [Fintype F] [DecidableEq F] [Nonempty ι] in
/-- The maximized list size is monotone on nonnegative radii. -/
theorem lambda_mono_nnreal {C : Set (ι → F)} {m : ℕ} {a b : ℝ≥0} (hab : a ≤ b) :
    (Code.Lambda (C ^⋈ (Fin m)) (a : ℝ) : ENNReal) ≤
      (Code.Lambda (C ^⋈ (Fin m)) (b : ℝ) : ENNReal) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact_mod_cast Code.Lambda_mono (C := C ^⋈ (Fin m)) hr


-- @@ L403-430 verbatim
/-- `Lambda` is constant on equal integer-agreement floor cells of nonnegative radii. -/
theorem lambda_eq_of_floor_eq {B : Type}
    {C : Set (ι → B)} {δ δ' : ℝ≥0}
    (h : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ =
      ⌊δ' * (Fintype.card ι : ℝ≥0)⌋₊) :
    Code.Lambda C (δ : ℝ) = Code.Lambda C (δ' : ℝ) := by
  classical
  unfold Code.Lambda
  apply iSup_congr
  intro y
  congr 1
  ext c
  rw [Code.mem_closeCodewordsRel_iff, Code.mem_closeCodewordsRel_iff]
  apply and_congr_right
  intro _
  constructor
  · intro hd
    have hdnn : δᵣ(y, c) ≤ δ := by exact_mod_cast hd
    rw [Code.pairRelDist_le_iff_pairDist_le] at hdnn
    rw [h] at hdnn
    rw [← Code.pairRelDist_le_iff_pairDist_le] at hdnn
    exact_mod_cast hdnn
  · intro hd
    have hdnn : δᵣ(y, c) ≤ δ' := by exact_mod_cast hd
    rw [Code.pairRelDist_le_iff_pairDist_le] at hdnn
    rw [← h] at hdnn
    rw [← Code.pairRelDist_le_iff_pairDist_le] at hdnn
    exact_mod_cast hdnn


-- @@ L432-432 verbatim
namespace GrandListResolution


-- @@ L434-434 verbatim
variable {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}


-- @@ L436-442 verbatim
omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- Below the safe list grid point, the bound remains safe. -/
theorem le_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  le_trans (lambda_mono_nnreal hδ) R.below


-- @@ L444-450 verbatim
omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- At or above the adjacent unsafe list grid point, the bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  lt_of_lt_of_le R.above (lambda_mono_nnreal hδ)


-- @@ L452-471 verbatim
omit [Field F] [DecidableEq F] in
/-- Exact safe half of the list-decoding boundary cell. -/
theorem le_of_lt_next (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ < gridPt (ι := ι) (R.kStar + 1)) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hfloor : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ≤ R.kStar := by
    have hlt : δ * (Fintype.card ι : ℝ≥0) < ((R.kStar + 1 : ℕ) : ℝ≥0) := by
      have h := hδ
      rw [gridPt, lt_div_iff₀ hn] at h
      exact h
    have := (Nat.floor_lt (by positivity)).mpr hlt
    omega
  let j := ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊
  have hgrid : ⌊gridPt (ι := ι) j * (Fintype.card ι : ℝ≥0)⌋₊ = j := by
    rw [gridPt_mul_card]
    exact Nat.floor_natCast _
  rw [lambda_eq_of_floor_eq (C := C ^⋈ (Fin m)) hgrid.symm]
  exact le_trans (lambda_mono_nnreal (gridPt_mono hfloor)) R.below


-- @@ L473-483 verbatim
omit [Field F] [DecidableEq F] in
/-- The list-decoding sublevel set is exactly the right-open interval ending at the unsafe grid
point. -/
theorem sublevel_iff (R : GrandListResolution C m ε_star) {δ : ℝ≥0} :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal) ↔
      δ < gridPt (ι := ι) (R.kStar + 1) := by
  refine ⟨fun hle => ?_, R.le_of_lt_next⟩
  by_contra hge
  push Not at hge
  exact absurd hle (not_le.mpr (R.gt_of_gridPt hge))


-- @@ L485-495 verbatim
omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- The adjacent-grid list-decoding boundary index is unique. -/
theorem kStar_unique (R R' : GrandListResolution C m ε_star) : R.kStar = R'.kStar := by
  rcases lt_trichotomy R.kStar R'.kStar with h | h | h
  · exact absurd
      (le_trans (lambda_mono_nnreal (gridPt_mono (by omega : R.kStar + 1 ≤ R'.kStar))) R'.below)
      (not_le.mpr R.above)
  · exact h
  · exact absurd
      (le_trans (lambda_mono_nnreal (gridPt_mono (by omega : R'.kStar + 1 ≤ R.kStar))) R.below)
      (not_le.mpr R'.above)


-- @@ L497-497 verbatim
end GrandListResolution


-- @@ L499-503 verbatim
/-- An adjacent list-size boundary satisfies the logical challenge. -/
theorem GrandListResolution.to_challenge
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (R : GrandListResolution C m ε_star) : grandListDecodingChallenge C m ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩


-- @@ L505-506 verbatim
/-- A list-decoding answer: either an adjacent boundary or an endpoint certificate. -/
inductive GrandListAnswer (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Type where
  
-- @@ L507-508 verbatim
/-- An adjacent-boundary answer. -/
  | boundary (R : GrandListResolution C m ε_star)
  
-- @@ L509-513 verbatim
/-- Safety at every grid point through radius one. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
          (ε_star : ENNReal) * (Fintype.card F : ENNReal))


-- @@ L515-521 verbatim
/-- A list-decoding answer satisfies the logical challenge. -/
theorem GrandListAnswer.to_challenge
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (A : GrandListAnswer C m ε_star) : grandListDecodingChallenge C m ε_star := by
  cases A with
  | boundary R => exact R.to_challenge
  | allGood h => exact Or.inr h


-- @@ L523-525 verbatim
/-- A list-decoding answer at each prize rate. -/
structure ListPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (m : ℕ) : Type where
  
-- @@ L526-527 verbatim
/-- The interleaving width is nonempty. -/
  m_pos : 0 < m
  
-- @@ L528-529 verbatim
/-- The evaluation domain realizes all four prize rates exactly. -/
  admissible : PrizeDomainAdmissible ι
  
-- @@ L530-534 verbatim
/-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandListAnswer
      (ReedSolomon.code domain (prizeDimension (ι := ι) j) : Set (ι → F))
      m (prizeThreshold : ℝ≥0)


-- @@ L536-539 verbatim
/-- Per-rate list-decoding answers satisfy the prize proposition. -/
theorem ListPrizeResolution.to_prize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    {m : ℕ} (R : ListPrizeResolution domain m) : listDecodingPrize domain m :=
  ⟨R.m_pos, R.admissible, fun j => (R.answer j).to_challenge⟩


-- @@ L541-548 verbatim
omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- A safe list witness lies strictly below the unsafe edge of every resolution. -/
theorem ListLowerWitness.lt_boundary {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListLowerWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))


-- @@ L550-557 verbatim
omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- An unsafe list witness lies strictly above the safe edge of every resolution. -/
theorem ListUpperWitness.boundary_lt {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListUpperWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)


-- @@ L559-559 verbatim
end GrandChallenges


-- @@ L561-561 verbatim
end ProximityGap
