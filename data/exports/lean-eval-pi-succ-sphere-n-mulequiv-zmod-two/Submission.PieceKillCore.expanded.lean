import Mathlib
import Submission.PieceKillRotationKit


-- @@ L4-22 verbatim
/-!
# The tube-to-birth-circle comparison cobordism

For every sign parameter set (`Params`), this file constructs one explicit
signed framed level cobordism from a "tube-form" presentation — a compactified
round circle in the coordinate plane `(0, 1)` whose defining rows are a signed
cyclic arrangement of the transverse coordinates and half the radial
equation — to the compact birth circle `CompactBirth.targetFLS (m + 1)`, flat
outside the spatial ball of radius `5/2` with the common compact background
value.

The moving family is
`level s x = (1 - u x) • M_s (circleMap (ρ_s x)) + u x • background`,
where `ρ_s` is a smooth special-orthogonal path carrying the plane `(0, 1)`
to the last-coordinate plane, `M_s` is a smooth path of invertible codomain
matrices from the signed cyclic block (with radial coefficient `1/2`) to the
identity, and `u` is the common ambient cutoff.  The determinant bookkeeping
of the block is exactly the `hprod` field of `Params`.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
set_option maxHeartbeats 2400000


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace Submission

-- @@ L30-30 verbatim
namespace PieceKill


-- @@ L32-32 verbatim
open Set Function Metric Matrix

-- @@ L33-33 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L35-35 verbatim
variable (m : ℕ)


-- @@ L37-37 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L38-38 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L40-40 verbatim
/-! ## Distinguished ambient indices -/


-- @@ L42-42 verbatim
def i0 : Fin (m + 3) := ⟨0, by omega⟩

-- @@ L43-43 verbatim
def i1 : Fin (m + 3) := ⟨1, by omega⟩

-- @@ L44-44 verbatim
def iA : Fin (m + 3) := ⟨m + 1, by omega⟩

-- @@ L45-45 verbatim
def iB : Fin (m + 3) := ⟨m + 2, by omega⟩


-- @@ L47-47 verbatim
@[simp] theorem i0_val : (i0 m).val = 0 := rfl

-- @@ L48-48 verbatim
@[simp] theorem i1_val : (i1 m).val = 1 := rfl

-- @@ L49-49 verbatim
@[simp] theorem iA_val : (iA m).val = m + 1 := rfl

-- @@ L50-50 verbatim
@[simp] theorem iB_val : (iB m).val = m + 2 := rfl


-- @@ L52-53 verbatim
theorem iA_ne_i0 : iA m ≠ i0 m := by
  intro h; have := congrArg Fin.val h; simp at this

-- @@ L54-55 verbatim
theorem iB_ne_i1 : iB m ≠ i1 m := by
  intro h; have := congrArg Fin.val h; simp at this

-- @@ L56-56 verbatim
theorem i1_ne_iB : i1 m ≠ iB m := (iB_ne_i1 m).symm

-- @@ L57-58 verbatim
theorem i0_ne_i1 : i0 m ≠ i1 m := by
  intro h; have := congrArg Fin.val h; simp at this

-- @@ L59-60 verbatim
theorem iA_ne_iB : iA m ≠ iB m := by
  intro h; have := congrArg Fin.val h; simp at this

-- @@ L61-62 verbatim
theorem i0_ne_iB : i0 m ≠ iB m := by
  intro h; have := congrArg Fin.val h; simp at this


-- @@ L64-64 verbatim
/-! ## The parameter pack -/


-- @@ L66-74 verbatim
/-- Sign data of one tube-form comparison: transverse row signs `eta`, the
ambient direction sign `eps`, and the determinant identity making the
transverse block special orthogonal. -/
structure Params where
  eta : Fin (m + 1) → ℝ
  eps : ℝ
  heta : ∀ j, eta j = 1 ∨ eta j = -1
  heps : eps = 1 ∨ eps = -1
  hprod : eps * ∏ j, eta j = (-1) ^ m


-- @@ L76-76 verbatim
variable {m}


-- @@ L78-79 verbatim
theorem Params.eps_sq (P : Params m) : P.eps * P.eps = 1 := by
  rcases P.heps with h | h <;> rw [h] <;> norm_num


-- @@ L81-81 verbatim
variable (m)


-- @@ L83-85 verbatim
/-- The transverse block of a parameter pack. -/
def Params.block (P : Params m) : SOGroup (m + 1) :=
  blockSO m P.eta P.eps P.heta P.heps P.hprod


-- @@ L87-90 verbatim
/-- A chosen smooth special-orthogonal path from the identity to the
transverse block. -/
def pathT (P : Params m) : SmoothSOPath (P.block m) :=
  (SmoothSOPath.nonempty (Nat.succ_pos m) (P.block m)).some


-- @@ L92-99 verbatim
open Classical in
/-- The ambient rotation: the product of the two canonical plane rotations
carrying the last-coordinate radial plane onto the plane `(0, 1)`, with the
second rotation run in the direction prescribed by `eps`. -/
def rotAmb (P : Params m) : SOGroup (m + 3) :=
  rotTo (uPt (iA m)) (uPt (i0 m)) *
    (if P.eps = 1 then rotTo (uPt (iB m)) (uPt (i1 m))
      else rotTo (uPt (i1 m)) (uPt (iB m)))


-- @@ L101-104 verbatim
/-- A chosen smooth special-orthogonal path from the identity to the ambient
rotation. -/
def pathA (P : Params m) : SmoothSOPath (rotAmb m P) :=
  (SmoothSOPath.nonempty (by omega) (rotAmb m P)).some


-- @@ L106-112 verbatim
/-- Pointwise form of `rotTo_uPt_mulVec`. -/
theorem rotTo_uPt_mulVec_apply {N : ℕ} {p q : Fin N} (hpq : p ≠ q)
    (w : Fin N → ℝ) (j : Fin N) :
    (((rotTo (uPt p) (uPt q) : SOGroup N) :
        Matrix (Fin N) (Fin N) ℝ) *ᵥ w) j =
      if j = p then -w q else if j = q then w p else w j := by
  rw [rotTo_uPt_mulVec hpq]


-- @@ L114-198 verbatim
/-- The action of the ambient rotation. -/
theorem rotAmb_mulVec_apply (P : Params m) (hm : 0 < m)
    (x : Fin (m + 3) → ℝ) (j : Fin (m + 3)) :
    (((rotAmb m P : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ x) j =
      if j = i0 m then x (iA m)
      else if j = i1 m then P.eps * x (iB m)
      else if j = iA m then -(x (i0 m))
      else if j = iB m then -(P.eps * x (i1 m))
      else x j := by
  classical
  have hA1 : iA m ≠ i1 m := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hA0 : iA m ≠ i0 m := iA_ne_i0 m
  have hAB : iA m ≠ iB m := iA_ne_iB m
  have h0B : i0 m ≠ iB m := i0_ne_iB m
  have h01 : i0 m ≠ i1 m := i0_ne_i1 m
  have hB1 : iB m ≠ i1 m := iB_ne_i1 m
  by_cases he : P.eps = 1
  · have hval : ((rotAmb m P : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ x =
        ((rotTo (uPt (iA m)) (uPt (i0 m)) : SOGroup (m + 3)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ
        (((rotTo (uPt (iB m)) (uPt (i1 m)) : SOGroup (m + 3)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ x) := by
      rw [rotAmb, if_pos he, Matrix.mulVec_mulVec]
      rfl
    rw [hval]
    rw [rotTo_uPt_mulVec_apply (iA_ne_i0 m)]
    rw [rotTo_uPt_mulVec_apply (iB_ne_i1 m),
      rotTo_uPt_mulVec_apply (iB_ne_i1 m),
      rotTo_uPt_mulVec_apply (iB_ne_i1 m)]
    simp only [if_neg (fun h : i0 m = iB m => h0B h),
      if_neg (fun h : i0 m = i1 m => h01 h),
      if_neg (fun h : iA m = iB m => hAB h),
      if_neg (fun h : iA m = i1 m => hA1 h)]
    -- now decide `j`
    by_cases hjA : j = iA m
    · have hn0 : ¬j = i0 m := by rw [hjA]; exact hA0
      have hn1 : ¬j = i1 m := by rw [hjA]; exact hA1
      simp only [if_pos hjA, if_neg hn0, if_neg hn1]
    · by_cases hj0 : j = i0 m
      · have hn1 : ¬j = i1 m := by rw [hj0]; exact h01
        simp only [if_neg hjA, if_pos hj0, if_neg hn1]
      · by_cases hjB : j = iB m
        · have hn1 : ¬j = i1 m := by rw [hjB]; exact hB1
          simp only [if_neg hjA, if_neg hj0, if_pos hjB, if_neg hn1, he,
            one_mul]
        · by_cases hj1 : j = i1 m
          · simp only [if_neg hjA, if_neg hj0, if_neg hjB, if_pos hj1, he,
              one_mul]
          · simp only [if_neg hjA, if_neg hj0, if_neg hjB, if_neg hj1]
  · have he' : P.eps = -1 := P.heps.resolve_left he
    have hval : ((rotAmb m P : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ x =
        ((rotTo (uPt (iA m)) (uPt (i0 m)) : SOGroup (m + 3)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ
        (((rotTo (uPt (i1 m)) (uPt (iB m)) : SOGroup (m + 3)) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ x) := by
      rw [rotAmb, if_neg he, Matrix.mulVec_mulVec]
      rfl
    rw [hval]
    rw [rotTo_uPt_mulVec_apply (iA_ne_i0 m)]
    rw [rotTo_uPt_mulVec_apply (i1_ne_iB m),
      rotTo_uPt_mulVec_apply (i1_ne_iB m),
      rotTo_uPt_mulVec_apply (i1_ne_iB m)]
    simp only [if_neg (fun h : i0 m = i1 m => h01 h),
      if_neg (fun h : i0 m = iB m => h0B h),
      if_neg (fun h : iA m = i1 m => hA1 h),
      if_neg (fun h : iA m = iB m => hAB h)]
    by_cases hjA : j = iA m
    · have hn0 : ¬j = i0 m := by rw [hjA]; exact hA0
      have hn1 : ¬j = i1 m := by rw [hjA]; exact hA1
      simp only [if_pos hjA, if_neg hn0, if_neg hn1]
    · by_cases hj0 : j = i0 m
      · have hn1 : ¬j = i1 m := by rw [hj0]; exact h01
        simp only [if_neg hjA, if_pos hj0, if_neg hn1]
      · by_cases hj1 : j = i1 m
        · have hnB : ¬j = iB m := by rw [hj1]; exact i1_ne_iB m
          simp only [if_neg hjA, if_neg hj0, if_pos hj1, if_neg hnB, he']
          ring
        · by_cases hjB : j = iB m
          · simp only [if_neg hjA, if_neg hj0, if_neg hj1, if_pos hjB, he']
            ring
          · simp only [if_neg hjA, if_neg hj0, if_neg hj1, if_neg hjB]


-- @@ L200-200 verbatim
/-! ## The moving spatial rotation and codomain matrix -/


-- @@ L202-205 verbatim
/-- The spatial rotation at time `s`: the chosen path run backwards, so that
time `0` is the full rotation and time `1` is the identity. -/
def rho (P : Params m) (s : ℝ) (x : E) : E :=
  SOFrameGauge.toCLM ((pathA m P).Q (1 - s)) x


-- @@ L207-210 verbatim
theorem rho_one (P : Params m) (x : E) : rho m P 1 x = x := by
  rw [rho, show (1 : ℝ) - 1 = 0 by norm_num, (pathA m P).zero,
    SOFrameGauge.toCLM_one]
  rfl


-- @@ L212-227 verbatim
theorem rho_zero_apply (P : Params m) (hm : 0 < m) (x : E) (j : Fin (m + 3)) :
    rho m P 0 x j =
      if j = i0 m then x (iA m)
      else if j = i1 m then P.eps * x (iB m)
      else if j = iA m then -(x (i0 m))
      else if j = iB m then -(P.eps * x (i1 m))
      else x j := by
  have h : rho m P 0 x = SOFrameGauge.toCLM (rotAmb m P) x := by
    rw [rho, show (1 : ℝ) - 0 = 1 by norm_num, (pathA m P).one]
  rw [h]
  have hc : SOFrameGauge.toCLM (rotAmb m P) x j =
      (((rotAmb m P : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *ᵥ WithLp.ofLp x) j := by
    rw [Matrix.mulVec]
    exact SOFrameGauge.toCLM_apply_coord _ _ _
  rw [hc, rotAmb_mulVec_apply m P hm]


-- @@ L229-231 verbatim
theorem normSq_rho (P : Params m) (s : ℝ) (x : E) :
    CompactBirth.normSq (rho m P s x) = CompactBirth.normSq x :=
  normSq_toCLM _ x


-- @@ L233-235 verbatim
/-- The transverse projection of a codomain vector. -/
def tp (w : F) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (fun j : Fin (m + 1) => w j.castSucc)


-- @@ L237-238 verbatim
@[simp] theorem tp_apply (w : F) (j : Fin (m + 1)) :
    tp m w j = w j.castSucc := rfl


-- @@ L240-243 verbatim
theorem tp_add (w w' : F) : tp m (w + w') = tp m w + tp m w' := by
  apply PiLp.ext
  intro j
  simp [tp, PiLp.add_apply]


-- @@ L245-248 verbatim
theorem tp_smul (c : ℝ) (w : F) : tp m (c • w) = c • tp m w := by
  apply PiLp.ext
  intro j
  simp [tp, PiLp.smul_apply]


-- @@ L250-251 verbatim
/-- The radial coefficient path, from `1/2` to `1`. -/
def lam (s : ℝ) : ℝ := (1 + s) / 2


-- @@ L253-254 verbatim
theorem lam_pos {s : ℝ} (hs : 0 ≤ s) : 0 < lam s := by
  rw [lam]; linarith


-- @@ L256-263 verbatim
/-- The codomain matrix action at time `s`: the transverse block path run
backwards on the transverse rows and the radial coefficient `lam s` on the
last row. -/
def mact (P : Params m) (s : ℝ) (w : F) : F :=
  WithLp.toLp 2 (Fin.lastCases (motive := fun _ => ℝ)
    (lam s * w (Fin.last (m + 1)))
    (fun i : Fin (m + 1) =>
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s)) (tp m w) i))


-- @@ L265-267 verbatim
@[simp] theorem mact_apply_last (P : Params m) (s : ℝ) (w : F) :
    mact m P s w (Fin.last (m + 1)) = lam s * w (Fin.last (m + 1)) := by
  simp [mact]


-- @@ L269-273 verbatim
@[simp] theorem mact_apply_castSucc (P : Params m) (s : ℝ) (w : F)
    (i : Fin (m + 1)) :
    mact m P s w i.castSucc =
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s)) (tp m w) i := by
  simp [mact]


-- @@ L275-285 verbatim
theorem mact_one (P : Params m) (w : F) : mact m P 1 w = w := by
  apply PiLp.ext
  intro j
  induction j using Fin.lastCases with
  | last =>
      rw [mact_apply_last, lam]
      norm_num
  | cast i =>
      rw [mact_apply_castSucc, show (1 : ℝ) - 1 = 0 by norm_num,
        (pathT m P).zero, SOFrameGauge.toCLM_one]
      rfl


-- @@ L287-309 verbatim
theorem mact_zero_castSucc (P : Params m) (w : F) (i : Fin (m + 1)) :
    mact m P 0 w i.castSucc =
      blockEta m P.eta P.eps i * w ((finRotate (m + 1) i).castSucc) := by
  rw [mact_apply_castSucc, show (1 : ℝ) - 0 = 1 by norm_num, (pathT m P).one]
  rw [SOFrameGauge.toCLM_apply_coord]
  have hterm : ∀ j' : Fin (m + 1),
      ((P.block m : SOGroup (m + 1)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j' * tp m w j' =
      if j' = finRotate (m + 1) i then
        blockEta m P.eta P.eps i * tp m w j' else 0 := by
    intro j'
    have hcoe : ((P.block m : SOGroup (m + 1)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j' =
        if j' = finRotate (m + 1) i then blockEta m P.eta P.eps i else 0 :=
      rfl
    rw [hcoe]
    by_cases hj : j' = finRotate (m + 1) i
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, zero_mul]
  rw [Finset.sum_congr rfl fun j' _ => hterm j']
  rw [Finset.sum_ite_eq' Finset.univ (finRotate (m + 1) i)
    (fun j' => blockEta m P.eta P.eps i * tp m w j')]
  simp


-- @@ L311-316 verbatim
/-- Explicit inverse of the codomain matrix action. -/
def mactInv (P : Params m) (s : ℝ) (y : F) : F :=
  WithLp.toLp 2 (Fin.lastCases (motive := fun _ => ℝ)
    (y (Fin.last (m + 1)) / lam s)
    (fun i : Fin (m + 1) =>
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s))⁻¹ (tp m y) i))


-- @@ L318-320 verbatim
@[simp] theorem mactInv_apply_last (P : Params m) (s : ℝ) (y : F) :
    mactInv m P s y (Fin.last (m + 1)) = y (Fin.last (m + 1)) / lam s := by
  simp [mactInv]


-- @@ L322-326 verbatim
@[simp] theorem mactInv_apply_castSucc (P : Params m) (s : ℝ) (y : F)
    (i : Fin (m + 1)) :
    mactInv m P s y i.castSucc =
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s))⁻¹ (tp m y) i := by
  simp [mactInv]


-- @@ L328-344 verbatim
theorem mact_surjective (P : Params m) {s : ℝ} (hs : 0 ≤ s) :
    Function.Surjective (mact m P s) := by
  intro y
  refine ⟨mactInv m P s y, ?_⟩
  have htp : tp m (mactInv m P s y) =
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s))⁻¹ (tp m y) := by
    apply PiLp.ext
    intro j
    rw [tp_apply, mactInv_apply_castSucc]
  apply PiLp.ext
  intro j
  induction j using Fin.lastCases with
  | last =>
      rw [mact_apply_last, mactInv_apply_last,
        mul_div_cancel₀ _ (ne_of_gt (lam_pos hs))]
  | cast i =>
      rw [mact_apply_castSucc, htp, SOFrameGauge.toCLM_apply_inv, tp_apply]


-- @@ L346-346 verbatim
/-! ## The moving level map -/


-- @@ L348-353 verbatim
/-- The one-parameter family of level maps interpolating from the tube-form
presentation to the compact birth circle. -/
def level (P : Params m) (s : ℝ) (x : E) : F :=
  (1 - CompactBirth.cutoff x) •
      mact m P s (StandardBirth.circleMap (m + 1) 1 (rho m P s x)) +
    CompactBirth.cutoff x • CompactBirth.background (m + 1)


-- @@ L355-358 verbatim
theorem level_one (P : Params m) (x : E) :
    level m P 1 x = CompactBirth.levelMap (m + 1) 1 x := by
  rw [level, rho_one, mact_one]
  rfl


-- @@ L360-364 verbatim
theorem level_eq_background (P : Params m) {s : ℝ} {x : E}
    (hx : 4 ≤ CompactBirth.normSq x) :
    level m P s x = CompactBirth.background (m + 1) := by
  rw [level, CompactBirth.cutoff_eq_one hx]
  simp


-- @@ L366-366 verbatim
/-! ## Zero analysis -/


-- @@ L368-378 verbatim
theorem normSq_eq_radialSq_of_transverse (y : E)
    (htr : ∀ i : Fin (m + 1), y (i.castSucc.castSucc) = 0) :
    CompactBirth.normSq y = StandardBirth.radialSq (m + 1) y := by
  unfold CompactBirth.normSq StandardBirth.radialSq
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : ∀ i : Fin (m + 1), y (i.castSucc.castSucc) ^ 2 = 0 := by
    intro i
    rw [htr i]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hz i]
  simp [StandardBirth.radialFirst, StandardBirth.radialSecond]


-- @@ L380-393 verbatim
theorem circleMap_zero_normSq {y : E}
    (hy : StandardBirth.circleMap (m + 1) 1 y = 0) :
    CompactBirth.normSq y = 1 := by
  have htr : ∀ i : Fin (m + 1), y (i.castSucc.castSucc) = 0 := by
    intro i
    have h := congrArg (fun q : F => q i.castSucc) hy
    simp only [PiLp.zero_apply] at h
    rwa [StandardBirth.circleMap_apply_castSucc] at h
  have hrad : StandardBirth.radialSq (m + 1) y = 1 := by
    have h := congrArg (fun q : F => q (Fin.last (m + 1))) hy
    simp only [PiLp.zero_apply] at h
    rw [StandardBirth.circleMap_apply_last] at h
    linarith
  rw [normSq_eq_radialSq_of_transverse m y htr, hrad]


-- @@ L395-398 verbatim
theorem cutoff_pos_of_ne_zero {y : E} (h : CompactBirth.cutoff y ≠ 0) :
    2 < CompactBirth.normSq y := by
  by_contra hn
  exact h (CompactBirth.cutoff_eq_zero (not_lt.mp hn))


-- @@ L400-496 verbatim
/-- Any zero of the moving level map has vanishing cutoff and lies on the
rotated circle. -/
theorem level_zero_analysis (P : Params m) {s : ℝ} {x : E} (hs : 0 ≤ s)
    (h : level m P s x = 0) :
    CompactBirth.cutoff x = 0 ∧
      StandardBirth.circleMap (m + 1) 1 (rho m P s x) = 0 := by
  set u := CompactBirth.cutoff x with hu
  set y := rho m P s x with hy
  set w := StandardBirth.circleMap (m + 1) 1 y with hwdef
  have hu0 : 0 ≤ u := CompactBirth.cutoff_nonneg x
  have hu1 : u ≤ 1 := CompactBirth.cutoff_le_one x
  -- last row
  have hlast : (1 - u) * (lam s * w (Fin.last (m + 1))) + u = 0 := by
    have hcoord := congrArg (fun q : F => q (Fin.last (m + 1))) h
    simp only [level, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply] at hcoord
    rw [mact_apply_last, CompactBirth.background_apply_last] at hcoord
    rw [← hu, ← hy, ← hwdef] at hcoord
    linarith [hcoord]
  have hune : u ≠ 1 := by
    intro hueq
    rw [hueq] at hlast
    norm_num at hlast
  have hult : u < 1 := lt_of_le_of_ne hu1 hune
  -- transverse rows
  have htrans : ∀ i : Fin (m + 1),
      SOFrameGauge.toCLM ((pathT m P).Q (1 - s)) (tp m w) i = 0 := by
    intro i
    have hcoord := congrArg (fun q : F => q i.castSucc) h
    simp only [level, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.zero_apply] at hcoord
    rw [mact_apply_castSucc, CompactBirth.background_apply_castSucc] at hcoord
    rw [← hu, ← hy, ← hwdef] at hcoord
    have hfac : (1 - u) ≠ 0 := by linarith
    have hprod0 : (1 - u) *
        SOFrameGauge.toCLM ((pathT m P).Q (1 - s)) (tp m w) i = 0 := by
      linarith [hcoord]
    exact (mul_eq_zero.mp hprod0).resolve_left hfac
  have htpzero : tp m w = 0 := by
    have happ : SOFrameGauge.toCLM ((pathT m P).Q (1 - s)) (tp m w) = 0 := by
      apply PiLp.ext
      intro i
      rw [htrans i, PiLp.zero_apply]
    have hinj := (SOFrameGauge.toCLM_bijective ((pathT m P).Q (1 - s))).1
    apply hinj
    rw [happ, map_zero]
  have htr : ∀ i : Fin (m + 1), y (i.castSucc.castSucc) = 0 := by
    intro i
    have hcoord := congrArg
      (fun q : EuclideanSpace ℝ (Fin (m + 1)) => q i) htpzero
    simp only [PiLp.zero_apply] at hcoord
    rw [tp_apply] at hcoord
    rwa [hwdef, StandardBirth.circleMap_apply_castSucc] at hcoord
  have hnormrad : CompactBirth.normSq y = StandardBirth.radialSq (m + 1) y :=
    normSq_eq_radialSq_of_transverse m y htr
  have hnormxy : CompactBirth.normSq y = CompactBirth.normSq x := by
    rw [hy]
    exact normSq_rho m P s x
  have hwlast : w (Fin.last (m + 1)) = StandardBirth.radialSq (m + 1) y - 1 :=
    StandardBirth.circleMap_apply_last (m + 1) 1 y
  have hu0eq : u = 0 := by
    by_contra hune0
    have hgt : 2 < CompactBirth.normSq x := by
      apply cutoff_pos_of_ne_zero
      rw [← hu]
      exact hune0
    have hradgt : 2 < StandardBirth.radialSq (m + 1) y := by
      rw [← hnormrad, hnormxy]
      exact hgt
    have hlampos := lam_pos hs
    have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hune0)
    rw [hwlast] at hlast
    have h1 : (0 : ℝ) < 1 - u := by linarith
    have h2 : (0 : ℝ) < StandardBirth.radialSq (m + 1) y - 1 := by linarith
    have h3 : (0 : ℝ) < lam s * (StandardBirth.radialSq (m + 1) y - 1) :=
      mul_pos hlampos h2
    have h4 : (0 : ℝ) < (1 - u) *
        (lam s * (StandardBirth.radialSq (m + 1) y - 1)) := mul_pos h1 h3
    linarith
  refine ⟨hu0eq, ?_⟩
  have hrad1 : StandardBirth.radialSq (m + 1) y = 1 := by
    rw [hu0eq, hwlast] at hlast
    have hlampos := lam_pos hs
    have hzero : lam s * (StandardBirth.radialSq (m + 1) y - 1) = 0 := by
      linarith
    have := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hlampos)
    linarith
  show w = 0
  apply PiLp.ext
  intro j
  induction j using Fin.lastCases with
  | last =>
      rw [hwdef, StandardBirth.circleMap_apply_last, hrad1, PiLp.zero_apply]
      ring
  | cast i =>
      rw [hwdef, StandardBirth.circleMap_apply_castSucc, htr i,
        PiLp.zero_apply]


-- @@ L498-498 verbatim
/-! ## Smoothness -/


-- @@ L500-517 verbatim
theorem rho_smooth (P : Params m) :
    ContDiff ℝ ∞ (fun p : ℝ × E => rho m P p.1 p.2) := by
  rw [contDiff_piLp]
  intro j
  have heq : (fun p : ℝ × E => rho m P p.1 p.2 j) =
      fun p : ℝ × E => ∑ k, (((pathA m P).Q (1 - p.1) : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) j k * p.2 k := by
    funext p
    exact SOFrameGauge.toCLM_apply_coord _ _ _
  rw [heq]
  apply ContDiff.sum
  intro k _
  have hentry : ContDiff ℝ ∞ (fun p : ℝ × E =>
      (((pathA m P).Q (1 - p.1) : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) j k) :=
    ((pathA m P).smooth j k).comp (contDiff_const.sub contDiff_fst)
  exact hentry.mul ((EuclideanSpace.proj k :
    EuclideanSpace ℝ (Fin (m + 3)) →L[ℝ] ℝ).contDiff.comp contDiff_snd)


-- @@ L519-567 verbatim
theorem level_smooth (P : Params m) :
    ContDiff ℝ ∞ (fun p : ℝ × E => level m P p.1 p.2) := by
  have hcut : ContDiff ℝ ∞ (fun p : ℝ × E => CompactBirth.cutoff p.2) :=
    CompactBirth.contDiff_cutoff.comp contDiff_snd
  have hcircle : ContDiff ℝ ∞ (fun p : ℝ × E =>
      StandardBirth.circleMap (m + 1) 1 (rho m P p.1 p.2)) :=
    (StandardBirth.contDiff_circleMap (m + 1) 1).comp (rho_smooth m P)
  have hmact : ContDiff ℝ ∞ (fun p : ℝ × E =>
      mact m P p.1 (StandardBirth.circleMap (m + 1) 1 (rho m P p.1 p.2))) := by
    rw [contDiff_piLp]
    intro j
    induction j using Fin.lastCases with
    | last =>
        have heq : (fun p : ℝ × E =>
            mact m P p.1 (StandardBirth.circleMap (m + 1) 1
              (rho m P p.1 p.2)) (Fin.last (m + 1))) =
            fun p : ℝ × E => lam p.1 *
              (StandardBirth.circleMap (m + 1) 1 (rho m P p.1 p.2))
                (Fin.last (m + 1)) := by
          funext p
          rw [mact_apply_last]
        rw [heq]
        have hlam : ContDiff ℝ ∞ (fun p : ℝ × E => lam p.1) := by
          unfold lam
          fun_prop
        exact hlam.mul ((EuclideanSpace.proj (Fin.last (m + 1)) :
          EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] ℝ).contDiff.comp hcircle)
    | cast i =>
        have heq : (fun p : ℝ × E =>
            mact m P p.1 (StandardBirth.circleMap (m + 1) 1
              (rho m P p.1 p.2)) i.castSucc) =
            fun p : ℝ × E => ∑ k,
              (((pathT m P).Q (1 - p.1) : SOGroup (m + 1)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i k *
              (StandardBirth.circleMap (m + 1) 1 (rho m P p.1 p.2))
                k.castSucc := by
          funext p
          rw [mact_apply_castSucc, SOFrameGauge.toCLM_apply_coord]
          exact Finset.sum_congr rfl fun k _ => rfl
        rw [heq]
        apply ContDiff.sum
        intro k _
        have hentry : ContDiff ℝ ∞ (fun p : ℝ × E =>
            (((pathT m P).Q (1 - p.1) : SOGroup (m + 1)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i k) :=
          ((pathT m P).smooth i k).comp (contDiff_const.sub contDiff_fst)
        exact hentry.mul ((EuclideanSpace.proj k.castSucc :
          EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] ℝ).contDiff.comp hcircle)
  exact ((contDiff_const.sub hcut).smul hmact).add (hcut.smul contDiff_const)


-- @@ L569-569 verbatim
/-! ## The codomain matrix as a continuous linear map -/


-- @@ L571-595 verbatim
def mactCLM (P : Params m) (s : ℝ) : F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    { toFun := mact m P s
      map_add' := by
        intro w w'
        apply PiLp.ext
        intro j
        induction j using Fin.lastCases with
        | last =>
            simp only [PiLp.add_apply, mact_apply_last]
            ring
        | cast i =>
            simp only [PiLp.add_apply, mact_apply_castSucc, tp_add, map_add]
      map_smul' := by
        intro c w
        apply PiLp.ext
        intro j
        induction j using Fin.lastCases with
        | last =>
            simp only [PiLp.smul_apply, mact_apply_last, smul_eq_mul,
              RingHom.id_apply]
            ring
        | cast i =>
            simp only [PiLp.smul_apply, mact_apply_castSucc, tp_smul,
              map_smul, RingHom.id_apply] }


-- @@ L597-598 verbatim
theorem mactCLM_apply (P : Params m) (s : ℝ) (w : F) :
    mactCLM m P s w = mact m P s w := rfl


-- @@ L600-600 verbatim
/-! ## The comparison cobordism -/


-- @@ L602-604 verbatim
/-- The full space-time comparison map. -/
def bigG (P : Params m) (v : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) : F :=
  level m P (normRamp (vertC v)) (initCLM (m + 3) v)


-- @@ L606-607 verbatim
theorem bigG_def (P : Params m) (v : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) :
    bigG m P v = level m P (normRamp (vertC v)) (initCLM (m + 3) v) := rfl


-- @@ L609-611 verbatim
theorem bigG_spaceTime (P : Params m) (x : E) (t : ℝ) :
    bigG m P (spaceTime x t) = level m P (normRamp t) x := by
  rw [bigG_def, initCLM_spaceTime, vertC_spaceTime]


-- @@ L613-620 verbatim
theorem bigG_smooth (P : Params m) : ContDiff ℝ ∞ (bigG m P) := by
  have hpair : ContDiff ℝ ∞
      (fun v : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1)) =>
        ((normRamp (vertC v), initCLM (m + 3) v) : ℝ × E)) :=
    (contDiff_normRamp.comp contDiff_vertC).prodMk (initCLM (m + 3)).contDiff
  show ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1)) =>
    level m P (normRamp (vertC v)) (initCLM (m + 3) v))
  simpa only [Function.comp_def] using (level_smooth m P).comp hpair


-- @@ L622-681 verbatim
/-- Surjectivity of the spatial differential of a fixed-time slice at a
zero. -/
theorem level_slice_surjective (P : Params m) {s₀ : ℝ} {x₀ : E}
    (hs : 0 ≤ s₀)
    (hw : StandardBirth.circleMap (m + 1) 1 (rho m P s₀ x₀) = 0) :
    Function.Surjective
      (fderiv ℝ (fun x' : E => level m P s₀ x') x₀) := by
  have hx₀normSq : CompactBirth.normSq x₀ = 1 := by
    have h1 : CompactBirth.normSq (rho m P s₀ x₀) = 1 :=
      circleMap_zero_normSq m hw
    rw [← normSq_rho m P s₀, h1]
  have hopen : IsOpen {z : E | CompactBirth.normSq z < 2} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  have hx₀mem : x₀ ∈ {z : E | CompactBirth.normSq z < 2} := by
    rw [mem_setOf_eq, hx₀normSq]
    norm_num
  have hev : (fun x' : E => level m P s₀ x') =ᶠ[nhds x₀]
      (fun x' : E => mactCLM m P s₀ (StandardBirth.circleMap (m + 1) 1
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x'))) := by
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hx₀mem) fun z hz => ?_
    have hcz : CompactBirth.cutoff z = 0 :=
      CompactBirth.cutoff_eq_zero (le_of_lt hz)
    rw [level, hcz, mactCLM_apply]
    simp [rho]
  rw [hev.fderiv_eq]
  -- chain rule
  have hF₁ : HasFDerivAt
      (fun x' : E => SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x')
      (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀))) x₀ :=
    (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀))).hasFDerivAt
  have hcirc : HasFDerivAt (StandardBirth.circleMap (m + 1) 1)
      (fderiv ℝ (StandardBirth.circleMap (m + 1) 1)
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x₀))
      (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x₀) :=
    ((StandardBirth.contDiff_circleMap (m + 1) 1).differentiable
      infty_ne_zero _).hasFDerivAt
  have hF₃ : HasFDerivAt (fun w : F => mactCLM m P s₀ w)
      (mactCLM m P s₀)
      (StandardBirth.circleMap (m + 1) 1
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x₀)) :=
    (mactCLM m P s₀).hasFDerivAt
  have hcomp := hF₃.comp x₀ (hcirc.comp x₀ hF₁)
  have hfd : fderiv ℝ (fun x' : E =>
      mactCLM m P s₀ (StandardBirth.circleMap (m + 1) 1
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x'))) x₀ =
      (mactCLM m P s₀).comp
        ((fderiv ℝ (StandardBirth.circleMap (m + 1) 1)
          (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x₀)).comp
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)))) := hcomp.fderiv
  rw [hfd]
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  apply Function.Surjective.comp
  · intro y
    obtain ⟨w, hwsurj⟩ := mact_surjective m P hs y
    exact ⟨w, by rw [mactCLM_apply]; exact hwsurj⟩
  apply Function.Surjective.comp
  · have hzero : StandardBirth.circleMap (m + 1) 1
        (SOFrameGauge.toCLM ((pathA m P).Q (1 - s₀)) x₀) = 0 := hw
    exact (StandardBirth.targetFLS (m + 1)).regular _ hzero
  · exact (SOFrameGauge.toCLM_bijective ((pathA m P).Q (1 - s₀))).2


-- @@ L683-718 verbatim
/-- The tube-form comparison cobordism: from any presentation whose defining
map is literally `level P 0` to the compact birth circle. -/
def cob (P : Params m) {X₀ : FramedLevelSet (m + 2)}
    (hg : ∀ x, X₀.g x = level m P 0 x) : FramedLevelCobordism (m + 2) where
  X₀ := X₀
  X₁ := CompactBirth.targetFLS (m + 1)
  G := bigG m P
  smooth := bigG_smooth m P
  spatial_bounded := by
    refine ⟨1, ?_⟩
    intro v hv
    rw [bigG_def] at hv
    obtain ⟨-, hw⟩ := level_zero_analysis m P (normRamp_nonneg _) hv
    have h1 : CompactBirth.normSq (rho m P (normRamp (vertC v))
        (initCLM (m + 3) v)) = 1 := circleMap_zero_normSq m hw
    have h2 : CompactBirth.normSq (initCLM (m + 3) v) = 1 := by
      rw [← normSq_rho m P (normRamp (vertC v)), h1]
    rw [CompactBirth.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg (initCLM (m + 3) v)]
  regular := by
    intro v hv
    rw [bigG_def] at hv
    obtain ⟨-, hw⟩ := level_zero_analysis m P (normRamp_nonneg _) hv
    apply surjective_fderiv_of_slice (bigG_smooth m P)
    have hchange : (fun x' : E => bigG m P (spaceTime x' (vertC v))) =
        fun x' : E => level m P (normRamp (vertC v)) x' :=
      funext fun x' => bigG_spaceTime m P x' (vertC v)
    rw [hchange]
    exact level_slice_surjective m P (normRamp_nonneg _) hw
  collar_zero := by
    intro x t ht
    rw [bigG_spaceTime, normRamp_of_le_quarter ht, hg x]
  collar_one := by
    intro x t ht
    rw [bigG_spaceTime, normRamp_of_three_quarter_le ht, level_one]
    rfl


-- @@ L720-732 verbatim
/-- The signed comparison cobordism, with constant positive label. -/
def signedCob (P : Params m) {X₀ : FramedLevelSet (m + 2)}
    (S : FiberSign X₀) (hS : ∀ x, S x = 1)
    (hg : ∀ x, X₀.g x = level m P 0 x) :
    SignedFramedLevelCobordism S (CompactBirth.targetSign (m + 1)) where
  cobordism := cob m P hg
  source_eq := rfl
  target_eq := rfl
  toFun _ := 1
  continuous := continuous_const
  nonzero := fun _ _ => one_ne_zero
  collar_zero := fun x _ _ => (hS x).symm
  collar_one := fun _ _ _ => rfl


-- @@ L734-748 verbatim
/-- The comparison cobordism is spatially flat with the common compact
background outside radius `5/2`. -/
theorem signedCob_flat (P : Params m) {X₀ : FramedLevelSet (m + 2)}
    (S : FiberSign X₀) (hS : ∀ x, S x = 1)
    (hg : ∀ x, X₀.g x = level m P 0 x) :
    (signedCob m P S hS hg).SpatialFlatOutside
      (ConcreteConfigurationMorseReduction.compactBackground m) 0 (5 / 2) := by
  intro v hv
  show bigG m P v = ConcreteConfigurationMorseReduction.compactBackground m
  rw [bigG_def]
  apply level_eq_background
  have hnorm : (5 : ℝ) / 2 ≤ ‖initCLM (m + 3) v‖ := by
    simpa [dist_zero_right] using hv
  rw [CompactBirth.normSq_eq_norm_sq]
  nlinarith


-- @@ L750-750 verbatim
/-! ## Coordinate identifications -/


-- @@ L752-754 verbatim
theorem i0_eq_zero : i0 m = (0 : Fin (m + 3)) := by
  apply Fin.ext
  rfl


-- @@ L756-758 verbatim
theorem i1_eq_one : i1 m = (1 : Fin (m + 3)) := by
  apply Fin.ext
  rfl


-- @@ L760-764 verbatim
theorem iA_ne_i1 (hm : 0 < m) : iA m ≠ i1 m := by
  intro h
  have hv := congrArg Fin.val h
  rw [iA_val, i1_val] at hv
  omega


-- @@ L766-768 verbatim
theorem radialFirst_eq_iA : StandardBirth.radialFirst (m + 1) = iA m := by
  apply Fin.ext
  rfl


-- @@ L770-772 verbatim
theorem radialSecond_eq_iB : StandardBirth.radialSecond (m + 1) = iB m := by
  apply Fin.ext
  rfl


-- @@ L774-775 verbatim
theorem val_castSucc_succ (i : Fin (m + 1)) :
    ((i.castSucc.succ : Fin (m + 3)) : ℕ) = (i : ℕ) + 1 := rfl


-- @@ L777-777 verbatim
/-! ## The time-zero level map in closed form -/


-- @@ L779-782 verbatim
theorem rho_zero_iA (P : Params m) (hm : 0 < m) (x : E) :
    rho m P 0 x (iA m) = -(x (0 : Fin (m + 3))) := by
  rw [rho_zero_apply m P hm x (iA m), if_neg (iA_ne_i0 m),
    if_neg (iA_ne_i1 m hm), if_pos rfl, i0_eq_zero]


-- @@ L784-787 verbatim
theorem rho_zero_iB (P : Params m) (hm : 0 < m) (x : E) :
    rho m P 0 x (iB m) = -(P.eps * x (1 : Fin (m + 3))) := by
  rw [rho_zero_apply m P hm x (iB m), if_neg (Ne.symm (i0_ne_iB m)),
    if_neg (iB_ne_i1 m), if_neg (Ne.symm (iA_ne_iB m)), if_pos rfl, i1_eq_one]


-- @@ L789-796 verbatim
theorem radialSq_rho_zero (P : Params m) (hm : 0 < m) (x : E) :
    StandardBirth.radialSq (m + 1) (rho m P 0 x) = radSq x := by
  have hsq : P.eps ^ 2 = 1 := by
    rw [sq]
    exact P.eps_sq
  rw [StandardBirth.radialSq, radialFirst_eq_iA, radialSecond_eq_iB,
    rho_zero_iA m P hm x, rho_zero_iB m P hm x, radSq, neg_sq, neg_sq,
    mul_pow, hsq, one_mul]


-- @@ L798-806 verbatim
theorem level_zero_apply_last (P : Params m) (hm : 0 < m) (x : E) :
    level m P 0 x (Fin.last (m + 1)) =
      (1 - CompactBirth.cutoff x) * ((radSq x - 1) / 2) +
        CompactBirth.cutoff x := by
  rw [level]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mact_apply_last,
    CompactBirth.background_apply_last, StandardBirth.circleMap_apply_last,
    radialSq_rho_zero m P hm x, lam]
  ring


-- @@ L808-811 verbatim
theorem finRotate_val_eq (i : Fin (m + 1)) :
    ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) =
      if i = Fin.last m then 0 else (i : ℕ) + 1 := by
  rw [finRotate_apply, Fin.val_add_one]


-- @@ L813-882 verbatim
theorem rho_zero_index (P : Params m) (hm : 0 < m) (x : E) (i : Fin (m + 1)) :
    rho m P 0 x ((finRotate (m + 1) i).castSucc.castSucc) =
      (if i = 0 then P.eps * x (iB m) else x (i.castSucc.succ)) := by
  by_cases hi0 : i = 0
  · subst hi0
    have hnl : ((0 : Fin (m + 1))) ≠ Fin.last m := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_last, Fin.val_zero] at hv
      omega
    have hj : (((finRotate (m + 1) (0 : Fin (m + 1))).castSucc.castSucc) :
        Fin (m + 3)) = i1 m := by
      apply Fin.ext
      show ((finRotate (m + 1) (0 : Fin (m + 1)) : Fin (m + 1)) : ℕ) = 1
      rw [finRotate_val_eq m (0 : Fin (m + 1)), if_neg hnl, Fin.val_zero]
    rw [hj, rho_zero_apply m P hm x (i1 m), if_neg (Ne.symm (i0_ne_i1 m)),
      if_pos rfl, if_pos rfl]
  · rw [if_neg hi0]
    have hi0' : (i : ℕ) ≠ 0 := by
      intro h
      apply hi0
      apply Fin.ext
      rw [h, Fin.val_zero]
    by_cases hil : i = Fin.last m
    · have hj : (((finRotate (m + 1) i).castSucc.castSucc) : Fin (m + 3)) =
          i0 m := by
        apply Fin.ext
        show ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) = 0
        rw [finRotate_val_eq m i, if_pos hil]
      have hval : (i : ℕ) = m := by
        rw [hil]
        rfl
      have hsucc : ((i.castSucc.succ : Fin (m + 3))) = iA m := by
        apply Fin.ext
        rw [val_castSucc_succ m i, iA_val, hval]
      rw [hj, rho_zero_apply m P hm x (i0 m), if_pos rfl, hsucc]
    · have hle := i.isLt
      have hlt : (i : ℕ) < m := by
        by_contra hcon
        refine hil (Fin.ext ?_)
        rw [Fin.val_last]
        omega
      have hj : (((finRotate (m + 1) i).castSucc.castSucc) : Fin (m + 3)) =
          i.castSucc.succ := by
        apply Fin.ext
        show ((finRotate (m + 1) i : Fin (m + 1)) : ℕ) =
          ((i.castSucc.succ : Fin (m + 3)) : ℕ)
        rw [finRotate_val_eq m i, if_neg hil, val_castSucc_succ m i]
      have hn0 : (i.castSucc.succ : Fin (m + 3)) ≠ i0 m := by
        intro h
        have hv := congrArg Fin.val h
        rw [val_castSucc_succ m i, i0_val] at hv
        omega
      have hn1 : (i.castSucc.succ : Fin (m + 3)) ≠ i1 m := by
        intro h
        have hv := congrArg Fin.val h
        rw [val_castSucc_succ m i, i1_val] at hv
        omega
      have hnA : (i.castSucc.succ : Fin (m + 3)) ≠ iA m := by
        intro h
        have hv := congrArg Fin.val h
        rw [val_castSucc_succ m i, iA_val] at hv
        omega
      have hnB : (i.castSucc.succ : Fin (m + 3)) ≠ iB m := by
        intro h
        have hv := congrArg Fin.val h
        rw [val_castSucc_succ m i, iB_val] at hv
        omega
      rw [hj, rho_zero_apply m P hm x (i.castSucc.succ), if_neg hn0,
        if_neg hn1, if_neg hnA, if_neg hnB]


-- @@ L884-900 verbatim
theorem level_zero_apply_castSucc (P : Params m) (hm : 0 < m) (x : E)
    (i : Fin (m + 1)) :
    level m P 0 x i.castSucc =
      (1 - CompactBirth.cutoff x) *
        (P.eta i * (if i = 0 then x (iB m) else x (i.castSucc.succ))) := by
  rw [level]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    CompactBirth.background_apply_castSucc, mact_zero_castSucc,
    StandardBirth.circleMap_apply_castSucc, rho_zero_index m P hm x i,
    blockEta]
  by_cases hi0 : i = 0
  · rw [if_pos hi0, if_pos hi0, if_pos hi0]
    have he := P.eps_sq
    linear_combination
      ((1 - CompactBirth.cutoff x) * P.eta i * x (iB m)) * he
  · rw [if_neg hi0, if_neg hi0, if_neg hi0]
    ring


-- @@ L902-902 verbatim
/-! ## Background coordinates and the harmonizing swap -/


-- @@ L904-910 verbatim
theorem tube_background_apply (i : Fin (m + 2)) :
    CompactTubeConfiguration.background m i = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0
  · rw [if_pos hi, hi]
    exact CompactTubeConfiguration.background_apply_zero m
  · rw [if_neg hi]
    exact CompactTubeConfiguration.background_apply_ne_zero m hi


-- @@ L912-921 verbatim
theorem compactBackground_apply (i : Fin (m + 2)) :
    ConcreteConfigurationMorseReduction.compactBackground m i =
      if i = Fin.last (m + 1) then 1 else 0 := by
  induction i using Fin.lastCases with
  | last =>
      rw [if_pos rfl]
      exact CompactBirth.background_apply_last (m + 1)
  | cast j =>
      rw [if_neg (Fin.castSucc_lt_last j).ne]
      exact CompactBirth.background_apply_castSucc (m + 1) j


-- @@ L923-926 verbatim
theorem last_ne_zero_F : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv


-- @@ L928-936 verbatim
theorem tubeSwap_apply (g : F) (i : Fin (m + 2)) :
    backgroundEquiv (CompactTubeConfiguration.background m)
        (ConcreteConfigurationMorseReduction.compactBackground m)
        (CompactTubeConfiguration.background_ne_zero m)
        (CompactBirth.background_ne_zero (m + 1)) g i =
      if i = 0 then g (Fin.last (m + 1))
      else if i = Fin.last (m + 1) then g 0 else g i :=
  backgroundEquiv_swap_apply (k := m) _ _ (tube_background_apply m)
    (compactBackground_apply m) _ _ g i


-- @@ L938-938 verbatim
/-! ## The harmonized class-one tube circle -/


-- @@ L940-946 verbatim
theorem onePos_g_eq (x : E) :
    (StandardCircleLedgerConfiguration.onePos m).X.g x =
      backgroundEquiv (CompactTubeConfiguration.background m)
        (ConcreteConfigurationMorseReduction.compactBackground m)
        (CompactTubeConfiguration.background_ne_zero m)
        (CompactBirth.background_ne_zero (m + 1))
        (CompactTubeConfiguration.levelMap m x) := rfl


-- @@ L948-954 verbatim
theorem onePos_g_apply (x : E) (i : Fin (m + 2)) :
    (StandardCircleLedgerConfiguration.onePos m).X.g x i =
      if i = 0 then CompactTubeConfiguration.levelMap m x (Fin.last (m + 1))
      else if i = Fin.last (m + 1) then CompactTubeConfiguration.levelMap m x 0
      else CompactTubeConfiguration.levelMap m x i := by
  rw [onePos_g_eq]
  exact tubeSwap_apply m (CompactTubeConfiguration.levelMap m x) i


-- @@ L956-958 verbatim
theorem last_succ_eq_iB : ((Fin.last (m + 1)).succ : Fin (m + 3)) = iB m := by
  apply Fin.ext
  simp


-- @@ L960-969 verbatim
/-- The parameter pack realizing the harmonized class-one tube circle. -/
def oneParams : Params m where
  eta := fun _ => 1
  eps := (-1) ^ m
  heta := fun _ => Or.inl rfl
  heps := by
    rcases Nat.even_or_odd m with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  hprod := by simp


-- @@ L971-971 verbatim
@[simp] theorem oneParams_eta (i : Fin (m + 1)) : (oneParams m).eta i = 1 := rfl


-- @@ L973-1002 verbatim
theorem onePos_g_eq_level (hm : 0 < m) (x : E) :
    (StandardCircleLedgerConfiguration.onePos m).X.g x =
      level m (oneParams m) 0 x := by
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
      rw [onePos_g_apply m x (Fin.last (m + 1)), if_neg (last_ne_zero_F m),
        if_pos rfl, CompactTubeConfiguration.levelMap_apply_zero m x,
        level_zero_apply_last m (oneParams m) hm x]
  | cast j =>
      have hjl : (j.castSucc : Fin (m + 2)) ≠ Fin.last (m + 1) :=
        (Fin.castSucc_lt_last j).ne
      rw [onePos_g_apply m x j.castSucc,
        level_zero_apply_castSucc m (oneParams m) hm x j, oneParams_eta]
      by_cases hj0 : j = 0
      · subst hj0
        rw [Fin.castSucc_zero, if_pos rfl,
          CompactTubeConfiguration.levelMap_apply_ne_zero m x
            (last_ne_zero_F m),
          if_pos rfl, last_succ_eq_iB, one_mul]
      · have hjne0 : (j.castSucc : Fin (m + 2)) ≠ 0 := by
          intro h
          apply hj0
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa using hv
        rw [if_neg hjne0, if_neg hjl,
          CompactTubeConfiguration.levelMap_apply_ne_zero m x hjne0,
          if_neg hj0, one_mul]


-- @@ L1004-1010 verbatim
/-- The comparison cobordism killing the harmonized class-one circle. -/
def oneKillCob (hm : 0 < m) :
    SignedFramedLevelCobordism
      (StandardCircleLedgerConfiguration.onePos m).sign
      (CompactBirth.targetSign (m + 1)) :=
  signedCob m (oneParams m) (StandardCircleLedgerConfiguration.onePos m).sign
    (fun _ => rfl) (onePos_g_eq_level m hm)


-- @@ L1012-1017 verbatim
theorem oneKillCob_flat (hm : 0 < m) :
    (oneKillCob m hm).SpatialFlatOutside
      (ConcreteConfigurationMorseReduction.compactBackground m) 0 (5 / 2) :=
  signedCob_flat m (oneParams m)
    (StandardCircleLedgerConfiguration.onePos m).sign (fun _ => rfl)
    (onePos_g_eq_level m hm)


-- @@ L1019-1026 verbatim
/-- The `oneKill` field of `PieceKillInput`. -/
theorem exists_oneKill (hm : 0 < m) :
    ∃ C : SignedFramedLevelCobordism
      (StandardCircleLedgerConfiguration.onePos m).sign
      (CompactBirth.targetSign (m + 1)),
      C.SpatialFlatOutside
        (ConcreteConfigurationMorseReduction.compactBackground m) 0 (5 / 2) :=
  ⟨oneKillCob m hm, oneKillCob_flat m hm⟩


-- @@ L1028-1028 verbatim
end PieceKill

-- @@ L1029-1029 verbatim
end Submission
