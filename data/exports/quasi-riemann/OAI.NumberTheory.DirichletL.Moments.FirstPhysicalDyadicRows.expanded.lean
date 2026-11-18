import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows

-- @@ L10-10 verbatim
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve

-- @@ L12-12 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst

-- @@ L13-13 verbatim
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization

-- @@ L14-14 verbatim
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O


-- @@ L17-18 verbatim
def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => h∈dyadRows (n 1))


-- @@ L20-22 verbatim
lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter,mem_dyadRows]


-- @@ L24-25 verbatim
lemma activeRows_subset (rows : Finset O) (n : Fin 4→ℤ) : activeRows rows n⊆rows :=
  Finset.filter_subset _ _


-- @@ L27-29 verbatim
lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 :=
  dyadRows_ne_zero (n 1) h (Finset.mem_filter.mp hh).2


-- @@ L31-35 verbatim
lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤normValue h ∧ dyadicScale (n 1)/4<normValue h ∧ normValue h<dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩


-- @@ L37-40 verbatim
lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1<dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2


-- @@ L42-45 verbatim
lemma activeRows_ball_majorant (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/dyadicScale (n 1))).re :=
  ballProfile_majorizes _ (dyadicScale_pos (n 1)) h (activeRows_norm rows n h hh).2.2.le


-- @@ L47-59 verbatim
lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖eisEmbedding h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm


-- @@ L61-80 verbatim
theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]


-- @@ L82-82 verbatim
end SevenEighths.CenteredMomentFirstPhysicalDyadicRows


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
