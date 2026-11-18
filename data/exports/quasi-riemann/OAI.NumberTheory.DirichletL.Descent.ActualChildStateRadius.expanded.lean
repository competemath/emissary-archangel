import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMoment

-- @@ L8-8 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks

-- @@ L9-9 verbatim
open InverseSecondFibers CompletedGauss

-- @@ L10-10 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-14 verbatim
def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta


-- @@ L16-17 verbatim
def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)


-- @@ L19-20 verbatim
lemma actual_cell_row_radius_pos (Z M ell A t V j eta : ℝ) (d : BlockIndex) (hZ : 0<Z) :
    0<actualCellRowRadius Z M ell A t V j eta d := Real.rpow_pos_of_pos hZ _


-- @@ L22-41 verbatim
theorem actual_cell_correlated_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ∀x∈source,‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs := cell_subset p source d hx
  exact (actual_second_row_ball p hp hpr x 1 1 _).mpr
    (actual_cell_correlated_row_support p hp hpr source hk d x hx 1 1
      Z M r ell V delta A B j t eta tau L hZ heta hbin hL0 (hd x hxs) hL (hgate x hxs))


-- @@ L43-54 verbatim
theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)


-- @@ L56-56 verbatim
end SevenEighths.InverseMoment

-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
