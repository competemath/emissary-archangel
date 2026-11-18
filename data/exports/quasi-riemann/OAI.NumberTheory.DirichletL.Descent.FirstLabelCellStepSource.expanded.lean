import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepGates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentFirstLabelCell

-- @@ L8-8 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents

-- @@ L10-10 verbatim
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks

-- @@ L11-11 verbatim
open InverseSecondUniformCutoff

-- @@ L12-12 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L14-14 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]


-- @@ L16-16 verbatim
abbrev exponent := InverseFirstGlobalCaps.dyadicExponent


-- @@ L18-19 verbatim
def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))


-- @@ L21-22 verbatim
def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)


-- @@ L24-27 verbatim
def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)


-- @@ L29-35 verbatim
def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)


-- @@ L37-37 verbatim
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L39-44 verbatim
include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=>extra_subset negative y.cube)
    negative J lists pool _ b _


-- @@ L46-49 verbatim
lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _


-- @@ L51-55 verbatim
lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _


-- @@ L57-75 verbatim
include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hwindow : Real.exp window≤Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc


-- @@ L77-91 verbatim
include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1<Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical


-- @@ L93-93 verbatim
end SevenEighths.InverseMomentFirstLabelCell

-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
end OAI
