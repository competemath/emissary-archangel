import OAI.Analysis.RecursivePotentials.Main


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-8 verbatim
/-! Proved construction certificates and a statement-preservation check for the
self-contained Comparator challenge. All eleven original conclusions are retained. -/


-- @@ L10-10 verbatim
namespace RecursivePotentials


-- @@ L12-12 verbatim
open VariableExponent Filter Topology TopologicalSpace UniformSpace


-- @@ L14-21 verbatim
def rec_mainOriginalStatement : Prop := (∀ t : ℝ, 0 < t → t < 1 → t^3/128 ≤ averagedModulus XSigma t ∧ t^3/128 ≤ averagedModulus XJoined t) ∧
    (∀ (H : Finset JoinedNode), joinedTree.Initial H → ∀ x : XZero,
      (∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0) → ∀ z : XZero,
      (∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) → z ≠ 0 →
      (‖x+z‖+‖x-z‖)/2 ≥ ‖x‖+‖z‖^3/(8*(2*‖x‖+‖z‖)^2)) ∧
    (∀ A : EquivalentNorm XSigma, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XZero, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XJoined, ¬A.AUC)


-- @@ L23-25 verbatim
def rec_completionOriginalStatement : Prop := RootSumCompletionStatement sequenceTree ∧
    ZeroRootCompletionStatement joinedTree ∧ RootSumCompletionStatement joinedTree ∧
    IsReflexive XZero ∧ IsReflexive XJoined


-- @@ L27-28 verbatim
def stop_all_radiiOriginalStatement : Prop := ∀ {t : ℝ} (_ht : 0 < t),
  0 < averagedModulus XSigma t


-- @@ L30-35 verbatim
def XJoined_separated_familiesOriginalStatement : Prop := ∀ {ε : ℝ} (_hε : 0 < ε),
  ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (ε ≤ 2 → η = min (1/2) (logarithmicGamma 2 (ε/16))) ∧
      ∀ (x : XJoined) (z : ℕ → XJoined),
        (∀ n, ‖x+z n‖ ≤ 1) → (∀ n, ‖x-z n‖ ≤ 1) →
        (∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ 1-η


-- @@ L37-37 verbatim
namespace Variable


-- @@ L39-48 verbatim
def spaceOriginalStatement : Prop := (∀ h : ℕ+, CompleteSpace (Component h) ∧ IsReflexive (Component h) ∧
      SeparableSpace (Component h →L[ℝ] ℝ) ∧ SourceNormStatement h ∧
      ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
        (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
        nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖) ∧
    CompleteSpace Xv ∧ IsReflexive Xv ∧ SeparableSpace (Xv →L[ℝ] ℝ) ∧
    Dense {x : Xv | FiniteTotalSupport x} ∧
    ∀ S : Finset Node, Continuous (projection S) ∧ FiniteDimensional ℝ (projection S).range ∧
      (∀ x : Xv, projection S (projection S x) = projection S x) ∧
      ∀ (s : Node) (x : Xv), coordinate s (projection S x) = if s ∈ S then coordinate s x else 0


-- @@ L50-56 verbatim
def lp_model_exactOriginalStatement : Prop := ∀ (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (f : ComponentNode h → ℝ × ℝ)
    (_hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2))),
  f = lpPotentials h v ∧ nu h v = (f (componentTree h).root).1+(f (componentTree h).root).2


-- @@ L58-59 verbatim
def one_sided_modulus_zeroOriginalStatement : Prop := ∀ (A : EquivalentNorm Xv),
  A.modulus (A.lower/A.upper) = 0


-- @@ L61-62 verbatim
def no_equivalent_AUCOriginalStatement : Prop := ∀ (A : EquivalentNorm Xv),
  ¬A.AUC


-- @@ L64-66 verbatim
def sixth_stabilityOriginalStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_hA : AdmissibleHeads x y A),
  sixthConstant*‖y‖^6/(‖x+y‖^2+‖x-y‖^2)^2 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2


-- @@ L68-70 verbatim
def cubic_stabilityOriginalStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_hA : AdmissibleHeads x y A) {R : ℝ} (_hR : 0 < R) (_hp : ‖x+y‖ ≤ R) (_hm : ‖x-y‖ ≤ R),
  ‖x‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2


-- @@ L72-75 verbatim
def weak_tailOriginalStatement : Prop := ∀ (x : Xv) {ε : ℝ} (_hε : 0 < ε) (_hε1 : ε ≤ 1)
    (y : ℕ → Xv) (_hy : WeaklyNull y) (_hyε : ∀ j, ε ≤ ‖y j‖)
    (_hp : ∀ j, ‖x+y j‖ ≤ 1) (_hm : ∀ j, ‖x-y j‖ ≤ 1),
  ‖x‖ ≤ theta ε ∧ theta ε < 1


-- @@ L77-77 verbatim
end Variable


-- @@ L79-90 verbatim
def OriginalResults : Prop :=
  rec_mainOriginalStatement ∧
  rec_completionOriginalStatement ∧
  stop_all_radiiOriginalStatement ∧
  XJoined_separated_familiesOriginalStatement ∧
  Variable.spaceOriginalStatement ∧
  Variable.lp_model_exactOriginalStatement ∧
  Variable.one_sided_modulus_zeroOriginalStatement ∧
  Variable.no_equivalent_AUCOriginalStatement ∧
  Variable.sixth_stabilityOriginalStatement ∧
  Variable.cubic_stabilityOriginalStatement ∧
  Variable.weak_tailOriginalStatement


-- @@ L92-92 verbatim
end RecursivePotentials


-- @@ L94-94 verbatim
namespace ComparatorModel.RecursivePotentials


-- @@ L96-97 verbatim
local instance canonicalHeads : FiniteRootedTree.Heads.{0} where
  initial := by intro ι _ T v; exact _root_.OAI.RecursivePotentials.FiniteRootedTree.head_initial T v


-- @@ L99-102 verbatim
local instance canonicalTree : TreeVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.TreeVector.normCore
  coordinate_bound := _root_.OAI.RecursivePotentials.FiniteRootedTree.abs_coordinate_le_normSum
  projection_bound := _root_.OAI.RecursivePotentials.FiniteRootedTree.projectHead_bound


-- @@ L104-106 verbatim
local instance canonicalZero : ZeroTreeVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.ZeroTreeVector.normCore
  half := _root_.OAI.RecursivePotentials.ZeroTreeVector.norm_half


-- @@ L108-110 verbatim
local instance canonicalAggregation : AggregationVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.AggregationVector.normCore
  coordinate_bound := _root_.OAI.RecursivePotentials.VariableTree.abs_coordinate_le_normSum


-- @@ L112-130 verbatim
local instance canonicalLp : AggregationVector.LpConstruction.{0} where
  bounds := _root_.OAI.RecursivePotentials.AggregationVector.lp_comparisons
  dense := by
    intro ι _ T e
    let f := AggregationVector.toLpLinear T e
    let V := f.range.topologicalClosure
    have hv : V = ⊤ := by
      apply top_unique
      intro x _
      exact f.range.isClosed_topologicalClosure.mem_of_tendsto
        (lp.hasSum_single ENNReal.ofReal_ne_top x)
        (Filter.Eventually.of_forall fun S => V.sum_mem fun i hi =>
          f.range.le_topologicalClosure ⟨Finsupp.single i (x i), by
            change ((Finsupp.lsum ℝ) (fun s : ι => lp.lsingle (𝕜 := ℝ)
              (E := fun _ : ι => ℝ) (ENNReal.ofReal e.val) s)) (Finsupp.single i (x i)) = _
            simp⟩)
    intro x
    have hm : x ∈ V := by rw [hv]; trivial
    exact hm


-- @@ L132-134 verbatim
private theorem rootStatement_iff {ι : Type} [DecidableEq ι] (T : FiniteRootedTree ι) :
    RootSumCompletionStatement T ↔ _root_.OAI.RecursivePotentials.RootSumCompletionStatement T := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption


-- @@ L136-138 verbatim
private theorem zeroStatement_iff {ι : Type} [DecidableEq ι] (T : FiniteRootedTree ι) :
    ZeroRootCompletionStatement T ↔ _root_.OAI.RecursivePotentials.ZeroRootCompletionStatement T := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption


-- @@ L140-142 verbatim
private theorem sourceNormStatement_iff (h : ℕ+) :
    Variable.SourceNormStatement h ↔ _root_.OAI.RecursivePotentials.Variable.SourceNormStatement h := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption


-- @@ L144-144 verbatim
private theorem result0_iff : rec_mainStatement ↔ _root_.OAI.RecursivePotentials.rec_mainOriginalStatement := Iff.rfl


-- @@ L146-148 verbatim
private theorem result1_iff : rec_completionStatement ↔ _root_.OAI.RecursivePotentials.rec_completionOriginalStatement := by
  simp only [rec_completionStatement, _root_.OAI.RecursivePotentials.rec_completionOriginalStatement, rootStatement_iff, zeroStatement_iff]
  rfl


-- @@ L150-150 verbatim
private theorem result2_iff : stop_all_radiiStatement ↔ _root_.OAI.RecursivePotentials.stop_all_radiiOriginalStatement := Iff.rfl


-- @@ L152-155 verbatim
private theorem result3_iff : XJoined_separated_familiesStatement ↔ _root_.OAI.RecursivePotentials.XJoined_separated_familiesOriginalStatement := Iff.rfl

-- Compare the finite-rank projections pointwise, so the statement comparison does not
-- repeatedly unfold the completion and operator-space instances.

-- @@ L156-157 verbatim
private theorem variableCoordinate_eq (s : Variable.Node) :
    Variable.coordinate s = _root_.OAI.RecursivePotentials.Variable.coordinate s := rfl


-- @@ L159-160 verbatim
private theorem variableBasis_eq (s : Variable.Node) :
    Variable.basis s = _root_.OAI.RecursivePotentials.Variable.basis s := rfl


-- @@ L162-164 verbatim
private theorem variableProjection_apply (S : Finset Variable.Node) (x : Variable.Xv) :
    Variable.projection S x = ∑ s ∈ S, Variable.coordinate s x • Variable.basis s := by
  simp only [Variable.projection, sum_apply, ContinuousLinearMap.smulRight_apply]


-- @@ L166-173 verbatim
private theorem originalVariableProjection_apply
    (S : Finset _root_.OAI.RecursivePotentials.Variable.Node)
    (x : _root_.OAI.RecursivePotentials.Variable.Xv) :
    _root_.OAI.RecursivePotentials.Variable.projection S x =
      ∑ s ∈ S, _root_.OAI.RecursivePotentials.Variable.coordinate s x •
        _root_.OAI.RecursivePotentials.Variable.basis s := by
  simp only [_root_.OAI.RecursivePotentials.Variable.projection, sum_apply,
    ContinuousLinearMap.smulRight_apply]


-- @@ L175-177 verbatim
private theorem variableAddCommMonoid_eq :
    (inferInstance : AddCommMonoid Variable.Xv) =
      (inferInstance : AddCommMonoid _root_.OAI.RecursivePotentials.Variable.Xv) := rfl


-- @@ L179-181 verbatim
private theorem variableModule_eq :
    (inferInstance : Module ℝ Variable.Xv) =
      (inferInstance : Module ℝ _root_.OAI.RecursivePotentials.Variable.Xv) := rfl


-- @@ L183-189 verbatim
private theorem variableProjection_sum_eq (S : Finset Variable.Node) (x : Variable.Xv) :
    (∑ s ∈ S, Variable.coordinate s x • Variable.basis s) =
      (∑ s ∈ S, _root_.OAI.RecursivePotentials.Variable.coordinate s x •
        _root_.OAI.RecursivePotentials.Variable.basis s) := by
  simp +instances only [variableAddCommMonoid_eq, variableModule_eq,
    variableCoordinate_eq, variableBasis_eq]
  rfl


-- @@ L191-194 verbatim
private theorem variableProjection_apply_eq (S : Finset Variable.Node) (x : Variable.Xv) :
    Variable.projection S x = _root_.OAI.RecursivePotentials.Variable.projection S x :=
  (variableProjection_apply S x).trans
    ((variableProjection_sum_eq S x).trans (originalVariableProjection_apply S x).symm)


-- @@ L196-198 verbatim
private theorem variableProjection_eq (S : Finset Variable.Node) :
    Variable.projection S = _root_.OAI.RecursivePotentials.Variable.projection S :=
  ContinuousLinearMap.ext (variableProjection_apply_eq S)


-- @@ L200-204 verbatim
private theorem variableProjection_toLinearMap_eq (S : Finset Variable.Node) :
    (Variable.projection S : Variable.Xv →ₗ[ℝ] Variable.Xv) =
      (_root_.OAI.RecursivePotentials.Variable.projection S :
        _root_.OAI.RecursivePotentials.Variable.Xv →ₗ[ℝ] _root_.OAI.RecursivePotentials.Variable.Xv) :=
  congrArg (fun T : Variable.Xv →L[ℝ] Variable.Xv => T.toLinearMap) (variableProjection_eq S)


-- @@ L206-210 verbatim
private theorem variableProjection_finiteDimensional_iff (S : Finset Variable.Node) :
    FiniteDimensional ℝ (Variable.projection S).range ↔
      FiniteDimensional ℝ (_root_.OAI.RecursivePotentials.Variable.projection S).range :=
  (congrArg (fun T : Variable.Xv →ₗ[ℝ] Variable.Xv => FiniteDimensional ℝ T.range)
    (variableProjection_toLinearMap_eq S)).to_iff


-- @@ L212-216 verbatim
private theorem variableFiniteTotalSupport_iff (x : Variable.Xv) :
    Variable.FiniteTotalSupport x ↔ _root_.OAI.RecursivePotentials.Variable.FiniteTotalSupport x := by
  simp only [Variable.FiniteTotalSupport, _root_.OAI.RecursivePotentials.Variable.FiniteTotalSupport,
    variableCoordinate_eq]
  rfl


-- @@ L218-222 verbatim
private theorem result4_iff : Variable.spaceStatement ↔ _root_.OAI.RecursivePotentials.Variable.spaceOriginalStatement := by
  simp only [Variable.spaceStatement, _root_.OAI.RecursivePotentials.Variable.spaceOriginalStatement,
    sourceNormStatement_iff, variableProjection_finiteDimensional_iff, variableProjection_eq,
    variableCoordinate_eq, variableFiniteTotalSupport_iff]
  rfl


-- @@ L224-224 verbatim
private theorem result5_iff : Variable.lp_model_exactStatement ↔ _root_.OAI.RecursivePotentials.Variable.lp_model_exactOriginalStatement := Iff.rfl


-- @@ L226-226 verbatim
private theorem result6_iff : Variable.one_sided_modulus_zeroStatement ↔ _root_.OAI.RecursivePotentials.Variable.one_sided_modulus_zeroOriginalStatement := Iff.rfl


-- @@ L228-228 verbatim
private theorem result7_iff : Variable.no_equivalent_AUCStatement ↔ _root_.OAI.RecursivePotentials.Variable.no_equivalent_AUCOriginalStatement := Iff.rfl


-- @@ L230-230 verbatim
private theorem result8_iff : Variable.sixth_stabilityStatement ↔ _root_.OAI.RecursivePotentials.Variable.sixth_stabilityOriginalStatement := Iff.rfl


-- @@ L232-232 verbatim
private theorem result9_iff : Variable.cubic_stabilityStatement ↔ _root_.OAI.RecursivePotentials.Variable.cubic_stabilityOriginalStatement := Iff.rfl


-- @@ L234-234 verbatim
private theorem result10_iff : Variable.weak_tailStatement ↔ _root_.OAI.RecursivePotentials.Variable.weak_tailOriginalStatement := Iff.rfl


-- @@ L236-248 verbatim
private theorem results_iff_original :
    (rec_mainStatement ∧
    rec_completionStatement ∧
    stop_all_radiiStatement ∧
    XJoined_separated_familiesStatement ∧
    Variable.spaceStatement ∧
    Variable.lp_model_exactStatement ∧
    Variable.one_sided_modulus_zeroStatement ∧
    Variable.no_equivalent_AUCStatement ∧
    Variable.sixth_stabilityStatement ∧
    Variable.cubic_stabilityStatement ∧
    Variable.weak_tailStatement) ↔ _root_.OAI.RecursivePotentials.OriginalResults := by
  exact and_congr result0_iff (and_congr result1_iff (and_congr result2_iff (and_congr result3_iff (and_congr result4_iff (and_congr result5_iff (and_congr result6_iff (and_congr result7_iff (and_congr result8_iff (and_congr result9_iff (result10_iff))))))))))


-- @@ L250-257 verbatim
/-- Packaging the construction obligations preserves the original eleven statements. -/
theorem main_iff_original : MainClaim ↔ _root_.OAI.RecursivePotentials.OriginalResults := by
  constructor
  · rintro ⟨_, _, _, _, _, h⟩
    exact results_iff_original.mp h
  · intro h
    exact ⟨canonicalHeads, canonicalTree, canonicalZero, canonicalAggregation, canonicalLp,
      results_iff_original.mpr h⟩


-- @@ L259-261 verbatim
theorem main : MainClaim := by
  apply main_iff_original.mpr
  exact ⟨@_root_.OAI.RecursivePotentials.rec_main, @_root_.OAI.RecursivePotentials.rec_completion, @_root_.OAI.RecursivePotentials.stop_all_radii, @_root_.OAI.RecursivePotentials.XJoined_separated_families, @_root_.OAI.RecursivePotentials.Variable.space, @_root_.OAI.RecursivePotentials.Variable.lp_model_exact, @_root_.OAI.RecursivePotentials.Variable.one_sided_modulus_zero, @_root_.OAI.RecursivePotentials.Variable.no_equivalent_AUC, @_root_.OAI.RecursivePotentials.Variable.sixth_stability, @_root_.OAI.RecursivePotentials.Variable.cubic_stability, @_root_.OAI.RecursivePotentials.Variable.weak_tail⟩


-- @@ L263-263 verbatim
end ComparatorModel.RecursivePotentials


-- @@ L265-265 verbatim
end


-- @@ L267-267 verbatim
end OAI
