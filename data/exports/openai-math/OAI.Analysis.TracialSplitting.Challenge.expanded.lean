import OAI.Analysis.TracialSplitting.Main


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-6 verbatim
/-! The construction certificates are proved here, outside the self-contained challenge.
`main_iff_original` checks that packaging them preserves the original assertion. -/


-- @@ L8-8 verbatim
universe uNuclear


-- @@ L10-10 verbatim
namespace CurrentMain


-- @@ L12-12 verbatim
open Pureness Filter


-- @@ L14-22 verbatim
def OriginalGammaStatement : Prop := ∀
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (_hsimple : TopologicallySimple A) (_hinf : ¬FiniteDimensional ℂ A)
    (_hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (_hfree : (U : Filter ℕ) ≤ atTop)
    (_hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)),
    UniformPropertyGammaAt A U

-- @@ L23-23 verbatim
end CurrentMain


-- @@ L25-25 verbatim
namespace ComparatorModel.CurrentMain


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Filter


-- @@ L31-34 verbatim
local instance canonicalNorm : Pureness.ClosedStarIdeal.NormConstruction where
  mul_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_mul_le
  star_eq := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_star
  square_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_square_le


-- @@ L36-43 verbatim
local instance canonicalNull : NullConstruction where
  zero := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_zero
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_add <;> assumption
  neg := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_neg; assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_star; assumption
  mul_left := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_left <;> assumption
  mul_right := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_right <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyNull_isClosed


-- @@ L45-50 verbatim
local instance canonicalCauchy : CauchyConstruction where
  const := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_const
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_add <;> assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_star; assumption
  mul := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_mul <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyCauchyAlgebra_isClosed


-- @@ L52-53 verbatim
local instance canonicalLimit : LimitConstruction where
  tendsto := by intros; apply _root_.OAI.CurrentMain.ultraTraceValue_tendsto


-- @@ L55-59 verbatim
local instance canonicalTrace : TraceConstruction where
  null := by
    intro D I X _ _ _ _ τ _ U s u hu
    apply _root_.OAI.CurrentMain.ultraTrace_null τ U s u
    exact (_root_.OAI.CurrentMain.familyNull_mem τ (U : Filter X) u).mpr hu


-- @@ L61-63 verbatim
/-- The asserted conclusion, including all hypotheses, is definitionally unchanged. -/
theorem statement_iff_original : Statement.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := Iff.rfl


-- @@ L65-73 verbatim
/-- The existential construction requirements do not change the original assertion. -/
theorem main_iff_original : MainClaim.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := by
  constructor
  · rintro ⟨_, _, _, _, _, h⟩
    exact statement_iff_original.mp h
  · intro h
    exact ⟨canonicalNorm, canonicalNull, canonicalCauchy, canonicalLimit, canonicalTrace,
      statement_iff_original.mpr h⟩


-- @@ L75-76 verbatim
theorem main : MainClaim.{uNuclear} :=
  main_iff_original.mpr @_root_.OAI.CurrentMain.real_rank_zero_uniform_gamma


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
end ComparatorModel.CurrentMain


-- @@ L82-82 verbatim
end OAI
