import Mathlib.Topology.MetricSpace.HausdorffDistance
import SphereEversion.Local.OneJet


-- @@ L4-16 verbatim
/-!
# Local partial differential relations and their formal solutions

This file defines `RelLoc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : RelLoc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `FormalSol R`.
(FIXME(grunweg): `sol` is never mentioned; is this docstring outdated?)

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `HtpyJetSet E F` (homotopies of 1-jet sections).
-/



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function Real Filter


-- @@ L23-23 verbatim
open scoped unitInterval Topology


-- @@ L25-27 verbatim
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L29-31 verbatim
/-- A first order relation for maps between real vector spaces. -/
abbrev RelLoc :=
  Set (OneJet E F)


-- @@ L33-33 verbatim
instance : Membership (E × F × (E →L[ℝ] F)) (RelLoc E F) := by delta RelLoc; infer_instance


-- @@ L35-35 verbatim
variable {E F}


-- @@ L37-40 verbatim
/-- A predicate stating that a 1-jet section is a formal solution to a first order relation for
maps between vector spaces. -/
def JetSec.IsFormalSol (𝓕 : JetSec E F) (R : RelLoc E F) : Prop :=
  ∀ x, (x, 𝓕.f x, 𝓕.φ x) ∈ R


-- @@ L42-42 verbatim
namespace RelLoc


-- @@ L44-47 verbatim
/-- A formal solution to a local relation `R`. -/
@[ext]
structure FormalSol (R : RelLoc E F) extends JetSec E F where
  is_sol : ∀ x, (x, f x, φ x) ∈ R


-- @@ L49-49 verbatim
attribute [coe] FormalSol.toJetSec


-- @@ L51-54 verbatim
instance (R : RelLoc E F) : CoeOut (FormalSol R) (JetSec E F) :=
  ⟨FormalSol.toJetSec⟩

-- Note: syntactic tautology

-- @@ L55-58 verbatim
@[simp]
theorem FormalSol.toJetSec_eq_coe {R : RelLoc E F} (𝓕 : FormalSol R) :
    𝓕.toJetSec = (𝓕 : JetSec E F) :=
  rfl


-- @@ L60-63 verbatim
@[simp]
theorem FormalSol.coeIsFormalSol {R : RelLoc E F} (𝓕 : FormalSol R) :
    (𝓕 : JetSec E F).IsFormalSol R :=
  𝓕.is_sol


-- @@ L65-68 verbatim
/-- Bundling a formal solution from a 1-jet section that is a formal solution. -/
def _root_.JetSec.IsFormalSol.formalSol {𝓕 : JetSec E F} {R : RelLoc E F} (h : 𝓕.IsFormalSol R) :
    FormalSol R :=
  { 𝓕 with is_sol := h }


-- @@ L70-75 verbatim
instance (R : RelLoc E F) : FunLike (FormalSol R) E (F × (E →L[ℝ] F)) :=
  ⟨fun 𝓕 x ↦ (𝓕.f x, 𝓕.φ x),
  by
     intros 𝓕 𝓕' h
     ext x : 2 <;> replace h := Prod.mk_inj.mp <| congrFun h x
     exacts [h.1, h.2]⟩


-- @@ L77-79 verbatim
@[simp]
theorem FormalSol.coe_apply {R : RelLoc E F} (𝓕 : FormalSol R) (x : E) : (𝓕 : JetSec E F) x = 𝓕 x :=
  rfl


-- @@ L81-81 verbatim
variable {R : RelLoc E F}


-- @@ L83-85 verbatim
theorem FormalSol.eq_iff {𝓕 𝓕' : FormalSol R} {x : E} :
    𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
  JetSec.eq_iff


-- @@ L87-91 expanded
/-- A formal solution (f, φ) is holonomic at `x` if the differential of `f` at `x` is `φ x`. -/
def FormalSol.IsHolonomicAt (𝓕 : FormalSol R) (x : E) : Prop :=
  (fderiv ℝ) 𝓕.f x = 𝓕.φ x


-- @@ L92-101 expanded
theorem FormalSol.isHolonomicAt_congr (𝓕 𝓕' : FormalSol R) {s : Set E}
    (h : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ s) x, 𝓕 x = 𝓕' x) :
    expand_binders% (p => Filter.Eventually p <| 𝓝ˢ s) x, 𝓕.IsHolonomicAt x ↔ 𝓕'.IsHolonomicAt x :=
  by
  apply h.eventually_nhdsSet.mono
  intro x hx
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply hx.mono
    simp_rw [RelLoc.FormalSol.eq_iff]
    tauto
  unfold RelLoc.FormalSol.IsHolonomicAt
  rw [hf.fderiv_eq, (RelLoc.FormalSol.eq_iff.mp hx.self_of_nhds).2]


-- @@ L103-106 verbatim
/-- A family of formal solutions is a 1-parameter family of formal solutions. -/
@[ext]
structure FamilyFormalSol (R : RelLoc E F) extends FamilyJetSec E F P where
  is_sol : ∀ t x, (x, f t x, φ t x) ∈ R


-- @@ L108-111 verbatim
/-- A homotopy of formal solutions is a 1-parameter family of formal solutions. -/
@[reducible]
def HtpyFormalSol (R : RelLoc E F) :=
  R.FamilyFormalSol ℝ


-- @@ L113-114 verbatim
def HtpyFormalSol.toHtpyJetSec {R : RelLoc E F} (𝓕 : R.HtpyFormalSol) : HtpyJetSec E F :=
  𝓕.toFamilyJetSec


-- @@ L116-116 verbatim
open RelLoc


-- @@ L118-122 verbatim
instance (R : RelLoc E F) : FunLike (FamilyFormalSol P R) P (JetSec E F) :=
  ⟨fun S ↦ S.toFamilyJetSec, by
      intros S S' h
      ext p x : 3 <;> replace h := congrFun h p
      exacts [congrFun (JetSec.ext_iff.1 h).1 x, congrFun (JetSec.ext_iff.1 h).2 x]⟩


-- @@ L124-124 verbatim
end RelLoc
