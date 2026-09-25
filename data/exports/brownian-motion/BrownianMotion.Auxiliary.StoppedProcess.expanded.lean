module

public import BrownianMotion.Auxiliary.Indistinguishable
public import BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Process.Stopping


-- @@ L7-7 verbatim
@[expose] public section


-- @@ L9-9 verbatim
open MeasureTheory Filter

-- @@ L10-10 verbatim
open scoped ENNReal Topology


-- @@ L12-12 verbatim
namespace MeasureTheory


-- @@ L14-15 verbatim
variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X Y : ι → Ω → E}


-- @@ L17-17 verbatim
section stoppedProcess


-- @@ L19-19 verbatim
variable [LinearOrder ι]


-- @@ L21-24 verbatim
@[simp]
lemma stoppedProcess_of_eq_top (s : ι) (hτ : τ ω = ⊤) :
    stoppedProcess X τ s ω = X s ω := by
  simp [stoppedProcess, hτ]


-- @@ L26-29 verbatim
@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]


-- @@ L31-34 expanded
lemma stoppedProcess_congr (h : Indistinguishable P X Y) :
    Indistinguishable P (stoppedProcess X τ) (stoppedProcess Y τ) :=
  by
  filter_upwards [h] with ω h t
  simp [stoppedProcess, h]


-- @@ L36-36 verbatim
section Topology


-- @@ L38-38 verbatim
variable [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]


-- @@ L40-48 verbatim
/-- If a trajectory of a process is continuous, then the corresponding trajectory of the stopped
process is also continuous. -/
lemma _root_.Continuous.stoppedProcess {ω : Ω} (hX : Continuous (X · ω)) (τ : Ω → WithTop ι) :
    Continuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    fun_prop


-- @@ L50-61 verbatim
/-- If a trajectory of a process is right-continuous,
then the corresponding trajectory of the stopped process is also right-continuous. -/
lemma _root_.IsRightContinuous.stoppedProcess (hX : IsRightContinuous (X · ω)) (τ : Ω → WithTop ι) :
    IsRightContinuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    intro s
    obtain hst | hts := lt_or_ge s t
    · exact hX (min s t) |>.comp (f := (min · t)) (by fun_prop) (by grind [Set.MapsTo])
    · exact (continuous_const (y := X t ω)).continuousWithinAt.congr (by grind) (by grind)


-- @@ L63-77 verbatim
/-- If a trajectory of a process is càdlàg, then the corresponding trajectory of the stopped
process is also càdlàg. -/
lemma _root_.IsCadlag.stoppedProcess (hX : IsCadlag (X · ω)) (τ : Ω → WithTop ι) :
    IsCadlag (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    refine ⟨hX.right_continuous.stoppedProcess τ, fun s ↦ ?_⟩
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    obtain hst | hts := le_or_gt s t
    · obtain ⟨l, hl⟩ := hX.left_limit s
      exact ⟨l, hl.congr' (Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ by grind)⟩
    · refine ⟨X t ω, tendsto_const_nhds.congr' ?_⟩
      rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
      exact ⟨Set.Ioi t, by grind, isOpen_Ioi, by grind⟩


-- @@ L79-79 verbatim
end Topology


-- @@ L81-81 verbatim
end stoppedProcess


-- @@ L83-83 verbatim
namespace stoppedValue


-- @@ L85-86 verbatim
@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl


-- @@ L88-89 verbatim
@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl


-- @@ L91-92 verbatim
@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl


-- @@ L94-94 verbatim
end stoppedValue


-- @@ L96-96 verbatim
end MeasureTheory
