import OAI.Combinatorics.MatrixRemoval.OrderedHost
import OAI.Combinatorics.MatrixRemoval.HostSampledSelection
import OAI.Combinatorics.MatrixRemoval.SampledPathOrder


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# The sampled selection on increasing host enumerations

The ten order assumptions of the concrete sampler follow from the independent
row and column enumerations. No order or entry certificate remains as a
hypothesis of `sampledSelection_valid`.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
namespace Problem348.OrderedHost


-- @@ L18-18 verbatim
open Construction


-- @@ L20-43 verbatim
/-- The actual row and column enumerations meet every sampler order condition. -/
theorem sampledAxisConditions (h : ℕ) :
    SampledSelection.AxisConditions (rowIndex h) (columnIndex h) := by
  constructor
  · intro t a
    exact row_anchor_strictMono t (fun _ => a)
  · intro t a
    exact column_anchor_strictMono t (fun _ => a)
  · exact row_anchor_lt_nonanchor
  · exact column_anchor_lt_nonanchor
  · exact row_variable_lt_dummy
  · exact column_dummy_lt_variable
  · intro i z u
    exact HostSampledPath.row_plus_sample_order (rowIndex h)
      (fun p q hpq => (rowIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.row_minus_sample_order (rowIndex h)
      (fun p q hpq => (rowIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.column_plus_sample_order (columnIndex h)
      (fun p q hpq => (columnIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.column_minus_sample_order (columnIndex h)
      (fun p q hpq => (columnIndex_variable_lt_iff p q).mpr hpq) i z u u


-- @@ L45-49 verbatim
/-- The three-seed selection in the concrete matrix of the prescribed size. -/
def sampledSelection {h : ℕ} (hh : 1 ≤ h) (z u v : Fin (2 ^ h)) :
    GuardedPath.Selection (size h) :=
  SampledSelection.selection hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) z u v


-- @@ L51-56 verbatim
/-- The actual sampled path and anchor frames are valid without extra inputs. -/
theorem sampledSelection_valid {h : ℕ} (hh : 1 ≤ h) (z u v : Fin (2 ^ h)) :
    (sampledSelection hh z u v).Valid
      (SelectedAnchor.matrix (rowIndex h) (columnIndex h)) h :=
  SampledSelection.selection_valid hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) z u v


-- @@ L58-58 verbatim
end Problem348.OrderedHost


-- @@ L60-60 verbatim
end


-- @@ L62-62 verbatim
end OAI
