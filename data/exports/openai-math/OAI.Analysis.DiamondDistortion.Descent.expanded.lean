import OAI.Analysis.DiamondDistortion.HeadProjections


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical Topology

-- @@ L9-9 verbatim
open Set


-- @@ L11-11 verbatim
namespace DiamondDistortion


-- @@ L13-13 verbatim
open scoped ENNReal


-- @@ L15-15 verbatim
namespace PathModel

-- @@ L16-16 verbatim
open RecursiveModel DirectLayers SignCube

-- @@ L17-24 verbatim
/-- Ancestral coordinate projections for the literal linear path cost are
    contractive, jointly cofinal, and nested in both orders. -/
theorem linear_regular : Regular linearHeads where
  nonempty := head_nonempty
  upper := head_upper
  nested_left H K hHK x := linearData.projection_nested H.val K.val hHK x
  nested_right H K hHK x := linearData.projection_nested_right H.val K.val hHK x
  contractive := linear_projection_contractive


-- @@ L26-31 verbatim
theorem adaptive_graph (C : ℝ) (hin : SignInput linearHeads.projection C)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace)
    (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ)/16 ≤ C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ∧
      C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ≤ C*(D^2+1) :=
  DirectLayers.adaptive_graph linearHeads linear_regular hin k f hf


-- @@ L33-36 verbatim
theorem predictable_495_graph (hin : PredictableInput linearHeads.projection 495)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace)
    (hf : Diamond.HasDistortion k f D s) : (k:ℝ)/4 ≤ 495*(D+1)^2 :=
  DirectLayers.predictable_graph linearHeads linear_regular hin k f hf


-- @@ L38-41 verbatim
theorem variation_252_graph (hin : PredictableInput linearHeads.projection 252)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace)
    (hf : Diamond.HasDistortion k f D s) : (k:ℝ)/(16*D^2) ≤ 1008 :=
  DirectLayers.variation_graph linearHeads linear_regular hin k f hf


-- @@ L43-48 verbatim
theorem leakage_1024_graph (hin : LeakageInput linearHeads.projection)
    {D s : ℝ} (k : ℕ) (hk : 1 ≤ k) (f : Diamond.Vertex k → LinearSpace)
    (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ)/8 ≤ 1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ∧
      1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ≤ 1024*(D^2+1) :=
  DirectLayers.leakage_graph linearHeads linear_regular hin k hk f hf


-- @@ L50-58 verbatim
theorem squared_gap_400_graph (hin : GapInput linearHeads.projection)
    {D s γ : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace)
    (hf : Diamond.HasDistortion k f D s) (hγ : 0 < γ)
    (hγa : γ < (2/D)/8) (hγk : γ < 1/((k:ℝ)+1)) :
    ∃ T : Protocol LinearSpace ForestHead k,
      T.Martingale ∧ T.Nested ∧ T.Anchored ∧ T.CommonHeads ∧ T.Supported linearHeads.projection ∧
      T.terminalEnergy ≤ 4 ∧ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 ≤ T.terminalEnergy ∧
      (k:ℝ)*((2/D)/8)^2/400 ≤ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 :=
  DirectLayers.gap_graph linearHeads linear_regular hin k f hf hγ hγa hγk

-- @@ L59-59 verbatim
end PathModel


-- @@ L61-61 verbatim
namespace DirectSegmentApplications


-- @@ L63-66 verbatim
theorem deterministic_descent {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → ForestDual)
    (hf : Diamond.HasDistortion k f D s) : (k:ℝ) ≤ 256*D^2 := by
  have h := headline.1 k f D s hf
  nlinarith [sq_nonneg D]


-- @@ L68-80 verbatim
theorem bin_descent {D : ℝ} (k : ℕ) (hk : 1 ≤ k) (f : Diamond.Vertex k → ForestDual)
    (hl : ∀ u v,Diamond.distance k u v ≤ ‖f u-f v‖)
    (hu : ∀ u v,‖f u-f v‖ ≤ D*Diamond.distance k u v) : Real.sqrt (k:ℝ)/144 < D := by
  have hsl := Diamond.slope_lower f (s := 1) (by simpa only [one_mul] using hl) (Diamond.baseEdge k)
  have hsu := Diamond.slope_upper f hu (Diamond.baseEdge k)
  have hD : 1 ≤ D := le_trans hsl hsu
  have hdist : Diamond.HasDistortion k f D 1 := ⟨hD,by norm_num,by simpa only [one_mul,mul_one] using fun u v => And.intro (hl u v) (hu u v)⟩
  have hh := headline.1 k f D 1 hdist
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hsp := Real.sqrt_nonneg (k:ℝ)
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk
  apply (div_lt_iff₀ (by norm_num : (0:ℝ)<144)).mpr
  nlinarith

-- @@ L81-81 verbatim
end DirectSegmentApplications


-- @@ L83-83 verbatim
namespace Diamond

-- @@ L84-84 verbatim
variable {X : Type*} [NormedAddCommGroup X]

-- @@ L85-101 verbatim
/-- The redundant conventional condition D≥1 follows from the
    all-pairs inequalities alone; thus HasDistortion adds no standing hypothesis. -/
lemma hasDistortion_iff_all_pairs {k : ℕ} (f : Vertex k → X) (D s : ℝ) :
    HasDistortion k f D s ↔ 0 < s ∧ ∀ u v,
      s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ D*s*distance k u v := by
  constructor
  · exact fun h => h.2
  · rintro ⟨hs,h⟩
    have hh := (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).1.trans
      (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).2
    rw [distance_edge] at hh
    have hp : 0 < s*(1/(2:ℝ)^k) := by positivity
    have hD : 1 ≤ D := (mul_le_mul_iff_left₀ hp).mp (by calc
      (1:ℝ)*(s*(1/(2:ℝ)^k)) = s*(1/(2:ℝ)^k) := one_mul _
      _ ≤ D*s*(1/(2:ℝ)^k) := hh
      _ = D*(s*(1/(2:ℝ)^k)) := by ring)
    exact ⟨hD,hs,h⟩

-- @@ L102-102 verbatim
end Diamond


-- @@ L104-115 verbatim
theorem headline_all_pairs :
    (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) ∧
    (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) := by
  constructor
  · intro k f D s hs h
    exact headline.1 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)
  · intro k f D s hs h
    exact headline.2 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)


-- @@ L117-126 verbatim
theorem direct_atomic_obstruction_positive :
    ¬ ∃ D : ℝ,∀ k : ℕ,1 ≤ k → ∃ (f : Diamond.Vertex k → ForestDual) (s : ℝ),
      0 < s ∧ ∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v := by
  rintro ⟨D,h⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (4*D^2)
  obtain ⟨f,s,hs,hf⟩ := h (n+1) (by omega)
  have hh := headline_all_pairs.1 (n+1) f D s hs hf
  push_cast at hh
  nlinarith


-- @@ L128-128 verbatim
end DiamondDistortion


-- @@ L130-130 verbatim
end


-- @@ L132-132 verbatim
end OAI
