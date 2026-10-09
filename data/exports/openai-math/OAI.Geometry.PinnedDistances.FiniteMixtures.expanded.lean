import OAI.Geometry.PinnedDistances.EmpiricalCompactness


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5 u6 u7


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open MeasureTheory Filter

-- @@ L10-10 verbatim
open scoped BigOperators Topology ENNReal

-- @@ L11-11 verbatim
namespace WeakPinned.Bounded


-- @@ L13-14 verbatim
variable {I : Type u1} {V : Type u2} {X : Type u3} {Y : Type u4} [Fintype I] [Fintype V]
  [MeasurableSpace X] [MeasurableSpace Y]


-- @@ L16-25 verbatim
lemma finiteLaw_fst (w : I → ℝ) (p : I → V → ℝ) (U : I → X)
    (hw : ∀ i,0≤w i) (hp : ∀ i x,0≤p i x) (hpsum : ∀ i,∑ x,p i x=1) :
    finiteLaw (edgeWeight w p) (fun r => U r.1)=finiteLaw w U := by
  unfold finiteLaw edgeWeight
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (hw i) (hp i x)),
    ← Finset.mul_sum,hpsum,mul_one]


-- @@ L27-43 verbatim
lemma tripleLaw_edge (w : I → ℝ) (p : I → V → ℝ) (U : I × V → X)
    (hw : ∀ i,0≤w i) (hp : ∀ i x,0≤p i x) (hpsum : ∀ i,∑ x,p i x=1) :
    finiteLaw (tripleWeight w p) (fun r => U (r.1,r.2.1))=finiteLaw (edgeWeight w p) U := by
  unfold finiteLaw tripleWeight edgeWeight
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  rw [show (∑ z,∑ t, ENNReal.ofReal (w i*p i x*p i z*p i t) • Measure.dirac (U (i,x))) =
    ∑ z,ENNReal.ofReal (w i*p i x*p i z) • Measure.dirac (U (i,x)) by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)) (hp i t)),
        ← Finset.mul_sum,hpsum,mul_one]]
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)),
    ← Finset.mul_sum,hpsum,mul_one]


-- @@ L45-53 verbatim
lemma finiteLaw_mono (w v : I → ℝ) (U : I → X) (hle : ∀ i,w i≤v i) :
    finiteLaw w U≤finiteLaw v U := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [finiteLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  gcongr
  exact hle i


-- @@ L55-61 verbatim
lemma finiteLaw_prod (w : I → ℝ) (v : V → ℝ) (U : I → X) (W : V → Y)
    (hw : ∀ i,0≤w i) :
    (finiteLaw w U).prod (finiteLaw v W)=
      finiteLaw (fun r : I × V => w r.1*v r.2) (fun r => (U r.1,W r.2)) := by
  simp only [finiteLaw,← Measure.sum_fintype,Measure.prod_sum,
    Measure.prod_smul_left,Measure.prod_smul_right,Measure.dirac_prod_dirac,
    smul_smul,ENNReal.ofReal_mul (hw _),mul_comm]


-- @@ L63-65 verbatim
lemma finiteLaw_smul (w : I → ℝ) (U : I → X) (c : ℝ) (hc : 0≤c) :
    finiteLaw (fun i => c*w i) U=ENNReal.ofReal c •finiteLaw w U := by
  simp only [finiteLaw,ENNReal.ofReal_mul hc,Finset.smul_sum,smul_smul]


-- @@ L67-67 verbatim
end WeakPinned.Bounded


-- @@ L69-69 verbatim
end

-- @@ L70-70 verbatim
end

-- @@ L71-71 verbatim
section

-- @@ L72-72 verbatim
noncomputable section

-- @@ L73-73 verbatim
open MeasureTheory Filter

-- @@ L74-74 verbatim
open scoped BigOperators Topology ENNReal

-- @@ L75-75 verbatim
namespace WeakPinned.Bounded

-- @@ L76-76 verbatim
open Variance

-- @@ L77-79 verbatim
variable {V : Type u5} {I : Type u6} {X : Type u7} [Fintype V] [DecidableEq V] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]

-- @@ L80-80 verbatim
variable (G : Core.Fibers V I)


-- @@ L82-87 verbatim
lemma graph_edge_eval (F : V → V → ℝ) :
    (∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*F (G.source e) y)=
      ∑ x,∑ y,G.edgeLaw x y*F x y := by
  rw [← G.incoming_eval]
  simp only [Finset.mul_sum,← mul_assoc,G.sampling_conditional]
  exact Finset.sum_comm


-- @@ L89-106 verbatim
lemma graph_edge_law (U : V → V → X) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) :
    finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
      (fun r => U (G.source r.1) r.2)=
    finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => U r.1 r.2) := by
  have hw (r : I × V) : 0≤edgeWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
    mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _)
  let : IsProbabilityMeasure (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
      (fun r => U (G.source r.1) r.2)) := finiteLaw_probability _ _ hw
        (sum_edgeWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))
  let : IsProbabilityMeasure (finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => U r.1 r.2)) :=
    finiteLaw_probability _ _ (fun r => G.edgeLaw_nonneg _ _)
      (by simpa only [Fintype.sum_prod_type] using G.sum_edgeLaw hG)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_finiteLaw _ _ hw,integral_finiteLaw _ _ (fun r => G.edgeLaw_nonneg _ _)]
  simp only [edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
  exact graph_edge_eval G (fun x y => f (U x y))


-- @@ L108-118 verbatim
omit G in
lemma pairProb_le_uniform (hn : 2≤Fintype.card V) (x y : V) :
    pairProb Finset.univ x y≤2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹ := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast hn
  have hn0 : (0:ℝ)<Fintype.card V := by linarith
  simp only [pairProb,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · field_simp
    apply (div_le_iff₀ (by linarith : 0<(Fintype.card V:ℝ)-1)).mpr
    nlinarith
  · positivity


-- @@ L120-132 verbatim
omit [Fintype I] [MeasurableSingletonClass X] [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
lemma graph_domination (U : V → X) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => (U r.1,U r.2))≤
      ENNReal.ofReal (2*M) • (uniformLaw U).prod (uniformLaw U) := by
  rw [uniformLaw,finiteLaw_prod _ _ _ _ (fun _ => by positivity),← finiteLaw_smul _ _ _ (by positivity)]
  apply finiteLaw_mono
  intro r
  calc
    _ ≤ M*pairProb Finset.univ r.1 r.2 := hdom _ _
    _ ≤ M*(2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (pairProb_le_uniform hn _ _) hM
    _ = _ := by ring


-- @@ L134-134 verbatim
end WeakPinned.Bounded


-- @@ L136-136 verbatim
end

-- @@ L137-137 verbatim
end


-- @@ L139-139 verbatim
end OAI
