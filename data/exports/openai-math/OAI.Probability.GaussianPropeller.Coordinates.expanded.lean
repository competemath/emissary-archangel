import OAI.Probability.GaussianPropeller.CapIntegral


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
open scoped RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped RealInnerProductSpace

-- @@ L11-11 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L12-12 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L13-13 verbatim
open Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L16-16 verbatim
open scoped Topology

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L20-20 verbatim
open scoped NNReal

-- @@ L21-21 verbatim
open Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L23-23 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L25-25 verbatim
open MeasureTheory Set Filter

-- @@ L26-26 verbatim
open scoped Topology BigOperators

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L31-31 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L32-32 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L33-33 verbatim
open Metric


-- @@ L35-35 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L36-36 verbatim
open scoped RealInnerProductSpace ENNReal


-- @@ L38-38 verbatim
namespace GaussianPropeller.Coords

-- @@ L39-39 verbatim
abbrev CS (n : ℕ) := EuclideanSpace ℝ (Fin n)


-- @@ L41-42 verbatim
noncomputable def split (n : ℕ) (x : CS (n+1)) : ℝ × CS n :=
  (x 0, WithLp.toLp 2 (fun i => x i.succ))

-- @@ L43-44 verbatim
noncomputable def join (n : ℕ) (y : ℝ × CS n) : CS (n+1) :=
  WithLp.toLp 2 (Fin.cons y.1 y.2.ofLp)


-- @@ L46-48 verbatim
lemma split_join (n : ℕ) (y : ℝ × CS n) : split n (join n y)=y := by
  rcases y with ⟨s,y⟩
  simp [split,join]


-- @@ L50-52 verbatim
lemma join_split (n : ℕ) (x : CS (n+1)) : join n (split n x)=x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join,split]


-- @@ L54-57 verbatim
lemma continuous_split (n : ℕ) : Continuous (split n) := by
  unfold split
  apply Continuous.prodMk (by fun_prop)
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)


-- @@ L59-66 verbatim
lemma continuous_join (n : ℕ) : Continuous (join n) := by
  unfold join
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ]
  · fun_prop
  · fun_prop


-- @@ L68-74 verbatim
noncomputable def splitEquiv (n : ℕ) : CS (n+1) ≃ᵐ ℝ × CS n where
  toFun := split n
  invFun := join n
  left_inv := join_split n
  right_inv := split_join n
  measurable_toFun := (continuous_split n).measurable
  measurable_invFun := (continuous_join n).measurable


-- @@ L76-88 verbatim
lemma split_measure (n : ℕ) :
    (stdGaussian (CS (n+1))).map (split n) = (gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).map_eq
  have he : (split n) ∘ WithLp.toLp 2 =
      (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) := by
    funext x
    rfl
  rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_split n).measurable
    (PiLp.continuous_toLp 2 _).measurable, he,
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),hm,
    ← Measure.map_prod_map _ _ measurable_id (PiLp.continuous_toLp 2 _).measurable,
    Measure.map_id,map_pi_eq_stdGaussian]


-- @@ L90-92 verbatim
lemma measurePreserving_split (n : ℕ) : MeasurePreserving (splitEquiv n)
    (stdGaussian (CS (n+1))) ((gaussianReal 0 1).prod (stdGaussian (CS n))) :=
  ⟨(continuous_split n).measurable,split_measure n⟩


-- @@ L94-97 verbatim
lemma integral_split (n : ℕ) (f : CS (n+1) → ℝ) :
    (∫ x, f x ∂stdGaussian (CS (n+1))) =
      ∫ y, f (join n y) ∂(gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  exact ((measurePreserving_split n).symm.integral_comp (splitEquiv n).symm.measurableEmbedding f).symm


-- @@ L99-101 verbatim
lemma norm_join_sq (n : ℕ) (y : ℝ × CS n) : ‖join n y‖^2 = y.1^2+‖y.2‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,join,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]


-- @@ L103-104 verbatim
lemma norm_join (n : ℕ) (y : ℝ × CS n) : ‖join n y‖ = Real.sqrt (y.1^2+‖y.2‖^2) := by
  rw [← norm_join_sq,Real.sqrt_sq (norm_nonneg _)]


-- @@ L106-106 verbatim
lemma join_zero (n : ℕ) (y : ℝ × CS n) : join n y 0 = y.1 := by simp [join]


-- @@ L108-121 verbatim
lemma exists_basis_zero {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E=n+1)
    (e : E) (he : ‖e‖=1) :
    ∃ b : OrthonormalBasis (Fin (n+1)) ℝ E, b 0=e := by
  have ho : Orthonormal ℝ (({0}:Set (Fin (n+1))).domRestrict (fun _ => e)) := by
    constructor
    · intro i; exact he
    · intro i j hij
      have hi : (i:Fin (n+1))=0 := i.2
      have hj : (j:Fin (n+1))=0 := j.2
      exact (hij (Subtype.ext (hi.trans hj.symm))).elim
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (ι:=Fin (n+1)) (by simpa using hn)
  exact ⟨b,hb 0 (by simp)⟩


-- @@ L123-123 verbatim
end GaussianPropeller.Coords


-- @@ L125-125 verbatim
end OAI
