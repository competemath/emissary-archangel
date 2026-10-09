import Mathlib


-- @@ L3-8 verbatim
/-!
# Character criterion for Jiang–Su absorption

The main statement is Theorem 1.1 of the Kirchberg–Rørdam character-criterion paper.
The constructions below specify the norm central-sequence algebra and Jiang–Su absorption.
-/


-- @@ L10-10 verbatim
namespace OAI


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
section


-- @@ L16-16 verbatim
open scoped TensorProduct InnerProductSpace BigOperators

-- @@ L17-17 verbatim
open Set Module


-- @@ L19-19 verbatim
universe uQuot

-- @@ L20-20 verbatim
namespace KirchbergRordam.QuotientNormSupport


-- @@ L22-73 verbatim
@[instance_reducible]
noncomputable def normedRing {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
    [IsClosed (I : Set R)] : NormedRing (R ⧸ I) := by
  classical
  have h_QuotientNormSupport_distance_eq  {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
      [IsClosed (I : Set R)] (x y : R ⧸ I) :
      dist x y = ‖-x + y‖ := dist_eq_norm_neg_add x y
  have h_QuotientNormSupport_multiplication_bound  {R : Type uQuot} [NormedRing R] (I : Ideal R) [I.IsTwoSided]
      [IsClosed (I : Set R)] (x y : R ⧸ I) :
      ‖x * y‖ ≤ ‖x‖ * ‖y‖ := le_of_forall_pos_le_add fun ε hε =>
    let neighborhood : ∃ radii : ℝ × ℝ, (0 < radii.1 ∧ 0 < radii.2) ∧
      ∀ point : ℝ × ℝ, (dist point.1 ‖x‖ < radii.1 ∧ dist point.2 ‖y‖ < radii.2) →
        dist (point.1 * point.2) (‖x‖ * ‖y‖) < ε :=
      ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
        Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    neighborhood.elim fun radii radii_spec =>
      (Submodule.Quotient.norm_mk_lt x radii_spec.1.1).elim fun representative_x x_spec =>
        (Submodule.Quotient.norm_mk_lt y radii_spec.1.2).elim fun representative_y y_spec =>
          let lower_x : ‖x‖ ≤ ‖representative_x‖ :=
            Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_x‖) x_spec.1)
              (Submodule.Quotient.norm_mk_le I representative_x)
          let lower_y : ‖y‖ ≤ ‖representative_y‖ :=
            Eq.mp (congrArg (fun value : R ⧸ I => ‖value‖ ≤ ‖representative_y‖) y_spec.1)
              (Submodule.Quotient.norm_mk_le I representative_y)
          let distance_x : dist ‖representative_x‖ ‖x‖ < radii.1 :=
            Eq.mpr (congrArg (fun distance : ℝ => distance < radii.1)
              (Real.dist_eq ‖representative_x‖ ‖x‖))
                (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr x_spec.2,
                  (sub_nonpos.mpr lower_x).trans_lt radii_spec.1.1⟩)
          let distance_y : dist ‖representative_y‖ ‖y‖ < radii.2 :=
            Eq.mpr (congrArg (fun distance : ℝ => distance < radii.2)
              (Real.dist_eq ‖representative_y‖ ‖y‖))
                (abs_sub_lt_iff.mpr ⟨sub_lt_iff_lt_add'.mpr y_spec.2,
                  (sub_nonpos.mpr lower_y).trans_lt radii_spec.1.2⟩)
          let product_distance :=
            radii_spec.2 (‖representative_x‖, ‖representative_y‖) ⟨distance_x, distance_y⟩
          let product_bound : ‖x * y‖ ≤ ‖representative_x‖ * ‖representative_y‖ :=
            Eq.mp (congrArg₂ (fun left right : R ⧸ I =>
              ‖left * right‖ ≤ ‖representative_x‖ * ‖representative_y‖) x_spec.1 y_spec.1)
                ((Submodule.Quotient.norm_mk_le I (representative_x * representative_y)).trans
                  (norm_mul_le representative_x representative_y))
          product_bound.trans (sub_lt_iff_lt_add'.mp (abs_sub_lt_iff.mp
            (Eq.mp (congrArg (fun distance : ℝ => distance < ε)
              (Real.dist_eq (‖representative_x‖ * ‖representative_y‖) (‖x‖ * ‖y‖)))
                product_distance)).1).le
  exact {
    toNorm := inferInstance
    toRing := inferInstance
    toMetricSpace := inferInstance
    dist_eq := h_QuotientNormSupport_distance_eq I
    norm_mul_le := h_QuotientNormSupport_multiplication_bound I
  }


-- @@ L75-75 verbatim
end KirchbergRordam.QuotientNormSupport


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
open scoped TensorProduct CStarAlgebra InnerProductSpace Matrix Kronecker ComplexOrder

-- @@ L80-80 verbatim
open UniformSpace Filter Topology BoundedContinuousFunction


-- @@ L82-82 verbatim
universe uQuot


-- @@ L84-84 verbatim
namespace KirchbergRordam.NormUltrapower


-- @@ L86-86 verbatim
variable {A : Type*} [CStarAlgebra A]


-- @@ L88-88 verbatim
abbrev BoundedSeq (A : Type*) [CStarAlgebra A] := ℕ →ᵇ A


-- @@ L90-100 verbatim
def normLimit (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : ℝ := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  exact
    (h_NormUltrapower_exists_norm_limit ω x).choose


-- @@ L102-143 verbatim
def nullIdeal (ω : Ultrafilter ℕ) : Ideal (OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_mul_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x * y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x*y))
      ((h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_mul_le (x n) (y n))
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  have h_NormUltrapower_normLimit_zero  (ω : Ultrafilter ℕ) : OAI.KirchbergRordam.NormUltrapower.normLimit ω (0 : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) = 0 := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω 0)
    simp
  exact {
    carrier := {x | OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0}
    zero_mem' := h_NormUltrapower_normLimit_zero ω
    add_mem' := by
      intro x y hx hy
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 at hx
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω y = 0 at hy
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x+y))
      simpa only [hx, hy, add_zero] using h_NormUltrapower_normLimit_add_le ω x y
    smul_mem' := by
      intro x y hy
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω y = 0 at hy
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x*y))
      simpa only [hy, mul_zero] using h_NormUltrapower_normLimit_mul_le ω x y
  }


-- @@ L145-171 verbatim
instance nullIdeal_twoSided (ω : Ultrafilter ℕ) : (OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω).IsTwoSided := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_mul_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x * y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x*y))
      ((h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_mul_le (x n) (y n))
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  exact {
    mul_mem_of_left := by
      intro x y hx
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω (x*y) = 0
      apply le_antisymm _ (h_NormUltrapower_normLimit_nonneg ω (x*y))
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 at hx
      simpa only [hx, zero_mul] using h_NormUltrapower_normLimit_mul_le ω x y
  }


-- @@ L173-208 verbatim
instance nullIdeal_closed (ω : Ultrafilter ℕ) : IsClosed (OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω : Set (OAI.KirchbergRordam.NormUltrapower.BoundedSeq A)) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_normLimit_le  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖x‖ :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.2
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_sub_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x - OAI.KirchbergRordam.NormUltrapower.normLimit ω y ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) := by
    have h := h_NormUltrapower_normLimit_add_le ω (x-y) y
    rw [sub_add_cancel] at h
    linarith
  have h_NormUltrapower_normLimit_lipschitz  (ω : Ultrafilter ℕ) :
      LipschitzWith 1 (OAI.KirchbergRordam.NormUltrapower.normLimit ω : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le, dist_eq_norm]
    constructor
    · have h := (h_NormUltrapower_normLimit_sub_le ω y x).trans (h_NormUltrapower_normLimit_le ω (y-x))
      rw [norm_sub_rev] at h
      linarith
    · exact (h_NormUltrapower_normLimit_sub_le ω x y).trans (h_NormUltrapower_normLimit_le ω (x-y))
  exact
    isClosed_eq (h_NormUltrapower_normLimit_lipschitz ω).continuous continuous_const


-- @@ L210-211 verbatim
abbrev Algebra (A : Type*) [CStarAlgebra A] (ω : Ultrafilter ℕ) :=
  OAI.KirchbergRordam.NormUltrapower.BoundedSeq A ⧸ OAI.KirchbergRordam.NormUltrapower.nullIdeal (A := A) ω


-- @@ L213-215 verbatim
noncomputable instance quotientNormedRing {R : Type uQuot} [NormedRing R] (I : Ideal R)
    [I.IsTwoSided] [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  KirchbergRordam.QuotientNormSupport.normedRing I


-- @@ L217-218 verbatim
instance quotientNormedAlgebra (ω : Ultrafilter ℕ) : NormedAlgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  norm_smul_le := norm_smul_le


-- @@ L220-242 verbatim
instance quotientStar (ω : Ultrafilter ℕ) : Star (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_star  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (star x))
    simp [h_NormUltrapower_tendsto_norm]
  exact {
    star := Quotient.map' star fun x y h => by
      rw [Submodule.quotientRel_def] at h ⊢
      change OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x - star y) = 0
      rw [← star_sub, h_NormUltrapower_normLimit_star]
      exact h
  }


-- @@ L244-256 verbatim
instance quotientStarRing (ω : Ultrafilter ℕ) : StarRing (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  star_involutive := by
    rintro ⟨x⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (star x)) = Ideal.Quotient.mk _ x
    rw [star_star]
  star_mul := by
    rintro ⟨x⟩ ⟨y⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (x*y)) = Ideal.Quotient.mk _ (star y * star x)
    rw [star_mul]
  star_add := by
    rintro ⟨x⟩ ⟨y⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (x+y)) = Ideal.Quotient.mk _ (star x + star y)
    rw [star_add]


-- @@ L258-263 verbatim
instance quotientStarModule (ω : Ultrafilter ℕ) : StarModule ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where
  star_smul := by
    intro z
    rintro ⟨x⟩
    change Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (star (z • x)) = Ideal.Quotient.mk _ (star z • star x)
    rw [star_smul]


-- @@ L265-270 verbatim
def cutRepresentative (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A :=
  ofNormedAddCommGroupDiscrete (fun n => if ‖x n‖ < c then x n else 0) c (by
    intro n
    split_ifs with h
    · exact h.le
    · simpa only [norm_zero] using hc)


-- @@ L272-368 verbatim
instance quotientCStarRing (ω : Ultrafilter ℕ) : CStarRing (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) := by
  classical
  have h_NormUltrapower_exists_norm_limit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ∃ r ∈ Set.Icc (0 : ℝ) ‖x‖, Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 r) := by
    obtain ⟨r, hr, h⟩ := isCompact_Icc.ultrafilter_le_nhds'
      (Ultrafilter.map (fun n => ‖x n‖) ω) (by
        change ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ ∈ Set.Icc (0 : ℝ) ‖x‖
        exact Eventually.of_forall fun n => ⟨norm_nonneg _, x.norm_coe_le_norm n⟩)
    exact ⟨r, hr, h⟩
  have h_NormUltrapower_tendsto_norm  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 (OAI.KirchbergRordam.NormUltrapower.normLimit ω x)) :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.2
  have h_NormUltrapower_normLimit_star_mul  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (star x * x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x * OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (star x * x))
    simpa only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply,
      CStarRing.norm_star_mul_self] using (h_NormUltrapower_tendsto_norm ω x).mul (h_NormUltrapower_tendsto_norm ω x)
  have h_NormUltrapower_normLimit_neg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (-x) = OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω (-x))
    simp [h_NormUltrapower_tendsto_norm]
  have h_NormUltrapower_normLimit_add_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω (x + y) ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    exact le_of_tendsto_of_tendsto (h_NormUltrapower_tendsto_norm ω (x+y))
      ((h_NormUltrapower_tendsto_norm ω x).add (h_NormUltrapower_tendsto_norm ω y))
      (Eventually.of_forall fun n => norm_add_le (x n) (y n))
  have h_NormUltrapower_normLimit_sub_le  (ω : Ultrafilter ℕ) (x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x - OAI.KirchbergRordam.NormUltrapower.normLimit ω y ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) := by
    have h := h_NormUltrapower_normLimit_add_le ω (x-y) y
    rw [sub_add_cancel] at h
    linarith
  have h_NormUltrapower_normLimit_eq_of_sub_mem  (ω : Ultrafilter ℕ) {x y : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A}
      (h : x-y ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x = OAI.KirchbergRordam.NormUltrapower.normLimit ω y := by
    change OAI.KirchbergRordam.NormUltrapower.normLimit ω (x-y) = 0 at h
    apply le_antisymm
    · have h' := h_NormUltrapower_normLimit_sub_le ω x y
      linarith
    · have h' := h_NormUltrapower_normLimit_sub_le ω y x
      rw [← neg_sub x y, h_NormUltrapower_normLimit_neg, h] at h'
      linarith
  have h_NormUltrapower_normLimit_le  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖x‖ :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.2
  have h_NormUltrapower_normLimit_le_quotient  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      OAI.KirchbergRordam.NormUltrapower.normLimit ω x ≤ ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ := by
    apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have h : y-x ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω := (Ideal.Quotient.eq).mp hy
    rw [← h_NormUltrapower_normLimit_eq_of_sub_mem ω h]
    exact h_NormUltrapower_normLimit_le ω y
  have h_NormUltrapower_mem_nullIdeal  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      x ∈ OAI.KirchbergRordam.NormUltrapower.nullIdeal ω ↔ Tendsto (fun n => ‖x n‖) (ω : Filter ℕ) (𝓝 0) := by
    change OAI.KirchbergRordam.NormUltrapower.normLimit ω x = 0 ↔ _
    constructor
    · intro h
      simpa only [h] using h_NormUltrapower_tendsto_norm ω x
    · exact fun h => tendsto_nhds_unique (h_NormUltrapower_tendsto_norm ω x) h
  have h_NormUltrapower_cutRepresentative_mk_eq  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A)
      (c : ℝ) (hc : 0 ≤ c) (hlim : OAI.KirchbergRordam.NormUltrapower.normLimit ω x < c) :
      Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x =
        Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) (OAI.KirchbergRordam.NormUltrapower.cutRepresentative x c hc) := by
    rw [Ideal.Quotient.eq, h_NormUltrapower_mem_nullIdeal]
    have he : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c :=
      (h_NormUltrapower_tendsto_norm ω x).eventually (eventually_lt_nhds hlim)
    have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0) := tendsto_const_nhds
    apply hz.congr'
    filter_upwards [he] with n hn
    change (0 : ℝ) = ‖x n - (if ‖x n‖ < c then x n else 0)‖
    rw [ite_eq_left hn, sub_self, norm_zero]
  have h_NormUltrapower_cutRepresentative_norm_le  (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) :
      ‖OAI.KirchbergRordam.NormUltrapower.cutRepresentative x c hc‖ ≤ c := by
    apply (BoundedContinuousFunction.norm_le hc).mpr
    intro n
    change ‖if ‖x n‖ < c then x n else 0‖ ≤ c
    split_ifs with h
    · exact h.le
    · simpa only [norm_zero] using hc
  have h_NormUltrapower_normLimit_nonneg  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    (h_NormUltrapower_exists_norm_limit ω x).choose_spec.1.1
  have h_NormUltrapower_quotient_norm_le_normLimit  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 ≤ OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε := add_nonneg (h_NormUltrapower_normLimit_nonneg ω x) hε.le
    rw [h_NormUltrapower_cutRepresentative_mk_eq ω x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos (lt_add_of_pos_right _ hε)]
    have hb := Submodule.Quotient.norm_mk_le (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω)
      (OAI.KirchbergRordam.NormUltrapower.cutRepresentative x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos)
    exact hb.trans (h_NormUltrapower_cutRepresentative_norm_le x (OAI.KirchbergRordam.NormUltrapower.normLimit ω x + ε) hpos)
  have h_NormUltrapower_norm_mk_eq  (ω : Ultrafilter ℕ) (x : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A) :
      ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ = OAI.KirchbergRordam.NormUltrapower.normLimit ω x :=
    le_antisymm (h_NormUltrapower_quotient_norm_le_normLimit ω x) (h_NormUltrapower_normLimit_le_quotient ω x)
  exact {
    norm_mul_self_le := by
      rintro ⟨x⟩
      change ‖Ideal.Quotient.mk (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω) x‖ * ‖Ideal.Quotient.mk _ x‖ ≤
        ‖Ideal.Quotient.mk _ (star x * x)‖
      rw [h_NormUltrapower_norm_mk_eq, h_NormUltrapower_norm_mk_eq, h_NormUltrapower_normLimit_star_mul]
  }


-- @@ L370-370 verbatim
instance quotientCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) where


-- @@ L372-374 verbatim
def quotientMap (ω : Ultrafilter ℕ) : OAI.KirchbergRordam.NormUltrapower.BoundedSeq A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.Algebra A ω where
  __ := Ideal.Quotient.mkₐ ℂ (OAI.KirchbergRordam.NormUltrapower.nullIdeal ω)
  map_star' _ := rfl


-- @@ L376-383 verbatim
def constantSeq : A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.BoundedSeq A where
  toFun := BoundedContinuousFunction.const ℕ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


-- @@ L385-386 verbatim
def diagonal (ω : Ultrafilter ℕ) : A →⋆ₐ[ℂ] OAI.KirchbergRordam.NormUltrapower.Algebra A ω :=
  (OAI.KirchbergRordam.NormUltrapower.quotientMap ω).comp OAI.KirchbergRordam.NormUltrapower.constantSeq


-- @@ L388-389 verbatim
def centralSubalgebra (ω : Ultrafilter ℕ) : StarSubalgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) :=
  StarSubalgebra.centralizer ℂ (Set.range (OAI.KirchbergRordam.NormUltrapower.diagonal (A := A) ω))


-- @@ L391-393 verbatim
instance centralSubalgebra_closed (ω : Ultrafilter ℕ) :
    IsClosed (OAI.KirchbergRordam.NormUltrapower.centralSubalgebra (A := A) ω : Set (OAI.KirchbergRordam.NormUltrapower.Algebra A ω)) :=
  Set.isClosed_centralizer _


-- @@ L395-396 verbatim
abbrev CentralAlgebra (A : Type*) [CStarAlgebra A] (ω : Ultrafilter ℕ) :=
  OAI.KirchbergRordam.NormUltrapower.centralSubalgebra (A := A) ω


-- @@ L398-400 verbatim
instance centralSubringClass (ω : Ultrafilter ℕ) :
    SubringClass (StarSubalgebra ℂ (OAI.KirchbergRordam.NormUltrapower.Algebra A ω)) (OAI.KirchbergRordam.NormUltrapower.Algebra A ω) :=
  StarSubalgebra.subringClass (R := ℂ) (A := OAI.KirchbergRordam.NormUltrapower.Algebra A ω)


-- @@ L402-403 verbatim
instance centralCStarAlgebra (ω : Ultrafilter ℕ) : CStarAlgebra (OAI.KirchbergRordam.NormUltrapower.CentralAlgebra A ω) :=
  StarSubalgebra.cstarAlgebra _


-- @@ L405-405 verbatim
end KirchbergRordam.NormUltrapower


-- @@ L407-407 verbatim
namespace KirchbergRordam

-- @@ L408-408 verbatim
namespace StarCompletion


-- @@ L410-410 verbatim
open UniformSpace

-- @@ L411-411 verbatim
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]


-- @@ L413-413 verbatim
instance completionStar : Star (Completion R) := ⟨Completion.map (star : R → R)⟩


-- @@ L415-416 verbatim
instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map


-- @@ L418-435 verbatim
instance completionStarRing : StarRing (Completion R) := by
  classical
  have h_StarCompletion_star_coe  (x : R) : star (x : Completion R) = (star x : R) :=
    Completion.map_coe star_isometry.uniformContinuous x
  exact {
    star_involutive x := by
      induction x using Completion.induction_on with
      | hp => exact isClosed_eq (continuous_star.comp continuous_star) continuous_id
      | ih x => simp only [h_StarCompletion_star_coe, star_star]
    star_mul x y := by
      induction x, y using Completion.induction_on₂ with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih x y => simp only [← Completion.coe_mul, h_StarCompletion_star_coe, star_mul]
    star_add x y := by
      induction x, y using Completion.induction_on₂ with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih x y => simp only [← Completion.coe_add, h_StarCompletion_star_coe, star_add]
  }


-- @@ L437-437 verbatim
variable [NormedAlgebra ℂ R] [StarModule ℂ R]


-- @@ L439-440 verbatim
instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le


-- @@ L442-455 verbatim
instance completionStarModule : StarModule ℂ (Completion R) := by
  classical
  have h_StarCompletion_star_coe  (x : R) : star (x : Completion R) = (star x : R) :=
    Completion.map_coe star_isometry.uniformContinuous x
  exact {
    star_smul z x := by
      induction x using Completion.induction_on with
      | hp =>
        exact isClosed_eq
          (continuous_star.comp (continuous_const_smul z))
          ((continuous_const_smul (star z)).comp continuous_star)
      | ih x =>
        rw [← Completion.coe_smul, h_StarCompletion_star_coe, star_smul, Completion.coe_smul, h_StarCompletion_star_coe]
  }


-- @@ L457-457 verbatim
end StarCompletion


-- @@ L459-459 verbatim
end KirchbergRordam


-- @@ L461-461 verbatim
namespace KirchbergRordam.CStarInductiveLimit

-- @@ L462-462 verbatim
universe u


-- @@ L464-471 verbatim
structure System where
  obj : ℕ → Type u
  [cstar : ∀ n, CStarAlgebra (obj n)]
  map : ∀ i j, i ≤ j → obj i →⋆ₐ[ℂ] obj j
  map_self : ∀ i x, map i i le_rfl x = x
  map_map : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
    map j k hjk (map i j hij x) = map i k (hij.trans hjk) x
  norm_map : ∀ i j (h : i ≤ j) x, ‖map i j h x‖ = ‖x‖


-- @@ L473-473 verbatim
attribute [instance] System.cstar


-- @@ L475-477 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : DirectedSystem S.obj (S.map · · ·) where
  map_self := fun {_} x => S.map_self _ x
  map_map := fun {_ _ _} hij hjk x => S.map_map _ _ _ hij hjk x


-- @@ L479-479 verbatim
def Raw (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) := DirectLimit S.obj S.map


-- @@ L481-481 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : Ring (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (Ring (DirectLimit S.obj S.map))


-- @@ L483-483 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : Algebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (Algebra ℂ (DirectLimit S.obj S.map))


-- @@ L485-485 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : StarRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (StarRing (DirectLimit S.obj S.map))


-- @@ L487-487 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : StarModule ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := inferInstanceAs (StarModule ℂ (DirectLimit S.obj S.map))


-- @@ L489-491 verbatim
def rawOf (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) : S.obj n →⋆ₐ[ℂ] OAI.KirchbergRordam.CStarInductiveLimit.Raw S where
  __ := DirectLimit.Algebra.of S.obj S.map n
  map_star' _ := rfl


-- @@ L493-494 verbatim
def normLift (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : OAI.KirchbergRordam.CStarInductiveLimit.Raw S → ℝ :=
  DirectLimit.lift S.map (fun _ x => ‖x‖) (fun i j h x => (S.norm_map i j h x).symm)


-- @@ L496-536 verbatim
def ringNorm (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : RingNorm (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  exact {
    toFun := OAI.KirchbergRordam.CStarInductiveLimit.normLift S
    map_zero' := by
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (0 : DirectLimit S.obj S.map) = 0
      rw [DirectLimit.zero_def (f := S.map) 0]
      exact norm_zero
    add_le' := by
      intro x y
      refine DirectLimit.induction₂ S.map ?_ x y
      intro n x y
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x + OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y) ≤
        OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) + OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y)
      rw [← map_add, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk]
      exact norm_add_le x y
    neg' := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (-OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x)
      rw [← map_neg, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, norm_neg]
    mul_le' := by
      intro x y
      refine DirectLimit.induction₂ S.map ?_ x y
      intro n x y
      change OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x * OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y) ≤
        OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) * OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n y)
      rw [← map_mul, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk, h_CStarInductiveLimit_normLift_mk]
      exact norm_mul_le x y
    eq_zero_of_map_eq_zero' := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x hx
      change ‖x‖ = 0 at hx
      rw [norm_eq_zero] at hx
      change OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x = 0
      rw [hx, map_zero]
  }


-- @@ L538-538 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := (OAI.KirchbergRordam.CStarInductiveLimit.ringNorm S).toNormedRing


-- @@ L540-554 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedAlgebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_smul_le z := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖z • OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ ≤ ‖z‖ * ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_smul, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf]
      exact norm_smul_le z x
  }


-- @@ L556-569 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : NormedStarGroup (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_star_le := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖star (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x)‖ ≤ ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_star, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf, norm_star]
  }


-- @@ L571-585 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Raw S) := by
  classical
  have h_CStarInductiveLimit_normLift_mk  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      OAI.KirchbergRordam.CStarInductiveLimit.normLift S (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) = ‖x‖ := rfl
  have h_CStarInductiveLimit_norm_rawOf  (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) (n : ℕ) (x : S.obj n) :
      ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ = ‖x‖ := rfl
  exact {
    norm_mul_self_le := by
      intro x
      refine DirectLimit.induction S.map ?_ x
      intro n x
      change ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ * ‖OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖ ≤ ‖star (OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x) * OAI.KirchbergRordam.CStarInductiveLimit.rawOf S n x‖
      rw [← map_star, ← map_mul, h_CStarInductiveLimit_norm_rawOf, h_CStarInductiveLimit_norm_rawOf]
      exact CStarRing.norm_mul_self_le x
  }


-- @@ L587-587 verbatim
abbrev Algebra (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) := UniformSpace.Completion (OAI.KirchbergRordam.CStarInductiveLimit.Raw S)


-- @@ L589-599 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S) := by
  classical
  have h_StarCompletion_star_coe (x : Raw S) : star (x : Completion (Raw S)) = ((star x : Raw S) : Completion (Raw S)) := Completion.map_coe star_isometry.uniformContinuous x
  exact {
    norm_mul_self_le x := by
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih x =>
        rw [(h_StarCompletion_star_coe), ← UniformSpace.Completion.coe_mul]
        simpa only [UniformSpace.Completion.norm_coe] using CStarRing.norm_mul_self_le x
  }


-- @@ L601-607 verbatim
instance (S : OAI.KirchbergRordam.CStarInductiveLimit.System.{u}) : CStarAlgebra (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S) :=
  { (inferInstance : NormedRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : NormedAlgebra ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : CompleteSpace (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : StarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : StarModule ℂ (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)),
    (inferInstance : CStarRing (OAI.KirchbergRordam.CStarInductiveLimit.Algebra S)) with }


-- @@ L609-613 verbatim
structure Chain where
  obj : ℕ → Type u
  [cstar : ∀ n, CStarAlgebra (obj n)]
  step : ∀ n, obj n →⋆ₐ[ℂ] obj (n+1)
  norm_step : ∀ n x, ‖step n x‖ = ‖x‖


-- @@ L615-615 verbatim
attribute [instance] Chain.cstar


-- @@ L617-619 verbatim
def Chain.map (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) : S.obj i →⋆ₐ[ℂ] S.obj j :=
  Nat.leRecOn (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n) h
    (fun {n} φ => (S.step n).comp φ) (StarAlgHom.id ℂ _)


-- @@ L621-649 verbatim
def Chain.system (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) : OAI.KirchbergRordam.CStarInductiveLimit.System.{u} := by
  classical
  have h_CStarInductiveLimit_Chain_map_self  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i : ℕ) :
      S.map i i le_rfl = StarAlgHom.id ℂ _ := by simp [Chain.map, Nat.leRecOn_self]
  have h_CStarInductiveLimit_Chain_map_succ  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) :
      S.map i (j+1) (h.trans (Nat.le_succ j)) = (S.step j).comp (S.map i j h) := by
    exact Nat.leRecOn_succ (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n)
      (next := fun {n} φ => (S.step n).comp φ) h (StarAlgHom.id ℂ (S.obj i))
  have h_CStarInductiveLimit_Chain_map_map  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
      (x : S.obj i) : S.map j k hjk (S.map i j hij x) = S.map i k (hij.trans hjk) x := by
    induction k, hjk using Nat.le_induction with
    | base => simp [h_CStarInductiveLimit_Chain_map_self]
    | succ k hjk ih =>
      rw [(h_CStarInductiveLimit_Chain_map_succ S j k hjk), (h_CStarInductiveLimit_Chain_map_succ S i k (LE.le.trans hij hjk))]
      exact congrArg (S.step k) ih
  have h_CStarInductiveLimit_Chain_norm_map  (S : OAI.KirchbergRordam.CStarInductiveLimit.Chain.{u}) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
      ‖S.map i j h x‖ = ‖x‖ := by
    induction j, h using Nat.le_induction with
    | base => simp [h_CStarInductiveLimit_Chain_map_self]
    | succ j h ih =>
      rw [(h_CStarInductiveLimit_Chain_map_succ S i j h)]
      exact (S.norm_step j (S.map i j h x)).trans ih
  exact {
    obj := S.obj
    map := S.map
    map_self i x := by simp [h_CStarInductiveLimit_Chain_map_self]
    map_map := (h_CStarInductiveLimit_Chain_map_map S)
    norm_map := (h_CStarInductiveLimit_Chain_norm_map S)
  }


-- @@ L651-651 verbatim
end KirchbergRordam.CStarInductiveLimit


-- @@ L653-653 verbatim
namespace KirchbergRordam.MaxTensor

-- @@ L654-654 verbatim
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


-- @@ L656-660 verbatim
structure CrossSeminorm extends Seminorm ℂ (A ⊗[ℂ] B) where
  mul_le : ∀ x y, toSeminorm (x * y) ≤ toSeminorm x * toSeminorm y
  star_eq : ∀ x, toSeminorm (star x) = toSeminorm x
  cstar_eq : ∀ x, toSeminorm (star x * x) = toSeminorm x * toSeminorm x
  tmul_le : ∀ a b, toSeminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖


-- @@ L662-667 verbatim
instance : Inhabited (OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B) := ⟨{
  toSeminorm := 0
  mul_le := by simp
  star_eq := by simp
  cstar_eq := by simp
  tmul_le := by intro a b; simp only [zero_apply]; positivity }⟩


-- @@ L669-669 verbatim
variable {A B}


-- @@ L671-671 verbatim
def Raw (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] := A ⊗[ℂ] B


-- @@ L673-673 verbatim
instance : Ring (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (Ring (A ⊗[ℂ] B))


-- @@ L675-675 verbatim
instance : Algebra ℂ (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))


-- @@ L677-677 verbatim
instance : StarRing (OAI.KirchbergRordam.MaxTensor.Raw A B) := inferInstanceAs (StarRing (A ⊗[ℂ] B))


-- @@ L679-680 verbatim
def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] OAI.KirchbergRordam.MaxTensor.Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)


-- @@ L682-682 verbatim
variable {C : Type*} [CStarAlgebra C]


-- @@ L684-695 verbatim
def liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : OAI.KirchbergRordam.MaxTensor.Raw A B →⋆ₐ[ℂ] C where
  toAlgHom := _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h
  map_star' x := by
    change _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h (star x) =
      star (_root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [star_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change φ (star a) * ψ (star b) = star (φ a * ψ b)
      rw [star_mul, ← map_star, ← map_star]
      exact h (star a) (star b)


-- @@ L697-723 verbatim
def representationSeminorm (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B := by
  classical
  have h_MaxTensor_liftRaw_tmul  (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
      (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
      OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl
  exact {
    toSeminorm := (normSeminorm ℂ C).comp (OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h).toLinearMap
    mul_le x y := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x * OAI.KirchbergRordam.MaxTensor.rawEquiv y)‖ ≤
        ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ * ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv y)‖
      rw [map_mul]
      exact norm_mul_le _ _
    star_eq x := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (star (OAI.KirchbergRordam.MaxTensor.rawEquiv x))‖ = ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖
      rw [map_star, norm_star]
    cstar_eq x := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (star (OAI.KirchbergRordam.MaxTensor.rawEquiv x) * OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ =
        ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖ * ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (OAI.KirchbergRordam.MaxTensor.rawEquiv x)‖
      rw [map_mul, map_star, CStarRing.norm_star_mul_self]
    tmul_le a b := by
      change ‖OAI.KirchbergRordam.MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖
      rw [h_MaxTensor_liftRaw_tmul]
      exact (norm_mul_le _ _).trans (mul_le_mul
        (NonUnitalStarAlgHom.norm_apply_le φ a) (NonUnitalStarAlgHom.norm_apply_le ψ b)
        (norm_nonneg _) (norm_nonneg _))
  }


-- @@ L725-725 verbatim
end KirchbergRordam.MaxTensor


-- @@ L727-727 verbatim
namespace KirchbergRordam.Spatial

-- @@ L728-728 verbatim
open Set Module NormedSpace

-- @@ L729-729 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L731-732 verbatim
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


-- @@ L734-735 verbatim
abbrev Hilbert (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (H ⊗[ℂ] K)


-- @@ L737-738 verbatim
def map (T : H →L[ℂ] H) (S : K →L[ℂ] K) : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K :=
  (TensorProduct.mapL T S).completion


-- @@ L740-740 verbatim
variable [CompleteSpace H] [CompleteSpace K]


-- @@ L742-810 verbatim
def left : (H →L[ℂ] H) →⋆ₐ[ℂ] (OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K) := by
  classical
  have h_Spatial_ext  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_add_left__simp_1_1 (a b : H ⊗[ℂ] K) : (a : Completion (H ⊗[ℂ] K)) + (b : Completion (H ⊗[ℂ] K)) = ((a + b : H ⊗[ℂ] K) : Completion (H ⊗[ℂ] K)) := (Completion.coe_add a b).symm
  have h_Spatial_map_coe  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_add_left  (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T + U) S = OAI.KirchbergRordam.Spatial.map T S + OAI.KirchbergRordam.Spatial.map U S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_add_left, (@h_Spatial_map_add_left__simp_1_1)]
  have h_Spatial_map_mul  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_map_one  : OAI.KirchbergRordam.Spatial.map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
      show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]
  have h_Spatial_map_smul_left  (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (z • T) S = z • OAI.KirchbergRordam.Spatial.map T S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_smul_left, ← Completion.coe_smul]
  have h_Spatial_map_inner_algebraic  (T : H →L[ℂ] H) (S : K →L[ℂ] K)
      (x y : H ⊗[ℂ] K) :
      ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
        ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
      | tmul c d =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h_Spatial_map_inner  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : OAI.KirchbergRordam.Spatial.Hilbert H K) :
      ⟪OAI.KirchbergRordam.Spatial.map (star T) (star S) x, y⟫_ℂ = ⟪x, OAI.KirchbergRordam.Spatial.map T S y⟫_ℂ := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simpa [h_Spatial_map_coe] using h_Spatial_map_inner_algebraic T S x y
  have h_Spatial_map_star  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (star T) (star S) = star (OAI.KirchbergRordam.Spatial.map T S) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [h_Spatial_map_inner, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  exact {
    toFun T := OAI.KirchbergRordam.Spatial.map T 1
    map_zero' := by apply h_Spatial_ext; intro x; simp [OAI.KirchbergRordam.Spatial.map]
    map_one' := h_Spatial_map_one
    map_add' T U := h_Spatial_map_add_left T U 1
    map_mul' T U := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_mul T U (1 : K →L[ℂ] K) 1
    commutes' z := by
      change OAI.KirchbergRordam.Spatial.map (z • 1) 1 = z • 1
      rw [h_Spatial_map_smul_left, h_Spatial_map_one]
    map_star' T := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_star T (1 : K →L[ℂ] K)
  }


-- @@ L812-880 verbatim
def right : (K →L[ℂ] K) →⋆ₐ[ℂ] (OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K) := by
  classical
  have h_Spatial_ext  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_add_right__simp_1_1 (a b : H ⊗[ℂ] K) : (a : Completion (H ⊗[ℂ] K)) + (b : Completion (H ⊗[ℂ] K)) = ((a + b : H ⊗[ℂ] K) : Completion (H ⊗[ℂ] K)) := (Completion.coe_add a b).symm
  have h_Spatial_map_coe  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_add_right  (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T (S + U) = OAI.KirchbergRordam.Spatial.map T S + OAI.KirchbergRordam.Spatial.map T U := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_add_right, (@h_Spatial_map_add_right__simp_1_1)]
  have h_Spatial_map_mul  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_map_one  : OAI.KirchbergRordam.Spatial.map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
      show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]
  have h_Spatial_map_smul_right  (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T (z • S) = z • OAI.KirchbergRordam.Spatial.map T S := by
    apply h_Spatial_ext
    intro x
    simp [h_Spatial_map_coe, TensorProduct.mapL_smul_right, ← Completion.coe_smul]
  have h_Spatial_map_inner_algebraic  (T : H →L[ℂ] H) (S : K →L[ℂ] K)
      (x y : H ⊗[ℂ] K) :
      ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
        ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
      | tmul c d =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h_Spatial_map_inner  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : OAI.KirchbergRordam.Spatial.Hilbert H K) :
      ⟪OAI.KirchbergRordam.Spatial.map (star T) (star S) x, y⟫_ℂ = ⟪x, OAI.KirchbergRordam.Spatial.map T S y⟫_ℂ := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simpa [h_Spatial_map_coe] using h_Spatial_map_inner_algebraic T S x y
  have h_Spatial_map_star  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (star T) (star S) = star (OAI.KirchbergRordam.Spatial.map T S) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [h_Spatial_map_inner, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  exact {
    toFun S := OAI.KirchbergRordam.Spatial.map 1 S
    map_zero' := by apply h_Spatial_ext; intro x; simp [OAI.KirchbergRordam.Spatial.map]
    map_one' := h_Spatial_map_one
    map_add' T U := h_Spatial_map_add_right 1 T U
    map_mul' T U := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_mul (1 : H →L[ℂ] H) 1 T U
    commutes' z := by
      change OAI.KirchbergRordam.Spatial.map 1 (z • 1) = z • 1
      rw [h_Spatial_map_smul_right, h_Spatial_map_one]
    map_star' S := by simpa [h_Spatial_map_coe, h_Spatial_map_one] using h_Spatial_map_star (1 : H →L[ℂ] H) S
  }


-- @@ L882-882 verbatim
end KirchbergRordam.Spatial


-- @@ L884-884 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L885-885 verbatim
open scoped TensorProduct

-- @@ L886-886 verbatim
universe u

-- @@ L887-887 verbatim
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]


-- @@ L889-899 verbatim
structure RepresentationPair where
  H : Type u
  K : Type u
  normH : NormedAddCommGroup H
  innerH : InnerProductSpace ℂ H
  completeH : CompleteSpace H
  normK : NormedAddCommGroup K
  innerK : InnerProductSpace ℂ K
  completeK : CompleteSpace K
  leftRep : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  rightRep : B →⋆ₐ[ℂ] (K →L[ℂ] K)


-- @@ L901-903 verbatim
attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK

-- @@ L904-904 verbatim
variable {A B}

-- @@ L905-907 verbatim
def RepresentationPair.left (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    A →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  Spatial.left.comp ρ.leftRep


-- @@ L909-911 verbatim
def RepresentationPair.right (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  Spatial.right.comp ρ.rightRep


-- @@ L913-942 verbatim
def RepresentationPair.crossSeminorm (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) :
    MaxTensor.CrossSeminorm A B := by
  classical
  have h_Spatial_ext {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  {T S : OAI.KirchbergRordam.Spatial.Hilbert H K →L[ℂ] OAI.KirchbergRordam.Spatial.Hilbert H K}
      (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq T.continuous S.continuous
    | ih x => exact h x
  have h_Spatial_map_coe {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map T S (x : OAI.KirchbergRordam.Spatial.Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
    simp [OAI.KirchbergRordam.Spatial.map]
  have h_Spatial_map_mul {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K]  (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
      OAI.KirchbergRordam.Spatial.map (T * U) (S * V) = OAI.KirchbergRordam.Spatial.map T S * OAI.KirchbergRordam.Spatial.map U V := by
    apply h_Spatial_ext
    intro x
    simp only [mul_apply_eq_comp, h_Spatial_map_coe, TensorProduct.mapL_mul]
  have h_Spatial_left_right_commute {H : Type u} {K : Type u} [inst2 : NormedAddCommGroup H] [inst3 : InnerProductSpace ℂ H] [inst4 : NormedAddCommGroup K] [inst5 : InnerProductSpace ℂ K] [inst6 : CompleteSpace H] [inst7 : CompleteSpace K]  (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
      Commute (OAI.KirchbergRordam.Spatial.left (K := K) T) (OAI.KirchbergRordam.Spatial.right (H := H) S) := by
    change OAI.KirchbergRordam.Spatial.map T 1 * OAI.KirchbergRordam.Spatial.map 1 S = OAI.KirchbergRordam.Spatial.map 1 S * OAI.KirchbergRordam.Spatial.map T 1
    rw [← h_Spatial_map_mul, ← h_Spatial_map_mul]
    simp
  have h_MinTensor_RepresentationPair_commute  (ρ : OAI.KirchbergRordam.MinTensor.RepresentationPair A B) (a : A) (b : B) :
      Commute (ρ.left a) (ρ.right b) :=
    (@h_Spatial_left_right_commute) _ _
  exact
    MaxTensor.representationSeminorm (A := A) (B := B)
        (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K))
        ρ.left ρ.right (h_MinTensor_RepresentationPair_commute ρ)


-- @@ L944-946 verbatim
def spatialIndex : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B) → MaxTensor.CrossSeminorm A B
  | none => default
  | some ρ => ρ.crossSeminorm


-- @@ L948-949 verbatim
def seminorm : Seminorm ℂ (A ⊗[ℂ] B) :=
  ⨆ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm


-- @@ L951-951 verbatim
end KirchbergRordam.MinTensor

-- @@ L952-952 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L953-953 verbatim
open scoped TensorProduct

-- @@ L954-954 verbatim
open Set Module NormedSpace

-- @@ L955-955 verbatim
universe u

-- @@ L956-956 verbatim
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L957-958 verbatim
local instance instRingTensorProductComplex_analysis : Ring (A ⊗[ℂ] B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)


-- @@ L960-960 verbatim
end KirchbergRordam.MinTensor


-- @@ L962-962 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L963-963 verbatim
universe u

-- @@ L964-964 verbatim
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]


-- @@ L966-966 verbatim
def Raw : Type u := A ⊗[ℂ] B


-- @@ L968-968 verbatim
variable {A B}

-- @@ L969-970 verbatim
instance : Ring (OAI.KirchbergRordam.MinTensor.Raw A B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)


-- @@ L972-972 verbatim
instance : Algebra ℂ (OAI.KirchbergRordam.MinTensor.Raw A B) := _root_.Algebra.TensorProduct.instAlgebra


-- @@ L974-975 verbatim
instance instStarRingRaw : StarRing (OAI.KirchbergRordam.MinTensor.Raw A B) :=
  inferInstanceAs (StarRing (MaxTensor.Raw A B))


-- @@ L977-1020 verbatim
def rawRingSeminorm : RingSeminorm (OAI.KirchbergRordam.MinTensor.Raw A B) := by
  classical
  have h_MaxTensor_bounded_at {A : Type u} {B : Type u} [inst2 : CStarAlgebra A] [inst3 : CStarAlgebra B]  (x : A ⊗[ℂ] B) :
      ∃ C : ℝ, ∀ p : OAI.KirchbergRordam.MaxTensor.CrossSeminorm A B, p.toSeminorm x ≤ C := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact ⟨‖a‖ * ‖b‖, fun p => p.tmul_le a b⟩
    | add x y hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, fun p => (map_add_le_add p.toSeminorm x y).trans
          (add_le_add (hC p) (hD p))⟩
  have h_MinTensor_bounded  : BddAbove (Set.range (fun ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B) =>
      (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm)) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    obtain ⟨C,hC⟩ := (@h_MaxTensor_bounded_at) x
    exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
  have h_MinTensor_seminorm_apply  (x : A ⊗[ℂ] B) :
      OAI.KirchbergRordam.MinTensor.seminorm x=⨆ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x :=
    Seminorm.iSup_apply h_MinTensor_bounded
  have h_MinTensor_le_seminorm  (ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B)) (x : A ⊗[ℂ] B) :
      (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x ≤ OAI.KirchbergRordam.MinTensor.seminorm x := by
    rw [h_MinTensor_seminorm_apply]
    apply le_ciSup _ ρ
    obtain ⟨C,hC⟩ := (@h_MaxTensor_bounded_at) x
    exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩
  have h_MinTensor_seminorm_le  {x : A ⊗[ℂ] B} {C : ℝ}
      (h : ∀ ρ : Option (OAI.KirchbergRordam.MinTensor.RepresentationPair A B), (OAI.KirchbergRordam.MinTensor.spatialIndex ρ).toSeminorm x ≤ C) :
      OAI.KirchbergRordam.MinTensor.seminorm x ≤ C := by
    rw [h_MinTensor_seminorm_apply]
    exact ciSup_le h
  have h_MinTensor_seminorm_mul_le  (x y : A ⊗[ℂ] B) :
      @LE.le ℝ Real.instLE
        (OAI.KirchbergRordam.MinTensor.seminorm (@Mul.mul (A ⊗[ℂ] B)
          (_root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)).toMul x y))
        (@Mul.mul ℝ Real.instMul (OAI.KirchbergRordam.MinTensor.seminorm x) (OAI.KirchbergRordam.MinTensor.seminorm y)) := by
    apply h_MinTensor_seminorm_le
    intro ρ
    exact ((OAI.KirchbergRordam.MinTensor.spatialIndex ρ).mul_le x y).trans (mul_le_mul (h_MinTensor_le_seminorm ρ x)
      (h_MinTensor_le_seminorm ρ y) (apply_nonneg _ _) (apply_nonneg _ _))
  exact {
    __ := (OAI.KirchbergRordam.MinTensor.seminorm (A := A) (B := B)).toAddGroupSeminorm
    mul_le' := h_MinTensor_seminorm_mul_le
  }


-- @@ L1022-1022 verbatim
instance : SeminormedRing (OAI.KirchbergRordam.MinTensor.Raw A B) := OAI.KirchbergRordam.MinTensor.rawRingSeminorm.toSeminormedRing


-- @@ L1024-1025 verbatim
abbrev Algebra (A B : Type u) [CStarAlgebra A] [CStarAlgebra B] :=
  UniformSpace.Completion (OAI.KirchbergRordam.MinTensor.Raw A B)


-- @@ L1027-1027 verbatim
end KirchbergRordam.MinTensor


-- @@ L1029-1029 verbatim
namespace KirchbergRordam.MatrixTensor

-- @@ L1030-1030 verbatim
open scoped Matrix Kronecker

-- @@ L1031-1031 verbatim
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- @@ L1032-1032 verbatim
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ


-- @@ L1034-1048 verbatim
def leftMatrixAlgebra : Matrix ι ι ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix κ κ ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix κ κ ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


-- @@ L1050-1064 verbatim
def rightMatrixAlgebra : Matrix κ κ ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := (1 : Matrix ι ι ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix ι ι ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


-- @@ L1066-1068 verbatim
def leftMatrix : OAI.KirchbergRordam.MatrixTensor.Mat ι →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixTensor.Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (OAI.KirchbergRordam.MatrixTensor.leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


-- @@ L1070-1072 verbatim
def rightMatrix : OAI.KirchbergRordam.MatrixTensor.Mat κ →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixTensor.Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (OAI.KirchbergRordam.MatrixTensor.rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


-- @@ L1074-1074 verbatim
end KirchbergRordam.MatrixTensor


-- @@ L1076-1076 verbatim
namespace KirchbergRordam.PrimeDimensionDrop

-- @@ L1077-1077 verbatim
open MatrixTensor

-- @@ L1078-1078 verbatim
open scoped Matrix Kronecker ComplexOrder CStarAlgebra


-- @@ L1080-1080 verbatim
abbrev Fiber (p q : ℕ) := OAI.KirchbergRordam.MatrixTensor.Mat (Fin p × Fin q)


-- @@ L1082-1090 verbatim
def eval (p q : ℕ) (t : unitInterval) :
    C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ] OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


-- @@ L1092-1094 verbatim
def subalgebra (p q : ℕ) : StarSubalgebra ℂ C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  (OAI.KirchbergRordam.MatrixTensor.leftMatrix (ι := Fin p) (κ := Fin q)).range.comap (OAI.KirchbergRordam.PrimeDimensionDrop.eval p q 0) ⊓
    (OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι := Fin p) (κ := Fin q)).range.comap (OAI.KirchbergRordam.PrimeDimensionDrop.eval p q 1)


-- @@ L1096-1097 verbatim
instance (p q : ℕ) : FiniteDimensional ℂ (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ))


-- @@ L1099-1107 verbatim
instance (p q : ℕ) : IsClosed (OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q : Set C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) := by
  change IsClosed ((fun f : C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) => f 0) ⁻¹'
    ((OAI.KirchbergRordam.MatrixTensor.leftMatrix (ι := Fin p) (κ := Fin q)).range : Set (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) ∩
    (fun f : C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) => f 1) ⁻¹'
    ((OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι := Fin p) (κ := Fin q)).range : Set (OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)))
  exact ((OAI.KirchbergRordam.MatrixTensor.leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((OAI.KirchbergRordam.MatrixTensor.rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))


-- @@ L1109-1109 verbatim
abbrev Algebra (p q : ℕ) := OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q


-- @@ L1111-1113 verbatim
instance (p q : ℕ) : SubringClass
    (StarSubalgebra ℂ C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q)) C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, OAI.KirchbergRordam.PrimeDimensionDrop.Fiber p q))


-- @@ L1115-1115 verbatim
instance (p q : ℕ) : CStarAlgebra (OAI.KirchbergRordam.PrimeDimensionDrop.Algebra p q) := StarSubalgebra.cstarAlgebra (OAI.KirchbergRordam.PrimeDimensionDrop.subalgebra p q)


-- @@ L1117-1117 verbatim
end KirchbergRordam.PrimeDimensionDrop


-- @@ L1119-1119 verbatim
namespace KirchbergRordam.UnitaryPaths


-- @@ L1121-1121 verbatim
variable {A : Type*} [CStarAlgebra A]


-- @@ L1123-1123 verbatim
def phase (t : unitInterval) : ℂ := Complex.exp (((t:ℝ) * Real.pi) * Complex.I)


-- @@ L1125-1126 verbatim
def involutionValue (U : A) (t : unitInterval) : A :=
  ((1 + OAI.KirchbergRordam.UnitaryPaths.phase t) / 2) • (1:A) + ((1 - OAI.KirchbergRordam.UnitaryPaths.phase t) / 2) • U


-- @@ L1128-1183 verbatim
def involutionPath (U : unitary A) (hs : star (U:A) = U) : Path 1 U := by
  classical
  have h_UnitaryPaths_phase_continuous  : Continuous OAI.KirchbergRordam.UnitaryPaths.phase := by unfold OAI.KirchbergRordam.UnitaryPaths.phase; fun_prop
  have h_UnitaryPaths_involutionValue_continuous  (U : A) : Continuous (OAI.KirchbergRordam.UnitaryPaths.involutionValue U) := by
    unfold OAI.KirchbergRordam.UnitaryPaths.involutionValue
    fun_prop
  have h_UnitaryPaths_phase_unitary  (t : unitInterval) : star (OAI.KirchbergRordam.UnitaryPaths.phase t) * OAI.KirchbergRordam.UnitaryPaths.phase t = 1 := by
    have hn : ‖OAI.KirchbergRordam.UnitaryPaths.phase t‖ = 1 := by
      simpa [OAI.KirchbergRordam.UnitaryPaths.phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I ((t:ℝ) * Real.pi)
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have h_UnitaryPaths_involutionValue_unitary  (U : A) (hs : star U = U) (hm : U * U = 1)
      (t : unitInterval) : OAI.KirchbergRordam.UnitaryPaths.involutionValue U t ∈ unitary A := by
    have hz := h_UnitaryPaths_phase_unitary t
    have h1 : (star ((1:ℂ)+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
        (star ((1:ℂ)-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)=1 := by
      simp only [star_add,star_sub,star_one]
      calc
        _ = (1+star (OAI.KirchbergRordam.UnitaryPaths.phase t)*OAI.KirchbergRordam.UnitaryPaths.phase t)/2 := by ring
        _ = 1 := by rw [hz]; norm_num
    have h2 : (star ((1:ℂ)+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
        (star ((1:ℂ)-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)=0 := by
      simp only [star_add,star_sub,star_one]
      calc
        _ = (1-star (OAI.KirchbergRordam.UnitaryPaths.phase t)*OAI.KirchbergRordam.UnitaryPaths.phase t)/2 := by ring
        _ = 0 := by rw [hz]; norm_num
    have h : star (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t) * OAI.KirchbergRordam.UnitaryPaths.involutionValue U t = 1 := by
      simp only [OAI.KirchbergRordam.UnitaryPaths.involutionValue, star_add, star_smul, star_one, hs, star_div₀,
        star_ofNat, star_sub, smul_add, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, smul_smul, one_mul, mul_one, hm]
      calc
        _ = (((1+star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
              ((1-star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)) • (1:A) +
            (((1+star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1-OAI.KirchbergRordam.UnitaryPaths.phase t)/2)+
              ((1-star (OAI.KirchbergRordam.UnitaryPaths.phase t))/2)*((1+OAI.KirchbergRordam.UnitaryPaths.phase t)/2)) • U := by
                rw [add_smul, add_smul]; module
        _ = 1 := by
          simp only [star_add, star_sub, star_one] at h1 h2
          rw [h1, h2, one_smul, zero_smul, add_zero]
    refine ⟨h, ?_⟩
    have hc : Commute (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t) (star (OAI.KirchbergRordam.UnitaryPaths.involutionValue U t)) := by
      unfold OAI.KirchbergRordam.UnitaryPaths.involutionValue
      simp only [star_add, star_smul, star_one, hs]
      exact ((Commute.one_left _).smul_left _).add_left
        ((((Commute.one_right U).smul_right _).add_right
          ((Commute.refl U).smul_right _)).smul_left _)
    exact hc.eq.trans h
  have h_UnitaryPaths_phase_one  : OAI.KirchbergRordam.UnitaryPaths.phase 1 = -1 := by simp [OAI.KirchbergRordam.UnitaryPaths.phase, Complex.exp_pi_mul_I]
  have h_UnitaryPaths_phase_zero  : OAI.KirchbergRordam.UnitaryPaths.phase 0 = 1 := by simp [OAI.KirchbergRordam.UnitaryPaths.phase]
  exact {
    toFun t := ⟨OAI.KirchbergRordam.UnitaryPaths.involutionValue (U:A) t,
      h_UnitaryPaths_involutionValue_unitary (U:A) hs (by simpa only [hs] using Unitary.coe_star_mul_self U) t⟩
    continuous_toFun := (h_UnitaryPaths_involutionValue_continuous _).subtype_mk _
    source' := by apply Subtype.ext; simp [h_UnitaryPaths_phase_zero, OAI.KirchbergRordam.UnitaryPaths.involutionValue]
    target' := by apply Subtype.ext; simp [h_UnitaryPaths_phase_one, OAI.KirchbergRordam.UnitaryPaths.involutionValue]
  }


-- @@ L1185-1185 verbatim
end KirchbergRordam.UnitaryPaths


-- @@ L1187-1187 verbatim
namespace KirchbergRordam.MatrixPermutationPath

-- @@ L1188-1188 verbatim
open scoped Matrix

-- @@ L1189-1189 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L1190-1190 verbatim
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ


-- @@ L1192-1200 verbatim
def perm (σ : Equiv.Perm ι) : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) :=
  ⟨CStarMatrix.ofMatrix (σ⁻¹.permMatrix ℂ), by
    constructor
    · change (σ⁻¹.permMatrix ℂ)ᴴ * σ⁻¹.permMatrix ℂ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp
    · change σ⁻¹.permMatrix ℂ * (σ⁻¹.permMatrix ℂ)ᴴ = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp⟩


-- @@ L1202-1225 verbatim
def path (σ τ : Equiv.Perm ι) : Path (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) (OAI.KirchbergRordam.MatrixPermutationPath.perm τ) := by
  classical
  have h_MatrixPermutationPath_perm_mul  (σ τ : Equiv.Perm ι) : OAI.KirchbergRordam.MatrixPermutationPath.perm (σ*τ) = OAI.KirchbergRordam.MatrixPermutationPath.perm σ * OAI.KirchbergRordam.MatrixPermutationPath.perm τ := by
    apply Subtype.ext
    change ((σ*τ)⁻¹).permMatrix ℂ = σ⁻¹.permMatrix ℂ * τ⁻¹.permMatrix ℂ
    simp
  have h_MatrixPermutationPath_perm_one  : OAI.KirchbergRordam.MatrixPermutationPath.perm (1 : Equiv.Perm ι) = 1 := by
    apply Subtype.ext
    change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
    simp
  have h_MatrixPermutationPath_perm_swap_selfadjoint  (i j : ι) : star (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j) : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) =
      (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j) : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) := by
    change ((Equiv.swap i j)⁻¹.permMatrix ℂ)ᴴ = (Equiv.swap i j)⁻¹.permMatrix ℂ
    simp
  have h_MatrixPermutationPath_joined_one_perm  (σ : Equiv.Perm ι) : Joined (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι)) (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one => simpa [h_MatrixPermutationPath_perm_one] using Joined.refl (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι))
    | swap_mul σ i j hij ih =>
      rw [h_MatrixPermutationPath_perm_mul]
      have hi : Joined (1 : unitary (OAI.KirchbergRordam.MatrixPermutationPath.Mat ι)) (OAI.KirchbergRordam.MatrixPermutationPath.perm (Equiv.swap i j)) :=
        ⟨UnitaryPaths.involutionPath _ (h_MatrixPermutationPath_perm_swap_selfadjoint i j)⟩
      simpa only [one_mul] using hi.mul ih
  exact
    ((h_MatrixPermutationPath_joined_one_perm σ).symm.trans (h_MatrixPermutationPath_joined_one_perm τ)).somePath


-- @@ L1227-1227 verbatim
end KirchbergRordam.MatrixPermutationPath


-- @@ L1229-1229 verbatim
namespace KirchbergRordam.MatrixDiagonalPath

-- @@ L1230-1230 verbatim
open scoped ComplexOrder CStarAlgebra Matrix

-- @@ L1231-1232 verbatim
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]

-- @@ L1233-1233 verbatim
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ


-- @@ L1235-1247 verbatim
def block : (ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι) where
  toFun a := CStarMatrix.ofMatrix (Matrix.blockDiagonal a)
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' := Matrix.blockDiagonal_add
  map_mul' := Matrix.blockDiagonal_mul
  commutes' z := by
    change Matrix.blockDiagonal (fun _ : ι => (algebraMap ℂ (Matrix κ κ ℂ)) z) =
      algebraMap ℂ (Matrix (κ × ι) (κ × ι) ℂ) z
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (Matrix.blockDiagonal_smul z (1 : ι → Matrix κ κ ℂ)).trans
      (congrArg (z • ·) Matrix.blockDiagonal_one)
  map_star' a := Matrix.blockDiagonal_conjTranspose a |>.symm


-- @@ L1249-1257 verbatim
def evaluationBlock (ξ : ι → C(unitInterval, unitInterval)) (t : unitInterval) :
    C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι) where
  toFun f := OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => f (ξ i t))
  map_zero' := map_zero OAI.KirchbergRordam.MatrixDiagonalPath.block
  map_one' := map_one OAI.KirchbergRordam.MatrixDiagonalPath.block
  map_add' first second := map_add OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => first (ξ index t)) (fun index => second (ξ index t))
  map_mul' first second := map_mul OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => first (ξ index t)) (fun index => second (ξ index t))
  commutes' z := OAI.KirchbergRordam.MatrixDiagonalPath.block.commutes z
  map_star' path := map_star OAI.KirchbergRordam.MatrixDiagonalPath.block (fun index => path (ξ index t))


-- @@ L1259-1273 verbatim
def diagonal (ξ : ι → C(unitInterval, unitInterval)) :
    C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) →⋆ₐ[ℂ] C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ × ι)) := by
  classical
  have h_MatrixDiagonalPath_evaluationBlock_continuous  (ξ : ι → C(unitInterval, unitInterval))
      (f : C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f) :=
    (map_continuous OAI.KirchbergRordam.MatrixDiagonalPath.block).comp (continuous_pi (fun i => f.continuous.comp (ξ i).continuous))
  exact {
    toFun f := ⟨fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f, h_MatrixDiagonalPath_evaluationBlock_continuous ξ f⟩
    map_zero' := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_zero) _) _
    map_one' := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_one) _) _
    map_add' f g := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_add f g) _) _
    map_mul' f g := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).map_mul f g) _) _
    commutes' z := by ext t; exact congrFun (congrFun ((OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t).commutes z) _) _
    map_star' f := by ext t; exact congrFun (congrFun (map_star (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t) f) _) _
  }


-- @@ L1275-1278 verbatim
def interpolate (e₀ e₁ : κ ≃ ν) (t : unitInterval) : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ ≃⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν :=
  (CStarMatrix.reindexₐ ℂ ℂ e₀).trans
    (Unitary.conjStarAlgAut ℂ _
      ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t))


-- @@ L1280-1280 verbatim
end KirchbergRordam.MatrixDiagonalPath


-- @@ L1282-1282 verbatim
namespace KirchbergRordam.MatrixBlockReindex

-- @@ L1283-1283 verbatim
open MatrixTensor (leftMatrix rightMatrix)

-- @@ L1284-1284 verbatim
open MatrixDiagonalPath

-- @@ L1285-1285 verbatim
open scoped ComplexOrder CStarAlgebra Matrix Kronecker

-- @@ L1286-1289 verbatim
variable {P Q L R S T : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T]


-- @@ L1291-1312 verbatim
def sumBlock : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P × OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q →⋆ₐ[ℂ] OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P ⊕ Q) where
  toFun a := CStarMatrix.ofMatrix (Matrix.fromBlocks a.1 0 0 a.2)
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by
    change Matrix.fromBlocks (1 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ) = 1
    exact Matrix.fromBlocks_one
  map_add' a b := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_mul' a b := by
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1 * CStarMatrix.ofMatrix.symm b.1) 0 0
      (CStarMatrix.ofMatrix.symm a.2 * CStarMatrix.ofMatrix.symm b.2) =
      Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1) 0 0 (CStarMatrix.ofMatrix.symm a.2) *
        Matrix.fromBlocks (CStarMatrix.ofMatrix.symm b.1) 0 0 (CStarMatrix.ofMatrix.symm b.2)
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  commutes' z := by
    ext i j; cases i <;> cases j <;>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.fromBlocks, CStarMatrix.one_apply]
  map_star' a := by
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1)ᴴ 0 0
      (CStarMatrix.ofMatrix.symm a.2)ᴴ =
        (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a.1) 0 0
          (CStarMatrix.ofMatrix.symm a.2))ᴴ
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]


-- @@ L1314-1314 verbatim
end KirchbergRordam.MatrixBlockReindex


-- @@ L1316-1316 verbatim
namespace KirchbergRordam.MatrixBlockReindex

-- @@ L1317-1317 verbatim
open MatrixDiagonalPath

-- @@ L1318-1318 verbatim
open MatrixTensor (leftMatrix rightMatrix)

-- @@ L1319-1319 verbatim
open scoped ComplexOrder CStarAlgebra Matrix

-- @@ L1320-1321 verbatim
variable {P Q R S : Type*} [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [DecidableEq R] [DecidableEq S]

-- @@ L1322-1322 verbatim
end KirchbergRordam.MatrixBlockReindex


-- @@ L1324-1324 verbatim
namespace KirchbergRordam.BalancedDropSystem


-- @@ L1326-1328 verbatim
def cardEquiv {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α = Fintype.card β) : α ≃ β :=
  Classical.choice ((Fintype.card_eq.mp h))


-- @@ L1330-1336 verbatim
def half : unitInterval := by
  classical
  have h_BalancedDropSystem_half_mem  : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  exact
    ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv Real.instOne.one
        (Real.instNatCast.natCast 2), h_BalancedDropSystem_half_mem⟩


-- @@ L1338-1345 verbatim
def lowerPath : C(unitInterval, unitInterval) :=
  ⟨fun point => ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv point.val
    (Real.instNatCast.natCast 2), by
      change (point : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1
      constructor <;> linarith [point.property.1, point.property.2]⟩, by
    apply Continuous.subtype_mk
    change Continuous (fun point : unitInterval => (point : ℝ) / 2)
    fun_prop⟩


-- @@ L1347-1355 verbatim
def upperPath : C(unitInterval, unitInterval) :=
  ⟨fun point => ⟨@Div.div ℝ Real.instDivInvMonoid.toDiv
    (@Add.add ℝ Real.instAdd point.val Real.instOne.one)
    (Real.instNatCast.natCast 2), by
      change ((point : ℝ) + 1) / 2 ∈ Set.Icc (0 : ℝ) 1
      constructor <;> linarith [point.property.1, point.property.2]⟩, by
    apply Continuous.subtype_mk
    change Continuous (fun point : unitInterval => ((point : ℝ) + 1) / 2)
    fun_prop⟩


-- @@ L1357-1357 verbatim
end KirchbergRordam.BalancedDropSystem


-- @@ L1359-1359 verbatim
namespace KirchbergRordam.GeneralBlockReindex

-- @@ L1360-1360 verbatim
open MatrixBlockReindex MatrixDiagonalPath


-- @@ L1362-1362 verbatim
open scoped CStarAlgebra Matrix

-- @@ L1363-1366 verbatim
variable {P Q L R S T U : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]

-- @@ L1367-1376 verbatim
def repackLeft (hL : Q × L ≃ U × T) (hR : R ≃ S × T) :
    (P × Q) × (L ⊕ R) ≃ ((P × U) ⊕ ((P × Q) × S)) × T where
  toFun x := match x.2 with
    | .inl l => (.inl (x.1.1,(hL (x.1.2,l)).1),(hL (x.1.2,l)).2)
    | .inr r => (.inr (x.1,(hR r).1),(hR r).2)
  invFun x := match x.1 with
    | .inl y => ((y.1,(hL.symm (y.2,x.2)).1),.inl (hL.symm (y.2,x.2)).2)
    | .inr y => (y.1,.inr (hR.symm (y.2,x.2)))
  left_inv x := by rcases x with ⟨⟨i,j⟩,l|r⟩ <;> simp
  right_inv x := by rcases x with ⟨⟨i,u⟩|⟨ij,s⟩,t⟩ <;> simp


-- @@ L1378-1440 verbatim
def repackRight (hL : P × L ≃ T × U) (hR : R ≃ T × S) :
    (P × Q) × (L ⊕ R) ≃ T × ((Q × U) ⊕ ((P × Q) × S)) := by
  classical
  have h_GeneralBlockReindex_left_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
  have h_GeneralBlockReindex_left_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
  exact {
    toFun x := match x.2 with
      | .inl l => ((hL (x.1.1,l)).1,.inl (x.1.2,(hL (x.1.1,l)).2))
      | .inr r => ((hR r).1,.inr (x.1,(hR r).2))
    invFun x := match x.2 with
      | .inl y => (((hL.symm (x.1,y.2)).1,y.1),.inl (hL.symm (x.1,y.2)).2)
      | .inr y => (y.1,.inr (hR.symm (x.1,y.2)))
    left_inv x := by rcases x with ⟨⟨i,j⟩,l|r⟩ <;> simp
    right_inv x := by rcases x with ⟨t,⟨j,u⟩|⟨ij,s⟩⟩ <;> simp
  }


-- @@ L1442-1442 verbatim
end KirchbergRordam.GeneralBlockReindex


-- @@ L1444-1444 verbatim
namespace KirchbergRordam.GeneralDropSystem

-- @@ L1445-1445 verbatim
open MatrixDiagonalPath MatrixBlockReindex

-- @@ L1446-1446 verbatim
open BalancedDropSystem (half lowerPath upperPath)

-- @@ L1447-1447 verbatim
open scoped CStarAlgebra Matrix ComplexOrder


-- @@ L1449-1464 verbatim
structure Data (p q P Q : ℕ) where
  lower : ℕ
  upper : ℕ
  middle : ℕ
  zeroEnd : ℕ
  zeroMid : ℕ
  oneEnd : ℕ
  oneMid : ℕ
  lower_pos : 0<lower
  upper_pos : 0<upper
  zero_low : q*lower=zeroEnd*Q
  zero_mid : upper+middle=zeroMid*Q
  one_low : p*upper=P*oneEnd
  one_mid : lower+middle=P*oneMid
  zero_dim : p*zeroEnd+p*q*zeroMid=P
  one_dim : q*oneEnd+p*q*oneMid=Q


-- @@ L1466-1466 verbatim
variable {p q P Q : ℕ} (d : Data p q P Q)

-- @@ L1467-1467 verbatim
abbrev Low := Fin d.lower


-- @@ L1469-1469 verbatim
abbrev High := Fin d.upper


-- @@ L1471-1471 verbatim
abbrev Mid := Fin d.middle


-- @@ L1473-1473 verbatim
abbrev Slot := OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ (OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d)


-- @@ L1475-1475 verbatim
abbrev Index := (Fin p × Fin q) × OAI.KirchbergRordam.GeneralDropSystem.Slot d


-- @@ L1477-1477 verbatim
abbrev ZeroSpace := (Fin p × Fin d.zeroEnd) ⊕ ((Fin p × Fin q) × Fin d.zeroMid)


-- @@ L1479-1479 verbatim
abbrev OneSpace := (Fin q × Fin d.oneEnd) ⊕ ((Fin p × Fin q) × Fin d.oneMid)


-- @@ L1481-1482 verbatim
def zeroLow : Fin q × OAI.KirchbergRordam.GeneralDropSystem.Low d ≃ Fin d.zeroEnd × Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_prod,Fintype.card_fin] using d.zero_low)


-- @@ L1484-1485 verbatim
def zeroMid : OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d ≃ Fin d.zeroMid × Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.zero_mid)


-- @@ L1487-1488 verbatim
def zeroOuter : OAI.KirchbergRordam.GeneralDropSystem.ZeroSpace d ≃ Fin P :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.zero_dim)


-- @@ L1490-1491 verbatim
def oneLow : Fin p × OAI.KirchbergRordam.GeneralDropSystem.High d ≃ Fin P × Fin d.oneEnd :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_prod,Fintype.card_fin] using d.one_low)


-- @@ L1493-1494 verbatim
def oneMid : OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d ≃ Fin P × Fin d.oneMid :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.one_mid)


-- @@ L1496-1497 verbatim
def oneOuter : OAI.KirchbergRordam.GeneralDropSystem.OneSpace d ≃ Fin Q :=
  BalancedDropSystem.cardEquiv (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using d.one_dim)


-- @@ L1499-1503 verbatim
def slotSwap : OAI.KirchbergRordam.GeneralDropSystem.Slot d ≃ OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ (OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d) where
  toFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  invFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  left_inv x := by rcases x with x|x|x <;> rfl
  right_inv x := by rcases x with x|x|x <;> rfl


-- @@ L1505-1507 verbatim
def zeroReindex : OAI.KirchbergRordam.GeneralDropSystem.Index d ≃ Fin P × Fin Q :=
  (GeneralBlockReindex.repackLeft (OAI.KirchbergRordam.GeneralDropSystem.zeroLow d) (OAI.KirchbergRordam.GeneralDropSystem.zeroMid d)).trans
    (Equiv.prodCongr (OAI.KirchbergRordam.GeneralDropSystem.zeroOuter d) (Equiv.refl _))


-- @@ L1509-1512 verbatim
def oneReindex : OAI.KirchbergRordam.GeneralDropSystem.Index d ≃ Fin P × Fin Q :=
  (Equiv.prodCongr (Equiv.refl _) (OAI.KirchbergRordam.GeneralDropSystem.slotSwap d)).trans
    ((GeneralBlockReindex.repackRight (OAI.KirchbergRordam.GeneralDropSystem.oneLow d) (OAI.KirchbergRordam.GeneralDropSystem.oneMid d)).trans
      (Equiv.prodCongr (Equiv.refl _) (OAI.KirchbergRordam.GeneralDropSystem.oneOuter d)))


-- @@ L1514-1515 verbatim
def eigenpath : OAI.KirchbergRordam.GeneralDropSystem.Slot d → C(unitInterval,unitInterval) :=
  Sum.elim (fun _ => OAI.KirchbergRordam.BalancedDropSystem.lowerPath) (Sum.elim (fun _ => OAI.KirchbergRordam.BalancedDropSystem.upperPath) (fun _ => ContinuousMap.const _ OAI.KirchbergRordam.BalancedDropSystem.half))


-- @@ L1517-1517 verbatim
section


-- @@ L1519-1533 verbatim
def interpolatedEvaluation.{sourceLevel, blockLevel, targetLevel}
    {SourceIndex : Type sourceLevel} {BlockIndex : Type blockLevel}
    {TargetIndex : Type targetLevel}
    [sourceFintype : Fintype SourceIndex] [sourceDecidableEq : DecidableEq SourceIndex]
    [blockFintype : Fintype BlockIndex] [blockDecidableEq : DecidableEq BlockIndex]
    [targetFintype : Fintype TargetIndex] [targetDecidableEq : DecidableEq TargetIndex]
    (zeroReindex oneReindex : SourceIndex × BlockIndex ≃ TargetIndex)
    (eigenpath : BlockIndex → C(unitInterval, unitInterval)) (point : unitInterval) :
    C(unitInterval, MatrixDiagonalPath.Mat SourceIndex) →⋆ₐ[ℂ]
      MatrixDiagonalPath.Mat TargetIndex :=
  (@MatrixDiagonalPath.interpolate (SourceIndex × BlockIndex) TargetIndex
    (instFintypeProd SourceIndex BlockIndex)
    targetFintype targetDecidableEq zeroReindex oneReindex point).toStarAlgHom.comp
      (@MatrixDiagonalPath.evaluationBlock BlockIndex SourceIndex
        blockFintype blockDecidableEq sourceFintype sourceDecidableEq eigenpath point)


-- @@ L1535-1535 verbatim
end


-- @@ L1537-1543 verbatim
def fiberMap (t : unitInterval) :
    C(unitInterval,PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ] PrimeDimensionDrop.Fiber P Q :=
  @OAI.KirchbergRordam.GeneralDropSystem.interpolatedEvaluation (Fin p × Fin q) (OAI.KirchbergRordam.GeneralDropSystem.Slot d) (Fin P × Fin Q)
    (instFintypeProd (Fin p) (Fin q)) inferInstance
    (instFintypeSum (OAI.KirchbergRordam.GeneralDropSystem.Low d) (OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d)) inferInstance
    (instFintypeProd (Fin P) (Fin Q)) inferInstance
    (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) t


-- @@ L1545-1555 verbatim
def continuousFamily {Source Target : Type*} [CStarAlgebra Source] [CStarAlgebra Target]
    (family : unitInterval → Source →⋆ₐ[ℂ] Target)
    (continuous_family : ∀ value, Continuous (fun point => family point value)) :
    Source →⋆ₐ[ℂ] C(unitInterval, Target) where
  toFun value := ⟨fun point => family point value, continuous_family value⟩
  map_zero' := ContinuousMap.ext fun point => (family point).map_zero
  map_one' := ContinuousMap.ext fun point => (family point).map_one
  map_add' first second := ContinuousMap.ext fun point => (family point).map_add first second
  map_mul' first second := ContinuousMap.ext fun point => (family point).map_mul first second
  commutes' scalar := ContinuousMap.ext fun point => (family point).commutes scalar
  map_star' value := ContinuousMap.ext fun point => map_star (family point) value


-- @@ L1557-1593 verbatim
def rawStep :
    C(unitInterval, PrimeDimensionDrop.Fiber p q) →⋆ₐ[ℂ]
      C(unitInterval, PrimeDimensionDrop.Fiber P Q) := by
  classical
  have h_MatrixDiagonalPath_evaluationBlock_continuous {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (ξ : ι → C(unitInterval, unitInterval))
      (f : C(unitInterval, OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock ξ t f) :=
    (map_continuous OAI.KirchbergRordam.MatrixDiagonalPath.block).comp (continuous_pi (fun i => f.continuous.comp (ξ i).continuous))
  have h_MatrixDiagonalPath_interpolate_continuous
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (f : unitInterval → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ)
      (hf : Continuous f) : Continuous (fun t => OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ t (f t)) := by
    change Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν) *
      (CStarMatrix.reindexₐ ℂ ℂ e₀) (f t) *
      star ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν))
    have hu : Continuous (fun t => ((MatrixPermutationPath.path 1 (e₀.symm.trans e₁)) t : OAI.KirchbergRordam.MatrixDiagonalPath.Mat ν)) :=
      continuous_subtype_val.comp (Path.continuous _)
    exact (hu.mul ((map_continuous (CStarMatrix.reindexₐ ℂ ℂ e₀)).comp hf)).mul hu.star
  have h_GeneralDropSystem_fiberMap_continuous (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (path : C(unitInterval, PrimeDimensionDrop.Fiber p q)) :
      Continuous (fun point => OAI.KirchbergRordam.GeneralDropSystem.fiberMap d point path) :=
    h_MatrixDiagonalPath_interpolate_continuous (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d)
      (fun point => OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) point path)
      (h_MatrixDiagonalPath_evaluationBlock_continuous (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) path)
  exact
    @OAI.KirchbergRordam.GeneralDropSystem.continuousFamily C(unitInterval, PrimeDimensionDrop.Fiber p q)
        (PrimeDimensionDrop.Fiber P Q)
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber p q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin p × Fin q) (instFintypeProd (Fin p) (Fin q)) inferInstance))
        (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
          (Fin P × Fin Q) (instFintypeProd (Fin P) (Fin Q)) inferInstance)
        (OAI.KirchbergRordam.GeneralDropSystem.fiberMap d) (h_GeneralDropSystem_fiberMap_continuous d)


-- @@ L1595-1599 verbatim
def restrictToSubalgebras {Source Target : Type*} [CStarAlgebra Source] [CStarAlgebra Target]
    (hom : Source →⋆ₐ[ℂ] Target) (domain : StarSubalgebra ℂ Source)
    (codomain : StarSubalgebra ℂ Target)
    (map_mem : ∀ value ∈ domain, hom value ∈ codomain) : domain →⋆ₐ[ℂ] codomain :=
  (hom.comp domain.subtype).codRestrict codomain (fun value => map_mem value value.property)


-- @@ L1601-1922 verbatim
def step := by
  classical
  have h_GeneralBlockReindex_right_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR ((i,j),.inl l) = ((hL (i,l)).1,.inl (j,(hL (i,l)).2)) := rfl
  have h_GeneralBlockReindex_right_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR ((i,j),.inr r) = ((hR r).1,.inr ((i,j),(hR r).2)) := rfl
  have h_MatrixBlockReindex_sumBlock_ll {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : P) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inl i) (Sum.inl j) = a i j := rfl
  have h_MatrixBlockReindex_sumBlock_lr {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i : P) (j : Q) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inl i) (Sum.inr j) = 0 := rfl
  have h_MatrixBlockReindex_sumBlock_rl {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i : Q) (j : P) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inr i) (Sum.inl j) = 0 := rfl
  have h_MatrixBlockReindex_sumBlock_rr {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : Q) :
      OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (a,b) (Sum.inr i) (Sum.inr j) = b i j := rfl
  have h_MatrixBlockReindex_right_apply {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (i j : P) (k l : Q) :
      OAI.KirchbergRordam.MatrixTensor.rightMatrix a (i,k) (j,l) = (if i=j then 1 else 0) * a k l := by
    change (Matrix.kronecker (1 : Matrix P P ℂ) (CStarMatrix.ofMatrix.symm a)) (i,k) (j,l)=_
    simp [Matrix.one_apply]
  have h_MatrixDiagonalPath_block_apply {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (a : ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) (i j : κ) (k l : ι) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl
  have h_GeneralBlockReindex_right_entry {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m)) x y =
        MatrixTensor.rightMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m)))
          (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR x) (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR y) := by
    rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
    · by_cases he : (i,l)=(i',l')
      · cases he; simp [h_GeneralBlockReindex_right_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
      · have hh : (hL (i,l)).1≠(hL (i',l')).1 ∨ (hL (i,l)).2≠(hL (i',l')).2 := by
          by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
        have hil : i≠i' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
        rcases hh with h|h <;> rcases hil with hil|hil <;>
          simp [h_GeneralBlockReindex_right_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply,h,hil]
    · simp [h_GeneralBlockReindex_right_low, h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_lr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
    · simp [h_GeneralBlockReindex_right_low, h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rl, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
    · by_cases hr : r=r'
      · subst r'; simp [h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply]
      · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
          by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
        rcases hrr with h|h <;> simp [h_GeneralBlockReindex_right_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_right_apply, h_MatrixDiagonalPath_block_apply,hr,h]
  have h_GeneralBlockReindex_right_matrix {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : P × L ≃ T × U) (hR : R ≃ T × S)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat Q) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) :
      CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR)
        (OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m))) =
          MatrixTensor.rightMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m))) := by
    ext x y
    exact h_GeneralBlockReindex_right_entry hL hR a m ((OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR).symm x)
      ((OAI.KirchbergRordam.GeneralBlockReindex.repackRight hL hR).symm y) |>.trans (by simp [h_MatrixBlockReindex_right_apply] )
  have h_BalancedDropSystem_lower_one  : OAI.KirchbergRordam.BalancedDropSystem.lowerPath 1 = OAI.KirchbergRordam.BalancedDropSystem.half := by
    apply Subtype.ext
    change (1 : ℝ) / 2 = (1 : ℝ) / 2
    rfl
  have h_BalancedDropSystem_upper_one  : OAI.KirchbergRordam.BalancedDropSystem.upperPath 1 = 1 := by
    apply Subtype.ext
    change ((1 : ℝ) + 1) / 2 = 1
    norm_num
  have h_GeneralDropSystem_rawStep_apply (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f) (t : unitInterval) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f t=OAI.KirchbergRordam.MatrixDiagonalPath.interpolate (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) t (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) t f) := rfl
  have h_MatrixBlockReindex_reindex_block {P : Type 0} {Q : Type 0} {R : Type 0} [inst3 : Fintype P] [inst4 : Fintype Q] [inst5 : Fintype R] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst8 : DecidableEq R]  (e : P ≃ Q) (a : P → OAI.KirchbergRordam.MatrixDiagonalPath.Mat R) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl R) e) (OAI.KirchbergRordam.MatrixDiagonalPath.block a) =
        OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => a (e.symm i)) := by
    ext i j
    rcases i with ⟨r,p⟩; rcases j with ⟨s,q⟩
    change (if e.symm p=e.symm q then a (e.symm p) r s else 0) =
      (if p=q then a (e.symm p) r s else 0)
    simp only [e.symm.injective.eq_iff]
  have h_GeneralDropSystem_one_eval (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (Fin p × Fin q)) (OAI.KirchbergRordam.GeneralDropSystem.slotSwap d))
        (OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) 1 f)=
        OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : OAI.KirchbergRordam.GeneralDropSystem.High d => MatrixTensor.rightMatrix (ι:=Fin p) b)
          (fun _ : OAI.KirchbergRordam.GeneralDropSystem.Low d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d => f OAI.KirchbergRordam.BalancedDropSystem.half)) := by
    change CStarMatrix.reindexₐ ℂ ℂ _ (OAI.KirchbergRordam.MatrixDiagonalPath.block _) = _
    rw [h_MatrixBlockReindex_reindex_block]
    apply congrArg OAI.KirchbergRordam.MatrixDiagonalPath.block
    funext k
    rcases k with k|k|k <;> simp [h_BalancedDropSystem_lower_one, h_BalancedDropSystem_upper_one, OAI.KirchbergRordam.GeneralDropSystem.slotSwap,OAI.KirchbergRordam.GeneralDropSystem.eigenpath,hb]
  have h_MatrixBlockReindex_reindex_right {P : Type 0} {Q : Type 0} {R : Type 0} {S : Type 0} [inst4 : Fintype P] [inst5 : Fintype Q] [inst6 : Fintype R] [inst7 : Fintype S] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst10 : DecidableEq R] [inst11 : DecidableEq S]  (e : P ≃ Q) (f : R ≃ S) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat R) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=P) a) =
        OAI.KirchbergRordam.MatrixTensor.rightMatrix (ι:=Q) (CStarMatrix.reindexₐ ℂ ℂ f a) := by
    ext i j
    rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
    change OAI.KirchbergRordam.MatrixTensor.rightMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
    simp only [h_MatrixBlockReindex_right_apply, e.symm.injective.eq_iff]
    rfl
  have h_MatrixBlockReindex_reindex_trans
      {P : Type 0}
      {Q : Type 0}
      [Fintype P]
      [Fintype Q]
      [DecidableEq P]
      [DecidableEq Q]
      {T : Type 0} [Fintype T] [DecidableEq T]
      (e : P ≃ Q) (f : Q ≃ T) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) :
      CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
        CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl
  have h_MatrixPermutationPath_perm_conjugation {ι : Type 0} [inst1 : Fintype ι] [inst2 : DecidableEq ι]  (σ : Equiv.Perm ι) (a : OAI.KirchbergRordam.MatrixPermutationPath.Mat ι) :
      Unitary.conjStarAlgAut ℂ _ (OAI.KirchbergRordam.MatrixPermutationPath.perm σ) a = CStarMatrix.reindexₐ ℂ ℂ σ a := by
    change σ⁻¹.permMatrix ℂ * CStarMatrix.ofMatrix.symm a * (σ⁻¹.permMatrix ℂ)ᴴ =
      Matrix.reindex σ σ (CStarMatrix.ofMatrix.symm a)
    rw [Matrix.conjTranspose_permMatrix]
    change σ.symm.toPEquiv.toMatrix * CStarMatrix.ofMatrix.symm a * σ.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have h_MatrixDiagonalPath_interpolate_one
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) :
      OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ 1 a = CStarMatrix.reindexₐ ℂ ℂ e₁ a := by
    simp only [OAI.KirchbergRordam.MatrixDiagonalPath.interpolate, StarAlgEquiv.trans_apply, Path.target,
      (@h_MatrixPermutationPath_perm_conjugation)]
    ext i j
    change a (e₀.symm ((e₀.symm.trans e₁).symm i))
      (e₀.symm ((e₀.symm.trans e₁).symm j)) = a (e₁.symm i) (e₁.symm j)
    simp
  have h_GeneralDropSystem_rawStep_one (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (b : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f 1=MatrixTensor.rightMatrix (ι:=Fin P)
        (CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralDropSystem.oneOuter d)
          (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.oneEnd => b),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.oneMid => f OAI.KirchbergRordam.BalancedDropSystem.half)))) := by
    rw [h_GeneralDropSystem_rawStep_apply,h_MatrixDiagonalPath_interpolate_one]
    unfold OAI.KirchbergRordam.GeneralDropSystem.oneReindex
    rw [h_MatrixBlockReindex_reindex_trans,h_GeneralDropSystem_one_eval d f b hb,h_MatrixBlockReindex_reindex_trans,(@h_GeneralBlockReindex_right_matrix),h_MatrixBlockReindex_reindex_right]
  have h_GeneralBlockReindex_left_low
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (l : L) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
  have h_GeneralBlockReindex_left_full
      {P : Type 0}
      {Q : Type 0}
      {L : Type 0}
      {R : Type 0}
      {S : Type 0}
      {T : Type 0}
      {U : Type 0}
      [Fintype P]
      [Fintype Q]
      [Fintype L]
      [Fintype R]
      [Fintype S]
      [Fintype T]
      [Fintype U]
      [DecidableEq P]
      [DecidableEq Q]
      [DecidableEq L]
      [DecidableEq R]
      [DecidableEq S]
      [DecidableEq T]
      [DecidableEq U]
      (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (i : P) (j : Q) (r : R) :
      OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
  have h_MatrixBlockReindex_left_apply {P : Type 0} {Q : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q]  (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (i j : P) (k l : Q) :
      OAI.KirchbergRordam.MatrixTensor.leftMatrix a (i,k) (j,l) = a i j * if k=l then 1 else 0 := by
    change (Matrix.kronecker (CStarMatrix.ofMatrix.symm a) (1 : Matrix Q Q ℂ)) (i,k) (j,l)=_
    simp [Matrix.one_apply]
  have h_GeneralBlockReindex_left_entry {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m)) x y =
        MatrixTensor.leftMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m)))
          (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR x) (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR y) := by
    rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
    · by_cases he : (j,l)=(j',l')
      · cases he; simp [h_GeneralBlockReindex_left_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
      · have hh : (hL (j,l)).1≠(hL (j',l')).1 ∨ (hL (j,l)).2≠(hL (j',l')).2 := by
          by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
        have hjl : j≠j' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
        rcases hh with h|h <;> rcases hjl with hjl|hjl <;>
          simp [h_GeneralBlockReindex_left_low, h_MatrixBlockReindex_sumBlock_ll, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply,h,hjl]
    · simp [h_GeneralBlockReindex_left_low, h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_lr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
    · simp [h_GeneralBlockReindex_left_low, h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rl, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
    · by_cases hr : r=r'
      · subst r'; simp [h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply]
      · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
          by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
        rcases hrr with h|h <;> simp [h_GeneralBlockReindex_left_full, h_MatrixBlockReindex_sumBlock_rr, h_MatrixBlockReindex_left_apply, h_MatrixDiagonalPath_block_apply,hr,h]
  have h_GeneralBlockReindex_left_matrix {P : Type 0} {Q : Type 0} {L : Type 0} {R : Type 0} {S : Type 0} {T : Type 0} {U : Type 0} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R] [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]  (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) (m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (P×Q)) :
      CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR)
        (OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m))) =
          MatrixTensor.leftMatrix (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : U => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : S => m))) := by
    ext x y
    exact h_GeneralBlockReindex_left_entry hL hR a m ((OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR).symm x)
      ((OAI.KirchbergRordam.GeneralBlockReindex.repackLeft hL hR).symm y) |>.trans (by simp [h_MatrixBlockReindex_left_apply] )
  have h_BalancedDropSystem_lower_zero  : OAI.KirchbergRordam.BalancedDropSystem.lowerPath 0 = 0 := by
    apply Subtype.ext
    change (0 : ℝ) / 2 = 0
    norm_num
  have h_BalancedDropSystem_upper_zero  : OAI.KirchbergRordam.BalancedDropSystem.upperPath 0 = OAI.KirchbergRordam.BalancedDropSystem.half := by
    apply Subtype.ext
    change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
    rw [zero_add]
  have h_GeneralDropSystem_zero_eval (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
      OAI.KirchbergRordam.MatrixDiagonalPath.evaluationBlock (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) 0 f =
        OAI.KirchbergRordam.MatrixDiagonalPath.block (Sum.elim (fun _ : OAI.KirchbergRordam.GeneralDropSystem.Low d => MatrixTensor.leftMatrix (κ:=Fin q) a)
          (fun _ : OAI.KirchbergRordam.GeneralDropSystem.High d ⊕ OAI.KirchbergRordam.GeneralDropSystem.Mid d => f OAI.KirchbergRordam.BalancedDropSystem.half)) := by
    apply congrArg OAI.KirchbergRordam.MatrixDiagonalPath.block
    funext k
    rcases k with k|k|k <;> simp [h_BalancedDropSystem_lower_zero, h_BalancedDropSystem_upper_zero, OAI.KirchbergRordam.GeneralDropSystem.eigenpath,ha]
  have h_MatrixBlockReindex_reindex_left {P : Type 0} {Q : Type 0} {R : Type 0} {S : Type 0} [inst4 : Fintype P] [inst5 : Fintype Q] [inst6 : Fintype R] [inst7 : Fintype S] [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [inst10 : DecidableEq R] [inst11 : DecidableEq S]  (e : P ≃ Q) (f : R ≃ S) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat P) :
      CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=R) a) =
        OAI.KirchbergRordam.MatrixTensor.leftMatrix (κ:=S) (CStarMatrix.reindexₐ ℂ ℂ e a) := by
    ext i j
    rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
    change OAI.KirchbergRordam.MatrixTensor.leftMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
    simp only [h_MatrixBlockReindex_left_apply, f.symm.injective.eq_iff]
    rfl
  have h_MatrixPermutationPath_perm_one {ι : Type 0} [inst1 : Fintype ι] [inst2 : DecidableEq ι]  : OAI.KirchbergRordam.MatrixPermutationPath.perm (1 : Equiv.Perm ι) = 1 := by
    apply Subtype.ext
    change (1⁻¹ : Equiv.Perm ι).permMatrix ℂ = 1
    simp
  have h_MatrixDiagonalPath_interpolate_zero
      {κ : Type 0}
      {ν : Type 0}
      [Fintype κ]
      [DecidableEq κ]
      [Fintype ν]
      [DecidableEq ν]
      (e₀ e₁ : κ ≃ ν) (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) :
      OAI.KirchbergRordam.MatrixDiagonalPath.interpolate e₀ e₁ 0 a = CStarMatrix.reindexₐ ℂ ℂ e₀ a := by
    simp only [OAI.KirchbergRordam.MatrixDiagonalPath.interpolate, StarAlgEquiv.trans_apply, Path.source,
      (@h_MatrixPermutationPath_perm_one)]
    simp
  have h_GeneralDropSystem_rawStep_zero (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
      (a : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d f 0=MatrixTensor.leftMatrix (κ:=Fin Q)
        (CStarMatrix.reindexₐ ℂ ℂ (OAI.KirchbergRordam.GeneralDropSystem.zeroOuter d)
          (OAI.KirchbergRordam.MatrixBlockReindex.sumBlock (OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.zeroEnd => a),OAI.KirchbergRordam.MatrixDiagonalPath.block (fun _ : Fin d.zeroMid => f OAI.KirchbergRordam.BalancedDropSystem.half)))) := by
    rw [h_GeneralDropSystem_rawStep_apply,h_MatrixDiagonalPath_interpolate_zero,h_GeneralDropSystem_zero_eval d f a ha]
    unfold OAI.KirchbergRordam.GeneralDropSystem.zeroReindex
    rw [h_MatrixBlockReindex_reindex_trans,(@h_GeneralBlockReindex_left_matrix),h_MatrixBlockReindex_reindex_left]
  have h_GeneralDropSystem_rawStep_mem (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (path : C(unitInterval, PrimeDimensionDrop.Fiber p q))
      (path_mem : path ∈ PrimeDimensionDrop.subalgebra p q) :
      OAI.KirchbergRordam.GeneralDropSystem.rawStep d path ∈ PrimeDimensionDrop.subalgebra P Q := by
    obtain ⟨⟨leftValue, left_eq⟩, ⟨rightValue, right_eq⟩⟩ := path_mem
    exact ⟨⟨_, (h_GeneralDropSystem_rawStep_zero d path leftValue left_eq).symm⟩,
      ⟨_, (h_GeneralDropSystem_rawStep_one d path rightValue right_eq).symm⟩⟩
  exact
    @OAI.KirchbergRordam.GeneralDropSystem.restrictToSubalgebras C(unitInterval, PrimeDimensionDrop.Fiber p q)
        C(unitInterval, PrimeDimensionDrop.Fiber P Q)
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber p q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin p × Fin q) (instFintypeProd (Fin p) (Fin q)) inferInstance))
        (@ContinuousMap.instCStarAlgebra unitInterval (PrimeDimensionDrop.Fiber P Q)
          inferInstance inferInstance
          (@CStarMatrix.instCStarAlgebra ℂ inferInstance Complex.partialOrder inferInstance
            (Fin P × Fin Q) (instFintypeProd (Fin P) (Fin Q)) inferInstance))
        (OAI.KirchbergRordam.GeneralDropSystem.rawStep d) (PrimeDimensionDrop.subalgebra p q) (PrimeDimensionDrop.subalgebra P Q)
        (h_GeneralDropSystem_rawStep_mem d)


-- @@ L1924-1924 verbatim
end KirchbergRordam.GeneralDropSystem


-- @@ L1926-1926 verbatim
namespace KirchbergRordam


-- @@ L1928-1934 verbatim
structure PrimeDropPresentation where
  size : ℕ → ℕ
  exponent : ℕ → ℕ
  size_power : ∀ n, size n=2^(exponent n+1)
  stepData : ∀ n, GeneralDropSystem.Data (size n) (size n+1) (size (n+1)) (size (n+1)+1)
  zero_copies : ∀ n, 2≤(stepData n).zeroEnd+(size n+1)*(stepData n).zeroMid
  one_copies : ∀ n, 2≤(stepData n).oneEnd+size n*(stepData n).oneMid


-- @@ L1936-1936 verbatim
namespace PrimeDropPresentation

-- @@ L1937-1937 verbatim
variable (S : PrimeDropPresentation)


-- @@ L1939-1939 verbatim
def Stage (n : ℕ) : Type := PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)


-- @@ L1941-1942 verbatim
instance (n : ℕ) : CStarAlgebra (S.Stage n) := inferInstanceAs
  (CStarAlgebra (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))


-- @@ L1944-1998 verbatim
def chain (S : OAI.KirchbergRordam.PrimeDropPresentation) : CStarInductiveLimit.Chain.{0} := by
  classical
  have h_GeneralDropSystem_eigen_cover {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (s : unitInterval) : ∃ i t, OAI.KirchbergRordam.GeneralDropSystem.eigenpath d i t=s := by
    by_cases hs : (s:ℝ)≤1/2
    · refine ⟨.inl ⟨0,d.lower_pos⟩,⟨2*s,by constructor <;> linarith [s.property.1]⟩,?_⟩
      apply Subtype.ext
      change 2*(s:ℝ)/2=(s:ℝ)
      ring
    · refine ⟨.inr (.inl ⟨0,d.upper_pos⟩),⟨2*s-1,by constructor <;> linarith [s.property.2]⟩,?_⟩
      apply Subtype.ext
      change ((2*(s:ℝ)-1)+1)/2=(s:ℝ)
      ring
  have h_MatrixDiagonalPath_block_apply {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (a : ι → OAI.KirchbergRordam.MatrixDiagonalPath.Mat κ) (i j : κ) (k l : ι) :
      OAI.KirchbergRordam.MatrixDiagonalPath.block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl
  have h_MatrixDiagonalPath_block_injective {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  : Function.Injective (OAI.KirchbergRordam.MatrixDiagonalPath.block (ι:=ι) (κ:=κ)) := by
    intro a b h
    funext k
    ext i j
    have := congrArg (fun m : OAI.KirchbergRordam.MatrixDiagonalPath.Mat (κ×ι) => m (i,k) (j,k)) h
    simpa [h_MatrixDiagonalPath_block_apply, h_MatrixDiagonalPath_block_apply] using this
  have h_MatrixDiagonalPath_diagonal_injective {ι : Type 0} {κ : Type 0} [inst2 : Fintype ι] [inst3 : DecidableEq ι] [inst4 : Fintype κ] [instDecidableEqκ : DecidableEq κ]  (ξ : ι → C(unitInterval, unitInterval))
      (hcover : ∀ s : unitInterval, ∃ i t, ξ i t = s) :
      Function.Injective (OAI.KirchbergRordam.MatrixDiagonalPath.diagonal (κ:=κ) ξ) := by
    intro f g h
    ext s a b
    obtain ⟨i,t,rfl⟩ := hcover s
    have ht : OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => f (ξ i t)) = OAI.KirchbergRordam.MatrixDiagonalPath.block (fun i => g (ξ i t)) :=
      DFunLike.congr_fun h t
    exact congrFun (congrFun (congrFun (h_MatrixDiagonalPath_block_injective ht) i) a) b
  have h_GeneralDropSystem_rawStep_injective {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  : Function.Injective (OAI.KirchbergRordam.GeneralDropSystem.rawStep d) := by
    intro f g h
    apply h_MatrixDiagonalPath_diagonal_injective (OAI.KirchbergRordam.GeneralDropSystem.eigenpath d) (h_GeneralDropSystem_eigen_cover d)
    apply ContinuousMap.ext
    intro t
    exact (OAI.KirchbergRordam.MatrixDiagonalPath.interpolate (OAI.KirchbergRordam.GeneralDropSystem.zeroReindex d) (OAI.KirchbergRordam.GeneralDropSystem.oneReindex d) t).injective (DFunLike.congr_fun h t)
  have h_GeneralDropSystem_step_injective {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  : Function.Injective (OAI.KirchbergRordam.GeneralDropSystem.step d) := by
    intro f g h
    apply Subtype.ext
    exact h_GeneralDropSystem_rawStep_injective d (congrArg Subtype.val h)
  have h_GeneralDropSystem_step_norm {p : ℕ} {q : ℕ} {P : ℕ} {Q : ℕ} (d : OAI.KirchbergRordam.GeneralDropSystem.Data p q P Q)  (f : PrimeDimensionDrop.Algebra p q) : ‖OAI.KirchbergRordam.GeneralDropSystem.step d f‖=‖f‖ :=
    NonUnitalStarAlgHom.norm_map _ (h_GeneralDropSystem_step_injective d) f
  have h_PrimeDropPresentation_stage_step_norm  (S : OAI.KirchbergRordam.PrimeDropPresentation) :
      ∀ stage (element : S.Stage stage),
        ‖GeneralDropSystem.step (S.stepData stage) element‖ = ‖element‖ :=
    fun stage element => (@h_GeneralDropSystem_step_norm) (S.stepData stage) element
  exact
    @CStarInductiveLimit.Chain.mk.{0}
        (@OAI.KirchbergRordam.PrimeDropPresentation.Stage S)
        (@OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraStage S)
        (fun stage : Nat => @GeneralDropSystem.step
          (@PrimeDropPresentation.size S stage) (Nat.succ (@PrimeDropPresentation.size S stage))
          (@PrimeDropPresentation.size S (Nat.succ stage))
          (Nat.succ (@PrimeDropPresentation.size S (Nat.succ stage)))
          (@PrimeDropPresentation.stepData S stage))
        (@h_PrimeDropPresentation_stage_step_norm S)


-- @@ L2000-2000 verbatim
abbrev system := S.chain.system


-- @@ L2002-2002 verbatim
end PrimeDropPresentation

-- @@ L2003-2003 verbatim
end KirchbergRordam


-- @@ L2005-2005 verbatim
namespace KirchbergRordam.StandardPrimeMultiplicity


-- @@ L2007-2007 verbatim
def copies (p : ℕ) : ℕ := (p-1)*(p^4+p^2+1)


-- @@ L2009-2009 verbatim
def lower (p : ℕ) : ℕ := p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1


-- @@ L2011-2011 verbatim
def upper (p : ℕ) : ℕ := (p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1


-- @@ L2013-2013 verbatim
def middle (p : ℕ) : ℕ := p*(p+1)*(OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p)^2-1


-- @@ L2015-2015 verbatim
def next (p : ℕ) : ℕ := p^7


-- @@ L2017-2068 verbatim
def data (p : ℕ) (hp : 2≤p) : GeneralDropSystem.Data p (p+1) (OAI.KirchbergRordam.StandardPrimeMultiplicity.next p) (OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1) := by
  classical
  have h_StandardPrimeMultiplicity_dimension  (p : ℕ) (hp : 2≤p) : p+p*(p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    cases p with
    | zero => omega
    | succ p => simp only [OAI.KirchbergRordam.StandardPrimeMultiplicity.copies,OAI.KirchbergRordam.StandardPrimeMultiplicity.next,Nat.add_sub_cancel]; ring
  have h_StandardPrimeMultiplicity_lower_pos  (p : ℕ) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p := by unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower; omega
  have h_StandardPrimeMultiplicity_one_low  (p : ℕ) (hp : 2≤p) : p*OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    rw [←h_StandardPrimeMultiplicity_dimension p hp]
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper
    ring
  have h_StandardPrimeMultiplicity_copies_pos  (p : ℕ) (hp : 2≤p) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.copies
    exact Nat.mul_pos (by omega) (by positivity)
  have h_StandardPrimeMultiplicity_middle_add_one  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p+1=p*(p+1)*(OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p)^2 := by
    have hc := h_StandardPrimeMultiplicity_copies_pos p hp
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.middle
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have h_StandardPrimeMultiplicity_one_mid  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    have he : (OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p)+1=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p+1 := by
      rw [add_assoc,h_StandardPrimeMultiplicity_middle_add_one p hp,←h_StandardPrimeMultiplicity_dimension p hp]
      unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower
      ring
    omega
  have h_StandardPrimeMultiplicity_upper_pos  (p : ℕ) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p := by unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper; omega
  have h_StandardPrimeMultiplicity_zero_low  (p : ℕ) (hp : 2≤p) : (p+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p=OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1 := by
    rw [←h_StandardPrimeMultiplicity_dimension p hp]
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.lower
    ring
  have h_StandardPrimeMultiplicity_zero_mid  (p : ℕ) (hp : 2≤p) : OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p=OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p*(OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1) := by
    have he : (OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p+OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p)+1=OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p*(OAI.KirchbergRordam.StandardPrimeMultiplicity.next p+1)+1 := by
      rw [add_assoc,h_StandardPrimeMultiplicity_middle_add_one p hp,←h_StandardPrimeMultiplicity_dimension p hp]
      unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.upper
      ring
    omega
  exact {
    lower := OAI.KirchbergRordam.StandardPrimeMultiplicity.lower p
    upper := OAI.KirchbergRordam.StandardPrimeMultiplicity.upper p
    middle := OAI.KirchbergRordam.StandardPrimeMultiplicity.middle p
    zeroEnd := 1
    zeroMid := OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p
    oneEnd := 1
    oneMid := OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p
    lower_pos := h_StandardPrimeMultiplicity_lower_pos p
    upper_pos := h_StandardPrimeMultiplicity_upper_pos p
    zero_low := by simpa using h_StandardPrimeMultiplicity_zero_low p hp
    zero_mid := h_StandardPrimeMultiplicity_zero_mid p hp
    one_low := by simpa using h_StandardPrimeMultiplicity_one_low p hp
    one_mid := h_StandardPrimeMultiplicity_one_mid p hp
    zero_dim := by simpa using h_StandardPrimeMultiplicity_dimension p hp
    one_dim := by have := h_StandardPrimeMultiplicity_dimension p hp; omega
  }


-- @@ L2070-2072 verbatim
def size : ℕ → ℕ
  | 0 => 2
  | n+1 => OAI.KirchbergRordam.StandardPrimeMultiplicity.next (size n)


-- @@ L2074-2074 verbatim
end KirchbergRordam.StandardPrimeMultiplicity


-- @@ L2076-2076 verbatim
namespace KirchbergRordam.StandardPrimeModel

-- @@ L2077-2077 verbatim
open StandardPrimeMultiplicity

-- @@ L2078-2110 verbatim
def presentation : OAI.KirchbergRordam.PrimeDropPresentation := by
  classical
  have h_StandardPrimeMultiplicity_copies_pos  (p : ℕ) (hp : 2≤p) : 0<OAI.KirchbergRordam.StandardPrimeMultiplicity.copies p := by
    unfold OAI.KirchbergRordam.StandardPrimeMultiplicity.copies
    exact Nat.mul_pos (by omega) (by positivity)
  have h_StandardPrimeMultiplicity_size_zero  : OAI.KirchbergRordam.StandardPrimeMultiplicity.size 0=2 := rfl
  have h_StandardPrimeMultiplicity_size_succ  (n : ℕ) : OAI.KirchbergRordam.StandardPrimeMultiplicity.size (n+1)=OAI.KirchbergRordam.StandardPrimeMultiplicity.next (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) := rfl
  have h_StandardPrimeMultiplicity_size_power  (n : ℕ) : OAI.KirchbergRordam.StandardPrimeMultiplicity.size n=2^(7^n) := by
    induction n with
    | zero => simp [h_StandardPrimeMultiplicity_size_zero]
    | succ n ih => rw [h_StandardPrimeMultiplicity_size_succ,OAI.KirchbergRordam.StandardPrimeMultiplicity.next,ih,←pow_mul,pow_succ]
  have h_StandardPrimeMultiplicity_next_two  (p : ℕ) (hp : 2≤p) : 2≤OAI.KirchbergRordam.StandardPrimeMultiplicity.next p := by
    exact hp.trans (Nat.le_self_pow (by decide) p)
  have h_StandardPrimeMultiplicity_size_two  (n : ℕ) : 2 ≤ OAI.KirchbergRordam.StandardPrimeMultiplicity.size n := by
    induction n with
    | zero => simp [h_StandardPrimeMultiplicity_size_zero]
    | succ n ih => exact h_StandardPrimeMultiplicity_next_two _ ih
  exact {
    size := OAI.KirchbergRordam.StandardPrimeMultiplicity.size
    exponent n := 7^n-1
    size_power n := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow n 7 (by decide))]
      exact h_StandardPrimeMultiplicity_size_power n
    stepData n := OAI.KirchbergRordam.StandardPrimeMultiplicity.data (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
    zero_copies n := by
      change 2≤1+(OAI.KirchbergRordam.StandardPrimeMultiplicity.size n+1)*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n)
      have h := h_StandardPrimeMultiplicity_copies_pos (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
      nlinarith [h_StandardPrimeMultiplicity_size_two n]
    one_copies n := by
      change 2≤1+OAI.KirchbergRordam.StandardPrimeMultiplicity.size n*OAI.KirchbergRordam.StandardPrimeMultiplicity.copies (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n)
      have h := h_StandardPrimeMultiplicity_copies_pos (OAI.KirchbergRordam.StandardPrimeMultiplicity.size n) (h_StandardPrimeMultiplicity_size_two n)
      nlinarith [h_StandardPrimeMultiplicity_size_two n]
  }


-- @@ L2112-2112 verbatim
end KirchbergRordam.StandardPrimeModel


-- @@ L2114-2114 verbatim
namespace KirchbergRordam.JiangSu


-- @@ L2116-2116 verbatim
def Algebra : Type := CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system


-- @@ L2118-2119 verbatim
instance : CStarAlgebra OAI.KirchbergRordam.JiangSu.Algebra := inferInstanceAs
  (CStarAlgebra (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))


-- @@ L2121-2121 verbatim
end KirchbergRordam.JiangSu


-- @@ L2123-2123 verbatim
namespace KirchbergRordam


-- @@ L2125-2126 verbatim
def HasNoCharacters (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ χ : A →⋆ₙₐ[ℂ] ℂ, χ=0



-- @@ L2129-2129 verbatim
end KirchbergRordam


-- @@ L2131-2131 verbatim
end


-- @@ L2133-2133 verbatim
end OAI
