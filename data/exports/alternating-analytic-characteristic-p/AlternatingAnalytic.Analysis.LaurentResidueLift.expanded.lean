import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient
import AlternatingAnalytic.Analysis.LaurentMultipliers
import AlternatingAnalytic.Analysis.LiftCriterion
import AlternatingAnalytic.Analysis.BaseChangeLiftDescent
import AlternatingAnalytic.Algebra.FiniteFieldObstruction
import AlternatingAnalytic.Algebra.MultiplierObstruction
import AlternatingAnalytic.Algebra.Polarization


-- @@ L9-24 verbatim
/-!
# The coefficient lift `Ψ` and Theorem C.1

Given a bounded `k`-linear lift `P` of `A^k` over `K₁ = κ((X))`, with `E₁ = ℓ^∞(ℕ, K₁)` and
`B` the completed projective exterior power, we evaluate `P` at multiplication operators and
the universal wedge `W_B`, restrict to `κ`-valued arrays and take constant coefficients. This
gives the map `Ψ` of Appendix C. Its properties (Lemma C.4) contradict the finite-field
multiplier theorem when `κ` is finite and `k ≥ p`, which proves Theorem C.1.

## Main results

* `laurentResidueLift`: the map `Ψ`.
* `laurentResidueLift_properties`: (Ψ2), (Ψ3), the diagonal identity and (Pol1).
* `laurent_not_hasBoundedLift`: Theorem C.1, no bounded lift.
* `laurent_not_analyticAt`: Theorem C.1, `A^k` is analytic at no point.
-/


-- @@ L26-26 verbatim
noncomputable section

-- @@ L27-27 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L28-28 verbatim
open Module

-- @@ L29-29 verbatim
open scoped NNReal BoundedContinuousFunction

-- @@ L30-30 verbatim
namespace AlternatingAnalytic


-- @@ L32-32 verbatim
variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)


-- @@ L34-34 verbatim
local notation "K" => LaurentField κ r

-- @@ L35-35 verbatim
local notation "E" => (ℕ →ᵇ LaurentField κ r)

-- @@ L36-36 verbatim
local notation "B" => ProjectiveExteriorCompletion (LaurentField κ r) ℕ k

-- @@ L37-38 verbatim
local notation "A" => ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
  ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)


-- @@ L40-45 verbatim
/-- Candidates for a bounded `n`-linear lift of `A^n : L(V, V) → L(Alt^n(V; W))`. -/
abbrev BoundedPrecompositionLiftCandidate (F : Type*) [NontriviallyNormedField F]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace F V]
    (W : Type*) [NormedAddCommGroup W] [NormedSpace F W] (n : ℕ) : Type _ :=
  ContinuousMultilinearMap F (fun _ : Fin n => V →L[F] V)
    ((V [⋀^Fin n]→L[F] W) →L[F] (V [⋀^Fin n]→L[F] W))


-- @@ L47-48 verbatim
/-- Lift candidates for `E₁ = ℓ^∞(ℕ, K₁)` and the completed exterior power `B`. -/
abbrev LaurentLiftCandidate : Type _ := BoundedPrecompositionLiftCandidate K E B k


-- @@ L50-52 verbatim
local instance laurentLiftSeminormedAddCommGroup : SeminormedAddCommGroup (LaurentLiftCandidate κ r k) :=
  ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := K)
    («E» := fun _ : Fin k => E →L[K] E) (G := A →L[K] A)


-- @@ L54-56 verbatim
local instance laurentLiftNorm : Norm (LaurentLiftCandidate κ r k) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := K)
    («E» := fun _ : Fin k => E →L[K] E) (G := A →L[K] A)


-- @@ L58-66 verbatim
/-- `(a₁, …, aₙ) ↦ P(D a₁, …, D aₙ)(w)` for an operator family `D` and a form `w`. -/
def evaluateBoundedPrecompositionLift (F : Type*) [NontriviallyNormedField F]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace F V]
    (W : Type*) [NormedAddCommGroup W] [NormedSpace F W] (n : ℕ)
    (P : BoundedPrecompositionLiftCandidate F V W n)
    (D : V →L[F] (V →L[F] V)) (w : V [⋀^Fin n]→L[F] W) :
    ContinuousMultilinearMap F (fun _ : Fin n => V) (V [⋀^Fin n]→L[F] W) :=
  (ContinuousLinearMap.apply F (V [⋀^Fin n]→L[F] W) w).compContinuousMultilinearMap
    (P.compContinuousLinearMap fun _ => D)


-- @@ L68-71 verbatim
/-- The map `Φ(a; ·) = P(D_{a₁}, …, D_{a_k})(W_B)` of Appendix C. -/
def laurentLiftAlternating (P : LaurentLiftCandidate κ r k) :=
  evaluateBoundedPrecompositionLift K E B k P (boundedSequenceMultiplier K ℕ)
    (completedExteriorWedge K ℕ k)


-- @@ L73-86 verbatim
/-- Restrict an alternating map to `κ`-valued inputs and apply the coefficient map `η`. -/
def laurentResiduePost (α : Fin k) :
    A →ₗ[κ] MultilinearMap κ (fun _ : Fin k => ℕ → κ) (⋀[κ]^k (ℕ → κ)) where
  toFun f := (completedLaurentCoefficient κ r ℕ k α).compMultilinearMap
    ((f.toMultilinearMap.restrictScalars κ).compLinearMap
      (fun _ => constantLaurentArrayLinear ℕ κ r))
  map_add' f g := by
    apply MultilinearMap.ext
    intro x
    exact map_add (completedLaurentCoefficient κ r ℕ k α) _ _
  map_smul' c f := by
    apply MultilinearMap.ext
    intro x
    exact map_smul (completedLaurentCoefficient κ r ℕ k α) c _


-- @@ L88-93 verbatim
/-- The coefficient lift `Ψ = η ∘ Φ` restricted to `κ`-valued arrays. -/
def laurentResidueLift (α : Fin k) (P : LaurentLiftCandidate κ r k) :
    MultiplierMap κ k (ℕ → κ) :=
  (laurentResiduePost κ r k α).compMultilinearMap
    (((laurentLiftAlternating κ r k P).toMultilinearMap.restrictScalars κ).compLinearMap
      (fun _ => constantLaurentArrayLinear ℕ κ r))


-- @@ L95-100 verbatim
@[simp]
theorem laurentResidueLift_apply (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (u x : Fin k → ℕ → κ) :
    laurentResidueLift κ r k α P u x = completedLaurentCoefficient κ r ℕ k α
      (P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
        (completedExteriorWedge K ℕ k) (fun i => constantLaurentArray κ r (x i))) := rfl


-- @@ L102-110 verbatim
/-- (Ψ2) `Ψ` is alternating in its last `k` slots. -/
theorem laurentResidueLift_alternating (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (u x : Fin k → ℕ → κ) {i j : Fin k} (hij : i ≠ j) (hx : x i = x j) :
    laurentResidueLift κ r k α P u x = 0 := by
  rw [laurentResidueLift_apply]
  have hz := (P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
    (completedExteriorWedge K ℕ k)).map_eq_zero_of_eq
      (fun i => constantLaurentArray κ r (x i)) (congrArg (constantLaurentArray κ r) hx) hij
  rw [hz, map_zero]


-- @@ L112-122 verbatim
/-- `Ψ` is antisymmetric in its last `k` slots. -/
theorem laurentResidueLift_antisymmetric (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (u x : Fin k → ℕ → κ) (σ : Equiv.Perm (Fin k)) :
    laurentResidueLift κ r k α P u (x ∘ σ) =
      Equiv.Perm.sign σ • laurentResidueLift κ r k α P u x := by
  have h := (P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
    (completedExteriorWedge K ℕ k)).toAlternatingMap.map_perm
      (fun i => constantLaurentArray κ r (x i)) σ
  have h' := congrArg (completedLaurentCoefficient κ r ℕ k α) h
  simpa only [laurentResidueLift_apply, Function.comp_def, ContinuousAlternatingMap.coe_toAlternatingMap,
    Units.smul_def, map_zsmul] using h'


-- @@ L124-159 verbatim
/-- On `κ`-valued inputs, `‖Φ(a; x)‖ ≤ ‖P‖`. -/
theorem norm_laurentLift_constant_le (P : LaurentLiftCandidate κ r k)
    (u x : Fin k → ℕ → κ) :
    ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
      (completedExteriorWedge K ℕ k) (fun i => constantLaurentArray κ r (x i))‖ ≤ ‖P‖ := by
  have hu : ∀ i, ‖boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i))‖ ≤ 1 :=
    fun i => (norm_boundedSequenceMultiplier_le K ℕ _).trans
      (norm_constantLaurentArray_le_one κ r (u i))
  have hprod : (∏ i, ‖boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i))‖) ≤ 1 := by
    calc
      _ ≤ ∏ _i : Fin k, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hu i)
      _ = 1 := by simp
  have hP : ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))‖ ≤ ‖P‖ := by
    calc
      _ ≤ ‖P‖ * ∏ i, ‖boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i))‖ :=
        norm_lift_apply_le K E B k P _
      _ ≤ ‖P‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg P)
      _ = _ := mul_one _
  have hPW : ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
      (completedExteriorWedge K ℕ k)‖ ≤ ‖P‖ := by
    calc
      _ ≤ ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))‖ *
          ‖completedExteriorWedge K ℕ k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P‖ * 1 := mul_le_mul hP (completedExteriorWedge_norm_le K ℕ k)
        (norm_nonneg _) (norm_nonneg P)
      _ = _ := mul_one _
  have hx : ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
      (completedExteriorWedge K ℕ k) (fun i => constantLaurentArray κ r (x i))‖ ≤
      ‖P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
        (completedExteriorWedge K ℕ k)‖ := by
    simpa using ContinuousAlternatingMap.le_opNorm_mul_prod_of_le
      (P (fun i => boundedSequenceMultiplier K ℕ (constantLaurentArray κ r (u i)))
        (completedExteriorWedge K ℕ k))
      (fun i => norm_constantLaurentArray_le_one κ r (x i))
  exact hx.trans hPW


-- @@ L161-170 verbatim
/-- (Ψ3) `sdim Ψ(a; x) ≤ ⌊k M_r ‖P‖⌋`. -/
theorem laurentResidueLift_support_le (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (u x : Fin k → ℕ → κ) :
    exteriorSupportDim (laurentResidueLift κ r k α P u x) ≤
      ⌊(k : ℝ) * geometricWeightMaximum r * ‖P‖⌋₊ := by
  apply Nat.le_floor
  rw [laurentResidueLift_apply]
  exact (completedLaurentCoefficient_support_le κ r ℕ k α _).trans
    (mul_le_mul_of_nonneg_left (norm_laurentLift_constant_le κ r k P u x)
      (mul_nonneg (Nat.cast_nonneg k) (zero_le_one.trans (one_le_geometricWeightMaximum r))))


-- @@ L172-184 verbatim
/-- On the diagonal, `Ψ(a, …, a; x) = (a x₁) ∧ … ∧ (a x_k)`. -/
theorem laurentResidueLift_diagonal (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : E →L[K] E, P (fun _ => f) = LiftCriterion.Q K (Fin k) E E B f)
    (a : ℕ → κ) (x : Fin k → ℕ → κ) :
    laurentResidueLift κ r k α P (fun _ => a) x =
      exteriorPower.ιMulti κ k (fun i => a * x i) := by
  rw [laurentResidueLift_apply, hP]
  change completedLaurentCoefficient κ r ℕ k α
    (completedExteriorWedge K ℕ k (fun i =>
      boundedSequenceMultiplier K ℕ (constantLaurentArray κ r a)
        (constantLaurentArray κ r (x i)))) = _
  simp only [boundedSequenceMultiplier_constant]
  exact completedLaurentCoefficient_constant_wedge κ r ℕ k α _


-- @@ L186-193 verbatim
/-- `Ψ` with its last `k` arguments fixed, as a multilinear map in the first `k`. -/
def laurentResidueFixedVectors (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (x : Fin k → ℕ → κ) : MultilinearMap κ (fun _ : Fin k => ℕ → κ) (⋀[κ]^k (ℕ → κ)) where
  toFun u := laurentResidueLift κ r k α P u x
  map_update_add' u i a b := congrArg (fun f => f x)
    ((laurentResidueLift κ r k α P).map_update_add u i a b)
  map_update_smul' u i c a := congrArg (fun f => f x)
    ((laurentResidueLift κ r k α P).map_update_smul u i c a)


-- @@ L195-203 verbatim
/-- (Pol1) for `Ψ`. -/
theorem laurentResidueLift_pol1 (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : E →L[K] E, P (fun _ => f) = LiftCriterion.Q K (Fin k) E E B f)
    (u x : Fin k → ℕ → κ) :
    (∑ σ : Equiv.Perm (Fin k), laurentResidueLift κ r k α P (u ∘ σ) x) =
      ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti κ k (fun i => u (σ i) * x i) := by
  exact MultilinearMap.sum_perm_eq_of_multiplier_diagonal
    (laurentResidueFixedVectors κ r k α P x) (exteriorPower.ιMulti κ k).toMultilinearMap
    (sequenceMultiplier κ) x (fun a => laurentResidueLift_diagonal κ r k α P hP a x) u


-- @@ L205-227 verbatim
/-- `Ψ` is alternating and antisymmetric in its last `k` slots, has support dimension at most
`⌊k M_r ‖P‖⌋`, and satisfies the diagonal identity and (Pol1). Multilinearity is in its type. -/
theorem laurentResidueLift_properties (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : E →L[K] E, P (fun _ => f) = LiftCriterion.Q K (Fin k) E E B f) :
    (∀ (u x : Fin k → ℕ → κ) (i j : Fin k), i ≠ j → x i = x j →
      laurentResidueLift κ r k α P u x = 0) ∧
    (∀ (u x : Fin k → ℕ → κ) (σ : Equiv.Perm (Fin k)),
      laurentResidueLift κ r k α P u (x ∘ σ) =
        Equiv.Perm.sign σ • laurentResidueLift κ r k α P u x) ∧
    (∀ u x : Fin k → ℕ → κ,
      exteriorSupportDim (laurentResidueLift κ r k α P u x) ≤
        ⌊(k : ℝ) * geometricWeightMaximum r * ‖P‖⌋₊) ∧
    (∀ (a : ℕ → κ) (x : Fin k → ℕ → κ),
      laurentResidueLift κ r k α P (fun _ => a) x =
        exteriorPower.ιMulti κ k (fun i => a * x i)) ∧
    (∀ u x : Fin k → ℕ → κ,
      (∑ σ : Equiv.Perm (Fin k), laurentResidueLift κ r k α P (u ∘ σ) x) =
        ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti κ k (fun i => u (σ i) * x i)) :=
  ⟨fun u x _ _ hij hx => laurentResidueLift_alternating κ r k α P u x hij hx,
    laurentResidueLift_antisymmetric κ r k α P,
    laurentResidueLift_support_le κ r k α P,
    laurentResidueLift_diagonal κ r k α P hP,
    laurentResidueLift_pol1 κ r k α P hP⟩


-- @@ L229-243 verbatim
/-- If `κ` is finite and `k! = 0` in `κ`, then `A^k` has no bounded lift over `κ((X))`. -/
theorem laurent_not_hasBoundedLift_of_factorial [Finite κ] (hk : 0 < k)
    (hfactorial : (k.factorial : κ) = 0) :
    ¬ LiftCriterion.HasBoundedLift K (Fin k) E E B := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P : LaurentLiftCandidate κ r k,
      ∀ f : E →L[K] E, P (fun _ => f) = LiftCriterion.Q K (Fin k) E E B f := by
    exact LiftCriterion.hasBoundedLift_iff_exists_ι.mp h
  let α : Fin k := ⟨0, hk⟩
  exact finiteField_multiplier_obstruction_full hfactorial (laurentResidueLift κ r k α P)
    (laurentResidueLift_antisymmetric κ r k α P)
    (fun u x => laurentResidueLift_pol1 κ r k α P hP
      (fun i n => u i n) (fun i n => x i n))
    ⌊(k : ℝ) * geometricWeightMaximum r * ‖P‖⌋₊
    (laurentResidueLift_support_le κ r k α P)


-- @@ L245-250 verbatim
/-- Theorem C.1: if `κ` is finite of characteristic `p` and `k ≥ p`, then `A^k` has no bounded lift. -/
theorem laurent_not_hasBoundedLift [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (hpk : p ≤ k) : ¬ LiftCriterion.HasBoundedLift K (Fin k) E E B := by
  apply laurent_not_hasBoundedLift_of_factorial κ r k ((Fact.out : p.Prime).pos.trans_le hpk)
  exact (CharP.cast_eq_zero_iff κ p k.factorial).2
    (Nat.dvd_factorial (Fact.out : p.Prime).pos hpk)


-- @@ L252-257 verbatim
/-- Theorem C.1: under the same hypotheses, `A^k` is analytic at no point. -/
theorem laurent_not_analyticAt [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (hpk : p ≤ k) (f₀ : E →L[K] E) :
    ¬ AnalyticAt K (LiftCriterion.Q K (Fin k) E E B) f₀ := by
  intro h
  exact laurent_not_hasBoundedLift κ r k p hpk (LiftCriterion.hasBoundedLift_of_analyticAt h)


-- @@ L259-259 verbatim
end AlternatingAnalytic
