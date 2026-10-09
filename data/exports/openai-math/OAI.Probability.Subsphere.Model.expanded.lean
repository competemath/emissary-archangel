import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
universe u

-- @@ L9-9 verbatim
namespace SubsphereCurrent

-- @@ L10-10 verbatim
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- @@ L11-11 verbatim
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

-- @@ L12-12 verbatim
abbrev State (M : ℕ) := Fin (2 ^ M)

-- @@ L13-13 verbatim
abbrev Samples (d T : ℕ) := Fin T → Vector d


-- @@ L15-17 verbatim
def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ


-- @@ L19-20 verbatim
def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)


-- @@ L22-23 verbatim
def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume


-- @@ L25-29 verbatim
structure KernelLearner (d M T : ℕ) where
  initial : PMF (Bool × State M)
  transition : ℕ → State M → (Vector d × ℝ) → PMF (Bool × State M)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t q, IsProbabilityMeasure (output t q)


-- @@ L31-31 verbatim
namespace KernelLearner

-- @@ L32-32 verbatim
abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)


-- @@ L34-35 verbatim
def tagged (M t : ℕ) (a : Bool × State M) : RunStatus M :=
  if a.1 then .inr (t, a.2) else .inl a.2


-- @@ L37-45 verbatim
def run {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : ℕ → PMF (RunStatus M)
  | 0 => L.initial.map (tagged M 0)
  | n + 1 => (L.run s x n).bind fun status =>
      match status with
      | .inr done => PMF.pure (.inr done)
      | .inl q => if hn : n < T then
          (L.transition (n + 1) q (x ⟨n, hn⟩, ⟪x ⟨n, hn⟩, s.val⟫)).map (tagged M (n + 1))
        else PMF.pure (.inl q)


-- @@ L47-52 verbatim
def terminal {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : PMF (ℕ × State M) :=
  (L.run s x T).map fun status =>
    match status with
    | .inl q => (T, q)
    | .inr done => done


-- @@ L54-56 verbatim
def estimateLaw {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : Measure (UnitSphere d) :=
  (L.terminal s x).toMeasure.bind fun a => L.output a.1 a.2


-- @@ L58-59 verbatim
def angularError {d : ℕ} (s u : UnitSphere d) : ℝ :=
  Real.arccos ⟪u.val, s.val⟫


-- @@ L61-63 verbatim
def conditionalSuccess {d M T : ℕ} (L : KernelLearner d M T) (ε : ℝ)
    (s : UnitSphere d) (x : Samples d T) : ℝ≥0∞ :=
  L.estimateLaw s x {u | angularError s u ≤ ε}


-- @@ L65-66 verbatim
def CompletedRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, AEMeasurable (fun obs => L.transition t q obs dest) (observationReference d)


-- @@ L68-68 verbatim
end KernelLearner


-- @@ L70-71 verbatim
structure SeededLearner (d M T : ℕ) (Ω : Type u) where
  rules : Ω → KernelLearner d M T


-- @@ L73-73 verbatim
namespace SeededLearner


-- @@ L75-84 verbatim
structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) : Prop where
  completed_rules : ∀ᵐ ω ∂ρ, (L.rules ω).CompletedRules
  fixed_experiment : ∀ s ε, AEMeasurable
    (fun z : Ω × Samples d T => (L.rules z.1).conditionalSuccess ε s z.2)
    (ρ.prod (sampleLaw d T))
  uniform_experiment : ∀ ε, AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))


-- @@ L86-89 verbatim
def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  ∫⁻ z : Ω × Samples d T, (L.rules z.1).conditionalSuccess ε s z.2
    ∂(ρ.prod (sampleLaw d T))


-- @@ L91-95 verbatim
def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × (Ω × Samples d T),
    (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2
      ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

-- @@ L96-96 verbatim
end SeededLearner


-- @@ L98-107 verbatim
def ExplicitPrecision : Prop :=
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    ((2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, (2 / 3 : ℝ≥0∞) ≤ L.success ρ ε s) →
    (2 : ℝ)⁻¹ ^ 16 * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ)

-- @@ L108-108 verbatim
end SubsphereCurrent

-- @@ L109-109 verbatim
end


-- @@ L111-111 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L112-112 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L113-113 verbatim
noncomputable section

-- @@ L114-114 verbatim
universe u v

-- @@ L115-115 verbatim
namespace SubsphereCurrent.Affine


-- @@ L117-117 verbatim
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- @@ L118-118 verbatim
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1


-- @@ L120-123 verbatim
def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ


-- @@ L125-132 verbatim
structure Test (d n : ℕ) where
  space : Submodule ℝ (Vector d)
  dimension : Module.finrank ℝ space = n
  center : Vector d
  perpendicular : center ∈ spaceᗮ
  radius : ℝ
  radius_positive : 0 < radius
  unit : ‖center‖^2 + radius^2 = 1


-- @@ L134-135 verbatim
def Test.point {d n : ℕ} (A : Test d n) (s : Sphere A.space) : Vector d :=
  A.center + A.radius • s.val.val


-- @@ L137-137 verbatim
end SubsphereCurrent.Affine

-- @@ L138-138 verbatim
end


-- @@ L140-140 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L141-141 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L142-142 verbatim
noncomputable section

-- @@ L143-143 verbatim
universe v

-- @@ L144-144 verbatim
namespace SubsphereCurrent.Weighted

-- @@ L145-145 verbatim
abbrev Vector (d : ℕ) := Affine.Vector d

-- @@ L146-146 verbatim
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

-- @@ L147-147 verbatim
abbrev Rows (d k : ℕ) := Fin k → Vector d

-- @@ L148-148 verbatim
abbrev Observation (d k : ℕ) := Rows d k × (Fin k → ℝ)


-- @@ L150-161 verbatim
def onTest {d n : ℕ} (A : Affine.Test d n) (s : Affine.Sphere A.space) : Sphere d := by
  refine ⟨A.point s,mem_sphere_zero_iff_norm.mpr ?_⟩
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [Affine.Test.point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]


-- @@ L163-165 verbatim
def norm (d n : ℕ) (g : Sphere d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ A : Affine.Test d n, (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
    ∫⁻ s : Affine.Sphere A.space, g (onTest A s) ∂Affine.sphereLaw A.space


-- @@ L167-171 verbatim
def blockInput {d k : ℕ} {V : Type*} [Fintype V]
    (κ : V → Observation d k → ℝ≥0∞) (g : V → Sphere d → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ X : Rows d k, ∑ v, κ v (X,fun i => ⟪X i,s.val⟫)*g v s
    ∂Measure.pi (fun _ => stdGaussian (Vector d))


-- @@ L173-174 verbatim
def terminalInput {d : ℕ} (π : Measure (Sphere d)) (ε : ℝ) (s : Sphere d) : ℝ≥0∞ :=
  π {u | Real.arccos ⟪u.val,s.val⟫ ≤ ε}


-- @@ L176-176 verbatim
end SubsphereCurrent.Weighted

-- @@ L177-177 verbatim
end


-- @@ L179-179 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L180-180 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L181-181 verbatim
noncomputable section

-- @@ L182-182 verbatim
universe v

-- @@ L183-183 verbatim
namespace SubsphereCurrent.Weighted


-- @@ L185-199 verbatim
def RadiusWeightedFullEstimate : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ W : ℝ, 1 ≤ W → ∀ (V : Type v) [Fintype V] [Nonempty V],
      (Fintype.card V : ℝ) ≤ W →
      ∀ κ : V → Observation d (d/16) → ℝ≥0∞,
      (∀ v, Measurable (κ v)) → (∀ obs, ∑ v, κ v obs ≤ 1) →
      ∀ g : V → Sphere d → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ v s, g v s ≤ 1) →
      ∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      norm d n (blockInput κ g) ≤
        (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal (C^d)*(⨆ v, norm d (n-2) (g v))) ∧
    (∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      ∀ π : Measure (Sphere d), IsProbabilityMeasure π →
      ∀ ε : ℝ, 0 < ε →
      norm d n (terminalInput π ε) ≤ ENNReal.ofReal (C^d)*(ENNReal.ofReal ε)^((d : ℝ)/16))


-- @@ L201-201 verbatim
end SubsphereCurrent.Weighted

-- @@ L202-202 verbatim
end


-- @@ L204-204 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L205-205 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L206-206 verbatim
noncomputable section

-- @@ L207-207 verbatim
universe u

-- @@ L208-208 verbatim
namespace SubsphereCurrent


-- @@ L210-218 verbatim
def HalfPrecision : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.logb 2 (1/ε) ≤ (T : ℝ)

-- @@ L219-219 verbatim
end SubsphereCurrent

-- @@ L220-220 verbatim
end


-- @@ L222-222 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L223-223 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L224-224 verbatim
noncomputable section

-- @@ L225-225 verbatim
universe u v

-- @@ L226-226 verbatim
namespace SubsphereCurrent

-- @@ L227-227 verbatim
namespace Fixed


-- @@ L229-229 verbatim
abbrev Vector (m : ℕ) := EuclideanSpace ℝ (Fin m)

-- @@ L230-230 verbatim
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1


-- @@ L232-235 verbatim
def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ


-- @@ L237-239 verbatim
def rowsLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (T : ℕ) :
    Measure (Fin T → E) := Measure.pi fun _ => stdGaussian E


-- @@ L241-245 verbatim
structure Stream (E J : Type*) [MeasurableSpace E] (T : ℕ) where
  initial : PMF J
  transition : ℕ → J → (E × ℝ) → PMF J
  output : J → Measure E
  output_probability : ∀ q, IsProbabilityMeasure (output q)


-- @@ L247-247 verbatim
namespace Stream

-- @@ L248-250 verbatim
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}


-- @@ L252-256 verbatim
def run (L : Stream E J T) (s : E) (x : Fin T → E) : ℕ → PMF J
  | 0 => L.initial
  | n+1 => (L.run s x n).bind fun q => if hn : n < T then
      L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s⟫)
    else PMF.pure q


-- @@ L258-259 verbatim
def estimateLaw (L : Stream E J T) (s : E) (x : Fin T → E) : Measure E :=
  (L.run s x T).toMeasure.bind L.output


-- @@ L261-262 verbatim
def euclideanSuccess (L : Stream E J T) (η : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | ‖y-s‖ ≤ η}


-- @@ L264-265 verbatim
def angularSuccess (L : Stream E J T) (ε : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | Real.arccos ⟪y,s⟫ ≤ ε}


-- @@ L267-268 verbatim
def BorelRules (L : Stream E J T) : Prop :=
  ∀ n q a, Measurable (fun obs => L.transition n q obs a)


-- @@ L270-274 verbatim
def suffix (L : Stream E J T) (n k : ℕ) (v : J) : Stream E J k where
  initial := PMF.pure v
  transition t := L.transition (n+t)
  output := L.output
  output_probability := L.output_probability


-- @@ L276-276 verbatim
end Stream


-- @@ L278-291 verbatim
def DimensionEstimate : Prop :=
  ∃ C : ℝ, 2 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ j m : ℕ,
    (d : ℝ)/2 + 2*j ≤ m → m ≤ d →
    ∀ η : ℝ, 0 < η →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Stream (Vector m) (Fin (2^(d^2))) (j*(d/32)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules) →
    AEMeasurable (fun z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)) =>
      (L z.2.1).euclideanSuccess η z.1.val z.2.2)
      ((sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32))))) →
    (∫⁻ z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)),
      (L z.2.1).euclideanSuccess η z.1.val z.2.2
        ∂(sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32)))))
      ≤ ENNReal.ofReal ((C^(j+1)*η)^((d : ℝ)/32))


-- @@ L293-293 verbatim
end Fixed

-- @@ L294-294 verbatim
end SubsphereCurrent

-- @@ L295-295 verbatim
end


-- @@ L297-297 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L298-298 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L299-299 verbatim
noncomputable section

-- @@ L300-300 verbatim
universe u v

-- @@ L301-301 verbatim
namespace SubsphereCurrent.Affine


-- @@ L303-317 verbatim
def AllAffineFullEstimate : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    (d+1)/2 + 2*k ≤ d → ∀ W : ℝ, 1 ≤ W →
    ∀ (J : Type v) [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J],
    (Fintype.card J : ℝ) ≤ W → W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Fixed.Stream (Vector d) J (k*(d/16)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules ∧ ∀ q, ∀ᵐ y ∂(L ω).output q, ‖y‖ = 1) →
    ∀ ell : ℕ, ell ≤ k → ∀ v : J, ∀ n : ℕ, (d+1)/2 + 2*ell ≤ n →
    ∀ A : Test d n,
    (∫⁻ z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)),
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) v).angularSuccess ε (A.point z.1) z.2.2
        ∂(sphereLaw A.space).prod (ρ.prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))))
      ≤ ENNReal.ofReal (((16 * ((1000 : ℝ)^32)^ell * ε)/A.radius)^(2*(d/32)))


-- @@ L319-319 verbatim
end SubsphereCurrent.Affine

-- @@ L320-320 verbatim
end


-- @@ L322-322 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L323-323 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L324-324 verbatim
noncomputable section

-- @@ L325-325 verbatim
namespace SubsphereRegression

-- @@ L326-326 verbatim
section

-- @@ L327-327 verbatim
open scoped Pointwise

-- @@ L328-329 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- @@ L330-332 verbatim
def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

-- @@ L333-333 verbatim
end

-- @@ L334-334 verbatim
section

-- @@ L335-335 verbatim
open scoped Pointwise

-- @@ L336-337 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L339-339 verbatim
def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val

-- @@ L340-340 verbatim
end

-- @@ L341-341 verbatim
end SubsphereRegression

-- @@ L342-342 verbatim
end


-- @@ L344-344 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L345-345 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L346-346 verbatim
noncomputable section

-- @@ L347-347 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L348-348 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- @@ L349-350 verbatim
abbrev Orthogonal (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  unitary (E →L[ℝ] E)


-- @@ L352-359 verbatim
instance orthogonal_compact : CompactSpace (Orthogonal E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  apply u.opNorm_le_bound (by norm_num)
  intro x
  simp only [u.norm_map_of_mem_unitary hu,one_mul,le_refl]


-- @@ L361-362 verbatim
noncomputable def orthogonalLaw : Measure (Orthogonal E) :=
  Measure.haarMeasure ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

-- @@ L363-363 verbatim
end SubsphereCurrent.Mixture

-- @@ L364-364 verbatim
end


-- @@ L366-366 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L367-367 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L368-368 verbatim
noncomputable section

-- @@ L369-369 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L370-370 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L372-375 verbatim
def blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) : E ≃ₗᵢ[ℝ] E :=
  (V.orthogonalDecomposition.trans
    ((Unitary.linearIsometryEquiv u).withLpProdCongr 2 (Unitary.linearIsometryEquiv w))).trans
      V.orthogonalDecomposition.symm

-- @@ L376-376 verbatim
end SubsphereCurrent.Mixture

-- @@ L377-377 verbatim
end


-- @@ L379-379 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L380-380 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L381-381 verbatim
noncomputable section

-- @@ L382-382 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L383-384 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- @@ L386-388 verbatim
def directionLaw (V N : Submodule ℝ E) : Measure E :=
  ((orthogonalLaw (E := Vᗮ)).prod (SubsphereRegression.ambientSphereLaw (E := N))).map
    (fun z => blockIso V 1 z.1 (z.2 : E))


-- @@ L390-393 verbatim
def directionJointLaw (V N : Submodule ℝ E) (t : ℕ) : Measure (Fin t → E) :=
  ((orthogonalLaw (E := Vᗮ)).prod
    (Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw (E := N)))).map
      (fun z i => blockIso V 1 z.1 (z.2 i : E))


-- @@ L395-396 verbatim
def latitudeSpace (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : Submodule ℝ E :=
  (ℝ ∙ (e.val : E))ᗮ


-- @@ L398-402 verbatim
def latitudeLaw (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) (a delta : ℝ) : Measure E :=
  ((betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))).map
      (fun z => blockIso V z.2.1 1
        (Real.sqrt (1-z.1) • (e.val : E) + Real.sqrt z.1 • (z.2.2 : E)))


-- @@ L404-417 verbatim
def MixtureEstimate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  (∀ (V N : Submodule ℝ E), V ≤ N → 1 ≤ Module.finrank ℝ V →
    Module.finrank ℝ V < Module.finrank ℝ N → Module.finrank ℝ N < Module.finrank ℝ E →
    ∀ e : Metric.sphere (0 : V) 1,
    directionLaw V N ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2))) ∧
  (∀ N : Submodule ℝ E, 1 ≤ Module.finrank ℝ N →
    directionLaw ⊥ N = SubsphereRegression.ambientSphereLaw) ∧
  (∀ (V : Submodule ℝ E) (t : ℕ), 1 ≤ Module.finrank ℝ E →
    directionJointLaw V ⊤ t =
      Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw))


-- @@ L419-419 verbatim
end SubsphereCurrent.Mixture

-- @@ L420-420 verbatim
end


-- @@ L422-422 verbatim
noncomputable section

-- @@ L423-423 verbatim
universe u v w

-- @@ L424-424 verbatim
namespace SubsphereCurrent


-- @@ L426-433 verbatim
def CurrentMainScope : Prop :=
  ExplicitPrecision.{u} ∧
  Weighted.RadiusWeightedFullEstimate.{v} ∧
  HalfPrecision.{u} ∧
  Affine.AllAffineFullEstimate.{u,v} ∧
  Fixed.DimensionEstimate.{u} ∧
  (∀ (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E], Mixture.MixtureEstimate E)


-- @@ L435-435 verbatim
end SubsphereCurrent

-- @@ L436-436 verbatim
end


-- @@ L438-438 verbatim
end OAI
