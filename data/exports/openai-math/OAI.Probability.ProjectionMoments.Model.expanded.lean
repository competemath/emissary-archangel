import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
section InlineMainProof


-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory Set Filter


-- @@ L11-11 verbatim
open scoped ENNReal NNReal RealInnerProductSpace


-- @@ L13-13 verbatim
universe u


-- @@ L15-15 verbatim
namespace NoiselessRegression


-- @@ L17-17 verbatim
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)


-- @@ L19-19 verbatim
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1


-- @@ L21-21 verbatim
abbrev State (M : ℕ) := Fin (2 ^ M)


-- @@ L23-23 verbatim
abbrev Samples (d T : ℕ) := Fin T → Vector d


-- @@ L25-27 verbatim
def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ


-- @@ L29-30 verbatim
def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)


-- @@ L32-33 verbatim
def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume


-- @@ L35-38 verbatim
structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d


-- @@ L40-40 verbatim
namespace Learner


-- @@ L42-42 verbatim
abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)


-- @@ L44-47 verbatim
def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2


-- @@ L49-60 verbatim
def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state


-- @@ L62-66 verbatim
def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done


-- @@ L68-71 verbatim
def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2


-- @@ L73-83 verbatim
structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))


-- @@ L85-86 verbatim
def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫


-- @@ L88-91 verbatim
def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}


-- @@ L93-93 verbatim
end Learner


-- @@ L95-95 verbatim
open scoped Topology


-- @@ L97-97 verbatim
open InnerProductSpace


-- @@ L99-99 verbatim
section SphereBounds


-- @@ L101-101 verbatim
open scoped Pointwise


-- @@ L103-104 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L106-108 verbatim
def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ


-- @@ L110-110 verbatim
end SphereBounds


-- @@ L112-112 verbatim
open scoped Pointwise


-- @@ L114-115 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L117-117 verbatim
def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val


-- @@ L119-119 verbatim
end NoiselessRegression


-- @@ L121-121 verbatim
end InlineMainProof


-- @@ L123-123 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator

-- @@ L124-124 verbatim
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix

-- @@ L125-125 verbatim
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

-- @@ L126-126 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Topology

-- @@ L127-127 verbatim
namespace ProjectionMoments


-- @@ L129-129 verbatim
section GaussianGraph


-- @@ L131-132 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L134-136 verbatim
def vectorSmoothing (ν : Measure E) (m : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, φ (fun j => z.2 j - ⟪t, z.1 j⟫) ∂ν


-- @@ L138-138 verbatim
end GaussianGraph


-- @@ L140-140 verbatim
section


-- @@ L142-142 verbatim
abbrev Label (m : ℕ) := EuclideanSpace ℝ (Fin m)


-- @@ L144-146 verbatim
def ballKernel (m : ℕ) (η : ℝ) (y : Fin m → ℝ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)


-- @@ L148-148 verbatim
section BallDensity


-- @@ L150-151 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L153-155 verbatim
def rowMap {m : ℕ} (A : Fin m → E) : E →L[ℝ] Label m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))


-- @@ L157-159 verbatim
def ballAverage (ν : Measure E) (m : ℕ) (η : ℝ)
    (z : (Fin m → E) × Label m) : ℝ≥0∞ :=
  vectorSmoothing ν m (ballKernel m η) (z.1, WithLp.ofLp z.2)


-- @@ L161-162 verbatim
def lowerDensity (ν : Measure E) (m : ℕ) (z : (Fin m → E) × Label m) : ℝ≥0∞ :=
  liminf (fun n : ℕ => ballAverage ν m ((n : ℝ) + 1)⁻¹ z) atTop


-- @@ L164-164 verbatim
end BallDensity


-- @@ L166-167 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L169-170 verbatim
def AllBallMass (ν : Measure E) (K a : ℝ) : Prop :=
  ∀ b : E, ∀ t : ℝ, 0 < t → ν (Metric.closedBall b t) ≤ ENNReal.ofReal (K * t ^ a)


-- @@ L172-172 verbatim
end


-- @@ L174-174 verbatim
section Rotations


-- @@ L176-177 verbatim
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


-- @@ L179-179 verbatim
abbrev Rotation := unitary (E →L[ℝ] E)


-- @@ L181-181 verbatim
instance rotationMeasurableSpace : MeasurableSpace (Rotation E) := borel (Rotation E)


-- @@ L183-183 verbatim
instance rotationBorelSpace : BorelSpace (Rotation E) := ⟨rfl⟩


-- @@ L185-195 verbatim
instance rotationCompact : CompactSpace (Rotation E) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply (Metric.isBounded_closedBall (x := (0 : E →L[ℝ] E)) (r := 1)).subset (s := (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)))
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases h : Subsingleton E
  · have := h
    simp
  · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp h
    exact (CStarRing.norm_of_mem_unitary hU).le


-- @@ L197-198 verbatim
def rotationLaw : Measure (Rotation E) :=
  ((Measure.haar : Measure (Rotation E)) Set.univ)⁻¹ • Measure.haar


-- @@ L200-200 verbatim
variable {E}


-- @@ L202-202 verbatim
variable [MeasurableSpace E] [BorelSpace E]


-- @@ L204-205 verbatim
def rotateRows {ι : Type*} (O : Rotation E) (v : ι → E) : ι → E :=
  fun i => (O : E →L[ℝ] E) (v i)


-- @@ L207-207 verbatim
end Rotations


-- @@ L209-209 verbatim
section Triangular


-- @@ L211-213 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- @@ L215-216 verbatim
def coordinateMap {m : ℕ} (A : Fin m → E) : E →ₗ[ℝ] (Fin m → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)) ∘ₗ (rowMap A).toLinearMap


-- @@ L218-218 verbatim
end Triangular


-- @@ L220-220 verbatim
section CoordinateDensity


-- @@ L222-224 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- @@ L226-227 verbatim
def coordinateDensity (ν : Measure E) (m : ℕ) (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  lowerDensity ν m (z.1, WithLp.toLp 2 z.2)


-- @@ L229-229 verbatim
end CoordinateDensity


-- @@ L231-231 verbatim
section


-- @@ L233-234 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L236-237 verbatim
def frameLaw {m : ℕ} (u : Fin m → E) : Measure (Fin m → E) :=
  (rotationLaw E).map (fun O => rotateRows O u)


-- @@ L239-239 verbatim
end


-- @@ L241-241 verbatim
section


-- @@ L243-244 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L246-246 verbatim
def rieszKernel (α : ℝ) (z s : E) : ℝ≥0∞ := (ENNReal.ofReal ‖s-z‖)^(-α)


-- @@ L248-249 verbatim
def rieszPotential (α : ℝ) (h : E → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ z : E, ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw


-- @@ L251-251 verbatim
end


-- @@ L253-253 verbatim
section


-- @@ L255-256 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L258-259 verbatim
def mixRows {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) : Fin k → E :=
  fun i => ∑ j, M i j • X j


-- @@ L261-262 verbatim
def polarRadial {k : ℕ} (X : Fin k → E) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt (Matrix.gram ℝ X)


-- @@ L264-265 verbatim
def rawPolarRows {k : ℕ} (X : Fin k → E) : Fin k → E :=
  mixRows (polarRadial X)⁻¹ X


-- @@ L267-269 verbatim
def polarRows {k : ℕ} (u X : Fin k → E) : Fin k → E := by
  classical
  exact if LinearIndependent ℝ X then rawPolarRows X else u


-- @@ L271-271 verbatim
end


-- @@ L273-273 verbatim
section


-- @@ L275-276 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L278-278 verbatim
def unitBallVolume (k : ℕ) : ℝ≥0∞ := (volume : Measure (Label k)) (Metric.closedBall 0 1)


-- @@ L280-281 verbatim
def unitBallLaw (k : ℕ) : Measure (Label k) :=
  (unitBallVolume k)⁻¹ • volume.restrict (Metric.closedBall 0 1)


-- @@ L283-285 verbatim
def normalizedDensity (ν : Measure E) (k : ℕ) (u : Fin k → E)
    (z : (Fin k → E) × Label k) : ℝ≥0∞ :=
  unitBallVolume k * lowerDensity ν k (polarRows u z.1,z.2)


-- @@ L287-288 verbatim
def sphereWeightedRestriction (h : E → ℝ≥0∞) (H : Set E) : Measure E :=
  (NoiselessRegression.ambientSphereLaw.withDensity h).restrict H


-- @@ L290-290 verbatim
end


-- @@ L292-292 verbatim
section


-- @@ L294-294 verbatim
universe u


-- @@ L296-297 verbatim
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L299-301 verbatim
def capMeasure (c : E) (r : ℝ) : Measure E :=
  (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ •
    NoiselessRegression.ambientSphereLaw.restrict (Metric.closedBall c r)


-- @@ L303-316 verbatim
structure CapDictionary (c : E) (r α : ℝ) where
  I : Type u
  countable : Countable I
  center : I → E
  radius : I → ℝ
  center_norm : ∀ i, ‖center i‖ = 1
  radius_pos : ∀ i, 0 < radius i
  radius_le : ∀ i, radius i ≤ r
  parent : I
  parent_center : center parent = c
  parent_radius : radius parent = r
  proper : ∀ R : ℝ, {i | (r/radius i)^α ≤ R}.Finite
  cover : ∀ (s : E), ‖s‖ = 1 → ∀ t : ℝ, 0 < t → t ≤ 1/4 →
    ∃ i, 4*r*t ≤ radius i ∧ radius i < 8*r*t ∧ dist s (center i) ≤ radius i/2


-- @@ L318-318 verbatim
end


-- @@ L320-320 verbatim
section


-- @@ L322-323 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L325-326 verbatim
def radialLabel {k : ℕ} (X : Fin k → E) (y : Label k) : Label k :=
  WithLp.toLp 2 (polarRadial X *ᵥ y.ofLp)


-- @@ L328-329 verbatim
def capKernelValue {k : ℕ} (K : (Fin k → E) × Label k → ℝ≥0∞) (s : E) : ℝ≥0∞ :=
  ∫⁻ X, K (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E)


-- @@ L331-332 verbatim
def capReferenceLabel {k : ℕ} (c : E) (r : ℝ) (X : Fin k → E) (z : Label k) : Label k :=
  rowMap X c + r • radialLabel X z


-- @@ L334-335 verbatim
def capReference {k : ℕ} (K : (Fin k → E) × Label k → ℝ≥0∞) (c : E) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ X, ∫⁻ z, K (X,capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E)


-- @@ L337-337 verbatim
end


-- @@ L339-340 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


-- @@ L342-344 verbatim
def fractionalBlock {J : Type*} [Fintype J] {k : ℕ}
    (Q : J → (Fin k → E) × Label k → ℝ≥0∞) (f : J → E → ℝ≥0∞) (s : E) : ℝ≥0∞ :=
  ∫⁻ X, ∑ j, Q j (X,rowMap X s)*f j s ∂Measure.pi (fun _ => stdGaussian E)


-- @@ L346-346 verbatim
end ProjectionMoments


-- @@ L348-348 verbatim
open MeasureTheory ProbabilityTheory Set Filter unitInterval

-- @@ L349-349 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L350-350 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L351-351 verbatim
namespace NoiselessRegression


-- @@ L353-353 verbatim
namespace Learner


-- @@ L355-355 verbatim
section


-- @@ L357-357 verbatim
universe u


-- @@ L359-359 verbatim
variable {d M T : ℕ} {Ω : Type u}


-- @@ L361-361 verbatim
abbrev TaggedState (M T : ℕ) := Sum (State M) (Fin (T+1) × State M)


-- @@ L363-363 verbatim
instance taggedMeasurableSpace : MeasurableSpace (TaggedState M T) := ⊤


-- @@ L365-366 verbatim
def taggedStart (a : Bool × State M) : TaggedState M T :=
  if a.1 then .inr (⟨0,by omega⟩,a.2) else .inl a.2


-- @@ L368-368 verbatim
end


-- @@ L370-370 verbatim
universe u


-- @@ L372-372 verbatim
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]


-- @@ L374-377 verbatim
structure MeasurableRules (L : Learner d M T Ω) : Prop where
  initial : Measurable L.initialChoice
  transition : ∀ t j, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 j z.2)
  output : ∀ t j, Measurable (fun ω => L.output t ω j)


-- @@ L379-379 verbatim
end Learner


-- @@ L381-387 verbatim
structure FiniteKernelLearner (d M T : ℕ) where
  initial : Measure (Bool × State M)
  initial_probability : IsProbabilityMeasure initial
  transition : ℕ → State M → (Vector d × ℝ) → Measure (Bool × State M)
  transition_probability : ∀ t j obs, IsProbabilityMeasure (transition t j obs)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t j, IsProbabilityMeasure (output t j)


-- @@ L389-389 verbatim
namespace FiniteKernelLearner


-- @@ L391-391 verbatim
variable {d M T : ℕ}


-- @@ L393-394 verbatim
structure CompletedRules (K : FiniteKernelLearner d M T) : Prop where
  transition : ∀ t j a, AEMeasurable (fun obs => K.transition t j obs {a}) (observationReference d)


-- @@ L396-396 verbatim
end FiniteKernelLearner


-- @@ L398-398 verbatim
section


-- @@ L400-401 verbatim
variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]


-- @@ L403-405 verbatim
def kernelRun (P : ℕ → J → O → Measure J) : (n : ℕ) → J → (Fin n → O) → Measure J
  | 0, j, _ => Measure.dirac j
  | n+1, j, obs => (kernelRun P n j (Fin.init obs)).bind (fun a => P (n+1) a (obs (Fin.last n)))


-- @@ L407-407 verbatim
end


-- @@ L409-409 verbatim
namespace FiniteKernelLearner


-- @@ L411-411 verbatim
section


-- @@ L413-413 verbatim
open Learner


-- @@ L415-415 verbatim
variable {d M T : ℕ}


-- @@ L417-417 verbatim
abbrev Tape (M T : ℕ) := (Bool × State M) × ((Fin T → I) × I)


-- @@ L419-420 verbatim
def destination (t : ℕ) (h : t ≤ T) (a : Bool × State M) : TaggedState M T :=
  if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2


-- @@ L422-426 verbatim
def taggedKernel (K : FiniteKernelLearner d M T) (t : ℕ) :
    TaggedState M T → (Vector d × ℝ) → Measure (TaggedState M T)
  | .inr a, _ => Measure.dirac (.inr a)
  | .inl j, obs => if ht : t ≤ T then (K.transition t j obs).map (destination t ht)
    else Measure.dirac (.inl j)


-- @@ L428-430 verbatim
def terminalOutput (K : FiniteKernelLearner d M T) : TaggedState M T → Measure (UnitSphere d)
  | .inl j => K.output T j
  | .inr (t,j) => K.output t j


-- @@ L432-432 verbatim
end


-- @@ L434-434 verbatim
open Learner


-- @@ L436-436 verbatim
variable {d M T : ℕ}


-- @@ L438-438 verbatim
abbrev Result (d M : ℕ) := (ℕ × State M) × UnitSphere d


-- @@ L440-442 verbatim
def terminalTag : TaggedState M T → ℕ × State M
  | .inl j => (T,j)
  | .inr (t,j) => (t,j)


-- @@ L444-445 verbatim
def terminalJointOutput (K : FiniteKernelLearner d M T) (j : TaggedState M T) : Measure (Result d M) :=
  (K.terminalOutput j).map (fun y => (terminalTag j,y))


-- @@ L447-448 verbatim
def jointExperimentLaw (K : FiniteKernelLearner d M T) (obs : Fin T → (Vector d × ℝ)) : Measure (Result d M) :=
  K.initial.bind (fun a => (kernelRun K.taggedKernel T (taggedStart a) obs).bind K.terminalJointOutput)


-- @@ L450-453 verbatim
def uniformSuccess (K : FiniteKernelLearner d M T) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
      {r | angularError z.1 r.2 ≤ ε} ∂((uniformSphere d).prod (sampleLaw d T))


-- @@ L455-458 verbatim
def uniformFixedSuccess (K : FiniteKernelLearner d M T) (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
      {r | r.1.1 = t ∧ angularError z.1 r.2 ≤ ε} ∂((uniformSphere d).prod (sampleLaw d T))


-- @@ L460-460 verbatim
end FiniteKernelLearner


-- @@ L462-462 verbatim
section


-- @@ L464-464 verbatim
universe u


-- @@ L466-467 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


-- @@ L469-469 verbatim
namespace Learner


-- @@ L471-471 verbatim
variable {d M T : ℕ} {Ω : Type u}


-- @@ L473-476 verbatim
def uniformFixedSuccess [MeasurableSpace Ω] (L : Learner d M T Ω) (ρ : Measure Ω)
    (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | (L.terminal z.1 z.2.1 z.2.2).1 = t ∧ angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}


-- @@ L478-478 verbatim
end Learner


-- @@ L480-480 verbatim
end


-- @@ L482-482 verbatim
namespace FiniteKernelLearner


-- @@ L484-484 verbatim
section


-- @@ L486-486 verbatim
universe u


-- @@ L488-488 verbatim
variable {d M T : ℕ}


-- @@ L490-492 verbatim
def seededSuccess {Ξ : Type u} [MeasurableSpace Ξ]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, (K ξ).uniformSuccess ε ∂ρ


-- @@ L494-496 verbatim
def seededFixedSuccess {Ξ : Type u} [MeasurableSpace Ξ]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) (t : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, (K ξ).uniformFixedSuccess ε t ∂ρ


-- @@ L498-505 verbatim
def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ)^2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)


-- @@ L507-507 verbatim
end


-- @@ L509-509 verbatim
universe u


-- @@ L511-511 verbatim
variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]


-- @@ L513-515 verbatim
def conditionalSuccess (K : FiniteKernelLearner d M T) (ε : ℝ)
    (s : UnitSphere d) (x : Samples d T) : ℝ≥0∞ :=
  K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) {r | Learner.angularError s r.2 ≤ ε}


-- @@ L517-519 verbatim
def seededPointwiseSuccess (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ)
    (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  ∫⁻ z : Ξ × Samples d T, (K z.1).conditionalSuccess ε s z.2 ∂ρ.prod (sampleLaw d T)


-- @@ L521-524 verbatim
def JointSuccessMeasurable (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) (ε : ℝ) : Prop :=
  AEMeasurable (fun z : UnitSphere d × (Ξ × Samples d T) =>
    (K z.2.1).conditionalSuccess ε z.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))


-- @@ L526-535 verbatim
def SubquadraticMemoryWithPointwise : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d:ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
    ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
    ((2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε ∨
      (JointSuccessMeasurable K ρ ε ∧ ∀ s, (2/3 : ℝ≥0∞) ≤ seededPointwiseSuccess K ρ ε s)) →
    c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ)


-- @@ L537-537 verbatim
end FiniteKernelLearner


-- @@ L539-539 verbatim
end NoiselessRegression


-- @@ L541-541 verbatim
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace


-- @@ L543-543 verbatim
open NoiselessRegression NoiselessRegression.FiniteKernelLearner


-- @@ L545-545 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Topology


-- @@ L547-547 verbatim
universe u


-- @@ L549-549 verbatim
namespace ProjectionMoments


-- @@ L551-569 verbatim
def IntegratedFrameMoment : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d k q : ℕ) (β K R : ℝ)
      (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
      (z : EuclideanSpace ℝ (Fin d)) (u : Fin k → EuclideanSpace ℝ (Fin d)),
      1 ≤ k → 2 ≤ q → k+q ≤ d → 0 < β → β ≤ d →
      1 ≤ β-k-((q:ℝ)-2) → 0 ≤ K → 0 < R →
      ν.support ⊆ Metric.closedBall z R → AllBallMass ν K β →
      Orthonormal ℝ u →
      (∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) →
      Measurable (coordinateDensity ν k) ∧
      (∀ᵐ A ∂frameLaw u,
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity ν k (A,y)) =
          ν.map (coordinateMap A)) ∧
      (∀ (A : Fin k → EuclideanSpace ℝ (Fin d)), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ,
          R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ → coordinateDensity ν k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity ν k (A,y)^q ∂volume ∂frameLaw u) ^ (1/(q:ℝ)) ≤
        ENNReal.ofReal (C^d * (C*Real.sqrt d)^((k:ℝ)*(1-1/(q:ℝ))) *
          K * R^(β-(k:ℝ)*(1-1/(q:ℝ))))


-- @@ L571-589 verbatim
def NormalizedUnitBallMoment : Prop :=
  ∀ D : ℝ, 0 < D →
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let lam : ℝ := ((d:ℝ)-1)/2
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
        (u : Fin k → EuclideanSpace ℝ (Fin d)),
        ν Set.univ ≤ 1 → ν.support ⊆ Metric.closedBall 0 1 →
        AllBallMass ν (D^d) lam → Orthonormal ℝ u →
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) →
        Measurable (normalizedDensity ν k u) ∧
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
            (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X))) ∧
        (∀ X y, 1 < ‖y‖ → normalizedDensity ν k u (X,y) = 0) ∧
        (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^k ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
          ENNReal.ofReal (Real.exp (C_D*d*k))


-- @@ L591-611 verbatim
def AllRadiiSphereMoment : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable f → (∀ s, f s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity f) K β →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∀ u : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ u →
      let μ := sphereWeightedRestriction f (Metric.closedBall z R)
      Measurable (coordinateDensity μ k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity μ k (A,y)) =
          μ.map (coordinateMap A)) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ, R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ →
          coordinateDensity μ k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity μ k (A,y)^k ∂volume ∂frameLaw u) ^ (1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d*(C*Real.sqrt d)^((k:ℝ)*(1-1/(k:ℝ)))*
          K*R^(β-(k:ℝ)*(1-1/(k:ℝ))))


-- @@ L613-627 verbatim
def PositiveCapDomination : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∀ K : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (K j)) → (∀ z, ∑ j, K j z ≤ 1) →
      (∑ j, capReference (K j) c r) ≤ 1 ∧
      ∀ j, ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference (K j) c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue (K j)) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞


-- @@ L629-645 verbatim
def DeterministicOffsetDensity : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/8
      let α : ℝ := (d:ℝ)/2
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h → (∀ s, h s ≤ 1) →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ ρ : ℝ, 0 < ρ →
      ∀ H : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet H → H ⊆ Metric.closedBall z ρ →
      rieszPotential α h < ∞ ∧
      Measurable (lowerDensity (sphereWeightedRestriction h H) k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), LinearIndependent ℝ A →
        volume.withDensity (fun y => lowerDensity (sphereWeightedRestriction h H) k (A,y)) =
          (sphereWeightedRestriction h H).map (rowMap A)) ∧
      (∀ b : Label k, (∫⁻ A, (lowerDensity (sphereWeightedRestriction h H) k (A,rowMap A z+b))^k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))))^(1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d) * rieszPotential α h * ENNReal.ofReal (ρ^(α-k))) ∧
      (∀ A y, ‖rowMap A‖*ρ < ‖y-rowMap A z‖ →
        lowerDensity (sphereWeightedRestriction h H) k (A,y) = 0)


-- @@ L647-658 verbatim
def AllRadiiBlockBound : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ N : ℕ, ∀ f : Fin N → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ j, Measurable (f j)) → (∀ j s, f j s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ j, AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (f j)) K β) →
      ∀ Q : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (Q j)) → (∀ z, ∑ j, Q j z ≤ 1) →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (fractionalBlock Q f))
        (C^d*(N:ℝ)^(1/(k:ℝ))*K) β


-- @@ L660-668 verbatim
def HaarStreamingCost : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k))


-- @@ L670-678 verbatim
def RieszStreamingCost : Prop :=
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q))


-- @@ L680-689 verbatim
def CapFixedStoppingCost : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k))


-- @@ L691-700 verbatim
def CapTotalStoppingCost : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C*d)*(ε/2)^α*
          (Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k))


-- @@ L702-713 verbatim
def CapFixedStoppingAsymptotic : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d*(1+((t+k-1)/k:ℕ)))*(ε/2)^α)


-- @@ L715-723 verbatim
def CapTotalStoppingAsymptotic : Prop :=
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C₁*d+C₂*T-(d:ℝ)*Real.log (1/ε)/3))


-- @@ L725-730 verbatim
def KernelModelBridge : Prop :=
  ∀ d M T : ℕ, 3 ≤ d → ∀ K : FiniteKernelLearner d M T, K.CompletedRules →
    ∃ (ρ : Measure (Tape M T)) (L : Learner d M T (Tape M T)),
      IsProbabilityMeasure ρ ∧ L.MeasurableRules ∧ L.Admissible ρ ∧
      (∀ ε, L.uniformSuccess ρ ε = K.uniformSuccess ε) ∧
      (∀ ε t, L.uniformFixedSuccess ρ ε t = K.uniformFixedSuccess ε t)


-- @@ L732-739 verbatim
def MainStatement : Prop :=
  IntegratedFrameMoment ∧ NormalizedUnitBallMoment ∧ AllRadiiSphereMoment ∧
  PositiveCapDomination ∧ DeterministicOffsetDensity ∧ AllRadiiBlockBound ∧
  HaarStreamingCost.{u} ∧ RieszStreamingCost.{u} ∧ CapFixedStoppingCost.{u} ∧
  CapTotalStoppingCost.{u} ∧ CapFixedStoppingAsymptotic.{u} ∧
  CapTotalStoppingAsymptotic.{u} ∧ KernelModelBridge ∧
  NoiselessRegression.FiniteKernelLearner.SubquadraticMemoryWithPointwise.{u} ∧
  NoiselessRegression.FiniteKernelLearner.FixedQuadraticMemory.{u}


-- @@ L741-741 verbatim
end ProjectionMoments


-- @@ L743-743 verbatim
end


-- @@ L745-745 verbatim
end OAI
