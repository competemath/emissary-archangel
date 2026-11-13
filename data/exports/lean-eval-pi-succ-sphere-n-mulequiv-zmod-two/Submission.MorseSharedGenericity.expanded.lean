import Mathlib
import Submission.Sard
import Submission.SardPrelim


-- @@ L5-19 verbatim
/-!
# Shared finite Sard parameters and compact regularity stability

A global Morse perturbation must use one parameter on every overlapping chart.
Density of regular values one chart at a time is not sufficient, since finite
intersections of arbitrary dense sets need not be dense.  Sard gives the
stronger null-set statement.  A finite union of critical-value sets is still
null, so one point of any prescribed ball is simultaneously regular for every
map in a finite family.

The second ingredient needed near the fixed collars is uniform stability.
Surjectivity of a continuous linear map into a finite Euclidean target is open;
compactness upgrades pointwise persistence to one common parameter
neighborhood.
-/


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function Metric Filter MeasureTheory

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace ContDiff Topology BigOperators ENNReal


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L30-30 verbatim
/-! ## One Sard value for a finite family -/


-- @@ L32-57 verbatim
/-- Every ball contains a value which is regular for all maps in a finite
smooth family.  The proof uses the actual Sard null-set theorem, not a finite
intersection-of-dense-sets shortcut. -/
theorem exists_common_regularValue_in_ball
    {ι : Type*} [Fintype ι] {p q : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q))
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (z : EuclideanSpace ℝ (Fin q)) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ ball z r, ∀ i, IsRegularValue (f i) y := by
  classical
  let bad : Set (EuclideanSpace ℝ (Fin q)) :=
    ⋃ i : ι, f i '' {x | ¬Surjective (fderiv ℝ (f i) x)}
  have hbad : volume bad = 0 := by
    dsimp [bad]
    exact measure_iUnion_null fun i => sard_global (hf i)
  have hballPos : 0 < volume (ball z r) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)
  have hnsub : ¬ball z r ⊆ bad := by
    intro hsub
    exact hballPos.ne' (measure_mono_null hsub hbad)
  obtain ⟨y, hyball, hybad⟩ := Set.not_subset.mp hnsub
  refine ⟨y, hyball, ?_⟩
  intro i x hfx
  by_contra hsurj
  apply hybad
  exact Set.mem_iUnion.mpr ⟨i, ⟨x, hsurj, hfx⟩⟩


-- @@ L59-85 verbatim
/-- Open-domain version used by local normal/parameter maps. -/
theorem exists_common_regularValueOn_in_ball
    {ι : Type*} [Fintype ι] {p q : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin p)))
    (hU : ∀ i, IsOpen (U i))
    (f : ι → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin q))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (z : EuclideanSpace ℝ (Fin q)) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ ball z r, ∀ i, IsRegularValueOn (f i) (U i) y := by
  classical
  let bad : Set (EuclideanSpace ℝ (Fin q)) :=
    ⋃ i : ι, f i '' {x | x ∈ U i ∧
      ¬Surjective (fderivWithin ℝ (f i) (U i) x)}
  have hbad : volume bad = 0 := by
    dsimp [bad]
    exact measure_iUnion_null fun i => sard (hU i) (hf i)
  have hballPos : 0 < volume (ball z r) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)
  have hnsub : ¬ball z r ⊆ bad := by
    intro hsub
    exact hballPos.ne' (measure_mono_null hsub hbad)
  obtain ⟨y, hyball, hybad⟩ := Set.not_subset.mp hnsub
  refine ⟨y, hyball, ?_⟩
  intro i x hxU hfx
  by_contra hsurj
  apply hybad
  exact Set.mem_iUnion.mpr ⟨i, ⟨x, ⟨hxU, hsurj⟩, hfx⟩⟩


-- @@ L87-87 verbatim
/-! ## Compact uniform stability of surjectivity -/


-- @@ L89-105 verbatim
/-- A jointly continuous family of linear maps which is surjective at one
parameter on a compact set remains surjective there for every sufficiently
nearby parameter. -/
theorem eventually_uniform_surjective
    {P X E : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {K : Set X} (hK : IsCompact K)
    (L : P → X → E →L[ℝ] (Fin q → ℝ))
    (hL : Continuous fun z : P × X => L z.1 z.2)
    {p₀ : P} (hzero : ∀ x ∈ K, Surjective (L p₀ x)) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, Surjective (L p x) := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hmem : L p₀ x ∈
      {A : E →L[ℝ] (Fin q → ℝ) | Surjective A} := hzero x hx
  exact hL.continuousAt
    (isOpen_setOf_surjective.mem_nhds hmem)


-- @@ L107-128 verbatim
/-- Useful affine specialization: a compact family of surjective maps stays
surjective after adding one uniformly small scalar multiple of a continuous
family. -/
theorem eventually_uniform_surjective_add_smul
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {K : Set X} (hK : IsCompact K)
    (L₀ Δ : X → E →L[ℝ] (Fin q → ℝ))
    (hL₀ : Continuous L₀) (hΔ : Continuous Δ)
    (hsurj : ∀ x ∈ K, Surjective (L₀ x)) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ x ∈ K,
      Surjective (L₀ x + s • Δ x) := by
  let L : ℝ → X → E →L[ℝ] (Fin q → ℝ) :=
    fun s x => L₀ x + s • Δ x
  have hL : Continuous fun z : ℝ × X => L z.1 z.2 := by
    exact (hL₀.comp continuous_snd).add
      (continuous_fst.smul (hΔ.comp continuous_snd))
  have hzero : ∀ x ∈ K, Surjective (L 0 x) := by
    intro x hx
    simpa [L] using hsurj x hx
  simpa [L] using
    (eventually_uniform_surjective hK L hL hzero)


-- @@ L130-130 verbatim
/-! ## Compact stability of the Morse condition -/


-- @@ L132-135 verbatim
/-- A first/second derivative jet is Morse-good when either its gradient is
nonzero or its Hessian is invertible. -/
def MorseJetGood : Set (E₂ × (E₂ →L[ℝ] E₂)) :=
  {J | J.1 ≠ 0 ∨ Bijective J.2}


-- @@ L137-161 verbatim
/-- Morse-good jets form an open set.  This is the precise openness statement
needed to keep all previously processed compact chart cores Morse while a
later local Sard tilt is chosen sufficiently small. -/
theorem isOpen_morseJetGood : IsOpen MorseJetGood := by
  have hgrad : IsOpen {J : E₂ × (E₂ →L[ℝ] E₂) | J.1 ≠ 0} := by
    have hzero : IsClosed ({0} : Set E₂) := isClosed_singleton
    have heq : {J : E₂ × (E₂ →L[ℝ] E₂) | J.1 ≠ 0} =
        Prod.fst ⁻¹' ({0} : Set E₂)ᶜ := by
      ext J
      simp
    rw [heq]
    exact hzero.isOpen_compl.preimage
      (continuous_fst : Continuous fun J : E₂ × (E₂ →L[ℝ] E₂) => J.1)
  have hhess : IsOpen {J : E₂ × (E₂ →L[ℝ] E₂) | Bijective J.2} := by
    have hopen : IsOpen {A : E₂ →L[ℝ] E₂ | IsUnit A} := Units.isOpen
    have hpre := hopen.preimage
      (continuous_snd : Continuous fun J : E₂ × (E₂ →L[ℝ] E₂) => J.2)
    have heq : {J : E₂ × (E₂ →L[ℝ] E₂) | Bijective J.2} =
        Prod.snd ⁻¹' {A : E₂ →L[ℝ] E₂ | IsUnit A} := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_preimage,
        ContinuousLinearMap.isUnit_iff_bijective]
    rw [heq]
    exact hpre
  exact hgrad.union hhess


-- @@ L163-175 verbatim
/-- Joint continuity of the gradient/Hessian jet upgrades Morse-goodness at
one parameter to one common parameter neighborhood on a compact set. -/
theorem eventually_uniform_morseJetGood
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    (jet : P → X → E₂ × (E₂ →L[ℝ] E₂))
    (hjet : Continuous fun z : P × X => jet z.1 z.2)
    {p₀ : P} (hgood : ∀ x ∈ K, jet p₀ x ∈ MorseJetGood) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, jet p x ∈ MorseJetGood := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  exact hjet.continuousAt
    (isOpen_morseJetGood.mem_nhds (hgood x hx))


-- @@ L177-177 verbatim
end Submission
