import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.StandardPrime


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology

-- @@ L27-27 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L28-28 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L29-29 verbatim
open NormedSpace

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped ComplexOrder

-- @@ L32-32 verbatim
open scoped InnerProductSpace

-- @@ L33-33 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L34-34 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L35-35 verbatim
open UniformSpace



-- @@ L38-38 verbatim
namespace KirchbergRordam.JiangSu



-- @@ L41-52 verbatim
structure StepParameters where
  p : ℕ
  q : ℕ
  k₀ : ℕ
  k₁ : ℕ
  p_two : 2≤p
  q_two : 2≤q
  coprime : p.Coprime q
  next_coprime : (p*k₀).Coprime (q*k₁)
  multipliers_coprime : k₀.Coprime k₁
  grow₀ : 2*p*q<k₀
  grow₁ : 2*p*q<k₁



-- @@ L55-69 verbatim
def parameters (n : ℕ) : StepParameters where
  p := StandardPrimeMultiplicity.size n
  q := StandardPrimeMultiplicity.size n+1
  k₀ := StandardPrimeMultiplicity.k₀ (StandardPrimeMultiplicity.size n)
  k₁ := StandardPrimeMultiplicity.k₁ (StandardPrimeMultiplicity.size n)
  p_two := StandardPrimeMultiplicity.size_two n
  q_two := by have := StandardPrimeMultiplicity.size_two n; omega
  coprime := StandardPrimeMultiplicity.size_coprime n
  next_coprime := by
    rw [←(StandardPrimeMultiplicity.next_factors _ (StandardPrimeMultiplicity.size_two n)).1,
      ←(StandardPrimeMultiplicity.next_factors _ (StandardPrimeMultiplicity.size_two n)).2]
    exact StandardPrimeMultiplicity.next_coprime _
  multipliers_coprime := StandardPrimeMultiplicity.multipliers_coprime _ (StandardPrimeMultiplicity.size_two n)
  grow₀ := (StandardPrimeMultiplicity.multiplier_growth _ (StandardPrimeMultiplicity.size_two n)).1
  grow₁ := (StandardPrimeMultiplicity.multiplier_growth _ (StandardPrimeMultiplicity.size_two n)).2



-- @@ L72-73 verbatim
instance : Nontrivial Algebra := inferInstanceAs
  (Nontrivial (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))

-- @@ L74-75 verbatim
instance : TopologicalSpace.SeparableSpace Algebra := inferInstanceAs
  (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))


-- @@ L77-77 verbatim
open StandardPrimeMultiplicity


-- @@ L79-80 verbatim
lemma initial_sizes : (parameters 0).p=2 ∧ (parameters 0).q=3 := by
  constructor <;> rfl

-- @@ L81-84 verbatim
lemma next_sizes (n : ℕ) :
    (parameters (n+1)).p=(parameters n).p*(parameters n).k₀ ∧
    (parameters (n+1)).q=(parameters n).q*(parameters n).k₁ :=
  next_factors (size n) (size_two n)


-- @@ L86-90 verbatim
lemma lower_count (n : ℕ) :
    (StandardPrimeModel.presentation.stepData n).lower=
      ((parameters n).k₀*(parameters n).k₁)%((parameters n).q*(parameters n).k₁) := by
  change lower (size n)=(k₀ (size n)*k₁ (size n))%((size n+1)*k₁ (size n))
  rw [←(next_factors _ (size_two n)).2,zero_remainder _ (size_two n)]


-- @@ L92-96 verbatim
lemma upper_count (n : ℕ) :
    (StandardPrimeModel.presentation.stepData n).upper=
      ((parameters n).k₀*(parameters n).k₁)%((parameters n).p*(parameters n).k₀) := by
  change upper (size n)=(k₀ (size n)*k₁ (size n))%(size n*k₀ (size n))
  rw [←(next_factors _ (size_two n)).1,one_remainder _ (size_two n)]

-- @@ L97-104 verbatim
lemma middle_count (n : ℕ) :
    (StandardPrimeModel.presentation.stepData n).middle=
      (parameters n).k₀*(parameters n).k₁-
      (StandardPrimeModel.presentation.stepData n).lower-
      (StandardPrimeModel.presentation.stepData n).upper := by
  have h := total_slots (size n) (size_two n)
  change middle (size n)=k₀ (size n)*k₁ (size n)-lower (size n)-upper (size n)
  omega

-- @@ L105-111 verbatim
lemma number_eigenpaths (n : ℕ) :
    Fintype.card (GeneralDropSystem.Slot (StandardPrimeModel.presentation.stepData n))=
      (parameters n).k₀*(parameters n).k₁ := by
  simp only [GeneralDropSystem.Slot,GeneralDropSystem.Low,GeneralDropSystem.High,
    GeneralDropSystem.Mid,Fintype.card_sum,Fintype.card_fin]
  change lower (size n)+(upper (size n)+middle (size n))=k₀ (size n)*k₁ (size n)
  rw [←add_assoc,total_slots _ (size_two n)]



-- @@ L114-114 verbatim
def Stage (n : ℕ) : Type := StandardPrimeModel.presentation.Stage n

-- @@ L115-116 verbatim
instance (n : ℕ) : CStarAlgebra (Stage n) :=
  inferInstanceAs (CStarAlgebra (StandardPrimeModel.presentation.Stage n))

-- @@ L117-118 verbatim
instance (n : ℕ) : Nontrivial (Stage n) :=
  inferInstanceAs (Nontrivial (StandardPrimeModel.presentation.Stage n))

-- @@ L119-120 verbatim
def connecting (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n+1) :=
  GeneralDropSystem.step (StandardPrimeModel.presentation.stepData n)

-- @@ L121-122 verbatim
lemma connecting_norm (n : ℕ) (f : Stage n) : ‖connecting n f‖=‖f‖ :=
  GeneralDropSystem.step_norm (StandardPrimeModel.presentation.stepData n) f



-- @@ L125-132 verbatim
lemma connecting_formula (n : ℕ) (f : Stage n) (t : unitInterval) :
    (connecting n f).val t=
      MatrixDiagonalPath.interpolate
        (GeneralDropSystem.zeroReindex (StandardPrimeModel.presentation.stepData n))
        (GeneralDropSystem.oneReindex (StandardPrimeModel.presentation.stepData n)) t
        (MatrixDiagonalPath.evaluationBlock
          (GeneralDropSystem.eigenpath (StandardPrimeModel.presentation.stepData n)) t f.val) :=
  GeneralDropSystem.rawStep_apply (StandardPrimeModel.presentation.stepData n) f.val t

-- @@ L133-133 verbatim
def inclusion (n : ℕ) : Stage n →⋆ₐ[ℂ] Algebra := StandardPrimeModel.presentation.inclusion n

-- @@ L134-135 verbatim
lemma inclusion_norm (n : ℕ) (f : Stage n) : ‖inclusion n f‖=‖f‖ :=
  StandardPrimeModel.presentation.norm_inclusion n f

-- @@ L136-138 verbatim
lemma inclusion_connecting (n : ℕ) (f : Stage n) :
    inclusion (n+1) (connecting n f)=inclusion n f :=
  StandardPrimeModel.presentation.inclusion_step n f

-- @@ L139-140 verbatim
lemma dense_stages : DenseRange (fun x : Σ n, Stage n => inclusion x.1 x.2) :=
  StandardPrimeModel.presentation.denseRange_inclusion



-- @@ L143-143 verbatim
lemma algebra_is_recipe_limit : Algebra=CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system := rfl



-- @@ L146-148 verbatim
theorem equiv_arithmetic_presentation (S : PrimeDropPresentation) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ)≤Filter.cofinite) : Nonempty (Algebra ≃⋆ₐ[ℂ] S.Algebra) :=
  StandardPrimeModel.presentation.equiv S ω hω

-- @@ L149-149 verbatim
end KirchbergRordam.JiangSu


-- @@ L151-151 verbatim
namespace KirchbergRordam.PrimeDropPresentation

-- @@ L152-152 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L153-153 verbatim
variable (S : PrimeDropPresentation)

-- @@ L154-156 verbatim
def stageTrace (n : ℕ) : Traces.State (S.Stage n) :=
  Traces.pullback (Traces.matrixState (Fin (S.size n) × Fin (S.size n+1)))
    (PrimeDimensionDrop.evaluation (S.size n) (S.size n+1) 0)

-- @@ L157-158 verbatim
theorem trace_exists : Nonempty (Traces.State S.Algebra) :=
  Traces.exists_inductive_trace S.system S.stageTrace

-- @@ L159-160 verbatim
theorem trace_unique (τ σ : Traces.State S.Algebra) : τ=σ :=
  Traces.unique_of_halfFlip (HalfFlip.exists_half_flip S) τ σ



-- @@ L163-171 verbatim
theorem projectionless (p : S.Algebra) (hp : IsStarProjection p) : p=0 ∨ p=1 := by
  obtain ⟨v,hv⟩ := S.denseRange_inclusion.exists_dist_lt p (show (0:ℝ)<1/100 by norm_num)
  have h : ‖S.inclusion v.1 v.2-p‖<1/100 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hv
  exact ProjectionRounding.projection_trivial_from_approximation
    (S.inclusion v.1) (S.inclusion_isometry v.1)
    (fun e he => PrimeProjectionless.prime_idempotent
      (S.size v.1) (S.size v.1+1)
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)) e he) v.2 p hp h

-- @@ L172-172 verbatim
end KirchbergRordam.PrimeDropPresentation


-- @@ L174-174 verbatim
namespace KirchbergRordam.JiangSu


-- @@ L176-178 verbatim
theorem hom_injective {C : Type} [CStarAlgebra C] [Nontrivial C]
    (φ : Algebra →⋆ₐ[ℂ] C) : Function.Injective φ :=
  StandardPrimeModel.presentation.hom_injective φ

-- @@ L179-180 verbatim
theorem trace_exists : Nonempty (Traces.State Algebra) :=
  StandardPrimeModel.presentation.trace_exists

-- @@ L181-182 verbatim
theorem trace_unique (τ σ : Traces.State Algebra) : τ=σ :=
  StandardPrimeModel.presentation.trace_unique τ σ

-- @@ L183-184 verbatim
theorem projectionless (p : Algebra) (hp : IsStarProjection p) : p=0 ∨ p=1 :=
  StandardPrimeModel.presentation.projectionless p hp


-- @@ L186-187 verbatim
theorem no_characters : IsEmpty (Algebra →⋆ₐ[ℂ] ℂ) :=
  ⟨fun χ => dimensionDrop23_no_character.false (χ.comp (inclusion 0))⟩

-- @@ L188-188 verbatim
end KirchbergRordam.JiangSu

-- @@ L189-189 verbatim
end


-- @@ L191-191 verbatim
end OAI
