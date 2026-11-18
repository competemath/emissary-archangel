import OAI.NumberTheory.DirichletL.Detector.HighSeries
import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import OAI.NumberTheory.DirichletL.IdealEuler


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical

-- @@ L9-9 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L10-10 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open ConcretePrimeRowBridge CubicEisenstein

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
local notation "Id" => Ideal O


-- @@ L15-16 verbatim
def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L


-- @@ L18-23 verbatim
lemma highSupport_mul (I J K L I' J' K' L' : Id) (hcop : IsCoprime I I') :
    highSupport (I*I') (J*J') (K*K') (L*L') ↔
      highSupport I J K L ∧ highSupport I' J' K' L' := by
  simp only [highSupport, squarefree_mul_iff, supported_mul_iff]
  have hc := hcop.isRelPrime
  tauto


-- @@ L25-27 verbatim
lemma span_primaryGenerator_of_supported (I : Id) (hI : Supported I) :
    Ideal.span {primaryGenerator I}=I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1


-- @@ L29-32 verbatim
lemma primaryGenerator_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rwa [span_primaryGenerator_of_supported I hI,span_primaryGenerator_of_supported J hJ]


-- @@ L34-36 verbatim
lemma completed_block_dvd_cube (I J K L : Id) : I*J^3*K ∣ (I*J*K*L)^3 := by
  refine ⟨I^2*K^2*L^3,?_⟩
  ring


-- @@ L38-40 verbatim
lemma first_block_dvd (I J K L : Id) : I ∣ I*J*K*L := by
  refine ⟨J*K*L,?_⟩
  ring


-- @@ L42-44 verbatim
lemma last_block_dvd (I J K L : Id) : L ∣ I*J*K*L := by
  refine ⟨I*J*K,?_⟩
  ring


-- @@ L46-100 verbatim
theorem bareIdealHighCoefficient_mul (η : HeckeFamily.Character)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η 1 (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η 1 I J K L * bareIdealHighCoefficient η 1 I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_frequency η I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul,one_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]


-- @@ L102-104 verbatim
lemma fullIdealWeight_mul (s : ℂ) (I J : Id) :
    fullIdealWeight s (I*J)=fullIdealWeight s I*fullIdealWeight s J :=
  (IdealEuler.normWeight s).map_mul I J


-- @@ L106-114 verbatim
theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_mul η I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring


-- @@ L116-116 verbatim
end SevenEighths.ProbePhysical

-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
end OAI
