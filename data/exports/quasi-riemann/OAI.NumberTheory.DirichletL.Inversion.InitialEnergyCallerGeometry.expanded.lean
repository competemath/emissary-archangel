import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerReference
import OAI.NumberTheory.DirichletL.Descent.SecondSquarefree
import OAI.NumberTheory.DirichletL.Descent.ChildCutoff


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped BigOperators Classical

-- @@ L10-10 verbatim
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic

-- @@ L11-11 verbatim
namespace SevenEighths.InverseInitialEnergyCallerGeometry

-- @@ L12-12 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure

-- @@ L13-13 verbatim
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource

-- @@ L14-14 verbatim
open InverseInitialProfile InverseInitialClippedColumns ConcreteTraceCRT

-- @@ L15-15 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L16-19 verbatim
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L21-32 verbatim
theorem outerCoefficient_nonzero_coprime
    (Ψ:Eis→*ℂ)(j:Eis)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hp hcop hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc : j*(∏k∈x.common,p k)∈Ideal.span {p i} := Ideal.mul_mem_left _ j hc
  have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) x.overlap (j*(∏k∈x.common,p k))=0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃i∈x.overlap,j*(∏k∈x.common,p k)∈Ideal.span {p i}
      from ⟨i,hi,hmc⟩)]
  apply hn
  simp only [outerCoefficient,initialColumn,hz,mul_zero,zero_mul,star_zero]


-- @@ L34-46 verbatim
theorem original_nonzero_child_squarefree
    (Ψ:Eis→*ℂ)(j:Eis)(x:Source (ι:=ι) 0)(ρ:SecondRayIndex)
    (hd:x.divisor⊆x.common)
    (hn:outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ≠0)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ hn
  change IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) at hc
  have hdv := sourceIdeal_dvd p x.divisor x.common hd
  have hcd : IsCoprime (sourceIdeal p x.divisor) (sourceIdeal p x.overlap) :=
    hc.symm.of_isCoprime_of_dvd_left hdv
  exact squarefree_mul_iff.mpr ⟨hcd.isRelPrime,sourceIdeal_squarefree p hcop x.divisor,
    sourceIdeal_squarefree p hcop x.overlap⟩


-- @@ L48-53 verbatim
omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp only [map_mul,Nat.cast_mul]


-- @@ L55-69 verbatim
include hp in

theorem initial_child_row_norm (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency))‖^2=_
  have he : primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      ((u^5:Eisˣ):Eis)*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      (u:Eis)^5*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul,map_mul,norm_mul,mul_pow]
  rw [eisEmbedding_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl


-- @@ L71-77 verbatim
include hp in
theorem initial_child_row_ball (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]


-- @@ L79-98 verbatim
include hp in

theorem initial_child_enclosures
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring


-- @@ L100-100 verbatim
end SevenEighths.InverseInitialEnergyCallerGeometry


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end OAI
