import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerGeometry


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialEnergyCallerSourceMask

-- @@ L10-10 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure

-- @@ L11-11 verbatim
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource

-- @@ L12-12 verbatim
open InverseInitialEnergyCallerGeometry InverseInitialProfile ConcreteTraceCRT

-- @@ L13-13 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L14-17 verbatim
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L19-20 verbatim
def coprimeSource (S:Finset (Source (ι:=ι) 0)) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common))


-- @@ L22-54 verbatim
theorem physicalBlock_coprimeSource
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(H:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j H W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (coprimeSource p S)) (w∘erasePoint)
      Ψ j H W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,coprimeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc:IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common)
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hxpoint : sourcePoint x N M∈pointSource pool S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x,hx,?_⟩
      apply Finset.mem_image.mpr
      exact ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
    have hv := pointSource_valid pool S hdiv hf _ hxpoint
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j H W₁ W₂ Φ Z D m _ hv ρ]
    have hz : outerCoefficient p hp hcop hg Ψ j (sourcePoint x N M) ρ=0 := by
      by_contra hn
      exact hc (outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x N M) ρ hn)
    simp only [hz,zero_mul,mul_zero]


-- @@ L56-65 verbatim
include hcop in
theorem retained_child_squarefree
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  obtain ⟨hxs,hcoprime⟩ := Finset.mem_filter.mp hx
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := hcoprime.symm.of_isCoprime_of_dvd_left (sourceIdeal_dvd p _ _ (hdiv x hxs))
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,sourceIdeal_squarefree p hcop _,
    sourceIdeal_squarefree p hcop _⟩


-- @@ L67-68 verbatim
def childLabels (S:Finset (Source (ι:=ι) 0)) : Finset (Ideal Eis) :=
  (coprimeSource p S).image (fun x=>sourceIdeal p x.divisor*sourceIdeal p x.overlap)


-- @@ L70-76 verbatim
include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem childLabels_ne_zero (S:Finset (Source (ι:=ι) 0)) :
    ∀f∈childLabels p S,f≠0 := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)


-- @@ L78-83 verbatim
include hcop in
theorem childLabels_squarefree (S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common) : ∀f∈childLabels p S,Squarefree f := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact retained_child_squarefree p hcop S hdiv hx 1


-- @@ L85-89 verbatim
omit [DecidableEq ι] in
theorem child_label_mem (S:Finset (Source (ι:=ι) 0))
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    (initialChild (toTuple p (sectorSource u x))).2.1∈childLabels p S :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩


-- @@ L91-94 verbatim
theorem nonzero_child_ball_neg (R:ℝ)(k:Eis)(hk:k∈nonzeroChildFrequencyBall 1 R) :
    -k∈nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul] at hk ⊢
  simpa only [map_neg,norm_neg] using hk


-- @@ L96-96 verbatim
end SevenEighths.InverseInitialEnergyCallerSourceMask


-- @@ L98-98 verbatim
end


-- @@ L100-100 verbatim
end OAI
