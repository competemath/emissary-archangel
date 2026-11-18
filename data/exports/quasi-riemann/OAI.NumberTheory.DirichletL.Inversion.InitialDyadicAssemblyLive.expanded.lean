import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialDyadicAssembly

-- @@ L10-10 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L11-11 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure

-- @@ L12-12 verbatim
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource

-- @@ L13-13 verbatim
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns


-- @@ L15-15 verbatim
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)


-- @@ L17-18 verbatim
def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))


-- @@ L20-22 verbatim
variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L24-49 verbatim
theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)


-- @@ L51-63 verbatim
theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ


-- @@ L65-78 verbatim
theorem physicalBlock_live_norm
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (E:ℝ)(he:∀k:Windows a b,‖windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_norm_le_windows p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ E he


-- @@ L80-80 verbatim
end SevenEighths.InverseInitialDyadicAssembly


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
