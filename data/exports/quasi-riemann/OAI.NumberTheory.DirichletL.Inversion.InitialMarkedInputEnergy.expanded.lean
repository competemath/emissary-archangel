import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap FourierTransform

-- @@ L8-8 verbatim
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic

-- @@ L9-9 verbatim
open FirstPassCubeLabels

-- @@ L10-10 verbatim
namespace SevenEighths.InverseInitialMarkedInputEnergy

-- @@ L11-11 verbatim
open InverseMoment InverseInitialOverlapFourier InverseInitialOverlapEnergy

-- @@ L12-12 verbatim
open InverseInitialRayAttachment InverseInitialArithmetic

-- @@ L13-13 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L14-16 verbatim
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L18-39 verbatim
theorem marked_input_integrable (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=>density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*supportMobius (fun i=>Ideal.span {p i}) A*
      Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)*
      wFresh (primeProductNorm p A/Z^D))
  convert hh using 1
  funext t
  unfold initialTest childLogTest
  ring


-- @@ L41-64 verbatim
theorem marked_input_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(rows:Finset Eis)
      (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
      (wFresh:ℝ→ℂ)(Z D xj E:ℝ),0≤E→
      (∀t,(∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑u∈rows,‖∫t:ℝ,density g xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
            (childLogTest wFresh t) Z D) u)‖^2)≤C*E := by
  obtain ⟨C,hC,htransfer⟩ := polynomial_measure_energy g J
  refine ⟨C,hC,?_⟩
  intro F Ψ j rows I L a y wFresh Z D xj E hE henergy
  let ψ : Eis→ℝ→ℂ := fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
    (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
      (childLogTest wFresh t) Z D) u
  let φ : rows→ℝ→ℂ := fun u t=>ψ u.val t
  have hh := htransfer xj φ E hE
    (fun u=>marked_input_integrable p hg g F Ψ j u.val I L a y wFresh Z D xj)
    (fun t=>by
      exact (Finset.sum_coe_sort rows (fun u=>‖ψ u t‖^2)).le.trans (henergy t))
  exact (Finset.sum_coe_sort rows
    (fun u=>‖∫t:ℝ,density g xj t*ψ u t‖^2)).symm.le.trans hh


-- @@ L66-66 verbatim
end SevenEighths.InverseInitialMarkedInputEnergy


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end OAI
