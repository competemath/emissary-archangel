import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L74-74 verbatim
open scoped BigOperators Classical


-- @@ L76-76 verbatim
open scoped BigOperators Classical ContDiff


-- @@ L78-78 verbatim
namespace CanonicalRowCompletion.ActualFiber

-- @@ L79-79 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L80-80 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L81-83 verbatim
noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

-- @@ L84-86 verbatim
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)

-- @@ L87-87 verbatim
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]


-- @@ L89-137 verbatim
theorem reflectedFiber_four_mul_value
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).value
      W X 1 completedRamifiedStep k=
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun h=>Fintype.ofFinite _
  let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let f:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      (d.branch (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        ⟨h,rho,u⟩,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k
  let g:=fun (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))=>
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
        h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let α:=fun h=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape:=fun h B=>sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w:=FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q)
  have hbranch:∀h rho u B l,4*f h rho u B l=
      if rho=chosen h B then α h*shape h B*g h u B l else 0 := by
    intro h rho u B l
    exact reflectedFiber_encoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound
      J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue:d.value W X 1 completedRamifiedStep k=
      ∑h,∑rho,∑u,∑B,w B*∑l,f h rho u B l := by
    rw [reflectedFiber_value q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) _
  change 4*d.value W X 1 completedRamifiedStep k=_
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen α shape w hbranch


-- @@ L139-161 verbatim
theorem completedT_eq_reflectedFiber_idealValue
    (Ψ:Eis→*ℂ)
    (hΨperiod:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨ:∀n,‖Ψ n‖≤1)
    (K:ℝ) (hshell:∀I∈rows,K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).idealValue W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,(hshell I hI).2⟩) J
  have hs:=residual_shell q m rows R F K (fun I hI=>⟨hrows I hI,hshell I hI⟩) J
  have he:=reflectedFiber_four_mul_value q hq m hm rows R F hR hF hrows v K Ψ hΨ
    (fun I hI=>(hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [completedT_eq_compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ hΨperiod hΨ
    J W lo hi hlo hsupp hW X hX,←he]
  have hid:rowResidualPart J.val (maskIdeal q m F)=k.val:=rfl
  rw [hid,ReflectedFiberData.idealValue_at]
  ring


-- @@ L163-163 verbatim
end CanonicalRowCompletion.ActualFiber


-- @@ L165-165 verbatim
namespace CanonicalRowCompletion


-- @@ L167-167 verbatim
section

-- @@ L168-168 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein

-- @@ L169-169 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L171-172 verbatim
def actualReflectionScale : ℂ :=
  4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar


-- @@ L174-186 verbatim
theorem actual_fixedShellModels (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      actualReflectionScale 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
  let : Finite (Eis⧸Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis⧸Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  apply fixedShellModels_of_actual_fiber_identity q hq χ actualReflectionScale
  intro Ψ hperiod hnorm m hm F hF u W a b ha hs hW K X hK hX rows hrows R hR J
  exact ActualFiber.completedT_eq_reflectedFiber_idealValue q hq m hm rows R F
    (hrows R hR).1 hF (fun I hI=>(hrows I hI).1) u Ψ hperiod hnorm K
    (fun I hI=>(hrows I hI).2) J W a b ha hs hW X hX


-- @@ L188-193 verbatim
theorem exists_actual_fixedShellModels (q:ℕ) [NeZero q] (χ:DirichletCharacter ℂ q) :
    ∃(rays:ℕ) (scale:ℂ),
      HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
        rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  exact ⟨fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q (NeZero.ne q)),
    actualReflectionScale,actual_fixedShellModels q (NeZero.ne q) χ⟩


-- @@ L195-195 verbatim
end


-- @@ L197-198 verbatim
theorem dirichletTarget_unconditional : ShortDraft.DirichletTarget :=
  dirichletTarget_of_reflection_shells exists_actual_fixedShellModels


-- @@ L200-200 verbatim
end CanonicalRowCompletion


-- @@ L202-202 verbatim
namespace ShortDraft


-- @@ L204-208 verbatim
theorem dirichlet_LFunction_ne_zero (q:ℕ) [NeZero q]
    (χ:DirichletCharacter ℂ q) (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s≠0 :=
  CanonicalRowCompletion.dirichletTarget_unconditional q χ s hs hpole


-- @@ L210-213 verbatim
theorem riemannZeta_ne_zero_of_re_gt (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 :=
  zeta_nonvanishing_of_dirichletTarget
    CanonicalRowCompletion.dirichletTarget_unconditional s hs hs1


-- @@ L215-215 verbatim
end ShortDraft


-- @@ L217-217 verbatim
end


-- @@ L219-219 verbatim
end OAI
