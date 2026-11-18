import OAI.NumberTheory.DirichletL.Reflection.IdealBridge
import OAI.NumberTheory.DirichletL.Reflection.Norms
import OAI.NumberTheory.DirichletL.Reflection.FrozenSplit


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L8-8 verbatim
open scoped Classical BigOperators

-- @@ L9-9 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets

-- @@ L10-10 verbatim
open InverseMoment

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L14-14 verbatim
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

-- @@ L15-15 verbatim
noncomputable local instance coefficientFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _


-- @@ L17-21 verbatim
def sourceRowPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (R F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ R, p i)


-- @@ L23-27 verbatim
def sourceSlotPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  markedWithFrozen hp hg c S F * ramifiedBlock hg (fun _ => 0) S
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ S, p i)


-- @@ L29-35 verbatim
def sourceFrozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  star D.fixedFactor * frozenCore hp hg c j F * ramifiedBlock hg j F
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)


-- @@ L37-46 verbatim
def sourceColumn [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b *
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))


-- @@ L48-89 verbatim
theorem mixed_coefficient_hybrid [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg (markedActiveExponent S j) R F u m * sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m *
      sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m) *
      sourceColumn D s hc hg (markedActiveExponent S j) F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hrj : ∀ i ∈ R, markedActiveExponent S j i = 1 := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hRS hi hs
    simp only [markedActiveExponent,hn,ite_false,hRj i hi]
  have hsj : ∀ i ∈ S, markedActiveExponent S j i = 0 := by
    intro i hi
    simp only [markedActiveExponent,hi,ite_true]
  have hmask : IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro k hk
    exact hcop (fun h => Finset.disjoint_left.mp hRS hi (h ▸ hk))
  rw [mixed_model_coefficient,modelRowPhase_three_blocks D s hp hg hcop hprimary R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj,
    frozenPhase_split D hp hg (markedActiveExponent S j) R S F hRS hF hu,← Finset.mul_sum,
    full_branch_sum_hybrid (fun i => Ideal.span {p i}) hg R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj hR n b hb,ite_eq_left hmask,mul_one]
  unfold sourceRowPhase sourceSlotPhase sourceFrozenPhase sourceColumn
  ring


-- @@ L91-91 verbatim
end

-- @@ L92-92 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L94-94 verbatim
end OAI
