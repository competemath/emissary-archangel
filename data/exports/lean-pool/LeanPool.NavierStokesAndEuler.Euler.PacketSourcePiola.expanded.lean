/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeSupport


-- @@ L17-17 verbatim
/-! Related estimates used together by the same construction modules. -/


-- @@ L19-19 verbatim
section


-- @@ L21-21 verbatim
/-! The genuine Piola constraint for every generated source high/corrector pair. -/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! Exact angular mean and raw corrector identities for the constructed source profiles. -/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerPacketCylinderField


-- @@ L33-33 verbatim
open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L35-38 verbatim
variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)


-- @@ L40-64 verbatim
include hT in
theorem source_high_mean_zero (p : ℕ) (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, (sourceProfiles P M D I Iprimary p).high (t,(x,θ))) = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change (∫ _ in (0 : ℝ)..P, (0 : Space)) = 0
    exact intervalIntegral.integral_zero
  by_cases hp1 : p = 1
  · subst p
    simpa only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile] using
      (homogeneousForcing (P := P) D).vector_mean_zero Iprimary t x
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceHighForcing P M D hT I Iprimary p hp⟩
  have he : sourceProfiles P M D I Iprimary p =
      EulerPacketProfileRecursion.step (sourceOperators P M D I) p (sourceProfiles P M D I
          Iprimary) :=
    profiles_step _ _ p hp
  rw [he]
  change (∫ θ in (0 : ℝ)..P, (EulerTransversePacketProvider.highSolve P D I
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))).1 (t,(x,θ))) = 0
  rw [EulerTransversePacketProvider.highSolve_of_admissible D I _ h]
  exact (Classical.choice h).vector_mean_zero I t x


-- @@ L66-74 verbatim
theorem source_corrector_eq (p : ℕ) (hp : 1 ≤ p) :
    (sourceProfiles P M D I Iprimary p).corrector =
      D.curlCorrector P (sourceProfiles P M D I Iprimary p).high := by
  by_cases hp1 : p = 1
  · subst p
    simp only [sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
    rfl
  have hp2 : 2 ≤ p := by omega
  exact profiles_corrector _ _ p hp2


-- @@ L76-76 verbatim
end EulerPacketCylinderField


-- @@ L78-78 verbatim
end

-- @@ L79-79 verbatim
end


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
@[expose] public section


-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
namespace EulerPacketCylinderField


-- @@ L89-90 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketProfileRecursion EulerLpCylinderPaths

-- @@ L91-91 verbatim
open scoped ContDiff


-- @@ L93-97 verbatim
theorem Field.changeTime_apply {P T T' : ℝ} [Fact (0 < P)] {raw : VectorField}
    (G : Field P T raw) (h : T = T') (t : Icc (0 : ℝ) T) :
    (G.changeTime h).path ⟨t,by rw [← h]; exact t.property⟩ = G.path t := by
  subst T'
  rfl


-- @@ L99-102 verbatim
variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)


-- @@ L104-106 verbatim
/-- Source time, given by `⟨t,by rw [← hT]; exact t.property⟩`. -/
def sourceTime (t : Icc (0 : ℝ) M.T) : Icc (0 : ℝ) D.T :=
  ⟨t,by rw [← hT]; exact t.property⟩


-- @@ L108-115 verbatim
/-- Source pair field used in packet source piola. -/
def sourcePairField (κ : ℝ) (p : ℕ) :
    Field P M.T (fun z => (sourceOperators P M D I).inverseFrame z
      (κ^p • (sourceProfiles P M D I Iprimary p).high z +
        κ^(p+1) • (sourceProfiles P M D I Iprimary p).corrector z)) :=
  (sourceCoefficientData P M D I hT).inverse.multiply
    (((sourceProfileWitness P M D hT I Iprimary p).high.smul (κ^p)).add
      ((sourceProfileWitness P M D hT I Iprimary p).corrector.smul (κ^(p+1))))


-- @@ L117-152 verbatim
theorem sourcePairField_mem (κ : ℝ) (p : ℕ) (hp : 1 ≤ p) (t : Icc (0 : ℝ) M.T)
    (Ξ : Space → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hF : ∀ x, fderiv ℝ Ξ x = D.F.field (sourceTime M D hT t) x)
    (hdet : ∀ x, (EulerPacketPiola.operatorMatrix (D.F.field (sourceTime M D hT t) x)).det = 1) :
    (sourcePairField P M D hT I Iprimary κ p).path t ∈ divergenceFreeSpace P κ D.m₀ := by
  let W := sourceProfileWitness P M D hT I Iprimary p
  let G := W.high.changeTime hT
  let C := (W.corrector.congr (fun _ _ _ => by
      rw [source_corrector_eq P M D I Iprimary p hp])).changeTime hT
  let V := piolaPairField D G C κ p
  have hs : G.path (sourceTime M D hT t) ∈ Supported P Space D.support D.support_measurable :=
    G.supported_of_raw_zero D.support D.support_measurable
      (raw_zero_changeTime hT D.support W.high_zero) _
  have hm : ∀ x, (∫ θ in (0 : ℝ)..P,
      (sourceProfiles P M D I Iprimary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    source_high_mean_zero P M D hT I Iprimary p _
  have ht : ∀ x θ, inner ℝ (D.normalField (sourceTime M D hT t,(x,θ)))
      ((sourceProfiles P M D I Iprimary p).high (sourceTime M D hT t,(x,θ))) = 0 :=
    source_high_tangent P M D hT I Iprimary p _
  have hV : V.path (sourceTime M D hT t) ∈ divergenceFreeSpace P κ D.m₀ :=
    piolaPairField_mem D G C κ p (sourceTime M D hT t) Ξ hΞ hF hdet hs hm ht
  let H := sourcePairField P M D hT I Iprimary κ p
  have he : (H.changeTime hT).path = V.path := by
    apply Field.path_eq_of_raw_eq
    intro r x θ
    change D.FInv.field (D.clamp r) x
        (κ^p • (sourceProfiles P M D I Iprimary p).high (r,(x,θ)) +
          κ^(p+1) • D.curlCorrector P (sourceProfiles P M D I Iprimary p).high (r,(x,θ))) =
      D.FInv.field (D.clamp r) x
        (κ^p • (sourceProfiles P M D I Iprimary p).high (r,(x,θ)) +
          κ^(p+1) • (sourceProfiles P M D I Iprimary p).corrector (r,(x,θ)))
    rw [source_corrector_eq P M D I Iprimary p hp]
  have hev : H.path t = V.path (sourceTime M D hT t) :=
    (H.changeTime_apply hT t).symm.trans (congrArg (fun q => q (sourceTime M D hT t)) he)
  rw [hev]
  exact hV


-- @@ L154-154 verbatim
end EulerPacketCylinderField


-- @@ L156-156 verbatim
end

-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end


-- @@ L161-161 verbatim
section


-- @@ L163-163 verbatim
/-! The literal packet sums and their genuine first derivatives match the graded assembly. -/


-- @@ L165-165 verbatim
@[expose] public section


-- @@ L167-167 verbatim
noncomputable section


-- @@ L169-169 verbatim
namespace EulerPacketPointJets


-- @@ L171-171 verbatim
open EulerFiniteGrades Finset


-- @@ L173-173 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L175-176 verbatim
theorem jet_zero (z : Domain) : jet (fun _ : Domain => (0 : E)) z = 0 := by
  simp [jet]


-- @@ L178-181 verbatim
theorem jet_add (f g : Domain → E) (z : Domain)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    jet (f+g) z = jet f z+jet g z := by
  simp only [jet, Pi.add_apply, fderiv_add hf hg, Prod.mk_add_mk]


-- @@ L183-188 verbatim
theorem jet_truncate (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    jet (truncate N u n) z = truncate N (fun i => jet (u i) z) n := by
  by_cases hn : n ≤ N
  · simp only [truncate_of_le N n _ hn]
  · simp only [truncate_of_gt N n _ (by omega), Pi.zero_def]
    exact jet_zero z


-- @@ L190-194 verbatim
theorem jet_shiftUp (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    jet (shiftUp N u n) z = shiftUp N (fun i => jet (u i) z) n := by
  cases n with
  | zero => exact jet_zero z
  | succ n => exact jet_truncate N n u z


-- @@ L196-202 verbatim
theorem differentiableAt_truncate (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z) :
    DifferentiableAt ℝ (truncate N u n) z := by
  by_cases hn : n ≤ N
  · simpa only [truncate_of_le N n _ hn] using hu n hn
  · simpa only [truncate_of_gt N n _ (by omega), Pi.zero_def] using
      (differentiableAt_const (c := (0 : E)))


-- @@ L204-209 verbatim
theorem differentiableAt_shiftUp (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z) :
    DifferentiableAt ℝ (shiftUp N u n) z := by
  cases n with
  | zero => exact differentiableAt_const (c := (0 : E))
  | succ n => exact differentiableAt_truncate N n u z hu


-- @@ L211-219 verbatim
theorem jet_assemble (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (c i) z) :
    jet (assemble N u c n) z =
      assemble N (fun i => jet (u i) z) (fun i => jet (c i) z) n := by
  change jet (truncate N u n+shiftUp N c n) z = _
  rw [jet_add _ _ z (differentiableAt_truncate N n u z hu)
      (differentiableAt_shiftUp N n c z hc), jet_truncate, jet_shiftUp]
  rfl


-- @@ L221-225 verbatim
theorem differentiableAt_assemble (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (u i) z)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (c i) z) :
    DifferentiableAt ℝ (assemble N u c n) z :=
  (differentiableAt_truncate N n u z hu).add (differentiableAt_shiftUp N n c z hc)


-- @@ L227-234 verbatim
/-- The extra degree N+1 is precisely the final divergence corrector in (13). -/
theorem fieldSum_assemble_from_one (N : ℕ) (κ : ℝ) (u c : ℕ → Domain → E)
    (hu : u 0 = 0) (hc : c 0 = 0) (z : Domain) :
    fieldSum (N+1) κ (assemble N u c) z =
      ∑ i ∈ range N, (κ^(i+1) • u (i+1) z+κ^(i+2) • c (i+1) z) := by
  have h := congrArg (fun f : Domain → E => f z)
    (evaluate_assemble_from_one N κ u c hu hc)
  simpa only [fieldSum, evaluate, Finset.sum_apply, Pi.smul_apply, Pi.add_apply] using h


-- @@ L236-236 verbatim
end EulerPacketPointJets


-- @@ L238-238 verbatim
end

-- @@ L239-239 verbatim
end


-- @@ L241-241 verbatim
end
