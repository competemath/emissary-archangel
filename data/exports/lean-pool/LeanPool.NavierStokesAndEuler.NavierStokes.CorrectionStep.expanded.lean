/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalResidualGrouping
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveStateRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.BandReindexedSignedMeanGain
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualNaturality
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformHarmonicInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedCurlRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeMassPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ExponentLedger
import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCovariance
import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicStructurePreservation
import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSupportPreservation
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedMeanInteraction
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanBoundsReindex
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.MovingMomentBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.NativePrincipalEquations
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds


-- @@ L30-37 verbatim
/-!
# Exact field bookkeeping for one correction cycle

The residuals in this file are the differentiated nonlinear fields in (32).
In particular, changing the wave covariance and changing a mean velocity are
not treated as independent black-box state transitions.  Every old/new cross
term is retained in the displayed residual differences.
-/


-- @@ L39-39 verbatim
@[expose] public section



-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
namespace NavierStokes.CorrectionStep


-- @@ L46-46 verbatim
open Set WeightedClasses MeanIncrementBounds

-- @@ L47-47 verbatim
open scoped ContDiff BigOperators


-- @@ L49-49 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L51-52 verbatim
/-- Scalar field: an abbreviation for `MeanIncrementBounds.Field D`. -/
abbrev ScalarField (D : Type) := MeanIncrementBounds.Field D

-- @@ L53-54 verbatim
/-- Tensor: an abbreviation for `Fin 3 → Fin 3 → ScalarField D`. -/
abbrev Tensor (D : Type) := Fin 3 → Fin 3 → ScalarField D


-- @@ L56-58 verbatim
/-- These are changes of the literal covariance terms in (32). -/
noncomputable def thetaCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  o.radialDiv 2 (X 0 1) + o.dz (X 2 1)


-- @@ L60-62 verbatim
/-- Axial covariance change, given by `o.radialDiv 1 (X 0 2) + o.dz (X 2 2)`. -/
noncomputable def axialCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  o.radialDiv 1 (X 0 2) + o.dz (X 2 2)


-- @@ L64-67 verbatim
/-- Radial covariance change, given by `-o.radialDiv 1 (X 0 0) - o.dz (X 2 0) + o.invRadius * X
1 1`. -/
noncomputable def radialCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  -o.radialDiv 1 (X 0 0) - o.dz (X 2 0) + o.invRadius * X 1 1


-- @@ L69-71 verbatim
theorem smooth_updated {U : Set D} {m h : Triple D}
    (hm : SmoothTriple U m) (hh : SmoothTriple U h) : SmoothTriple U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩


-- @@ L73-73 verbatim
section CovarianceChanges


-- @@ L75-78 verbatim
variable {U : Set D} (hU : IsOpen U) (o : Operators D)
  {b m : Triple D} (hb : SmoothTriple U b) (hm : SmoothTriple U m)
  (W X : Tensor D) (hW : ∀ i j, SmoothOn U (W i j))
  (hX : ∀ i j, SmoothOn U (X i j))


-- @@ L80-98 verbatim
include hU hb hm hW hX in
theorem thetaResidual_covariance_change (T : ScalarField D) :
    Agree U (thetaResidual o b m (W + X) T - thetaResidual o b m W T)
      (thetaCovarianceChange o X) := by
  have hr : thetaRadial b m + (W + X) 0 1 = (thetaRadial b m + W 0 1) + X 0 1 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : thetaAxial b m + (W + X) 2 1 = (thetaAxial b m + W 2 1) + X 2 1 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [thetaResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz, o.radialDiv_add hU 2 ((hb.thetaRadial hm).add (hW 0 1)) (hX 0 1) n hx,
    o.dz_add hU ((hb.thetaAxial hm).add (hW 2 1)) (hX 2 1) n hx]
  simp only [thetaCovarianceChange, Pi.add_apply]
  ring


-- @@ L100-118 verbatim
include hU hb hm hW hX in
theorem axialResidual_covariance_change (p T : ScalarField D) (hp : SmoothOn U p) :
    Agree U (axialResidual o b m (W + X) p T - axialResidual o b m W p T)
      (axialCovarianceChange o X) := by
  have hr : axialRadial b m + (W + X) 0 2 = (axialRadial b m + W 0 2) + X 0 2 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : axialAxial b m + (W + X) 2 2 + p = (axialAxial b m + W 2 2 + p) + X 2 2 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [axialResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz, o.radialDiv_add hU 1 ((hb.axialRadial hm).add (hW 0 2)) (hX 0 2) n hx,
    o.dz_add hU (((hb.axialAxial hm).add (hW 2 2)).add hp) (hX 2 2) n hx]
  simp only [axialCovarianceChange, Pi.add_apply]
  ring


-- @@ L120-137 verbatim
include hU hb hm hW hX in
theorem gr_covariance_change :
    Agree U (gr o b m (W + X) - gr o b m W) (radialCovarianceChange o X) := by
  have hr : radialRadial b m + (W + X) 0 0 = (radialRadial b m + W 0 0) + X 0 0 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : axialRadial b m + (W + X) 2 0 = (axialRadial b m + W 2 0) + X 2 0 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [gr, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
  rw [hr, hz, o.radialDiv_add hU 1 ((hb.radialRadial hm).add (hW 0 0)) (hX 0 0) n hx,
    o.dz_add hU ((hb.axialRadial hm).add (hW 2 0)) (hX 2 0) n hx]
  simp only [radialCovarianceChange, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  ring


-- @@ L139-139 verbatim
end CovarianceChanges


-- @@ L141-141 verbatim
section JointChanges


-- @@ L143-147 verbatim
variable {U : Set D} (hU : IsOpen U) (o : Operators D)
  (ha : ContDiffOn ℝ ∞ o.radialProfile U)
  {b m h : Triple D} (hb : SmoothTriple U b) (hm : SmoothTriple U m)
  (hh : SmoothTriple U h) (W X : Tensor D)
  (hW : ∀ i j, SmoothOn U (W i j)) (hX : ∀ i j, SmoothOn U (X i j))


-- @@ L149-157 verbatim
include hU ha hb hm hh hW hX in
theorem thetaResidual_joint_change (T : ScalarField D) :
    Agree U (thetaResidual o b (updated m h) (W + X) T - thetaResidual o b m W T)
      (o.fastTime h.angular + thetaRemainder o b m h + thetaCovarianceChange o X) := by
  intro n x hx
  have hmean := thetaResidual_change hU o ha hb hm hh W hW T n hx
  have hwave := thetaResidual_covariance_change hU o hb (smooth_updated hm hh) W X hW hX T n hx
  simp only [Pi.add_apply, Pi.sub_apply] at *
  linarith


-- @@ L159-170 verbatim
include hU ha hb hm hh hW hX in
theorem axialResidual_joint_change (p δp T : ScalarField D)
    (hp : SmoothOn U p) (hδp : SmoothOn U δp) :
    Agree U (axialResidual o b (updated m h) (W + X) (p + δp) T -
      axialResidual o b m W p T)
      (o.fastTime h.axial + axialRemainder o b m h δp + axialCovarianceChange o X) := by
  intro n x hx
  have hmean := axialResidual_change hU o ha hb hm hh W hW p δp T hp hδp n hx
  have hwave := axialResidual_covariance_change hU o hb (smooth_updated hm hh) W X hW hX
    (p + δp) T (hp.add hδp) n hx
  simp only [Pi.add_apply, Pi.sub_apply] at *
  linarith


-- @@ L172-180 verbatim
include hU ha hb hm hh hW hX in
theorem gr_joint_change :
    Agree U (gr o b (updated m h) (W + X) - gr o b m W)
      (leadingRadial o b h + radialRemainder o b m h + radialCovarianceChange o X) := by
  intro n x hx
  have hmean := gr_change hU o ha hb hm hh W hW n hx
  have hwave := gr_covariance_change hU o hb (smooth_updated hm hh) W X hW hX n hx
  simp only [Pi.add_apply, Pi.sub_apply] at *
  linarith


-- @@ L182-182 verbatim
end JointChanges


-- @@ L184-187 verbatim
/-- A bound on each actual tensor entry. It is not a bound on the resulting
residual and contains no update-preservation assertion. -/
def TensorClass (s : StripData D) (α : ℝ) (X : Tensor D) : Prop :=
  ∀ i j, MeanClass s α (X i j)


-- @@ L189-189 verbatim
section CovarianceBounds


-- @@ L191-192 verbatim
variable {s : StripData D} {o : Operators D} {κ α : ℝ}
  (ho : OperatorBounds s o κ) {X : Tensor D} (hX : TensorClass s α X)


-- @@ L194-198 verbatim
include ho hX in
theorem thetaCovarianceChange_mem :
    MeanClass s (α - κ) (thetaCovarianceChange o X) := by
  exact (ho.radialDiv (hX 0 1) 2).add
    ((ho.dz (hX 2 1)).mono_exponent (by linarith [ho.kappa_nonneg]))


-- @@ L200-204 verbatim
include ho hX in
theorem axialCovarianceChange_mem :
    MeanClass s (α - κ) (axialCovarianceChange o X) := by
  exact (ho.radialDiv (hX 0 2) 1).add
    ((ho.dz (hX 2 2)).mono_exponent (by linarith [ho.kappa_nonneg]))


-- @@ L206-211 verbatim
include ho hX in
theorem radialCovarianceChange_mem :
    MeanClass s (α - κ) (radialCovarianceChange o X) := by
  exact (Class.sub (Class.neg (ho.radialDiv (hX 0 0) 1))
    ((ho.dz (hX 2 0)).mono_exponent (by linarith [ho.kappa_nonneg]))).add
    ((ho.inv_mul (hX 1 1)).mono_exponent (by linarith [ho.kappa_nonneg]))


-- @@ L213-213 verbatim
end CovarianceBounds


-- @@ L215-215 verbatim
/-! ## The full differential residual, before angular averaging -/


-- @@ L217-217 verbatim
section FullCalculus


-- @@ L219-219 verbatim
open HarmonicCalculus LinearWaveResidual


-- @@ L221-225 verbatim
theorem angularGenerator_add (a b : ComplexVector) :
    angularGenerator (a + b) = angularGenerator a + angularGenerator b := by
  ext i
  fin_cases i <;> simp [angularGenerator]
  abel


-- @@ L227-233 verbatim
theorem transport_add_left (R : D → ℝ) (Vr Vθ Vz : D → D)
    (a b v : D → ComplexVector) (x : D) :
    transport R Vr Vθ Vz (a + b) v x =
      transport R Vr Vθ Vz a v x + transport R Vr Vθ Vz b v x := by
  ext i
  simp only [transport, Pi.add_apply]
  ring


-- @@ L235-244 verbatim
theorem transport_add_right (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u a b : D → ComplexVector) {x : D}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) :
    transport R Vr Vθ Vz u (a + b) x =
      transport R Vr Vθ Vz u a x + transport R Vr Vθ Vz u b x := by
  ext i
  simp only [transport, Pi.add_apply, angularGenerator_add,
    along_add _ (ha i) (hb i)]
  ring


-- @@ L246-258 verbatim
theorem twiceAlong_add {U : Set D} (hU : IsOpen U) {V : D → D}
    (hV : ContDiffOn ℝ ∞ V U) {f g : D → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) :
    along V (along V (f + g)) x = along V (along V f) x + along V (along V g) x := by
  have heq : EqOn (along V (f + g)) (along V f + along V g) U := by
    intro y hy
    exact along_add V ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [along_congr hU heq hx]
  exact along_add V
    (((contDiffOn_along hU hV hf).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((contDiffOn_along hU hV hg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))


-- @@ L260-273 verbatim
theorem cylindricalLaplacian_add {U : Set D} (hU : IsOpen U) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {f g : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (f + g) x =
      cylindricalLaplacian R Vr Vθ Vz f x + cylindricalLaplacian R Vr Vθ Vz g x := by
  have df := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dg := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hfirst : along Vr (f + g) x = along Vr f x + along Vr g x := along_add Vr df dg
  simp only [cylindricalLaplacian, twiceAlong_add hU hr hf hg hx,
    twiceAlong_add hU hθ hf hg hx, twiceAlong_add hU hz hf hg hx,
    hfirst, smul_add]
  abel


-- @@ L275-295 verbatim
theorem cylindricalVectorLaplacian_add {U : Set D} (hU : IsOpen U) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {a b : D → ComplexVector}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    {x : D} (hx : x ∈ U) :
    cylindricalVectorLaplacian R Vr Vθ Vz (a + b) x =
      cylindricalVectorLaplacian R Vr Vθ Vz a x +
        cylindricalVectorLaplacian R Vr Vθ Vz b x := by
  have hL i : cylindricalLaplacian R Vr Vθ Vz (fun y => a y i + b y i) x =
      cylindricalLaplacian R Vr Vθ Vz (fun y => a y i) x +
        cylindricalLaplacian R Vr Vθ Vz (fun y => b y i) x :=
    cylindricalLaplacian_add hU R hr hθ hz (ha i) (hb i) hx
  have hD i := along_add Vθ
    (((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  ext i
  fin_cases i <;>
    simp [cylindricalVectorLaplacian, angularGenerator, hL 0, hL 1, hL 2,
      hD 0, hD 1, Complex.real_smul] <;> ring


-- @@ L297-303 verbatim
theorem gradient_add (R : D → ℝ) (Vr Vθ Vz : D → D)
    {p q : D → ℂ} {x : D} (hp : DifferentiableAt ℝ p x)
    (hq : DifferentiableAt ℝ q x) :
      gradient R Vr Vθ Vz (p + q) x = gradient R Vr Vθ Vz p x + gradient R Vr Vθ Vz q x := by
  have hd (V : D → D) : along V (p + q) x = along V p x + along V q x := along_add V hp hq
  ext i
  fin_cases i <;> simp [gradient, hd, smul_add]


-- @@ L305-324 verbatim
theorem linearResidual_add {U : Set D} (hU : IsOpen U) (ε : ℝ) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (Vt : D → D) (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B a b : D → ComplexVector) (p q : D → ℂ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    {x : D} (hx : x ∈ U) :
    linearResidual ε R Vr Vθ Vz Vt B (a + b) (p + q) x =
      linearResidual ε R Vr Vθ Vz Vt B a p x + linearResidual ε R Vr Vθ Vz Vt B b q x := by
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have db i := ((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dp := (hp.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dq := (hq.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hL := cylindricalVectorLaplacian_add hU R hr hθ hz ha hb hx
  ext i
  simp only [linearResidual, Pi.add_apply, along_add _ (da i) (db i),
    transport_add_left, transport_add_right R Vr Vθ Vz B a b da db,
    gradient_add R Vr Vθ Vz dp dq, hL]
  ring


-- @@ L326-330 verbatim
/-- Exact residual of a perturbation of a fixed base, before the virtual
stress and the separately retained base residual are added. -/
noncomputable def nonlinearResidual (ε : ℝ) (R : D → ℝ) (Vr Vθ Vz Vt : D → D)
    (B a : D → ComplexVector) (p : D → ℂ) (x : D) : ComplexVector :=
  linearResidual ε R Vr Vθ Vz Vt B a p x + transport R Vr Vθ Vz a a x


-- @@ L332-349 verbatim
theorem nonlinearResidual_add_sub {U : Set D} (hU : IsOpen U) (ε : ℝ) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (Vt : D → D) (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B a b : D → ComplexVector) (p q : D → ℂ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    {x : D} (hx : x ∈ U) :
    nonlinearResidual ε R Vr Vθ Vz Vt B (a + b) (p + q) x -
        nonlinearResidual ε R Vr Vθ Vz Vt B a p x =
      linearResidual ε R Vr Vθ Vz Vt B b q x + transport R Vr Vθ Vz a b x +
        transport R Vr Vθ Vz b a x + transport R Vr Vθ Vz b b x := by
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have db i := ((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [nonlinearResidual, linearResidual_add hU ε R Vt hr hθ hz B a b p q ha hb hp hq hx,
    transport_add_left, transport_add_right R Vr Vθ Vz a a b da db,
    transport_add_right R Vr Vθ Vz b a b da db, nonlinearResidual]
  abel


-- @@ L351-351 verbatim
end FullCalculus


-- @@ L353-353 verbatim
section FullFields


-- @@ L355-355 verbatim
open CorrectionState HarmonicCalculus


-- @@ L357-361 verbatim
/-- Radial direction, given by `(c.operators.eR + (c.operators.radialFrequency n *
c.operators.radialProfile x.1) • c.operators.vR, 0)`. -/
noncomputable def radialDirection (c : Context D) (n : ℕ) (x : D × ℝ) : D × ℝ :=
  (c.operators.eR + (c.operators.radialFrequency n * c.operators.radialProfile x.1) •
    c.operators.vR, 0)


-- @@ L363-365 verbatim
/-- Axial direction, given by `(c.operators.epsilon n • c.operators.eZ, 0)`. -/
noncomputable def axialDirection (c : Context D) (n : ℕ) (_x : D × ℝ) : D × ℝ :=
  (c.operators.epsilon n • c.operators.eZ, 0)


-- @@ L367-368 verbatim
/-- Angular direction, given by `(0, 1)`. -/
noncomputable def angularDirection (_x : D × ℝ) : D × ℝ := (0, 1)


-- @@ L370-373 verbatim
/-- Time direction, given by `(c.operators.fastCoefficient n • c.operators.vT -
c.operators.epsilon n • c.operators.eT, 0)`. -/
noncomputable def timeDirection (c : Context D) (n : ℕ) (_x : D × ℝ) : D × ℝ :=
  (c.operators.fastCoefficient n • c.operators.vT - c.operators.epsilon n • c.operators.eT, 0)


-- @@ L375-378 verbatim
/-- Complex base, given by `![(c.base.radial n x.1 : ℂ), (c.base.angular n x.1 : ℂ),
(c.base.axial n x.1 : ℂ)]`. -/
noncomputable def complexBase (c : Context D) (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(c.base.radial n x.1 : ℂ), (c.base.angular n x.1 : ℂ), (c.base.axial n x.1 : ℂ)]


-- @@ L380-384 verbatim
/-- Complex perturbation as an element of `ComplexVector`. -/
noncomputable def complexPerturbation (u : State D) (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(u.mean.radial n x.1 + u.oscillation n x 0 : ℝ),
    (u.mean.angular n x.1 + u.oscillation n x 1 : ℝ),
    (u.mean.axial n x.1 + u.oscillation n x 2 : ℝ)]


-- @@ L386-388 verbatim
/-- Complex pressure, given by `(u.totalPressureIncrement n x : ℝ)`. -/
noncomputable def complexPressure (u : State D) (n : ℕ) (x : D × ℝ) : ℂ :=
  (u.totalPressureIncrement n x : ℝ)


-- @@ L390-394 verbatim
/-- Virtual divergence, given by `![0, -(c.operators.radialDiv 2 c.virtualTheta n x.1),
-(c.operators.radialDiv 1 c.virtualAxial n x.1)]`. -/
noncomputable def virtualDivergence (c : Context D) (n : ℕ) (x : D × ℝ) : Fin 3 → ℝ :=
  ![0, -(c.operators.radialDiv 2 c.virtualTheta n x.1),
    -(c.operators.radialDiv 1 c.virtualAxial n x.1)]


-- @@ L396-402 verbatim
/-- This field uses actual Fréchet derivatives.  The base flat error is
restored once, alongside the negative virtual-stress divergence. -/
noncomputable def fullResidual (c : Context D) (u : State D) : Oscillation D := fun n x i =>
  (nonlinearResidual (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1)
    (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
    (complexBase c n) (complexPerturbation u n) (complexPressure u n) x i).re +
    virtualDivergence c n x i + u.errors.base n x i


-- @@ L404-406 verbatim
/-- Full good residual, given by `fullResidual c u - u.errors.total`. -/
noncomputable def fullGoodResidual (c : Context D) (u : State D) : Oscillation D :=
  fullResidual c u - u.errors.total


-- @@ L408-410 verbatim
/-- Angular mean vector, defined pointwise by `angularAverage (fun k p => f k p i) n x`. -/
noncomputable def angularMeanVector (f : Oscillation D) : MeanVector D :=
  fun n x i => angularAverage (fun k p => f k p i) n x


-- @@ L412-414 verbatim
/-- Angular nonconstant, defined pointwise by `f n x i - angularMeanVector f n x.1 i`. -/
noncomputable def angularNonconstant (f : Oscillation D) : Oscillation D :=
  fun n x i => f n x i - angularMeanVector f n x.1 i


-- @@ L416-418 verbatim
/-- Full good wave residual, given by `angularNonconstant (fullGoodResidual c u)`. -/
noncomputable def fullGoodWaveResidual (c : Context D) (u : State D) : Oscillation D :=
  angularNonconstant (fullGoodResidual c u)


-- @@ L420-422 verbatim
theorem fullResidual_eq_good_add_excluded (c : Context D) (u : State D) :
    fullResidual c u = fullGoodResidual c u + u.errors.total := by
  simp [fullGoodResidual]


-- @@ L424-430 verbatim
theorem fullResidual_decomposition (c : Context D) (u : State D) :
    fullResidual c u = fun n x i => fullGoodWaveResidual c u n x i +
      angularMeanVector (fullGoodResidual c u) n x.1 i + u.errors.total n x i := by
  funext n x i
  simp only [fullGoodWaveResidual, angularNonconstant, fullGoodResidual,
    Pi.sub_apply]
  ring


-- @@ L432-432 verbatim
end FullFields


-- @@ L434-434 verbatim
section ActualCovariance


-- @@ L436-436 verbatim
open CorrectionState MeasureTheory


-- @@ L438-440 verbatim
/-- Angular continuous, given by `∀ n x i, Continuous (fun θ : ℝ => u n (x, θ) i)`. -/
def AngularContinuous (u : Oscillation D) : Prop :=
  ∀ n x i, Continuous (fun θ : ℝ => u n (x, θ) i)


-- @@ L442-445 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.add {u v : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) : AngularContinuous (u + v) :=
  fun n x i => (hu n x i).add (hv n x i)


-- @@ L447-461 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_add_left {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance (u + v) w = bilinearCovariance u w + bilinearCovariance v w := by
  funext i j n x
  have he : (fun θ : ℝ => (u + v) n (x, θ) i * w n (x, θ) j) =
      (fun θ => u n (x, θ) i * w n (x, θ) j + v n (x, θ) i * w n (x, θ) j) := by
    funext θ
    simp only [Pi.add_apply]
    ring
  change (∫ θ in (0 : ℝ)..2 * Real.pi, (u + v) n (x, θ) i * w n (x, θ) j) /
    (2 * Real.pi) = _
  rw [he, intervalIntegral.integral_add (((hu n x i).fun_mul (hw n x j)).intervalIntegrable _ _)
    (((hv n x i).fun_mul (hw n x j)).intervalIntegrable _ _), add_div]
  rfl


-- @@ L463-470 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_add_right {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance u (v + w) = bilinearCovariance u v + bilinearCovariance u w := by
  funext i j
  rw [bilinearCovariance_comm u (v + w) i j,
    congrFun (congrFun (bilinearCovariance_add_left hv hw hu) j) i]
  simp only [Pi.add_apply, bilinearCovariance_comm v u j i, bilinearCovariance_comm w u j i]


-- @@ L472-475 verbatim
/-- The actual covariance increment contains both cross terms and the
entire square of the exact increment. -/
noncomputable def covarianceIncrement (u v : Oscillation D) : Tensor D :=
  bilinearCovariance u v + bilinearCovariance v u + bilinearCovariance v v


-- @@ L477-485 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_add {u v : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) :
    bilinearCovariance (u + v) (u + v) =
      bilinearCovariance u u + covarianceIncrement u v := by
  rw [bilinearCovariance_add_left hu hv (hu.add hv),
    bilinearCovariance_add_right hu hu hv, bilinearCovariance_add_right hv hu hv]
  unfold covarianceIncrement
  abel


-- @@ L487-492 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_actual_update (s : State D) (m : Triple D) (p : ScalarField D)
    (v : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D)
    (hu : AngularContinuous s.oscillation) (hv : AngularContinuous v) :
    (s.addIncrement m p v q e).covariance = s.covariance + covarianceIncrement s.oscillation v :=
  covariance_add hu hv


-- @@ L494-494 verbatim
end ActualCovariance


-- @@ L496-496 verbatim
section ActualFullUpdate


-- @@ L498-498 verbatim
open CorrectionState HarmonicCalculus


-- @@ L500-505 verbatim
/-- Complex increment, given by `![(m.radial n x.1 + v n x 0 : ℝ), (m.angular n x.1 + v n x 1 :
ℝ), (m.axial n x.1 + v n x 2 : ℝ)]`. -/
noncomputable def complexIncrement (m : Triple D) (v : Oscillation D)
    (n : ℕ) (x : D × ℝ) : ComplexVector :=
  ![(m.radial n x.1 + v n x 0 : ℝ), (m.angular n x.1 + v n x 1 : ℝ),
    (m.axial n x.1 + v n x 2 : ℝ)]


-- @@ L507-509 verbatim
/-- Complex pressure increment, given by `(p n x.1 + q n x : ℝ)`. -/
noncomputable def complexPressureIncrement (p : ScalarField D) (q : OscillatoryScalar D)
    (n : ℕ) (x : D × ℝ) : ℂ := (p n x.1 + q n x : ℝ)


-- @@ L511-517 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexPerturbation_actual_update (s : State D) (m : Triple D) (p : ScalarField D)
    (v : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) (n : ℕ) :
    complexPerturbation (s.addIncrement m p v q e) n =
      complexPerturbation s n + complexIncrement m v n := by
  funext x i
  fin_cases i <;> simp [complexPerturbation, complexIncrement, State.addIncrement, updated] <;> ring


-- @@ L519-526 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexPressure_actual_update (s : State D) (m : Triple D) (p : ScalarField D)
    (v : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) (n : ℕ) :
    complexPressure (s.addIncrement m p v q e) n =
      complexPressure s n + complexPressureIncrement p q n := by
  funext x
  simp [complexPressure, complexPressureIncrement, State.totalPressureIncrement, State.addIncrement]
  ring


-- @@ L528-543 verbatim
/-- The differential increment uses the old *exact* perturbation in both
cross terms. The stored excluded residual is not multiplied into the PDE. -/
noncomputable def fullDifferentialIncrement (c : Context D) (s : State D)
    (m : Triple D) (p : ScalarField D) (v : Oscillation D) (q : OscillatoryScalar D) :
    ℕ → D × ℝ → ComplexVector := fun n x =>
  let R : D × ℝ → ℝ := fun y => c.operators.radius y.1
  let a := complexPerturbation s n
  let b := complexIncrement m v n
  LinearWaveResidual.linearResidual (c.operators.epsilon n) R
      (radialDirection c n) angularDirection (axialDirection c n) (timeDirection c n)
      (complexBase c n) b (complexPressureIncrement p q n) x +
    LinearWaveResidual.transport R (radialDirection c n) angularDirection (axialDirection c n) a b
        x +
    LinearWaveResidual.transport R (radialDirection c n) angularDirection (axialDirection c n) b a
        x +
    LinearWaveResidual.transport R (radialDirection c n) angularDirection (axialDirection c n) b b x


-- @@ L545-570 verbatim
theorem fullResidual_actual_update {U : Set (D × ℝ)} (hU : IsOpen U)
    (c : Context D) (s : State D) (m : Triple D) (p : ScalarField D)
    (v : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => complexPerturbation s n x i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun x => complexIncrement m v n x i) U)
    (hp : ContDiffOn ℝ ∞ (complexPressure s n) U)
    (hq : ContDiffOn ℝ ∞ (complexPressureIncrement p q n) U)
    {x : D × ℝ} (hx : x ∈ U) (i : Fin 3) :
    fullResidual c (s.addIncrement m p v q e) n x i - fullResidual c s n x i =
      (fullDifferentialIncrement c s m p v q n x i).re + e.base n x i := by
  have hd := nonlinearResidual_add_sub hU (c.operators.epsilon n)
    (fun y : D × ℝ => c.operators.radius y.1) (timeDirection c n) hr
    (show ContDiffOn ℝ ∞ (angularDirection : D × ℝ → D × ℝ) U from contDiffOn_const)
    (show ContDiffOn ℝ ∞ (axialDirection c n) U from contDiffOn_const)
    (complexBase c n) (complexPerturbation s n) (complexIncrement m v n)
    (complexPressure s n) (complexPressureIncrement p q n) ha hb hp hq hx
  have hdreal := congrArg Complex.re (congrFun hd i)
  simp only [Pi.sub_apply, Pi.add_apply, Complex.sub_re, Complex.add_re] at hdreal
  simp only [fullResidual]
  rw [complexPerturbation_actual_update, complexPressure_actual_update]
  simp only [State.addIncrement, ExcludedErrors.add, Pi.add_apply]
  change _ = (fullDifferentialIncrement c s m p v q n x i).re + _
  unfold fullDifferentialIncrement
  simp only [Pi.add_apply, Complex.add_re]
  linarith


-- @@ L572-587 verbatim
theorem fullGoodResidual_actual_update {U : Set (D × ℝ)} (hU : IsOpen U)
    (c : Context D) (s : State D) (m : Triple D) (p : ScalarField D)
    (v : Oscillation D) (q : OscillatoryScalar D) (e : ExcludedErrors D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => complexPerturbation s n x i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun x => complexIncrement m v n x i) U)
    (hp : ContDiffOn ℝ ∞ (complexPressure s n) U)
    (hq : ContDiffOn ℝ ∞ (complexPressureIncrement p q n) U)
    {x : D × ℝ} (hx : x ∈ U) (i : Fin 3) :
    fullGoodResidual c (s.addIncrement m p v q e) n x i - fullGoodResidual c s n x i =
      (fullDifferentialIncrement c s m p v q n x i).re -
        e.gaussian n x i - e.aliasError n x i := by
  have hd := fullResidual_actual_update hU c s m p v q e n hr ha hb hp hq hx i
  simp only [fullGoodResidual, State.addIncrement, ExcludedErrors.total,
    ExcludedErrors.add, Pi.sub_apply, Pi.add_apply] at *
  linarith


-- @@ L589-589 verbatim
end ActualFullUpdate


-- @@ L591-591 verbatim
section TemporalComposition


-- @@ L593-593 verbatim
open CorrectionState


-- @@ L595-595 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L597-600 verbatim
/-- Mean bar, defined pointwise by `PressureStream.torusAverage (f n) (x.1, x.2.1)`. -/
noncomputable def meanBar (f : ScalarField (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) :=
  fun n x => PressureStream.torusAverage (f n) (x.1, x.2.1)


-- @@ L602-606 verbatim
/-- Temporal pressure change, given by `(temporalStage r h axial c u).pressure - u.pressure`. -/
noncomputable def temporalPressureChange (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (temporalStage r h axial c u).pressure - u.pressure


-- @@ L608-623 verbatim
theorem temporalIncrement_smooth (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (U : Set (PressureStream.Lift S))
    (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n)) :
    SmoothTriple U (temporalIncrement r h axial c u) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact (TemporalMeanUpdate.radialUpdate_smooth ha r.inner_lt_outer hd r.radialDirection
      (c.operators.epsilon n • axial) h n (hz n) (hpz n) (hsz n)).contDiffOn
  · exact (TemporalMeanUpdate.desiredIncrement_smooth h n (hθ n) (hpθ n)).contDiffOn
  · exact (TemporalMeanUpdate.axialUpdate_smooth ha r.inner_lt_outer hd r.radialDirection
      h n (hz n) (hpz n) (hsz n)).contDiffOn


-- @@ L625-662 verbatim
theorem temporalStage_theta_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (r : ReconstructionData) (h : ℝ) (axial slow : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (hcompat : c.operators = graphOperators r c.operators.epsilon
      (ChartScales.timeCoefficient h) axial slow (TorusInverse.vector .temporal))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n)) :
    Agree U ((temporalStage r h axial c u).thetaResidual c)
      (meanBar (u.thetaResidual c) + thetaRemainder c.operators c.base u.mean
        (temporalIncrement r h axial c u)) := by
  have hi := temporalIncrement_smooth r h axial c u U ha hd hθ hz hpθ hpz hsz
  have he := thetaResidual_change hU c.operators hprofile hb hm hi u.covariance hW c.virtualTheta
  have hnew : (temporalStage r h axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base
        (updated u.mean (temporalIncrement r h axial c u)) u.covariance c.virtualTheta := by
    simp [temporalStage, reconstructPressure, State.thetaResidual, State.addIncrement]
    rfl
  intro n x hx
  have he' := he n hx
  have hf := (temporal_fast_cancellation r h axial c u ha hd hθ hz hpθ hpz hsz n x).1
  have hfast : c.operators.fastTime (temporalIncrement r h axial c u).angular n x =
      TemporalMeanUpdate.fastDerivative h n ((temporalIncrement r h axial c u).angular n) x := by
    conv_lhs => rw [hcompat]
    rfl
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply, hfast] at he'
  simp only [TemporalMeanUpdate.centered] at hf
  change _ = PressureStream.torusAverage (u.thetaResidual c n) (x.1, x.2.1) + _
  change _ + (u.thetaResidual c n x - _) = 0 at hf
  change _ - u.thetaResidual c n x = _ at he'
  linarith


-- @@ L664-711 verbatim
theorem temporalStage_axial_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (r : ReconstructionData) (h : ℝ) (axial slow : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (hcompat : c.operators = graphOperators r c.operators.epsilon
      (ChartScales.timeCoefficient h) axial slow (TorusInverse.vector .temporal))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hp : SmoothOn U u.pressure) (hnp : SmoothOn U (temporalStage r h axial c u).pressure)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n)) :
    Agree U (fun n x => (temporalStage r h axial c u).axialResidual c n x -
      temporalAlias r h c u n (x, 0) 2)
      (meanBar (u.axialResidual c) + axialRemainder c.operators c.base u.mean
        (temporalIncrement r h axial c u) (temporalPressureChange r h axial c u)) := by
  have hi := temporalIncrement_smooth r h axial c u U ha hd hθ hz hpθ hpz hsz
  have he := axialResidual_change hU c.operators hprofile hb hm hi u.covariance hW
    u.pressure (temporalPressureChange r h axial c u) c.virtualAxial hp (hnp.sub hp)
  have hpressure : u.pressure + temporalPressureChange r h axial c u =
      (temporalStage r h axial c u).pressure := by
    unfold temporalPressureChange
    abel
  have hnew : (temporalStage r h axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (temporalIncrement r h axial c u)) u.covariance
        (u.pressure + temporalPressureChange r h axial c u) c.virtualAxial := by
    rw [hpressure]
    simp [temporalStage, reconstructPressure, State.axialResidual, State.addIncrement]
    rfl
  intro n x hx
  have he' := he n hx
  have hf := (temporal_fast_cancellation r h axial c u ha hd hθ hz hpθ hpz hsz n x).2
  have hfast : c.operators.fastTime (temporalIncrement r h axial c u).axial n x =
      TemporalMeanUpdate.fastDerivative h n ((temporalIncrement r h axial c u).axial n) x := by
    conv_lhs => rw [hcompat]
    rfl
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply, hfast] at he'
  simp only [TemporalMeanUpdate.centered] at hf
  change _ = PressureStream.torusAverage (u.axialResidual c n) (x.1, x.2.1) + _
  change _ + (u.axialResidual c n x - _) = _ at hf
  change _ - u.axialResidual c n x = _ at he'
  dsimp only
  linarith


-- @@ L713-743 verbatim
/-- The increment bound is proved for the actual inverse and stream, from
the current residual classes. No increment or updated-residual class is
assumed. The inverse-direction hypothesis is the concrete graph direction. -/
theorem temporalIncrement_mem (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H : ℝ}
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (hM : ∀ n, r.frequency n ≠ 0)
    (hvr : r.radialDirection = TorusInverse.vector .radial)
    (hθclass : MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (u.thetaResidual c))
    (hzclass : MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (u.axialResidual c))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n)) :
    IncrementBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (temporalIncrement r h axial c u) := by
  refine ⟨?_, ?_, ?_⟩
  · exact TemporalMeanUpdate.meanClass_scaledRadialUpdate ha r.inner_lt_outer hd hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale r.frequency (fun _ => r.radialDirection) axial
      hzclass hz hpz hsz
  · exact TemporalMeanUpdate.meanClass_desiredIncrement ha hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale hθclass hθ hpθ
  · simpa only [temporalIncrement, hvr] using
      (TemporalMeanUpdate.meanClass_axialUpdate ha r.inner_lt_outer hd hcL hcR hh
        c.operators.epsilon L hε hεone hL hscale r.frequency hM hzclass hz hpz hsz)


-- @@ L745-745 verbatim
end TemporalComposition


-- @@ L747-747 verbatim
section TemporalAngularGain


-- @@ L749-749 verbatim
open CorrectionState


-- @@ L751-751 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L753-797 verbatim
/-- An actual temporal stage preserves the improved bar exponent whenever
that exponent is below its proved differentiated remainder exponent. -/
theorem temporalStage_theta_mem (r : ReconstructionData) (h : ℝ)
    (axial slow : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H κ β : ℝ}
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (hM : ∀ n, r.frequency n ≠ 0)
    (hvr : r.radialDirection = TorusInverse.vector .radial)
    (hcompat : c.operators = graphOperators r c.operators.epsilon
      (ChartScales.timeCoefficient h) axial slow (TorusInverse.vector .temporal))
    (ho : OperatorBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.operators κ)
    (hb : BaseBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
        ha hcL hcR c.operators.epsilon L hε hεone hL) u.mean)
    (hW : ∀ i j, SmoothOn (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL).domain (u.covariance i j))
    (hθclass : MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (u.thetaResidual c))
    (hzclass : MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (u.axialResidual c))
    (hbar : MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) β (meanBar (u.thetaResidual c)))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) β
      ((temporalStage r h axial c u).thetaResidual c) := by
  have hi := temporalIncrement_mem r h axial c u ha hd hcL hcR hh L hε hεone hL
    hscale hM hvr hθclass hzclass hθ hz hpθ hpz hsz
  have herr := (thetaRemainder_mem ho hb hm hi hH).mono_exponent hβ
  apply class_congr (hbar.add herr)
  intro n x hx
  exact temporalStage_theta_exact (S := S) (WeightedRadialPrimitive.logStripData r.inner r.outer cL
      cR
    ha hcL hcR c.operators.epsilon L hε hεone hL).isOpen_domain r h axial slow c u ha hd
    hcompat (ho.radialProfile.smooth 0) hb.smooth hm.smooth hW hθ hz hpθ hpz hsz n hx


-- @@ L799-799 verbatim
end TemporalAngularGain


-- @@ L801-801 verbatim
section TemporalPressureAndAxial


-- @@ L803-803 verbatim
open CorrectionState


-- @@ L805-805 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L807-817 verbatim
omit [FiniteDimensional ℝ S] in
theorem temporalStage_pressure_formula (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (temporalStage r h axial c u).pressure =
      reconstructedPressure r.exponent r.inner r.outer r.inner_lt_outer r.frequency
        (fun _ => r.radialDirection) c.operators c.base
        (updated u.mean (temporalIncrement r h axial c u)) u.covariance := by
  simp [temporalStage, reconstructPressure, State.addIncrement,
    State.gr]
  rfl


-- @@ L819-857 verbatim
omit [FiniteDimensional ℝ S] in
/-- The pressure change is bounded by applying the actual compact inverse
to the actual change of `gr`, whose centrifugal term is retained. -/
theorem temporalPressureChange_mem (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H κ : ℝ}
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (ho : OperatorBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.operators κ)
    (hb : BaseBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds (WeightedRadialPrimitive.logStripData
      r.inner r.outer cL cR ha hcL hcR c.operators.epsilon L hε hεone hL) u.mean)
    (hi : IncrementBounds (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (temporalIncrement r h axial c u))
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (hW : ∀ i j, SmoothOn (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL).domain (u.covariance i j))
    (hf : ∀ n, ContDiff ℝ ∞ (MeanIncrementBounds.gr c.operators c.base
      (updated u.mean (temporalIncrement r h axial c u)) u.covariance n))
    (hg : ∀ n, ContDiff ℝ ∞ (u.gr c n))
    (hsf : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (MeanIncrementBounds.gr
      c.operators c.base (updated u.mean (temporalIncrement r h axial c u)) u.covariance n))
    (hsg : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.gr c n))
    (hpressure : u.pressure = (reconstructPressure r c u).pressure) :
    MeanClass (WeightedRadialPrimitive.logStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H
      (temporalPressureChange r h axial c u) := by
  have hp := reconstructedPressure_change_mem ha r.inner_lt_outer hd hcL hcR
    c.operators.epsilon L hε hεone hL ho hb hm hi hH hκ u.covariance hW hf hg hsf hsg
    r.frequency (fun _ => r.radialDirection)
  have hpressure' : u.pressure = reconstructedPressure r.exponent r.inner r.outer
      r.inner_lt_outer r.frequency (fun _ => r.radialDirection) c.operators c.base
      u.mean u.covariance := hpressure
  unfold temporalPressureChange
  rw [temporalStage_pressure_formula, hpressure']
  exact hp


-- @@ L859-893 verbatim
/-- The axial alias remains explicit in the conclusion. Its superflatness
is handled separately; it is not erased from the constructed velocity. -/
theorem temporalStage_axial_mem {s : StripData (PressureStream.Lift S)}
    (r : ReconstructionData) (h : ℝ) (axial slow : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    {H κ β : ℝ} (ha : 0 < r.inner) (hd : 0 < r.exponent)
    (hcompat : c.operators = graphOperators r c.operators.epsilon
      (ChartScales.timeCoefficient h) axial slow (TorusInverse.vector .temporal))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hi : IncrementBounds s H (temporalIncrement r h axial c u))
    (hp : SmoothOn s.domain u.pressure)
    (hdp : MeanClass s H (temporalPressureChange r h axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hbar : MeanClass s β (meanBar (u.axialResidual c)))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported r.inner r.outer (u.axialResidual c n))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β (fun n x => (temporalStage r h axial c u).axialResidual c n x -
      temporalAlias r h c u n (x, 0) 2) := by
  have hnp : SmoothOn s.domain (temporalStage r h axial c u).pressure := by
    have he : (temporalStage r h axial c u).pressure =
        u.pressure + temporalPressureChange r h axial c u := by
      unfold temporalPressureChange
      abel
    rw [he]
    exact hp.add hdp.smooth
  have herr := (axialRemainder_mem ho hb hm hi hH hdp).mono_exponent hβ
  apply class_congr (hbar.add herr)
  intro n x hx
  exact temporalStage_axial_exact (S := S) s.isOpen_domain r h axial slow c u ha hd hcompat
    (ho.radialProfile.smooth 0) hb.smooth hm.smooth hW hp hnp hθ hz hpθ hpz hsz n hx


-- @@ L895-909 verbatim
omit [FiniteDimensional ℝ S] in
theorem temporalStage_cumulative {s : StripData (PressureStream.Lift S)}
    (r : ReconstructionData) (h : ℝ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (temporalIncrement r h axial c u))
    (hp : MeanClass s H (temporalPressureChange r h axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (temporalStage r h axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (temporalStage r h axial c u).pressure =
      u.pressure + temporalPressureChange r h axial c u := by
    unfold temporalPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)


-- @@ L911-911 verbatim
end TemporalPressureAndAxial


-- @@ L913-919 verbatim
/-! ## One physical field behind the chart family

The predicate below is deliberately stronger than an indexed collection of
unrelated chart solutions.  Every chart is tied to the same physical fields
by specified maps and the manuscript's velocity, pressure, and residual units.
Operator naturality and the concrete chart maps are separate obligations.
-/


-- @@ L921-921 verbatim
section PhysicalRepresentation


-- @@ L923-923 verbatim
open CorrectionState


-- @@ L925-925 verbatim
variable {P : Type}


-- @@ L927-943 verbatim
/-- Physical fields data, collecting `mean`, `pressure`, `oscillation`, `oscillatoryPressure`,
`baseError`, `gaussianError` and their compatibility conditions. -/
structure PhysicalFields (P : Type) where
  /-- Mean field of `PhysicalFields`, of type `P → Fin 3 → ℝ`. -/
  mean : P → Fin 3 → ℝ
  /-- Pressure field of `PhysicalFields`, of type `P → ℝ`. -/
  pressure : P → ℝ
  /-- Oscillation of `PhysicalFields`, of type `P × ℝ → Fin 3 → ℝ`. -/
  oscillation : P × ℝ → Fin 3 → ℝ
  /-- Oscillatory pressure of `PhysicalFields`, of type `P × ℝ → ℝ`. -/
  oscillatoryPressure : P × ℝ → ℝ
  /-- Base error of `PhysicalFields`, of type `P × ℝ → Fin 3 → ℝ`. -/
  baseError : P × ℝ → Fin 3 → ℝ
  /-- Gaussian error of `PhysicalFields`, of type `P × ℝ → Fin 3 → ℝ`. -/
  gaussianError : P × ℝ → Fin 3 → ℝ
  /-- Alias error of `PhysicalFields`, of type `P × ℝ → Fin 3 → ℝ`. -/
  aliasError : P × ℝ → Fin 3 → ℝ


-- @@ L945-954 verbatim
/-- Add, bundling `mean`, `pressure`, `oscillation`, `oscillatoryPressure` and the required
compatibility proofs. -/
noncomputable def PhysicalFields.add (u v : PhysicalFields P) : PhysicalFields P where
  mean := u.mean + v.mean
  pressure := u.pressure + v.pressure
  oscillation := u.oscillation + v.oscillation
  oscillatoryPressure := u.oscillatoryPressure + v.oscillatoryPressure
  baseError := u.baseError + v.baseError
  gaussianError := u.gaussianError + v.gaussianError
  aliasError := u.aliasError + v.aliasError


-- @@ L956-958 verbatim
/-- Mean components, given by `![m.radial n x, m.angular n x, m.axial n x]`. -/
noncomputable def meanComponents (m : Triple D) (n : ℕ) (x : D) : Fin 3 → ℝ :=
  ![m.radial n x, m.angular n x, m.axial n x]


-- @@ L960-963 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem meanComponents_updated (m h : Triple D) (n : ℕ) (x : D) (i : Fin 3) :
    meanComponents (updated m h) n x i = meanComponents m n x i + meanComponents h n x i := by
  fin_cases i <;> rfl


-- @@ L965-981 verbatim
/-- `chart` includes the actual torus covering as well as spatial/time
rescaling. `domain n` specifies where that band is active. -/
structure RepresentsPhysical (chart : ℕ → P → D) (domain : ℕ → Set P)
    (Q : ℕ → ℝ) (A : ℝ) (u : State D) (v : PhysicalFields P) : Prop where
  mean : ∀ n x, x ∈ domain n → ∀ i,
    meanComponents u.mean n (chart n x) i = Q n ^ A * v.mean x i
  pressure : ∀ n x, x ∈ domain n → u.pressure n (chart n x) = Q n ^ (2 * A) * v.pressure x
  oscillation : ∀ n x, x ∈ domain n → ∀ θ i,
    u.oscillation n (chart n x, θ) i = Q n ^ A * v.oscillation (x, θ) i
  oscillatoryPressure : ∀ n x, x ∈ domain n → ∀ θ,
    u.oscillatoryPressure n (chart n x, θ) = Q n ^ (2 * A) * v.oscillatoryPressure (x, θ)
  baseError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.base n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.baseError (x, θ) i
  gaussianError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.gaussian n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.gaussianError (x, θ) i
  aliasError : ∀ n x, x ∈ domain n → ∀ θ i,
    u.errors.aliasError n (chart n x, θ) i = Q n ^ (2 * A + 1 / 2) * v.aliasError (x, θ) i


-- @@ L983-1026 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Actual addition preserves the specified common physical realization.
This does not manufacture a realization for a separately solved chart. -/
theorem RepresentsPhysical.addIncrement {chart : ℕ → P → D} {domain : ℕ → Set P}
    {Q : ℕ → ℝ} {A : ℝ} {u : State D} {v w : PhysicalFields P}
    (hu : RepresentsPhysical chart domain Q A u v)
    (m : Triple D) (p : ScalarField D) (osc : Oscillation D) (pr : OscillatoryScalar D)
    (e : ExcludedErrors D)
    (hw : RepresentsPhysical chart domain Q A (⟨m, p, osc, pr, e⟩ : State D) w) :
    RepresentsPhysical chart domain Q A (u.addIncrement m p osc pr e) (v.add w) := by
  constructor
  · intro n x hx i
    simp only [State.addIncrement, meanComponents_updated, PhysicalFields.add, Pi.add_apply]
    rw [hu.mean n x hx i, hw.mean n x hx i]
    ring
  · intro n x hx
    have hi : p n (chart n x) = Q n ^ (2 * A) * w.pressure x := hw.pressure n x hx
    simp only [State.addIncrement, PhysicalFields.add, Pi.add_apply]
    rw [hu.pressure n x hx, hi]
    ring
  · intro n x hx θ i
    have hi : osc n (chart n x, θ) i = Q n ^ A * w.oscillation (x, θ) i :=
      hw.oscillation n x hx θ i
    simp only [State.addIncrement, PhysicalFields.add, Pi.add_apply]
    rw [hu.oscillation n x hx θ i, hi]
    ring
  · intro n x hx θ
    have hi : pr n (chart n x, θ) = Q n ^ (2 * A) * w.oscillatoryPressure (x, θ) :=
      hw.oscillatoryPressure n x hx θ
    simp only [State.addIncrement, PhysicalFields.add, Pi.add_apply]
    rw [hu.oscillatoryPressure n x hx θ, hi]
    ring
  · intro n x hx θ i
    simp only [State.addIncrement, ExcludedErrors.add, PhysicalFields.add, Pi.add_apply]
    rw [hu.baseError n x hx θ i, hw.baseError n x hx θ i]
    ring
  · intro n x hx θ i
    simp only [State.addIncrement, ExcludedErrors.add, PhysicalFields.add, Pi.add_apply]
    rw [hu.gaussianError n x hx θ i, hw.gaussianError n x hx θ i]
    ring
  · intro n x hx θ i
    simp only [State.addIncrement, ExcludedErrors.add, PhysicalFields.add, Pi.add_apply]
    rw [hu.aliasError n x hx θ i, hw.aliasError n x hx θ i]
    ring


-- @@ L1028-1037 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem RepresentsPhysical.mean_overlap {chart : ℕ → P → D} {domain : ℕ → Set P}
    {Q : ℕ → ℝ} {A : ℝ} {u : State D} {v : PhysicalFields P}
    (hu : RepresentsPhysical chart domain Q A u v) (hQ : ∀ n, 0 < Q n)
    (n m : ℕ) (x : P) (hn : x ∈ domain n) (hm : x ∈ domain m) (i : Fin 3) :
    meanComponents u.mean n (chart n x) i / Q n ^ A =
      meanComponents u.mean m (chart m x) i / Q m ^ A := by
  rw [hu.mean n x hn i, hu.mean m x hm i]
  rw [mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos (hQ n) A).ne',
    mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos (hQ m) A).ne']


-- @@ L1039-1039 verbatim
end PhysicalRepresentation


-- @@ L1041-1041 verbatim
section RankMeanComposition


-- @@ L1043-1043 verbatim
open CorrectionState


-- @@ L1045-1045 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1047-1051 verbatim
/-- Rank pressure change, given by `(rankStage p r axial c u).pressure - u.pressure`. -/
noncomputable def rankPressureChange (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (rankStage p r axial c u).pressure - u.pressure


-- @@ L1053-1062 verbatim
theorem slow_directional_zero {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {f : ScalarField (PressureStream.Lift S)} (hf : SmoothOn U f)
    (hslow : DefectIncrementBounds.IsSlow f) (v : PressureStream.Plane)
    (n : ℕ) {x : PressureStream.Lift S} (hx : x ∈ U) :
    fderiv ℝ (f n) x (0, (0, v)) = 0 := by
  apply directional_zero_of_line_const ((hf.at_point hU n hx).differentiableAt (by simp))
  intro t
  rcases x with ⟨R, s, Y⟩
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  rw [hslow, hslow]


-- @@ L1064-1091 verbatim
theorem rankStage_theta_mem {s : StripData (PressureStream.Lift S)}
    (p : ReconstructionData) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    {H κ β : ℝ} (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hi : IncrementBounds s H (rankIncrement p r axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hcurrent : MeanClass s β (u.thetaResidual c))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((rankStage p r axial c u).thetaResidual c) := by
  have hz : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrement p r axial c u).angular n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero s.isOpen_domain hi.angular.smooth
      (DefectIncrementBounds.rankIncrement_angular_slow p r axial c u) v n hx
  have hdelta := thetaResidual_change_slow_mem ho hb hm hi hH u.covariance hW c.virtualTheta hz
  have hnew : (rankStage p r axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base
        (updated u.mean (rankIncrement p r axial c u)) u.covariance c.virtualTheta := by
    simp [rankStage, reconstructPressure, State.thetaResidual, State.addIncrement]
    rfl
  apply class_congr (hcurrent.add (hdelta.mono_exponent hβ))
  intro n x hx
  rw [hnew]
  change _ = u.thetaResidual c n x + (_ - u.thetaResidual c n x)
  ring


-- @@ L1093-1129 verbatim
theorem rankStage_axial_mem {s : StripData (PressureStream.Lift S)}
    (p : ReconstructionData) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hg : DefectIncrementBounds.RankGeometry p r c u)
    {H κ β : ℝ} (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hi : IncrementBounds s H (rankIncrement p r axial c u))
    (hp : SmoothOn s.domain u.pressure)
    (hdp : MeanClass s H (rankPressureChange p r axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hcurrent : MeanClass s β (u.axialResidual c))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((rankStage p r axial c u).axialResidual c) := by
  have hz : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrement p r axial c u).axial n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero s.isOpen_domain hi.axial.smooth (hg.axial_slow axial) v n hx
  have hdelta := axialResidual_change_slow_mem ho hb hm hi hH u.covariance hW
    u.pressure (rankPressureChange p r axial c u) c.virtualAxial hp hdp hz
  have hpressure : u.pressure + rankPressureChange p r axial c u =
      (rankStage p r axial c u).pressure := by
    unfold rankPressureChange
    abel
  have hnew : (rankStage p r axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (rankIncrement p r axial c u)) u.covariance
        (u.pressure + rankPressureChange p r axial c u) c.virtualAxial := by
    rw [hpressure]
    simp [rankStage, reconstructPressure, State.axialResidual, State.addIncrement]
    rfl
  apply class_congr (hcurrent.add (hdelta.mono_exponent hβ))
  intro n x hx
  rw [hnew]
  change _ = u.axialResidual c n x + (_ - u.axialResidual c n x)
  ring


-- @@ L1131-1143 verbatim
theorem rankStage_cumulative {s : StripData (PressureStream.Lift S)}
    (p : ReconstructionData) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (rankIncrement p r axial c u))
    (hp : MeanClass s H (rankPressureChange p r axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (rankStage p r axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (rankStage p r axial c u).pressure = u.pressure + rankPressureChange p r axial c u := by
    unfold rankPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)


-- @@ L1145-1145 verbatim
end RankMeanComposition


-- @@ L1147-1147 verbatim
section ExcludedMeanErrors


-- @@ L1149-1149 verbatim
open CorrectionState MeasureTheory


-- @@ L1151-1160 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_add {f g : OscillatoryScalar D}
    (hf : ∀ n x, Continuous (fun θ : ℝ => f n (x, θ)))
    (hg : ∀ n x, Continuous (fun θ : ℝ => g n (x, θ))) :
    angularAverage (f + g) = angularAverage f + angularAverage g := by
  funext n x
  change (∫ θ in (0 : ℝ)..2 * Real.pi, f n (x, θ) + g n (x, θ)) / (2 * Real.pi) = _
  rw [intervalIntegral.integral_add ((hf n x).intervalIntegrable _ _)
    ((hg n x).intervalIntegrable _ _), add_div]
  rfl


-- @@ L1162-1167 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularMeanVector_add {f g : Oscillation D}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    angularMeanVector (f + g) = angularMeanVector f + angularMeanVector g := by
  funext n x i
  exact congrFun (congrFun (angularAverage_add (fun n x => hf n x i) (fun n x => hg n x i)) n) x


-- @@ L1169-1179 verbatim
/-- The base error is restored and subtracted exactly once.  Gaussian and
alias errors remain actual subtracted means, with no zero/flat substitution. -/
theorem meanGoodResidual_exact_errors (c : Context D) (u : State D)
    (hb : AngularContinuous u.errors.base) (hg : AngularContinuous u.errors.gaussian)
    (ha : AngularContinuous u.errors.aliasError) :
    u.meanGoodResidual c = u.reducedMeanResidual c - angularMeanVector u.errors.gaussian -
      angularMeanVector u.errors.aliasError := by
  change u.reducedMeanResidual c + angularMeanVector u.errors.base -
    angularMeanVector (u.errors.base + u.errors.gaussian + u.errors.aliasError) = _
  rw [angularMeanVector_add (hb.add hg) ha, angularMeanVector_add hb hg]
  abel


-- @@ L1181-1198 verbatim
/-- The same cancellation only uses angular continuity on the selected
fiber. No regularity outside the current physical domain is needed. -/
theorem meanGoodResidual_at (c : Context D) (u : State D) (n : ℕ) (x : D) (i : Fin 3)
    (hb : Continuous (fun θ : ℝ => u.errors.base n (x, θ) i))
    (hg : Continuous (fun θ : ℝ => u.errors.gaussian n (x, θ) i))
    (ha : Continuous (fun θ : ℝ => u.errors.aliasError n (x, θ) i)) :
    u.meanGoodResidual c n x i = u.reducedMeanResidual c n x i -
      angularMeanVector u.errors.gaussian n x i - angularMeanVector u.errors.aliasError n x i := by
  change u.reducedMeanResidual c n x i +
    HarmonicResidual.realAngularMean (fun θ => u.errors.base n (x, θ) i) -
    HarmonicResidual.realAngularMean (fun θ =>
      u.errors.base n (x, θ) i + u.errors.gaussian n (x, θ) i +
        u.errors.aliasError n (x, θ) i) = _
  rw [HarmonicResidual.realAngularMean_add (hb.fun_add hg) ha,
    HarmonicResidual.realAngularMean_add hb hg]
  dsimp only [angularMeanVector, angularAverage, HarmonicResidual.realAngularMean,
    HarmonicFields.period]
  ring


-- @@ L1200-1220 verbatim
theorem meanResidualBounds_of_explicit_errors {s : StripData D} {σ : ℝ}
    (c : Context D) (u : State D)
    (hb : AngularContinuous u.errors.base) (hg : AngularContinuous u.errors.gaussian)
    (ha : AngularContinuous u.errors.aliasError)
    (hθ : MeanClass s (1 + σ) (u.thetaResidual c))
    (hz : MeanClass s (1 + σ) (u.axialResidual c))
    (hgθ : MeanClass s (1 + σ) (fun n x => angularMeanVector u.errors.gaussian n x 1))
    (hgz : MeanClass s (1 + σ) (fun n x => angularMeanVector u.errors.gaussian n x 2))
    (haθ : MeanClass s (1 + σ) (fun n x => angularMeanVector u.errors.aliasError n x 1))
    (haz : MeanClass s (1 + σ) (fun n x => angularMeanVector u.errors.aliasError n x 2)) :
    CorrectionState.MeanResidualBounds s σ c u := by
  have he := meanGoodResidual_exact_errors c u hb hg ha
  constructor
  · apply class_congr (Class.sub (Class.sub hθ hgθ) haθ)
    intro n x hx
    rw [he]
    rfl
  · apply class_congr (Class.sub (Class.sub hz hgz) haz)
    intro n x hx
    rw [he]
    rfl


-- @@ L1222-1222 verbatim
end ExcludedMeanErrors


-- @@ L1224-1224 verbatim
section ConcreteRankConstruction


-- @@ L1226-1226 verbatim
open CorrectionState


-- @@ L1228-1238 verbatim
/-- The concrete normalized five-row inverse uses the physical coordinate
functions of the current slow point, with no dependence on the torus slot. -/
noncomputable def normalizedRankData (coord A B lam a b : ℝ) :
    RankData PressureStream.Plane where
  lambda := lam
  inner := a
  outer := b
  length := fun _ z => Real.sqrt (MeanRankUpdate.chartQ coord (0, z, 0))
  velocity := fun _ z => MeanRankUpdate.chartQ coord (0, z, 0) ^ (-A)
  coefficient := fun _ z => MeanRankUpdate.shapedAmplitude B
    (MeanRankUpdate.chartEta coord (0, z, 0))


-- @@ L1240-1244 verbatim
theorem normalizedRank_angular (coord A B lam a b : ℝ)
    (c : Context MeanRankUpdate.ChartPoint) (u : State MeanRankUpdate.ChartPoint) (n : ℕ) :
    MeanRankUpdate.slowLift (rankAngular (normalizedRankData coord A B lam a b) c u n) =
      MeanRankUpdate.chartAngular coord A B lam a b (fun z => debt c u n z.2.1) := by
  rfl


-- @@ L1246-1250 verbatim
theorem normalizedRank_desired (coord A B lam a b : ℝ)
    (c : Context MeanRankUpdate.ChartPoint) (u : State MeanRankUpdate.ChartPoint) (n : ℕ) :
    rankDesiredAxial (normalizedRankData coord A B lam a b) c u n =
      MeanRankUpdate.slowChartDesired coord A B lam a b (debt c u n) := by
  rfl


-- @@ L1252-1257 verbatim
theorem normalizedRank_potential (p : ReconstructionData) (coord A B lam a b : ℝ)
    (c : Context MeanRankUpdate.ChartPoint) (u : State MeanRankUpdate.ChartPoint) (n : ℕ) :
    rankPotential p (normalizedRankData coord A B lam a b) c u n =
      MeanRankUpdate.actualChartPotential coord A B lam a b p.exponent p.inner p.outer
        (p.frequency n) p.radialDirection (debt c u n) := by
  rfl


-- @@ L1259-1273 verbatim
theorem normalizedRank_radial (p : ReconstructionData) (coord A B lam a b : ℝ)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context MeanRankUpdate.ChartPoint) (u : State MeanRankUpdate.ChartPoint) :
    (rankIncrement p (normalizedRankData coord A B lam a b) axial c u).radial =
      fun n x => c.operators.epsilon n * MeanRankUpdate.actualChartRadial coord A B lam a b
        p.exponent p.inner p.outer (p.frequency n) p.radialDirection axial (debt c u n) x := by
  funext n x
  change -(fderiv ℝ (rankPotential p (normalizedRankData coord A B lam a b) c u n) x
    (0, c.operators.epsilon n • axial)) = _
  have hv : ((0 : ℝ), c.operators.epsilon n • axial) =
      c.operators.epsilon n • ((0 : ℝ), axial) := by simp
  rw [hv, map_smul]
  simp only [smul_eq_mul, normalizedRank_potential,
    MeanRankUpdate.actualChartRadial, PressureStream.streamBeta, PressureStream.graphDz,
    mul_neg]


-- @@ L1275-1300 verbatim
/-- All three classes of the actual rank increment follow from the measured
debt. The radial factor is the literal epsilon in `rankIncrement`. -/
theorem normalizedRankIncrement_mem (s : StripData MeanRankUpdate.ChartPoint)
    (p : ReconstructionData) (c : Context MeanRankUpdate.ChartPoint)
    (u : State MeanRankUpdate.ChartPoint)
    {coord A B lam a b qlo qhi H : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) (hB : B ≠ 0)
    (hp : 0 < p.exponent) (hlo : 0 < p.inner) (hqlo : 0 < qlo)
    (hleft : p.inner ≤ Real.sqrt qlo * a) (hright : Real.sqrt qhi * b ≤ p.outer)
    (hT : ∀ x ∈ s.domain, MeanRankUpdate.chartInput x ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ x ∈ s.domain, MeanRankUpdate.chartQ coord x ∈ Icc qlo qhi)
    (hR : ∀ x ∈ s.domain, x.1 ∈ Icc p.inner p.outer)
    (hz : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s.domain,
      x ∈ MeanRankUpdate.supportBand a b qlo qhi → δ ≤ s.zeta x)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (hε : c.operators.epsilon = s.epsilon)
    (hd : UnweightedClass s H (fun n x => debt c u n x.2.1)) :
    IncrementBounds s H (rankIncrement p (normalizedRankData coord A B lam a b) axial c u) := by
  have hv := MeanRankUpdate.actual_rank_velocity_meanClass (A := A) s hc hc1 hlam ha hab hB hp hlo
    p.inner_lt_outer hqlo hleft hright hT hq hR hz p.frequency (fun _ => p.radialDirection) axial hd
  refine ⟨?_, ?_, ?_⟩
  · rw [normalizedRank_radial, hε]
    exact MeanRankUpdate.radial_physical_scale_gain s hv.2.2
  · exact hv.1
  · exact hv.2.1


-- @@ L1302-1302 verbatim
end ConcreteRankConstruction


-- @@ L1304-1304 verbatim
section RankPressureConstruction


-- @@ L1306-1306 verbatim
open CorrectionState


-- @@ L1308-1308 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1310-1319 verbatim
theorem rankStage_pressure_formula (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (rankStage p r axial c u).pressure =
      reconstructedPressure p.exponent p.inner p.outer p.inner_lt_outer p.frequency
        (fun _ => p.radialDirection) c.operators c.base
        (updated u.mean (rankIncrement p r axial c u)) u.covariance := by
  simp [rankStage, reconstructPressure, State.addIncrement,
    State.gr]
  rfl


-- @@ L1321-1359 verbatim
/-- The pressure estimate is for the pressure actually recomputed after
the rank correction. The input is the current radial source, not an assumed
bound on the new pressure. -/
theorem rankPressureChange_mem (p : ReconstructionData) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H κ : ℝ}
    (ha : 0 < p.inner) (hd : 0 < p.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (ho : OperatorBounds (WeightedRadialPrimitive.logStripData p.inner p.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.operators κ)
    (hb : BaseBounds (WeightedRadialPrimitive.logStripData p.inner p.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds (WeightedRadialPrimitive.logStripData
      p.inner p.outer cL cR ha hcL hcR c.operators.epsilon L hε hεone hL) u.mean)
    (hi : IncrementBounds (WeightedRadialPrimitive.logStripData p.inner p.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H (rankIncrement p r axial c u))
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (hW : ∀ i j, SmoothOn (WeightedRadialPrimitive.logStripData p.inner p.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL).domain (u.covariance i j))
    (hf : ∀ n, ContDiff ℝ ∞ (MeanIncrementBounds.gr c.operators c.base
      (updated u.mean (rankIncrement p r axial c u)) u.covariance n))
    (hg : ∀ n, ContDiff ℝ ∞ (u.gr c n))
    (hsf : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (MeanIncrementBounds.gr
      c.operators c.base (updated u.mean (rankIncrement p r axial c u)) u.covariance n))
    (hsg : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.gr c n))
    (hpressure : u.pressure = (reconstructPressure p c u).pressure) :
    MeanClass (WeightedRadialPrimitive.logStripData p.inner p.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL) H
      (rankPressureChange p r axial c u) := by
  have hp := reconstructedPressure_change_mem ha p.inner_lt_outer hd hcL hcR
    c.operators.epsilon L hε hεone hL ho hb hm hi hH hκ u.covariance hW hf hg hsf hsg
    p.frequency (fun _ => p.radialDirection)
  have hpressure' : u.pressure = reconstructedPressure p.exponent p.inner p.outer
      p.inner_lt_outer p.frequency (fun _ => p.radialDirection) c.operators c.base
      u.mean u.covariance := hpressure
  unfold rankPressureChange
  rw [rankStage_pressure_formula, hpressure']
  exact hp


-- @@ L1361-1361 verbatim
end RankPressureConstruction


-- @@ L1363-1363 verbatim
section PressureAliasBookkeeping


-- @@ L1365-1365 verbatim
open CorrectionState


-- @@ L1367-1367 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1369-1375 verbatim
/-- Replace precisely the obsolete radial alias when the pressure has been
recomputed. All other accumulated aliases remain in the error field. -/
noncomputable def refreshPressureAlias (p : ReconstructionData)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  { current with errors := { current.errors with aliasError :=
      current.errors.aliasError + (pressureAlias p c current - pressureAlias p c old) } }


-- @@ L1377-1384 verbatim
theorem refreshPressureAlias_separated (p : ReconstructionData)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S))
    (other : Oscillation (PressureStream.Lift S))
    (he : current.errors.aliasError = other + pressureAlias p c old) :
    (refreshPressureAlias p c old current).errors.aliasError =
      other + pressureAlias p c current := by
  simp only [refreshPressureAlias, he]
  abel


-- @@ L1386-1388 verbatim
theorem refreshPressureAlias_fullResidual (p : ReconstructionData)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    fullResidual c (refreshPressureAlias p c old current) = fullResidual c current := rfl


-- @@ L1390-1397 verbatim
theorem refreshPressureAlias_fullGoodResidual (p : ReconstructionData)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    fullGoodResidual c (refreshPressureAlias p c old current) = fullGoodResidual c current -
      (pressureAlias p c current - pressureAlias p c old) := by
  unfold fullGoodResidual
  rw [refreshPressureAlias_fullResidual]
  simp only [refreshPressureAlias, ExcludedErrors.total]
  abel


-- @@ L1399-1413 verbatim
/-- The exact current radial alias cancels only the alias part of the
reconstructed radial equation; the repaired pressure defect remains. -/
theorem reconstructed_radial_minus_alias (p : ReconstructionData)
    (ha : 0 < p.inner) (hd : 0 < p.exponent) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (hoperator : ∀ f : ScalarField (PressureStream.Lift S), ∀ n x, c.operators.dr f n x =
      PressureStream.graphDr (PressureStream.physicalSpeed p.exponent (p.frequency n))
        (0, p.radialDirection) (f n) x)
    (hsmooth : ∀ n, ContDiff ℝ ∞ (u.gr c n))
    (hsupport : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.gr c n))
    (n : ℕ) (x : PressureStream.Lift S) :
    (reconstructPressure p c u).radialResidual c n x - pressureAlias p c u n (x, 0) 0 =
      -PressureStream.rho p.inner p.outer p.inner_lt_outer x.1 * pressureDefect c u n x.2.1 := by
  rw [CorrectionState.reconstructed_radial_residual p ha hd c u hoperator hsmooth hsupport]
  ring


-- @@ L1415-1415 verbatim
end PressureAliasBookkeeping


-- @@ L1417-1417 verbatim
section ActualHarmonicForcing


-- @@ L1419-1419 verbatim
open CorrectionState


-- @@ L1421-1422 verbatim
theorem fullResidual_eq_harmonicResidual (c : Context D) (u : State D) :
    fullResidual c u = HarmonicResidual.stateFullResidual c u := rfl


-- @@ L1424-1425 verbatim
theorem fullGoodResidual_eq_harmonicResidual (c : Context D) (u : State D) :
    fullGoodResidual c u = HarmonicResidual.stateGoodResidual c u := rfl


-- @@ L1427-1428 verbatim
theorem fullGoodWaveResidual_eq_harmonicResidual (c : Context D) (u : State D) :
    fullGoodWaveResidual c u = HarmonicResidual.stateGoodWaveResidual c u := rfl


-- @@ L1430-1444 verbatim
/-- The right-hand sides for the particular solves are obtained from the
literal current nonlinear PDE residual, by differentiating and convolving
its stored finite harmonics and then removing the zero harmonic. -/
theorem fullGoodWaveResidual_grouped {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {u : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasError : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasError u) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c u labels blocks gaussian aliasError n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullGoodWaveResidual c u n x i =
      ∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c u (blocks l) (gaussian l) (aliasError l)).oscillation n x
            i :=
  HarmonicResidual.stateGoodWaveResidual_grouped hU hrep h hx i


-- @@ L1446-1461 verbatim
/-- Reconstruction retains the actual zero mode and every stored error.
No mean equation or error-flatness assertion is hidden in this identity. -/
theorem fullResidual_harmonic_decomposition {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {u : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasError : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasError u) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c u labels blocks gaussian aliasError n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullResidual c u n x i =
      (∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c u (blocks l) (gaussian l) (aliasError l)).oscillation n x
            i) +
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasError c u n x.1 i +
      u.errors.total n x i :=
  HarmonicResidual.stateFullResidual_reconstructed hU hrep h hx i


-- @@ L1463-1463 verbatim
end ActualHarmonicForcing


-- @@ L1465-1465 verbatim
section TemporalMasses


-- @@ L1467-1467 verbatim
open CorrectionState MeasureTheory


-- @@ L1469-1469 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L1471-1487 verbatim
/-- The actual angular and reconstructed axial temporal increments have
zero torus mean before taking either radial moment. -/
theorem temporalIncrement_torusMean (p : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n))
    (n : ℕ) (x : ℝ × S) :
    PressureStream.torusAverage ((temporalIncrement p h axial c u).angular n) x = 0 ∧
      PressureStream.torusAverage ((temporalIncrement p h axial c u).axial n) x = 0 := by
  exact ⟨TemporalMeanUpdate.desiredIncrement_zeroMean h n (hθ n) (hpθ n) x,
    TemporalMeanUpdate.axialUpdate_zeroMean ha p.inner_lt_outer hd p.radialDirection h n
      (hz n) (hpz n) (hsz n) x⟩


-- @@ L1489-1528 verbatim
theorem temporalStage_preserve_masses (p : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hmθ : ∀ n, Continuous (u.mean.angular n)) (hmz : ∀ n, Continuous (u.mean.axial n))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n)) :
    radialMoment 2 (temporalStage p h axial c u).mean.angular = radialMoment 2 u.mean.angular ∧
      radialMoment 1 (temporalStage p h axial c u).mean.axial = radialMoment 1 u.mean.axial := by
  have hi := temporalIncrement_smooth p h axial c u Set.univ ha hd hθ hz hpθ hpz hsz
  have hiθ n : Continuous ((temporalIncrement p h axial c u).angular n) :=
    (contDiffOn_univ.mp (hi.angular n)).continuous
  have hiz n : Continuous ((temporalIncrement p h axial c u).axial n) :=
    (contDiffOn_univ.mp (hi.axial n)).continuous
  constructor
  · funext n z
    change DefectIncrementBounds.barMoment 2
        (u.mean.angular + (temporalIncrement p h axial c u).angular) n z =
      DefectIncrementBounds.barMoment 2 u.mean.angular n z
    simp only [DefectIncrementBounds.barMoment_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      change r ^ 2 * PressureStream.torusAverage
        (fun x => u.mean.angular n x + (temporalIncrement p h axial c u).angular n x) (r, z) = _
      rw [DefectIncrementBounds.torusAverage_add (hmθ n) (hiθ n),
        (temporalIncrement_torusMean p h axial c u ha hd hθ hz hpθ hpz hsz n (r, z)).1, add_zero]
  · funext n z
    change DefectIncrementBounds.barMoment 1
        (u.mean.axial + (temporalIncrement p h axial c u).axial) n z =
      DefectIncrementBounds.barMoment 1 u.mean.axial n z
    simp only [DefectIncrementBounds.barMoment_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      change r ^ 1 * PressureStream.torusAverage
        (fun x => u.mean.axial n x + (temporalIncrement p h axial c u).axial n x) (r, z) = _
      rw [DefectIncrementBounds.torusAverage_add (hmz n) (hiz n),
        (temporalIncrement_torusMean p h axial c u ha hd hθ hz hpθ hpz hsz n (r, z)).2, add_zero]


-- @@ L1530-1530 verbatim
end TemporalMasses


-- @@ L1532-1532 verbatim
section ActualMeanAndDivergence


-- @@ L1534-1534 verbatim
open CorrectionState


-- @@ L1536-1540 verbatim
theorem angularMean_fullGoodResidual {U : Set D} {c : Context D} {u : State D}
    (H : LiftedMeanResidual.MeanHypotheses U c u) (n : ℕ) {x : D}
    (hx : x ∈ U) (i : Fin 3) :
    angularMeanVector (fullGoodResidual c u) n x i = u.meanGoodResidual c n x i :=
  LiftedMeanResidual.angularMean_fullGoodResidual H n hx i


-- @@ L1542-1555 verbatim
/-- The zero harmonic of the differentiated coefficient reconstruction is
the actual mean equation, with its exact excluded-error subtraction. -/
theorem meanCoefficientValue_eq_meanResidual {ι : Type*} {U : Set D}
    {c : Context D} {u : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasError : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasError u)
    (H : LiftedMeanResidual.MeanHypotheses U c u) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c u labels blocks gaussian aliasError n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasError c u n x i =
      u.meanGoodResidual c n x i := by
  rw [HarmonicResidual.stateMeanCoefficientValue_eq_average H.isOpen hrep h hx i]
  exact angularMean_fullGoodResidual H n hx i


-- @@ L1557-1571 verbatim
theorem fullResidual_reconstructed_with_mean {ι : Type*} {U : Set D}
    {c : Context D} {u : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasError : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasError u)
    (H : LiftedMeanResidual.MeanHypotheses U c u) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c u labels blocks gaussian aliasError n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullResidual c u n x i =
      (∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c u (blocks l) (gaussian l) (aliasError l)).oscillation n x
            i) +
      u.meanGoodResidual c n x.1 i + u.errors.total n x i := by
  rw [fullResidual_harmonic_decomposition H.isOpen hrep h hx i,
    meanCoefficientValue_eq_meanResidual hrep H h hx.1 i]


-- @@ L1573-1575 verbatim
/-- Mean lift, defined pointwise by `meanComponents m n x.1`. -/
noncomputable def meanLift (m : Triple D) : Oscillation D :=
  fun n x => meanComponents m n x.1


-- @@ L1577-1581 verbatim
/-- Mean divergence, defined pointwise by `c.operators.dr m.radial n x + m.radial n x /
c.operators.radius x + c.operators.dz m.axial n x`. -/
noncomputable def meanDivergence (c : Context D) (m : Triple D) : ScalarField D :=
  fun n x => c.operators.dr m.radial n x + m.radial n x / c.operators.radius x +
    c.operators.dz m.axial n x


-- @@ L1583-1586 verbatim
/-- Full divergence as an element of `OscillatoryScalar D`. -/
noncomputable def fullDivergence (c : Context D) (u : State D) : OscillatoryScalar D :=
  fun n => LiftedMeanResidual.realDivergence (fun x => c.operators.radius x.1)
    (radialDirection c n) angularDirection (axialDirection c n) (u.totalVelocity c n)


-- @@ L1588-1610 verbatim
theorem meanLift_divergence {U : Set D} (hU : IsOpen U)
    (c : Context D) (m : Triple D) (hm : SmoothTriple U m)
    (n : ℕ) {x : D} (hx : x ∈ U) (θ : ℝ) :
    LiftedMeanResidual.realDivergence (fun y => c.operators.radius y.1)
      (radialDirection c n) angularDirection (axialDirection c n) (meanLift m n) (x, θ) =
      meanDivergence c m n x := by
  have hr := ((hm.radial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have ht := ((hm.angular n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hz := ((hm.axial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  change HarmonicCalculus.along (LiftedMeanResidual.liftDirection
      (fun y => c.operators.eR + (c.operators.radialFrequency n * c.operators.radialProfile y) •
        c.operators.vR)) (LiftedMeanResidual.liftScalar (m.radial n)) (x, θ) +
    m.radial n x / c.operators.radius x +
    HarmonicCalculus.along LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.liftScalar (m.angular n)) (x, θ) / c.operators.radius x +
    HarmonicCalculus.along (LiftedMeanResidual.liftDirection
      (fun _ => c.operators.epsilon n • c.operators.eZ))
      (LiftedMeanResidual.liftScalar (m.axial n)) (x, θ) = _
  rw [LiftedMeanResidual.along_lift hr, LiftedMeanResidual.theta_lift_zero ht,
    LiftedMeanResidual.along_lift hz]
  simp only [HarmonicCalculus.along, meanDivergence, Operators.dr, graphDerivative,
    Operators.dz, map_add, map_smul, smul_eq_mul, zero_div, add_zero]
  ring


-- @@ L1612-1631 verbatim
/-- Addition preserves actual cylindrical divergence by the derivative
sum rule. The correction's divergence is a separate explicit summand. -/
theorem fullDivergence_actual_update (c : Context D) (u : State D)
    (m : Triple D) (p : ScalarField D) (w : Oscillation D) (q : OscillatoryScalar D)
    (e : ExcludedErrors D) (n : ℕ) (x : D × ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x)
    (hi : ∀ i, DifferentiableAt ℝ (fun y => meanLift m n y i + w n y i) x) :
    fullDivergence c (u.addIncrement m p w q e) n x = fullDivergence c u n x +
      LiftedMeanResidual.realDivergence (fun y => c.operators.radius y.1)
        (radialDirection c n) angularDirection (axialDirection c n)
        (fun y => meanLift m n y + w n y) x := by
  have hv : (u.addIncrement m p w q e).totalVelocity c n =
      fun y => u.totalVelocity c n y + (meanLift m n y + w n y) := by
    funext y i
    have ht := congrFun (congrFun (congrFun
      (State.totalVelocity_addIncrement u c m p w q e) n) y) i
    simpa only [Pi.add_apply, meanLift, meanComponents, add_assoc] using ht
  unfold fullDivergence
  rw [hv]
  exact LiftedMeanResidual.realDivergence_add _ _ _ _ hu hi


-- @@ L1633-1633 verbatim
end ActualMeanAndDivergence


-- @@ L1635-1635 verbatim
section MeanDivergencePreservation


-- @@ L1637-1637 verbatim
open CorrectionState


-- @@ L1639-1655 verbatim
theorem meanAddition_fullDivergence {U : Set D} (hU : IsOpen U)
    (c : Context D) (u : State D) (m : Triple D) (p : ScalarField D)
    (q : OscillatoryScalar D) (e : ExcludedErrors D) (hm : SmoothTriple U m)
    (n : ℕ) {x : D} (hx : x ∈ U) (θ : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) (x, θ)) :
    fullDivergence c (u.addIncrement m p 0 q e) n (x, θ) =
      fullDivergence c u n (x, θ) + meanDivergence c m n x := by
  have hi (i : Fin 3) : DifferentiableAt ℝ (fun y => meanLift m n y i) (x, θ) := by
    have hs := LiftedMeanResidual.liftScalar_smooth
      (LiftedMeanResidual.tripleVector_smooth hm n i)
    exact (hs.contDiffAt ((LiftedMeanResidual.cylinder_open hU).mem_nhds
      ⟨hx, mem_univ θ⟩)).differentiableAt (by simp)
  have he := fullDivergence_actual_update c u m p 0 q e n (x, θ) hu
    (fun i => by simpa only [Pi.zero_apply, add_zero] using hi i)
  simp only [Pi.zero_apply, add_zero] at he
  rw [meanLift_divergence hU c m hm n hx θ] at he
  exact he


-- @@ L1657-1657 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1659-1661 verbatim
theorem fullDivergence_reconstructPressure (p : ReconstructionData)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    fullDivergence c (reconstructPressure p c u) = fullDivergence c u := rfl


-- @@ L1663-1673 verbatim
theorem meanDivergence_eq_graph (p : ReconstructionData)
    (epsilon fast : ℕ → ℝ) (axial slowTime : S × PressureStream.Plane)
    (temporal : PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (hcompat : c.operators = graphOperators p epsilon fast axial slowTime temporal)
    (m : Triple (PressureStream.Lift S)) (n : ℕ) (x : PressureStream.Lift S) :
    meanDivergence c m n x =
      PressureStream.graphDivergence (PressureStream.physicalSpeed p.exponent (p.frequency n))
        (0, p.radialDirection) (epsilon n • axial) (m.radial n) (m.axial n) x := by
  unfold meanDivergence
  rw [hcompat, graphOperators_dr, graphOperators_dz]
  rfl


-- @@ L1675-1675 verbatim
variable [FiniteDimensional ℝ S]


-- @@ L1677-1691 verbatim
theorem temporalIncrement_meanDivergence_zero (p : ReconstructionData) (h : ℝ)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hcompat : c.operators = graphOperators p c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n))
    (n : ℕ) (x : PressureStream.Lift S) :
    meanDivergence c (temporalIncrement p h axial c u) n x = 0 := by
  rw [meanDivergence_eq_graph p c.operators.epsilon c.operators.fastCoefficient
    axial slowTime temporal c hcompat]
  exact TemporalMeanUpdate.update_divergence_zero ha p.inner_lt_outer hd p.radialDirection
    (c.operators.epsilon n • axial) h n (hz n) (hpz n) (hsz n) x


-- @@ L1693-1711 verbatim
theorem temporalStage_fullDivergence (p : ReconstructionData) (h : ℝ)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hcompat : c.operators = graphOperators p c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n))
    (n : ℕ) (x : PressureStream.Lift S × ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x) :
    fullDivergence c (temporalStage p h axial c u) n x = fullDivergence c u n x := by
  rw [temporalStage, fullDivergence_reconstructPressure]
  have hi := temporalIncrement_smooth p h axial c u Set.univ ha hd hθ hz hpθ hpz hsz
  rw [meanAddition_fullDivergence isOpen_univ c u _ _ _ _ hi n (mem_univ x.1) x.2 hu,
    temporalIncrement_meanDivergence_zero p h axial slowTime temporal c u ha hd hcompat hz hpz hsz,
    add_zero]


-- @@ L1713-1725 verbatim
theorem temporalStage_zeroMasses (p : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hmθ : ∀ n, Continuous (u.mean.angular n)) (hmz : ∀ n, Continuous (u.mean.axial n))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n))
    (hzero : ZeroMasses u) : ZeroMasses (temporalStage p h axial c u) := by
  obtain ⟨ht, hz⟩ := temporalStage_preserve_masses p h axial c u ha hd hmθ hmz hθ hz hpθ hpz hsz
  exact ⟨ht.trans hzero.1, hz.trans hzero.2⟩


-- @@ L1727-1740 verbatim
omit [FiniteDimensional ℝ S] in
theorem rankIncrement_meanDivergence_zero (p : ReconstructionData) (r : RankData S)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hcompat : c.operators = graphOperators p c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (hf : ∀ n, ContDiff ℝ ∞ (rankDesiredAxial r c u n))
    (hs : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (rankDesiredAxial r c u n))
    (n : ℕ) (x : PressureStream.Lift S) :
    meanDivergence c (rankIncrement p r axial c u) n x = 0 := by
  rw [meanDivergence_eq_graph p c.operators.epsilon c.operators.fastCoefficient
    axial slowTime temporal c hcompat]
  exact rank_divergence_zero p r axial c u ha hd n (hf n) (hs n) x


-- @@ L1742-1759 verbatim
omit [FiniteDimensional ℝ S] in
theorem rankStage_fullDivergence {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (p : ReconstructionData) (r : RankData S)
    (axial slowTime : S × PressureStream.Plane) (temporal : PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hcompat : c.operators = graphOperators p c.operators.epsilon c.operators.fastCoefficient
      axial slowTime temporal)
    (hm : SmoothTriple U (rankIncrement p r axial c u))
    (hf : ∀ n, ContDiff ℝ ∞ (rankDesiredAxial r c u n))
    (hs : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (rankDesiredAxial r c u n))
    (n : ℕ) {x : PressureStream.Lift S × ℝ} (hx : x.1 ∈ U)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x) :
    fullDivergence c (rankStage p r axial c u) n x = fullDivergence c u n x := by
  rw [rankStage, fullDivergence_reconstructPressure]
  rw [meanAddition_fullDivergence hU c u _ _ _ _ hm n hx x.2 hu,
    rankIncrement_meanDivergence_zero p r axial slowTime temporal c u ha hd hcompat hf hs,
    add_zero]


-- @@ L1761-1761 verbatim
end MeanDivergencePreservation


-- @@ L1763-1763 verbatim
section CommonTemporalConstruction


-- @@ L1765-1765 verbatim
open CorrectionState


-- @@ L1767-1767 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1769-1774 verbatim
/-- Pressure reconstruction with the prescribed transported radial data
for each band. This is an actual field constructor. -/
noncomputable def reconstructPressureFamily (r : ℕ → ReconstructionData)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  { u with pressure := fun n => (reconstructPressure (r n) c u).pressure n }


-- @@ L1776-1781 verbatim
/-- Common temporal error as an element of `Oscillation (PressureStream.Lift S)`. -/
noncomputable def commonTemporalError (r : ℕ → ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : Oscillation (PressureStream.Lift S) :=
  fun n x => ![0, 0, -MeanChartCompatibility.fastAtIndex h n (index n)
    (MeanChartCompatibility.commonTemporalAlias r h index (u.axialResidual c) n) x.1]


-- @@ L1783-1790 verbatim
/-- Common temporal stage, constructed using `reconstructPressureFamily`. -/
noncomputable def commonTemporalStage (r : ℕ → ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  reconstructPressureFamily r c (u.addIncrement
    (MeanChartCompatibility.commonTemporalIncrement r h index axial c u) 0 0 0
    ⟨0, 0, commonTemporalError r h index c u⟩)


-- @@ L1792-1798 verbatim
/-- Common temporal pressure change, given by `(commonTemporalStage r h index axial c
u).pressure - u.pressure`. -/
noncomputable def commonTemporalPressureChange (r : ℕ → ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) :=
  (commonTemporalStage r h index axial c u).pressure - u.pressure


-- @@ L1800-1806 verbatim
theorem common_fastTime (h : ℝ) (index : ℕ → ℕ) (c : Context (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hf : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (f : ScalarField (PressureStream.Lift S)) (n : ℕ) (x : PressureStream.Lift S) :
    c.operators.fastTime f n x = MeanChartCompatibility.fastAtIndex h n (index n) (f n) x := by
  simp only [Operators.fastTime, hv, hf, MeanChartCompatibility.fastAtIndex, PressureStream.graphDz]


-- @@ L1808-1808 verbatim
variable [FiniteDimensional ℝ S]


-- @@ L1810-1816 verbatim
omit [FiniteDimensional ℝ S] in
theorem commonTemporalStage_native (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    commonTemporalStage (fun _ => r) h (ChartScales.nativeIndex h) axial c u =
      temporalStage r h axial c u := by
  rfl


-- @@ L1818-1838 verbatim
theorem commonTemporalIncrement_smooth (r : ℕ → ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (U : Set (PressureStream.Lift S))
    (ha : ∀ n, 0 < (r n).inner) (hd : ∀ n, 0 < (r n).exponent)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported (r n).inner (r n).outer (u.axialResidual c n)) :
    SmoothTriple U (MeanChartCompatibility.commonTemporalIncrement r h index axial c u) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact (PressureStream.streamBeta_contDiff (ha n) (r n).inner_lt_outer (hd n)
      (0, (r n).radialDirection) (c.operators.epsilon n • axial)
      (MeanChartCompatibility.temporalAtIndex_smooth h n (index n) (hz n) (hpz n))
      (MeanChartCompatibility.temporalAtIndex_supported h n (index n) (hsz n))).contDiffOn
  · exact (MeanChartCompatibility.temporalAtIndex_smooth h n (index n) (hθ n) (hpθ n)).contDiffOn
  · exact (PressureStream.streamGamma_contDiff (ha n) (r n).inner_lt_outer (hd n)
      (0, (r n).radialDirection)
      (MeanChartCompatibility.temporalAtIndex_smooth h n (index n) (hz n) (hpz n))
      (MeanChartCompatibility.temporalAtIndex_supported h n (index n) (hsz n))).contDiffOn


-- @@ L1840-1885 verbatim
/-- Fast cancellation is now performed at the chosen common index; the
remaining angular mean is the original torus bar plus the exact remainder. -/
theorem commonTemporalStage_theta_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (r : ℕ → ReconstructionData) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (ha : ∀ n, 0 < (r n).inner) (hd : ∀ n, 0 < (r n).exponent)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported (r n).inner (r n).outer (u.axialResidual c n)) :
    Agree U ((commonTemporalStage r h index axial c u).thetaResidual c)
      (meanBar (u.thetaResidual c) + thetaRemainder c.operators c.base u.mean
        (MeanChartCompatibility.commonTemporalIncrement r h index axial c u)) := by
  have hi := commonTemporalIncrement_smooth r h index axial c u U ha hd hθ hz hpθ hpz hsz
  have he := thetaResidual_change hU c.operators hprofile hb hm hi u.covariance hW c.virtualTheta
  have hnew : (commonTemporalStage r h index axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base
        (updated u.mean (MeanChartCompatibility.commonTemporalIncrement r h index axial c u))
        u.covariance c.virtualTheta := by
    simp [commonTemporalStage, reconstructPressureFamily, State.thetaResidual, State.addIncrement]
    rfl
  intro n x hx
  have he' := he n hx
  have hf := (MeanChartCompatibility.commonTemporalFields_fast_cancellation r h index
    c.operators.epsilon axial (u.thetaResidual c) (u.axialResidual c) n (ha n) (hd n)
    (hθ n) (hz n) (hpθ n) (hpz n) (hsz n) x).1
  have ht := common_fastTime h index c hv hfast
    (MeanChartCompatibility.commonTemporalIncrement r h index axial c u).angular n x
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply, ht] at he'
  simp only [TemporalMeanUpdate.centered] at hf
  change _ = PressureStream.torusAverage (u.thetaResidual c n) (x.1, x.2.1) + _
  change MeanChartCompatibility.fastAtIndex h n (index n)
    ((MeanChartCompatibility.commonTemporalIncrement r h index axial c u).angular n) x +
      (u.thetaResidual c n x - PressureStream.torusAverage (u.thetaResidual c n) (x.1, x.2.1)) = 0
          at hf
  change _ - u.thetaResidual c n x = _ at he'
  linarith


-- @@ L1887-1944 verbatim
theorem commonTemporalStage_axial_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (r : ℕ → ReconstructionData) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (ha : ∀ n, 0 < (r n).inner) (hd : ∀ n, 0 < (r n).exponent)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hp : SmoothOn U u.pressure)
    (hnp : SmoothOn U (commonTemporalStage r h index axial c u).pressure)
    (hθ : ∀ n, ContDiff ℝ ∞ (u.thetaResidual c n))
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (u.thetaResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported (r n).inner (r n).outer (u.axialResidual c n)) :
    Agree U (fun n x => (commonTemporalStage r h index axial c u).axialResidual c n x -
      commonTemporalError r h index c u n (x, 0) 2)
      (meanBar (u.axialResidual c) + axialRemainder c.operators c.base u.mean
        (MeanChartCompatibility.commonTemporalIncrement r h index axial c u)
        (commonTemporalPressureChange r h index axial c u)) := by
  have hi := commonTemporalIncrement_smooth r h index axial c u U ha hd hθ hz hpθ hpz hsz
  have he := axialResidual_change hU c.operators hprofile hb hm hi u.covariance hW
    u.pressure (commonTemporalPressureChange r h index axial c u) c.virtualAxial hp (hnp.sub hp)
  have hpressure : u.pressure + commonTemporalPressureChange r h index axial c u =
      (commonTemporalStage r h index axial c u).pressure := by
    unfold commonTemporalPressureChange
    abel
  have hnew : (commonTemporalStage r h index axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (MeanChartCompatibility.commonTemporalIncrement r h index axial c u))
        u.covariance (u.pressure + commonTemporalPressureChange r h index axial c u) c.virtualAxial
            := by
    rw [hpressure]
    simp [commonTemporalStage, reconstructPressureFamily, State.axialResidual, State.addIncrement]
    rfl
  intro n x hx
  have he' := he n hx
  have hf := (MeanChartCompatibility.commonTemporalFields_fast_cancellation r h index
    c.operators.epsilon axial (u.thetaResidual c) (u.axialResidual c) n (ha n) (hd n)
    (hθ n) (hz n) (hpθ n) (hpz n) (hsz n) x).2
  have ht := common_fastTime h index c hv hfast
    (MeanChartCompatibility.commonTemporalIncrement r h index axial c u).axial n x
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply, ht] at he'
  simp only [TemporalMeanUpdate.centered] at hf
  change _ = PressureStream.torusAverage (u.axialResidual c n) (x.1, x.2.1) + _
  change MeanChartCompatibility.fastAtIndex h n (index n)
    ((MeanChartCompatibility.commonTemporalIncrement r h index axial c u).axial n) x +
      (u.axialResidual c n x - PressureStream.torusAverage (u.axialResidual c n) (x.1, x.2.1)) =
        -MeanChartCompatibility.fastAtIndex h n (index n)
          (MeanChartCompatibility.commonTemporalAlias r h index (u.axialResidual c) n) x at hf
  change _ - u.axialResidual c n x = _ at he'
  change _ - -MeanChartCompatibility.fastAtIndex h n (index n)
    (MeanChartCompatibility.commonTemporalAlias r h index (u.axialResidual c) n) x = _
  linarith


-- @@ L1946-1946 verbatim
end CommonTemporalConstruction


-- @@ L1948-1948 verbatim
section CommonTemporalScale


-- @@ L1950-1950 verbatim
open CorrectionState


-- @@ L1952-1952 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L1954-1967 verbatim
theorem streamPotential_const_mul (d a b M c : ℝ) (v : S) (f : ℝ × S → ℝ) :
    PressureStream.streamPotential d a b M v (fun x => c * f x) =
      fun x => c * PressureStream.streamPotential d a b M v f x := by
  have he : RadialPullback.normalizeSource d a (PressureStream.weightedSource (fun x => c * f x)) =
      fun x => c • RadialPullback.normalizeSource d a (PressureStream.weightedSource f) x := by
    funext x
    simp only [RadialPullback.normalizeSource, PressureStream.weightedSource, smul_eq_mul]
    ring
  funext x
  simp only [PressureStream.streamPotential, PressureStream.divideRadius,
    RadialPullback.physicalCompact, RadialPullback.pullback, Function.comp_apply, he]
  rw [TransportPrimitive.compactIntegral_smul]
  simp only [smul_eq_mul]
  ring


-- @@ L1969-1973 verbatim
/-- Scale triple, bundling `radial`, `angular`, `axial`. -/
noncomputable def scaleTriple (a : ℕ → ℝ) (m : Triple D) : Triple D where
  radial := fun n x => a n * m.radial n x
  angular := fun n x => a n * m.angular n x
  axial := fun n x => a n * m.axial n x


-- @@ L1975-1981 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem triple_ext {a b : Triple D} (hr : a.radial = b.radial)
    (ht : a.angular = b.angular) (hz : a.axial = b.axial) : a = b := by
  cases a
  cases b
  simp only [Triple.mk.injEq] at *
  exact ⟨hr, ht, hz⟩


-- @@ L1983-1989 verbatim
theorem scaleTriple_mem {s : StripData D} {H : ℝ} {a : ℕ → ℝ} {m : Triple D}
    (ha : BandBound s 0 a) (hm : IncrementBounds s H m) :
    IncrementBounds s H (scaleTriple a m) := by
  constructor
  · simpa only [scaleTriple, smul_eq_mul, add_zero] using hm.radial.band_smul ha
  · simpa only [scaleTriple, smul_eq_mul, add_zero] using hm.angular.band_smul ha
  · simpa only [scaleTriple, smul_eq_mul, add_zero] using hm.axial.band_smul ha


-- @@ L1991-1991 verbatim
variable [FiniteDimensional ℝ S]


-- @@ L1993-2040 verbatim
/-- Changing the common clock multiplies the actual inverse and its
actual stream realization by the same band scalar. -/
theorem commonTemporalIncrement_eq_scale (p : ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (ha : 0 < p.inner) (hd : 0 < p.exponent)
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n)) :
    MeanChartCompatibility.commonTemporalIncrement (fun _ => p) h index axial c u =
      scaleTriple (fun n => MeanChartCompatibility.commonRatio h n (index n))
        (temporalIncrement p h axial c u) := by
  have hpot n : MeanChartCompatibility.commonTemporalPotential (fun _ => p) h index
      (u.axialResidual c) n = fun x => MeanChartCompatibility.commonRatio h n (index n) *
        TemporalMeanUpdate.axialPotential p.exponent p.inner p.outer (p.frequency n)
          p.radialDirection h n (u.axialResidual c n) x := by
    unfold MeanChartCompatibility.commonTemporalPotential
    rw [MeanChartCompatibility.temporalAtIndex_eq_native, streamPotential_const_mul]
    rfl
  have hdpot n x := ((TemporalMeanUpdate.axialPotential_smooth (M := p.frequency n) ha
      p.inner_lt_outer hd
    p.radialDirection h n (hz n) (hpz n) (hsz n)).differentiable (by
        simp) x).hasFDerivAt.fun_const_smul
      (MeanChartCompatibility.commonRatio h n (index n))
  simp only [smul_eq_mul] at hdpot
  apply triple_ext
  · funext n x
    change PressureStream.streamBeta (c.operators.epsilon n • axial)
      (MeanChartCompatibility.commonTemporalPotential (fun _ => p) h index (u.axialResidual c) n) x
          = _
    rw [hpot]
    simp only [PressureStream.streamBeta, PressureStream.graphDz, (hdpot n x).fderiv,
      _root_.smul_apply, smul_eq_mul, scaleTriple, temporalIncrement,
      TemporalMeanUpdate.radialUpdate]
    ring
  · funext n x
    exact congrFun (MeanChartCompatibility.temporalAtIndex_eq_native h n (index n)
      (u.thetaResidual c n)) x
  · funext n x
    change PressureStream.streamGamma (PressureStream.physicalSpeed p.exponent (p.frequency n))
      (0, p.radialDirection)
      (MeanChartCompatibility.commonTemporalPotential (fun _ => p) h index (u.axialResidual c) n) x
          = _
    rw [hpot]
    simp only [PressureStream.streamGamma, PressureStream.graphDr, PressureStream.divideRadius,
      (hdpot n x).fderiv, _root_.smul_apply, smul_eq_mul, scaleTriple,
      temporalIncrement, TemporalMeanUpdate.axialUpdate]
    ring


-- @@ L2042-2061 verbatim
/-- The common/native gap has no cost in the residual exponent. This
statement works on any strip on which the native construction was proved. -/
theorem commonTemporalIncrement_mem_of_native {s : StripData (PressureStream.Lift S)}
    (p : ReconstructionData) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (ha : 0 < p.inner) (hd : 0 < p.exponent) (gap : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hz : ∀ n, ContDiff ℝ ∞ (u.axialResidual c n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (u.axialResidual c n))
    (hsz : ∀ n, RadialAlias.RadiallySupported p.inner p.outer (u.axialResidual c n))
    (hi : IncrementBounds s H (temporalIncrement p h axial c u)) :
    IncrementBounds s H (MeanChartCompatibility.commonTemporalIncrement (fun _ => p) h index axial
        c u) := by
  rw [commonTemporalIncrement_eq_scale p h index axial c u ha hd hz hpz hsz]
  apply scaleTriple_mem (hm := hi)
  refine ⟨ChartScales.Tg ^ gap, (pow_pos ChartScales.Tg_pos gap).le, 0, ?_⟩
  intro n
  simp only [Real.norm_eq_abs, abs_of_pos (MeanChartCompatibility.commonRatio_pos h n (index n)),
    Real.rpow_zero, pow_zero, mul_one]
  exact MeanChartCompatibility.commonRatio_le (hgap n)


-- @@ L2063-2063 verbatim
end CommonTemporalScale


-- @@ L2065-2065 verbatim
section HarmonicStateUpdates


-- @@ L2067-2067 verbatim
open CorrectionState


-- @@ L2069-2072 verbatim
/-- Add coefficient families on the same fixed label carrier. -/
noncomputable def addBlock (a b : HarmonicBlock D) : HarmonicBlock D :=
  { a with velocity := fun n i => a.velocity n i + b.velocity n i
           pressure := fun n => a.pressure n + b.pressure n }


-- @@ L2074-2078 verbatim
/-- Same carrier data, collecting `frequency`, `phase`, `angular`. -/
structure SameCarrier (a b : HarmonicBlock D) : Prop where
  frequency : b.frequency = a.frequency
  phase : b.phase = a.phase
  angular : b.angularFrequency = a.angularFrequency


-- @@ L2080-2085 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_oscillation (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (addBlock a b).oscillation = a.oscillation + b.oscillation := by
  funext n x i
  simp only [addBlock, HarmonicBlock.oscillation, HarmonicFields.field, HarmonicFields.evaluate_add,
    Complex.add_re, Pi.add_apply, h.frequency, h.phase, h.angular]


-- @@ L2087-2093 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_pressure (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (addBlock a b).oscillatoryPressure = a.oscillatoryPressure + b.oscillatoryPressure := by
  funext n x
  simp only [addBlock, HarmonicBlock.oscillatoryPressure, HarmonicFields.field,
      HarmonicFields.evaluate_add,
    Complex.add_re, Pi.add_apply, h.frequency, h.phase, h.angular]


-- @@ L2095-2100 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_band {a b : HarmonicBlock D} {N M : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited M) :
    (addBlock a b).BandLimited (max N M) :=
  ⟨fun n i => (ha.1 n i |>.mono (le_max_left _ _)).add (hb.1 n i |>.mono (le_max_right _ _)),
    fun n => (ha.2 n |>.mono (le_max_left _ _)).add (hb.2 n |>.mono (le_max_right _ _))⟩


-- @@ L2102-2105 verbatim
theorem addBlock_waveBounds {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {a b : HarmonicBlock D} (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (hαβ : α ≤ β) : (addBlock a b).WaveBounds s P α :=
  fun i j hj => (ha i j hj).add ((hb i j hj).mono_exponent hαβ)


-- @@ L2107-2110 verbatim
theorem addBlock_pressureBounds {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {a b : HarmonicBlock D} (ha : a.PressureBounds s P α) (hb : b.PressureBounds s P β)
    (hαβ : α ≤ β) : (addBlock a b).PressureBounds s P α :=
  fun j hj => (ha j hj).add ((hb j hj).mono_exponent hαβ)


-- @@ L2112-2126 verbatim
/-- The cumulative difference is the literal coefficient difference from
the same primary field, including all previous corrections. -/
theorem addBlock_differenceBounds {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (primary old increment : HarmonicBlock D)
    (hold : ∀ i j, j ≠ 0 → WaveClass s P α
      (fun n x => old.velocity n i j x - primary.velocity n i j x))
    (hi : increment.WaveBounds s P β) (hαβ : α ≤ β) :
    ∀ i j, j ≠ 0 → WaveClass s P α
      (fun n x => (addBlock old increment).velocity n i j x - primary.velocity n i j x) := by
  intro i j hj
  apply WaveInteractionBounds.class_congr ((hold i j hj).add ((hi i j hj).mono_exponent hαβ))
  intro n x hx
  change old.velocity n i j x - primary.velocity n i j x + increment.velocity n i j x =
    old.velocity n i j x + increment.velocity n i j x - primary.velocity n i j x
  ring


-- @@ L2128-2141 verbatim
theorem block_waveBounds_all {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (b : HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hzero : ∀ n i, b.velocity n i 0 = 0)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    ∀ i j, WaveClass s P α (fun n x => b.velocity n i j x) := by
  intro i j
  by_cases hj : j = 0
  · subst j
    have hz : WaveClass s P α (0 : ℕ → D → ℂ) := MemClass.zero (fun n x hx =>
      mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx))
    apply WaveInteractionBounds.class_congr hz
    intro n x hx
    simp only [hzero, Pi.zero_apply]
  · exact hb i j hj


-- @@ L2143-2147 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_angularContinuous (b : HarmonicBlock D) : AngularContinuous b.oscillation :=
  fun n x i => Complex.continuous_re.comp
    (HarmonicFields.field_angular_continuous (b.velocity n i) (b.frequency n)
      (b.phase n) (b.angularFrequency n) x)


-- @@ L2149-2172 verbatim
/-- Both old/new cross covariances and the entire new-wave square are
estimated as actual angular integrals. There is no tensor-update premise. -/
theorem sameCarrier_covarianceIncrement_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : HarmonicBlock D) (hcarrier : SameCarrier a b) (N M : ℕ)
    (hNa : a.BandLimited N) (hMb : b.BandLimited M)
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ∀ n i, a.velocity n i 0 = 0) (hb0 : ∀ n i, b.velocity n i 0 = 0)
    (hαβ : α ≤ β) (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    TensorClass s (α + β) (covarianceIncrement a.oscillation b.oscillation) := by
  have hca := block_waveBounds_all a ha ha0 hP0
  have hcb := block_waveBounds_all b hb hb0 hP0
  intro i j
  have hcross := HarmonicCovariance.mixedBlockCovariance_mem a b N hNa
    hcarrier.frequency hcarrier.phase hcarrier.angular hca hcb hP0 hP1 hkp i j
  have hreverse : MeanClass s (α + β) (bilinearCovariance b.oscillation a.oscillation i j) := by
    rw [bilinearCovariance_comm]
    exact HarmonicCovariance.mixedBlockCovariance_mem a b N hNa
      hcarrier.frequency hcarrier.phase hcarrier.angular hca hcb hP0 hP1 hkp j i
  have hsquare : MeanClass s (α + β) (bilinearCovariance b.oscillation b.oscillation i j) :=
    (HarmonicCovariance.blockCovariance_mem b M hMb hcb hP0 hP1
      (fun n => by simpa only [hcarrier.angular] using hkp n) i j).mono_exponent (by linarith)
  exact (hcross.add hreverse).add hsquare


-- @@ L2174-2194 verbatim
/-- Substitution of the constructed field into the state's covariance is
now paired with the tensor class of its exact change. -/
theorem oneLabel_stateCovariance_change {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (u : State D) (a b : HarmonicBlock D) (hu : u.oscillation = a.oscillation)
    (hcarrier : SameCarrier a b) (N M : ℕ)
    (hNa : a.BandLimited N) (hMb : b.BandLimited M)
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ∀ n i, a.velocity n i 0 = 0) (hb0 : ∀ n i, b.velocity n i 0 = 0)
    (hαβ : α ≤ β) (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (m : Triple D) (p : ScalarField D) (e : ExcludedErrors D) :
    TensorClass s (α + β)
      ((u.addIncrement m p b.oscillation b.oscillatoryPressure e).covariance - u.covariance) := by
  have hv : AngularContinuous u.oscillation := by rw [hu]; exact block_angularContinuous a
  rw [covariance_actual_update u m p b.oscillation b.oscillatoryPressure e hv
    (block_angularContinuous b)]
  have he : u.covariance + covarianceIncrement u.oscillation b.oscillation - u.covariance =
      covarianceIncrement a.oscillation b.oscillation := by rw [hu]; abel
  rw [he]
  exact sameCarrier_covarianceIncrement_mem a b hcarrier N M hNa hMb ha hb ha0 hb0 hαβ hkp hP0 hP1


-- @@ L2196-2196 verbatim
end HarmonicStateUpdates


-- @@ L2198-2198 verbatim
section MeanWaveComposition


-- @@ L2200-2200 verbatim
open CorrectionState


-- @@ L2202-2229 verbatim
/-- The actual residual block retains a target exponent through a mean
update. Its change is estimated by the two differentiated cross-advections. -/
theorem meanUpdate_residualBlock_mem {s : StripData D} {κ α H β : ℝ} {P : ℕ → D → ℝ}
    (c : Context D) (ho : OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (m : Triple D) (he : v.mean = updated u.mean m)
    (hbase : SmoothTriple s.domain c.base) (hmean : SmoothTriple s.domain u.mean)
    (hm : IncrementBounds s H m) (b : HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hN : ∀ i, UnweightedClass s 0
      (fun n x => HarmonicMeanInteraction.slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A₁ n i - A₀ n i) 0)
    (hold : (HarmonicResidual.residualBlock c u b G A₀).WaveBounds s P β)
    (hβ : β ≤ α + H - 1 / 2) :
    (HarmonicResidual.residualBlock c v b G A₁).WaveBounds s P β := by
  have hchange := HarmonicMeanInteraction.residualDifferenceBlock_class c ho hκ hR
    u v m he hbase hmean hm b hb hN hk hkp hP G A₀ A₁ hA
  intro i j hj
  apply WaveInteractionBounds.class_congr ((hold i j hj).add ((hchange i j hj).mono_exponent hβ))
  intro n x hx
  change (HarmonicResidual.residualBlock c u b G A₀).velocity n i j x +
    ((HarmonicResidual.residualBlock c v b G A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c u b G A₀).velocity n i j x) =
    (HarmonicResidual.residualBlock c v b G A₁).velocity n i j x
  ring


-- @@ L2231-2254 verbatim
/-- With the cumulative wave exponent `1/2`, each actual temporal or rank
mean increment has wave effect of exponent `H`. -/
theorem meanUpdate_residualBlock_next {s : StripData D} {κ σ : ℝ} {P : ℕ → D → ℝ}
    (c : Context D) (ho : OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 100000) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (m : Triple D) (he : v.mean = updated u.mean m)
    (hbase : SmoothTriple s.domain c.base) (hmean : SmoothTriple s.domain u.mean)
    (hm : IncrementBounds s (ExponentLedger.meanUpdateExponent σ κ) m)
    (b : HarmonicBlock D) (hb : b.WaveBounds s P (1 / 2))
    (hN : ∀ i, UnweightedClass s 0
      (fun n x => HarmonicMeanInteraction.slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A₁ n i - A₀ n i) 0)
    (hold : (HarmonicResidual.residualBlock c u b G A₀).WaveBounds s P
      (ExponentLedger.waveExponent (σ + 1 / 10))) :
    (HarmonicResidual.residualBlock c v b G A₁).WaveBounds s P
      (ExponentLedger.waveExponent (σ + 1 / 10)) := by
  apply meanUpdate_residualBlock_mem c ho (by linarith) hR u v m he hbase hmean hm b hb
    hN hk hkp hP G A₀ A₁ hA hold
  have hg := ExponentLedger.mean_update_wave_margin (σ := σ) hκ
  linarith


-- @@ L2256-2256 verbatim
end MeanWaveComposition


-- @@ L2258-2258 verbatim
section RankRetainedAlias


-- @@ L2260-2260 verbatim
open CorrectionState


-- @@ L2262-2262 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L2264-2304 verbatim
/-- A previously accumulated temporal alias remains subtracted through the
rank stage. No size assumption on that unchanged alias is needed here. -/
theorem rankStage_axial_sub_mem {s : StripData (PressureStream.Lift S)}
    (p : ReconstructionData) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hg : DefectIncrementBounds.RankGeometry p r c u)
    {H κ β : ℝ} (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hi : IncrementBounds s H (rankIncrement p r axial c u))
    (hp : SmoothOn s.domain u.pressure)
    (hdp : MeanClass s H (rankPressureChange p r axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (A : ScalarField (PressureStream.Lift S))
    (hcurrent : MeanClass s β (u.axialResidual c - A))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((rankStage p r axial c u).axialResidual c - A) := by
  have hz : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrement p r axial c u).axial n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero s.isOpen_domain hi.axial.smooth (hg.axial_slow axial) v n hx
  have hdelta := axialResidual_change_slow_mem ho hb hm hi hH u.covariance hW
    u.pressure (rankPressureChange p r axial c u) c.virtualAxial hp hdp hz
  have hpressure : u.pressure + rankPressureChange p r axial c u =
      (rankStage p r axial c u).pressure := by
    unfold rankPressureChange
    abel
  have hnew : (rankStage p r axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (rankIncrement p r axial c u)) u.covariance
        (u.pressure + rankPressureChange p r axial c u) c.virtualAxial := by
    rw [hpressure]
    simp [rankStage, reconstructPressure, State.axialResidual, State.addIncrement]
    rfl
  apply class_congr (hcurrent.add (hdelta.mono_exponent hβ))
  intro n x hx
  rw [hnew]
  change _ - _ = (_ - A n x) + (_ - _)
  simp only [State.axialResidual]
  ring


-- @@ L2306-2306 verbatim
end RankRetainedAlias


-- @@ L2308-2308 verbatim
section SignedTensorRemainder


-- @@ L2310-2310 verbatim
open CorrectionState MeasureTheory


-- @@ L2312-2314 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.neg {u : Oscillation D} (hu : AngularContinuous u) :
    AngularContinuous (-u) := fun n x i => (hu n x i).neg


-- @@ L2316-2319 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.sub {u v : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) : AngularContinuous (u - v) :=
  fun n x i => (hu n x i).sub (hv n x i)


-- @@ L2321-2328 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_neg_left (u v : Oscillation D) :
    bilinearCovariance (-u) v = -bilinearCovariance u v := by
  funext i j n x
  change (∫ θ in (0 : ℝ)..2 * Real.pi, -u n (x, θ) i * v n (x, θ) j) /
    (2 * Real.pi) = -((∫ θ in (0 : ℝ)..2 * Real.pi, u n (x, θ) i * v n (x, θ) j) /
      (2 * Real.pi))
  simp only [neg_mul, intervalIntegral.integral_neg, neg_div]


-- @@ L2330-2337 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_neg_right (u v : Oscillation D) :
    bilinearCovariance u (-v) = -bilinearCovariance u v := by
  funext i j
  rw [bilinearCovariance_comm u (-v) i j,
    congrFun (congrFun (bilinearCovariance_neg_left v u) j) i]
  change -bilinearCovariance v u j i = -bilinearCovariance u v i j
  rw [bilinearCovariance_comm v u j i]


-- @@ L2339-2344 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_sub_left {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance (u - v) w = bilinearCovariance u w - bilinearCovariance v w := by
  rw [sub_eq_add_neg, bilinearCovariance_add_left hu hv.neg hw,
    bilinearCovariance_neg_left, sub_eq_add_neg]


-- @@ L2346-2351 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearCovariance_sub_right {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance u (v - w) = bilinearCovariance u v - bilinearCovariance u w := by
  rw [sub_eq_add_neg, bilinearCovariance_add_right hu hv hw.neg,
    bilinearCovariance_neg_right, sub_eq_add_neg]


-- @@ L2353-2355 verbatim
/-- Symmetric covariance, given by `bilinearCovariance u v + bilinearCovariance v u`. -/
noncomputable def symmetricCovariance (u v : Oscillation D) : Tensor D :=
  bilinearCovariance u v + bilinearCovariance v u


-- @@ L2357-2360 verbatim
/-- The signed update is separated at the level of actual angular
integrals. The square contains the entire tangent plus curl increment. -/
noncomputable def signedTensorRemainder (primary old tangent curl : Oscillation D) : Tensor D :=
  covarianceIncrement old (tangent + curl) - symmetricCovariance primary tangent


-- @@ L2362-2372 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem signedTensorRemainder_exact (primary old tangent curl : Oscillation D)
    (hp : AngularContinuous primary) (ho : AngularContinuous old)
    (ht : AngularContinuous tangent) (hc : AngularContinuous curl) :
    signedTensorRemainder primary old tangent curl =
      symmetricCovariance (old - primary) tangent + symmetricCovariance old curl +
        bilinearCovariance (tangent + curl) (tangent + curl) := by
  unfold signedTensorRemainder covarianceIncrement symmetricCovariance
  rw [bilinearCovariance_add_right ho ht hc, bilinearCovariance_add_left ht hc ho,
    bilinearCovariance_sub_left ho hp ht, bilinearCovariance_sub_right ht ho hp]
  abel


-- @@ L2374-2378 verbatim
/-- Sub block, given by `{ a with velocity := fun n i => a.velocity n i - b.velocity n i
pressure := fun n => a.pressure n - b.pressure n }`. -/
noncomputable def subBlock (a b : HarmonicBlock D) : HarmonicBlock D :=
  { a with velocity := fun n i => a.velocity n i - b.velocity n i
           pressure := fun n => a.pressure n - b.pressure n }


-- @@ L2380-2385 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem subBlock_oscillation (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (subBlock a b).oscillation = a.oscillation - b.oscillation := by
  funext n x i
  simp only [subBlock, HarmonicBlock.oscillation, HarmonicResidual.field_sub,
    Complex.sub_re, Pi.sub_apply, h.frequency, h.phase, h.angular]


-- @@ L2387-2394 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem subBlock_band {a b : HarmonicBlock D} {N M : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited M) :
    (subBlock a b).BandLimited (max N M) :=
  ⟨fun n i => HarmonicResidual.band_sub (ha.1 n i |>.mono (le_max_left _ _))
      (hb.1 n i |>.mono (le_max_right _ _)),
    fun n => HarmonicResidual.band_sub (ha.2 n |>.mono (le_max_left _ _))
      (hb.2 n |>.mono (le_max_right _ _))⟩


-- @@ L2396-2413 verbatim
theorem symmetricCovariance_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : HarmonicBlock D) (hcarrier : SameCarrier a b) (N : ℕ)
    (hNa : a.BandLimited N) (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : ∀ n i, a.velocity n i 0 = 0) (hb0 : ∀ n i, b.velocity n i 0 = 0)
    (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    TensorClass s (α + β) (symmetricCovariance a.oscillation b.oscillation) := by
  have hca := block_waveBounds_all a ha ha0 hP0
  have hcb := block_waveBounds_all b hb hb0 hP0
  intro i j
  have hcross := HarmonicCovariance.mixedBlockCovariance_mem a b N hNa
    hcarrier.frequency hcarrier.phase hcarrier.angular hca hcb hP0 hP1 hkp i j
  have hreverse : MeanClass s (α + β) (bilinearCovariance b.oscillation a.oscillation i j) := by
    rw [bilinearCovariance_comm]
    exact HarmonicCovariance.mixedBlockCovariance_mem a b N hNa
      hcarrier.frequency hcarrier.phase hcarrier.angular hca hcb hP0 hP1 hkp j i
  exact hcross.add hreverse


-- @@ L2415-2462 verbatim
/-- The three signed errors have exponents `δ+β`, `α+η`, and `2β`.
The stronger bound on the old-minus-primary field is used only for the
first term. No class of a resulting covariance is assumed. -/
theorem signedTensorRemainder_mem {s : StripData D} {P : ℕ → D → ℝ}
    {α δ β η γ : ℝ} (primary old tangent curl : HarmonicBlock D) (N : ℕ)
    (hop : SameCarrier old primary) (hot : SameCarrier old tangent)
    (hoc : SameCarrier old curl)
    (hpN : primary.BandLimited N) (hoN : old.BandLimited N)
    (htN : tangent.BandLimited N) (hcN : curl.BandLimited N)
    (ho : old.WaveBounds s P α)
    (hd : (subBlock old primary).WaveBounds s P δ)
    (ht : tangent.WaveBounds s P β) (hc : curl.WaveBounds s P η)
    (hp0 : ∀ n i, primary.velocity n i 0 = 0) (ho0 : ∀ n i, old.velocity n i 0 = 0)
    (ht0 : ∀ n i, tangent.velocity n i 0 = 0) (hc0 : ∀ n i, curl.velocity n i 0 = 0)
    (hβη : β ≤ η) (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β)
    (hkp : ∀ n, old.angularFrequency n ≠ 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    TensorClass s γ (signedTensorRemainder primary.oscillation old.oscillation
      tangent.oscillation curl.oscillation) := by
  have hdt : SameCarrier (subBlock old primary) tangent :=
    ⟨hot.frequency, hot.phase, hot.angular⟩
  have htc : SameCarrier tangent curl :=
    ⟨hoc.frequency.trans hot.frequency.symm, hoc.phase.trans hot.phase.symm,
      hoc.angular.trans hot.angular.symm⟩
  have hd0 : ∀ n i, (subBlock old primary).velocity n i 0 = 0 := by
    intro n i
    change old.velocity n i 0 - primary.velocity n i 0 = 0
    rw [ho0, hp0, sub_self]
  have hsum0 : ∀ n i, (addBlock tangent curl).velocity n i 0 = 0 := by
    intro n i
    change tangent.velocity n i 0 + curl.velocity n i 0 = 0
    rw [ht0, hc0, add_zero]
  have hdiff := symmetricCovariance_mem (subBlock old primary) tangent hdt (max N N)
    (subBlock_band hoN hpN) hd ht hd0 ht0 hkp hP0 hP1
  have hcurl := symmetricCovariance_mem old curl hoc N hoN ho hc ho0 hc0 hkp hP0 hP1
  have hsum := block_waveBounds_all (addBlock tangent curl)
    (addBlock_waveBounds ht hc hβη) hsum0 hP0
  have hsquare := HarmonicCovariance.blockCovariance_mem (addBlock tangent curl) (max N N)
    (addBlock_band htN hcN) hsum hP0 hP1
    (fun n => by simpa only [addBlock, hot.angular] using hkp n)
  rw [subBlock_oscillation old primary hop] at hdiff
  simp only [addBlock_oscillation tangent curl htc] at hsquare
  rw [signedTensorRemainder_exact _ _ _ _ (block_angularContinuous primary)
    (block_angularContinuous old) (block_angularContinuous tangent) (block_angularContinuous curl)]
  intro i j
  exact ((hdiff i j).mono_exponent hγd |>.add ((hcurl i j).mono_exponent hγc)).add
    ((hsquare i j).mono_exponent (by linarith))


-- @@ L2464-2497 verbatim
/-- Applying the fixed radial derivative loss still leaves the signed
tensor error at the manuscript's `.17` improvement. -/
theorem signedTensorRemainder_divergence_mem {s : StripData D} {P : ℕ → D → ℝ}
    {σ κ : ℝ} (c : Context D) (hops : OperatorBounds s c.operators κ)
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000)
    (primary old tangent curl : HarmonicBlock D) (N : ℕ)
    (hop : SameCarrier old primary) (hot : SameCarrier old tangent)
    (hoc : SameCarrier old curl)
    (hpN : primary.BandLimited N) (hoN : old.BandLimited N)
    (htN : tangent.BandLimited N) (hcN : curl.BandLimited N)
    (ho : old.WaveBounds s P (1 / 2))
    (hd : (subBlock old primary).WaveBounds s P (17 / 25))
    (ht : tangent.WaveBounds s P (ExponentLedger.waveExponent σ - κ))
    (hc : curl.WaveBounds s P (ExponentLedger.waveExponent σ + 1 / 2 - 2 * κ))
    (hp0 : ∀ n i, primary.velocity n i 0 = 0) (ho0 : ∀ n i, old.velocity n i 0 = 0)
    (ht0 : ∀ n i, tangent.velocity n i 0 = 0) (hc0 : ∀ n i, curl.velocity n i 0 = 0)
    (hkp : ∀ n, old.angularFrequency n ≠ 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    let E := signedTensorRemainder primary.oscillation old.oscillation tangent.oscillation
        curl.oscillation
    MeanClass s (ExponentLedger.meanExponent σ + 17 / 100) (thetaCovarianceChange c.operators E) ∧
      MeanClass s (ExponentLedger.meanExponent σ + 17 / 100) (axialCovarianceChange c.operators E) ∧
      MeanClass s (ExponentLedger.meanExponent σ + 17 / 100) (radialCovarianceChange c.operators E)
          := by
  have he := signedTensorRemainder_mem (γ := ExponentLedger.meanExponent σ + 17 / 100 + κ)
    primary old tangent curl N hop hot hoc hpN hoN htN hcN ho hd ht hc hp0 ho0 ht0 hc0
    (by linarith) (by unfold ExponentLedger.waveExponent ExponentLedger.meanExponent; linarith)
    (by unfold ExponentLedger.waveExponent ExponentLedger.meanExponent; linarith)
    (by unfold ExponentLedger.waveExponent ExponentLedger.meanExponent; linarith)
    hkp hP0 hP1
  simpa only [add_sub_cancel_right] using
    And.intro (thetaCovarianceChange_mem hops he)
      (And.intro (axialCovarianceChange_mem hops he) (radialCovarianceChange_mem hops he))


-- @@ L2499-2499 verbatim
end SignedTensorRemainder


-- @@ L2501-2501 verbatim
section LocalMeanConstruction


-- @@ L2503-2503 verbatim
open CorrectionState PhysicalMeanDomain


-- @@ L2505-2505 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L2507-2535 verbatim
/-- The native temporal construction is bounded on a genuine open slow
domain. The source need not satisfy estimates at nonpositive slow time. -/
theorem temporalIncrement_local_mem (r : ReconstructionData) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H : ℝ}
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (U : Set S) (hU : IsOpen U)
    (hθclass : MeanClass (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H (u.thetaResidual c))
    (hzclass : MeanClass (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H (u.axialResidual c))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain U))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain U))
    (hpθ : ∀ n, PeriodicOn U (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn U (u.axialResidual c n))
    (hsz : ∀ n, SupportedOn r.inner r.outer U (u.axialResidual c n)) :
    IncrementBounds (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H (temporalIncrement r h axial c u) := by
  refine ⟨?_, ?_, ?_⟩
  · exact PhysicalMeanDomain.meanClass_scaledRadialUpdate ha r.inner_lt_outer hd hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale U hU hz hpz hsz hzclass
      r.frequency (fun _ => r.radialDirection) axial
  · exact PhysicalMeanDomain.meanClass_desiredIncrement ha hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale U hU hθ hpθ hθclass
  · exact PhysicalMeanDomain.meanClass_axialUpdate ha r.inner_lt_outer hd hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale U hU hz hpz hsz hzclass
      r.frequency (fun _ => r.radialDirection)


-- @@ L2537-2544 verbatim
theorem commonRatio_bandBound {s : StripData D} (h : ℝ) (index : ℕ → ℕ) (gap : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap) :
    BandBound s 0 (fun n => MeanChartCompatibility.commonRatio h n (index n)) := by
  refine ⟨ChartScales.Tg ^ gap, (pow_pos ChartScales.Tg_pos gap).le, 0, ?_⟩
  intro n
  simp only [Real.norm_eq_abs, abs_of_pos (MeanChartCompatibility.commonRatio_pos h n (index n)),
    Real.rpow_zero, pow_zero, mul_one]
  exact MeanChartCompatibility.commonRatio_le (hgap n)


-- @@ L2546-2616 verbatim
/-- A local source estimate is transported through the actual common-clock
inverse and then through the actual stream. No output estimate or global
slow-domain extension is a hypothesis. -/
theorem commonTemporalIncrement_local_mem (r : ReconstructionData) (h : ℝ)
    (index : ℕ → ℕ) (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) {cL cR H : ℝ}
    (ha : 0 < r.inner) (hd : 0 < r.exponent) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (L : ℕ → ℝ) (hε : ∀ n, 0 < c.operators.epsilon n)
    (hεone : ∀ n, c.operators.epsilon n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n) (U : Set S) (hU : IsOpen U)
    (hθclass : MeanClass (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H (u.thetaResidual c))
    (hzclass : MeanClass (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H (u.axialResidual c))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain U))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain U))
    (hpθ : ∀ n, PeriodicOn U (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn U (u.axialResidual c n))
    (hsz : ∀ n, SupportedOn r.inner r.outer U (u.axialResidual c n)) :
    IncrementBounds (localStripData r.inner r.outer cL cR
      ha hcL hcR c.operators.epsilon L hε hεone hL U hU) H
      (MeanChartCompatibility.commonTemporalIncrement (fun _ => r) h index axial c u) := by
  let s := localStripData r.inner r.outer cL cR ha hcL hcR c.operators.epsilon L hε hεone hL U hU
  let z : ScalarField (PressureStream.Lift S) := fun n =>
    MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n)
  have hratio := commonRatio_bandBound (s := s) h index gap hgap
  have hzt : MeanClass s H z := by
    have hh' := (PhysicalMeanDomain.meanClass_desiredIncrement ha hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale U hU hz hpz hzclass).band_smul hratio
    simpa only [z, MeanChartCompatibility.temporalAtIndex_eq_native, smul_eq_mul, add_zero] using
        hh'
  have hzs : ∀ n, ContDiffOn ℝ ∞ (z n) (slowDomain U) := by
    intro n
    simpa only [z, MeanChartCompatibility.temporalAtIndex_eq_native] using
      (contDiffOn_const (c := MeanChartCompatibility.commonRatio h n (index n))).mul
        (PhysicalMeanDomain.desiredIncrement_contDiffOn h n hU (hz n) (hpz n))
  have hzsupport : ∀ n, SupportedOn r.inner r.outer U (z n) := by
    intro n x hx hn
    have hs := PhysicalMeanDomain.desiredIncrement_supportedOn h n hU (hz n) (hsz n)
    apply hs x hx
    have hn' : MeanChartCompatibility.commonRatio h n (index n) *
        TemporalMeanUpdate.desiredIncrement h n (u.axialResidual c n) x ≠ 0 := by
      simpa only [z, MeanChartCompatibility.temporalAtIndex_eq_native] using hn
    exact right_ne_zero_of_mul hn'
  refine ⟨?_, ?_, ?_⟩
  · have hi := PhysicalMeanDomain.meanClass_streamBeta ha r.inner_lt_outer hd hcL hcR
      c.operators.epsilon L hε hεone hL U hU hzs hzsupport hzt
      r.frequency (fun _ => r.radialDirection) axial
    have heps : BandBound s 1 c.operators.epsilon := by
      have he := bandBound_rpow s 1
      simp only [Real.rpow_one] at he
      exact he
    apply class_congr (hi.band_smul heps)
    intro n x hx
    simp only [MeanChartCompatibility.commonTemporalIncrement,
        MeanChartCompatibility.commonTemporalFields,
      MeanChartCompatibility.commonTemporalPotential, PressureStream.streamBeta,
      PressureStream.graphDz, smul_eq_mul]
    rw [show ((0 : ℝ), c.operators.epsilon n • axial) =
      c.operators.epsilon n • ((0 : ℝ), axial) by simp]
    simp only [map_smul, smul_eq_mul, mul_neg]
    rfl
  · have hi := (PhysicalMeanDomain.meanClass_desiredIncrement ha hcL hcR hh
      c.operators.epsilon L hε hεone hL hscale U hU hθ hpθ hθclass).band_smul hratio
    simpa only [MeanChartCompatibility.commonTemporalIncrement,
        MeanChartCompatibility.commonTemporalFields,
      MeanChartCompatibility.temporalAtIndex_eq_native, smul_eq_mul, add_zero] using hi
  · exact PhysicalMeanDomain.meanClass_streamGamma ha r.inner_lt_outer hd hcL hcR
      c.operators.epsilon L hε hεone hL U hU hzs hzsupport hzt
      r.frequency (fun _ => r.radialDirection)


-- @@ L2618-2643 verbatim
/-- Recomputed pressure on the same local slow domain. The source change
class is derived from the exact nonlinear radial equation. -/
theorem reconstructedPressure_local_change_mem
    {a b d cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hL : ∀ n, 1 ≤ L n) (U : Set S) (hU : IsOpen U) {κ H : ℝ}
    {o : Operators (PressureStream.Lift S)} {base mean inc : Triple (PressureStream.Lift S)}
    (ho : OperatorBounds (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) o κ)
    (hb : BaseBounds (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) mean)
    (hi : IncrementBounds (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) H inc)
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (W : Tensor (PressureStream.Lift S))
    (hW : ∀ i j, SmoothOn (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU).domain (W i j))
    (hf : ∀ n, ContDiffOn ℝ ∞ (gr o base (updated mean inc) W n) (slowDomain U))
    (hg : ∀ n, ContDiffOn ℝ ∞ (gr o base mean W n) (slowDomain U))
    (hsf : ∀ n, SupportedOn a b U (gr o base (updated mean inc) W n))
    (hsg : ∀ n, SupportedOn a b U (gr o base mean W n))
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) H
      (reconstructedPressure d a b hab M v o base (updated mean inc) W -
        reconstructedPressure d a b hab M v o base mean W) := by
  exact PhysicalMeanDomain.meanClass_meanPressure_change ha hab hd hcL hcR ε L hε hεone hL
    U hU hf hg hsf hsg (gr_change_mem ho hb hm hi hH W hW hκ) M v


-- @@ L2645-2645 verbatim
end LocalMeanConstruction


-- @@ L2647-2647 verbatim
section ConstructedSignedBlocks


-- @@ L2649-2649 verbatim
open CorrectionState SignedWaveUpdate


-- @@ L2651-2669 verbatim
/-- The class of a literal coefficient difference is transported from the
full cylindrical coefficient domain to the actual harmonic blocks. -/
theorem blockOfCoefficients_difference_mem
    {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α : ℝ}
    (a b : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (hab : WaveClass s P α (fun n x => a.amplitude n x - b.amplitude n x)) :
    (subBlock (blockOfCoefficients a kp) (blockOfCoefficients b kp)).WaveBounds
      (sectionStrip s) (fun n x => P n (x, 0)) α := by
  have hsection := class_zeroSection hab
  intro i j hj
  have hh := conjugatePair_class (CurlClassBounds.class_component hsection i) j
  apply WaveInteractionBounds.class_congr hh
  intro n x hx
  change ErrorHarmonics.conjugatePair 1 (fun x => a.amplitude n (x,0) i - b.amplitude n (x,0) i) j
      x =
    ErrorHarmonics.conjugatePair 1 (fun x => a.amplitude n (x,0) i) j x -
      ErrorHarmonics.conjugatePair 1 (fun x => b.amplitude n (x,0) i) j x
  simp only [conjugatePair_apply]
  split_ifs <;> simp only [map_sub, map_zero, sub_div] <;> ring


-- @@ L2671-2675 verbatim
theorem correctedBlock_sameCarrier
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) :
    SameCarrier (blockOfCoefficients (a.withCutoff ψ) kp)
      (blockOfCoefficients (a.corrected s d ψ) kp) := ⟨rfl, rfl, rfl⟩


-- @@ L2677-2687 verbatim
theorem correctedBlock_split
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ)) (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) :
    (blockOfCoefficients (a.corrected s d ψ) kp).oscillation =
      (blockOfCoefficients (a.withCutoff ψ) kp).oscillation +
        (subBlock (blockOfCoefficients (a.corrected s d ψ) kp)
          (blockOfCoefficients (a.withCutoff ψ) kp)).oscillation := by
  have h : SameCarrier (blockOfCoefficients (a.corrected s d ψ) kp)
      (blockOfCoefficients (a.withCutoff ψ) kp) := ⟨rfl, rfl, rfl⟩
  rw [subBlock_oscillation _ _ h]
  abel


-- @@ L2689-2726 verbatim
/-- The tangent and curl-difference blocks used by the tensor estimate are
the blocks of the actual signed quotient, homogeneous pressure, cutoff,
and curl construction. Their classes are conclusions from primitive data. -/
theorem constructedSignedBlock_bounds
    {s : StripData (D × ℝ)} {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {P₀ P : ℕ → D × ℝ → ℝ} {α₀ B κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a) (hκ : κ ≤ 1 / 2)
    {H : ℕ → D × ℝ → Mat2} {T R : ℕ → D × ℝ → Vec2} {mask ψ : ℕ → D × ℝ → ℝ}
    {v Ndot : ℕ → D × ℝ → Space} {A : ℕ → D × ℝ → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s (B - 1 / 2 - κ) (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n))
    {radius : D × ℝ → ℝ} (hradius : a.radius = fun _ => radius)
    (hψ : UnweightedClass s 0 ψ) (kp : ℕ → ℤ) (j : Fin 2) :
    let z := SignedWaveUpdate.coefficients a s d H T R mask v Ndot A j
    let tangent := blockOfCoefficients (z.withCutoff ψ) kp
    let exactBlock := blockOfCoefficients (z.corrected s d ψ) kp
    tangent.WaveBounds (sectionStrip s) (fun n x => P n (x,0)) (B - κ) ∧
      exactBlock.WaveBounds (sectionStrip s) (fun n x => P n (x,0)) (B - κ) ∧
      exactBlock.PressureBounds (sectionStrip s) (fun n x => P n (x,0)) (B + 1 / 2 - κ) ∧
      (subBlock exactBlock tangent).WaveBounds (sectionStrip s) (fun n x => P n (x,0))
        (B + 1 / 2 - 2 * κ) := by
  let z := SignedWaveUpdate.coefficients a s d H T R mask v Ndot A j
  have hi : LinearWaveBounds.InputBounds s P (B - κ) κ d z := by
    convert! coefficients_inputBounds hbase hcov hR hm hv hN hNdot hA hb hlo hhi hK j using 1
    ring
  have ht := blockOfCoefficients_classes (z.withCutoff ψ) kp
    (LinearWaveBounds.component_classes (hi.with_cutoff hψ).amplitude) (hi.with_cutoff hψ).pressure
  have he := signed_bounds hbase hκ hcov hR hm hv hN hNdot hA hb hlo hhi hK hradius hψ j
  have hex := blockOfCoefficients_classes (z.corrected s d ψ) kp he.1 he.2.1
  exact ⟨ht.1, hex.1, hex.2,
    blockOfCoefficients_difference_mem (z.corrected s d ψ) (z.withCutoff ψ) kp he.2.2.1⟩


-- @@ L2728-2728 verbatim
end ConstructedSignedBlocks


-- @@ L2730-2730 verbatim
section CumulativeWaveUpdates


-- @@ L2732-2732 verbatim
open CorrectionState


-- @@ L2734-2743 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Both wave insertions retain their original carrier. This equality is
about the actual evaluated fields, not only their coefficient arrays. -/
theorem twoWaveUpdates_oscillation (old particular signed : HarmonicBlock D)
    (hp : SameCarrier old particular) (hs : SameCarrier old signed) :
    (addBlock (addBlock old particular) signed).oscillation =
      old.oscillation + particular.oscillation + signed.oscillation := by
  have hs' : SameCarrier (addBlock old particular) signed :=
    ⟨hs.frequency, hs.phase, hs.angular⟩
  rw [addBlock_oscillation _ _ hs', addBlock_oscillation _ _ hp]


-- @@ L2745-2749 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem twoWaveUpdates_band {old particular signed : HarmonicBlock D} {N M K : ℕ}
    (ho : old.BandLimited N) (hp : particular.BandLimited M) (hs : signed.BandLimited K) :
    (addBlock (addBlock old particular) signed).BandLimited (max (max N M) K) :=
  addBlock_band (addBlock_band ho hp) hs


-- @@ L2751-2774 verbatim
/-- Cumulative bounds after the actual two coefficient additions. The
reference field in the difference is the same primary tangent throughout. -/
theorem twoWaveUpdates_cumulative {s : StripData D} {P : ℕ → D → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000)
    (primary old particular signed : HarmonicBlock D)
    (ho : old.WaveBounds s P (1 / 2))
    (hod : ∀ i j, j ≠ 0 → WaveClass s P (17 / 25)
      (fun n x => old.velocity n i j x - primary.velocity n i j x))
    (hop : old.PressureBounds s P 1)
    (hp : particular.WaveBounds s P (ExponentLedger.waveExponent σ))
    (hpp : particular.PressureBounds s P (ExponentLedger.waveExponent σ + 1 / 2))
    (hs : signed.WaveBounds s P (ExponentLedger.waveExponent σ - κ))
    (hsp : signed.PressureBounds s P (ExponentLedger.waveExponent σ + 1 / 2 - κ)) :
    let finalBlock := addBlock (addBlock old particular) signed
    finalBlock.WaveBounds s P (1 / 2) ∧
      (∀ i j, j ≠ 0 → WaveClass s P (17 / 25)
        (fun n x => finalBlock.velocity n i j x - primary.velocity n i j x)) ∧
      finalBlock.PressureBounds s P 1 := by
  have hpbound := ExponentLedger.particular_increment_above_cumulative_difference hσ
  have hsbound := ExponentLedger.signed_increment_above_cumulative_difference hσ hκ
  refine ⟨addBlock_waveBounds (addBlock_waveBounds ho hp (by linarith)) hs (by linarith), ?_, ?_⟩
  · exact addBlock_differenceBounds primary (addBlock old particular) signed
      (addBlock_differenceBounds primary old particular hod hp hpbound.le) hs hsbound.le
  · exact addBlock_pressureBounds (addBlock_pressureBounds hop hpp (by linarith)) hsp (by linarith)


-- @@ L2776-2776 verbatim
end CumulativeWaveUpdates


-- @@ L2778-2778 verbatim
section LocalCommonClock


-- @@ L2780-2780 verbatim
open CorrectionState PhysicalMeanDomain


-- @@ L2782-2782 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L2784-2789 verbatim
theorem temporalAtIndex_local_smooth (h : ℝ) (n i : ℕ) {V : Set S} (hV : IsOpen V)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain V))
    (hp : PeriodicOn V f) :
    ContDiffOn ℝ ∞ (MeanChartCompatibility.temporalAtIndex h n i f) (slowDomain V) := by
  rw [MeanChartCompatibility.temporalAtIndex_eq_native]
  exact contDiffOn_const.mul (PhysicalMeanDomain.desiredIncrement_contDiffOn h n hV hf hp)


-- @@ L2791-2809 verbatim
/-- The common clock cancels the actual local residual. Localization is
used only to prove a germ identity for the same torus inverse. -/
theorem temporalAtIndex_local_fast (h : ℝ) (n i : ℕ) {V : Set S} (hV : IsOpen V)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain V))
    (hp : PeriodicOn V f) {x : PressureStream.Lift S} (hx : x.2.1 ∈ V) :
    MeanChartCompatibility.fastAtIndex h n i (MeanChartCompatibility.temporalAtIndex h n i f) x =
      -TemporalMeanUpdate.centered f x := by
  obtain ⟨cutoff, _, hsupport, hglobal, he⟩ := exists_fiber_localization hV hx hf
  have hd := ((desiredIncrement_fiberLocal h n).germ he).eventuallyEq x.1 x.2.2
  have hc := ((centered_fiberLocal.germ he).eventuallyEq x.1 x.2.2).self_of_nhds
  have hi : MeanChartCompatibility.temporalAtIndex h n i (localize cutoff f) =ᶠ[nhds x]
      MeanChartCompatibility.temporalAtIndex h n i f := by
    rw [MeanChartCompatibility.temporalAtIndex_eq_native,
      MeanChartCompatibility.temporalAtIndex_eq_native]
    exact hd.mono fun y hy => congrArg (MeanChartCompatibility.commonRatio h n i * ·) hy
  have hsolve := MeanChartCompatibility.temporalAtIndex_fast_cancellation h n i hglobal
    (localize_periodic hsupport hp) x
  simpa only [MeanChartCompatibility.fastAtIndex, PressureStream.graphDz, hi.fderiv_eq, hc] using
      hsolve


-- @@ L2811-2811 verbatim
end LocalCommonClock


-- @@ L2813-2813 verbatim
section GaugeMeanBookkeeping


-- @@ L2815-2815 verbatim
open CorrectionState VariableGaugeMean


-- @@ L2817-2817 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L2819-2824 verbatim
/-- Gauge temporal pressure change, given by `(temporalStageState g h index axial c u).pressure
- u.pressure`. -/
noncomputable def gaugeTemporalPressureChange (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (temporalStageState g h index axial c u).pressure - u.pressure


-- @@ L2826-2830 verbatim
/-- Gauge rank pressure change, given by `(rankStageState g r axial c u).pressure - u.pressure`. -/
noncomputable def gaugeRankPressureChange (g : GaugeData S) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (rankStageState g r axial c u).pressure - u.pressure


-- @@ L2832-2837 verbatim
theorem gaugeTemporalStage_covariance (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (temporalStageState g h index axial c u).covariance = u.covariance := by
  simp only [temporalStageState, reconstructState, State.addIncrement, add_zero]
  rfl


-- @@ L2839-2844 verbatim
theorem gaugeRankStage_covariance (g : GaugeData S) (r : RankData S)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) :
    (rankStageState g r axial c u).covariance = u.covariance := by
  simp only [rankStageState, reconstructState, State.addIncrement, add_zero]
  rfl


-- @@ L2846-2859 verbatim
theorem gaugeTemporalStage_cumulative {s : StripData (PressureStream.Lift S)}
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (temporalIncrementState g h index axial c u))
    (hp : MeanClass s H (gaugeTemporalPressureChange g h index axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (temporalStageState g h index axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (temporalStageState g h index axial c u).pressure =
      u.pressure + gaugeTemporalPressureChange g h index axial c u := by
    unfold gaugeTemporalPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)


-- @@ L2861-2874 verbatim
theorem gaugeRankStage_cumulative {s : StripData (PressureStream.Lift S)}
    (g : GaugeData S) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H : ℝ}
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (rankIncrementState g r axial c u))
    (hp : MeanClass s H (gaugeRankPressureChange g r axial c u)) (hH : 9 / 10 ≤ H) :
    CorrectionState.CumulativeBounds s (rankStageState g r axial c u) := by
  refine ⟨cumulative_updated hu.velocity hi hH, ?_⟩
  have he : (rankStageState g r axial c u).pressure =
      u.pressure + gaugeRankPressureChange g r axial c u := by
    unfold gaugeRankPressureChange
    abel
  rw [he]
  exact hu.pressure.add (hp.mono_exponent hH)


-- @@ L2876-2876 verbatim
end GaugeMeanBookkeeping


-- @@ L2878-2878 verbatim
section GaugeTemporalResidual


-- @@ L2880-2880 verbatim
open CorrectionState VariableGaugeMean PhysicalMeanDomain


-- @@ L2882-2882 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L2884-2934 verbatim
/-- The actual gauge stream may differ from the desired axial inverse;
its entire fast derivative is retained as the named axial alias. -/
theorem gaugeTemporal_fastCancellation {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n))
    (n : ℕ) {x : PressureStream.Lift S} (hx : x ∈ U) :
    c.operators.fastTime (temporalIncrementState g h index axial c u).angular n x +
        (u.thetaResidual c n x - meanBar (u.thetaResidual c) n x) = 0 ∧
      c.operators.fastTime (temporalIncrementState g h index axial c u).axial n x +
        (u.axialResidual c n x - meanBar (u.axialResidual c) n x) =
          temporalAliasState g h index c u n (x, 0) 2 := by
  have hθf := temporalAtIndex_local_fast h n (index n) hV (hθ n) (hpθ n) (hUV x hx)
  have hzf := temporalAtIndex_local_fast h n (index n) hV (hz n) (hpz n) (hUV x hx)
  let desired : ScalarField (PressureStream.Lift S) := fun m =>
    MeanChartCompatibility.temporalAtIndex h m (index m) (u.axialResidual c m)
  have hdes : DifferentiableAt ℝ (desired n) x :=
    ((temporalAtIndex_local_smooth h n (index n) hV (hz n) (hpz n)).contDiffAt
      ((slowDomain_open hV).mem_nhds (hUV x hx))).differentiableAt (by simp)
  have hinc : DifferentiableAt ℝ ((temporalIncrementState g h index axial c u).axial n) x :=
    ((hi.axial n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt (temporalAxialDifference g h index c u n)
      (fderiv ℝ (desired n) x -
        fderiv ℝ ((temporalIncrementState g h index axial c u).axial n) x) x :=
    hdes.hasFDerivAt.sub hinc.hasFDerivAt
  have he : c.operators.fastTime (temporalAxialDifference g h index c u) n x =
      c.operators.fastTime desired n x -
        c.operators.fastTime (temporalIncrementState g h index axial c u).axial n x := by
    simp only [Operators.fastTime, hd.fderiv, _root_.sub_apply, mul_sub]
  constructor
  · rw [common_fastTime h index c hv hfast]
    change MeanChartCompatibility.fastAtIndex h n (index n)
      (MeanChartCompatibility.temporalAtIndex h n (index n) (u.thetaResidual c n)) x + _ = 0
    rw [hθf]
    simp only [TemporalMeanUpdate.centered, meanBar]
    ring
  · have hdesired : c.operators.fastTime desired n x =
        -(u.axialResidual c n x - meanBar (u.axialResidual c) n x) := by
      rw [common_fastTime h index c hv hfast]
      exact hzf
    change _ = -c.operators.fastTime (temporalAxialDifference g h index c u) n x
    rw [he, hdesired]
    ring


-- @@ L2936-2969 verbatim
theorem gaugeTemporalStage_theta_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n)) :
    Agree U ((temporalStageState g h index axial c u).thetaResidual c)
      (meanBar (u.thetaResidual c) + thetaRemainder c.operators c.base u.mean
        (temporalIncrementState g h index axial c u)) := by
  have he := thetaResidual_change hU c.operators hprofile hb hm hi u.covariance hW c.virtualTheta
  have hnew : (temporalStageState g h index axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base
        (updated u.mean (temporalIncrementState g h index axial c u)) u.covariance c.virtualTheta
            := by
    simp [State.thetaResidual, temporalStageState,
      reconstructState, State.addIncrement]
    rfl
  intro n x hx
  have hc := (gaugeTemporal_fastCancellation hU hV hUV g h index axial c u hv hfast
    hi hθ hz hpθ hpz n hx).1
  have he' := he n hx
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply] at he' ⊢
  change _ - u.thetaResidual c n x = _ at he'
  linarith


-- @@ L2971-3014 verbatim
theorem gaugeTemporalStage_axial_exact {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ U, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hi : SmoothTriple U (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hp : SmoothOn U u.pressure)
    (hnp : SmoothOn U (temporalStageState g h index axial c u).pressure)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n)) :
    Agree U (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
      temporalAliasState g h index c u n (x, 0) 2)
      (meanBar (u.axialResidual c) + axialRemainder c.operators c.base u.mean
        (temporalIncrementState g h index axial c u) (gaugeTemporalPressureChange g h index axial c
            u)) := by
  have he := axialResidual_change hU c.operators hprofile hb hm hi u.covariance hW u.pressure
    (gaugeTemporalPressureChange g h index axial c u) c.virtualAxial hp (hnp.sub hp)
  have hpressure : u.pressure + gaugeTemporalPressureChange g h index axial c u =
      (temporalStageState g h index axial c u).pressure := by
    unfold gaugeTemporalPressureChange
    abel
  have hnew : (temporalStageState g h index axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base
        (updated u.mean (temporalIncrementState g h index axial c u)) u.covariance
        (u.pressure + gaugeTemporalPressureChange g h index axial c u) c.virtualAxial := by
    rw [hpressure]
    simp [State.axialResidual, temporalStageState,
      reconstructState, State.addIncrement]
    rfl
  intro n x hx
  have hc := (gaugeTemporal_fastCancellation hU hV hUV g h index axial c u hv hfast
    hi hθ hz hpθ hpz n hx).2
  have he' := he n hx
  rw [hnew]
  simp only [Pi.add_apply, Pi.sub_apply] at he' ⊢
  change _ - u.axialResidual c n x = _ at he'
  linarith


-- @@ L3016-3016 verbatim
end GaugeTemporalResidual


-- @@ L3018-3018 verbatim
section GaugeTemporalGain


-- @@ L3020-3020 verbatim
open CorrectionState VariableGaugeMean PhysicalMeanDomain


-- @@ L3022-3022 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L3024-3063 verbatim
/-- The actual variable-gauge temporal update has the same differentiated
mean remainder as the fixed-gauge update. Its axial alias remains explicit. -/
theorem gaugeTemporalStage_mean_gain {s : StripData (PressureStream.Lift S)}
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ s.domain, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {H κ β : ℝ}
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (temporalIncrementState g h index axial c u))
    (hdp : MeanClass s H (gaugeTemporalPressureChange g h index axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hbarθ : MeanClass s β (meanBar (u.thetaResidual c)))
    (hbarz : MeanClass s β (meanBar (u.axialResidual c)))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((temporalStageState g h index axial c u).thetaResidual c) ∧
      MeanClass s β (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
        temporalAliasState g h index c u n (x, 0) 2) := by
  have hnp : SmoothOn s.domain (temporalStageState g h index axial c u).pressure := by
    have he : (temporalStageState g h index axial c u).pressure =
        u.pressure + gaugeTemporalPressureChange g h index axial c u := by
      unfold gaugeTemporalPressureChange
      abel
    rw [he]
    exact fun n => (hu.pressure.smooth n).add (hdp.smooth n)
  constructor
  · apply class_congr (hbarθ.add ((thetaRemainder_mem ho hb hu.velocity hi hH).mono_exponent hβ))
    exact gaugeTemporalStage_theta_exact s.isOpen_domain hV hUV g h index axial c u hv hfast
      (ho.radialProfile.smooth 0) hb.smooth hu.velocity.smooth hi.smooth hW hθ hz hpθ hpz
  · apply class_congr (hbarz.add ((axialRemainder_mem ho hb hu.velocity hi hH hdp).mono_exponent
      hβ))
    exact gaugeTemporalStage_axial_exact s.isOpen_domain hV hUV g h index axial c u hv hfast
      (ho.radialProfile.smooth 0) hb.smooth hu.velocity.smooth hi.smooth hW hu.pressure.smooth hnp
      hθ hz hpθ hpz


-- @@ L3065-3097 verbatim
theorem gaugeTemporalStage_next_mean {s : StripData (PressureStream.Lift S)}
    {V : Set S} (hV : IsOpen V) (hUV : ∀ x ∈ s.domain, x.2.1 ∈ V)
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s (ExponentLedger.meanUpdateExponent σ κ)
      (temporalIncrementState g h index axial c u))
    (hdp : MeanClass s (ExponentLedger.meanUpdateExponent σ κ)
      (gaugeTemporalPressureChange g h index axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hbarθ : MeanClass s (ExponentLedger.meanExponent σ + 17 / 100) (meanBar (u.thetaResidual c)))
    (hbarz : MeanClass s (ExponentLedger.meanExponent σ + 17 / 100) (meanBar (u.axialResidual c)))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (slowDomain V))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (slowDomain V))
    (hpθ : ∀ n, PeriodicOn V (u.thetaResidual c n))
    (hpz : ∀ n, PeriodicOn V (u.axialResidual c n)) :
    MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10))
        ((temporalStageState g h index axial c u).thetaResidual c) ∧
      MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10))
        (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
          temporalAliasState g h index c u n (x, 0) 2) := by
  apply gaugeTemporalStage_mean_gain hV hUV g h index axial c u hv hfast ho hb hu hi hdp hW
    (hbarθ.mono_exponent (by unfold ExponentLedger.meanExponent; linarith))
    (hbarz.mono_exponent (by unfold ExponentLedger.meanExponent; linarith))
    hθ hz hpθ hpz
  · exact (ExponentLedger.mean_increment_above_cumulative_mean hσ hκ).le
  · simp only [ExponentLedger.meanUpdateExponent, ExponentLedger.meanExponent]
    linarith


-- @@ L3099-3099 verbatim
end GaugeTemporalGain


-- @@ L3101-3101 verbatim
section GaugeAliasBookkeeping


-- @@ L3103-3103 verbatim
open CorrectionState VariableGaugeMean


-- @@ L3105-3105 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L3107-3112 verbatim
/-- Gauge refresh pressure alias as an element of `State (PressureStream.Lift S)`. -/
noncomputable def gaugeRefreshPressureAlias (g : GaugeData S)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  { current with errors := { current.errors with aliasError :=
      current.errors.aliasError + (pressureAliasState g c current - pressureAliasState g c old) } }


-- @@ L3114-3121 verbatim
theorem gaugeRefreshPressureAlias_separated (g : GaugeData S)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S))
    (other : Oscillation (PressureStream.Lift S))
    (he : current.errors.aliasError = other + pressureAliasState g c old) :
    (gaugeRefreshPressureAlias g c old current).errors.aliasError =
      other + pressureAliasState g c current := by
  simp only [gaugeRefreshPressureAlias, he]
  abel


-- @@ L3123-3125 verbatim
theorem gaugeRefreshPressureAlias_fullResidual (g : GaugeData S)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    fullResidual c (gaugeRefreshPressureAlias g c old current) = fullResidual c current := rfl


-- @@ L3127-3134 verbatim
theorem gaugeRefreshPressureAlias_fullGoodResidual (g : GaugeData S)
    (c : Context (PressureStream.Lift S)) (old current : State (PressureStream.Lift S)) :
    fullGoodResidual c (gaugeRefreshPressureAlias g c old current) = fullGoodResidual c current -
      (pressureAliasState g c current - pressureAliasState g c old) := by
  unfold fullGoodResidual
  rw [gaugeRefreshPressureAlias_fullResidual]
  simp only [gaugeRefreshPressureAlias, ExcludedErrors.total]
  abel


-- @@ L3136-3142 verbatim
/-- Gauge pressure alias block, given by `ErrorHarmonics.zeroBlock b.frequency b.phase
b.angularFrequency (fun n x => pressureAliasState g c u n (x, 0))`. -/
noncomputable def gaugePressureAliasBlock (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (b : HarmonicBlock (PressureStream.Lift S)) :
    HarmonicBlock (PressureStream.Lift S) :=
  ErrorHarmonics.zeroBlock b.frequency b.phase b.angularFrequency
    (fun n x => pressureAliasState g c u n (x, 0))


-- @@ L3144-3150 verbatim
/-- Gauge temporal alias block, given by `ErrorHarmonics.zeroBlock b.frequency b.phase
b.angularFrequency (fun n x => temporalAliasState g h index c u n (x, 0))`. -/
noncomputable def gaugeTemporalAliasBlock (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (b : HarmonicBlock (PressureStream.Lift S)) : HarmonicBlock (PressureStream.Lift S) :=
  ErrorHarmonics.zeroBlock b.frequency b.phase b.angularFrequency
    (fun n x => temporalAliasState g h index c u n (x, 0))


-- @@ L3152-3157 verbatim
theorem gaugePressureAliasBlock_represents (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (b : HarmonicBlock (PressureStream.Lift S)) :
    (gaugePressureAliasBlock g c u b).oscillation = pressureAliasState g c u := by
  funext n x i
  rw [gaugePressureAliasBlock, ErrorHarmonics.zeroBlock_evaluation]
  rfl


-- @@ L3159-3165 verbatim
theorem gaugeTemporalAliasBlock_represents (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (b : HarmonicBlock (PressureStream.Lift S)) :
    (gaugeTemporalAliasBlock g h index c u b).oscillation = temporalAliasState g h index c u := by
  funext n x i
  rw [gaugeTemporalAliasBlock, ErrorHarmonics.zeroBlock_evaluation]
  rfl


-- @@ L3167-3169 verbatim
theorem gaugePressureAliasBlock_band (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (b : HarmonicBlock (PressureStream.Lift S)) :
    (gaugePressureAliasBlock g c u b).BandLimited 0 := ErrorHarmonics.zeroBlock_band _ _ _ _


-- @@ L3171-3174 verbatim
theorem gaugeTemporalAliasBlock_band (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (b : HarmonicBlock (PressureStream.Lift S)) :
    (gaugeTemporalAliasBlock g h index c u b).BandLimited 0 := ErrorHarmonics.zeroBlock_band _ _ _ _


-- @@ L3176-3176 verbatim
end GaugeAliasBookkeeping


-- @@ L3178-3178 verbatim
section PhysicalResidualDecomposition


-- @@ L3180-3180 verbatim
open CorrectionState PhysicalResidualBridge ProblemStatement Filter

-- @@ L3181-3181 verbatim
open scoped Topology


-- @@ L3183-3225 verbatim
/-- The coefficient/mean/error decomposition is a decomposition of the
actual viscosity-one Cartesian residual after the proved graph scaling. -/
theorem physicalResidual_decomposition {ι : Type*} {Q : ℝ} (hQ : 0 < Q)
    (h : ℝ) (k n : ℕ) (c : Context Lift) (s : State Lift)
    (hop : MatchesAt c.operators (commonGraph Q h k) n)
    {V : Set Lift} (hmean : LiftedMeanResidual.MeanHypotheses V c s)
    {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock Lift}
    {gaussian aliasError : ι → HarmonicResidual.BlockCoefficients Lift}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasError s)
    (hregular : HarmonicResidual.ExtractionRegular V c s labels blocks gaussian aliasError n)
    (hR : ∀ x ∈ HarmonicResidual.liftDomain V, x.1.1 ≠ 0)
    {p₀ : Cylinder → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun x => baseComponents c n x i) (HarmonicResidual.liftDomain V))
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => incrementComponents s n x i) (HarmonicResidual.liftDomain
        V))
    (hp₀ : ContDiffOn ℝ ∞ p₀ (HarmonicResidual.liftDomain V))
    (hp : ContDiffOn ℝ ∞ (s.totalPressureIncrement n) (HarmonicResidual.liftDomain V))
    {t : ℝ} {q : Space}
    (hz : (t, q) ∈ (commonGraph Q h k).source (HarmonicResidual.liftDomain V))
    (hbase : ∀ i, graphResidual (Q ^ h) ScaledGraph.radius (commonGraph Q h k).radial
      ScaledGraph.angular (commonGraph Q h k).axial (commonGraph Q h k).temporal
      (baseComponents c n) p₀ ((commonGraph Q h k).map (t, q)) i =
        LiftedMeanResidual.virtualDivergence c n ((commonGraph Q h k).map (t, q)) i +
          s.errors.base n ((commonGraph Q h k).map (t, q)) i)
    {u : VelocityField} {P : PressureField}
    (hu : ContDiffAt ℝ 2 u (t, CylindricalResidual.chart q))
    (hP : DifferentiableAt ℝ P (t, CylindricalResidual.chart q))
    (huRep : (fun z : SpaceTime => u (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) ((commonGraph Q h k).velocity
        (fun y j => baseComponents c n y j + incrementComponents s n y j) z)))
    (hpRep : CylindricalResidual.pressurePullback P =ᶠ[𝓝 (t, q)] (commonGraph Q h k).pressure
      (fun y => p₀ y + s.totalPressureIncrement n y)) (i : Fin 3) :
    Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
        CylindricalResidual.frame (-(q 1))
          (navierStokesResidual u P t (CylindricalResidual.chart q)) i =
      (∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c s (blocks l) (gaussian l) (aliasError l)).oscillation
          n ((commonGraph Q h k).map (t, q)) i) +
      s.meanGoodResidual c n ((commonGraph Q h k).map (t, q)).1 i +
      s.errors.total n ((commonGraph Q h k).map (t, q)) i := by
  have he := context_fullResidual_physical hQ h k n c s hop
    (HarmonicResidual.liftDomain_open hmean.isOpen) hR hB ha hp₀ hp hz hbase hu hP huRep hpRep i
  exact he.symm.trans (fullResidual_reconstructed_with_mean hrep hmean hregular hz.2 i)


-- @@ L3227-3227 verbatim
end PhysicalResidualDecomposition


-- @@ L3229-3229 verbatim
section SourceCoefficientCompatibility


-- @@ L3231-3231 verbatim
open CorrectionState HarmonicFields MeasureTheory


-- @@ L3233-3236 verbatim
theorem angularMean_const_mul (a : ℂ) (f : ℝ → ℂ) :
    angularMean (fun θ => a * f θ) = a * angularMean f := by
  simp only [angularMean, intervalIntegral.integral_const_mul]
  ring


-- @@ L3238-3276 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Equality of actual real block fields, together with the literal
carrier transformation, determines the transformed source coefficients.
Conjugacy is used explicitly to recover the full complex field. -/
theorem block_velocity_pullback_at (a b : HarmonicBlock D) (n m : ℕ)
    (φ : D → D) (scale : ℝ) (x : D) (i : Fin 3) (j : ℤ)
    (ha : ConjugateSymmetric (a.velocity n i)) (hb : ConjugateSymmetric (b.velocity m i))
    (hkp : a.angularFrequency n = b.angularFrequency m)
    (hkn : a.angularFrequency n ≠ 0)
    (hphase : a.frequency n * a.phase n x = b.frequency m * b.phase m (φ x))
    (hfield : ∀ θ : ℝ, a.oscillation n (x, θ) i = scale * b.oscillation m (φ x, θ) i) :
    a.velocity n i j x = (scale : ℂ) * b.velocity m i j (φ x) := by
  have hkb : b.angularFrequency m ≠ 0 := by rw [← hkp]; exact hkn
  have hf θ : field (a.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ) =
      (scale : ℂ) * field (b.velocity m i) (b.frequency m) (b.phase m) (b.angularFrequency m) (φ x,
          θ) := by
    rw [← field_real ha, ← field_real hb]
    change (a.oscillation n (x, θ) i : ℂ) = (scale : ℂ) * (b.oscillation m (φ x, θ) i : ℂ)
    rw [hfield]
    exact Complex.ofReal_mul _ _
  have hcarrier θ : field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ)))
      (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ) =
      field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ)))
        (b.frequency m) (b.phase m) (b.angularFrequency m) (φ x, θ) := by
    simp only [field, evaluate_single, hphase, hkp]
  rw [← HarmonicResidual.extract_field (a.velocity n i) (a.frequency n) (a.phase n) hkn j x,
    ← HarmonicResidual.extract_field (b.velocity m i) (b.frequency m) (b.phase m) hkb j (φ x)]
  unfold HarmonicResidual.extract
  have he : (fun θ => field (a.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x,
      θ) *
      field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ))) (a.frequency n) (a.phase n)
          (a.angularFrequency n) (x, θ)) =
      fun θ => (scale : ℂ) *
        (field (b.velocity m i) (b.frequency m) (b.phase m) (b.angularFrequency m) (φ x, θ) *
          field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ)))
            (b.frequency m) (b.phase m) (b.angularFrequency m) (φ x, θ)) := by
    funext θ
    rw [hf θ, hcarrier θ, mul_assoc]
  rw [he, angularMean_const_mul]


-- @@ L3278-3278 verbatim
end SourceCoefficientCompatibility


-- @@ L3280-3280 verbatim
section AssembledSignedTensor


-- @@ L3282-3282 verbatim
open CorrectionState


-- @@ L3284-3284 verbatim
variable {ι : Type}


-- @@ L3286-3334 verbatim
/-- Uniform label bounds and the proved slot overlap bound control the
actual state covariance after adding every signed tangent and curl. -/
theorem assembledSigned_stateTensor_mem {s : StripData D} {P : ι → ℕ → D → ℝ}
    {α δ β η γ : ℝ} (f : LabelSumBounds.SignedFamily s P α δ β η)
    (hβη : β ≤ η) (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β)
    {d h : ℝ} {vr vt : TorusInverse.Plane} {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → LabelSumBounds.WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (hp : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (f.primary
        l).oscillation))
    (ho : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (f.old
        l).oscillation))
    (ht : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (f.tangent
        l).oscillation))
    (hc : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (f.curl
        l).oscillation))
    (u : State D) (hu : u.oscillation = LabelSumBounds.fieldSum labels (fun l => (f.old
        l).oscillation))
    (m : Triple D) (p : ScalarField D) (q : OscillatoryScalar D) (e : ExcludedErrors D) :
    let primary := LabelSumBounds.fieldSum labels (fun l => (f.primary l).oscillation)
    let tangent := LabelSumBounds.fieldSum labels (fun l => (f.tangent l).oscillation)
    let curl := LabelSumBounds.fieldSum labels (fun l => (f.curl l).oscillation)
    TensorClass s γ ((u.addIncrement m p (tangent + curl) q e).covariance - u.covariance -
      symmetricCovariance primary tangent) := by
  let primary := LabelSumBounds.fieldSum labels (fun l => (f.primary l).oscillation)
  let old := LabelSumBounds.fieldSum labels (fun l => (f.old l).oscillation)
  let tangent := LabelSumBounds.fieldSum labels (fun l => (f.tangent l).oscillation)
  let curl := LabelSumBounds.fieldSum labels (fun l => (f.curl l).oscillation)
  have hcont (a : ι → HarmonicBlock D) :
      AngularContinuous (LabelSumBounds.fieldSum labels (fun l => (a l).oscillation)) :=
    LabelSumBounds.fieldSum_angularContinuous labels _ (fun l =>
        LabelSumBounds.block_angularContinuous (a l))
  have hucont : AngularContinuous u.oscillation := by rw [hu]; exact hcont f.old
  have he : (u.addIncrement m p (tangent + curl) q e).covariance - u.covariance -
      symmetricCovariance primary tangent = signedTensorRemainder primary old tangent curl := by
    rw [covariance_actual_update u m p (tangent + curl) q e hucont ((hcont f.tangent).add (hcont
        f.curl))]
    unfold signedTensorRemainder
    rw [hu]
    change u.covariance + covarianceIncrement old (tangent + curl) - u.covariance - _ = _
    abel
  change TensorClass s γ ((u.addIncrement m p (tangent + curl) q e).covariance - u.covariance -
    symmetricCovariance primary tangent)
  rw [he]
  exact fun i j => f.remainder_sum_mem hβη hγd hγc hγs labels label hinj hlevel χ hχ Y hp ho ht hc
      i j


-- @@ L3336-3336 verbatim
end AssembledSignedTensor


-- @@ L3338-3338 verbatim
section WaveStageGain


-- @@ L3340-3340 verbatim
open CorrectionState


-- @@ L3342-3393 verbatim
/-- The only linear input is a bound on the literal old residual plus
the literal linear increment after its Gaussian subtraction. All nonlinear
terms of the actual new residual are derived by the harmonic calculus. -/
theorem waveStage_residual_mem {s : StripData D} {P : ℕ → D → ℝ} {κ α β H γ : ℝ}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1 / 2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (hmean : v.mean = u.mean)
    (hm : IncrementBounds s H u.mean)
    (hbase : SmoothTriple s.domain c.base)
    (a b : HarmonicBlock D) {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : HarmonicWaveInteraction.ZeroMode a) (hb0 : HarmonicWaveInteraction.ZeroMode b)
    (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hda : HarmonicWaveInteraction.ModeSolenoidal s c a)
    (hdb : HarmonicWaveInteraction.ModeSolenoidal s c (HarmonicWaveInteraction.withCarrier a b))
    (hNormal : ∀ i, UnweightedClass s 0
      (fun n x => HarmonicMeanInteraction.slowNormal c ho hR a.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) a.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (a.angularFrequency n : ℝ)))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (hpa : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (a.pressure n))
    (hpb : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (b.pressure n))
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A₁ n i - A₀ n i) 0)
    (hlinear : ∀ i j, j ≠ 0 → WaveClass s P γ (fun n x =>
      (HarmonicResidual.residualBlock c u a G A₀).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c a b g).velocity n i j x))
    (hγm : γ ≤ β + H - 1 / 2) (hγc : γ ≤ α + β - κ) (hγs : γ ≤ β + β - κ) :
    (HarmonicResidual.residualBlock c v (HarmonicWaveInteraction.addBlock a b) (G + g)
        A₁).WaveBounds
      s P γ := by
  have hnon := HarmonicWaveInteraction.interactionBlock_class c ho hκ hR hm ha hb ha0 hb0 hM hN
    hΦ hk hda hdb hNormal hFreq hAng hP0 hP1
  have hca := block_waveBounds_all a ha ha0 hP0
  have hcb := block_waveBounds_all b hb hb0 hP0
  intro i j hj
  apply WaveInteractionBounds.class_congr
    ((hlinear i j hj).add ((hnon i j hj).mono_exponent (le_min hγm (le_min hγc hγs))))
  intro n x hx
  have hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
    contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)
  have he := HarmonicWaveInteraction.residualBlock_wave_update_split s.isOpen_domain c u v hmean
    a b G g A₀ A₁ hA n hr
    contDiffOn_const (hΦ n) (hkp n)
    (fun l => (HarmonicMeanInteraction.tripleField_smooth hbase n l))
    (fun l => (HarmonicMeanInteraction.tripleField_smooth hm.smooth n l))
    (fun l k => (hca l k).smooth n) (fun l k => (hcb l k).smooth n) (hpa n) (hpb n) hx j i
  change _ = _ at he
  linear_combination -he


-- @@ L3395-3395 verbatim
end WaveStageGain


-- @@ L3397-3397 verbatim
section WaveMeanResidual


-- @@ L3399-3399 verbatim
open CorrectionState VariableGaugeMean


-- @@ L3401-3402 verbatim
/-- Zero triple, given by `⟨0, 0, 0⟩`. -/
noncomputable def zeroTriple : Triple D := ⟨0, 0, 0⟩


-- @@ L3404-3406 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem updated_zeroTriple (m : Triple D) : updated m zeroTriple = m := by
  apply triple_ext <;> simp only [updated, zeroTriple, add_zero]


-- @@ L3408-3408 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L3410-3416 verbatim
/-- Insert the actual oscillation and its actual excluded error, then
reconstruct pressure from the resulting literal covariance. -/
noncomputable def gaugeWaveStage (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  reconstructState g c (u.addIncrement zeroTriple 0 w q e)


-- @@ L3418-3422 verbatim
/-- Gauge wave pressure change, given by `(gaugeWaveStage g c u w q e).pressure - u.pressure`. -/
noncomputable def gaugeWavePressureChange (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) := (gaugeWaveStage g c u w q e).pressure - u.pressure


-- @@ L3424-3427 verbatim
theorem gaugeWaveStage_mean (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    (gaugeWaveStage g c u w q e).mean = u.mean := updated_zeroTriple u.mean


-- @@ L3429-3434 verbatim
theorem gaugeWaveStage_covariance (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hu : AngularContinuous u.oscillation) (hw : AngularContinuous w) :
    (gaugeWaveStage g c u w q e).covariance = u.covariance + covarianceIncrement u.oscillation w :=
  covariance_add hu hw


-- @@ L3436-3450 verbatim
theorem gaugeWaveStage_theta_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hu : AngularContinuous u.oscillation) (hw : AngularContinuous w)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j)) :
    Agree U ((gaugeWaveStage g c u w q e).thetaResidual c - u.thetaResidual c)
      (thetaCovarianceChange c.operators (covarianceIncrement u.oscillation w)) := by
  change Agree U (MeanIncrementBounds.thetaResidual c.operators c.base
    (gaugeWaveStage g c u w q e).mean (gaugeWaveStage g c u w q e).covariance c.virtualTheta - _ ) _
  rw [gaugeWaveStage_mean, gaugeWaveStage_covariance g c u w q e hu hw]
  exact thetaResidual_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX c.virtualTheta


-- @@ L3452-3466 verbatim
theorem gaugeWaveStage_gr_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hu : AngularContinuous u.oscillation) (hw : AngularContinuous w)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j)) :
    Agree U ((gaugeWaveStage g c u w q e).gr c - u.gr c)
      (radialCovarianceChange c.operators (covarianceIncrement u.oscillation w)) := by
  change Agree U (MeanIncrementBounds.gr c.operators c.base
    (gaugeWaveStage g c u w q e).mean (gaugeWaveStage g c u w q e).covariance - _) _
  rw [gaugeWaveStage_mean, gaugeWaveStage_covariance g c u w q e hu hw]
  exact gr_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX


-- @@ L3468-3479 verbatim
theorem axialResidual_pressure_change {U : Set D} (hU : IsOpen U) (o : Operators D)
    {b m : Triple D} (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (W : Tensor D) (hW : ∀ i j, SmoothOn U (W i j))
    (p q T : ScalarField D) (hp : SmoothOn U p) (hq : SmoothOn U q) :
    Agree U (MeanIncrementBounds.axialResidual o b m W (p + q) T -
      MeanIncrementBounds.axialResidual o b m W p T) (o.dz q) := by
  have he : axialAxial b m + W 2 2 + (p + q) = (axialAxial b m + W 2 2 + p) + q := by abel
  intro n x hx
  simp only [MeanIncrementBounds.axialResidual, Pi.sub_apply, Pi.add_apply]
  rw [he, o.dz_add hU (((hb.axialAxial hm).add (hW 2 2)).add hp) hq n hx]
  simp only [Pi.add_apply]
  ring


-- @@ L3481-3510 verbatim
theorem gaugeWaveStage_axial_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hu : AngularContinuous u.oscillation) (hw : AngularContinuous w)
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j))
    (hp : SmoothOn U u.pressure) (hδp : SmoothOn U (gaugeWavePressureChange g c u w q e)) :
    Agree U ((gaugeWaveStage g c u w q e).axialResidual c - u.axialResidual c)
      (axialCovarianceChange c.operators (covarianceIncrement u.oscillation w) +
        c.operators.dz (gaugeWavePressureChange g c u w q e)) := by
  have hpressure : (gaugeWaveStage g c u w q e).pressure =
      u.pressure + gaugeWavePressureChange g c u w q e := by unfold gaugeWavePressureChange; abel
  have hc := axialResidual_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX
    (u.pressure + gaugeWavePressureChange g c u w q e) c.virtualAxial (hp.add hδp)
  have hd := axialResidual_pressure_change hU c.operators hb hm u.covariance hW
    u.pressure (gaugeWavePressureChange g c u w q e) c.virtualAxial hp hδp
  intro n x hx
  have hc' := hc n hx
  have hd' := hd n hx
  change MeanIncrementBounds.axialResidual c.operators c.base (gaugeWaveStage g c u w q e).mean
    (gaugeWaveStage g c u w q e).covariance (gaugeWaveStage g c u w q e).pressure c.virtualAxial n
        x - _ = _
  rw [gaugeWaveStage_mean, gaugeWaveStage_covariance g c u w q e hu hw, hpressure]
  simp only [Pi.add_apply, Pi.sub_apply] at hc' hd' ⊢
  change _ - MeanIncrementBounds.axialResidual c.operators c.base u.mean u.covariance
    u.pressure c.virtualAxial n x = _
  linarith


-- @@ L3512-3536 verbatim
theorem gaugeWaveStage_mean_changes_mem {s : StripData (PressureStream.Lift S)} {α κ : ℝ}
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hu : AngularContinuous u.oscillation) (hw : AngularContinuous w)
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hm : CorrectionState.CumulativeBounds s u)
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (hX : TensorClass s α (covarianceIncrement u.oscillation w))
    (hδp : MeanClass s (α - κ) (gaugeWavePressureChange g c u w q e)) :
    MeanClass s (α - κ) ((gaugeWaveStage g c u w q e).thetaResidual c - u.thetaResidual c) ∧
      MeanClass s (α - κ) ((gaugeWaveStage g c u w q e).axialResidual c - u.axialResidual c) ∧
      MeanClass s (α - κ) ((gaugeWaveStage g c u w q e).gr c - u.gr c) := by
  have hXs := fun i j => (hX i j).smooth
  refine ⟨?_, ?_, ?_⟩
  · apply class_congr (thetaCovarianceChange_mem ho hX)
    exact gaugeWaveStage_theta_change s.isOpen_domain g c u w q e hu hw
      hb.smooth hm.velocity.smooth hW hXs
  · apply class_congr ((axialCovarianceChange_mem ho hX).add
      ((ho.dz hδp).mono_exponent (by linarith)))
    exact gaugeWaveStage_axial_change s.isOpen_domain g c u w q e hu hw
      hb.smooth hm.velocity.smooth hW hXs hm.pressure.smooth hδp.smooth
  · apply class_congr (radialCovarianceChange_mem ho hX)
    exact gaugeWaveStage_gr_change s.isOpen_domain g c u w q e hu hw
      hb.smooth hm.velocity.smooth hW hXs


-- @@ L3538-3551 verbatim
theorem gaugeWaveStage_cumulative {s : StripData (PressureStream.Lift S)} {α : ℝ}
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hm : CorrectionState.CumulativeBounds s u)
    (hδp : MeanClass s α (gaugeWavePressureChange g c u w q e)) (hα : 9 / 10 ≤ α) :
    CorrectionState.CumulativeBounds s (gaugeWaveStage g c u w q e) := by
  constructor
  · rw [gaugeWaveStage_mean]
    exact hm.velocity
  · have he : (gaugeWaveStage g c u w q e).pressure =
        u.pressure + gaugeWavePressureChange g c u w q e := by unfold gaugeWavePressureChange; abel
    rw [he]
    exact hm.pressure.add (hδp.mono_exponent hα)


-- @@ L3553-3553 verbatim
end WaveMeanResidual


-- @@ L3555-3555 verbatim
section SignedParameters


-- @@ L3557-3557 verbatim
open CorrectionState


-- @@ L3559-3584 verbatim
/-- Fixed primitive data of one primary signed slot. No output field,
output estimate, or state transition is stored in this record. -/
structure SignedParameters (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  /-- Base wave coefficients for the signed correction step. -/
  base : LinearWaveBounds.WaveCoefficients (D × ℝ)
  /-- Directions of `SignedParameters`, of type `LinearWaveBounds.GraphDirections (D × ℝ)`. -/
  directions : LinearWaveBounds.GraphDirections (D × ℝ)
  /-- Matrix of `SignedParameters`, of type `ℕ → D × ℝ → SignedWaveUpdate.Mat2`. -/
  matrix : ℕ → D × ℝ → SignedWaveUpdate.Mat2
  /-- Target of `SignedParameters`, of type `ℕ → D × ℝ → SignedWaveUpdate.Vec2`. -/
  target : ℕ → D × ℝ → SignedWaveUpdate.Vec2
  /-- Mask of `SignedParameters`, of type `ℕ → D × ℝ → ℝ`. -/
  mask : ℕ → D × ℝ → ℝ
  /-- Fundamental of `SignedParameters`, of type `ℕ → D × ℝ → ProblemStatement.Space`. -/
  fundamental : ℕ → D × ℝ → ProblemStatement.Space
  /-- Normal motion of `SignedParameters`, of type `ℕ → D × ℝ → ProblemStatement.Space`. -/
  normalMotion : ℕ → D × ℝ → ProblemStatement.Space
  /-- Action of `SignedParameters`, of type `ℕ → D × ℝ → ProblemStatement.Space →L[ℝ]
  ProblemStatement.Space`. -/
  action : ℕ → D × ℝ → ProblemStatement.Space →L[ℝ] ProblemStatement.Space
  /-- Cutoff of `SignedParameters`, of type `ℕ → D × ℝ → ℝ`. -/
  cutoff : ℕ → D × ℝ → ℝ
  /-- Angular frequency of `SignedParameters`, of type `ℕ → ℤ`. -/
  angularFrequency : ℕ → ℤ
  /-- Column of `SignedParameters`, of type `Fin 2`. -/
  column : Fin 2


-- @@ L3586-3590 verbatim
/-- Coefficients, constructed using `SignedWaveUpdate.coefficients`. -/
noncomputable def SignedParameters.coefficients (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
  SignedWaveUpdate.coefficients p.base (HarmonicWaveInteraction.productStrip s) p.directions
    p.matrix p.target request p.mask p.fundamental p.normalMotion p.action p.column


-- @@ L3592-3598 verbatim
/-- Exact block, constructed using `SignedWaveUpdate.blockOfCoefficients`. -/
noncomputable def SignedParameters.exactBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients
    ((p.coefficients s request).corrected (HarmonicWaveInteraction.productStrip s) p.directions
        p.cutoff)
    p.angularFrequency


-- @@ L3600-3605 verbatim
/-- Tangent block, given by `SignedWaveUpdate.blockOfCoefficients ((p.coefficients s
request).withCutoff p.cutoff) p.angularFrequency`. -/
noncomputable def SignedParameters.tangentBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients ((p.coefficients s request).withCutoff p.cutoff)
      p.angularFrequency


-- @@ L3607-3610 verbatim
/-- Curl block, given by `subBlock (p.exactBlock s request) (p.tangentBlock s request)`. -/
noncomputable def SignedParameters.curlBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  subBlock (p.exactBlock s request) (p.tangentBlock s request)


-- @@ L3612-3617 verbatim
theorem SignedParameters.exactBlock_split (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).oscillation =
      (p.tangentBlock s request).oscillation + (p.curlBlock s request).oscillation :=
  correctedBlock_split (p.coefficients s request) (HarmonicWaveInteraction.productStrip s)
    p.directions p.cutoff p.angularFrequency


-- @@ L3619-3622 verbatim
theorem sectionStrip_productStrip (s : StripData D) :
    SignedWaveUpdate.sectionStrip (HarmonicWaveInteraction.productStrip s) = s := by
  cases s
  rfl


-- @@ L3624-3626 verbatim
theorem SignedParameters.exactBlock_band (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : (p.exactBlock s request).BandLimited 1 :=
  SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


-- @@ L3628-3630 verbatim
theorem SignedParameters.tangentBlock_band (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : (p.tangentBlock s request).BandLimited 1 :=
  SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


-- @@ L3632-3634 verbatim
theorem SignedParameters.curlBlock_band (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : (p.curlBlock s request).BandLimited 1 :=
  subBlock_band (p.exactBlock_band s request) (p.tangentBlock_band s request)


-- @@ L3636-3639 verbatim
theorem SignedParameters.exactBlock_zero (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    ∀ n i, (p.exactBlock s request).velocity n i 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1


-- @@ L3641-3644 verbatim
theorem SignedParameters.tangentBlock_zero (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    ∀ n i, (p.tangentBlock s request).velocity n i 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1


-- @@ L3646-3681 verbatim
/-- Every output bound here is derived from the same explicit signed
quotient and curl, on the exact product strip used by the current state. -/
theorem SignedParameters.block_bounds (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ B κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s) P₀ α₀ κ
      p.directions p.base) (hκ : κ ≤ 1 / 2)
    (hcov : SignedWaveUpdate.CovarianceControl (HarmonicWaveInteraction.productStrip s) p.matrix
        p.target)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i))
    (hm : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.mask)
    (hv : MemClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) 0 p.fundamental)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain
        (HarmonicWaveInteraction.productStrip s))
      (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions))
    (hNdot : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.normalMotion)
    (hA : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.action)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
      b ≤ ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖)
    (hhi : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
      ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ≤ M)
    (hK : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2) (fun n => 1 / p.base.frequency
        n))
    {radius : D × ℝ → ℝ} (hradius : p.base.radius = fun _ => radius)
    (hψ : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.cutoff) :
    (p.tangentBlock s request).WaveBounds s P (B - κ) ∧
      (p.exactBlock s request).WaveBounds s P (B - κ) ∧
      (p.exactBlock s request).PressureBounds s P (B + 1 / 2 - κ) ∧
      (p.curlBlock s request).WaveBounds s P (B + 1 / 2 - 2 * κ) := by
  have he := constructedSignedBlock_bounds hbase hκ hcov hR hm hv hN hNdot hA hb hlo hhi hK
    hradius hψ p.angularFrequency p.column
  simpa only [SignedParameters.tangentBlock, SignedParameters.exactBlock,
      SignedParameters.curlBlock,
    SignedParameters.coefficients, sectionStrip_productStrip] using he


-- @@ L3683-3716 verbatim
/-- Control data, collecting `baseBounds`, `kappa_le_half`, `covariance`, `mask`, `fundamental`,
`normal` and their compatibility conditions. -/
structure SignedParameters.Control (p : SignedParameters D) (s : StripData D)
    (P₀ : ℕ → D × ℝ → ℝ) (P : ℕ → D → ℝ) (α₀ κ : ℝ) where
  baseBounds : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s) P₀ α₀ κ
    p.directions p.base
  kappa_le_half : κ ≤ 1 / 2
  /-- Covariance of `Control`, of type `SignedWaveUpdate.CovarianceControl
  (HarmonicWaveInteraction.productStrip s) p.matrix p.target`. -/
  covariance : SignedWaveUpdate.CovarianceControl (HarmonicWaveInteraction.productStrip s) p.matrix
      p.target
  mask : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.mask
  fundamental : MemClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) 0
      p.fundamental
  normal : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain
      (HarmonicWaveInteraction.productStrip s))
    (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions)
  normalMotion : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.normalMotion
  action : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.action
  /-- Lower of `Control`, of type `ℝ`. -/
  lower : ℝ
  /-- Upper of `Control`, of type `ℝ`. -/
  upper : ℝ
  lower_pos : 0 < lower
  norm_lower : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    lower ≤ ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖
  norm_upper : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ≤ upper
  inverseFrequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / p.base.frequency n)
  /-- Radius of `Control`, of type `D × ℝ → ℝ`. -/
  radius : D × ℝ → ℝ
  radius_eq : p.base.radius = fun _ => radius
  cutoff : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.cutoff


-- @@ L3718-3729 verbatim
theorem SignedParameters.Control.bounds {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    (h : p.Control s P₀ P α₀ κ) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) :
    (p.tangentBlock s request).WaveBounds s P (B - κ) ∧
      (p.exactBlock s request).WaveBounds s P (B - κ) ∧
      (p.exactBlock s request).PressureBounds s P (B + 1 / 2 - κ) ∧
      (p.curlBlock s request).WaveBounds s P (B + 1 / 2 - 2 * κ) :=
  p.block_bounds s request h.baseBounds h.kappa_le_half h.covariance hR h.mask h.fundamental
    h.normal h.normalMotion h.action h.lower_pos h.norm_lower h.norm_upper h.inverseFrequency
    h.radius_eq h.cutoff


-- @@ L3731-3731 verbatim
end SignedParameters


-- @@ L3733-3733 verbatim
section ActualSignedStage


-- @@ L3735-3735 verbatim
open CorrectionState


-- @@ L3737-3743 verbatim
/-- State signed block, given by `p.exactBlock s (LocalSignedRequest.fullRequest s patch coord c
u)`. -/
noncomputable def stateSignedBlock (p : SignedParameters LocalSignedRequest.Point)
    (s : StripData LocalSignedRequest.Point) (patch : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point) :
    HarmonicBlock LocalSignedRequest.Point :=
  p.exactBlock s (LocalSignedRequest.fullRequest s patch coord c u)


-- @@ L3745-3751 verbatim
/-- State signed tangent, given by `p.tangentBlock s (LocalSignedRequest.fullRequest s patch
coord c u)`. -/
noncomputable def stateSignedTangent (p : SignedParameters LocalSignedRequest.Point)
    (s : StripData LocalSignedRequest.Point) (patch : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point) :
    HarmonicBlock LocalSignedRequest.Point :=
  p.tangentBlock s (LocalSignedRequest.fullRequest s patch coord c u)


-- @@ L3753-3759 verbatim
/-- State signed curl, given by `p.curlBlock s (LocalSignedRequest.fullRequest s patch coord c
u)`. -/
noncomputable def stateSignedCurl (p : SignedParameters LocalSignedRequest.Point)
    (s : StripData LocalSignedRequest.Point) (patch : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point) :
    HarmonicBlock LocalSignedRequest.Point :=
  p.curlBlock s (LocalSignedRequest.fullRequest s patch coord c u)


-- @@ L3761-3768 verbatim
/-- State signed gaussian, constructed using `SignedWaveUpdate.gaussianBlock`. -/
noncomputable def stateSignedGaussian (p : SignedParameters LocalSignedRequest.Point)
    (s : StripData LocalSignedRequest.Point) (patch : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point) :
    HarmonicBlock LocalSignedRequest.Point :=
  SignedWaveUpdate.gaussianBlock (p.coefficients s (LocalSignedRequest.fullRequest s patch coord c
      u))
    p.directions p.cutoff p.angularFrequency


-- @@ L3770-3784 verbatim
/-- Every signed block and Gaussian field is computed from the actual
current residual. The pressure is then recomputed from the updated field. -/
noncomputable def signedWaveStage {ι : Type}
    (g : VariableGaugeMean.GaugeData PressureStream.Plane)
    (parameters : ι → SignedParameters LocalSignedRequest.Point) (labels : ℕ → Finset ι)
    (s : StripData LocalSignedRequest.Point) (patch : SignedStressPrimitive.Patch) (coord : ℝ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point) : State
        LocalSignedRequest.Point :=
  gaugeWaveStage g c u
    (LabelSumBounds.fieldSum labels (fun l => (stateSignedBlock (parameters l) s patch coord c
        u).oscillation))
    (fun n x => ∑ l ∈ labels n, (stateSignedBlock (parameters l) s patch coord c
        u).oscillatoryPressure n x)
    ⟨0, LabelSumBounds.fieldSum labels
      (fun l => (stateSignedGaussian (parameters l) s patch coord c u).oscillation), 0⟩


-- @@ L3786-3819 verbatim
/-- The requested tensor is not supplied as an arbitrary input: these
classes start from the current state's two actual mean residuals. -/
theorem stateSignedBlock_bounds {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (patch : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (s : StripData LocalSignedRequest.Point)
    (hs : s = LocalSignedRequest.movingStripData U patch.a patch.b cL cR patch.a_pos hcL hcR
      ε L hε hεone hL)
    (p : SignedParameters LocalSignedRequest.Point)
    {P₀ : ℕ → LocalSignedRequest.Point × ℝ → ℝ} {P : ℕ → LocalSignedRequest.Point → ℝ}
    {α₀ κ B : ℝ} (hcontrol : p.Control s P₀ P α₀ κ)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsθ : ∀ n, LocalSignedRequest.MovingSupport patch.a patch.b coord U.carrier (u.thetaResidual c
        n))
    (hsz : ∀ n, LocalSignedRequest.MovingSupport patch.a patch.b coord U.carrier (u.axialResidual c
        n))
    (hcθ : MeanClass s (B + 1 / 2 - κ) (u.thetaResidual c))
    (hcz : MeanClass s (B + 1 / 2 - κ) (u.axialResidual c)) :
    (stateSignedTangent p s patch coord c u).WaveBounds s P (B - κ) ∧
      (stateSignedBlock p s patch coord c u).WaveBounds s P (B - κ) ∧
      (stateSignedBlock p s patch coord c u).PressureBounds s P (B + 1 / 2 - κ) ∧
      (stateSignedCurl p s patch coord c u).WaveBounds s P (B + 1 / 2 - 2 * κ) := by
  have hnorm : ∀ i, MeanClass s ((B + 1 / 2 - κ) - 1)
      (fun n x => LocalSignedRequest.normalizedRequest s patch coord c u n x i) := by
    subst s
    exact LocalSignedRequest.normalizedRequest_class U patch hcL hcR ε L hε hεone hL
      c u (B + 1 / 2 - κ) hθ hz hsθ hsz hcθ hcz
  have hfull := LocalSignedRequest.fullRequest_class s patch coord c u hnorm
  apply hcontrol.bounds (LocalSignedRequest.fullRequest s patch coord c u)
  intro i
  convert! hfull i using 1
  ring


-- @@ L3821-3821 verbatim
end ActualSignedStage


-- @@ L3823-3823 verbatim
section LinearCoefficientBridge


-- @@ L3825-3825 verbatim
open CorrectionState


-- @@ L3827-3834 verbatim
/-- The actual real linearized cylindrical residual of a block, evaluated
with the carrier of the old spatial label. -/
noncomputable def linearBlockField (c : Context D) (a b : HarmonicBlock D) : Oscillation D :=
  fun n x i => (LinearWaveResidual.linearResidual (c.operators.epsilon n)
    (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
    (axialDirection c n) (timeDirection c n) (complexBase c n)
    (LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n))
    (fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ)) x i).re


-- @@ L3836-3871 verbatim
theorem linearCoefficients_field {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) {x : D × ℝ}
    (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    (HarmonicFields.field (HarmonicWaveInteraction.linearCoefficients c a b n i)
      (a.frequency n) (a.phase n) (a.angularFrequency n) x).re = linearBlockField c a b n x i := by
  have he := HarmonicResidual.field_linearResidual hU (HarmonicResidual.contextFrame c n)
    hr hz (fun l => HarmonicResidual.smoothCoefficients_constant (hB l))
    (fun l => (hb l).realCoefficients) hp.realCoefficients hΦ
    (a.frequency n) (a.angularFrequency n) hx
  change HarmonicResidual.vectorField
    (HarmonicWaveInteraction.linearCoefficients c a b n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) x = _ at he
  have hbase : HarmonicResidual.vectorField
      (fun l => HarmonicFields.constantCoefficient (fun y => HarmonicResidual.contextBase c n y l))
      (a.frequency n) (a.phase n) (a.angularFrequency n) = complexBase c n := by
    funext y l
    exact HarmonicResidual.field_constant _ _ _ _ y
  have hamp : HarmonicResidual.vectorField
      (fun l => HarmonicResidual.realCoefficients (b.velocity n l))
      (a.frequency n) (a.phase n) (a.angularFrequency n) =
        LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n) := by
    funext y l
    exact HarmonicResidual.field_realCoefficients _ _ _ _ y
  have hpress : HarmonicFields.field (HarmonicResidual.realCoefficients (b.pressure n))
      (a.frequency n) (a.phase n) (a.angularFrequency n) =
        fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ) := by
    funext y
    exact HarmonicResidual.field_realCoefficients _ _ _ _ y
  rw [hbase, hamp, hpress] at he
  exact congrArg Complex.re (congrFun he i)


-- @@ L3873-3920 verbatim
/-- An actual field cancellation determines every nonzero coefficient.
The Gaussian is subtracted only after its full field is retained in the
identity. The conclusion uses the literal `linearGoodBlock`. -/
theorem linearGoodBlock_cancel {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b source good : HarmonicBlock D)
    (g : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) (hkp : a.angularFrequency n ≠ 0)
    (hs : ∀ i, HarmonicFields.ConjugateSymmetric (source.velocity n i))
    (hg : ∀ i, HarmonicFields.ConjugateSymmetric (good.velocity n i))
    {x : D} (hx : x ∈ U) (j : ℤ) (hj : j ≠ 0) (i : Fin 3)
    (hcancel : ∀ θ, linearBlockField c a b n (x, θ) i +
      (HarmonicWaveInteraction.withCarrier a source).oscillation n (x, θ) i =
      (HarmonicWaveInteraction.withCarrier a good).oscillation n (x, θ) i +
      (HarmonicFields.field (g n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re) :
    source.velocity n i j x + (HarmonicWaveInteraction.linearGoodBlock c a b g).velocity n i j x =
      good.velocity n i j x := by
  have he : (source.velocity n i + HarmonicResidual.realCoefficients
      (HarmonicWaveInteraction.linearCoefficients c a b n i - g n i)) j x =
        good.velocity n i j x := by
    apply HarmonicWaveInteraction.coefficient_eq_of_field_eq_at _ _
      (a.frequency n) (a.phase n) hkp j x
    intro θ
    rw [HarmonicResidual.field_add, HarmonicResidual.field_realCoefficients,
      HarmonicResidual.field_sub, Complex.sub_re,
      linearCoefficients_field hU c a b n hr hz hB hb hp hΦ ⟨hx, trivial⟩ i,
      ← HarmonicFields.field_real (hs i), ← HarmonicFields.field_real (hg i)]
    have hc := hcancel θ
    change linearBlockField c a b n (x, θ) i +
      (HarmonicFields.field (source.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency
          n) (x, θ)).re =
      (HarmonicFields.field (good.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency n)
          (x, θ)).re + _ at hc
    have hh : (HarmonicFields.field (source.velocity n i) (a.frequency n) (a.phase n)
        (a.angularFrequency n) (x, θ)).re +
        (linearBlockField c a b n (x, θ) i -
          (HarmonicFields.field (g n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x,
              θ)).re) =
        (HarmonicFields.field (good.velocity n i) (a.frequency n) (a.phase n)
          (a.angularFrequency n) (x, θ)).re := by linarith
    exact_mod_cast hh
  simpa only [HarmonicWaveInteraction.linearGoodBlock,
    HarmonicMeanInteraction.nonconstant_apply_of_ne _ hj, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, Pi.add_apply] using he


-- @@ L3922-3945 verbatim
theorem linearGoodBlock_cancel_mem {s : StripData D} {P : ℕ → D → ℝ} {γ : ℝ}
    (c : Context D) (a b source good : HarmonicBlock D)
    (g : HarmonicResidual.BlockCoefficients D)
    (hr : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hz : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial s.domain)
    (hB : SmoothTriple s.domain c.base)
    (hb : ∀ n i, HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i))
    (hp : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (b.pressure n))
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hs : ∀ n i, HarmonicFields.ConjugateSymmetric (source.velocity n i))
    (hg : ∀ n i, HarmonicFields.ConjugateSymmetric (good.velocity n i))
    (hgood : good.WaveBounds s P γ)
    (hcancel : ∀ n x, x ∈ s.domain → ∀ θ i, linearBlockField c a b n (x, θ) i +
      (HarmonicWaveInteraction.withCarrier a source).oscillation n (x, θ) i =
      (HarmonicWaveInteraction.withCarrier a good).oscillation n (x, θ) i +
      (HarmonicFields.field (g n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re) :
    ∀ i j, j ≠ 0 → WaveClass s P γ (fun n x => source.velocity n i j x +
      (HarmonicWaveInteraction.linearGoodBlock c a b g).velocity n i j x) := by
  intro i j hj
  apply WaveInteractionBounds.class_congr (hgood i j hj)
  intro n x hx
  exact (linearGoodBlock_cancel s.isOpen_domain c a b source good g n (hr n) (hz n)
    (fun l => HarmonicMeanInteraction.tripleField_smooth hB n l) (hb n) (hp n)
    (hΦ n) (hkp n) (hs n) (hg n) hx j hj i (fun θ => hcancel n x hx θ i)).symm


-- @@ L3947-3947 verbatim
end LinearCoefficientBridge


-- @@ L3949-3949 verbatim
section ConstructedSignedLinear


-- @@ L3951-3951 verbatim
open CorrectionState


-- @@ L3953-3956 verbatim
/-- Context real base, given by `![c.base.radial n x.1, c.base.angular n x.1, c.base.axial n
x.1]`. -/
noncomputable def contextRealBase (c : Context D) (n : ℕ) (x : D × ℝ) : Fin 3 → ℝ :=
  ![c.base.radial n x.1, c.base.angular n x.1, c.base.axial n x.1]


-- @@ L3958-3962 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexBase_eq_realLift (c : Context D) (n : ℕ) :
    complexBase c n = LinearWaveResidual.realLift (contextRealBase c n) := by
  funext x i
  fin_cases i <;> rfl


-- @@ L3964-3970 verbatim
theorem contextRealBase_smooth {U : Set D} {c : Context D}
    (hB : SmoothTriple U c.base) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => contextRealBase c n x i) (HarmonicResidual.liftDomain U) := by
  fin_cases i
  · exact (hB.radial n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  · exact (hB.angular n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  · exact (hB.axial n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)


-- @@ L3972-4005 verbatim
theorem linearBlockField_eq_real {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain U))
    (hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain U))
    (hB : SmoothTriple U c.base)
    (hb : ∀ i, ContDiffOn ℝ ∞
      (fun x => (HarmonicWaveInteraction.withCarrier a b).oscillation n x i)
      (HarmonicResidual.liftDomain U))
    (hp : ContDiffOn ℝ ∞ ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n)
      (HarmonicResidual.liftDomain U))
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) :
    linearBlockField c a b n x =
      LinearWaveResidual.realComponentLinearResidual (c.operators.epsilon n)
        (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (contextRealBase c n)
        ((HarmonicWaveInteraction.withCarrier a b).oscillation n)
        ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n) x := by
  have hU' := HarmonicResidual.liftDomain_open hU
  have he := LinearWaveResidual.realMap_linearResidual Complex.reCLM
    (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1) (timeDirection c n)
    (Vθ := angularDirection)
    (B := contextRealBase c n)
    (a := LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n))
    (p := fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ))
    hU' hr contDiffOn_const hz
    (fun i => Complex.ofRealCLM.contDiff.comp_contDiffOn (hb i))
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt (hU'.mem_nhds hx)).differentiableAt (by
        simp))
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn hp).contDiffAt
      (hU'.mem_nhds hx)).differentiableAt (by simp)) hx
  rw [← complexBase_eq_realLift] at he
  simp only [ LinearWaveResidual.realLift, Complex.reCLM_apply,
    Complex.ofReal_re] at he ⊢
  exact he


-- @@ L4007-4021 verbatim
/-- Primitive equality of the direction and background data. This record
contains no residual identity and no statement about a corrected field. -/
structure WaveFrameMatch (c : Context D) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) : Prop where
  epsilon : ∀ n, s.epsilon n = c.operators.epsilon n
  radius : ∀ n, a.radius n = fun y : D × ℝ => c.operators.radius y.1
  radial : ∀ n, d.radialField n = radialDirection c n
  angular : d.angular = (0,1)
  axial : ∀ n, d.axialField s n = axialDirection c n
  time : ∀ n, LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow) =
    timeDirection c n
  radialBase : ∀ n x, a.radialBase n x = c.base.radial n x.1
  angularBase : ∀ n x, a.radius n x * a.frequencyBase n x = c.base.angular n x.1
  axialBase : ∀ n x, a.axialBase n x = c.base.axial n x.1


-- @@ L4023-4031 verbatim
theorem WaveFrameMatch.base {c : Context D} {s : StripData (D × ℝ)}
    {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} (h : WaveFrameMatch c s d a) (n : ℕ) :
    LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase
        n) =
      complexBase c n := by
  funext x i
  fin_cases i <;> simp [LinearWaveResidual.complexBase, LinearWaveResidual.base, complexBase,
    h.radialBase n x, h.angularBase n x, h.axialBase n x]


-- @@ L4033-4044 verbatim
theorem WaveFrameMatch.harmonicResidual {c : Context D} {s : StripData (D × ℝ)}
    {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {z : LinearWaveBounds.WaveCoefficients (D × ℝ)} (h : WaveFrameMatch c s d z) (n : ℕ) :
    z.harmonicResidual s d n =
      LinearWaveResidual.linearResidual (c.operators.epsilon n)
        (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (complexBase c n)
        (HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n))
        (HarmonicCalculus.mode (z.frequency n) (z.phase n) (z.pressure n)) := by
  unfold LinearWaveBounds.WaveCoefficients.harmonicResidual
  rw [h.base, h.time, h.epsilon, h.radius, h.radial, h.axial, h.angular]
  rfl


-- @@ L4046-4081 verbatim
theorem linearBlockField_eq_modeResidual {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (z : LinearWaveBounds.WaveCoefficients (D × ℝ)) (hm : WaveFrameMatch c s d z)
    (n : ℕ) (hB : SmoothTriple U c.base)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain U))
    (hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain U))
    (hphase : ContDiffOn ℝ ∞ (z.phase n) (HarmonicResidual.liftDomain U))
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => z.amplitude n x i) (HarmonicResidual.liftDomain U))
    (hp : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain U))
    (hvel : (HarmonicWaveInteraction.withCarrier a b).oscillation n =
      fun x i => (HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n) x i).re)
    (hpress : (HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n =
      fun x => (HarmonicCalculus.mode (z.frequency n) (z.phase n) (z.pressure n) x).re)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) :
    linearBlockField c a b n x = fun i => (z.harmonicResidual s d n x i).re := by
  have hU' := HarmonicResidual.liftDomain_open hU
  have hv' i : ContDiffOn ℝ ∞
      (fun y => HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i)
      (HarmonicResidual.liftDomain U) := HarmonicCalculus.contDiffOn_mode _ hphase (hv i)
  have hp' := HarmonicCalculus.contDiffOn_mode (z.frequency n) hphase hp
  have he := LinearWaveResidual.realMap_linearResidual Complex.reCLM
    (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1) (timeDirection c n)
    (Vθ := angularDirection)
    (B := contextRealBase c n)
    hU' hr contDiffOn_const hz hv'
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt (hU'.mem_nhds hx)).differentiableAt (by
        simp))
    ((hp'.contDiffAt (hU'.mem_nhds hx)).differentiableAt (by simp)) hx
  rw [← complexBase_eq_realLift, ← hm.harmonicResidual] at he
  simp only [Complex.reCLM_apply] at he
  rw [← hvel, ← hpress] at he
  rw [linearBlockField_eq_real hU c a b n hr hz hB
    (fun i => by rw [hvel]; exact Complex.reCLM.contDiff.comp_contDiffOn (hv' i))
    (by rw [hpress]; exact Complex.reCLM.contDiff.comp_contDiffOn hp') hx]
  exact he.symm


-- @@ L4083-4101 verbatim
theorem SignedParameters.Control.full_bounds {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    (h : p.Control s P₀ P α₀ κ) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) :
    let z := p.coefficients s request
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (B - κ)
        (z.corrected (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff).amplitude ∧
      WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (B + 1 / 2 - κ)
        (z.corrected (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff).pressure ∧
      WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (B + 1 / 2 - 2 * κ)
        (fun n x => (z.corrected (HarmonicWaveInteraction.productStrip s) p.directions
            p.cutoff).amplitude n x -
          (z.withCutoff p.cutoff).amplitude n x) ∧
      WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (B + 1 / 2 - 4 * κ)
        (z.constructedGood (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff) :=
  SignedWaveUpdate.signed_bounds h.baseBounds h.kappa_le_half h.covariance hR h.mask h.fundamental
    h.normal h.normalMotion h.action h.lower_pos h.norm_lower h.norm_upper h.inverseFrequency
    h.radius_eq h.cutoff p.column


-- @@ L4103-4109 verbatim
/-- Good block, constructed using `SignedWaveUpdate.coefficientBlock`. -/
noncomputable def SignedParameters.goodBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0))
      p.angularFrequency
    (fun n x => (p.coefficients s request).constructedGood
      (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff n (x,0)) 0


-- @@ L4111-4121 verbatim
theorem SignedParameters.Control.good_bounds {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    (h : p.Control s P₀ P α₀ κ) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) :
    (p.goodBlock s request).WaveBounds s P (B + 1 / 2 - 4 * κ) := by
  have hg := SignedWaveUpdate.class_zeroSection (h.full_bounds request hR).2.2.2
  rw [sectionStrip_productStrip] at hg
  exact (SignedWaveUpdate.coefficientBlock_classes p.base.frequency
    (fun n x => p.base.phase n (x,0)) p.angularFrequency hg
    (MemClass.zero (α := (0 : ℝ)) hg.weight_nonneg)).1


-- @@ L4123-4154 verbatim
/-- The ODE and phase data of the fixed primary column, before performing
any signed update. All equalities concern primitive inputs. -/
structure SignedParameters.Dynamics (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) where
  /-- Slope of `Dynamics`, of type `ℕ → ℝ`. -/
  slope : ℕ → ℝ
  angular : SignedWaveUpdate.AngularInputs (HarmonicWaveInteraction.productStrip s) p.directions
    p.base p.matrix p.target request p.mask p.fundamental p.normalMotion p.action p.cutoff slope
  angular_direction : p.directions.angular = (0,1)
  angular_frequency : ∀ n, p.base.frequency n * slope n = (p.angularFrequency n : ℝ)
  angular_nonzero : ∀ n, p.angularFrequency n ≠ 0
  geometry : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip
      s).domain
    (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
    (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n)
  matrix_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.matrix
  target_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.target
  request_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast request
  mask_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.mask
  frequency_nonzero : ∀ n, p.base.frequency n ≠ 0
  ode : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    HarmonicCalculus.along (p.directions.fastField n) (p.fundamental n) x =
      TangentProjection.projectedRhs (p.base.normal (HarmonicWaveInteraction.productStrip s)
          p.directions n x)
        (p.normalMotion n x) (p.fundamental n x) (p.action n x (p.fundamental n x)) 0
        (s.epsilon n * p.base.frequency n ^ 2 *
          ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ^ 2)
  action_eq : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    CurlClassBounds.complexify (p.action n x (p.fundamental n x)) =
      LinearWaveResidual.shear (p.base.radius n) (p.base.frequencyBase n) (p.base.axialBase n)
        (p.directions.radialField n) (fun y => CurlClassBounds.complexify (p.fundamental n y)) x
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (p.cutoff n)


-- @@ L4156-4164 verbatim
theorem SignedParameters.Dynamics.phase_eq {p : SignedParameters D} {s : StripData D}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2} (h : p.Dynamics s request)
    (n : ℕ) (x : D) (θ : ℝ) :
    p.base.frequency n * p.base.phase n (x,θ) =
      p.base.frequency n * p.base.phase n (x,0) + (p.angularFrequency n : ℝ) * θ := by
  rw [CopyAngularInvariance.affinePhase_eq_zeroSlice
    (Φ := p.base.phase n) (m := h.slope n)
    (by simpa only [h.angular_direction] using h.angular.phase n) x θ,
    mul_add, ← mul_assoc, h.angular_frequency]


-- @@ L4166-4187 verbatim
theorem SignedParameters.Dynamics.good_represents {p : SignedParameters D} {s : StripData D}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2} (h : p.Dynamics s request) :
    (p.goodBlock s request).oscillation = fun n x i =>
      ((p.coefficients s request).constructedGood (HarmonicWaveInteraction.productStrip s)
        p.directions p.cutoff n x i * HarmonicCalculus.carrier (p.base.frequency n) (p.base.phase
            n) x).re := by
  have hi (n : ℕ) : CopyAngularInvariance.Invariant p.directions.angular
      ((p.coefficients s request).constructedGood (HarmonicWaveInteraction.productStrip s)
        p.directions p.cutoff n) :=
    ParticularWaveAssembly.constructedGood_invariant (a := p.coefficients s request)
      p.cutoff h.angular.radius h.angular.radial_base h.angular.frequency_base h.angular.axial_base
      h.angular.radialField (fun _ => CopyAngularInvariance.Invariant.const _)
      (fun n => ⟨h.slope n, h.angular.phase n⟩)
      (h.angular.amplitude p.column) (h.angular.pressure p.column) h.angular.cutoff n
  let z : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
    {p.base with amplitude := ((p.coefficients s request).constructedGood
      (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff), pressure := 0}
  have he := (SignedWaveUpdate.blockOfCoefficients_represents z p.angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [h.angular_direction] using hi n) x θ)
    (fun _ _ _ => rfl) h.phase_eq).1
  exact he


-- @@ L4189-4200 verbatim
theorem SignedParameters.Dynamics.exact_represents {p : SignedParameters D} {s : StripData D}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2} (h : p.Dynamics s request) :
    let z := (p.coefficients s request).corrected (HarmonicWaveInteraction.productStrip s)
      p.directions p.cutoff
    (p.exactBlock s request).oscillation =
      (fun n x i => (HarmonicCalculus.vectorMode (p.base.frequency n) (p.base.phase n) (z.amplitude
          n) x i).re) ∧
    (p.exactBlock s request).oscillatoryPressure =
      (fun n x => (HarmonicCalculus.mode (p.base.frequency n) (p.base.phase n) (z.pressure n)
          x).re) :=
  SignedWaveUpdate.signedBlock_represents h.angular h.angular_direction p.angularFrequency
    h.angular_frequency p.column


-- @@ L4202-4220 verbatim
theorem SignedParameters.Dynamics.linear_identity {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.Dynamics s request) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) :
    let z := p.coefficients s request
    ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
      (z.corrected (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions n x =
      (fun i => (z.constructedGood (HarmonicWaveInteraction.productStrip s) p.directions p.cutoff n
          x i +
        LinearWaveBounds.excludedSlotError p.directions p.cutoff z.amplitude 0 n x i) *
        HarmonicCalculus.carrier (p.base.frequency n) (p.base.phase n) x) :=
  SignedWaveUpdate.signed_linear_identity hc.baseBounds hc.kappa_le_half hc.covariance hR
    hc.mask hc.fundamental hc.normal hc.normalMotion hc.action hc.lower_pos hc.norm_lower
        hc.norm_upper
    hc.inverseFrequency hc.radius_eq hc.cutoff h.angular h.geometry h.matrix_frozen h.target_frozen
    h.request_frozen h.mask_frozen h.frequency_nonzero h.ode h.action_eq p.column


-- @@ L4222-4226 verbatim
theorem productStrip_domain (s : StripData D) :
    (HarmonicWaveInteraction.productStrip s).domain = HarmonicResidual.liftDomain s.domain := by
  ext x
  simp [HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip,
    HarmonicWaveInteraction.projection, HarmonicResidual.liftDomain]


-- @@ L4228-4238 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem withCarrier_of_same {a b : HarmonicBlock D} (h : SameCarrier a b) :
    HarmonicWaveInteraction.withCarrier a b = b := by
  rcases a with ⟨av,ap,ak,aΦ,akp⟩
  rcases b with ⟨bv,bp,bk,bΦ,bkp⟩
  rcases h with ⟨hk,hΦ,hkp⟩
  simp only at hk hΦ hkp
  subst bk
  subst bΦ
  subst bkp
  rfl


-- @@ L4240-4247 verbatim
theorem SignedParameters.frame_corrected (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) {c : Context D}
    (h : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base) :
    WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions
      ((p.coefficients s request).corrected (HarmonicWaveInteraction.productStrip s) p.directions
          p.cutoff) :=
  ⟨h.epsilon, h.radius, h.radial, h.angular, h.axial, h.time, h.radialBase, h.angularBase,
      h.axialBase⟩


-- @@ L4249-4253 verbatim
/-- Gaussian block, given by `SignedWaveUpdate.gaussianBlock (p.coefficients s request)
p.directions p.cutoff p.angularFrequency`. -/
noncomputable def SignedParameters.gaussianBlock (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : HarmonicBlock D :=
  SignedWaveUpdate.gaussianBlock (p.coefficients s request) p.directions p.cutoff p.angularFrequency


-- @@ L4255-4258 verbatim
theorem SignedParameters.exactBlock_pressure_zero (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    ∀ n, (p.exactBlock s request).pressure n 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).2


-- @@ L4260-4267 verbatim
theorem SignedParameters.Dynamics.gaussian_represents {p : SignedParameters D} {s : StripData D}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2} (h : p.Dynamics s request) :
    (p.gaussianBlock s request).oscillation = fun n x i =>
      (LinearWaveBounds.excludedSlotError p.directions p.cutoff (p.coefficients s
          request).amplitude 0 n x i *
        HarmonicCalculus.carrier (p.base.frequency n) (p.base.phase n) x).re :=
  SignedWaveUpdate.gaussianBlock_represents h.angular h.angular_direction h.cutoff_smooth
    p.angularFrequency h.angular_frequency p.column


-- @@ L4269-4314 verbatim
/-- The actual signed field, with the literal `Context` operators, has the
computed good residual plus its computed Gaussian error. -/
theorem SignedParameters.Dynamics.context_linear_identity
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.Dynamics s request) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i))
    (c : Context D) (hB : SmoothTriple s.domain c.base)
    (hmatch : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request))
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c a (p.exactBlock s request) n x =
      (p.goodBlock s request).oscillation n x + (p.gaussianBlock s request).oscillation n x := by
  let z := (p.coefficients s request).corrected (HarmonicWaveInteraction.productStrip s)
      p.directions p.cutoff
  have hb := hc.full_bounds request hR
  have hr := (h.geometry n).radial_smooth
  have hz := (h.geometry n).axial_smooth
  rw [productStrip_domain, hmatch.radial] at hr
  rw [productStrip_domain, hmatch.axial] at hz
  have hp := h.angular.phase_smooth n
  rw [productStrip_domain] at hp
  have hv (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => z.amplitude n y i)
      (HarmonicResidual.liftDomain s.domain) := by
    simpa only [productStrip_domain] using (CurlClassBounds.class_component hb.1 i).smooth n
  have hpressure : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain s.domain) := by
    simpa only [productStrip_domain] using hb.2.1.smooth n
  have hvrep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillation n =
      fun y i => (HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i).re
          := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun h.exact_represents.1 n
  have hprep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillatoryPressure
      n =
      fun y => (HarmonicCalculus.mode (z.frequency n) (z.phase n) (z.pressure n) y).re := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun h.exact_represents.2 n
  rw [linearBlockField_eq_modeResidual s.isOpen_domain c a (p.exactBlock s request)
    (HarmonicWaveInteraction.productStrip s) p.directions z (p.frame_corrected s request hmatch)
    n hB hr hz hp hv hpressure hvrep hprep ⟨hx, trivial⟩]
  rw [h.good_represents, h.gaussian_represents]
  funext i
  have he := congrArg Complex.re (congrFun (h.linear_identity hc hR n x hx) i)
  simpa only [add_mul, Complex.add_re, Pi.add_apply] using he


-- @@ L4316-4379 verbatim
/-- The literal harmonic linear remainder has the gain proved for the
constructed signed coefficient. No output residual class is an input. -/
theorem SignedParameters.Dynamics.linearGood_bounds
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.Dynamics s request) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i))
    (c : Context D) (hB : SmoothTriple s.domain c.base)
    (hmatch : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request)) :
    (HarmonicWaveInteraction.linearGoodBlock c a (p.exactBlock s request)
      (p.gaussianBlock s request).velocity).WaveBounds s P (B + 1 / 2 - 4 * κ) := by
  let zero : HarmonicBlock D := ErrorHarmonics.zeroBlock a.frequency a.phase a.angularFrequency 0
  have hbounds := hc.bounds request hR
  have hbs := HarmonicWaveInteraction.waveBounds_smooth hbounds.2.1 (p.exactBlock_zero s request)
  have hps (n : ℕ) : HarmonicResidual.SmoothCoefficients s.domain ((p.exactBlock s
      request).pressure n) := by
    intro j
    by_cases hj : j = 0
    · subst j
      rw [p.exactBlock_pressure_zero s request n]
      exact contDiffOn_const
    exact (hbounds.2.2.1 j hj).smooth n
  have hphase (n : ℕ) : ContDiffOn ℝ ∞ (a.phase n) s.domain := by
    rw [← hcarrier.phase]
    exact (h.angular.phase_smooth n).comp (SignedWaveUpdate.zeroSection (D :=
        D)).contDiff.contDiffOn
      (fun x hx => hx)
  have hkp (n : ℕ) : a.angularFrequency n ≠ 0 := by
    rw [← hcarrier.angular]
    exact h.angular_nonzero n
  have hrad (n : ℕ) : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain := by
    have he := (h.geometry n).radial_smooth
    rw [hmatch.radial] at he
    have hh := (contDiff_fst.comp_contDiffOn he).comp
      (SignedWaveUpdate.zeroSection (D := D)).contDiff.contDiffOn (fun x hx => hx)
    exact hh
  have hgcarrier : SameCarrier a (p.goodBlock s request) :=
    ⟨hcarrier.frequency, hcarrier.phase, hcarrier.angular⟩
  have hecarrier : SameCarrier a (p.gaussianBlock s request) :=
    ⟨hcarrier.frequency, hcarrier.phase, hcarrier.angular⟩
  have hcancel := linearGoodBlock_cancel_mem c a (p.exactBlock s request) zero
    (p.goodBlock s request) (p.gaussianBlock s request).velocity hrad
    (fun _ => contDiffOn_const) hB hbs hps hphase hkp
    (fun n i => ErrorHarmonics.zeroBlock_symmetric _ _ _ _ n i)
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1
    (hc.good_bounds request hR) ?_
  · intro i j hj
    simpa [zero, ErrorHarmonics.zeroBlock, HarmonicFields.constantCoefficient,
      Finsupp.single_apply, hj, Ne.symm hj] using hcancel i j hj
  · intro n x hx θ i
    have he := congrFun (h.context_linear_identity hc hR c hB hmatch a hcarrier n (x,θ) hx) i
    rw [withCarrier_of_same hgcarrier]
    have heval : (HarmonicFields.field ((p.gaussianBlock s request).velocity n i)
        (a.frequency n) (a.phase n) (a.angularFrequency n) (x,θ)).re =
        (p.gaussianBlock s request).oscillation n (x,θ) i := by
      simp only [HarmonicBlock.oscillation, hecarrier.frequency, hecarrier.phase, hecarrier.angular]
    rw [heval]
    simpa only [zero, HarmonicWaveInteraction.withCarrier, ErrorHarmonics.zeroBlock,
      HarmonicBlock.oscillation, HarmonicResidual.field_constant, Pi.zero_apply,
          Complex.ofReal_zero,
      Complex.zero_re, Pi.add_apply, add_zero] using he


-- @@ L4381-4381 verbatim
end ConstructedSignedLinear


-- @@ L4383-4383 verbatim
section ConstructedSignedInvariants


-- @@ L4385-4385 verbatim
open CorrectionState

-- @@ L4386-4386 verbatim
open scoped InnerProductSpace


-- @@ L4388-4406 verbatim
/-- Primitive localization data for the already chosen signed cutoff. -/
structure SignedParameters.GaussianControl (p : SignedParameters D) (s : StripData D)
    (P : ℕ → D → ℝ) where
  /-- Slot of `GaussianControl`, of type `GaussianTailFlat.SlotFamily
  (HarmonicWaveInteraction.productStrip s)`. -/
  slot : GaussianTailFlat.SlotFamily (HarmonicWaveInteraction.productStrip s)
  cutoff : p.cutoff = slot.cutoff
  fast : ∀ n, slot.linear n (p.directions.fastScale n • p.directions.fast) = (slot.length n)⁻¹
  /-- Edges of `GaussianControl`, of type `GaussianTailFlat.FlatEdges
  (HarmonicWaveInteraction.productStrip s)`. -/
  edges : GaussianTailFlat.FlatEdges (HarmonicWaveInteraction.productStrip s)
  /-- Scales of `GaussianControl`, of type `GaussianTailFlat.BandScaleControl
  (HarmonicWaveInteraction.productStrip s)`. -/
  scales : GaussianTailFlat.BandScaleControl (HarmonicWaveInteraction.productStrip s)
  /-- Rate of `GaussianControl`, of type `ℝ`. -/
  rate : ℝ
  rate_pos : 0 < rate
  envelope : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    P n x.1 ≤ Real.exp (-rate * (slot.coordinate n x - 1 / 2) ^ 2 * slot.length n)


-- @@ L4408-4425 verbatim
theorem SignedParameters.GaussianControl.coefficient_flat
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.GaussianControl s P) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) (N : ℝ) :
    UnweightedClass (HarmonicWaveInteraction.productStrip s) N
      (LinearWaveBounds.excludedSlotError p.directions p.cutoff (p.coefficients s
          request).amplitude 0) := by
  have hi := SignedWaveUpdate.coefficients_inputBounds hc.baseBounds hc.covariance hR hc.mask
      hc.fundamental
    hc.normal hc.normalMotion hc.action hc.lower_pos hc.norm_lower hc.norm_upper
        hc.inverseFrequency p.column
  have ha := LinearWaveBounds.component_classes hi.amplitude
  rw [h.cutoff]
  exact LinearWaveBounds.excludedSlotError_all_gains h.slot p.directions h.fast h.edges h.scales
    ha (MemClass.zero ha.weight_nonneg) h.rate_pos h.envelope N


-- @@ L4427-4437 verbatim
theorem SignedParameters.GaussianControl.block_flat
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.GaussianControl s P) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i)) (N : ℝ) (i : Fin 3) (j : ℤ) :
    UnweightedClass s N (fun n x => (p.gaussianBlock s request).velocity n i j x) := by
  have he := HarmonicWaveInteraction.class_slice (s := s) (w := fun _ _ => 1)
    (h.coefficient_flat hc hR N)
  exact SignedWaveUpdate.conjugatePair_class (CurlClassBounds.class_component he i) j


-- @@ L4439-4485 verbatim
theorem SignedParameters.Dynamics.full_divergence_zero
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.Dynamics s request) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i))
    (ht : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental n
          x⟫_ℝ = 0)
    (c : Context D)
    (hmatch : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    HarmonicCalculus.cylindricalDivergence (fun q => c.operators.radius q.1)
      (radialDirection c n) angularDirection (axialDirection c n)
      (fun q i => ((p.exactBlock s request).oscillation n q i : ℂ)) x = 0 := by
  let z := (p.coefficients s request).corrected (HarmonicWaveInteraction.productStrip s)
      p.directions p.cutoff
  have hb := hc.full_bounds request hR
  have hdiff (i : Fin 3) : DifferentiableAt ℝ
      (fun y => HarmonicCalculus.vectorMode (p.base.frequency n) (p.base.phase n) (z.amplitude n) y
          i) x := by
    exact ((HarmonicCalculus.contDiffOn_mode (p.base.frequency n) (h.angular.phase_smooth n)
      ((CurlClassBounds.class_component hb.1 i).smooth n)).contDiffAt
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hx)).differentiableAt (by
          simp)
  have hd := (SignedWaveUpdate.signed_curl_realization hc.baseBounds hc.covariance hR
    hc.mask hc.fundamental hc.normal hc.normalMotion hc.action hc.lower_pos hc.norm_lower
        hc.norm_upper
    hc.inverseFrequency hc.cutoff p.column n (h.geometry n) (h.frequency_nonzero n)
    (h.angular.phase_smooth n) ht x hx).2
  change HarmonicCalculus.cylindricalDivergence (p.base.radius n) (p.directions.radialField n)
    (fun _ => p.directions.angular) (p.directions.axialField (HarmonicWaveInteraction.productStrip
        s) n)
    (HarmonicCalculus.vectorMode (p.base.frequency n) (p.base.phase n) (z.amplitude n)) x = 0 at hd
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have he := ParticularWaveAssembly.divergence_map L (p.base.radius n) (p.directions.radialField n)
    (fun _ => p.directions.angular) (p.directions.axialField (HarmonicWaveInteraction.productStrip
        s) n) hdiff
  rw [hd] at he
  have ha : angularDirection (D := D) = fun _ => p.directions.angular := by
    rw [h.angular_direction]
    rfl
  rw [h.exact_represents.1, ← hmatch.radius, ← hmatch.radial, ← hmatch.axial, ha]
  · simp only [L, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
      map_zero] at he
    exact he


-- @@ L4487-4508 verbatim
theorem SignedParameters.Dynamics.modeSolenoidal
    {p : SignedParameters D} {s : StripData D}
    {P₀ : ℕ → D × ℝ → ℝ} {P : ℕ → D → ℝ} {α₀ κ B : ℝ}
    {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
    (h : p.Dynamics s request) (hc : p.Control s P₀ P α₀ κ)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x i))
    (ht : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental n
          x⟫_ℝ = 0)
    (c : Context D)
    (hmatch : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base) :
    HarmonicWaveInteraction.ModeSolenoidal s c (p.exactBlock s request) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full c (p.exactBlock s request)
  · intro n
    exact (h.angular.phase_smooth n).comp (SignedWaveUpdate.zeroSection (D :=
        D)).contDiff.contDiffOn
      (fun x hx => hx)
  · exact h.angular_nonzero
  · exact HarmonicWaveInteraction.waveBounds_smooth (hc.bounds request hR).2.1 (p.exactBlock_zero s
      request)
  · exact h.full_divergence_zero hc hR ht c hmatch


-- @@ L4510-4510 verbatim
end ConstructedSignedInvariants


-- @@ L4512-4512 verbatim
section GaugeRankMean


-- @@ L4514-4514 verbatim
open CorrectionState VariableGaugeMean


-- @@ L4516-4516 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


-- @@ L4518-4530 verbatim
omit [FiniteDimensional ℝ S] in
theorem slow_directional_zero_on {s : StripData (PressureStream.Lift S)} {U : Set S}
    (hU : ∀ x ∈ s.domain, x.2.1 ∈ U)
    {f : ScalarField (PressureStream.Lift S)} (hf : SmoothOn s.domain f)
    (hslow : LocalRankDefect.IsSlowOn U f) (v : PressureStream.Plane)
    (n : ℕ) {x : PressureStream.Lift S} (hx : x ∈ s.domain) :
    fderiv ℝ (f n) x (0, (0, v)) = 0 := by
  apply directional_zero_of_line_const ((hf.at_point s.isOpen_domain n hx).differentiableAt (by
      simp))
  intro t
  rcases x with ⟨R, p, Y⟩
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  rw [hslow n R p (hU _ hx), hslow n R p (hU _ hx)]


-- @@ L4532-4600 verbatim
/-- Slow rank increments preserve an already subtracted temporal alias.
The slow axial identity comes from the constructed zero-mass stream. -/
theorem gaugeRankStage_mean_gain {s : StripData (PressureStream.Lift S)}
    {U : Set S} (hU : IsOpen U) (hSU : ∀ x ∈ s.domain, x.2.1 ∈ U)
    (g : GaugeData S) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hg : LocalRankDefect.RankGeometry g r U c u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hleft : ∀ n p, p ∈ U → a ≤ r.length n p * r.inner)
    (hright : ∀ n p, p ∈ U → r.length n p * r.outer ≤ b)
    {H κ β : ℝ} (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (rankIncrementState g r axial c u))
    (hdp : MeanClass s H (gaugeRankPressureChange g r axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (A : ScalarField (PressureStream.Lift S))
    (hθ : MeanClass s β (u.thetaResidual c))
    (hz : MeanClass s β (u.axialResidual c - A))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((rankStageState g r axial c u).thetaResidual c) ∧
      MeanClass s β ((rankStageState g r axial c u).axialResidual c - A) := by
  have hslowθ : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrementState g r axial c u).angular n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero_on hSU hi.angular.smooth
      (LocalRankDefect.rank_angular_slow g r axial U c u) v n hx
  have hslowz : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrementState g r axial c u).axial n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero_on hSU hi.axial.smooth
      (hg.axial_slow ha hab hU hleft hright axial) v n hx
  have hδθ := thetaResidual_change_slow_mem ho hb hu.velocity hi hH
    u.covariance hW c.virtualTheta hslowθ
  have hδz := axialResidual_change_slow_mem ho hb hu.velocity hi hH
    u.covariance hW u.pressure (gaugeRankPressureChange g r axial c u)
    c.virtualAxial hu.pressure.smooth hdp hslowz
  have hpressure : u.pressure + gaugeRankPressureChange g r axial c u =
      (rankStageState g r axial c u).pressure := by
    unfold gaugeRankPressureChange
    abel
  have hnewθ : (rankStageState g r axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base (updated u.mean (rankIncrementState g r
          axial c u))
        u.covariance c.virtualTheta := by
    change MeanIncrementBounds.thetaResidual c.operators c.base _ _ _ = _
    rw [gaugeRankStage_covariance]
    rfl
  have hnewz : (rankStageState g r axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base (updated u.mean (rankIncrementState g r
          axial c u))
        u.covariance (u.pressure + gaugeRankPressureChange g r axial c u) c.virtualAxial := by
    rw [hpressure]
    change MeanIncrementBounds.axialResidual c.operators c.base _ _ _ _ = _
    rw [gaugeRankStage_covariance]
    rfl
  constructor
  · apply class_congr (hθ.add (hδθ.mono_exponent hβ))
    intro n x hx
    rw [hnewθ]
    change _ = u.thetaResidual c n x + (_ - u.thetaResidual c n x)
    ring
  · apply class_congr (hz.add (hδz.mono_exponent hβ))
    intro n x hx
    rw [hnewz]
    change _ - _ = (u.axialResidual c n x - A n x) + (_ - u.axialResidual c n x)
    ring


-- @@ L4602-4631 verbatim
theorem gaugeRankStage_next_mean {s : StripData (PressureStream.Lift S)}
    {U : Set S} (hU : IsOpen U) (hSU : ∀ x ∈ s.domain, x.2.1 ∈ U)
    (g : GaugeData S) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hg : LocalRankDefect.RankGeometry g r U c u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hleft : ∀ n p, p ∈ U → a ≤ r.length n p * r.inner)
    (hright : ∀ n p, p ∈ U → r.length n p * r.outer ≤ b)
    {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000)
    (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s (ExponentLedger.meanUpdateExponent σ κ) (rankIncrementState g r axial c
        u))
    (hdp : MeanClass s (ExponentLedger.meanUpdateExponent σ κ) (gaugeRankPressureChange g r axial c
        u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (A : ScalarField (PressureStream.Lift S))
    (hθ : MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10)) (u.thetaResidual c))
    (hz : MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10)) (u.axialResidual c - A)) :
    MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10)) ((rankStageState g r axial c
        u).thetaResidual c) ∧
      MeanClass s (ExponentLedger.meanExponent (σ + 1 / 10)) ((rankStageState g r axial c
          u).axialResidual c - A) := by
  apply gaugeRankStage_mean_gain hU hSU g r axial c u hg ha hab hleft hright v hfast
    ho hb hu hi hdp hW A hθ hz
  · unfold ExponentLedger.meanUpdateExponent ExponentLedger.meanExponent
    linarith
  · unfold ExponentLedger.meanUpdateExponent ExponentLedger.meanExponent
    linarith


-- @@ L4633-4633 verbatim
end GaugeRankMean



-- @@ L4636-4636 verbatim
section MovingSupport


-- @@ L4638-4638 verbatim
open CorrectionState VariableGaugeMean


-- @@ L4640-4640 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L4642-4645 verbatim
/-- Gauge supported, given by `∀ n, SupportedGauge a b ell U (f n)`. -/
def GaugeSupported (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (f : ScalarField (PressureStream.Lift S)) : Prop :=
  ∀ n, SupportedGauge a b ell U (f n)


-- @@ L4647-4647 verbatim
namespace GaugeSupported


-- @@ L4649-4650 verbatim
variable {a b : ℝ} {ell : S → ℝ} {U : Set S}
  {f g : ScalarField (PressureStream.Lift S)}


-- @@ L4652-4655 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem zero : GaugeSupported a b ell U (0 : ScalarField (PressureStream.Lift S)) := by
  intro n x hx hn
  exact (hn rfl).elim


-- @@ L4657-4663 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem add (hf : GaugeSupported a b ell U f) (hg : GaugeSupported a b ell U g) :
    GaugeSupported a b ell U (f + g) := by
  intro n x hx hn
  by_cases hzero : f n x = 0
  · exact hg n x hx (by simpa only [Pi.add_apply, hzero, zero_add] using hn)
  · exact hf n x hx hzero


-- @@ L4665-4668 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem neg (hf : GaugeSupported a b ell U f) : GaugeSupported a b ell U (-f) := by
  intro n x hx hn
  exact hf n x hx (neg_ne_zero.mp hn)


-- @@ L4670-4673 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sub (hf : GaugeSupported a b ell U f) (hg : GaugeSupported a b ell U g) :
    GaugeSupported a b ell U (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg


-- @@ L4675-4679 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem mul_right (hf : GaugeSupported a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    GaugeSupported a b ell U (f * g) := by
  intro n x hx hn
  exact hf n x hx (left_ne_zero_of_mul hn)


-- @@ L4681-4685 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem mul_left (hf : GaugeSupported a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    GaugeSupported a b ell U (g * f) := by
  intro n x hx hn
  exact hf n x hx (right_ne_zero_of_mul hn)


-- @@ L4687-4691 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem smul (hf : GaugeSupported a b ell U f) (t : ℝ) :
    GaugeSupported a b ell U (t • f) := by
  intro n x hx hn
  exact hf n x hx (right_ne_zero_of_mul hn)


-- @@ L4693-4696 verbatim
theorem directional (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (v : PressureStream.Lift S) :
    GaugeSupported a b ell U (fun n x => fderiv ℝ (f n) x v) :=
  fun n => fderiv_apply_supportedGauge hU hell (hf n) (fun _ => v)


-- @@ L4698-4706 verbatim
theorem dr (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.dr f) := by
  have he := (hf.directional hU hell o.eR).add
    ((hf.directional hU hell o.vR).mul_left (fun n x => o.radialFrequency n * o.radialProfile x))
  convert! he using 1
  funext n x
  simp only [Operators.dr, graphDerivative, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring


-- @@ L4708-4711 verbatim
theorem dz (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.dz f) :=
  (hf.directional hU hell o.eZ).mul_left (fun n _ => o.epsilon n)


-- @@ L4713-4717 verbatim
theorem time (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.time f) :=
  ((hf.directional hU hell o.eT).mul_left (fun n _ => o.epsilon n)).neg.add
    ((hf.directional hU hell o.vT).mul_left (fun n _ => o.fastCoefficient n))


-- @@ L4719-4722 verbatim
theorem radialDiv (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) (t : ℝ) :
    GaugeSupported a b ell U (o.radialDiv t f) :=
  (hf.dr hU hell o).add ((hf.mul_left o.invRadius).smul t)


-- @@ L4724-4729 verbatim
theorem viscosity (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) (t : ℝ) :
    GaugeSupported a b ell U (o.viscosity t f) :=
  (((((hf.dr hU hell o).dr hU hell o).add ((hf.dr hU hell o).mul_left o.invRadius)).add
    ((hf.dz hU hell o).dz hU hell o)).sub
      (((hf.mul_left o.invRadius).mul_left o.invRadius).smul t)).mul_left (fun n _ => o.epsilon n)


-- @@ L4731-4731 verbatim
end GaugeSupported


-- @@ L4733-4738 verbatim
/-- Gauge supported triple data, collecting `radial`, `angular`, `axial`. -/
structure GaugeSupportedTriple (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (m : Triple (PressureStream.Lift S)) : Prop where
  radial : GaugeSupported a b ell U m.radial
  angular : GaugeSupported a b ell U m.angular
  axial : GaugeSupported a b ell U m.axial


-- @@ L4740-4744 verbatim
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem GaugeSupportedTriple.updated {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {m h : Triple (PressureStream.Lift S)} (hm : GaugeSupportedTriple a b ell U m)
    (hh : GaugeSupportedTriple a b ell U h) : GaugeSupportedTriple a b ell U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩


-- @@ L4746-4761 verbatim
theorem gr_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) (base m : Triple (PressureStream.Lift S))
    (W : Tensor (PressureStream.Lift S)) (hm : GaugeSupportedTriple a b ell U m)
    (hW : ∀ i j, GaugeSupported a b ell U (W i j)) :
    GaugeSupported a b ell U (MeanIncrementBounds.gr o base m W) := by
  have hrr : GaugeSupported a b ell U (radialRadial base m) :=
    ((hm.radial.mul_left base.radial).smul 2).add (hm.radial.mul_right m.radial)
  have hzr : GaugeSupported a b ell U (axialRadial base m) :=
    ((hm.axial.mul_left base.radial).add (hm.radial.mul_right base.axial)).add
      (hm.radial.mul_right m.axial)
  have htt : GaugeSupported a b ell U (radialAngular base m) :=
    ((hm.angular.mul_left base.angular).smul 2).add (hm.angular.mul_right m.angular)
  exact (((((hm.radial.time hU hell o).add ((hrr.add (hW 0 0)).radialDiv hU hell o 1)).add
    ((hzr.add (hW 2 0)).dz hU hell o)).sub ((htt.add (hW 1 1)).mul_left o.invRadius)).sub
      (hm.radial.viscosity hU hell o 1)).neg


-- @@ L4763-4791 verbatim
/-- The containing fixed annulus supplies smoothness only. The precise
support conclusion retains the same moving physical edges. -/
theorem state_gr_moving_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (ha : 0 < a) (hab : a < b)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point)
    (ho : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple a b (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported a b (qLength coord) U.carrier (u.covariance i j)) :
    SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.gr c) ∧
      GaugeSupported a b (qLength coord) U.carrier (u.gr c) := by
  obtain ⟨a₀, b₀, L, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have contain {f : ScalarField LocalSignedRequest.Point}
      (hf : GaugeSupported a b (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hf n x hx hn).1, (hf n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier u.mean :=
    ⟨⟨hm.radial, contain hms.radial⟩, ⟨hm.angular, contain hms.angular⟩, ⟨hm.axial, contain
        hms.axial⟩⟩
  have hWl (i j) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) :=
    ⟨hW i j, contain (hWs i j)⟩
  refine ⟨(LocalRankDefect.gr_localShell ha₀ U.isOpen hb hml ho u.covariance hWl).smooth, ?_⟩
  exact gr_supportedGauge U.isOpen
    (((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun p hp => U.time_pos p
        hp)).continuousOn)
    c.operators c.base u.mean u.covariance hms hWs



-- @@ L4794-4794 verbatim
end MovingSupport



-- @@ L4797-4797 verbatim
section MovingMeanPressure


-- @@ L4799-4799 verbatim
open CorrectionState VariableGaugeMean LocalSignedRequest


-- @@ L4801-4804 verbatim
variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)


-- @@ L4806-4806 verbatim
include hd hell


-- @@ L4808-4809 verbatim
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L
    hε hεone hL


-- @@ L4811-4845 verbatim
/-- The pressure difference is computed by the same variable-gauge integral.
Both radial-source regularity statements and its class follow from the
actual updated mean and unchanged covariance. -/
theorem reconstructedMeanStage_pressure_change_mem
    (c : Context Point) (u v : State Point) (inc : Triple Point)
    (hme : v.mean = updated u.mean inc) (hce : v.covariance = u.covariance)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H inc)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) inc)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier inc)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance i j)) :
    MeanClass stageStrip H ((reconstructState g c v).pressure - u.pressure) := by
  have huReg := state_gr_moving_regular U ha g.radial.inner_lt_outer c u hop hbase hm hms hW hWs
  have hvReg := state_gr_moving_regular U ha g.radial.inner_lt_outer c v hop hbase
    (by rw [hme]; exact smooth_updated hm him)
    (by rw [hme]; exact hms.updated his)
    (by simpa only [hce] using hW) (by simpa only [hce] using hWs)
  have hcov : ∀ i j, SmoothOn (stageStrip).domain (u.covariance i j) :=
    fun i j n => (hW i j n).mono (fun _ hx => hx.1)
  have hgr : MeanClass stageStrip H (v.gr c - u.gr c) := by
    simpa only [State.gr, hme, hce] using gr_change_mem ho hb hu.velocity hi hH u.covariance hcov hκ
  have hp := reconstructState_pressure_change_class U g ha hd hcL hcR ε L hε hεone hL hell
    c v u hvReg.1 huReg.1 hvReg.2 huReg.2 hgr
  simp only [hfixed] at hp
  exact hp


-- @@ L4847-4875 verbatim
/-- Direct pressure bound for the literal temporal stage. No class of a
pressure source or pressure output is supplied as a hypothesis. -/
theorem gaugeTemporalStage_pressure_change_mem
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H (temporalIncrementState g h index axial c u))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalIncrementState g h index
        axial c u))
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance i j)) :
    MeanClass stageStrip H (gaugeTemporalPressureChange g h index axial c u) := by
  let v := u.addIncrement (temporalIncrementState g h index axial c u) 0 0 0
    ⟨0, 0, temporalAliasState g h index c u⟩
  exact reconstructedMeanStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell c u v
    (temporalIncrementState g h index axial c u) rfl
    (by simp only [v, State.addIncrement, add_zero]; rfl)
    hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs


-- @@ L4877-4904 verbatim
/-- The same integral update for the literal rank stage, with its full
centrifugal source change derived by the nonlinear mean identity. -/
theorem gaugeRankStage_pressure_change_mem
    (r : RankData PressureStream.Plane) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H (rankIncrementState g r axial c u))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (rankIncrementState g r axial c
        u))
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u))
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance i j)) :
    MeanClass stageStrip H (gaugeRankPressureChange g r axial c u) := by
  let v := u.addIncrement (rankIncrementState g r axial c u) 0 0 0 ExcludedErrors.zero
  exact reconstructedMeanStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell c u v
    (rankIncrementState g r axial c u) rfl
    (by simp only [v, State.addIncrement, add_zero]; rfl)
    hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs


-- @@ L4906-4906 verbatim
end MovingMeanPressure



-- @@ L4909-4909 verbatim
section TemporalRegularity


-- @@ L4911-4911 verbatim
open CorrectionState VariableGaugeMean LocalSignedRequest


-- @@ L4913-4923 verbatim
variable {coord : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = qLength coord)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual
        c))


-- @@ L4925-4992 verbatim
include ha hd hell hθ hz hpθ hpz hsz in
/-- Full local smoothness of the actual temporal stream components,
including the axis where the annular support makes the quotients zero. -/
theorem gaugeTemporalIncrement_smooth :
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalIncrementState g h index axial
        c u) := by
  let pot := temporalPotential g h index c u
  have hf : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) pot := by
    intro n
    simpa only [pot, temporalPotential, hell] using
      streamPotential_q_contDiffOn U ha g.radial.inner_lt_outer hd (g.radial.frequency n)
        g.radial.radialDirection
        (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n))
        (temporalAtIndex_supportedGauge h n (index n) (hsz n))
  have hs : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier pot := by
    intro n
    simpa only [pot, temporalPotential, hell] using
      streamPotential_supportedGauge (M := g.radial.frequency n) ha g.radial.inner_lt_outer hd
        (qLength coord) g.radial.radialDirection U.isOpen
        (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs))
        (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n))
        (temporalAtIndex_supportedGauge h n (index n) (hsz n))
  obtain ⟨a, b, L, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha
      g.radial.inner_lt_outer
  have hfShell : LocalRankDefect.LocalShell a b U.carrier pot :=
    ⟨hf, fun n x hx hn => ⟨(hleft _ hx).trans (hs n x hx hn).1,
      (hs n x hx hn).2.trans (hright _ hx)⟩⟩
  constructor
  · intro n
    exact (((contDiffOn_infty_iff_fderiv_of_isOpen (PhysicalMeanDomain.slowDomain_open U.isOpen)).mp
      (hf n)).2.clm_apply contDiffOn_const).neg
  · intro n
    exact temporalAtIndex_contDiffOn h n (index n) U.isOpen (hθ n) (hpθ n)
  · have hrad := hfShell.directional U.isOpen (1, 0)
    have htor := hfShell.directional U.isOpen (0, (0, g.radial.radialDirection))
    have hspeed : SmoothOn (LocalRankDefect.positiveDomain U.carrier)
        (fun n (x : Point) => PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)
            x.1) := by
      intro n x hx
      exact ((PressureStream.physicalSpeed_smooth g.radial.exponent (g.radial.frequency n)
        hx.1.ne').comp x contDiffAt_fst).contDiffWithinAt
    have hprod := htor.coefficient_mul ha₀ U.isOpen hspeed
    have hgraph : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier)
        (fun n => PressureStream.graphDr (PressureStream.physicalSpeed g.radial.exponent
            (g.radial.frequency n))
          (0, g.radial.radialDirection) (pot n)) := by
      have he : (fun n => PressureStream.graphDr (PressureStream.physicalSpeed g.radial.exponent
          (g.radial.frequency n))
          (0, g.radial.radialDirection) (pot n)) =
          (fun n x => fderiv ℝ (pot n) x (1, 0)) +
            (fun n (x : Point) => PressureStream.physicalSpeed g.radial.exponent
                (g.radial.frequency n) x.1) *
              (fun n x => fderiv ℝ (pot n) x (0, (0, g.radial.radialDirection))) := by
        funext n x
        change fderiv ℝ (pot n) x (1, _ • (0, g.radial.radialDirection)) = _
        rw [show (((1 : ℝ), PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)
            x.1 •
            ((0 : PressureStream.Plane), g.radial.radialDirection)) : Point) =
            ((1, (0, (0 : PressureStream.Plane))) : Point) +
            PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n) x.1 •
              ((0, (0, g.radial.radialDirection)) : Point) by simp]
        simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.mul_apply]
        rfl
      rw [he]
      exact hrad.smooth.add hprod.smooth
    intro n
    exact (hgraph n).add (VariableGaugeMean.divideRadius_contDiffOn ha₀ U.isOpen (hf n)
        (hfShell.supported n))


-- @@ L4994-4994 verbatim
end TemporalRegularity



-- @@ L4997-4997 verbatim
section PeriodizedSignedConstruction


-- @@ L4999-4999 verbatim
open CorrectionState VariableGaugeMean LocalSignedRequest


-- @@ L5001-5001 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I : Type}


-- @@ L5003-5031 verbatim
/-- The primitive native data of one signed spatial label. Every copy
uses the same carrier, base, and graph directions. -/
structure PeriodizedSignedParameters (D I : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  /-- Base wave coefficients for the periodized signed correction. -/
  base : LinearWaveBounds.WaveCoefficients (D × ℝ)
  /-- Directions of `PeriodizedSignedParameters`, of type `LinearWaveBounds.GraphDirections (D ×
  ℝ)`. -/
  directions : LinearWaveBounds.GraphDirections (D × ℝ)
  /-- Matrix of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ → SignedWaveUpdate.Mat2`. -/
  matrix : I → ℕ → D × ℝ → SignedWaveUpdate.Mat2
  /-- Target of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ → SignedWaveUpdate.Vec2`. -/
  target : I → ℕ → D × ℝ → SignedWaveUpdate.Vec2
  /-- Mask of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ → ℝ`. -/
  mask : I → ℕ → D × ℝ → ℝ
  /-- Fundamental of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ →
  ProblemStatement.Space`. -/
  fundamental : I → ℕ → D × ℝ → ProblemStatement.Space
  /-- Normal motion of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ →
  ProblemStatement.Space`. -/
  normalMotion : I → ℕ → D × ℝ → ProblemStatement.Space
  /-- Action of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ → ProblemStatement.Space
  →L[ℝ] ProblemStatement.Space`. -/
  action : I → ℕ → D × ℝ → ProblemStatement.Space →L[ℝ] ProblemStatement.Space
  /-- Cutoff of `PeriodizedSignedParameters`, of type `I → ℕ → D × ℝ → ℝ`. -/
  cutoff : I → ℕ → D × ℝ → ℝ
  /-- Angular frequency of `PeriodizedSignedParameters`, of type `ℕ → ℤ`. -/
  angularFrequency : ℕ → ℤ
  /-- Column of `PeriodizedSignedParameters`, of type `Fin 2`. -/
  column : Fin 2


-- @@ L5033-5033 verbatim
namespace PeriodizedSignedParameters

-- @@ L5034-5034 verbatim
variable (p : PeriodizedSignedParameters D I)


-- @@ L5036-5049 verbatim
/-- Native, bundling `base`, `directions`, `matrix`, `target` and the required compatibility
proofs. -/
noncomputable def native (i : I) : SignedParameters D where
  base := p.base
  directions := p.directions
  matrix := p.matrix i
  target := p.target i
  mask := p.mask i
  fundamental := p.fundamental i
  normalMotion := p.normalMotion i
  action := p.action i
  cutoff := p.cutoff i
  angularFrequency := p.angularFrequency
  column := p.column


-- @@ L5051-5059 verbatim
/-- The native fields are evaluated from the signed quotient and projected
homogeneous pressure before the one native cutoff is applied. -/
noncomputable def copyData (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    PeriodizedWaveBounds.CopyData (D × ℝ) I where
  background := p.base
  amplitude n i := ((p.native i).coefficients s request).amplitude n
  pressure n i := ((p.native i).coefficients s request).pressure n
  cutoff n i := p.cutoff i n
  source := fun _ _ => 0


-- @@ L5061-5062 verbatim
theorem copyData_raw (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) (i : I) :
    (p.copyData s request).raw i = (p.native i).coefficients s request := rfl


-- @@ L5064-5069 verbatim
/-- Exact block, constructed using `SignedWaveUpdate.blockOfCoefficients`. -/
noncomputable def exactBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions)
    p.angularFrequency


-- @@ L5071-5075 verbatim
/-- Tangent block, given by `SignedWaveUpdate.blockOfCoefficients (p.copyData s request).common
p.angularFrequency`. -/
noncomputable def tangentBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients (p.copyData s request).common p.angularFrequency


-- @@ L5077-5079 verbatim
/-- Curl block, given by `subBlock (p.exactBlock s request) (p.tangentBlock s request)`. -/
noncomputable def curlBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D := subBlock (p.exactBlock s request) (p.tangentBlock s request)


-- @@ L5081-5088 verbatim
/-- Good block, constructed using `SignedWaveUpdate.coefficientBlock`. -/
noncomputable def goodBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0))
      p.angularFrequency
    (fun n x => (p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s)
        p.directions n (x,0))
    (fun _ _ => 0)


-- @@ L5090-5095 verbatim
/-- Gaussian block, constructed using `SignedWaveUpdate.coefficientBlock`. -/
noncomputable def gaussianBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0))
      p.angularFrequency
    (fun n x => (p.copyData s request).globalGaussian p.directions n (x,0)) (fun _ _ => 0)


-- @@ L5097-5098 verbatim
theorem exact_tangent_carrier (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (p.exactBlock s request) (p.tangentBlock s request) := ⟨rfl, rfl, rfl⟩


-- @@ L5100-5104 verbatim
theorem exactBlock_split (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).oscillation =
      (p.tangentBlock s request).oscillation + (p.curlBlock s request).oscillation := by
  rw [curlBlock, subBlock_oscillation _ _ (p.exact_tangent_carrier s request)]
  abel


-- @@ L5106-5107 verbatim
theorem exactBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


-- @@ L5109-5110 verbatim
theorem tangentBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.tangentBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


-- @@ L5112-5113 verbatim
theorem gaussianBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.gaussianBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


-- @@ L5115-5118 verbatim
theorem gaussian_source_zero (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.copyData s request).globalGaussian p.directions = (p.copyData s request).globalTail
        p.directions :=
  (p.copyData s request).globalGaussian_of_source_zero p.directions rfl


-- @@ L5120-5120 verbatim
end PeriodizedSignedParameters

-- @@ L5121-5121 verbatim
end PeriodizedSignedConstruction


-- @@ L5123-5123 verbatim
section ParticularConstruction


-- @@ L5125-5125 verbatim
open CorrectionState VariableGaugeMean


-- @@ L5127-5127 verbatim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L5129-5147 verbatim
/-- Primitive per-band data of the actual complex Volterra inverse. The
interval may vary with the physical clock. No solved field is stored. -/
structure ParticularParameters (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  /-- Tangent of `ParticularParameters`, of type `ℤ → ℕ → CommonCoverSolve.TangentData P
  ProblemStatement.Space`. -/
  tangent : ℤ → ℕ → CommonCoverSolve.TangentData P ProblemStatement.Space
  /-- Geometry of `ParticularParameters`, of type `ℕ → CommonCoverSolve.Geometry`. -/
  geometry : ℕ → CommonCoverSolve.Geometry
  /-- Length of `ParticularParameters`, of type `ℕ → ℝ`. -/
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  /-- Cutoff of `ParticularParameters`, of type `ℕ → TorusInverse.Plane → ℝ`. -/
  cutoff : ℕ → TorusInverse.Plane → ℝ
  /-- Background of `ParticularParameters`, of type `LinearWaveBounds.WaveCoefficients ((P × ℝ)
  × TorusInverse.Plane)`. -/
  background : LinearWaveBounds.WaveCoefficients ((P × ℝ) × TorusInverse.Plane)
  /-- Directions of `ParticularParameters`, of type `LinearWaveBounds.GraphDirections ((P × ℝ) ×
  TorusInverse.Plane)`. -/
  directions : LinearWaveBounds.GraphDirections ((P × ℝ) × TorusInverse.Plane)


-- @@ L5149-5149 verbatim
namespace ParticularParameters

-- @@ L5150-5150 verbatim
variable (p : ParticularParameters P)


-- @@ L5152-5171 verbatim
/-- Copy data, bundling `background`, `amplitude`, `pressure`, `cutoff` and the required
compatibility proofs. -/
noncomputable def copyData (c : Context (P × TorusInverse.Plane)) (u : State (P ×
    TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (j : ℤ) :
    PeriodizedWaveBounds.CopyData ((P × ℝ) × TorusInverse.Plane) TorusInverse.Frequency where
  background := ParticularWaveAssembly.actualCarrier p.background b j
  amplitude n k := (ParticularWaveBounds.complexCopyCoefficients
    (ParticularWaveAssembly.actualCarrier p.background b j)
    (fun n => ParticularWaveAssembly.angleTangent (p.tangent j n))
    (ParticularWaveAssembly.sourceFamily c u b G A j) p.geometry (fun _ => k) p.length
        p.length_pos).amplitude n
  pressure n k := (ParticularWaveBounds.complexCopyCoefficients
    (ParticularWaveAssembly.actualCarrier p.background b j)
    (fun n => ParticularWaveAssembly.angleTangent (p.tangent j n))
    (ParticularWaveAssembly.sourceFamily c u b G A j) p.geometry (fun _ => k) p.length
        p.length_pos).pressure n
  cutoff n k x := p.cutoff n ((p.geometry n).coordinates k x.2)
  source := ParticularWaveAssembly.sourceFamily c u b G A j


-- @@ L5173-5178 verbatim
/-- Native strip, given by `ParticularWaveBounds.reindexStrip
ParticularWaveAssembly.angleShuffle.symm (HarmonicWaveInteraction.productStrip s)`. -/
noncomputable def nativeStrip (s : StripData (P × TorusInverse.Plane)) :
    StripData ((P × ℝ) × TorusInverse.Plane) :=
  ParticularWaveBounds.reindexStrip ParticularWaveAssembly.angleShuffle.symm
      (HarmonicWaveInteraction.productStrip s)


-- @@ L5180-5186 verbatim
/-- Wave, given by `(p.copyData c u b G A j).commonCorrected (nativeStrip s) p.directions`. -/
noncomputable def wave (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (j : ℤ) :
    LinearWaveBounds.WaveCoefficients ((P × ℝ) × TorusInverse.Plane) :=
  (p.copyData c u b G A j).commonCorrected (nativeStrip s) p.directions


-- @@ L5188-5196 verbatim
/-- Update block, constructed using `ParticularWaveAssembly.assembledBlock`. -/
noncomputable def updateBlock (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P
        × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.wave s c u b G A j).amplitude n (ParticularWaveAssembly.angleShuffle (x,0)))
    (fun j n x => (p.wave s c u b G A j).pressure n (ParticularWaveAssembly.angleShuffle (x,0)))


-- @@ L5198-5206 verbatim
/-- Good block, constructed using `ParticularWaveAssembly.assembledBlock`. -/
noncomputable def goodBlock (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P
        × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n
      (ParticularWaveAssembly.angleShuffle (x,0))) (fun _ _ _ => 0)


-- @@ L5208-5216 verbatim
/-- Gaussian block, constructed using `ParticularWaveAssembly.assembledBlock`. -/
noncomputable def gaussianBlock
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P
        × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.copyData c u b G A j).globalGaussian p.directions n
      (ParticularWaveAssembly.angleShuffle (x,0))) (fun _ _ _ => 0)


-- @@ L5218-5223 verbatim
theorem updateBlock_band (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) :
    (p.updateBlock s c u b G A N).BandLimited N := ParticularWaveAssembly.assembledBlock_band _ _ _
        _ _ _


-- @@ L5225-5230 verbatim
theorem gaussianBlock_band
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) :
    (p.gaussianBlock c u b G A N).BandLimited N := ParticularWaveAssembly.assembledBlock_band _ _ _
        _ _ _


-- @@ L5232-5238 verbatim
theorem source_eq_residual (c : Context (P × TorusInverse.Plane)) (u : State (P ×
    TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (j : ℤ) (n : ℕ)
    (x : (P × ℝ) × TorusInverse.Plane) (i : Fin 3) :
    (p.copyData c u b G A j).source n x i =
      (HarmonicResidual.residualBlock c u b G A).velocity n i j (x.1.1,x.2) := rfl


-- @@ L5240-5240 verbatim
end ParticularParameters

-- @@ L5241-5241 verbatim
end ParticularConstruction


-- @@ L5243-5243 verbatim
section ActualCycle


-- @@ L5245-5245 verbatim
open CorrectionState VariableGaugeMean


-- @@ L5247-5248 verbatim
/-- Cycle point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev CyclePoint := LocalSignedRequest.Point

-- @@ L5249-5250 verbatim
/-- Cycle slow: an abbreviation for `ℝ × PressureStream.Plane`. -/
abbrev CycleSlow := ℝ × PressureStream.Plane


-- @@ L5252-5254 verbatim
/-- Cycle assoc, given by `ParticularWaveBounds.liftAssoc PressureStream.Plane`. -/
noncomputable def cycleAssoc : CyclePoint ≃ₗᵢ[ℝ] (CycleSlow × TorusInverse.Plane) :=
  ParticularWaveBounds.liftAssoc PressureStream.Plane


-- @@ L5256-5269 verbatim
/-- Finite labeled coefficient data of the current fields. Correct
representation is a separate invariant, not part of the construction. -/
structure CycleCoefficients (ι : Type) where
  /-- Label type of `CycleCoefficients`, of type `ℕ → Finset ι`. -/
  labels : ℕ → Finset ι
  /-- Blocks of `CycleCoefficients`, of type `ι → HarmonicBlock CyclePoint`. -/
  blocks : ι → HarmonicBlock CyclePoint
  /-- Gaussian residual coefficients indexed by harmonic label. -/
  gaussian : ι → HarmonicResidual.BlockCoefficients CyclePoint
  /-- Alias coefficients of `CycleCoefficients`, of type `ι → HarmonicResidual.BlockCoefficients
  CyclePoint`. -/
  aliasCoefficients : ι → HarmonicResidual.BlockCoefficients CyclePoint
  /-- Residual band of `CycleCoefficients`, of type `ℕ`. -/
  residualBand : ℕ


-- @@ L5271-5294 verbatim
/-- Fixed geometric and primitive solver data for an actual correction
cycle. The only state-dependent source is computed inside the stages. -/
structure CycleParameters (ι : Type) where
  /-- Gauge of `CycleParameters`, of type `GaugeData PressureStream.Plane`. -/
  gauge : GaugeData PressureStream.Plane
  /-- Strip of `CycleParameters`, of type `StripData CyclePoint`. -/
  strip : StripData CyclePoint
  /-- Patch of `CycleParameters`, of type `SignedStressPrimitive.Patch`. -/
  patch : SignedStressPrimitive.Patch
  /-- Coordinate of `CycleParameters`, of type `ℝ`. -/
  coordinate : ℝ
  /-- Time exponent of `CycleParameters`, of type `ℝ`. -/
  timeExponent : ℝ
  /-- Common index of `CycleParameters`, of type `ℕ → ℕ`. -/
  commonIndex : ℕ → ℕ
  /-- Axial of `CycleParameters`, of type `PressureStream.Plane × PressureStream.Plane`. -/
  axial : PressureStream.Plane × PressureStream.Plane
  /-- Particular of `CycleParameters`, of type `ι → ParticularParameters CycleSlow`. -/
  particular : ι → ParticularParameters CycleSlow
  /-- Signed of `CycleParameters`, of type `ι → PeriodizedSignedParameters CyclePoint
  TorusInverse.Frequency`. -/
  signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency
  /-- Rank of `CycleParameters`, of type `RankData PressureStream.Plane`. -/
  rank : RankData PressureStream.Plane


-- @@ L5296-5296 verbatim
namespace CycleParameters

-- @@ L5297-5298 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L5300-5307 verbatim
/-- Particular block, constructed using `StateReindex.block`. -/
noncomputable def particularBlock (l : ι) : HarmonicBlock CyclePoint :=
  StateReindex.block cycleAssoc ((p.particular l).updateBlock
    (ParticularWaveBounds.reindexStrip cycleAssoc.symm p.strip)
    (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
    (StateReindex.block cycleAssoc.symm (v.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.aliasCoefficients l)) v.residualBand)


-- @@ L5309-5315 verbatim
/-- Particular gaussian block, constructed using `StateReindex.block`. -/
noncomputable def particularGaussianBlock (l : ι) : HarmonicBlock CyclePoint :=
  StateReindex.block cycleAssoc ((p.particular l).gaussianBlock
    (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
    (StateReindex.block cycleAssoc.symm (v.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.aliasCoefficients l)) v.residualBand)


-- @@ L5317-5320 verbatim
/-- Particular velocity, given by `LabelSumBounds.fieldSum v.labels (fun l => (p.particularBlock
v c u l).oscillation)`. -/
noncomputable def particularVelocity : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.particularBlock v c u l).oscillation)


-- @@ L5322-5325 verbatim
/-- Particular pressure, defined pointwise by `∑ l ∈ v.labels n, (p.particularBlock v c u
l).oscillatoryPressure n x`. -/
noncomputable def particularPressure : OscillatoryScalar CyclePoint :=
  fun n x => ∑ l ∈ v.labels n, (p.particularBlock v c u l).oscillatoryPressure n x


-- @@ L5327-5330 verbatim
/-- Particular gaussian, given by `LabelSumBounds.fieldSum v.labels (fun l =>
(p.particularGaussianBlock v c u l).oscillation)`. -/
noncomputable def particularGaussian : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.particularGaussianBlock v c u l).oscillation)


-- @@ L5332-5336 verbatim
/-- After particular, given by `gaugeWaveStage p.gauge c u (p.particularVelocity v c u)
(p.particularPressure v c u) ⟨0, p.particularGaussian v c u, 0⟩`. -/
noncomputable def afterParticular : State CyclePoint :=
  gaugeWaveStage p.gauge c u (p.particularVelocity v c u) (p.particularPressure v c u)
    ⟨0, p.particularGaussian v c u, 0⟩


-- @@ L5338-5341 verbatim
/-- The signed request is recomputed from the actual state after the
particular solve; it is not supplied independently. -/
noncomputable def signedRequest : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2 :=
  LocalSignedRequest.fullRequest p.strip p.patch p.coordinate c (p.afterParticular v c u)


-- @@ L5343-5345 verbatim
/-- Signed block, given by `(p.signed l).exactBlock p.strip (p.signedRequest v c u)`. -/
noncomputable def signedBlock (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).exactBlock p.strip (p.signedRequest v c u)


-- @@ L5347-5350 verbatim
/-- Signed gaussian block, given by `(p.signed l).gaussianBlock p.strip (p.signedRequest v c
u)`. -/
noncomputable def signedGaussianBlock (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).gaussianBlock p.strip (p.signedRequest v c u)


-- @@ L5352-5355 verbatim
/-- Signed velocity, given by `LabelSumBounds.fieldSum v.labels (fun l => (p.signedBlock v c u
l).oscillation)`. -/
noncomputable def signedVelocity : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.signedBlock v c u l).oscillation)


-- @@ L5357-5360 verbatim
/-- Signed pressure, defined pointwise by `∑ l ∈ v.labels n, (p.signedBlock v c u
l).oscillatoryPressure n x`. -/
noncomputable def signedPressure : OscillatoryScalar CyclePoint :=
  fun n x => ∑ l ∈ v.labels n, (p.signedBlock v c u l).oscillatoryPressure n x


-- @@ L5362-5365 verbatim
/-- Signed gaussian, given by `LabelSumBounds.fieldSum v.labels (fun l => (p.signedGaussianBlock
v c u l).oscillation)`. -/
noncomputable def signedGaussian : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.signedGaussianBlock v c u l).oscillation)


-- @@ L5367-5370 verbatim
/-- After signed, constructed using `gaugeWaveStage`. -/
noncomputable def afterSigned : State CyclePoint :=
  gaugeWaveStage p.gauge c (p.afterParticular v c u)
    (p.signedVelocity v c u) (p.signedPressure v c u) ⟨0, p.signedGaussian v c u, 0⟩


-- @@ L5372-5375 verbatim
/-- Temporal increment, given by `temporalIncrementState p.gauge p.timeExponent p.commonIndex
p.axial c (p.afterSigned v c u)`. -/
noncomputable def temporalIncrement : Triple CyclePoint :=
  temporalIncrementState p.gauge p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)


-- @@ L5377-5380 verbatim
/-- After temporal, given by `temporalStageState p.gauge p.timeExponent p.commonIndex p.axial c
(p.afterSigned v c u)`. -/
noncomputable def afterTemporal : State CyclePoint :=
  temporalStageState p.gauge p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)


-- @@ L5382-5385 verbatim
/-- Rank increment, given by `rankIncrementState p.gauge p.rank p.axial c (p.afterTemporal v c
u)`. -/
noncomputable def rankIncrement : Triple CyclePoint :=
  rankIncrementState p.gauge p.rank p.axial c (p.afterTemporal v c u)


-- @@ L5387-5389 verbatim
/-- After rank, given by `rankStageState p.gauge p.rank p.axial c (p.afterTemporal v c u)`. -/
noncomputable def afterRank : State CyclePoint :=
  rankStageState p.gauge p.rank p.axial c (p.afterTemporal v c u)


-- @@ L5391-5394 verbatim
/-- Four literal updates followed by replacement of the obsolete radial
pressure alias. The current radial alias is recorded exactly once. -/
noncomputable def next : State CyclePoint :=
  gaugeRefreshPressureAlias p.gauge c u (p.afterRank v c u)


-- @@ L5396-5399 verbatim
/-- Final block, given by `addBlock (addBlock (v.blocks l) (p.particularBlock v c u l))
(p.signedBlock v c u l)`. -/
noncomputable def finalBlock (l : ι) : HarmonicBlock CyclePoint :=
  addBlock (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l)


-- @@ L5401-5402 verbatim
theorem particularBlock_band (l : ι) : (p.particularBlock v c u l).BandLimited v.residualBand :=
  StateReindex.block_bandLimited cycleAssoc ((p.particular l).updateBlock_band _ _ _ _ _ _ _)


-- @@ L5404-5406 verbatim
theorem particularGaussianBlock_band (l : ι) :
    (p.particularGaussianBlock v c u l).BandLimited v.residualBand :=
  StateReindex.block_bandLimited cycleAssoc ((p.particular l).gaussianBlock_band _ _ _ _ _ _)


-- @@ L5408-5411 verbatim
theorem finalBlock_band {N : ℕ} (hb : ∀ l, (v.blocks l).BandLimited N) (l : ι) :
    (p.finalBlock v c u l).BandLimited (max (max N v.residualBand) 1) :=
  twoWaveUpdates_band (hb l) (p.particularBlock_band v c u l)
    ((p.signed l).exactBlock_band p.strip (p.signedRequest v c u))


-- @@ L5413-5418 verbatim
theorem next_oscillation :
    (p.next v c u).oscillation = u.oscillation + p.particularVelocity v c u + p.signedVelocity v c
        u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, add_zero]


-- @@ L5420-5425 verbatim
theorem next_oscillatoryPressure :
    (p.next v c u).oscillatoryPressure =
      u.oscillatoryPressure + p.particularPressure v c u + p.signedPressure v c u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, add_zero]


-- @@ L5427-5435 verbatim
theorem next_mean :
    (p.next v c u).mean = updated (updated u.mean (p.temporalIncrement v c u)) (p.rankIncrement v c
        u) := by
  change updated (updated (p.afterSigned v c u).mean (p.temporalIncrement v c u))
    (p.rankIncrement v c u) = _
  have he : (p.afterSigned v c u).mean = u.mean := by
    simp only [afterSigned, afterParticular, gaugeWaveStage, reconstructState, State.addIncrement,
      updated_zeroTriple]
  rw [he]


-- @@ L5437-5440 verbatim
theorem next_base_error : (p.next v c u).errors.base = u.errors.base := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, ExcludedErrors.add, ExcludedErrors.zero, add_zero]


-- @@ L5442-5447 verbatim
theorem next_gaussian_error :
    (p.next v c u).errors.gaussian =
      u.errors.gaussian + p.particularGaussian v c u + p.signedGaussian v c u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, ExcludedErrors.add, ExcludedErrors.zero, add_zero]


-- @@ L5449-5460 verbatim
theorem next_alias_error :
    (p.next v c u).errors.aliasError = u.errors.aliasError +
      temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) +
      (pressureAliasState p.gauge c (p.afterRank v c u) - pressureAliasState p.gauge c u) := by
  change (p.afterRank v c u).errors.aliasError + _ = _
  have he : (p.afterRank v c u).errors.aliasError = u.errors.aliasError +
      temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) := by
    simp only [afterRank, rankStageState, afterTemporal, temporalStageState, afterSigned,
        afterParticular,
      gaugeWaveStage, reconstructState, State.addIncrement, ExcludedErrors.add,
          ExcludedErrors.zero, add_zero]
  rw [he]


-- @@ L5462-5463 verbatim
theorem next_reconstructed :
    (reconstructState p.gauge c (p.next v c u)).pressure = (p.next v c u).pressure := rfl


-- @@ L5465-5465 verbatim
end CycleParameters

-- @@ L5466-5466 verbatim
end ActualCycle




-- @@ L5470-5470 verbatim
section ConstructedTemporalStage


-- @@ L5472-5472 verbatim
open CorrectionState VariableGaugeMean LocalSignedRequest


-- @@ L5474-5477 verbatim
variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)


-- @@ L5479-5479 verbatim
include hd hell

-- @@ L5480-5481 verbatim
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L
    hε hεone hL


-- @@ L5483-5544 verbatim
/-- Full mean-step bound for the constructed temporal inverse and stream.
The increment and pressure-change classes are conclusions. -/
theorem gaugeTemporalStage_constructed
    {h H κ β : ℝ} (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (index : ℕ → ℕ) (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point)
    (heps : c.operators.epsilon = ε)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 +
        h))
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10) (hβ : β ≤ H + 1 - 2 * κ)
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsθ : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.thetaResidual
        c))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual
        c))
    (hcθ : MeanClass stageStrip H (u.thetaResidual c))
    (hcz : MeanClass stageStrip H (u.axialResidual c))
    (hbarθ : MeanClass stageStrip β (meanBar (u.thetaResidual c)))
    (hbarz : MeanClass stageStrip β (meanBar (u.axialResidual c))) :
    IncrementBounds stageStrip H (temporalIncrementState g h index axial c u) ∧
    MeanClass stageStrip H (gaugeTemporalPressureChange g h index axial c u) ∧
    CorrectionState.CumulativeBounds stageStrip (temporalStageState g h index axial c u) ∧
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalStageState g h index axial c
        u).mean ∧
    GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalStageState g h index axial c u).mean ∧
    MeanClass stageStrip β ((temporalStageState g h index axial c u).thetaResidual c) ∧
    MeanClass stageStrip β (fun n x => (temporalStageState g h index axial c u).axialResidual c n x
        -
      temporalAliasState g h index c u n (x,0) 2) := by
  obtain ⟨hR, hT, hZ⟩ := temporalIncrementState_classes U g ha hd hcL hcR ε L hε hεone hL hell
    hh hscale index gap hgap axial c u heps hθ hz hpθ hpz hsz hcθ hcz
  have hi : IncrementBounds stageStrip H (temporalIncrementState g h index axial c u) := ⟨hR, hT,
      hZ⟩
  have him := gaugeTemporalIncrement_smooth U g ha hd hell h index axial c u hθ hz hpθ hpz hsz
  have his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u) := by
    have hs n := temporalIncrementState_supportedGauge U g ha hd hell c u h index axial n
      (hz n) (hpz n) (hsz n) (hsθ n)
    exact ⟨fun n => (hs n).1, fun n => (hs n).2.1, fun n => (hs n).2.2⟩
  have hp := gaugeTemporalStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell
    h index axial c u hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs
  have hgain := gaugeTemporalStage_mean_gain (s := stageStrip) U.isOpen (fun _ hx => hx.1) g h
      index axial c u
    hv hfast ho hb hu hi hp (fun i j n => (hW i j n).mono (fun _ hx => hx.1))
    hbarθ hbarz hθ hz hpθ hpz hH hβ
  exact ⟨hi, hp, gaugeTemporalStage_cumulative g h index axial c u hu hi hp hH,
    smooth_updated hm him, hms.updated his, hgain⟩


-- @@ L5546-5546 verbatim
end ConstructedTemporalStage

-- @@ L5547-5547 verbatim
section ConstructedRankStage


-- @@ L5549-5549 verbatim
open CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L5550-5554 verbatim
variable {coord cL cR A B : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (r : RankData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)


-- @@ L5556-5556 verbatim
include hd hell

-- @@ L5557-5558 verbatim
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L
    hε hεone hL


-- @@ L5560-5632 verbatim
/-- The actual rank increment and its pressure change are derived from the
measured debt. The previous temporal alias stays subtracted. -/
theorem gaugeRankStage_constructed
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    {H κ β : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10) (hβ : β ≤ H + 1 - 2 * κ)
    (hfast : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.covariance i j))
    (hdebt : UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone
        hL)
      H (debt c u))
    (aliasField : ScalarField Point)
    (hθ : MeanClass stageStrip β (u.thetaResidual c))
    (hz : MeanClass stageStrip β (u.axialResidual c - aliasField)) :
    IncrementBounds stageStrip H (rankIncrementState g r axial c u) ∧
    MeanClass stageStrip H (gaugeRankPressureChange g r axial c u) ∧
    CorrectionState.CumulativeBounds stageStrip (rankStageState g r axial c u) ∧
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (rankStageState g r axial c u).mean ∧
    GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankStageState g r axial c u).mean ∧
    MeanClass stageStrip β ((rankStageState g r axial c u).thetaResidual c) ∧
    MeanClass stageStrip β ((rankStageState g r axial c u).axialResidual c - aliasField) := by
  have heps : BandBound stageStrip 1 c.operators.epsilon := by
    rw [ho.epsilon_eq]
    simpa only [Real.rpow_one] using bandBound_rpow stageStrip 1
  have hi := RankStateBounds.rankIncrementState_bounds U g r ha hcL hcR ε L hε hεone hL
    c u hg hparam hB hleft hright axial heps hdebt
  obtain ⟨a, b, L₀, ha₀, hab, _, _, hLo, hHi, _⟩ := qLength_reference_bounds U ha
      g.radial.inner_lt_outer
  have hleft₀ (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : a ≤ r.length n x * r.inner
      := by
    rw [hparam.length n x hx]
    exact (hLo x hx).trans (mul_le_mul_of_nonneg_left hleft.le
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x hx)).le)
  have hright₀ (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ b
      := by
    rw [hparam.length n x hx]
    exact (mul_le_mul_of_nonneg_left hright.le
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x hx)).le).trans (hHi x hx)
  have hil := hg.increment_localTriple ha₀ hab U.isOpen hleft₀ hright₀ axial
  have his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u) := by
    have hsup n := hg.increment_supportedGauge ha₀ hab U.isOpen hleft₀ hright₀ axial n
    have enlarge {f : Point → ℝ} (n : ℕ) (hf : SupportedGauge r.inner r.outer (r.length n)
        U.carrier f) :
        SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier f := by
      intro x hx hn
      have hs := hf x hx hn
      rw [hparam.length n x.2.1 hx] at hs
      have hq := (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x.2.1 hx)).le
      exact ⟨(mul_le_mul_of_nonneg_left hleft.le hq).trans hs.1,
        hs.2.trans (mul_le_mul_of_nonneg_left hright.le hq)⟩
    exact ⟨fun n => enlarge n (hsup n).1, fun n => enlarge n (hsup n).2.1,
      fun n => enlarge n (hsup n).2.2⟩
  have hp := gaugeRankStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell
    r axial c u hfixed hH hκ ho hb hu hi hop hbase hm hil.smooth hms his hW hWs
  have hgain := gaugeRankStage_mean_gain (s := stageStrip) U.isOpen (fun _ hx => hx.1) g r axial c
      u hg ha₀ hab
    hleft₀ hright₀ (TorusInverse.vector .temporal) hfast ho hb hu hi hp
    (fun i j n => (hW i j n).mono (fun _ hx => hx.1)) aliasField hθ hz hH hβ
  exact ⟨hi, hp, gaugeRankStage_cumulative g r axial c u hu hi hp hH,
    smooth_updated hm hil.smooth, hms.updated his, hgain⟩


-- @@ L5634-5634 verbatim
end ConstructedRankStage



-- @@ L5637-5637 verbatim
section CycleMassPreservation


-- @@ L5639-5639 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L5640-5640 verbatim
open scoped ContDiff BigOperators


-- @@ L5642-5642 verbatim
namespace CycleParameters

-- @@ L5643-5644 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L5646-5647 verbatim
theorem afterParticular_mean : (p.afterParticular v c u).mean = u.mean :=
  gaugeWaveStage_mean _ _ _ _ _ _


-- @@ L5649-5650 verbatim
theorem afterSigned_mean : (p.afterSigned v c u).mean = u.mean :=
  (gaugeWaveStage_mean _ _ _ _ _ _).trans (p.afterParticular_mean v c u)


-- @@ L5652-5728 verbatim
/-- Both actual conserved masses survive all four stages. All radial
integrals are evaluated on the valid local slow region. -/
theorem next_preserve_masses {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
        u.mean)
    (hθ : ∀ n, ContDiffOn ℝ ∞ ((p.afterSigned v c u).thetaResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ ((p.afterSigned v c u).axialResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((p.afterSigned v c u).thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((p.afterSigned v c u).axialResidual c n))
    (hsθ : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      ((p.afterSigned v c u).thetaResidual c))
    (hsz : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      ((p.afterSigned v c u).axialResidual c))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c (p.afterTemporal v c u))
    (hrlength : ∀ n x, x ∈ U.carrier → p.rank.length n x = qLength coord x)
    (hleft : p.gauge.radial.inner ≤ p.rank.inner) (hright : p.rank.outer ≤ p.gauge.radial.outer)
    (n : ℕ) {x : PressureStream.Plane} (hx : x ∈ U.carrier) :
    radialMoment 2 (p.next v c u).mean.angular n x = radialMoment 2 u.mean.angular n x ∧
    radialMoment 1 (p.next v c u).mean.axial n x = radialMoment 1 u.mean.axial n x := by
  have hmid : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (p.afterSigned v c u).mean :=
      by
    rw [p.afterSigned_mean v c u]
    exact hm
  have hi := gaugeTemporalIncrement_smooth U p.gauge ha hd hell p.timeExponent p.commonIndex p.axial
    c (p.afterSigned v c u) hθ hz hpθ hpz hsz
  have him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (p.afterTemporal v c u).mean :=
    smooth_updated hmid hi
  have his : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
      U.carrier
      (p.temporalIncrement v c u) := by
    have hs k := temporalIncrementState_supportedGauge U p.gauge ha hd hell c (p.afterSigned v c u)
      p.timeExponent p.commonIndex p.axial k (hz k) (hpz k) (hsz k) (hsθ k)
    exact ⟨fun k => (hs k).1, fun k => (hs k).2.1, fun k => (hs k).2.2⟩
  have hmidd : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
      U.carrier
      (p.afterSigned v c u).mean := by
    rw [p.afterSigned_mean v c u]
    exact hms
  have hmids : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
      U.carrier
      (p.afterTemporal v c u).mean := hmidd.updated his
  have ht := GaugeMassPreservation.temporalStage_preserve_masses_on U p.gauge ha hd hell
    p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)
    (fun k => (hmid.angular k).continuousOn) (fun k => (hmid.axial k).continuousOn)
    hθ hz hpθ hpz hsz n hx
  change radialMoment 2 (p.afterTemporal v c u).mean.angular n x =
      radialMoment 2 (p.afterSigned v c u).mean.angular n x ∧
    radialMoment 1 (p.afterTemporal v c u).mean.axial n x =
      radialMoment 1 (p.afterSigned v c u).mean.axial n x at ht
  rw [p.afterSigned_mean v c u] at ht
  obtain ⟨a, b, L, ha₀, hab, _, _, hLo, hHi, _⟩ := qLength_reference_bounds U ha
      p.gauge.radial.inner_lt_outer
  have hrl (k : ℕ) (y : PressureStream.Plane) (hy : y ∈ U.carrier) : a ≤ p.rank.length k y *
      p.rank.inner := by
    rw [hrlength k y hy]
    exact (hLo y hy).trans (mul_le_mul_of_nonneg_left hleft
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos y hy)).le)
  have hrr (k : ℕ) (y : PressureStream.Plane) (hy : y ∈ U.carrier) : p.rank.length k y *
      p.rank.outer ≤ b := by
    rw [hrlength k y hy]
    exact (mul_le_mul_of_nonneg_left hright
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos y hy)).le).trans (hHi y hy)
  have localize {f : ScalarField Point}
      (hf : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier f) :
      ∀ k, PhysicalMeanDomain.SupportedOn a b U.carrier (f k) := by
    intro k y hy hn
    exact ⟨(hLo _ hy).trans (hf k y hy hn).1, (hf k y hy hn).2.trans (hHi _ hy)⟩
  have hml : LocalRankDefect.LocalTriple a b U.carrier (p.afterTemporal v c u).mean :=
    ⟨⟨him.radial, localize hmids.radial⟩, ⟨him.angular, localize hmids.angular⟩,
      ⟨him.axial, localize hmids.axial⟩⟩
  have hr := hg.preserve_masses ha₀ hab U.isOpen hrl hrr p.axial hml n hx
  exact ⟨hr.1.trans ht.1, hr.2.trans ht.2⟩


-- @@ L5730-5730 verbatim
end CycleParameters


-- @@ L5732-5732 verbatim
end CycleMassPreservation


-- @@ L5734-5734 verbatim
section CycleMeanCompletion


-- @@ L5736-5736 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L5737-5737 verbatim
open scoped ContDiff BigOperators


-- @@ L5739-5739 verbatim
namespace CycleParameters

-- @@ L5740-5746 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)
    {coord cL cR A B : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, p.gauge.length n = qLength coord)


-- @@ L5748-5748 verbatim
include hd hell

-- @@ L5749-5750 verbatim
local notation "stageStrip" => movingStripData U p.gauge.radial.inner p.gauge.radial.outer cL cR ha
    hcL hcR ε L hε hεone hL

-- @@ L5751-5752 verbatim
local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone
    hL

-- @@ L5753-5753 verbatim
local notation "signedState" => p.afterSigned v c u

-- @@ L5754-5754 verbatim
local notation "temporalState" => p.afterTemporal v c u


-- @@ L5756-5852 verbatim
/-- The two actual mean stages complete the `σ+1/10` mean and debt gains.
Every increment and pressure-change estimate is derived internally from the
post-signed residuals and measured debts. -/
theorem finish_mean_stages {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (hh : 0 ≤ p.timeExponent) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex p.timeExponent n ≤ p.commonIndex n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ p.commonIndex n * ChartScales.Q n ^ (1 + p.timeExponent))
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hsigned : CorrectionState.CumulativeBounds stageStrip signedState)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (signedState).mean)
    (hms : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
        (signedState).mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((signedState).covariance i j))
    (hWs : ∀ i j, GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
        U.carrier ((signedState).covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ ((signedState).thetaResidual c n) (PhysicalMeanDomain.slowDomain
        U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ ((signedState).axialResidual c n) (PhysicalMeanDomain.slowDomain
        U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).axialResidual c n))
    (hsθ : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
        ((signedState).thetaResidual c))
    (hsz : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
        ((signedState).axialResidual c))
    (hcθ : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).thetaResidual c))
    (hcz : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).axialResidual c))
    (hbarθ : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).thetaResidual c)))
    (hbarz : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).axialResidual c)))
    (hdebt : ∀ i : Fin 3, UnweightedClass slowStrip (1 + σ - 2 * κ)
      (fun n x => debt c signedState n x i))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c temporalState)
    (hparam : RankStateBounds.NormalizedParameters coord A B p.rank U.carrier) (hB : B ≠ 0)
    (hleft : p.gauge.radial.inner < p.rank.inner) (hright : p.rank.outer < p.gauge.radial.outer) :
    CorrectionState.CumulativeBounds stageStrip (p.next v c u) ∧
    DefectBounds slowStrip (σ + 1 / 10) c (p.next v c u) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10)) ((p.next v c u).thetaResidual c) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10))
      ((p.next v c u).axialResidual c -
        fun n x => temporalAliasState p.gauge p.timeExponent p.commonIndex c signedState n (x,0) 2)
            := by
  have hH : 9 / 10 ≤ 1 + σ - 2 * κ := by linarith
  have hκ : 2 * κ ≤ 9 / 10 := by linarith
  have hβ : 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 1 - 2 * κ := by linarith
  obtain ⟨hi, hp, htCum, htSmooth, htSupport, htTheta, htAxial⟩ :=
    gaugeTemporalStage_constructed U p.gauge ha hd hcL hcR ε L hε hεone hL hell
      hh hscale p.commonIndex gap hgap p.axial c signedState ho.epsilon_eq hv hfast rfl
      hH hκ hβ ho hb hsigned hop hbase hm hms hW hWs hθ hz hpθ hpz hsθ hsz hcθ hcz
      (hbarθ.mono_exponent (by linarith)) (hbarz.mono_exponent (by linarith))
  have hiSmooth := gaugeTemporalIncrement_smooth U p.gauge ha hd hell p.timeExponent p.commonIndex
      p.axial
    c signedState hθ hz hpθ hpz hsz
  have hiSupport : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
      U.carrier
      (p.temporalIncrement v c u) := by
    have hs n := temporalIncrementState_supportedGauge U p.gauge ha hd hell c signedState
      p.timeExponent p.commonIndex p.axial n (hz n) (hpz n) (hsz n) (hsθ n)
    exact ⟨fun n => (hs n).1, fun n => (hs n).2.1, fun n => (hs n).2.2⟩
  have hmReg : GaugeDebtIncrement.RegularTriple U p.gauge.radial.inner p.gauge.radial.outer
      (signedState).mean :=
    ⟨⟨hm.radial, hms.radial⟩, ⟨hm.angular, hms.angular⟩, ⟨hm.axial, hms.axial⟩⟩
  have hiReg : GaugeDebtIncrement.RegularTriple U p.gauge.radial.inner p.gauge.radial.outer
      (p.temporalIncrement v c u) :=
    ⟨⟨hiSmooth.radial, hiSupport.radial⟩, ⟨hiSmooth.angular, hiSupport.angular⟩,
      ⟨hiSmooth.axial, hiSupport.axial⟩⟩
  have htDebt := GaugeDebtIncrement.temporalStage_debt_mem U ha p.gauge.radial.inner_lt_outer
    hcL hcR ε L hε hεone hL p.gauge p.timeExponent p.commonIndex p.axial c signedState
    hop hbase hmReg hiReg (fun i j => ⟨hW i j, hWs i j⟩) ho hb hsigned.velocity hi hH hκ le_rfl
        hdebt
  have hcov : (temporalState).covariance = (signedState).covariance :=
    gaugeTemporalStage_covariance p.gauge p.timeExponent p.commonIndex p.axial c signedState
  have htW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((temporalState).covariance
      i j) := by
    simpa only [hcov] using hW
  have htWs : ∀ i j, GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord)
      U.carrier
      ((temporalState).covariance i j) := by simpa only [hcov] using hWs
  let aliasField : ScalarField Point := fun n x =>
    temporalAliasState p.gauge p.timeExponent p.commonIndex c signedState n (x,0) 2
  obtain ⟨hrInc, hrPressure, hrCum, _, _, hrTheta, hrAxial⟩ :=
    gaugeRankStage_constructed U p.gauge p.rank ha hd hcL hcR ε L hε hεone hL hell
      p.axial c temporalState hg hparam hB hleft hright hH hκ hβ hv rfl
      ho hb htCum hop hbase htSmooth htSupport htW htWs
      (RankStateBounds.debtClass_of_components _ htDebt) aliasField htTheta htAxial
  have hrDebt := MovingMomentBounds.rankStage_defectBounds U p.gauge p.rank ha hcL hcR
    ε L hε hεone hL hell p.axial c temporalState hg hop hbase htSmooth
    ⟨htSupport.radial, htSupport.angular, htSupport.axial⟩ htW htWs hV hG
    ho hb htCum.velocity hrInc hH (show 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 9 / 10 - 2 * κ by
        linarith)
  exact ⟨⟨hrCum.velocity, hrCum.pressure⟩, hrDebt, hrTheta, hrAxial⟩


-- @@ L5854-5854 verbatim
end CycleParameters


-- @@ L5856-5856 verbatim
end CycleMeanCompletion



-- @@ L5859-5859 verbatim
section PeriodizedNativeBounds


-- @@ L5861-5861 verbatim
open Set Filter WeightedClasses CorrectionState

-- @@ L5862-5862 verbatim
open scoped ContDiff Topology


-- @@ L5864-5864 verbatim
variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L5866-5871 verbatim
/-- Only primitive background fields remain in this native family. Its
amplitude and pressure are zero, so its bounds assume no constructed output. -/
noncomputable def nativeBackground (a : LinearWaveBounds.WaveCoefficients D) :
    LocalizedWaveBounds.WaveFamily D I :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun _ =>
    { a with amplitude := 0, pressure := 0 })


-- @@ L5873-5891 verbatim
theorem localInput_of_coefficients
    (a : PeriodizedWaveBounds.CopyData D I) {s : StripData D}
    {K : ℕ → I → Set D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (h : LocalizedWaveBounds.InputBounds s K (fun n _ => P n) 0 κ d
      (nativeBackground a.background))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (ha : PeriodizedWaveBounds.LocalJets s (fun n x => Real.sqrt (s.zeta x) * P n x)
      α K a.amplitude)
    (hp : PeriodizedWaveBounds.LocalJets s (fun n x => Real.sqrt (s.zeta x) * P n x)
      (α + 1 / 2) K a.pressure) :
    LocalizedWaveBounds.InputBounds s K (fun n _ => P n) α κ d
      (LocalizedWaveBounds.rawFamily a) := by
  have hw n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx)
  exact ⟨h.loss_nonneg, h.radial_profile, h.radial_scale, h.fast_scale, h.frequency_scale,
    h.radius, h.inverse_radius, h.radial_base, h.frequency_base, h.axial_base,
    h.radial_base_aux, h.frequency_base_aux, h.axial_base_aux, h.normal, h.defect,
    fun j => (LocalizedWaveBounds.LocalClass.of_localJets hw ha).map (ContinuousLinearMap.proj j),
    LocalizedWaveBounds.LocalClass.of_localJets hw hp⟩


-- @@ L5893-5893 verbatim
namespace PeriodizedSignedParameters


-- @@ L5895-5895 verbatim
variable (p : PeriodizedSignedParameters D I) (s : StripData D)


-- @@ L5897-5934 verbatim
/-- Uniform native-copy input data for the signed quotient. The current
request is deliberately absent; it is supplied from the measured residual. -/
structure NativeControl (P : ℕ → D → ℝ) (κ : ℝ) where
  /-- Cells of `NativeControl`, of type `PeriodizedWaveBounds.Cells (D × ℝ) I`. -/
  cells : PeriodizedWaveBounds.Cells (D × ℝ) I
  /-- Phase patch of `NativeControl`, of type `ℕ → I → Set (D × ℝ)`. -/
  phasePatch : ℕ → I → Set (D × ℝ)
  background : LocalizedWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s)
    phasePatch (fun n _ x => P n x.1) 0 κ p.directions (nativeBackground p.base)
  /-- Covariance supplied by `NativeControl`. -/
  covariance : SignedCopyBounds.NativeCovariance (HarmonicWaveInteraction.productStrip s)
    phasePatch p.matrix p.target
  mask : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s) (fun _ _ => 1)
    0 phasePatch (fun n i => p.mask i n)
  fundamental : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun n x => P n x.1) 0 phasePatch (fun n i => p.fundamental i n)
  normalMotion : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.normalMotion i n)
  action : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.action i n)
  cutoff : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.cutoff i n)
  cutoff_support : ∀ n i, Function.support (p.cutoff i n) ⊆ cells.carrier n i
  phase_cover : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ cells.carrier n
      i →
    x ∈ phasePatch n i ∨ (p.cutoff i n =ᶠ[𝓝 x] fun _ => 0) ∨ (p.mask i n =ᶠ[𝓝 x] fun _ => 0)
  envelope_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ P n x
  /-- Lower of `NativeControl`, of type `ℝ`. -/
  lower : ℝ
  /-- Upper of `NativeControl`, of type `ℝ`. -/
  upper : ℝ
  lower_pos : 0 < lower
  normal_lower : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ phasePatch n i →
    lower ≤ ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖
  normal_upper : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ phasePatch n i →
    ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ≤ upper
  inverse_frequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / p.base.frequency n)


-- @@ L5936-5936 verbatim
variable {p s} {P : ℕ → D → ℝ} {κ β : ℝ}


-- @@ L5938-5944 verbatim
theorem raw_zero_of_mask (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) (i : I) (x : D × ℝ) (hm : p.mask i n x = 0) :
    (p.copyData s request).amplitude n i x = 0 ∧ (p.copyData s request).pressure n i x = 0 := by
  simp [copyData, native, SignedParameters.coefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, SignedWaveUpdate.signedVector,
        SignedWaveUpdate.signedScalar,
    hm, ParticularWaveBounds.projectedPressure, TangentProjection.pressureCoefficient]


-- @@ L5946-5956 verbatim
theorem localized_zero_of_mask (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    {n : ℕ} {i : I} {x : D × ℝ} (hm : p.mask i n =ᶠ[𝓝 x] fun _ => 0) :
    ((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
    ((p.copyData s request).localized i).pressure n =ᶠ[𝓝 x] (fun _ => 0) := by
  constructor
  · filter_upwards [hm] with y hy
    change p.cutoff i n y • (p.copyData s request).amplitude n i y = 0
    rw [(raw_zero_of_mask request n i y hy).1, smul_zero]
  · filter_upwards [hm] with y hy
    change (p.cutoff i n y : ℂ) * (p.copyData s request).pressure n i y = 0
    rw [(raw_zero_of_mask request n i y hy).2, mul_zero]


-- @@ L5958-5975 verbatim
theorem NativeControl.raw_jets (h : p.NativeControl s P κ)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
      (fun n x => Real.sqrt (s.zeta x.1) * P n x.1) (β + 1 / 2) h.phasePatch
      (p.copyData s request).amplitude ∧
    PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
      (fun n x => Real.sqrt (s.zeta x.1) * P n x.1) (β + 1) h.phasePatch
      (p.copyData s request).pressure := by
  have hK : UniformPrimaryWeights.UniformBandBound (HarmonicWaveInteraction.productStrip s)
      (1 / 2) (fun (_ : I) n => 1 / p.base.frequency n) := by
    obtain ⟨C, hC, q, hb⟩ := h.inverse_frequency
    exact ⟨C, hC, q, fun _ n => hb n⟩
  exact SignedCopyBounds.coefficients_jets (a := fun _ => p.base) (d := fun _ => p.directions)
    h.covariance (fun j => PeriodizedWaveBounds.LocalJets.of_memClass (hR j))
    h.mask h.fundamental (fun n x hx => h.envelope_nonneg n x.1 hx)
    h.background.normal.to_localJets h.normalMotion h.action h.lower_pos
    h.normal_lower h.normal_upper hK p.column


-- @@ L5977-6015 verbatim
/-- All five full-lift classes are obtained from the actual quotient and
uniform native data. Background estimates are used only on the cells. -/
theorem NativeControl.global_bounds (h : p.NativeControl s P κ) (hκ : κ ≤ 1 / 2)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 / 2)
      (p.copyData s request).common.amplitude ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 / 2)
      ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
          p.directions).amplitude ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1)
      (p.copyData s request).common.pressure ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - κ)
      ((p.copyData s request).common.curlCorrection (HarmonicWaveInteraction.productStrip s)
          p.directions) ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - 3 * κ)
      ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) p.directions) :=
          by
  obtain ⟨ha, hp⟩ := h.raw_jets request hR
  have hinput := localInput_of_coefficients (p.copyData s request) h.background
    (fun n x hx => h.envelope_nonneg n x.1 hx) ha
    (by simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring]; exact hp)
  have hcover : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.cells.carrier
      n i →
      x ∈ h.phasePatch n i ∨
      (((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((p.copyData s request).localized i).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
    intro n i x hx hi
    rcases h.phase_cover n i x hx hi with hp | hcut | hmask
    · exact Or.inl hp
    · exact Or.inr ((p.copyData s request).localized_zero_germs hcut)
    · exact Or.inr (localized_zero_of_mask request hmask)
  have hh := LocalizedWaveBounds.common_bounds_from_supported_native (p.copyData s request)
    h.cells h.cutoff_support h.phasePatch (fun n x hx => h.envelope_nonneg n x.1 hx)
    (hinput.with_cutoff (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one)
        h.cutoff))
    hκ h.lower_pos h.normal_lower h.normal_upper
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) hcover
  simpa only [show β + 1 / 2 + 1 / 2 = β + 1 by ring] using hh


-- @@ L6017-6044 verbatim
theorem NativeControl.block_bounds (h : p.NativeControl s P κ) (hκ : κ ≤ 1 / 2)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    (p.tangentBlock s request).WaveBounds s P (β + 1 / 2) ∧
    (p.exactBlock s request).WaveBounds s P (β + 1 / 2) ∧
    (p.exactBlock s request).PressureBounds s P (β + 1) ∧
    (p.curlBlock s request).WaveBounds s P (β + 1 - κ) ∧
    (p.goodBlock s request).WaveBounds s P (β + 1 - 3 * κ) := by
  obtain ⟨ha, he, hp, hc, hg⟩ := h.global_bounds hκ request hR
  have ht := SignedWaveUpdate.blockOfCoefficients_classes (p.copyData s request).common
      p.angularFrequency ha hp
  have hx := SignedWaveUpdate.blockOfCoefficients_classes
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions)
    p.angularFrequency he hp
  have hd : WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - κ)
      (fun n x => ((p.copyData s request).commonCorrected
        (HarmonicWaveInteraction.productStrip s) p.directions).amplitude n x -
        (p.copyData s request).common.amplitude n x) := by
    apply LinearWaveBounds.class_congr hc
    intro n x hx
    simp only [PeriodizedWaveBounds.CopyData.commonCorrected,
      LinearWaveBounds.WaveCoefficients.addAmplitude, add_sub_cancel_left]
  have hd' := blockOfCoefficients_difference_mem _ _ p.angularFrequency hd
  have hg' := SignedWaveUpdate.class_zeroSection hg
  rw [sectionStrip_productStrip] at ht hx hd' hg'
  exact ⟨ht.1, hx.1, hx.2, hd', (SignedWaveUpdate.coefficientBlock_classes
    p.base.frequency (fun n x => p.base.phase n (x,0)) p.angularFrequency hg'
      (MemClass.zero (α := (0 : ℝ)) hg'.weight_nonneg)).1⟩


-- @@ L6046-6046 verbatim
end PeriodizedSignedParameters


-- @@ L6048-6048 verbatim
namespace ParticularParameters


-- @@ L6050-6050 verbatim
open CommonCoverSolve TorusInverse


-- @@ L6052-6055 verbatim
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)


-- @@ L6057-6059 verbatim
/-- Native tangent, defined pointwise by `ParticularWaveAssembly.angleTangent (p.tangent j n)`. -/
noncomputable def nativeTangent : ℕ → TangentData (Q × ℝ) ProblemStatement.Space :=
  fun n => ParticularWaveAssembly.angleTangent (p.tangent j n)


-- @@ L6061-6121 verbatim
/-- Input bounds for the actual complex Volterra solve on all of its
native cells. The modal forcing is the literal current residual source. -/
structure NativeControl (W : ℕ → (Q × ℝ) × Plane → ℝ) (α κ : ℝ) where
  /-- Cells of `NativeControl`, of type `PeriodizedWaveBounds.Cells ((Q × ℝ) × Plane)
  Frequency`. -/
  cells : PeriodizedWaveBounds.Cells ((Q × ℝ) × Plane) Frequency
  /-- Phase patch of `NativeControl`, of type `ℕ → Frequency → Set ((Q × ℝ) × Plane)`. -/
  phasePatch : ℕ → Frequency → Set ((Q × ℝ) × Plane)
  background : LocalizedWaveBounds.InputBounds (nativeStrip s) phasePatch
    (fun n _ => W n) 0 κ p.directions (nativeBackground (p.copyData c u b G A j).background)
  /-- Frame of `NativeControl`, of type `ℕ → PrimaryODE.FrameData ((Q × ℝ) × ℝ)`. -/
  frame : ℕ → PrimaryODE.FrameData ((Q × ℝ) × ℝ)
  /-- Envelope of `NativeControl`, of type `ℕ → ℝ → ℝ`. -/
  envelope : ℕ → ℝ → ℝ
  /-- Real control supplied by `NativeControl`. -/
  realControl : ParticularCopyBounds.ModalControl (nativeStrip s) α frame
    (fun n => ParticularWaveBounds.realData (p.nativeTangent j n) ((p.copyData c u b G A j).source
        n))
    j p.geometry p.length envelope phasePatch
  /-- Imag control supplied by `NativeControl`. -/
  imagControl : ParticularCopyBounds.ModalControl (nativeStrip s) α frame
    (fun n => ParticularWaveBounds.imagData (p.nativeTangent j n) ((p.copyData c u b G A j).source
        n))
    j p.geometry p.length envelope phasePatch
  envelope_nonneg : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x
  envelope_compare : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    envelope n ((p.geometry n).coordinates i x.2).2 ≤ W n x
  normal : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i
        x))
  normalMotion : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).normalDot (ParticularWaveBounds.nativePoint (p.geometry n)
        i x))
  action : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).action (ParticularWaveBounds.nativePoint (p.geometry n) i
        x))
  source : PeriodizedWaveBounds.LocalJets (nativeStrip s)
    (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) α phasePatch
    (fun n _ => (p.copyData c u b G A j).source n)
  cutoff : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (p.copyData c u b G A j).cutoff
  cutoff_support : ∀ n i, Function.support ((p.copyData c u b G A j).cutoff n i) ⊆ cells.carrier n i
  phase_cover : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ cells.carrier n i →
    x ∈ phasePatch n i ∨ ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0
  /-- Lower of `NativeControl`, of type `ℝ`. -/
  lower : ℝ
  /-- Upper of `NativeControl`, of type `ℝ`. -/
  upper : ℝ
  lower_pos : 0 < lower
  normal_lower : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    lower ≤ ‖(p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)‖
  normal_upper : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    ‖(p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)‖ ≤ upper
  normal_match : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    (p.copyData c u b G A j).background.normal (nativeStrip s) p.directions n x =
      (p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)
  inverse_frequency : BandBound (nativeStrip s) (1 / 2)
    (fun n => 1 / (p.copyData c u b G A j).background.frequency n)


-- @@ L6123-6123 verbatim
variable {p s c u b G A j} {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}


-- @@ L6125-6142 verbatim
theorem raw_zero_of_source_path {n : ℕ} {i : Frequency} {x : (Q × ℝ) × Plane}
    (hf : ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0) :
    (p.copyData c u b G A j).amplitude n i =ᶠ[𝓝 x] (fun _ => 0) ∧
    (p.copyData c u b G A j).pressure n i =ᶠ[𝓝 x] (fun _ => 0) ∧
    (p.copyData c u b G A j).source n =ᶠ[𝓝 x] (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hf] with y hy
    exact ParticularWaveBounds.complexCopyVelocity_zero_of_path (p.nativeTangent j n)
      ((p.copyData c u b G A j).source n) (p.geometry n) (p.length_pos n).le i y.1 y.2 hy.2
  · filter_upwards [hf] with y hy
    exact ParticularWaveBounds.complexCopyPressure_zero_of_path (p.nativeTangent j n)
      ((p.copyData c u b G A j).source n) (p.geometry n) (p.length_pos n).le i
      ((p.copyData c u b G A j).background.frequency n) y.1 y.2 hy.2 hy.1
  · filter_upwards [hf] with y hy
    simpa only [Geometry.path_current, Prod.mk.eta] using hy.2 _ hy.1


-- @@ L6144-6158 verbatim
theorem localized_zero_of_source_path {n : ℕ} {i : Frequency} {x : (Q × ℝ) × Plane}
    (hf : ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0) :
    ((p.copyData c u b G A j).localized i).amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
    ((p.copyData c u b G A j).localized i).pressure n =ᶠ[𝓝 x] (fun _ => 0) := by
  obtain ⟨ha, hp, _⟩ := raw_zero_of_source_path hf
  constructor
  · filter_upwards [ha] with y hy
    change _ • (p.copyData c u b G A j).amplitude n i y = 0
    rw [hy, smul_zero]
  · filter_upwards [hp] with y hy
    change _ * (p.copyData c u b G A j).pressure n i y = 0
    rw [hy, mul_zero]


-- @@ L6160-6171 verbatim
theorem NativeControl.raw_jets (h : p.NativeControl s c u b G A j W α κ) :
    PeriodizedWaveBounds.LocalJets (nativeStrip s)
      (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) α h.phasePatch
      (p.copyData c u b G A j).amplitude ∧
    PeriodizedWaveBounds.LocalJets (nativeStrip s)
      (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) (α + 1 / 2) h.phasePatch
      (p.copyData c u b G A j).pressure :=
  ParticularCopyBounds.coefficients_jets (p.copyData c u b G A j).background
    (p.nativeTangent j) (p.copyData c u b G A j).source p.geometry p.length p.length_pos
    h.envelope W h.frame j h.phasePatch h.realControl h.imagControl h.envelope_nonneg
    h.envelope_compare h.normal h.normalMotion h.action h.source h.lower_pos h.normal_lower
    h.normal_upper h.inverse_frequency


-- @@ L6173-6198 verbatim
/-- The global amplitude, pressure, exact curl, and retained linear error
are derived from native modal inputs for the same actual residual solve. -/
theorem NativeControl.global_bounds (h : p.NativeControl s c u b G A j W α κ) (hκ : κ ≤ 1 / 2) :
    WaveClass (nativeStrip s) W α (p.copyData c u b G A j).common.amplitude ∧
    WaveClass (nativeStrip s) W α (p.wave s c u b G A j).amplitude ∧
    WaveClass (nativeStrip s) W (α + 1 / 2) (p.copyData c u b G A j).common.pressure ∧
    WaveClass (nativeStrip s) W (α + 1 / 2 - κ)
      ((p.copyData c u b G A j).common.curlCorrection (nativeStrip s) p.directions) ∧
    WaveClass (nativeStrip s) W (α + 1 / 2 - 3 * κ)
      ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions) := by
  obtain ⟨ha, hp⟩ := h.raw_jets
  have hin := localInput_of_coefficients (p.copyData c u b G A j) h.background h.envelope_nonneg ha
      hp
  exact LocalizedWaveBounds.common_bounds_from_supported_native (M := h.upper)
    (p.copyData c u b G A j) h.cells h.cutoff_support h.phasePatch h.envelope_nonneg
    (hin.with_cutoff (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one)
        h.cutoff))
    hκ h.lower_pos
    (fun n i x hx hi => by
      rw [h.normal_match n i x hx hi]
      exact h.normal_lower n i x hx hi)
    (fun n i x hx hi => by
      rw [h.normal_match n i x hx hi]
      exact h.normal_upper n i x hx hi)
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency)
    (fun n i x hx hi => (h.phase_cover n i x hx hi).imp_right localized_zero_of_source_path)


-- @@ L6200-6203 verbatim
theorem sectionStrip_nativeStrip (s : StripData (Q × Plane)) :
    ParticularWaveAssembly.sectionStrip (nativeStrip s) = s := by
  cases s
  rfl


-- @@ L6205-6229 verbatim
theorem assembled_bounds (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
    {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (C : ∀ j ∈ ParticularWaveAssembly.modes N, p.NativeControl s c u b G A j W α κ)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x) (hκ : κ ≤ 1 / 2) :
    (p.updateBlock s c u b G A N).WaveBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) α ∧
    (p.updateBlock s c u b G A N).PressureBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) (α + 1 / 2) ∧
    (p.goodBlock s c u b G A N).WaveBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) (α + 1 / 2 - 3 * κ) := by
  have hu := ParticularWaveAssembly.assembledBlock_classes
    (s := ParticularWaveAssembly.sectionStrip (nativeStrip s)) N b.frequency b.phase
        b.angularFrequency
    (fun n x hx => hW n _ hx)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.1)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.2.1)
  have hg := ParticularWaveAssembly.assembledBlock_classes
    (s := ParticularWaveAssembly.sectionStrip (nativeStrip s)) (γ := (0 : ℝ)) N
    b.frequency b.phase b.angularFrequency (fun n x hx => hW n _ hx)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.2.2.2)
    (fun _ _ => MemClass.zero (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n _ hx)))
  rw [sectionStrip_nativeStrip] at hu hg
  exact ⟨hu.1, hu.2, hg.1⟩


-- @@ L6231-6231 verbatim
end ParticularParameters


-- @@ L6233-6233 verbatim
end PeriodizedNativeBounds


-- @@ L6235-6235 verbatim
section NativeEquations


-- @@ L6237-6237 verbatim
open Set Filter WeightedClasses HarmonicCalculus CorrectionState

-- @@ L6238-6238 verbatim
open scoped ContDiff Topology


-- @@ L6240-6240 verbatim
variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L6242-6248 verbatim
theorem localClass_contDiffOn_inter {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {C : ℕ → I → Set D} {w : ℕ → I → D → ℝ} {α : ℝ}
    {f : ℕ → I → D → E} (hf : LocalizedWaveBounds.LocalClass s C w α f)
    (hC : ∀ n i, IsOpen (C n i)) (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ (f n i) (s.domain ∩ C n i) :=
  (s.isOpen_domain.inter (hC n i)).contDiffOn_iff.mpr
    (fun x hx => hf.smooth n i x hx.1 hx.2)


-- @@ L6250-6267 verbatim
/-- Angular and radial geometry of the actual raw copies. The analytic
bounds on the normal and material defect remain restricted to `C`. -/
structure NativeAngularGeometry (a : PeriodizedWaveBounds.CopyData D I) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) (C : ℕ → I → Set D) : Prop where
  open_patch : ∀ n i, IsOpen (C n i)
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.background.phase n) s.domain
  radius_nonzero : ∀ n i x, x ∈ s.domain → x ∈ C n i → a.background.radius n x ≠ 0
  radial_radius : ∀ n i x, x ∈ s.domain → x ∈ C n i →
    along (d.radialField n) (a.background.radius n) x = 1
  radius : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.radius n)
  radial_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.radialBase n)
  frequency_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.frequencyBase n)
  axial_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.axialBase n)
  radial_field : ∀ n, CopyAngularInvariance.Invariant d.angular (d.radialField n)
  phase : ∀ n, ∃ m, CopyAngularInvariance.AffinePhase d.angular m (a.background.phase n)
  amplitude : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.amplitude n i)
  pressure : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.pressure n i)
  cutoff : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.cutoff n i)


-- @@ L6269-6310 verbatim
theorem NativeAngularGeometry.exactOn
    {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
    {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α κ lower upper : ℝ}
    (g : NativeAngularGeometry a s d C)
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (hκ : κ ≤ 1 / 2) (hlower : 0 < lower)
    (hlo : ∀ n i x, x ∈ s.domain → x ∈ C n i → lower ≤ ‖a.background.normal s d n x‖)
    (hhi : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.background.normal s d n x‖ ≤ upper)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s C (1 / 2)
      (fun n _ _ => 1 / a.background.frequency n)) (n : ℕ) (i : I) :
    LocalizedWaveBounds.ExactOn (a.corrected s d i) s d n (s.domain ∩ C n i) := by
  have hn := h.with_cutoff hψ
  have hc := hn.curlCorrection_class hlower hlo hhi hfreq
  have he := hn.add_curl_amplitude hκ (fun j => hc.map (ContinuousLinearMap.proj j))
  have ha i n := CopyAngularInvariance.corrected_amplitude_invariant
    (a := a.raw i) (s := s) (d := d) (fun n => a.cutoff n i) g.radius g.radial_field
    (fun _ => CopyAngularInvariance.Invariant.const _) g.phase (g.amplitude i) (g.cutoff i) n
  have hp i n := CopyAngularInvariance.corrected_pressure_invariant
    (a := a.raw i) (s := s) (d := d) (fun n => a.cutoff n i) (g.pressure i) (g.cutoff i) n
  refine ⟨s.isOpen_domain.inter (g.open_patch n i),
    localClass_contDiffOn_inter h.radial_profile g.open_patch n i,
    (g.phase_smooth n).mono inter_subset_left,
    (fun j => localClass_contDiffOn_inter (he.amplitude j) g.open_patch n i),
    (fun x hx => (h.radius.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.radial_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.frequency_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.axial_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (he.pressure.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => g.radius_nonzero n i x hx.1 hx.2),
    (fun x hx => g.radial_radius n i x hx.1 hx.2), ?_, ?_, ?_, ?_⟩
  · intro x hx j
    exact ((CopyAngularInvariance.base_invariant (g.radius n) (g.radial_base n)
      (g.frequency_base n) (g.axial_base n)).component j).along_zero x
  · intro j x hx
    exact ((ha i n).component j).along_zero x
  · obtain ⟨m, hm⟩ := g.phase n
    exact ⟨m, fun x hx => hm.directional_eq
      (((g.phase_smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx.1)).differentiableAt (by simp))⟩
  · intro x hx
    exact (hp i n).along_zero x


-- @@ L6312-6340 verbatim
/-- The generic local identity is applied only after the primitive raw
principal equation has been proved by its actual ODE constructor. -/
theorem native_cancellation_of_principal
    {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
    {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α κ lower upper : ℝ}
    (g : NativeAngularGeometry a s d C)
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (hκ : κ ≤ 1 / 2) (hlower : 0 < lower)
    (hlo : ∀ n i x, x ∈ s.domain → x ∈ C n i → lower ≤ ‖a.background.normal s d n x‖)
    (hhi : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.background.normal s d n x‖ ≤ upper)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s C (1 / 2)
      (fun n _ _ => 1 / a.background.frequency n))
    (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ C n i)
    (hsolve : (a.raw i).principal s d n x = -a.source n x) :
    (a.corrected s d i).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) := by
  have hc := (h.with_cutoff hψ).curlCorrection_class hlower hlo hhi hfreq
  exact LocalizedWaveBounds.harmonicResidual_eq_good_add_excluded_on (a.raw i) s d
    (fun n => a.cutoff n i) ((a.localized i).curlCorrection s d) a.source n
    (g.exactOn h hψ hκ hlower hlo hhi hfreq n i) ⟨hx,hi⟩
    (fun j => (h.amplitude j).smooth n i x hx hi |>.differentiableAt (by simp))
    ((hψ.smooth n i x hx hi).differentiableAt (by simp))
    (fun j => (hc.map (ContinuousLinearMap.proj j)).smooth n i x hx hi |>.differentiableAt (by
        simp))
    hsolve


-- @@ L6342-6360 verbatim
theorem harmonicResidual_zero_germ
    (a : LinearWaveBounds.WaveCoefficients D) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) {n : ℕ} {x : D}
    (ha : a.amplitude n =ᶠ[𝓝 x] fun _ => 0) (hp : a.pressure n =ᶠ[𝓝 x] fun _ => 0) :
    a.harmonicResidual s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have hv : vectorMode (a.frequency n) (a.phase n) (a.amplitude n) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ha] with y hy
    ext j
    simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]
  have hpr : mode (a.frequency n) (a.phase n) (a.pressure n) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hp] with y hy
    simp only [mode, hy, zero_mul]
  have hh := ParticularWaveAssembly.linearResidual_germ hv hpr (s.epsilon n) (a.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase
        n))
  simp only [PeriodizedWaveBounds.linearResidual_zero] at hh
  exact hh


-- @@ L6362-6379 verbatim
theorem local_cancellation_of_zero_germs
    (a : PeriodizedWaveBounds.CopyData D I) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) {n : ℕ} {i : I} {x : D}
    (ha : (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0)
    (hp : (a.localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)
    (hg : a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0)
    (hf : a.source n =ᶠ[𝓝 x] fun _ => 0) :
    (a.corrected s d i).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) := by
  have hz := (LocalizedWaveBounds.nativeFamily a).outputs_zero_germs s d ha hp
  have hcor : (a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := hz.2.1
  have hgood : a.localGood s d n i =ᶠ[𝓝 x] fun _ => 0 := hz.2.2
  have hres := harmonicResidual_zero_germ (a.corrected s d i) s d hcor hp
  rw [hres.self_of_nhds, hf.self_of_nhds, hgood.self_of_nhds, hg.self_of_nhds]
  ext j
  simp


-- @@ L6381-6381 verbatim
namespace PeriodizedSignedParameters


-- @@ L6383-6385 verbatim
variable {p : PeriodizedSignedParameters D I} {s : StripData D}
    {P : ℕ → D → ℝ} {κ β : ℝ} (h : p.NativeControl s P κ)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)


-- @@ L6387-6415 verbatim
/-- Primitive angular identities and the fixed unit fundamental's ODE.
The signed principal equation and every cutoff/curl identity are derived. -/
structure NativeDynamics where
  /-- Slope of `NativeDynamics`, of type `ℕ → ℝ`. -/
  slope : ℕ → ℝ
  angular : ∀ i, SignedWaveUpdate.AngularInputs (HarmonicWaveInteraction.productStrip s)
    p.directions p.base (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i)
    (p.normalMotion i) (p.action i) (p.cutoff i) slope
  open_patch : ∀ n i, IsOpen (h.phasePatch n i)
  radius_nonzero : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    x ∈ h.phasePatch n i → p.base.radius n x ≠ 0
  radial_radius : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    x ∈ h.phasePatch n i → along (p.directions.radialField n) (p.base.radius n) x = 1
  matrix_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.matrix i)
  target_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.target i)
  request_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast request
  mask_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.mask i)
  frequency_nonzero : ∀ n, p.base.frequency n ≠ 0
  ode : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
    along (p.directions.fastField n) (p.fundamental i n) x =
      TangentProjection.projectedRhs
        (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x)
        (p.normalMotion i n x) (p.fundamental i n x) (p.action i n x (p.fundamental i n x)) 0
        (s.epsilon n * p.base.frequency n ^ 2 *
          ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ^ 2)
  action_eq : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
    CurlClassBounds.complexify (p.action i n x (p.fundamental i n x)) =
      LinearWaveResidual.shear (p.base.radius n) (p.base.frequencyBase n) (p.base.axialBase n)
        (p.directions.radialField n) (fun y => CurlClassBounds.complexify (p.fundamental i n y)) x


-- @@ L6417-6417 verbatim
variable {h request}


-- @@ L6419-6427 verbatim
theorem NativeDynamics.angularGeometry (d : NativeDynamics h request) (i₀ : I) :
    NativeAngularGeometry (p.copyData s request) (HarmonicWaveInteraction.productStrip s)
      p.directions h.phasePatch :=
  ⟨d.open_patch, (d.angular i₀).phase_smooth, d.radius_nonzero, d.radial_radius,
    (d.angular i₀).radius, (d.angular i₀).radial_base, (d.angular i₀).frequency_base,
    (d.angular i₀).axial_base, (d.angular i₀).radialField,
    fun n => ⟨d.slope n, (d.angular i₀).phase n⟩,
    fun i => (d.angular i).amplitude p.column, fun i => (d.angular i).pressure p.column,
    fun i => (d.angular i).cutoff⟩


-- @@ L6429-6439 verbatim
theorem NativeDynamics.principal (d : NativeDynamics h request)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) (i : I) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain)
    (hi : x ∈ h.phasePatch n i) :
    ((p.copyData s request).raw i).principal (HarmonicWaveInteraction.productStrip s) p.directions
        n x = 0 :=
  NativePrincipalEquations.signed_coefficients_principal_at (a := fun _ => p.base)
    (dirs := fun _ => p.directions) h.covariance
    (fun j => PeriodizedWaveBounds.LocalJets.of_memClass (hR j)) h.mask h.fundamental
    p.column n i hx hi (d.matrix_frozen i) (d.target_frozen i) d.request_frozen (d.mask_frozen i)
    (d.frequency_nonzero n) (d.ode n i x hx hi) (d.action_eq n i x hx hi)


-- @@ L6441-6462 verbatim
theorem NativeDynamics.local_equation (d : NativeDynamics h request) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) (i : I) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain)
    (hi : x ∈ h.phasePatch n i) :
    ((p.copyData s request).corrected (HarmonicWaveInteraction.productStrip s) p.directions
        i).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions n x +
        (fun j => (p.copyData s request).source n x j * carrier (p.base.frequency n) (p.base.phase
            n) x) =
      (fun j => ((p.copyData s request).localGood (HarmonicWaveInteraction.productStrip s)
          p.directions n i x j +
        (p.copyData s request).localGaussian p.directions n i x j) * carrier (p.base.frequency n)
            (p.base.phase n) x) := by
  obtain ⟨ha, hp⟩ := h.raw_jets request hR
  have hin := localInput_of_coefficients (p.copyData s request) h.background
    (fun n x hx => h.envelope_nonneg n x.1 hx) ha
    (by simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring]; exact hp)
  exact native_cancellation_of_principal (d.angularGeometry i) hin
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    hκ h.lower_pos h.normal_lower h.normal_upper
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) n i hx hi
    (by simpa only [copyData, Pi.zero_apply, neg_zero] using d.principal hR n i hx hi)


-- @@ L6464-6509 verbatim
/-- The literal signed common curl has its actual retained good term and
Gaussian derivative tail on the entire lift. Native ODE input is needed
only on the supported phase patches. -/
theorem NativeDynamics.common_equation (d : NativeDynamics h request) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain) :
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
        p.directions).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions n x =
      (fun j => ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s)
          p.directions n x j +
        (p.copyData s request).globalGaussian p.directions n x j) * carrier (p.base.frequency n)
            (p.base.phase n) x) := by
  let a := p.copyData s request
  have hzsource (m : ℕ) (y : D × ℝ) : a.source m =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hl : ∀ m i y, y ∈ (HarmonicWaveInteraction.productStrip s).domain → y ∈ h.cells.carrier m i →
      (a.corrected (HarmonicWaveInteraction.productStrip s) p.directions i).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions m y +
        (fun j => a.source m y j * carrier (a.background.frequency m) (a.background.phase m) y) =
      (fun j => (a.localGood (HarmonicWaveInteraction.productStrip s) p.directions m i y j +
        a.localGaussian p.directions m i y j) * carrier (a.background.frequency m)
            (a.background.phase m) y) := by
    intro m i y hy hi
    rcases h.phase_cover m i y hy hi with hC | hcut | hmask
    · exact d.local_equation hκ hR m i hy hC
    · have hz := a.localized_zero_germs hcut
      have hg : a.localGaussian p.directions m i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [a.localTail_zero_germ p.directions hcut] with z hz
        rw [a.localGaussian_eq, hz]
        simp only [a, copyData, smul_zero, add_zero]
      exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2 hg (hzsource m y)
    · have hz := localized_zero_of_mask (s := s) request hmask
      have hu : a.amplitude m i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hmask] with z hz
        exact (raw_zero_of_mask request m i z hz).1
      exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2
        (a.localGaussian_zero_of_fields p.directions hu (hzsource m y)) (hzsource m y)
  have he := a.common_cancellation h.cells h.cutoff_support
    (HarmonicWaveInteraction.productStrip s) p.directions hl n hx
  have hz : (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x)
      = 0 := by
    ext j
    exact zero_mul _
  simp only [hz, add_zero] at he
  exact he


-- @@ L6511-6511 verbatim
end PeriodizedSignedParameters


-- @@ L6513-6513 verbatim
namespace ParticularParameters


-- @@ L6515-6515 verbatim
open CommonCoverSolve TorusInverse ParticularWaveAssembly CopyAngularInvariance


-- @@ L6517-6522 verbatim
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {p : ParticularParameters Q} {s : StripData (Q × Plane)}
    {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
    {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
    {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (h : p.NativeControl s c u b G A j W α κ)


-- @@ L6524-6542 verbatim
/-- Native dynamics data, collecting `background`, `open_patch`, `frequency_nonzero`, `damping`,
`fast`, `action`. -/
structure NativeDynamics : Prop where
  background : BackgroundControl (nativeStrip s) p.directions p.background b j
  open_patch : ∀ n i, IsOpen (h.phasePatch n i)
  frequency_nonzero : ∀ n, (j : ℝ) * b.frequency n ≠ 0
  damping : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ h.phasePatch n i →
    (p.nativeTangent j n).damping (ParticularWaveBounds.nativePoint (p.geometry n) i x) =
      s.epsilon n * ((j : ℝ) * b.frequency n) ^ 2 *
        ‖(p.copyData c u b G A j).background.normal (nativeStrip s) p.directions n x‖ ^ 2
  fast : ∀ n, p.directions.fastScale n • p.directions.fast =
    ((0 : Q × ℝ), ParticularWaveBounds.slotDirection (p.geometry n))
  action : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ h.phasePatch n i → ∀ z :
      ProblemStatement.Space,
    CurlClassBounds.complexify ((p.nativeTangent j n).action
      (ParticularWaveBounds.nativePoint (p.geometry n) i x) z) =
      LinearWaveResidual.shear (p.background.radius n) (p.background.frequencyBase n)
        (p.background.axialBase n) (p.directions.radialField n) (fun _ =>
            CurlClassBounds.complexify z) x


-- @@ L6544-6544 verbatim
variable {h}


-- @@ L6546-6567 verbatim
theorem NativeDynamics.angularGeometry (d : NativeDynamics h) :
    NativeAngularGeometry (p.copyData c u b G A j) (nativeStrip s) p.directions h.phasePatch := by
  refine ⟨d.open_patch, d.background.phase_smooth,
    (fun n _ x hx _ => d.background.radius_ne n x hx),
    (fun n _ x hx _ => d.background.radial_radius n x hx),
    d.background.radius_invariant, d.background.radial_base_invariant,
    d.background.frequency_base_invariant, d.background.axial_base_invariant,
    d.background.radial_invariant, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [d.background.angular]
    exact ⟨_, actualCarrier_affine p.background b j n⟩
  · intro i n
    rw [d.background.angular]
    exact complexCopyVelocity_invariant (angleTangent_invariant _) (angleLift_invariant _)
      (p.geometry n) (p.length_pos n).le i
  · intro i n
    rw [d.background.angular]
    exact complexCopyPressure_invariant (angleTangent_invariant _) (angleLift_invariant _)
      (p.geometry n) (p.length_pos n).le i _
  · intro i n
    rw [d.background.angular]
    exact nativeCutoff_invariant ((0 : Q), (1 : ℝ)) (p.geometry n) (p.cutoff n) i


-- @@ L6569-6577 verbatim
theorem NativeDynamics.principal (d : NativeDynamics h)
    (n : ℕ) (i : Frequency) {x : (Q × ℝ) × Plane}
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.phasePatch n i) :
    ((p.copyData c u b G A j).raw i).principal (nativeStrip s) p.directions n x =
      -(p.copyData c u b G A j).source n x :=
  NativePrincipalEquations.complexCopyCoefficients_principal_at
    (p.copyData c u b G A j).background p.length_pos h.realControl h.imagControl n i hx hi
    (d.frequency_nonzero n) (h.normal_match n i x hx hi) (d.damping n i x hx hi)
    (d.fast n) (d.action n i x hx hi)


-- @@ L6579-6598 verbatim
theorem NativeDynamics.local_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) (i : Frequency) {x : (Q × ℝ) × Plane}
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.phasePatch n i) :
    ((p.copyData c u b G A j).corrected (nativeStrip s) p.directions i).harmonicResidual
        (nativeStrip s) p.directions n x +
        (fun k => (p.copyData c u b G A j).source n x k *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) =
      (fun k => ((p.copyData c u b G A j).localGood (nativeStrip s) p.directions n i x k +
        (p.copyData c u b G A j).localGaussian p.directions n i x k) *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) := by
  obtain ⟨ha, hp⟩ := h.raw_jets
  have hin := localInput_of_coefficients (p.copyData c u b G A j) h.background h.envelope_nonneg ha
      hp
  exact native_cancellation_of_principal d.angularGeometry hin
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    hκ h.lower_pos
    (fun n i x hx hi => by rw [h.normal_match n i x hx hi]; exact h.normal_lower n i x hx hi)
    (fun n i x hx hi => by rw [h.normal_match n i x hx hi]; exact h.normal_upper n i x hx hi)
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) n i hx hi (d.principal n i hx
        hi)


-- @@ L6600-6620 verbatim
/-- The actual inhomogeneous common wave cancels the literal HR source
on the whole lift, including the uncovered-source term in its Gaussian. -/
theorem NativeDynamics.common_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) {x : (Q × ℝ) × Plane} (hx : x ∈ (nativeStrip s).domain) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n x +
        (fun k => (p.copyData c u b G A j).source n x k *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) =
      (fun k => ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n x k +
        (p.copyData c u b G A j).globalGaussian p.directions n x k) *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) := by
  apply (p.copyData c u b G A j).common_cancellation h.cells h.cutoff_support (nativeStrip s)
      p.directions _ n hx
  intro m i y hy hi
  rcases h.phase_cover m i y hy hi with hC | hpath
  · exact d.local_equation hκ m i hy hC
  · have hz := localized_zero_of_source_path (p := p) (c := c) (u := u) (b := b) (G := G) (A := A)
      (j := j) hpath
    have hr := raw_zero_of_source_path (p := p) (c := c) (u := u) (b := b) (G := G) (A := A) (j :=
        j) hpath
    exact local_cancellation_of_zero_germs _ _ _ hz.1 hz.2
      ((p.copyData c u b G A j).localGaussian_zero_of_fields p.directions hr.1 hr.2.2) hr.2.2


-- @@ L6622-6622 verbatim
end ParticularParameters


-- @@ L6624-6624 verbatim
end NativeEquations


-- @@ L6626-6626 verbatim
section PeriodizedSignedLinear

-- @@ L6627-6627 verbatim
open Set Filter WeightedClasses HarmonicCalculus CorrectionState

-- @@ L6628-6628 verbatim
open scoped ContDiff Topology


-- @@ L6630-6630 verbatim
variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L6632-6632 verbatim
namespace NativeAngularGeometry

-- @@ L6633-6635 verbatim
variable {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
  {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
  (g : NativeAngularGeometry a s d C)


-- @@ L6637-6637 verbatim
include g


-- @@ L6639-6642 verbatim
theorem common_amplitude (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.common.amplitude n) :=
  a.common_amplitude_invariant d.angular (fun n i => g.cutoff i n)
    (fun n i => g.amplitude i n) n


-- @@ L6644-6647 verbatim
theorem common_pressure (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.common.pressure n) :=
  a.common_pressure_invariant d.angular (fun n i => g.cutoff i n)
    (fun n i => g.pressure i n) n


-- @@ L6649-6653 verbatim
theorem corrected_amplitude (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((a.commonCorrected s d).amplitude n) :=
  a.commonCorrected_invariant s d d.angular (fun n i => g.cutoff i n)
    (fun n i => g.amplitude i n) g.radius g.radial_field
    (fun _ => CopyAngularInvariance.Invariant.const _) g.phase n


-- @@ L6655-6659 verbatim
theorem good (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.globalGood s d n) :=
  a.globalGood_invariant s d (fun n i => g.cutoff i n) (fun n i => g.amplitude i n)
    (fun n i => g.pressure i n) g.radius g.radial_base g.frequency_base g.axial_base
    g.radial_field (fun _ => CopyAngularInvariance.Invariant.const _) g.phase n


-- @@ L6661-6664 verbatim
theorem gaussian (hf : ∀ n, CopyAngularInvariance.Invariant d.angular (a.source n)) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.globalGaussian d n) :=
  a.globalGaussian_invariant d d.angular (fun n i => g.cutoff i n)
    (fun n i => g.amplitude i n) hf n

-- @@ L6665-6665 verbatim
end NativeAngularGeometry


-- @@ L6667-6667 verbatim
namespace PeriodizedSignedParameters

-- @@ L6668-6671 verbatim
variable {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {κ β : ℝ} {h : p.NativeControl s P κ}
  {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
  (d : NativeDynamics h request) (i₀ : I)


-- @@ L6673-6682 verbatim
include i₀ in
theorem NativeDynamics.phase_eq (hθ : p.directions.angular = (0, 1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (n : ℕ) (x : D) (θ : ℝ) :
    p.base.frequency n * p.base.phase n (x,θ) =
      p.base.frequency n * p.base.phase n (x,0) + (p.angularFrequency n : ℝ) * θ := by
  rw [CopyAngularInvariance.affinePhase_eq_zeroSlice
    (Φ := p.base.phase n) (m := d.slope n)
    (by simpa only [hθ] using (d.angular i₀).phase n) x θ,
    mul_add, ← mul_assoc, hkp]


-- @@ L6684-6703 verbatim
include i₀ in
theorem NativeDynamics.exact_represents (hθ : p.directions.angular = (0, 1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    let z := (p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
        p.directions
    (p.exactBlock s request).oscillation =
      (fun n x i => (vectorMode (p.base.frequency n) (p.base.phase n) (z.amplitude n) x i).re) ∧
    (p.exactBlock s request).oscillatoryPressure =
      (fun n x => (mode (p.base.frequency n) (p.base.phase n) (z.pressure n) x).re) := by
  apply SignedWaveUpdate.blockOfCoefficients_represents
  · intro n x θ
    exact CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using (d.angularGeometry i₀).corrected_amplitude n) x θ
  · intro n x θ
    exact CopyAngularInvariance.invariant_eq_zeroSlice
      (by
        have hp := (d.angularGeometry i₀).common_pressure n
        simp only [hθ] at hp
        exact hp) x θ
  · exact d.phase_eq i₀ hθ hkp


-- @@ L6705-6717 verbatim
include i₀ in
theorem NativeDynamics.good_represents (hθ : p.directions.angular = (0, 1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    (p.goodBlock s request).oscillation = fun n x i =>
      ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s)
        p.directions n x i * carrier (p.base.frequency n) (p.base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
    {p.base with amplitude := ((p.copyData s request).globalGood
      (HarmonicWaveInteraction.productStrip s) p.directions), pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z p.angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using (d.angularGeometry i₀).good n) x θ)
    (fun _ _ _ => rfl) (d.phase_eq i₀ hθ hkp)).1


-- @@ L6719-6731 verbatim
include i₀ in
theorem NativeDynamics.gaussian_represents (hθ : p.directions.angular = (0, 1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    (p.gaussianBlock s request).oscillation = fun n x i =>
      ((p.copyData s request).globalGaussian p.directions n x i *
        carrier (p.base.frequency n) (p.base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
    {p.base with amplitude := (p.copyData s request).globalGaussian p.directions, pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z p.angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using ((d.angularGeometry i₀).gaussian
        (fun _ => CopyAngularInvariance.Invariant.const _) n)) x θ)
    (fun _ _ _ => rfl) (d.phase_eq i₀ hθ hkp)).1


-- @@ L6733-6740 verbatim
theorem frame_common (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) {c : Context D}
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base) :
    WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions
      ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
          p.directions) :=
  ⟨hm.epsilon, hm.radius, hm.radial, hm.angular, hm.axial, hm.time,
    hm.radialBase, hm.angularBase, hm.axialBase⟩


-- @@ L6742-6745 verbatim
theorem exactBlock_zero (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicWaveInteraction.ZeroMode (p.exactBlock s request) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1


-- @@ L6747-6750 verbatim
theorem exactBlock_pressure_zero (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    ∀ n, (p.exactBlock s request).pressure n 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).2


-- @@ L6752-6796 verbatim
include i₀ in
/-- The periodized signed update satisfies the actual context linear
operator, with the computed Gaussian term retained. -/
theorem NativeDynamics.context_linear_identity (hκ : κ ≤ 1 / 2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x i))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (c : Context D) (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request))
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c a (p.exactBlock s request) n x =
      (p.goodBlock s request).oscillation n x + (p.gaussianBlock s request).oscillation n x := by
  let z := (p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
      p.directions
  have hb := h.global_bounds hκ request hR
  have hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain s.domain) :=
    HarmonicResidual.liftDirection_smooth (hrad n)
  have hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain s.domain) :=
      contDiffOn_const
  have hphase := (d.angular i₀).phase_smooth n
  rw [productStrip_domain] at hphase
  have hv (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => z.amplitude n y i)
      (HarmonicResidual.liftDomain s.domain) := by
    simpa only [productStrip_domain] using (CurlClassBounds.class_component hb.2.1 i).smooth n
  have hp : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain s.domain) := by
    have hp := hb.2.2.1.smooth n
    simp only [productStrip_domain] at hp
    exact hp
  have hvrep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillation n =
      fun y i => (vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i).re := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun (d.exact_represents i₀ hm.angular hkp).1 n
  have hprep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillatoryPressure
      n =
      fun y => (mode (z.frequency n) (z.phase n) (z.pressure n) y).re := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun (d.exact_represents i₀ hm.angular hkp).2 n
  rw [linearBlockField_eq_modeResidual s.isOpen_domain c a (p.exactBlock s request)
    (HarmonicWaveInteraction.productStrip s) p.directions z (p.frame_common s request hm)
    n hB hr hz hphase hv hp hvrep hprep ⟨hx, trivial⟩]
  rw [d.good_represents i₀ hm.angular hkp, d.gaussian_represents i₀ hm.angular hkp]
  funext i
  have he := congrArg Complex.re (congrFun (d.common_equation hκ hR n hx) i)
  simpa only [add_mul, Complex.add_re, Pi.add_apply] using he


-- @@ L6798-6854 verbatim
include i₀ in
/-- This is the literal HWI linear remainder of the constructed common
signed block; its class follows from the native quotient and unit ODE. -/
theorem NativeDynamics.linearGood_bounds (hκ : κ ≤ 1 / 2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x i))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (hkpne : ∀ n, p.angularFrequency n ≠ 0)
    (c : Context D) (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request)) :
    (HarmonicWaveInteraction.linearGoodBlock c a (p.exactBlock s request)
      (p.gaussianBlock s request).velocity).WaveBounds s P (β + 1 - 3 * κ) := by
  let zero : HarmonicBlock D := ErrorHarmonics.zeroBlock a.frequency a.phase a.angularFrequency 0
  have hb := h.block_bounds hκ request hR
  have hbs := HarmonicWaveInteraction.waveBounds_smooth hb.2.1 (p.exactBlock_zero s request)
  have hps (n : ℕ) : HarmonicResidual.SmoothCoefficients s.domain ((p.exactBlock s
      request).pressure n) := by
    intro j
    by_cases hj : j = 0
    · subst j
      rw [p.exactBlock_pressure_zero s request n]
      exact contDiffOn_const
    exact (hb.2.2.1 j hj).smooth n
  have hphase (n : ℕ) : ContDiffOn ℝ ∞ (a.phase n) s.domain := by
    rw [← hcarrier.phase]
    exact ((d.angular i₀).phase_smooth n).comp (SignedWaveUpdate.zeroSection (D :=
        D)).contDiff.contDiffOn
      (fun x hx => hx)
  have hkp' (n : ℕ) : a.angularFrequency n ≠ 0 := by
    rw [← hcarrier.angular]
    exact hkpne n
  have hgcarrier : SameCarrier a (p.goodBlock s request) :=
    ⟨hcarrier.frequency, hcarrier.phase, hcarrier.angular⟩
  have hecarrier : SameCarrier a (p.gaussianBlock s request) :=
    ⟨hcarrier.frequency, hcarrier.phase, hcarrier.angular⟩
  have hc := linearGoodBlock_cancel_mem c a (p.exactBlock s request) zero
    (p.goodBlock s request) (p.gaussianBlock s request).velocity hrad
    (fun _ => contDiffOn_const) hB hbs hps hphase hkp'
    (fun n i => ErrorHarmonics.zeroBlock_symmetric _ _ _ _ n i)
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1 hb.2.2.2.2 ?_
  · intro i j hj
    simpa [zero, ErrorHarmonics.zeroBlock, HarmonicFields.constantCoefficient,
      Finsupp.single_apply, hj, Ne.symm hj] using hc i j hj
  · intro n x hx θ i
    have he := congrFun (d.context_linear_identity i₀ hκ hR hkp c hB hrad hm a hcarrier n (x,θ) hx)
        i
    rw [withCarrier_of_same hgcarrier]
    have heval : (HarmonicFields.field ((p.gaussianBlock s request).velocity n i)
        (a.frequency n) (a.phase n) (a.angularFrequency n) (x,θ)).re =
        (p.gaussianBlock s request).oscillation n (x,θ) i := by
      simp only [HarmonicBlock.oscillation, hecarrier.frequency, hecarrier.phase, hecarrier.angular]
    rw [heval]
    simpa only [zero, HarmonicWaveInteraction.withCarrier, ErrorHarmonics.zeroBlock,
      HarmonicBlock.oscillation, HarmonicResidual.field_constant, Pi.zero_apply,
          Complex.ofReal_zero,
      Complex.zero_re, Pi.add_apply, add_zero] using he


-- @@ L6856-6856 verbatim
end PeriodizedSignedParameters


-- @@ L6858-6858 verbatim
end PeriodizedSignedLinear


-- @@ L6860-6860 verbatim
section ParticularLinear

-- @@ L6861-6861 verbatim
open Set WeightedClasses HarmonicCalculus

-- @@ L6862-6862 verbatim
open ParticularWaveBounds LinearWaveBounds

-- @@ L6863-6864 verbatim
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L6866-6885 verbatim
theorem harmonicResidual_reindex (e : D ≃ₗᵢ[ℝ] E) (a : WaveCoefficients E)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : D) :
    (reindexCoefficients e a).harmonicResidual (reindexStrip e s) (reindexDirections e d) n x =
      a.harmonicResidual s d n (e x) := by
  have ht : LinearWaveResidual.timeDirection ((reindexStrip e s).epsilon n)
      ((reindexDirections e d).fastField n) (fun _ => (reindexDirections e d).slow) =
      reindexVector e (LinearWaveResidual.timeDirection (s.epsilon n)
        (d.fastField n) (fun _ => d.slow)) := by
    funext y
    simp only [LinearWaveResidual.timeDirection, GraphDirections.fastField,
      reindexDirections, reindexStrip, reindexVector, map_sub, map_smul]
  unfold WaveCoefficients.harmonicResidual
  rw [reindex_radialField, reindex_axialField, ht]
  exact StateReindex.linearResidual_field_pull e (s.epsilon n) (a.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase
        n))
    (vectorMode (a.frequency n) (a.phase n) (a.amplitude n))
    (mode (a.frequency n) (a.phase n) (a.pressure n)) x


-- @@ L6887-6887 verbatim
open CorrectionState TorusInverse CommonCoverSolve ParticularWaveAssembly CopyAngularInvariance

-- @@ L6888-6888 verbatim
open scoped ContDiff BigOperators


-- @@ L6890-6890 verbatim
namespace ParticularParameters

-- @@ L6891-6896 verbatim
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {p : ParticularParameters Q} {s : StripData (Q × Plane)}
  {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
  {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
  {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
  {h : p.NativeControl s c u b G A j W α κ}


-- @@ L6898-6900 verbatim
theorem NativeDynamics.frequency_ne (d : NativeDynamics h) (n : ℕ) : b.frequency n ≠ 0 := by
  intro hz
  exact d.frequency_nonzero n (by rw [hz, mul_zero])


-- @@ L6902-6905 verbatim
theorem NativeDynamics.good_invariant (d : NativeDynamics h) (n : ℕ) :
    Invariant p.directions.angular ((p.copyData c u b G A j).globalGood (nativeStrip s)
        p.directions n) :=
  d.angularGeometry.good n


-- @@ L6907-6912 verbatim
theorem NativeDynamics.gaussian_invariant (d : NativeDynamics h) (n : ℕ) :
    Invariant p.directions.angular ((p.copyData c u b G A j).globalGaussian p.directions n) := by
  apply d.angularGeometry.gaussian
  intro m
  rw [d.background.angular]
  exact angleLift_invariant (residualSource c u b G A j m)


-- @@ L6914-6938 verbatim
theorem NativeDynamics.section_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) (i : Fin 3) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i +
      residualSource c u b G A j n x.1 i *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) *
            x.2) =
      ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle (x.1,0)) i +
        (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle (x.1,0)) i) *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) *
            x.2) := by
  have hg := d.good_invariant n
  have he := d.gaussian_invariant n
  rw [d.background.angular] at hg he
  have hgs := invariant_angleShuffle hg x.1 x.2
  have hes := invariant_angleShuffle he x.1 x.2
  have hh := congrFun (d.common_equation hκ n (x := angleShuffle x) hx) i
  change (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i +
    residualSource c u b G A j n x.1 i * carrier ((actualCarrier p.background b j).frequency n)
      ((actualCarrier p.background b j).phase n) (angleShuffle x) =
    ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle x) i +
      (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle x) i) *
      carrier ((actualCarrier p.background b j).frequency n)
        ((actualCarrier p.background b j).phase n) (angleShuffle x) at hh
  rw [actualCarrier_character p.background b j d.frequency_ne n x, hgs, hes] at hh
  exact hh


-- @@ L6940-6947 verbatim
theorem NativeDynamics.wave_smooth (d : NativeDynamics h) (hκ : κ ≤ 1 / 2) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => vectorMode ((p.wave s c u b G A j).frequency n)
      ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).amplitude n) (angleShuffle x) i)
      (HarmonicResidual.liftDomain s.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((j : ℝ) * b.frequency n) (d.background.phase_smooth
      n)
    ((CurlClassBounds.class_component (h.global_bounds hκ).2.1 i).smooth n)
  exact hf.comp (angleShuffle (P := Q)).contDiff.contDiffOn (fun _ hx => hx.1)


-- @@ L6949-6956 verbatim
theorem NativeDynamics.pressure_smooth (d : NativeDynamics h) (hκ : κ ≤ 1 / 2) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => mode ((p.wave s c u b G A j).frequency n)
      ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).pressure n) (angleShuffle x))
      (HarmonicResidual.liftDomain s.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((j : ℝ) * b.frequency n) (d.background.phase_smooth
      n)
    ((h.global_bounds hκ).2.2.1.smooth n)
  exact hf.comp (angleShuffle (P := Q)).contDiff.contDiffOn (fun _ hx => hx.1)


-- @@ L6958-6961 verbatim
theorem angleStrip_nativeStrip (s : StripData (Q × Plane)) :
    reindexStrip angleShuffle (nativeStrip s) = HarmonicWaveInteraction.productStrip s := by
  cases s
  rfl


-- @@ L6963-6973 verbatim
theorem frame_wave (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle
          p.background)) :
    WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions)
      (reindexCoefficients angleShuffle (p.wave s c u b G A j)) :=
  ⟨hm.epsilon, hm.radius, hm.radial, hm.angular, hm.axial, hm.time,
    hm.radialBase, hm.angularBase, hm.axialBase⟩


-- @@ L6975-6991 verbatim
theorem native_context_residual (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) =
      LinearWaveResidual.linearResidual (c.operators.epsilon n)
        (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (complexBase c n)
        (fun y => vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
          ((p.wave s c u b G A j).amplitude n) (angleShuffle y))
        (fun y => mode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
          ((p.wave s c u b G A j).pressure n) (angleShuffle y)) x := by
  rw [← harmonicResidual_reindex angleShuffle (p.wave s c u b G A j) (nativeStrip s) p.directions,
    angleStrip_nativeStrip, (p.frame_wave s c u b G A j hm).harmonicResidual]
  rfl


-- @@ L6993-6997 verbatim
variable (p : ParticularParameters Q) (s : StripData (Q × Plane))
  (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
  (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
  (C : ∀ j ∈ modes N, p.NativeControl s c u b G A j W α κ)
  (dyn : ∀ j hj, NativeDynamics (C j hj))


-- @@ L6999-7036 verbatim
include dyn in
theorem update_represents :
    (p.updateBlock s c u b G A N).oscillation =
      (fun n x i => ∑ j ∈ modes N, (vectorMode ((p.wave s c u b G A j).frequency n)
        ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).amplitude n) (angleShuffle x)
            i).re) ∧
    (p.updateBlock s c u b G A N).oscillatoryPressure =
      (fun n x => ∑ j ∈ modes N, (mode ((p.wave s c u b G A j).frequency n)
        ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).pressure n) (angleShuffle x)).re)
            := by
  constructor
  · funext n x i
    rw [updateBlock, assembledBlock_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := (dyn j hj).angularGeometry.corrected_amplitude n
    rw [(dyn j hj).background.angular] at hinv
    have hi : (p.wave s c u b G A j).amplitude n (angleShuffle x) =
        (p.wave s c u b G A j).amplitude n (angleShuffle (x.1,0)) :=
      invariant_angleShuffle hinv x.1 x.2
    change Complex.re (_ * _) = ((p.wave s c u b G A j).amplitude n (angleShuffle x) i *
      carrier ((actualCarrier p.background b j).frequency n) ((actualCarrier p.background b
          j).phase n)
        (angleShuffle x)).re
    rw [actualCarrier_character p.background b j (dyn j hj).frequency_ne n x, hi]
  · funext n x
    rw [updateBlock, assembledBlock_pressure_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := (dyn j hj).angularGeometry.common_pressure n
    rw [(dyn j hj).background.angular] at hinv
    have hi := invariant_angleShuffle hinv x.1 x.2
    change Complex.re (_ * _) = ((p.copyData c u b G A j).common.pressure n (angleShuffle x) *
      carrier ((actualCarrier p.background b j).frequency n) ((actualCarrier p.background b
          j).phase n)
        (angleShuffle x)).re
    rw [actualCarrier_character p.background b j (dyn j hj).frequency_ne n x, hi]
    rfl


-- @@ L7038-7055 verbatim
include dyn in
theorem cancellation_sum (hκ : κ ≤ 1 / 2)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    (fun i => ∑ j ∈ modes N,
      ((p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x)
          i).re) +
      (HarmonicResidual.residualBlock c u b G A).oscillation n x =
        (p.goodBlock s c u b G A N).oscillation n x + (p.gaussianBlock c u b G A N).oscillation n x
            := by
  apply finite_cancellation c u b G A N hN
    (fun j n x => (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n
        (angleShuffle x))
    (fun j n x => (p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle
        (x,0)))
    (fun j n x => (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle (x,0))) n x
  intro j hj i
  exact (dyn j hj).section_equation hκ n x hx i


-- @@ L7057-7107 verbatim
include dyn in
theorem context_linear_sum (hκ : κ ≤ 1 / 2)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c b (p.updateBlock s c u b G A N) n x =
      fun i => ∑ j ∈ modes N,
        ((p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x)
            i).re := by
  have hu := p.update_represents s c u b G A N C dyn
  have hv (j : ℤ) (hj : j ∈ modes N) (i : Fin 3) := (dyn j hj).wave_smooth hκ n i
  have hp (j : ℤ) (hj : j ∈ modes N) := (dyn j hj).pressure_smooth hκ n
  have hvs (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (p.updateBlock s c u b G A N).oscillation n y i) (HarmonicResidual.liftDomain
          s.domain) := by
    rw [hu.1]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hv j hj i))
  have hps : ContDiffOn ℝ ∞ ((p.updateBlock s c u b G A N).oscillatoryPressure n)
      (HarmonicResidual.liftDomain s.domain) := by
    rw [hu.2]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hp j hj))
  have hcarrier : SameCarrier b (p.updateBlock s c u b G A N) := ⟨rfl,rfl,rfl⟩
  have hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain s.domain) :=
    HarmonicResidual.liftDirection_smooth (hrad n)
  rw [linearBlockField_eq_real s.isOpen_domain c b (p.updateBlock s c u b G A N) n hr
    contDiffOn_const hB (by simpa only [withCarrier_of_same hcarrier] using hvs)
    (by simpa only [withCarrier_of_same hcarrier] using hps) ⟨hx,trivial⟩,
    withCarrier_of_same hcarrier, hu.1, hu.2]
  have he := real_linearResidual_sum (Vθ := angularDirection) (modes N)
      (HarmonicResidual.liftDomain_open s.isOpen_domain)
    (c.operators.epsilon n) (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) (timeDirection c n)
    hr contDiffOn_const (show ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain
        s.domain)
      from contDiffOn_const) (contextRealBase c n)
    (fun j y => vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
      ((p.wave s c u b G A j).amplitude n) (angleShuffle y))
    (fun j y => mode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
      ((p.wave s c u b G A j).pressure n) (angleShuffle y)) hv hp
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt
      ((HarmonicResidual.liftDomain_open s.isOpen_domain).mem_nhds ⟨hx,trivial⟩)).differentiableAt
          (by
          simp))
    ⟨hx,trivial⟩
  rw [← complexBase_eq_realLift] at he
  rw [he]
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  rw [p.native_context_residual s c u b G A j hm]


-- @@ L7109-7122 verbatim
include dyn in
theorem context_linear_cancellation (hκ : κ ≤ 1 / 2)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c b (p.updateBlock s c u b G A N) n x +
      (HarmonicResidual.residualBlock c u b G A).oscillation n x =
        (p.goodBlock s c u b G A N).oscillation n x + (p.gaussianBlock c u b G A N).oscillation n x
            := by
  rw [p.context_linear_sum s c u b G A N C dyn hκ hB hrad hm n x hx]
  exact p.cancellation_sum s c u b G A N C dyn hκ hN n x hx


-- @@ L7124-7163 verbatim
include dyn in
/-- The current residual is cancelled by the actual finite inverse. The
remaining coefficient is precisely the computed retained-good block. -/
theorem linearGood_bounds (hκ : κ ≤ 1 / 2)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain)
    (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x) :
    ∀ i j, j ≠ 0 → WaveClass s (fun n x => W n (angleShuffle (x,0)))
      (α + 1 / 2 - 3 * κ) (fun n x =>
        (HarmonicResidual.residualBlock c u b G A).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c b (p.updateBlock s c u b G A N)
          (p.gaussianBlock c u b G A N).velocity).velocity n i j x) := by
  have hb := p.assembled_bounds s c u b G A N C hW hκ
  have hz : HarmonicWaveInteraction.ZeroMode (p.updateBlock s c u b G A N) :=
    (assembledBlock_zero _ _ _ _ _ _).1
  have hpz : ∀ n, (p.updateBlock s c u b G A N).pressure n 0 = 0 :=
    (assembledBlock_zero _ _ _ _ _ _).2
  have hbs := HarmonicWaveInteraction.waveBounds_smooth hb.1 hz
  have hps (n : ℕ) : HarmonicResidual.SmoothCoefficients s.domain
      ((p.updateBlock s c u b G A N).pressure n) := by
    intro j
    by_cases hj : j = 0
    · subst j
      rw [hpz]
      exact contDiffOn_const
    exact (hb.2.1 j hj).smooth n
  apply linearGoodBlock_cancel_mem c b (p.updateBlock s c u b G A N)
    (HarmonicResidual.residualBlock c u b G A) (p.goodBlock s c u b G A N)
    (p.gaussianBlock c u b G A N).velocity hrad (fun _ => contDiffOn_const)
    hB hbs hps hphase hkp (HarmonicResidual.residualBlock_conjugate _ _ _ _ _)
    (assembledBlock_real _ _ _ _ _ _).1 hb.2.2
  intro n x hx θ i
  have he := congrFun (p.context_linear_cancellation s c u b G A N C dyn hκ hN hB hrad hm n (x,θ)
      hx) i
  exact he


-- @@ L7165-7165 verbatim
end ParticularParameters


-- @@ L7167-7167 verbatim
end ParticularLinear


-- @@ L7169-7169 verbatim
section SupportedWaveGain

-- @@ L7170-7170 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L7171-7171 verbatim
open scoped ContDiff Topology

-- @@ L7172-7172 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L7174-7225 verbatim
theorem waveStage_residual_mem_local {s : StripData D} {C : ℕ → Set D} {P : ℕ → D → ℝ} {κ α β H γ :
    ℝ}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1 / 2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (hmean : v.mean = u.mean)
    (hm : IncrementBounds s H u.mean)
    (hbase : SmoothTriple s.domain c.base)
    (a b : HarmonicBlock D) {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : HarmonicWaveInteraction.ZeroMode a) (hb0 : HarmonicWaveInteraction.ZeroMode b)
    (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hkp : ∀ n, a.angularFrequency n ≠ 0)
    (hda : HarmonicWaveInteraction.ModeSolenoidal s c a)
    (hdb : HarmonicWaveInteraction.ModeSolenoidal s c (HarmonicWaveInteraction.withCarrier a b))
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s (fun n (_ : Unit) => C n) 0
      (fun n _ x => HarmonicMeanInteraction.slowNormal c ho hR a.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) a.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (a.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ C n →
      ∀ i j, j ≠ 0 → b.velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (hpa : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (a.pressure n))
    (hpb : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (b.pressure n))
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, HarmonicFields.BandLimited (A₁ n i - A₀ n i) 0)
    (hlinear : ∀ i j, j ≠ 0 → WaveClass s P γ (fun n x =>
      (HarmonicResidual.residualBlock c u a G A₀).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c a b g).velocity n i j x))
    (hγm : γ ≤ β + H - 1 / 2) (hγc : γ ≤ α + β - κ) (hγs : γ ≤ β + β - κ) :
    (HarmonicResidual.residualBlock c v (HarmonicWaveInteraction.addBlock a b) (G + g)
        A₁).WaveBounds
      s P γ := by
  have hnon := LocalizedMeanInteraction.interactionBlock_class c ho hκ hR hm ha hb ha0 hb0 hM hN
    hΦ hk hda hdb hNormal hFreq hAng hz hP0 hP1
  have hca := block_waveBounds_all a ha ha0 hP0
  have hcb := block_waveBounds_all b hb hb0 hP0
  intro i j hj
  apply WaveInteractionBounds.class_congr
    ((hlinear i j hj).add ((hnon i j hj).mono_exponent (le_min hγm (le_min hγc hγs))))
  intro n x hx
  have hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
    contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)
  have he := HarmonicWaveInteraction.residualBlock_wave_update_split s.isOpen_domain c u v hmean
    a b G g A₀ A₁ hA n hr
    contDiffOn_const (hΦ n) (hkp n)
    (fun l => (HarmonicMeanInteraction.tripleField_smooth hbase n l))
    (fun l => (HarmonicMeanInteraction.tripleField_smooth hm.smooth n l))
    (fun l k => (hca l k).smooth n) (fun l k => (hcb l k).smooth n) (hpa n) (hpb n) hx j i
  change _ = _ at he
  linear_combination -he


-- @@ L7227-7227 verbatim
end SupportedWaveGain


-- @@ L7229-7229 verbatim
section ActualRecurrence

-- @@ L7230-7230 verbatim
open Set CorrectionState WeightedClasses

-- @@ L7231-7231 verbatim
open scoped BigOperators


-- @@ L7233-7234 verbatim
/-- Axisymmetric alias: an abbreviation for `ℕ → CyclePoint → Fin 3 → ℝ`. -/
abbrev AxisymmetricAlias := ℕ → CyclePoint → Fin 3 → ℝ


-- @@ L7236-7241 verbatim
/-- Coefficient field, defined pointwise by `(HarmonicFields.field (a n i) (b.frequency n)
(b.phase n) (b.angularFrequency n) x).re`. -/
noncomputable def coefficientField (b : HarmonicBlock CyclePoint)
    (a : HarmonicResidual.BlockCoefficients CyclePoint) : Oscillation CyclePoint :=
  fun n x i => (HarmonicFields.field (a n i) (b.frequency n) (b.phase n) (b.angularFrequency n)
      x).re


-- @@ L7243-7253 verbatim
/-- The axisymmetric alias is kept separately from the spatial labels.
No slot support is imposed on a zero angular mode. -/
structure CycleRepresentation {ι : Type} (v : CycleCoefficients ι)
    (u : State CyclePoint) (axis : AxisymmetricAlias) : Prop where
  velocity : ∀ n x i, u.oscillation n x i = ∑ l ∈ v.labels n, (v.blocks l).oscillation n x i
  pressure : ∀ n x, u.oscillatoryPressure n x = ∑ l ∈ v.labels n, (v.blocks l).oscillatoryPressure
      n x
  gaussian : ∀ n x i, u.errors.gaussian n x i = ∑ l ∈ v.labels n, coefficientField (v.blocks l)
      (v.gaussian l) n x i
  aliasError : ∀ n x i, u.errors.aliasError n x i =
    (∑ l ∈ v.labels n, coefficientField (v.blocks l) (v.aliasCoefficients l) n x i) + axis n x.1 i


-- @@ L7255-7259 verbatim
/-- A common integer bound for stored coefficient values, including errors. -/
structure CoefficientBands {ι : Type} (v : CycleCoefficients ι) : Prop where
  velocityPressure : ∀ l, (v.blocks l).BandLimited v.residualBand
  gaussian : ∀ l n i, HarmonicFields.BandLimited (v.gaussian l n i) v.residualBand
  aliasError : ∀ l n i, HarmonicFields.BandLimited (v.aliasCoefficients l n i) v.residualBand


-- @@ L7261-7261 verbatim
namespace CycleParameters

-- @@ L7262-7263 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L7265-7266 verbatim
theorem particular_carrier (l : ι) : SameCarrier (v.blocks l) (p.particularBlock v c u l) :=
  ⟨rfl,rfl,rfl⟩


-- @@ L7268-7270 verbatim
theorem particularGaussian_carrier (l : ι) : SameCarrier (v.blocks l) (p.particularGaussianBlock v
    c u l) :=
  ⟨rfl,rfl,rfl⟩


-- @@ L7272-7280 verbatim
/-- The new nonzero harmonic data are literal sums of the old and
constructed coefficients. All new mean aliases remain in the separate field. -/
noncomputable def nextCoefficients : CycleCoefficients ι where
  labels := v.labels
  blocks := p.finalBlock v c u
  gaussian := fun l => v.gaussian l + (p.particularGaussianBlock v c u l).velocity +
    (p.signedGaussianBlock v c u l).velocity
  aliasCoefficients := v.aliasCoefficients
  residualBand := 2 * max v.residualBand 1


-- @@ L7282-7288 verbatim
/-- Next axisymmetric alias as an element of `AxisymmetricAlias`. -/
noncomputable def nextAxisymmetricAlias (axis : AxisymmetricAlias) : AxisymmetricAlias :=
  fun n x i => axis n x i +
    VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c
        u) n (x,0) i +
    (VariableGaugeMean.pressureAliasState p.gauge c (p.afterRank v c u) n (x,0) i -
      VariableGaugeMean.pressureAliasState p.gauge c u n (x,0) i)


-- @@ L7290-7298 verbatim
theorem finalBlock_oscillation
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι) :
    (p.finalBlock v c u l).oscillation = (v.blocks l).oscillation +
      (p.particularBlock v c u l).oscillation + (p.signedBlock v c u l).oscillation := by
  have hs : SameCarrier (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l)
      :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  rw [finalBlock, addBlock_oscillation _ _ hs, addBlock_oscillation _ _ (p.particular_carrier v c u
      l)]


-- @@ L7300-7308 verbatim
theorem finalBlock_pressure
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι) :
    (p.finalBlock v c u l).oscillatoryPressure = (v.blocks l).oscillatoryPressure +
      (p.particularBlock v c u l).oscillatoryPressure + (p.signedBlock v c u l).oscillatoryPressure
          := by
  have hs : SameCarrier (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l)
      :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  rw [finalBlock, addBlock_pressure _ _ hs, addBlock_pressure _ _ (p.particular_carrier v c u l)]


-- @@ L7310-7327 verbatim
theorem nextCoefficients_gaussian_field
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (l : ι) (n : ℕ) (x : CyclePoint × ℝ) (i : Fin 3) :
    coefficientField ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).gaussian l)
        n x i =
      coefficientField (v.blocks l) (v.gaussian l) n x i +
        (p.particularGaussianBlock v c u l).oscillation n x i +
        (p.signedGaussianBlock v c u l).oscillation n x i := by
  have hs : SameCarrier (v.blocks l) (p.signedGaussianBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  have hp := p.particularGaussian_carrier v c u l
  change (HarmonicFields.field (v.gaussian l n i +
      (p.particularGaussianBlock v c u l).velocity n i + (p.signedGaussianBlock v c u l).velocity n
          i)
      ((v.blocks l).frequency n) ((v.blocks l).phase n) ((v.blocks l).angularFrequency n) x).re = _
  rw [HarmonicResidual.field_add, HarmonicResidual.field_add, Complex.add_re, Complex.add_re]
  simp only [coefficientField, HarmonicBlock.oscillation, hp.frequency, hp.phase, hp.angular,
    hs.frequency, hs.phase, hs.angular]


-- @@ L7329-7354 verbatim
theorem next_representation {axis : AxisymmetricAlias}
    (hrep : CycleRepresentation v u axis)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) :
    CycleRepresentation (p.nextCoefficients v c u) (p.next v c u)
      (p.nextAxisymmetricAlias v c u axis) := by
  constructor
  · intro n x i
    rw [p.next_oscillation]
    simp only [Pi.add_apply, hrep.velocity n x i, particularVelocity, signedVelocity,
      LabelSumBounds.fieldSum, nextCoefficients, p.finalBlock_oscillation v c u hc,
      Finset.sum_add_distrib]
  · intro n x
    rw [p.next_oscillatoryPressure]
    simp only [Pi.add_apply, hrep.pressure n x, particularPressure, signedPressure,
      nextCoefficients, p.finalBlock_pressure v c u hc, Finset.sum_add_distrib]
  · intro n x i
    rw [p.next_gaussian_error]
    simp only [Pi.add_apply, hrep.gaussian n x i, particularGaussian, signedGaussian,
      LabelSumBounds.fieldSum, p.nextCoefficients_gaussian_field v c u hc,
      show (p.nextCoefficients v c u).labels = v.labels from rfl, Finset.sum_add_distrib]
  · intro n x i
    rw [p.next_alias_error]
    simp only [Pi.add_apply, Pi.sub_apply, hrep.aliasError n x i, nextCoefficients,
      coefficientField, finalBlock, addBlock, nextAxisymmetricAlias]
    simp only [VariableGaugeMean.temporalAliasState, VariableGaugeMean.pressureAliasState]
    ring


-- @@ L7356-7369 verbatim
theorem next_coefficient_bands (h : CoefficientBands v) :
    CoefficientBands (p.nextCoefficients v c u) := by
  have hn : max v.residualBand 1 ≤ 2 * max v.residualBand 1 := by omega
  have hb l : (p.finalBlock v c u l).BandLimited (max v.residualBand 1) := by
    simpa only [max_self] using p.finalBlock_band v c u h.velocityPressure l
  have hg l n i : HarmonicFields.BandLimited
      ((p.nextCoefficients v c u).gaussian l n i) (max v.residualBand 1) := by
    exact (((h.gaussian l n i).mono (le_max_left _ _)).add
      (((p.particularGaussianBlock_band v c u l).1 n i).mono (le_max_left _ _))).add
      ((((p.signed l).gaussianBlock_band p.strip (p.signedRequest v c u)).1 n i).mono (le_max_right
          _ _))
  exact ⟨fun l => ⟨fun n i => ((hb l).1 n i).mono hn, fun n => ((hb l).2 n).mono hn⟩,
    fun l n i => (hg l n i).mono hn,
    fun l n i => (h.aliasError l n i).mono ((le_max_left _ _).trans hn)⟩


-- @@ L7371-7395 verbatim
/-- The residual value bound of the next actual state is derived from
stored coefficient bands, independently of a norm estimate. -/
theorem next_residual_band (h : CoefficientBands v) (l : ι) :
    (HarmonicResidual.residualBlock c (p.next v c u)
      ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).gaussian l)
      ((p.nextCoefficients v c u).aliasCoefficients l)).BandLimited
      (p.nextCoefficients v c u).residualBand := by
  have hb : (p.finalBlock v c u l).BandLimited (max v.residualBand 1) := by
    simpa only [max_self] using p.finalBlock_band v c u h.velocityPressure l
  have hg n i : HarmonicFields.BandLimited
      ((p.nextCoefficients v c u).gaussian l n i) (max v.residualBand 1) := by
    exact (((h.gaussian l n i).mono (le_max_left _ _)).add
      (((p.particularGaussianBlock_band v c u l).1 n i).mono (le_max_left _ _))).add
      ((((p.signed l).gaussianBlock_band p.strip (p.signedRequest v c u)).1 n i).mono (le_max_right
          _ _))
  have ha n i : HarmonicFields.BandLimited
      ((p.nextCoefficients v c u).aliasCoefficients l n i) (max v.residualBand 1) :=
    (h.aliasError l n i).mono (le_max_left _ _)
  have he := HarmonicResidual.residualBlock_band c (p.next v c u) (p.finalBlock v c u l)
    ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l) hb hg
        ha
  have hn : max (max v.residualBand 1 + max v.residualBand 1) (max v.residualBand 1) =
      2 * max v.residualBand 1 := by omega
  simp only [hn] at he
  exact he


-- @@ L7397-7397 verbatim
end CycleParameters


-- @@ L7399-7406 verbatim
/-- The represented state and its literal coefficient data evolve together. -/
structure CycleState (ι : Type) where
  /-- State of `CycleState`, of type `State CyclePoint`. -/
  state : State CyclePoint
  /-- Coefficients of `CycleState`, of type `CycleCoefficients ι`. -/
  coefficients : CycleCoefficients ι
  /-- Axisymmetric alias of `CycleState`, of type `AxisymmetricAlias`. -/
  axisymmetricAlias : AxisymmetricAlias


-- @@ L7408-7408 verbatim
namespace CycleState

-- @@ L7409-7409 verbatim
variable {ι : Type}


-- @@ L7411-7416 verbatim
/-- Step, bundling `state`, `coefficients`, `axisymmetricAlias`. -/
noncomputable def step (p : CycleParameters ι) (c : Context CyclePoint) (u : CycleState ι) :
    CycleState ι where
  state := p.next u.coefficients c u.state
  coefficients := p.nextCoefficients u.coefficients c u.state
  axisymmetricAlias := p.nextAxisymmetricAlias u.coefficients c u.state u.axisymmetricAlias


-- @@ L7418-7423 verbatim
/-- Iterate as an element of `ℕ → CycleState ι | 0 => seed | n + 1 => (iterate p c seed n).step
(p n) c`. -/
noncomputable def iterate (p : ℕ → CycleParameters ι) (c : Context CyclePoint)
    (seed : CycleState ι) : ℕ → CycleState ι
  | 0 => seed
  | n + 1 => (iterate p c seed n).step (p n) c


-- @@ L7425-7426 verbatim
theorem iterate_zero (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed : CycleState ι) :
    iterate p c seed 0 = seed := rfl


-- @@ L7428-7430 verbatim
theorem iterate_succ (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed : CycleState ι) (n
    : ℕ) :
    iterate p c seed (n+1) = (iterate p c seed n).step (p n) c := rfl


-- @@ L7432-7444 verbatim
theorem iterate_representation (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed :
    CycleState ι)
    (hseed : CycleRepresentation seed.coefficients seed.state seed.axisymmetricAlias)
    (hc : ∀ n l, let v := iterate p c seed n
      SameCarrier (v.coefficients.blocks l) ((p n).signedBlock v.coefficients c v.state l)) :
    ∀ n, let v := iterate p c seed n
      CycleRepresentation v.coefficients v.state v.axisymmetricAlias := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    exact (p n).next_representation (iterate p c seed n).coefficients c (iterate p c seed n).state
        ih (hc n)


-- @@ L7446-7454 verbatim
theorem iterate_bands (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed : CycleState ι)
    (hseed : CoefficientBands seed.coefficients) :
    ∀ n, CoefficientBands (iterate p c seed n).coefficients := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    exact (p n).next_coefficient_bands (iterate p c seed n).coefficients c (iterate p c seed
        n).state ih


-- @@ L7456-7464 verbatim
theorem iterate_residual_band (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed :
    CycleState ι)
    (hseed : CoefficientBands seed.coefficients) (n : ℕ) (l : ι) :
    let v := iterate p c seed (n+1)
    (HarmonicResidual.residualBlock c v.state (v.coefficients.blocks l)
      (v.coefficients.gaussian l) (v.coefficients.aliasCoefficients l)).BandLimited
          v.coefficients.residualBand :=
  (p n).next_residual_band (iterate p c seed n).coefficients c (iterate p c seed n).state
    (iterate_bands p c seed hseed n) l


-- @@ L7466-7466 verbatim
end CycleState


-- @@ L7468-7468 verbatim
end ActualRecurrence


-- @@ L7470-7470 verbatim
section PeriodizedCurl

-- @@ L7471-7471 verbatim
open Set Filter WeightedClasses HarmonicCalculus CorrectionState

-- @@ L7472-7472 verbatim
open scoped ContDiff Topology InnerProductSpace


-- @@ L7474-7474 verbatim
variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L7476-7481 verbatim
theorem cylindricalDivergence_reindex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ) (Vr Vθ Vz : E → E) (a : E → ComplexVector) (x : D) :
    cylindricalDivergence (fun y => R (e y)) (StateReindex.vector e Vr)
      (StateReindex.vector e Vθ) (StateReindex.vector e Vz) (fun y => a (e y)) x =
      cylindricalDivergence R Vr Vθ Vz a (e x) := by
  simp only [cylindricalDivergence, StateReindex.along_pull_component]


-- @@ L7483-7483 verbatim
namespace PeriodizedSignedParameters

-- @@ L7484-7486 verbatim
variable {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {κ β : ℝ} (h : p.NativeControl s P κ)
  (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)


-- @@ L7488-7494 verbatim
theorem NativeControl.amplitude_cover (n : ℕ) (i : I) (x : D × ℝ)
    (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain) (hi : x ∈ h.cells.carrier n i) :
    x ∈ h.phasePatch n i ∨ ((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  rcases h.phase_cover n i x hx hi with hC | hcut | hmask
  · exact Or.inl hC
  · exact Or.inr ((p.copyData s request).localized_zero_germs hcut).1
  · exact Or.inr (localized_zero_of_mask request hmask).1


-- @@ L7496-7496 verbatim
variable {h request}


-- @@ L7498-7526 verbatim
theorem NativeDynamics.rawCurlData (d : NativeDynamics h request)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n
          x⟫_ℝ = 0) :
    LocalizedCurlRealization.RawData (p.copyData s request) (HarmonicWaveInteraction.productStrip s)
      p.directions h.phasePatch := by
  apply LocalizedCurlRealization.RawData.of_localClasses
    (fun n i => LocalizedCurlRealization.geometry_restrict (G n)
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.inter (d.open_patch n i))
          inter_subset_left)
    (fun n i => ((d.angular i).phase_smooth n).mono inter_subset_left)
    (LocalizedWaveBounds.LocalClass.of_localJets
      (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (h.envelope_nonneg n x.1 hx)) (h.raw_jets
          request hR).1)
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    d.frequency_nonzero
  · intro n i x hx hzero
    change p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x = 0 at hzero
    have hh := h.normal_lower n i x hx.1 hx.2
    rw [hzero, norm_zero] at hh
    exact (not_le_of_gt h.lower_pos) hh
  · intro n i x hx
    exact LocalizedCurlRealization.signed_coefficients_tangent_at p.base
      (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i)
      (p.normalMotion i) (p.action i) p.column n (ht n i x hx.1 hx.2)


-- @@ L7528-7558 verbatim
theorem NativeDynamics.full_divergence_zero (d : NativeDynamics h request) (i₀ : I)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n
          x⟫_ℝ = 0)
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (c : Context D) (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions
        p.base)
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    cylindricalDivergence (fun q => c.operators.radius q.1) (radialDirection c n)
      angularDirection (axialDirection c n) (fun q i => ((p.exactBlock s request).oscillation n q i
          : ℂ)) x = 0 := by
  have rd := d.rawCurlData hR G ht
  have hd := rd.common_divergence_zero h.cells h.cutoff_support (h.amplitude_cover request) n hx
  change cylindricalDivergence (p.base.radius n) _ _ _ _ x = 0 at hd
  have hs := rd.common_velocity_smooth h.cells h.cutoff_support (h.amplitude_cover request) n
  have hv i := ((contDiffOn_pi.mp hs i).contDiffAt
    ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have he := ParticularWaveAssembly.divergence_map L (p.base.radius n) (p.directions.radialField n)
    (fun _ => p.directions.angular) (p.directions.axialField (HarmonicWaveInteraction.productStrip
        s) n) hv
  rw [hd] at he
  have hθ : angularDirection (D := D) = fun _ => p.directions.angular := by rw [hm.angular]; rfl
  rw [(d.exact_represents i₀ hm.angular hkp).1, ← hm.radius, ← hm.radial, ← hm.axial, hθ]
  · simp only [L, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
      map_zero] at he
    exact he


-- @@ L7560-7581 verbatim
theorem NativeDynamics.modeSolenoidal (d : NativeDynamics h request) (i₀ : I) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n
          x⟫_ℝ = 0)
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (hkpne : ∀ n, p.angularFrequency n ≠ 0)
    (c : Context D) (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions
        p.base) :
    HarmonicWaveInteraction.ModeSolenoidal s c (p.exactBlock s request) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full c (p.exactBlock s request)
  · intro n
    exact ((d.angular i₀).phase_smooth n).comp (SignedWaveUpdate.zeroSection (D :=
        D)).contDiff.contDiffOn
      (fun _ hx => hx)
  · exact hkpne
  · exact HarmonicWaveInteraction.waveBounds_smooth (h.block_bounds hκ request hR).2.1
      (p.exactBlock_zero s request)
  · exact d.full_divergence_zero i₀ hR G ht hkp c hm

-- @@ L7582-7582 verbatim
end PeriodizedSignedParameters


-- @@ L7584-7584 verbatim
open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds LinearWaveBounds


-- @@ L7586-7586 verbatim
namespace ParticularParameters

-- @@ L7587-7592 verbatim
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {p : ParticularParameters Q} {s : StripData (Q × Plane)}
  {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
  {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
  {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
  (h : p.NativeControl s c u b G A j W α κ)


-- @@ L7594-7597 verbatim
theorem NativeControl.amplitude_cover (n : ℕ) (i : Frequency) (x : (Q × ℝ) × Plane)
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.cells.carrier n i) :
    x ∈ h.phasePatch n i ∨ ((p.copyData c u b G A j).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0 :=
  (h.phase_cover n i x hx hi).imp_right (fun hz => (localized_zero_of_source_path hz).1)


-- @@ L7599-7599 verbatim
variable {h}


-- @@ L7601-7619 verbatim
theorem NativeDynamics.rawCurlData (d : NativeDynamics h) :
    LocalizedCurlRealization.RawData (p.copyData c u b G A j) (nativeStrip s)
      p.directions h.phasePatch := by
  apply LocalizedCurlRealization.RawData.of_localClasses
    (fun n i => LocalizedCurlRealization.geometry_restrict (d.background.cylindrical n)
      ((nativeStrip s).isOpen_domain.inter (d.open_patch n i)) inter_subset_left)
    (fun n _ => (d.background.phase_smooth n).mono inter_subset_left)
    (LocalizedWaveBounds.LocalClass.of_localJets
      (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (h.envelope_nonneg n x hx)) h.raw_jets.1)
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    d.frequency_nonzero
  · intro n i x hx hz
    have hh := h.normal_lower n i x hx.1 hx.2
    rw [← h.normal_match n i x hx.1 hx.2, hz, norm_zero] at hh
    exact (not_le_of_gt h.lower_pos) hh
  · intro n i x hx
    exact LocalizedCurlRealization.complexCopyCoefficients_tangent_at
      (p.copyData c u b G A j).background p.length_pos h.realControl h.imagControl n i hx.1 hx.2
      (h.normal_match n i x hx.1 hx.2)


-- @@ L7621-7627 verbatim
theorem NativeDynamics.common_divergence_zero (d : NativeDynamics h) (n : ℕ)
    {x : (Q × ℝ) × Plane} (hx : x ∈ (nativeStrip s).domain) :
    cylindricalDivergence (p.background.radius n) (p.directions.radialField n)
      (fun _ => p.directions.angular) (p.directions.axialField (nativeStrip s) n)
      (vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
        ((p.wave s c u b G A j).amplitude n)) x = 0 :=
  d.rawCurlData.common_divergence_zero h.cells h.cutoff_support h.amplitude_cover n hx



-- @@ L7630-7660 verbatim
theorem native_context_divergence (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane))
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (a : ((Q × ℝ) × Plane) → ComplexVector) (n : ℕ) (x : (Q × Plane) × ℝ) :
    cylindricalDivergence (fun y => c.operators.radius y.1) (radialDirection c n)
      angularDirection (axialDirection c n) (fun y => a (angleShuffle y)) x =
      cylindricalDivergence (p.background.radius n) (p.directions.radialField n)
        (fun _ => p.directions.angular) (p.directions.axialField (nativeStrip s) n) a (angleShuffle
            x) := by
  have hr : StateReindex.vector (angleShuffle (P := Q)) (p.directions.radialField n) =
      radialDirection c n :=
    (reindex_radialField (angleShuffle (P := Q)) p.directions n).symm.trans (hm.radial n)
  have hz : StateReindex.vector (angleShuffle (P := Q)) (p.directions.axialField (nativeStrip s) n)
      =
      axialDirection c n := by
    change reindexVector (angleShuffle (P := Q)) (p.directions.axialField (nativeStrip s) n) = _
    rw [← reindex_axialField (angleShuffle (P := Q)) p.directions (nativeStrip s) n,
        angleStrip_nativeStrip]
    exact hm.axial n
  have hθ : StateReindex.vector (angleShuffle (P := Q)) (fun _ => p.directions.angular) =
      angularDirection (D := Q × Plane) := by
    funext y
    exact hm.angular
  have hR : (fun y => p.background.radius n (angleShuffle y)) =
      (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) := hm.radius n
  have he := cylindricalDivergence_reindex (angleShuffle (P := Q)) (p.background.radius n)
    (p.directions.radialField n) (fun _ => p.directions.angular)
    (p.directions.axialField (nativeStrip s) n) a x
  rw [hr, hz, hθ, hR] at he
  exact he



-- @@ L7663-7667 verbatim
variable (p : ParticularParameters Q) (s : StripData (Q × Plane))
  (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
  (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
  (C : ∀ j ∈ modes N, p.NativeControl s c u b G A j W α κ)
  (dyn : ∀ j hj, NativeDynamics (C j hj))


-- @@ L7669-7686 verbatim
include dyn in
theorem full_divergence_zero (hκ : κ ≤ 1 / 2)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    cylindricalDivergence (fun y => c.operators.radius y.1) (radialDirection c n)
      angularDirection (axialDirection c n)
      (fun y i => ((p.updateBlock s c u b G A N).oscillation n y i : ℂ)) x = 0 := by
  rw [(p.update_represents s c u b G A N C dyn).1]
  apply real_divergence_sum_zero (modes N)
  · intro j hj i
    exact (((dyn j hj).wave_smooth hκ n i).contDiffAt
      ((HarmonicResidual.liftDomain_open s.isOpen_domain).mem_nhds ⟨hx,trivial⟩)).differentiableAt
          (by
          simp)
  · intro j hj
    rw [p.native_context_divergence s c hm]
    exact (dyn j hj).common_divergence_zero n hx


-- @@ L7688-7699 verbatim
include dyn in
theorem modeSolenoidal (hκ : κ ≤ 1 / 2)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain)
    (hkp : ∀ n, b.angularFrequency n ≠ 0) :
    HarmonicWaveInteraction.ModeSolenoidal s c (p.updateBlock s c u b G A N) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full c (p.updateBlock s c u b G A N) hphase hkp
  · exact HarmonicWaveInteraction.waveBounds_smooth (p.assembled_bounds s c u b G A N C hW hκ).1
      (assembledBlock_zero _ _ _ _ _ _).1
  · exact p.full_divergence_zero s c u b G A N C dyn hκ hm


-- @@ L7701-7701 verbatim
end ParticularParameters


-- @@ L7703-7703 verbatim
end PeriodizedCurl


-- @@ L7705-7705 verbatim
section UniformCycleGains

-- @@ L7706-7706 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L7707-7707 verbatim
open LabelSumBounds UniformHarmonicInteraction

-- @@ L7708-7708 verbatim
open scoped ContDiff Topology

-- @@ L7709-7709 verbatim
variable {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L7711-7739 verbatim
/-- Coefficient extraction preserves constants chosen before the spatial
label. The identity concerns the actual linear field and retained Gaussian. -/
theorem linearGoodBlock_cancel_uniform {s : StripData D} {P : ι → ℕ → D → ℝ} {γ : ℝ}
    (c : Context D) (a b source good : ι → HarmonicBlock D)
    (g : ι → HarmonicResidual.BlockCoefficients D)
    (hr : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hz : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial s.domain)
    (hB : SmoothTriple s.domain c.base)
    (hb : ∀ l n i, HarmonicResidual.SmoothCoefficients s.domain ((b l).velocity n i))
    (hp : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hs : ∀ l n i, HarmonicFields.ConjugateSymmetric ((source l).velocity n i))
    (hg : ∀ l n i, HarmonicFields.ConjugateSymmetric ((good l).velocity n i))
    (hgood : UniformVelocity s P γ good)
    (hcancel : ∀ l n x, x ∈ s.domain → ∀ θ i, linearBlockField c (a l) (b l) n (x, θ) i +
      (HarmonicWaveInteraction.withCarrier (a l) (source l)).oscillation n (x, θ) i =
      (HarmonicWaveInteraction.withCarrier (a l) (good l)).oscillation n (x, θ) i +
      (HarmonicFields.field (g l n i) ((a l).frequency n) ((a l).phase n)
        ((a l).angularFrequency n) (x, θ)).re) :
    ∀ i j, j ≠ 0 → UniformWaveClass s P γ (fun l n x => (source l).velocity n i j x +
      (HarmonicWaveInteraction.linearGoodBlock c (a l) (b l) (g l)).velocity n i j x) := by
  intro i j hj
  apply (hgood i j hj).congr
  intro l n x hx
  exact (linearGoodBlock_cancel s.isOpen_domain c (a l) (b l) (source l) (good l) (g l) n
    (hr n) (hz n) (fun k => HarmonicMeanInteraction.tripleField_smooth hB n k)
    (hb l n) (hp l n) (hΦ l n) (hkp l n) (hs l n) (hg l n) hx j hj i
    (fun θ => hcancel l n x hx θ i)).symm


-- @@ L7741-7793 verbatim
/-- The exact nonlinear update preserves the joint label/band estimate.
All three wave products and the support-local mean interaction are retained. -/
theorem waveStage_residual_uniform {s : StripData D} {P : ι → ℕ → D → ℝ}
    {κ α β H γ : ℝ} {C : ℕ → ι → Set D}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1 / 2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (hmean : v.mean = u.mean) (hm : IncrementBounds s H u.mean)
    (hbase : SmoothTriple s.domain c.base)
    (a b : ι → HarmonicBlock D) {M N : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l))
    (hb0 : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hda : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (a l))
    (hdb : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (HarmonicWaveInteraction.withCarrier (a
        l) (b l)))
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (a l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s C (-(1 / 2)) (fun n l _ => (a l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s C (-(1 / 2)) (fun n l _ => ((a l).angularFrequency
        n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hpa : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((a l).pressure n))
    (hpb : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    (G g A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D)
    (hA : ∀ l n i, HarmonicFields.BandLimited (A₁ l n i - A₀ l n i) 0)
    (hlinear : ∀ i j, j ≠ 0 → UniformWaveClass s P γ (fun l n x =>
      (HarmonicResidual.residualBlock c u (a l) (G l) (A₀ l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (a l) (b l) (g l)).velocity n i j x))
    (hγm : γ ≤ β + H - 1 / 2) (hγc : γ ≤ α + β - κ) (hγs : γ ≤ 2 * β - κ) :
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c v
      (HarmonicWaveInteraction.addBlock (a l) (b l)) (G l + g l) (A₁ l)) := by
  have hca l := block_waveBounds_all (a l) (waveBounds_each ha l) (ha0 l) (hP0 l)
  have hcb l := block_waveBounds_all (b l) (waveBounds_each hb l) (hb0 l) (hP0 l)
  intro i j hj
  have hnon := UniformHarmonicInteraction.interactionBlock_uniform c ho hκ hR hm ha hb ha0 hb0 hM hN
    hΦ hk hda hdb hNormal hFreq hAng hz hP0 hP1 hj i
  apply ((hlinear i j hj).add (hnon.mono_exponent (le_min hγm (le_min hγc hγs)))).congr
  intro l n x hx
  have hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
    contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)
  have he := HarmonicWaveInteraction.residualBlock_wave_update_split s.isOpen_domain c u v hmean
    (a l) (b l) (G l) (g l) (A₀ l) (A₁ l) (hA l) n hr contDiffOn_const (hΦ l n) (hkp l n)
    (fun k => HarmonicMeanInteraction.tripleField_smooth hbase n k)
    (fun k => HarmonicMeanInteraction.tripleField_smooth hm.smooth n k)
    (fun k m => (hca l k m).smooth n) (fun k m => (hcb l k m).smooth n) (hpa l n) (hpb l n) hx j i
  change _ = _ at he
  linear_combination -he


-- @@ L7795-7836 verbatim
/-- The unchanged oscillation retains a uniform residual estimate after
an actual mean increment; pressure recomputation and axisymmetric aliases
may change freely. -/
theorem meanStage_residual_uniform {s : StripData D} {P : ι → ℕ → D → ℝ}
    {κ α H γ : ℝ} {C : ℕ → ι → Set D}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1 / 2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (h : Triple D) (he : v.mean = updated u.mean h)
    (hbase : SmoothTriple s.domain c.base) (hm : SmoothTriple s.domain u.mean)
    (hh : IncrementBounds s H h) (b : ι → HarmonicBlock D) (hb : UniformVelocity s P α b)
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (b l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s C (-(1 / 2)) (fun n l _ => (b l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s C (-(1 / 2)) (fun n l _ => ((b l).angularFrequency
        n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (G A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D)
    (hA : ∀ l n i, HarmonicFields.BandLimited (A₁ l n i - A₀ l n i) 0)
    (hold : UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A₀ l)))
    (hγ : γ ≤ α + H - 1 / 2) :
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c v (b l) (G l) (A₁ l)) := by
  intro i j hj
  have hdelta := LocalizedMeanInteraction.uniform_realMeanCross_class c ho hκ hR hh hb
    hNormal hFreq hAng hz hj i
  apply ((hold i j hj).add (hdelta.mono_exponent hγ)).congr
  intro l n x hx
  have hm' := (s.isOpen_domain.mem_nhds hx)
  have hd := HarmonicMeanInteraction.residualBlock_axisymmetric_alias_update c u v h he (b l)
    (G l) (A₀ l) (A₁ l) (hA l) n
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hbase n k).contDiffAt
        hm').differentiableAt (by
        simp))
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hm n k).contDiffAt hm').differentiableAt
        (by
        simp))
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hh.smooth n k).contDiffAt
        hm').differentiableAt (by
        simp))
    hj i
  change _ = _ at hd
  linear_combination -hd


-- @@ L7838-7838 verbatim
end UniformCycleGains


-- @@ L7840-7840 verbatim
section ConstructedWaveGains

-- @@ L7841-7841 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L7842-7842 verbatim
open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds

-- @@ L7843-7843 verbatim
open scoped ContDiff Topology InnerProductSpace

-- @@ L7844-7844 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L7846-7848 verbatim
theorem meanIncrement_of_cumulative {s : StripData D} {m : Triple D}
    (h : MeanIncrementBounds.CumulativeBounds s m) : IncrementBounds s (9/10) m :=
  ⟨by convert! h.radial using 1; norm_num, h.angular, h.axial⟩


-- @@ L7850-7858 verbatim
theorem pressureBounds_smooth {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {b : HarmonicBlock D} (h : b.PressureBounds s P α) (hz : ∀ n, b.pressure n 0 = 0)
    (n : ℕ) : HarmonicResidual.SmoothCoefficients s.domain (b.pressure n) := by
  intro j
  by_cases hj : j = 0
  · subst j
    rw [hz]
    exact contDiffOn_const
  · exact (h j hj).smooth n


-- @@ L7860-7863 verbatim
theorem operator_radial_smooth {s : StripData D} {κ : ℝ} {c : Context D}
    (ho : OperatorBounds s c.operators κ) (n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
  contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)


-- @@ L7865-7865 verbatim
namespace ParticularParameters

-- @@ L7866-7866 verbatim
open TorusInverse

-- @@ L7867-7867 verbatim
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]


-- @@ L7869-7921 verbatim
theorem residual_gain_local
    (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u v : State (Q × Plane)) (hmean : v.mean = u.mean)
    (b : HarmonicBlock (Q × Plane)) (G A : HarmonicResidual.BlockCoefficients (Q × Plane))
    {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ} {M N : ℕ}
    (C : ∀ j ∈ modes N, p.NativeControl s c u b G A j W α κ)
    (dyn : ∀ j hj, NativeDynamics (C j hj))
    (hα : 7 / 10 ≤ α) (hκ : κ ≤ 1 / 100000)
    (ho : OperatorBounds s c.operators κ) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hb : BaseBounds s c.base) (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x)
    (hWone : ∀ n x, x ∈ s.domain → W n (angleShuffle (x, 0)) ≤ 1)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (hold : b.WaveBounds s (fun n x => W n (angleShuffle (x, 0))) (1 / 2))
    (hold0 : HarmonicWaveInteraction.ZeroMode b) (holdBand : b.BandLimited M)
    (hsourceBand : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (hphase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain)
    (hk : ∀ n, b.frequency n ≠ 0) (hkp : ∀ n, b.angularFrequency n ≠ 0)
    (hdiv : HarmonicWaveInteraction.ModeSolenoidal s c b)
    (hpress : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (b.pressure n))
    {patch : ℕ → Set (Q × Plane)}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s (fun n (_ : Unit) => patch n) 0
      (fun n _ x => HarmonicMeanInteraction.slowNormal c ho hR b.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) b.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ patch n → ∀ i j, j ≠ 0 →
      (p.updateBlock s c u b G A N).velocity n i j =ᶠ[𝓝 x] fun _ => 0) :
    (HarmonicResidual.residualBlock c v
      (HarmonicWaveInteraction.addBlock b (p.updateBlock s c u b G A N))
      (G + (p.gaussianBlock c u b G A N).velocity) A).WaveBounds
      s (fun n x => W n (angleShuffle (x,0))) (α + 1/10) := by
  have hκhalf : κ ≤ 1/2 := by linarith
  have hbounds := p.assembled_bounds s c u b G A N C hW hκhalf
  have hzmode : HarmonicWaveInteraction.ZeroMode (p.updateBlock s c u b G A N) :=
    (assembledBlock_zero _ _ _ _ _ _).1
  have hzpress : ∀ n, (p.updateBlock s c u b G A N).pressure n 0 = 0 :=
    (assembledBlock_zero _ _ _ _ _ _).2
  have hnewdiv : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier b (p.updateBlock s c u b G A N)) := by
    rw [withCarrier_of_same (show SameCarrier b (p.updateBlock s c u b G A N) from ⟨rfl,rfl,rfl⟩)]
    exact p.modeSolenoidal s c u b G A N C dyn hκhalf hW hm hphase hkp
  apply waveStage_residual_mem_local c ho hκhalf hR u v hmean (meanIncrement_of_cumulative hu)
    hb.smooth b (p.updateBlock s c u b G A N) hold hbounds.1 hold0 hzmode holdBand
    (p.updateBlock_band s c u b G A N) hphase hk hkp hdiv hnewdiv hNormal hFreq hAng hz
    (fun n x hx => hW n _ hx) hWone hpress (pressureBounds_smooth hbounds.2.1 hzpress)
    G (p.gaussianBlock c u b G A N).velocity A A
    (fun n i => by
        rw [sub_self]; exact HarmonicResidual.band_zero _) _ (by
            linarith) (by linarith) (by linarith)
  intro i j hj
  exact (p.linearGood_bounds s c u b G A N C dyn hκhalf hsourceBand hb.smooth
    (operator_radial_smooth ho) hm hphase hkp hW i j hj).mono_exponent (by linarith)


-- @@ L7923-7923 verbatim
end ParticularParameters


-- @@ L7925-7925 verbatim
namespace PeriodizedSignedParameters

-- @@ L7926-7928 verbatim
variable {I : Type} {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {B κ : ℝ} {h : p.NativeControl s P κ}
  {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}


-- @@ L7930-7983 verbatim
theorem NativeDynamics.residual_gain_local (d : NativeDynamics h request) (i₀ : I)
    (hB : 7 / 10 ≤ B) (hκ : κ ≤ 1 / 100000)
    (hRquest : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ)
      (fun n x => request n x j))
    (geom : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n
          x⟫_ℝ = 0)
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (hkpne : ∀ n, p.angularFrequency n ≠ 0)
    (c : Context D) (u v : State D) (hmean : v.mean = u.mean)
    (ho : OperatorBounds s c.operators κ) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hbase : BaseBounds s c.base) (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request))
    (ha : a.WaveBounds s P (1 / 2)) (ha0 : HarmonicWaveInteraction.ZeroMode a)
    {M : ℕ} (hM : a.BandLimited M)
    (hphase : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain)
    (hk : ∀ n, a.frequency n ≠ 0) (hka : ∀ n, a.angularFrequency n ≠ 0)
    (hdiv : HarmonicWaveInteraction.ModeSolenoidal s c a)
    (hpress : ∀ n, HarmonicResidual.SmoothCoefficients s.domain (a.pressure n))
    {patch : ℕ → Set D}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s (fun n (_ : Unit) => patch n) 0
      (fun n _ x => HarmonicMeanInteraction.slowNormal c ho hR a.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) a.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (a.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ patch n → ∀ i j, j ≠ 0 →
      (p.exactBlock s request).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (G A : HarmonicResidual.BlockCoefficients D)
    (hold : (HarmonicResidual.residualBlock c u a G A).WaveBounds s P (B + 1 / 10)) :
    (HarmonicResidual.residualBlock c v
      (HarmonicWaveInteraction.addBlock a (p.exactBlock s request))
      (G + (p.gaussianBlock s request).velocity) A).WaveBounds s P (B+1/10) := by
  have hκhalf : κ ≤ 1/2 := by linarith
  have hbounds := h.block_bounds hκhalf request hRquest
  have hnewdiv : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)) := by
    rw [withCarrier_of_same hcarrier]
    exact d.modeSolenoidal i₀ hκhalf hRquest geom ht hkp hkpne c hm
  apply waveStage_residual_mem_local c ho hκhalf hR u v hmean (meanIncrement_of_cumulative hu)
    hbase.smooth a (p.exactBlock s request) ha hbounds.2.1 ha0 (p.exactBlock_zero s request)
    hM (p.exactBlock_band s request) hphase hk hka hdiv hnewdiv hNormal hFreq hAng hz
    h.envelope_nonneg hP1 hpress (pressureBounds_smooth hbounds.2.2.1 (p.exactBlock_pressure_zero s
        request))
    G (p.gaussianBlock s request).velocity A A
    (fun n i => by
        rw [sub_self]; exact HarmonicResidual.band_zero _) _ (by
            linarith) (by linarith) (by linarith)
  intro i j hj
  exact (hold i j hj).add ((d.linearGood_bounds i₀ hκhalf hRquest hkp hkpne c hbase.smooth
    (operator_radial_smooth ho) hm a hcarrier i j hj).mono_exponent (by linarith))


-- @@ L7985-7985 verbatim
end PeriodizedSignedParameters


-- @@ L7987-7987 verbatim
end ConstructedWaveGains


-- @@ L7989-7989 verbatim
section ConstructedWaveMeans

-- @@ L7990-7991 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean
    LocalSignedRequest

-- @@ L7992-7992 verbatim
open scoped ContDiff BigOperators Topology


-- @@ L7994-7994 verbatim
section CovarianceAssembly

-- @@ L7995-7995 verbatim
variable {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L7997-8027 verbatim
theorem assembledCovarianceIncrement_mem
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → LabelSumBounds.WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (a b : ι → HarmonicBlock D) (N : ℕ)
    (hNa : ∀ l, (a l).BandLimited N) (hNb : ∀ l, (b l).BandLimited N)
    (hcarrier : ∀ l, LabelSumBounds.SameCarrier (a l) (b l))
    (ha : UniformHarmonicInteraction.UniformVelocity s P α a)
    (hb : UniformHarmonicInteraction.UniformVelocity s P β b)
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l))
    (hb0 : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hsu : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (a l).oscillation))
    (hsv : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (b l).oscillation))
    (u : State D)
    (hrep : u.oscillation = LabelSumBounds.fieldSum labels (fun l => (a l).oscillation)) :
    SignedMeanGain.TensorClass s (α + β)
      (SignedMeanGain.covarianceIncrement u.oscillation
        (LabelSumBounds.fieldSum labels (fun l => (b l).oscillation))) := by
  rw [hrep]
  exact fun i j => LabelSumBounds.harmonic_covariance_increment_sum_mem hαβ labels label hinj hlevel
    χ hχ Y a b N hNa hNb hcarrier
    (LabelSumBounds.uniform_coefficients_of_nonzero a ha ha0 hP0)
    (LabelSumBounds.uniform_coefficients_of_nonzero b hb hb0 hP0) hP0 hP1 hkp hsu hsv i j


-- @@ L8029-8029 verbatim
end CovarianceAssembly


-- @@ L8031-8031 verbatim
section WavePressureDebt

-- @@ L8032-8035 verbatim
variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

-- @@ L8036-8037 verbatim
local notation "st" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
    hεone hL

-- @@ L8038-8038 verbatim
local notation "ss" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL

-- @@ L8039-8050 verbatim
variable (c : Context Point) (u : State Point) (w : Oscillation Point)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular U g.radial.inner g.radial.outer (u.covariance i j))
    (hX : ∀ i j, GaugeDebtIncrement.Regular U g.radial.inner g.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    {κ α : ℝ} (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL
        hcR ε L hε hεone hL) c.operators κ)
    (hcX : SignedMeanGain.TensorClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL
        hcR ε L hε hεone hL) α (SignedMeanGain.covarianceIncrement u.oscillation w))


-- @@ L8052-8069 verbatim
include hd hell hop hbase hm hW hX ho hcX in
theorem gaugeWaveStage_pressure_from_covariance
    (hfixed : (reconstructState g c u).pressure = u.pressure) :
    MeanClass st (α-κ) (SignedMeanGain.pressureChange g c u w q gaussian) := by
  let v := SignedMeanGain.waveStage g c u w q gaussian
  have hmu := GaugeDebtIncrement.waveStage_mean_regular U g c u w q gaussian hm
  have hvW := GaugeDebtIncrement.waveStage_covariance_regular U g c u w q gaussian hW hX
  have hgu := hm.gr ha g.radial.inner_lt_outer hbase hop u.covariance hW
  have hgv := hmu.gr ha g.radial.inner_lt_outer hbase hop v.covariance hvW
  have hgr : MeanClass st (α-κ) (v.gr c - u.gr c) := by
    apply class_congr (SignedMeanGain.radialCovarianceChange_mem ho hcX)
    intro n x hx
    exact GaugeDebtIncrement.waveStage_gr_agree U ha g.radial.inner_lt_outer g c u w q gaussian
      hop hbase hm hW hX n hx.1
  have hp := reconstructState_pressure_change_class U g ha hd hcL hcR ε L hε hεone hL hell
    c v u hgv.smooth hgu.smooth hgv.supported hgu.supported hgr
  simp only [hfixed] at hp
  exact hp


-- @@ L8071-8112 verbatim
include hd hell hop hbase hm hW hX ho hcX in
theorem gaugeWaveStage_mean_from_covariance
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hb : BaseBounds st c.base) (hu : CorrectionState.CumulativeBounds st u)
    (hα : 9 / 10 ≤ α - κ) {β : ℝ} (hβ : β ≤ α - κ)
    (hθ : MeanClass st β (u.thetaResidual c))
    (hz : MeanClass st β (u.axialResidual c))
    (hdebt : ∀ i : Fin 3, UnweightedClass ss β (fun n x => debt c u n x i)) :
    let v := SignedMeanGain.waveStage g c u w q gaussian
    MeanClass st (α-κ) (SignedMeanGain.pressureChange g c u w q gaussian) ∧
    CorrectionState.CumulativeBounds st v ∧
    MeanClass st β (v.thetaResidual c) ∧
    MeanClass st β (v.axialResidual c) ∧
    (∀ i : Fin 3, UnweightedClass ss β (fun n x => debt c v n x i)) := by
  let v := SignedMeanGain.waveStage g c u w q gaussian
  have hp := gaugeWaveStage_pressure_from_covariance U g ha hd hcL hcR ε L hε hεone hL hell
    c u w q gaussian hop hbase hm hW hX ho hcX hfixed
  have hWs : ∀ i j, SmoothOn (st).domain (u.covariance i j) :=
    fun i j n => ((hW i j).smooth n).mono (fun _ hx => hx.1)
  have ht : MeanClass st (α-κ) (v.thetaResidual c - u.thetaResidual c) := by
    apply class_congr (SignedMeanGain.thetaCovarianceChange_mem ho hcX)
    exact SignedMeanGain.waveStage_theta_change (st).isOpen_domain g c u w q gaussian
      hb.smooth hu.velocity.smooth hWs (fun i j => (hcX i j).smooth)
  have hz' : MeanClass st (α-κ) (v.axialResidual c - u.axialResidual c) := by
    apply class_congr ((SignedMeanGain.axialCovarianceChange_mem ho hcX).add
      ((ho.dz hp).mono_exponent (by linarith)))
    exact SignedMeanGain.waveStage_axial_change (st).isOpen_domain g c u w q gaussian
      hb.smooth hu.velocity.smooth hWs (fun i j => (hcX i j).smooth) hu.pressure.smooth hp.smooth
  refine ⟨hp, gaugeWaveStage_cumulative g c u w q ⟨0,gaussian,0⟩ hu hp hα, ?_, ?_, ?_⟩
  · apply class_congr (hθ.add (ht.mono_exponent hβ))
    intro n x hx
    change v.thetaResidual c n x = u.thetaResidual c n x + (v.thetaResidual c n x - u.thetaResidual
        c n x)
    ring
  · apply class_congr (hz.add (hz'.mono_exponent hβ))
    intro n x hx
    change v.axialResidual c n x = u.axialResidual c n x + (v.axialResidual c n x - u.axialResidual
        c n x)
    ring
  · exact GaugeDebtIncrement.debt_mem_after_change ss c u v le_rfl hβ hdebt
      (GaugeDebtIncrement.waveStage_debt_change_mem U ha g.radial.inner_lt_outer hcL hcR
        ε L hε hεone hL g c u w q gaussian hop hbase hm hW hX ho hcX)


-- @@ L8114-8114 verbatim
end WavePressureDebt


-- @@ L8116-8116 verbatim
end ConstructedWaveMeans


-- @@ L8118-8118 verbatim
section CycleSignedFamily

-- @@ L8119-8119 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L8120-8120 verbatim
open scoped ContDiff Topology BigOperators


-- @@ L8122-8122 verbatim
namespace CycleParameters

-- @@ L8123-8124 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L8126-8128 verbatim
/-- Before signed block, given by `addBlock (v.blocks l) (p.particularBlock v c u l)`. -/
noncomputable def beforeSignedBlock (l : ι) : HarmonicBlock CyclePoint :=
  addBlock (v.blocks l) (p.particularBlock v c u l)


-- @@ L8130-8132 verbatim
/-- Signed tangent, given by `(p.signed l).tangentBlock p.strip (p.signedRequest v c u)`. -/
noncomputable def signedTangent (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).tangentBlock p.strip (p.signedRequest v c u)


-- @@ L8134-8136 verbatim
/-- Signed curl, given by `(p.signed l).curlBlock p.strip (p.signedRequest v c u)`. -/
noncomputable def signedCurl (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).curlBlock p.strip (p.signedRequest v c u)


-- @@ L8138-8146 verbatim
theorem beforeSignedBlock_represents {axis : AxisymmetricAlias}
    (hrep : CycleRepresentation v u axis) :
    (p.afterParticular v c u).oscillation =
      LabelSumBounds.fieldSum v.labels (fun l => (p.beforeSignedBlock v c u l).oscillation) := by
  funext n x i
  change u.oscillation n x i + p.particularVelocity v c u n x i = _
  rw [hrep.velocity n x i]
  simp only [beforeSignedBlock, addBlock_oscillation _ _ (p.particular_carrier v c u _),
    LabelSumBounds.fieldSum, particularVelocity, Pi.add_apply, Finset.sum_add_distrib]


-- @@ L8148-8155 verbatim
theorem signedVelocity_split :
    p.signedVelocity v c u =
      LabelSumBounds.fieldSum v.labels (fun l => (p.signedTangent v c u l).oscillation) +
      LabelSumBounds.fieldSum v.labels (fun l => (p.signedCurl v c u l).oscillation) := by
  funext n x i
  simp only [signedVelocity, signedBlock, signedTangent, signedCurl,
    PeriodizedSignedParameters.exactBlock_split, LabelSumBounds.fieldSum,
    Pi.add_apply, Finset.sum_add_distrib]


-- @@ L8157-8159 verbatim
theorem block_band_mono {b : HarmonicBlock CyclePoint} {N M : ℕ}
    (h : b.BandLimited N) (hle : N ≤ M) : b.BandLimited M :=
  ⟨fun n i => (h.1 n i).mono hle, fun n => (h.2 n).mono hle⟩


-- @@ L8161-8218 verbatim
/-- The family in the signed covariance identity is computed from the
current cycle, including its actual particular increment and signed curl. -/
noncomputable def signedFamily
    (primary : ι → HarmonicBlock CyclePoint) (P : ι → ℕ → CyclePoint → ℝ)
    {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (N : ℕ)
    (hprimary : ∀ l, (primary l).BandLimited N) (hband : CoefficientBands v)
    (hcp : ∀ l, SameCarrier (v.blocks l) (primary l))
    (hcs : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17 / 25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ - κ)
      (fun l n x => (p.signedTangent v c u l).velocity n i j x))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 + σ - 2 * κ)
      (fun l n x => (p.signedCurl v c u l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ p.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ p.strip.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0) :
    LabelSumBounds.SignedFamily p.strip P (1/2) (17/25) (1/2+σ-κ) (1+σ-2*κ) where
  primary := primary
  old := p.beforeSignedBlock v c u
  tangent := p.signedTangent v c u
  curl := p.signedCurl v c u
  bandwidth := max (max N v.residualBand) 1
  primary_band l := block_band_mono (hprimary l) ((le_max_left _ _).trans (le_max_left _ _))
  old_band l := block_band_mono
    (show (p.beforeSignedBlock v c u l).BandLimited v.residualBand from by
      have hb := addBlock_band (hband.velocityPressure l) (p.particularBlock_band v c u l)
      simp only [max_self] at hb
      exact hb)
    ((le_max_right _ _).trans (le_max_left _ _))
  tangent_band l := block_band_mono ((p.signed l).tangentBlock_band _ _) (le_max_right _ _)
  curl_band l := block_band_mono
    (show (p.signedCurl v c u l).BandLimited 1 from by
      have hb := subBlock_band ((p.signed l).exactBlock_band p.strip (p.signedRequest v c u))
        ((p.signed l).tangentBlock_band p.strip (p.signedRequest v c u))
      simp only [max_self] at hb
      exact hb) (le_max_right _ _)
  primary_carrier l := ⟨(hcp l).frequency, (hcp l).phase, (hcp l).angular⟩
  tangent_carrier l := ⟨(hcs l).frequency, (hcs l).phase, (hcs l).angular⟩
  curl_carrier l := ⟨(hcs l).frequency, (hcs l).phase, (hcs l).angular⟩
  old_bounds i j := (hold i j).add ((hpart i j).mono_exponent (by linarith))
  difference_bounds i j := by
    apply ((hdiff i j).add ((hpart i j).mono_exponent (by linarith))).congr
    intro l n x hx
    change (v.blocks l).velocity n i j x - (primary l).velocity n i j x +
      (p.particularBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x -
        (primary l).velocity n i j x
    ring
  tangent_bounds := htangent
  curl_bounds := hcurl
  envelope_nonneg := hP0
  envelope_le_one := hP1
  angular_ne_zero := hkp


-- @@ L8220-8220 verbatim
end CycleParameters


-- @@ L8222-8222 verbatim
end CycleSignedFamily


-- @@ L8224-8224 verbatim
section NativeSignedMeanComposition

-- @@ L8225-8225 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L8226-8226 verbatim
open scoped ContDiff BigOperators


-- @@ L8228-8294 verbatim
/-- The actual native signed update supplies its pressure, cumulative,
mean-residual, and measured-debt bounds from the same covariance. -/
theorem nativeSignedStage_mean_debt
    (G : SignedMeanGain.Geometry) (B : SignedMeanGain.NativeData G)
    (c : Context Point) (u : State Point)
    {P : SignedMeanGain.NativeIndex → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : SignedMeanGain.Assembly f)
    (hl : a.labels = B.labels)
    (hp : ∀ l, (f.primary l).velocity = (B.primaryBlocks l).velocity)
    (hcp : ∀ l, LabelSumBounds.SameCarrier (f.primary l) (B.primaryBlocks l))
    (ht : ∀ l, (f.tangent l).velocity = (B.signedBlocks c u l).velocity)
    (hct : ∀ l, LabelSumBounds.SameCarrier (f.tangent l) (B.signedBlocks c u l))
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = SignedMeanGain.oldField f a)
    (H : SignedMeanGain.LocalData G c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain G.region.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple G.region G.patch.a G.patch.b u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b (u.covariance i j))
    (hX : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u) :
    let v := SignedMeanGain.waveStage G.gauge c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian
    MeanClass G.strip (1+σ-2*κ) (v.pressure - u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    MeanClass G.strip (1+σ-2*κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ) (v.axialResidual c) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.axialResidual c)) ∧
    DefectBounds G.slowStrip (σ-2*κ) c v := by
  let w := SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a
  let v := SignedMeanGain.waveStage G.gauge c u w q gaussian
  have hXT : SignedMeanGain.TensorClass G.strip (1+σ-κ)
      (SignedMeanGain.covarianceIncrement u.oscillation w) := by
    simpa only [hold, w, SignedMeanGain.incrementTensor] using
      (SignedMeanGain.signed_tensor_bounds hσ hκsmall f a).1
  have hXR : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j) := by
    intro i j
    have hf := hX i j
    change GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.incrementTensor f a i j) at hf
    rw [hold]
    exact ⟨hf.smooth, hf.supported⟩
  have hpressure : MeanClass G.strip (1+σ-2*κ) (SignedMeanGain.pressureChange G.gauge c u w q
      gaussian) := by
    simpa only [show 1+σ-κ-κ = 1+σ-2*κ by ring] using H.pressureChange_mem ho hXT
  have hc : OperatorBounds G.strip c.operators κ := by simpa only [H.operators_eq] using ho
  have hop : LocalRankDefect.LocalOperators G.region.carrier c.operators := by
    rw [H.operators_eq]
    exact G.local_operators
  have hdebt := GaugeDebtIncrement.waveStage_defectBounds G.region G.patch.a_pos G.patch.a_lt_b
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one
    G.gauge c u w q gaussian hop hbase hm hW hXR hc hXT
    (show σ-2*κ ≤ σ-κ by linarith) (show 1+(σ-2*κ) ≤ (1+σ-κ)-κ by linarith) hd
  have hgain := SignedMeanGain.native_signed_mean_gain G B c u hσ hκ hκsmall f a hl hp hcp ht hct
    q gaussian hold H ho hX hS hθ hz hd
  have hcum : CorrectionState.CumulativeBounds G.strip v :=
    gaugeWaveStage_cumulative G.gauge c u w q ⟨0,gaussian,0⟩ hu hpressure (by linarith)
  exact ⟨hpressure, hcum, hgain.1, hgain.2.1, hgain.2.2.1, hgain.2.2.2, hdebt⟩



-- @@ L8297-8297 verbatim
end NativeSignedMeanComposition


-- @@ L8299-8299 verbatim
section UniformPeriodizedCoefficients

-- @@ L8300-8300 verbatim
open Set Filter Function WeightedClasses CorrectionState

-- @@ L8301-8301 verbatim
open scoped ContDiff Topology

-- @@ L8302-8302 verbatim
variable {D I ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L8304-8309 verbatim
/-- Joint raw background, given by `LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j => {(a
j.1).background with amplitude := 0, pressure := 0})`. -/
noncomputable def jointRawBackground (a : ι → PeriodizedWaveBounds.CopyData D I) :
    LocalizedWaveBounds.WaveFamily D (ι × I) :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j =>
    {(a j.1).background with amplitude := 0, pressure := 0})


-- @@ L8311-8315 verbatim
/-- Joint raw coefficients, given by `LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j => (a
j.1).raw j.2)`. -/
noncomputable def jointRawCoefficients (a : ι → PeriodizedWaveBounds.CopyData D I) :
    LocalizedWaveBounds.WaveFamily D (ι × I) :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j => (a j.1).raw j.2)


-- @@ L8317-8336 verbatim
theorem uniform_localInput_of_coefficients
    (a : ι → PeriodizedWaveBounds.CopyData D I) {s : StripData D}
    {C : ι → ℕ → I → Set D} {W : ι → ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (h : LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) 0 κ d (jointRawBackground a))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (ha : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α C (fun l => (a l).amplitude))
    (hp : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2) C (fun l => (a l).pressure)) :
    LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) α κ d (jointRawCoefficients a) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW l n x hx)
  exact ⟨h.loss_nonneg, h.radial_profile, h.radial_scale, h.fast_scale, h.frequency_scale,
    h.radius, h.inverse_radius, h.radial_base, h.frequency_base, h.axial_base,
    h.radial_base_aux, h.frequency_base_aux, h.axial_base_aux, h.normal, h.defect,
    fun j => (LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw ha).map
        (ContinuousLinearMap.proj j),
    LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw hp⟩


-- @@ L8338-8370 verbatim
/-- The native solver estimates enter before summation over copies or
spatial labels. All bounds on the background remain local to `C`. -/
theorem uniform_common_bounds_from_raw
    (a : ι → PeriodizedWaveBounds.CopyData D I) (K : ι → PeriodizedWaveBounds.Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} {C : ι → ℕ → I → Set D} {W : ι → ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (h : LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) 0 κ d (jointRawBackground a))
    (ha : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α C (fun l => (a l).amplitude))
    (hp : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2) C (fun l => (a l).pressure))
    (hcut : PeriodizedWaveBounds.UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hκ : κ ≤ 1 / 2) {lo hi : ℝ} (hlo : 0 < lo)
    (hLower : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → lo ≤ ‖(a l).background.normal s d n x‖)
    (hUpper : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → ‖(a l).background.normal s d n x‖ ≤ hi)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s (fun n (j : ι × I) => C j.1 n j.2) (1 / 2)
      (fun n j _ => 1 / (a j.1).background.frequency n))
    (hcover : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∈ C l n i ∨
      (((a l).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((a l).localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)) :
    LabelSumBounds.UniformWaveClass s W α (fun l => (a l).common.amplitude) ∧
    LabelSumBounds.UniformWaveClass s W α (fun l => ((a l).commonCorrected s d).amplitude) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2) (fun l => (a l).common.pressure) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2-κ) (fun l => (a l).common.curlCorrection s d) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2-3*κ) (fun l => (a l).globalGood s d) := by
  have hin := uniform_localInput_of_coefficients a h hW ha hp
  have hout := hin.with_cutoff
    (LocalizedWaveBounds.LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hcut)
  exact LocalizedWaveBounds.uniform_common_bounds_from_supported_native a K hs C hW hout
    hκ hlo hLower hUpper hfreq hcover


-- @@ L8372-8372 verbatim
namespace PeriodizedSignedParameters

-- @@ L8373-8374 verbatim
variable (p : ι → PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)


-- @@ L8376-8421 verbatim
/-- Literal stored coefficients inherit the joint estimates of the
actual common solves, including the exact-minus-tangent curl. -/
theorem uniform_block_bounds
    {P : ι → ℕ → D → ℝ} {α κ : ℝ}
    (ha : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) α (fun l => ((p l).copyData s request).common.amplitude))
    (he : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) α (fun l =>
        (((p l).copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) (p
            l).directions).amplitude))
    (hp : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α + 1 / 2) (fun l => ((p l).copyData s request).common.pressure))
    (hc : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α + 1 / 2 - κ) (fun l =>
        ((p l).copyData s request).common.curlCorrection (HarmonicWaveInteraction.productStrip s)
            (p l).directions))
    (hg : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α + 1 / 2 - 3 * κ) (fun l =>
        ((p l).copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) (p
            l).directions)) :
    (∀ i j, LabelSumBounds.UniformWaveClass s P α (fun l n x => ((p l).tangentBlock s
        request).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P α (fun l n x => ((p l).exactBlock s
        request).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass s P (α+1/2) (fun l n x => ((p l).exactBlock s
        request).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P (α+1/2-κ) (fun l n x => ((p l).curlBlock s
        request).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P (α+1/2-3*κ) (fun l n x => ((p l).goodBlock s
        request).velocity n i j x)) := by
  have ht := UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l => ((p l).copyData s request).common) (fun l => (p l).angularFrequency) ha hp
  have hx := UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l => ((p l).copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s)
        (p l).directions)
    (fun l => (p l).angularFrequency) he hp
  have hd := UniformBlockBounds.commonCorrected_product_difference_uniform
    (fun l => (p l).copyData s request) (fun l => (p l).directions) (fun l => (p
        l).angularFrequency) hc
  have hgs := UniformBlockBounds.uniform_slice (s := s)
    (w := fun l n x => Real.sqrt (s.zeta x) * P l n x) hg
  have hgb := UniformBlockBounds.coefficientBlock_uniform
    (fun l => (p l).base.frequency) (fun l n x => (p l).base.phase n (x,0)) (fun l => (p
        l).angularFrequency)
    hgs (LabelSumBounds.UniformClass.zero (E := ℂ) (α := (0:ℝ)) hgs.weight_nonneg)
  exact ⟨ht.1,hx.1,hx.2,hd,hgb.1⟩


-- @@ L8423-8423 verbatim
end PeriodizedSignedParameters


-- @@ L8425-8425 verbatim
end UniformPeriodizedCoefficients


-- @@ L8427-8427 verbatim
section CoherentReferenceParticular


-- @@ L8429-8429 verbatim
open Set Filter Function CorrectionState WeightedClasses ParticularWaveAssembly ParticularWaveBounds

-- @@ L8430-8430 verbatim
open scoped ContDiff Topology BigOperators

-- @@ L8431-8431 verbatim
namespace ParticularParameters

-- @@ L8432-8432 verbatim
open TorusInverse

-- @@ L8433-8433 verbatim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L8435-8447 verbatim
theorem common_amplitude (p : ParticularParameters P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (n : ℕ) :
    (p.copyData c u b G A j).common.amplitude n =
      angleLift (ParticularWaveBounds.commonVelocity (p.tangent j n)
        (residualSource c u b G A j n) (p.geometry n) (p.length_pos n).le (p.cutoff n)) := by
  funext z
  rcases z with ⟨⟨x,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun w => p.cutoff n ((p.geometry n).coordinates k Y) • w)
    (complexCopyVelocity_angle (p.tangent j n) (residualSource c u b G A j n)
      (p.geometry n) (p.length_pos n).le k x θ Y)


-- @@ L8449-8463 verbatim
theorem common_pressure (p : ParticularParameters P)
    (c : Context (P × Plane)) (u : State (P × Plane)) (b : HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (n : ℕ)
    (hk : (j : ℝ) * b.frequency n ≠ 0) :
    (p.copyData c u b G A j).common.pressure n =
      angleLift (ParticularWaveBounds.commonPressure (p.tangent j n)
        (residualSource c u b G A j n) (p.geometry n) (p.length_pos n).le (p.cutoff n)
          ((j:ℝ)*b.frequency n)) := by
  funext z
  rcases z with ⟨⟨x,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun w => p.cutoff n ((p.geometry n).coordinates k Y) • w)
    (complexCopyPressure_angle (p.tangent j n) (residualSource c u b G A j n)
      (p.geometry n) (p.length_pos n).le k hk x θ Y)


-- @@ L8465-8491 verbatim
/-- Every target band uses the same chosen reference tangent, geometry,
clock interval and cutoff. Only the current HR source is supplied at solve time. -/
noncomputable def fromReference
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ → ℕ) :
    ParticularParameters PhysicalParticularWave.Parameter where
  tangent j n := ScaledTangentTransport.transportTangent (D.reference.tangent j)
    (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band))
        (gap n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q D.reference.band)
      ((j:ℝ)*D.carrierBlock.frequency n) (PhysicalParticularWave.referenceFrequency D j))
  geometry n := CopySolveCompatibility.transportGeometry D.reference.geometry (gap n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos
        D.reference.band)
      (CoordinateAlgebra.A h+1/2)).ne'
  length n := D.reference.length /
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band)
  length_pos n := div_pos D.reference.length_pos
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos
        D.reference.band)
      (CoordinateAlgebra.A h+1/2))
  cutoff n := D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
  background := D.background
  directions := D.directions


-- @@ L8493-8499 verbatim
theorem fromReference_amplitude
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) (n : ℕ) :
    ((fromReference D h gap).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
        j).common.amplitude n =
      angleLift (PhysicalParticularWave.residualBandAmplitude D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) (gap n) ((j:ℝ)*D.carrierBlock.frequency n) j n) :=
  common_amplitude _ _ _ _ _ _ _ _


-- @@ L8501-8508 verbatim
theorem fromReference_pressure
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) (n : ℕ)
    (hk : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) :
    ((fromReference D h gap).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
        j).common.pressure n =
      angleLift (PhysicalParticularWave.residualBandPressure D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) (gap n) ((j:ℝ)*D.carrierBlock.frequency n) j n) :=
  common_pressure _ _ _ _ _ _ _ _ hk


-- @@ L8510-8523 verbatim
/-- Full-lift current-state coherence identifies the actual solved amplitude
with the one reference physical wave, before taking a graph restriction. -/
theorem fromReference_coherent_amplitude
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band) :
    ((fromReference D h gap).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
        j).common.amplitude n =
      angleLift (PhysicalParticularWave.bandAmplitude D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) (gap n) ((j:ℝ)*D.carrierBlock.frequency n) j) := by
  rw [fromReference_amplitude, H.residualBandAmplitude_eq hn hr]


-- @@ L8525-8537 verbatim
theorem fromReference_coherent_pressure
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
        D.reference.band)
    (hk : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) :
    ((fromReference D h gap).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput
        j).common.pressure n =
      angleLift (PhysicalParticularWave.bandPressure D h (ChartScales.Q_pos n)
        (ChartScales.Q_pos D.reference.band) (gap n) ((j:ℝ)*D.carrierBlock.frequency n) j) := by
  rw [fromReference_pressure D h gap j n hk, H.residualBandPressure_eq hn hr]


-- @@ L8539-8539 verbatim
end ParticularParameters


-- @@ L8541-8541 verbatim
end CoherentReferenceParticular


-- @@ L8543-8543 verbatim
section ConstructedMeanStages


-- @@ L8545-8545 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L8546-8546 verbatim
open scoped ContDiff BigOperators

-- @@ L8547-8547 verbatim
section

-- @@ L8548-8555 verbatim
variable (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    {coord cL cR A B : ℝ} (U : SlowRegion coord)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

-- @@ L8556-8556 verbatim
include hd hell

-- @@ L8557-8558 verbatim
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L
    hε hεone hL

-- @@ L8559-8560 verbatim
local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone
    hL

-- @@ L8561-8561 verbatim
local notation "signedState" => u

-- @@ L8562-8562 verbatim
local notation "temporalState" => temporalStageState g h index axial c u

-- @@ L8563-8666 verbatim
theorem meanStages_constructed {σ κ : ℝ}
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hsigned : CorrectionState.CumulativeBounds stageStrip signedState)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (signedState).mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
        (signedState).mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((signedState).covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        ((signedState).covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ ((signedState).thetaResidual c n) (PhysicalMeanDomain.slowDomain
        U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ ((signedState).axialResidual c n) (PhysicalMeanDomain.slowDomain
        U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).axialResidual c n))
    (hsθ : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        ((signedState).thetaResidual c))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
        ((signedState).axialResidual c))
    (hcθ : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).thetaResidual c))
    (hcz : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).axialResidual c))
    (hbarθ : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).thetaResidual c)))
    (hbarz : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).axialResidual c)))
    (hdebt : ∀ i : Fin 3, UnweightedClass slowStrip (1 + σ - 2 * κ)
      (fun n x => debt c signedState n x i))
    (hg : LocalRankDefect.RankGeometry g r U.carrier c temporalState)
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer) :
    IncrementBounds stageStrip (1 + σ - 2 * κ) (temporalIncrementState g h index axial c u) ∧
    IncrementBounds stageStrip (1 + σ - 2 * κ) (rankIncrementState g r axial c temporalState) ∧
    MeanClass stageStrip (1 + σ - 2 * κ) ((rankStageState g r axial c temporalState).pressure -
        u.pressure) ∧
    CorrectionState.CumulativeBounds stageStrip (rankStageState g r axial c temporalState) ∧
    DefectBounds slowStrip (σ + 1 / 10) c (rankStageState g r axial c temporalState) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10)) ((rankStageState g r axial c
        temporalState).thetaResidual c) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10))
      ((rankStageState g r axial c temporalState).axialResidual c -
        fun n x => temporalAliasState g h index c signedState n (x,0) 2) := by
  have hH : 9 / 10 ≤ 1 + σ - 2 * κ := by linarith
  have hκ : 2 * κ ≤ 9 / 10 := by linarith
  have hβ : 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 1 - 2 * κ := by linarith
  obtain ⟨hi, hp, htCum, htSmooth, htSupport, htTheta, htAxial⟩ :=
    gaugeTemporalStage_constructed U g ha hd hcL hcR ε L hε hεone hL hell
      hh hscale index gap hgap axial c signedState ho.epsilon_eq hv hfast hfixed
      hH hκ hβ ho hb hsigned hop hbase hm hms hW hWs hθ hz hpθ hpz hsθ hsz hcθ hcz
      (hbarθ.mono_exponent (by linarith)) (hbarz.mono_exponent (by linarith))
  have hiSmooth := gaugeTemporalIncrement_smooth U g ha hd hell h index axial
    c signedState hθ hz hpθ hpz hsz
  have hiSupport : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u) := by
    have hs n := temporalIncrementState_supportedGauge U g ha hd hell c signedState
      h index axial n (hz n) (hpz n) (hsz n) (hsθ n)
    exact ⟨fun n => (hs n).1, fun n => (hs n).2.1, fun n => (hs n).2.2⟩
  have hmReg : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer (signedState).mean
      :=
    ⟨⟨hm.radial, hms.radial⟩, ⟨hm.angular, hms.angular⟩, ⟨hm.axial, hms.axial⟩⟩
  have hiReg : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer
      (temporalIncrementState g h index axial c u) :=
    ⟨⟨hiSmooth.radial, hiSupport.radial⟩, ⟨hiSmooth.angular, hiSupport.angular⟩,
      ⟨hiSmooth.axial, hiSupport.axial⟩⟩
  have htDebt := GaugeDebtIncrement.temporalStage_debt_mem U ha g.radial.inner_lt_outer
    hcL hcR ε L hε hεone hL g h index axial c signedState
    hop hbase hmReg hiReg (fun i j => ⟨hW i j, hWs i j⟩) ho hb hsigned.velocity hi hH hκ le_rfl
        hdebt
  have hcov : (temporalState).covariance = (signedState).covariance :=
    gaugeTemporalStage_covariance g h index axial c signedState
  have htW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((temporalState).covariance
      i j) := by
    simpa only [hcov] using hW
  have htWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((temporalState).covariance i j) := by simpa only [hcov] using hWs
  let aliasField : ScalarField Point := fun n x =>
    temporalAliasState g h index c signedState n (x,0) 2
  obtain ⟨hrInc, hrPressure, hrCum, _, _, hrTheta, hrAxial⟩ :=
    gaugeRankStage_constructed U g r ha hd hcL hcR ε L hε hεone hL hell
      axial c temporalState hg hparam hB hleft hright hH hκ hβ hv rfl
      ho hb htCum hop hbase htSmooth htSupport htW htWs
      (RankStateBounds.debtClass_of_components _ htDebt) aliasField htTheta htAxial
  have hrDebt := MovingMomentBounds.rankStage_defectBounds U g r ha hcL hcR
    ε L hε hεone hL hell axial c temporalState hg hop hbase htSmooth
    ⟨htSupport.radial, htSupport.angular, htSupport.axial⟩ htW htWs hV hG
    ho hb htCum.velocity hrInc hH (show 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 9 / 10 - 2 * κ by
        linarith)
  have hpressure : MeanClass stageStrip (1 + σ - 2 * κ)
      ((rankStageState g r axial c temporalState).pressure - u.pressure) := by
    apply class_congr (hp.add hrPressure)
    intro n x hx
    change (rankStageState g r axial c temporalState).pressure n x - u.pressure n x =
      ((temporalState).pressure n x - u.pressure n x) +
        ((rankStageState g r axial c temporalState).pressure n x - (temporalState).pressure n x)
    ring
  exact ⟨hi, hrInc, hpressure, hrCum, hrDebt, hrTheta, hrAxial⟩


-- @@ L8668-8668 verbatim
end


-- @@ L8670-8670 verbatim
end ConstructedMeanStages


-- @@ L8672-8672 verbatim
section UniformParticularGain


-- @@ L8674-8674 verbatim
open Set Filter Function WeightedClasses CorrectionState ParticularWaveAssembly ParticularWaveBounds

-- @@ L8675-8675 verbatim
open scoped ContDiff Topology BigOperators

-- @@ L8676-8676 verbatim
namespace ParticularParameters

-- @@ L8677-8677 verbatim
open TorusInverse

-- @@ L8678-8682 verbatim
variable {Q ι : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (p : ι → ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane))
    (b : ι → HarmonicBlock (Q × Plane)) (G A : ι → HarmonicResidual.BlockCoefficients (Q × Plane))
    (N : ℕ)


-- @@ L8684-8705 verbatim
theorem uniform_assembled_bounds {W : ι → ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (ha : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W α
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).amplitude))
    (hp : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α + 1 / 2)
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).pressure))
    (hg : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α + 1 / 2 - 3 * κ)
      (fun l => ((p l).copyData c u (b l) (G l) (A l) j).globalGood (nativeStrip s) (p
          l).directions)) :
    (∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) α
      (fun l n x => ((p l).updateBlock s c u (b l) (G l) (A l) N).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) (α+1/2)
      (fun l n x => ((p l).updateBlock s c u (b l) (G l) (A l) N).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) (α+1/2-3*κ)
      (fun l n x => ((p l).goodBlock s c u (b l) (G l) (A l) N).velocity n i j x)) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg ((nativeStrip s).zeta x)) (hW l n x hx)
  have hupdate := UniformBlockBounds.native_assembledBlock_original_uniform (s := s)
    N (fun l => (b l).frequency) (fun l => (b l).phase) (fun l => (b l).angularFrequency) hw ha hp
  have hgood := UniformBlockBounds.native_assembledBlock_original_uniform (s := s)
    N (fun l => (b l).frequency) (fun l => (b l).phase) (fun l => (b l).angularFrequency) hw hg
    (fun _ _ => LabelSumBounds.UniformClass.zero (E := ℂ) (α := (0:ℝ)) hw)
  exact ⟨hupdate.1,hupdate.2,hgood.1⟩


-- @@ L8707-8742 verbatim
theorem uniform_linearGood_bounds {W : ι → ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (C : ∀ l j, j ∈ modes N → (p l).NativeControl s c u (b l) (G l) (A l) j (W l) α κ)
    (dyn : ∀ l j hj, NativeDynamics (C l j hj))
    (hκ : κ ≤ 1 / 2)
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (hg : ∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x, 0)))
      (α + 1 / 2 - 3 * κ) (fun l n x => ((p l).goodBlock s c u (b l) (G l) (A l) N).velocity n i j
          x))
    (hN : ∀ l, (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).BandLimited N)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle (p l).directions) (reindexCoefficients angleShuffle (p
          l).background))
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((b l).phase n) s.domain)
    (hkp : ∀ l n, (b l).angularFrequency n ≠ 0) :
    ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0)))
      (α+1/2-3*κ) (fun l n x =>
        (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (b l) ((p l).updateBlock s c u (b l) (G l) (A l)
            N)
          ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity).velocity n i j x) := by
  have hb l := (p l).assembled_bounds s c u (b l) (G l) (A l) N (C l) (hW l) hκ
  apply linearGoodBlock_cancel_uniform c b (fun l => (p l).updateBlock s c u (b l) (G l) (A l) N)
    (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l))
    (fun l => (p l).goodBlock s c u (b l) (G l) (A l) N)
    (fun l => ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity)
    hrad (fun _ => contDiffOn_const) hB
    (fun l => HarmonicWaveInteraction.waveBounds_smooth (hb l).1 (assembledBlock_zero _ _ _ _ _
        _).1)
    (fun l => pressureBounds_smooth (hb l).2.1 (assembledBlock_zero _ _ _ _ _ _).2)
    hphase hkp (fun l => HarmonicResidual.residualBlock_conjugate _ _ _ _ _)
    (fun _ => (assembledBlock_real _ _ _ _ _ _).1) (fun i j _ => hg i j)
  intro l n x hx θ i
  exact congrFun ((p l).context_linear_cancellation s c u (b l) (G l) (A l) N (C l) (dyn l)
    hκ (hN l) hB hrad (hm l) n (x,θ) hx) i


-- @@ L8744-8807 verbatim
theorem uniform_residual_gain {W : ι → ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (C : ∀ l j, j ∈ modes N → (p l).NativeControl s c u (b l) (G l) (A l) j (W l) α κ)
    (dyn : ∀ l j hj, NativeDynamics (C l j hj))
    (hα : 7 / 10 ≤ α) (hκ : κ ≤ 1 / 100000)
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hb : MeanIncrementBounds.BaseBounds s c.base)
    (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (v : State (Q × Plane)) (hmean : v.mean = u.mean)
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (hWone : ∀ l n x, x ∈ s.domain → W l n (angleShuffle (x, 0)) ≤ 1)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle (p l).directions) (reindexCoefficients angleShuffle (p
          l).background))
    (hcopy : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W α
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).amplitude))
    (hpressure : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α + 1 / 2)
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).pressure))
    (hgood : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α + 1 / 2 - 3 * κ)
      (fun l => ((p l).copyData c u (b l) (G l) (A l) j).globalGood (nativeStrip s) (p
          l).directions))
    (hold : UniformHarmonicInteraction.UniformVelocity s (fun l n x => W l n (angleShuffle (x, 0)))
        (1 / 2) b)
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    {M : ℕ} (hband : ∀ l, (b l).BandLimited M)
    (hsource : ∀ l, (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).BandLimited N)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((b l).phase n) s.domain)
    (hk : ∀ l n, (b l).frequency n ≠ 0) (hkp : ∀ l n, (b l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (b l))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    {patch : ℕ → ι → Set (Q × Plane)}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s patch 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (b l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s patch (-(1 / 2)) (fun n l _ => (b l).frequency
        n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s patch (-(1 / 2))
      (fun n l _ => ((b l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ patch n l → ∀ i j, j ≠ 0 →
      ((p l).updateBlock s c u (b l) (G l) (A l) N).velocity n i j =ᶠ[𝓝 x] fun _ => 0) :
    UniformHarmonicInteraction.UniformVelocity s (fun l n x => W l n (angleShuffle (x,0))) (α+1/10)
      (fun l => HarmonicResidual.residualBlock c v
        (HarmonicWaveInteraction.addBlock (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N))
        (G l + ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity) (A l)) := by
  have hkhalf : κ ≤ 1/2 := by linarith
  have hblocks := uniform_assembled_bounds p s c u b G A N hW hcopy hpressure hgood
  have hlin := uniform_linearGood_bounds p s c u b G A N C dyn hkhalf hW hblocks.2.2
    hsource hb.smooth (operator_radial_smooth ho) hm hphase hkp
  have hnewdiv l : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N)) :=
          by
    rw [withCarrier_of_same (show SameCarrier (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N)
        from ⟨rfl,rfl,rfl⟩)]
    exact (p l).modeSolenoidal s c u (b l) (G l) (A l) N (C l) (dyn l) hkhalf (hW l) (hm l) (hphase
        l) (hkp l)
  exact waveStage_residual_uniform c ho hkhalf hR u v hmean (meanIncrement_of_cumulative hu)
      hb.smooth
    b (fun l => (p l).updateBlock s c u (b l) (G l) (A l) N) hold (fun i j _ => hblocks.1 i j)
    hzero (fun _ => (assembledBlock_zero _ _ _ _ _ _).1) hband
    (fun l => (p l).updateBlock_band _ _ _ _ _ _ _) hphase hk hkp hdiv hnewdiv hNormal hFreq hAng hz
    (fun l n x hx => hW l n _ hx) hWone hpold (fun l n j => (hblocks.2.1 j).smooth l n)
    G (fun l => ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity) A A
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hlin i j hj).mono_exponent (by linarith))
    (by linarith) (by linarith) (by linarith)


-- @@ L8809-8809 verbatim
end ParticularParameters


-- @@ L8811-8811 verbatim
end UniformParticularGain


-- @@ L8813-8813 verbatim
section BandNativeSignedMeanComposition


-- @@ L8815-8815 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L8816-8816 verbatim
open scoped ContDiff BigOperators


-- @@ L8818-8890 verbatim
/-- The actual native signed update supplies its pressure, cumulative,
mean-residual, and measured-debt bounds from the same covariance. -/
theorem bandNativeSignedStage_mean_debt {ι : Type}
    (G : SignedMeanGain.Geometry) (B : SignedMeanGain.NativeData G)
    (c : Context Point) (u : State Point)
    {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : SignedMeanGain.Assembly f)
    (e : ℕ → ι → SignedMeanGain.NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n → (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n → (f.tangent l).velocity n = (B.signedBlocks c u (e n l)).velocity
        n)
    (hct : ∀ n l, l ∈ a.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      (f.tangent l) (B.signedBlocks c u (e n l)) n)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = SignedMeanGain.oldField f a)
    (H : SignedMeanGain.LocalData G c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain G.region.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple G.region G.patch.a G.patch.b u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b (u.covariance i j))
    (hX : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u) :
    let v := SignedMeanGain.waveStage G.gauge c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian
    MeanClass G.strip (1+σ-2*κ) (v.pressure - u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    MeanClass G.strip (1+σ-2*κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ) (v.axialResidual c) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.axialResidual c)) ∧
    DefectBounds G.slowStrip (σ-2*κ) c v := by
  let w := SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a
  let v := SignedMeanGain.waveStage G.gauge c u w q gaussian
  have hXT : SignedMeanGain.TensorClass G.strip (1+σ-κ)
      (SignedMeanGain.covarianceIncrement u.oscillation w) := by
    simpa only [hold, w, SignedMeanGain.incrementTensor] using
      (SignedMeanGain.signed_tensor_bounds hσ hκsmall f a).1
  have hXR : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j) := by
    intro i j
    have hf := hX i j
    change GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.incrementTensor f a i j) at hf
    rw [hold]
    exact ⟨hf.smooth, hf.supported⟩
  have hpressure : MeanClass G.strip (1+σ-2*κ) (SignedMeanGain.pressureChange G.gauge c u w q
      gaussian) := by
    simpa only [show 1+σ-κ-κ = 1+σ-2*κ by ring] using H.pressureChange_mem ho hXT
  have hc : OperatorBounds G.strip c.operators κ := by simpa only [H.operators_eq] using ho
  have hop : LocalRankDefect.LocalOperators G.region.carrier c.operators := by
    rw [H.operators_eq]
    exact G.local_operators
  have hdebt := GaugeDebtIncrement.waveStage_defectBounds G.region G.patch.a_pos G.patch.a_lt_b
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one
    G.gauge c u w q gaussian hop hbase hm hW hXR hc hXT
    (show σ-2*κ ≤ σ-κ by linarith) (show 1+(σ-2*κ) ≤ (1+σ-κ)-κ by linarith) hd
  have hgain := BandReindexedSignedMeanGain.native_signed_mean_gain G B c u hσ hκ hκsmall f a e he
      hlabels hp hcp ht hct
    q gaussian hold H ho hX hS hθ hz hd
  have hcum : CorrectionState.CumulativeBounds G.strip v :=
    gaugeWaveStage_cumulative G.gauge c u w q ⟨0,gaussian,0⟩ hu hpressure (by linarith)
  exact ⟨hpressure, hcum, hgain.1, hgain.2.1, hgain.2.2.1, hgain.2.2.2, hdebt⟩


-- @@ L8892-8892 verbatim
end BandNativeSignedMeanComposition


-- @@ L8894-8894 verbatim
section UniformSignedGain


-- @@ L8896-8896 verbatim
open Set Filter Function WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L8897-8897 verbatim
open scoped ContDiff Topology BigOperators InnerProductSpace

-- @@ L8898-8898 verbatim
namespace PeriodizedSignedParameters

-- @@ L8899-8904 verbatim
variable {D I ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : ι → PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    {P : ι → ℕ → D → ℝ} {β κ : ℝ}
    (C : ∀ l, (p l).NativeControl s (P l) κ)
    (dyn : ∀ l, NativeDynamics (C l) request) (i₀ : I)


-- @@ L8906-8906 verbatim
include i₀


-- @@ L8908-8959 verbatim
theorem uniform_linearGood_bounds
    (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (hkp : ∀ l n, (p l).base.frequency n * (dyn l).slope n = ((p l).angularFrequency n : ℝ))
    (hkpne : ∀ l n, (p l).angularFrequency n ≠ 0)
    (c : Context D) (hB : SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) (p l).directions (p
        l).base)
    (a : ι → HarmonicBlock D) (hc : ∀ l, SameCarrier (a l) ((p l).exactBlock s request))
    (hg : UniformHarmonicInteraction.UniformVelocity s P (β + 1 - 3 * κ)
      (fun l => (p l).goodBlock s request)) :
    UniformHarmonicInteraction.UniformVelocity s P (β+1-3*κ)
      (fun l => HarmonicWaveInteraction.linearGoodBlock c (a l) ((p l).exactBlock s request)
        ((p l).gaussianBlock s request).velocity) := by
  let z : ι → HarmonicBlock D := fun l => ErrorHarmonics.zeroBlock (a l).frequency (a l).phase (a
      l).angularFrequency 0
  have hb l := (C l).block_bounds hκ request hR
  have hphase l n : ContDiffOn ℝ ∞ ((a l).phase n) s.domain := by
    rw [← (hc l).phase]
    exact (((dyn l).angular i₀).phase_smooth n).comp (SignedWaveUpdate.zeroSection (D :=
        D)).contDiff.contDiffOn
      (fun x hx => hx)
  have hka l n : (a l).angularFrequency n ≠ 0 := by rw [← (hc l).angular]; exact hkpne l n
  have he := linearGoodBlock_cancel_uniform c a (fun l => (p l).exactBlock s request) z
    (fun l => (p l).goodBlock s request) (fun l => ((p l).gaussianBlock s request).velocity)
    hrad (fun _ => contDiffOn_const) hB
    (fun l => HarmonicWaveInteraction.waveBounds_smooth (hb l).2.1 ((p l).exactBlock_zero s
        request))
    (fun l => pressureBounds_smooth (hb l).2.2.1 ((p l).exactBlock_pressure_zero s request))
    hphase hka (fun l n i => ErrorHarmonics.zeroBlock_symmetric _ _ _ _ n i)
    (fun _ => (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1) hg ?_
  · intro i j hj
    simpa [z, ErrorHarmonics.zeroBlock, HarmonicFields.constantCoefficient, Finsupp.single_apply,
      hj, Ne.symm hj] using he i j hj
  · intro l n x hx θ i
    have hgood : SameCarrier (a l) ((p l).goodBlock s request) :=
      ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
    have hgauss : SameCarrier (a l) ((p l).gaussianBlock s request) :=
      ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
    have hh := congrFun ((dyn l).context_linear_identity i₀ hκ hR (hkp l) c hB hrad (hm l)
      (a l) (hc l) n (x,θ) hx) i
    rw [withCarrier_of_same hgood]
    have heval : (HarmonicFields.field (((p l).gaussianBlock s request).velocity n i)
        ((a l).frequency n) ((a l).phase n) ((a l).angularFrequency n) (x,θ)).re =
        ((p l).gaussianBlock s request).oscillation n (x,θ) i := by
      simp only [HarmonicBlock.oscillation, hgauss.frequency, hgauss.phase, hgauss.angular]
    rw [heval]
    simpa only [z, HarmonicWaveInteraction.withCarrier, ErrorHarmonics.zeroBlock,
      HarmonicBlock.oscillation, HarmonicResidual.field_constant, Pi.zero_apply,
          Complex.ofReal_zero,
      Complex.zero_re, Pi.add_apply, add_zero] using hh


-- @@ L8961-9032 verbatim
theorem uniform_residual_gain {B : ℝ}
    (hB : 7 / 10 ≤ B) (hκ : κ ≤ 1 / 100000)
    (hRquest : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) (B - 1 / 2 - κ) (fun n x =>
        request n x j))
    (geom : ∀ l n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip
        s).domain
      ((p l).base.radius n) ((p l).directions.radialField n) (fun _ => (p l).directions.angular)
      ((p l).directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ (C l).phasePatch n i
        →
      ⟪(p l).base.normal (HarmonicWaveInteraction.productStrip s) (p l).directions n x,
        (p l).fundamental i n x⟫_ℝ = 0)
    (hkp : ∀ l n, (p l).base.frequency n * (dyn l).slope n = ((p l).angularFrequency n : ℝ))
    (hkpne : ∀ l n, (p l).angularFrequency n ≠ 0)
    (c : Context D) (u v : State D) (hmean : v.mean = u.mean)
    (ho : OperatorBounds s c.operators κ) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hbase : BaseBounds s c.base) (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) (p l).directions (p
        l).base)
    (a : ι → HarmonicBlock D) (hc : ∀ l, SameCarrier (a l) ((p l).exactBlock s request))
    (ha : UniformHarmonicInteraction.UniformVelocity s P (1 / 2) a)
    (hnew : UniformHarmonicInteraction.UniformVelocity s P (B - κ) (fun l => (p l).exactBlock s
        request))
    (hgood : UniformHarmonicInteraction.UniformVelocity s P (B + 1 / 2 - 4 * κ) (fun l => (p
        l).goodBlock
        s
        request))
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l)) {M : ℕ} (hM : ∀ l, (a l).BandLimited M)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hka : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (a l))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((a l).pressure n))
    {patch : ℕ → ι → Set D}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s patch 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (a l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s patch (-(1 / 2)) (fun n l _ => (a l).frequency
        n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s patch (-(1 / 2)) (fun n l _ => ((a
        l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ patch n l → ∀ i j, j ≠ 0 →
      ((p l).exactBlock s request).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (G A : ι → HarmonicResidual.BlockCoefficients D)
    (hold : UniformHarmonicInteraction.UniformVelocity s P (B + 1 / 10)
      (fun l => HarmonicResidual.residualBlock c u (a l) (G l) (A l))) :
    UniformHarmonicInteraction.UniformVelocity s P (B+1/10)
      (fun l => HarmonicResidual.residualBlock c v
        (HarmonicWaveInteraction.addBlock (a l) ((p l).exactBlock s request))
        (G l+((p l).gaussianBlock s request).velocity) (A l)) := by
  have hkhalf : κ ≤ 1/2 := by linarith
  have hgood' : UniformHarmonicInteraction.UniformVelocity s P ((B-1/2-κ)+1-3*κ)
      (fun l => (p l).goodBlock s request) := by
    convert! hgood using 1
    ring
  have hlin := uniform_linearGood_bounds p s request C dyn i₀ hkhalf hRquest hkp hkpne c
      hbase.smooth
    (operator_radial_smooth ho) hm a hc hgood'
  have hnewdiv l : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier (a l) ((p l).exactBlock s request)) := by
    rw [withCarrier_of_same (hc l)]
    exact (dyn l).modeSolenoidal i₀ hkhalf hRquest (geom l) (ht l) (hkp l) (hkpne l) c (hm l)
  exact waveStage_residual_uniform c ho hkhalf hR u v hmean (meanIncrement_of_cumulative hu)
      hbase.smooth
    a (fun l => (p l).exactBlock s request) ha hnew ha0 (fun l => (p l).exactBlock_zero s request)
    hM (fun l => (p l).exactBlock_band s request) hphase hk hka hdiv hnewdiv hNormal hFreq hAng hz
    (fun l => (C l).envelope_nonneg) hP1 hpold
    (fun l => pressureBounds_smooth ((C l).block_bounds hkhalf request hRquest).2.2.1
      ((p l).exactBlock_pressure_zero s request)) G (fun l => ((p l).gaussianBlock s
          request).velocity) A A
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hold i j hj).add ((hlin i j hj).mono_exponent (by linarith)))
    (by linarith) (by linarith) (by linarith)


-- @@ L9034-9034 verbatim
end PeriodizedSignedParameters


-- @@ L9036-9036 verbatim
end UniformSignedGain


-- @@ L9038-9038 verbatim
section FourStageMeanComposition


-- @@ L9040-9040 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L9041-9041 verbatim
open scoped ContDiff BigOperators


-- @@ L9043-9043 verbatim
section MeanCycle

-- @@ L9044-9050 verbatim
variable {ι : Type} (G : SignedMeanGain.Geometry) (B : SignedMeanGain.NativeData G)
    (c : Context Point) (u : State Point)
    (w₁ : Oscillation Point) (q₁ : OscillatoryScalar Point) (e₁ : Oscillation Point)
    {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25) (1 / 2 + σ - κ) (1 + σ - 2 * κ))
    (a : SignedMeanGain.Assembly f)
    (q₂ : OscillatoryScalar Point) (e₂ : Oscillation Point)


-- @@ L9052-9052 verbatim
local notation "u₁" => SignedMeanGain.waveStage G.gauge c u w₁ q₁ e₁

-- @@ L9053-9053 verbatim
local notation "w₂" => SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a

-- @@ L9054-9054 verbatim
local notation "u₂" => SignedMeanGain.waveStage G.gauge c u₁ w₂ q₂ e₂


-- @@ L9056-9180 verbatim
/-- The two actual wave updates, temporal inverse, and rank solve form one
mean/debt gain. All intermediate residual and flux regularity is derived
from the original primitive fields and the actual covariance increments. -/
theorem fourStage_mean_gain
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hop : c.operators = G.operators)
    (ho : OperatorBounds G.strip G.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w₁ i j))
    (hX₁class : SignedMeanGain.TensorClass G.strip (1 + σ)
      (SignedMeanGain.covarianceIncrement u.oscillation w₁))
    (hX₂ : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hold : (u₁).oscillation = SignedMeanGain.oldField f a)
    (e : ℕ → ι → SignedMeanGain.NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n → (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n → (f.tangent l).velocity n = (B.signedBlocks c u₁ (e n l)).velocity
        n)
    (hct : ∀ n l, l ∈ a.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      (f.tangent l) (B.signedBlocks c u₁ (e n l)) n)
    (r : RankData PressureStream.Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ G.slow n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^
        (1 + h))
    (hV : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c
      (temporalStageState G.gauge h index axial c u₂))
    {A₀ B₀ : ℝ} (hparam : RankStateBounds.NormalizedParameters G.coord A₀ B₀ r G.region.carrier)
    (hB : B₀ ≠ 0) (hleft : G.patch.a < r.inner) (hright : r.outer < G.patch.b) :
    let t := temporalStageState G.gauge h index axial c u₂
    let v := rankStageState G.gauge r axial c t
    IncrementBounds G.strip (1+σ-2*κ) (temporalIncrementState G.gauge h index axial c u₂) ∧
    IncrementBounds G.strip (1+σ-2*κ) (rankIncrementState G.gauge r axial c t) ∧
    MeanClass G.strip (1+σ-2*κ) (v.pressure-u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    DefectBounds G.slowStrip (σ+1/10) c v ∧
    MeanClass G.strip (1+(σ+1/10)) (v.thetaResidual c) ∧
    MeanClass G.strip (1+(σ+1/10))
      (v.axialResidual c - fun n x => temporalAliasState G.gauge h index c u₂ n (x,0) 2) := by
  have hs : movingStripData G.region G.gauge.radial.inner G.gauge.radial.outer
      G.leftWeight G.rightWeight G.inner_pos G.left_pos G.right_pos
      G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one = G.strip := by
    simp only [SignedMeanGain.Geometry.strip, G.inner_eq, G.outer_eq]
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have HX₁ : ∀ i j, GaugeDebtIncrement.Regular G.region G.gauge.radial.inner G.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w₁ i j) := by
    simpa only [G.inner_eq, G.outer_eq] using
      (fun i j => MeanStateRegularity.MovingField.regular (hX₁ i j))
  have hc : OperatorBounds G.strip c.operators κ := by simpa only [hop] using ho
  have hfirst := gaugeWaveStage_mean_from_covariance G.region G.gauge G.inner_pos G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    c u w₁ q₁ e₁ H.operators.regular H.base.smooth H₀.mean.regular
    (fun i j => MeanStateRegularity.MovingField.regular (H₀.covariance i j)) HX₁
    (hs.symm ▸ hc) (hs.symm ▸ hX₁class) hfixed (hs.symm ▸ hb) (hs.symm ▸ hu)
    (show 9/10 ≤ (1+σ)-κ by linarith) le_rfl
    (hs.symm ▸ hθ.mono_exponent (by linarith)) (hs.symm ▸ hz.mono_exponent (by linarith))
    (fun i => (hd i).mono_exponent (by linarith))
  rw [hs] at hfirst
  obtain ⟨hp₁, hu₁, hθ₁, hz₁, hd₁⟩ := hfirst
  have H₁ := H.waveStage G.gauge w₁ q₁ e₁ hX₁
  have HX₂ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement (u₁).oscillation w₂ i j) := by
    simp only [hold]
    exact hX₂
  have Hsigned := MeanStateRegularity.localData G c u₁ w₂ q₂ e₂ H₁ hop HX₂
    (GaugeMomentBalances.reconstructState_idempotent _ _ _)
    (by simpa only [SignedMeanGain.waveStage_mean] using hmθ)
    (by simpa only [SignedMeanGain.waveStage_mean] using hmz)
  have hdebt₁ : DefectBounds G.slowStrip (σ-κ) c u₁ := by
    simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-κ) = 1+σ-κ by ring] using hd₁
  obtain ⟨hp₂, hu₂, hθ₂, hz₂, hbarθ, hbarz, hd₂⟩ :=
    bandNativeSignedStage_mean_debt G B c u₁ hσ hκ hκsmall f a e he hlabels hp hcp ht hct
      q₂ e₂ hold Hsigned ho hu₁ H.base.smooth H₁.mean.regular
      (fun i j => MeanStateRegularity.MovingField.regular (H₁.covariance i j)) hX₂ hS
      hθ₁ hz₁ hdebt₁
  have H₂ := H₁.waveStage G.gauge w₂ q₂ e₂ HX₂
  have H₂g : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u₂ := by
    simpa only [G.inner_eq, G.outer_eq] using H₂
  have hθreg := H₂g.theta G.inner_pos G.gauge.radial.inner_lt_outer
  have hzreg := H₂g.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq rfl
  have hmean := meanStages_constructed G.gauge r h index axial c u₂ G.region G.inner_pos
      G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    rfl hσ hκsmall hh hscale gap hgap hv hfast (hs.symm ▸ hc) (hs.symm ▸ hb) (hs.symm ▸ hu₂)
    H.operators.regular H.base.smooth hV hG H₂g.mean.regular.smooth
    ⟨H₂g.mean.radial.supported, H₂g.mean.angular.supported, H₂g.mean.axial.supported⟩
    (fun i j => (H₂g.covariance i j).smooth) (fun i j => (H₂g.covariance i j).supported)
    hθreg.smooth hzreg.smooth hθreg.periodic hzreg.periodic hθreg.supported hzreg.supported
    (hs.symm ▸ hθ₂) (hs.symm ▸ hz₂) (hs.symm ▸ hbarθ) (hs.symm ▸ hbarz)
    (by simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-2*κ) = 1+σ-2*κ by ring] using hd₂)
    hg hparam hB (by simpa only [G.inner_eq] using hleft) (by simpa only [G.outer_eq] using hright)
  rw [hs] at hmean
  obtain ⟨hi, hr, hpmean, hcum, hdebt, htheta, haxial⟩ := hmean
  refine ⟨hi, hr, ?_, hcum, hdebt, htheta, haxial⟩
  apply class_congr (((hp₁.mono_exponent (by linarith)).add hp₂).add hpmean)
  intro n x hx
  change (rankStageState G.gauge r axial c (temporalStageState G.gauge h index axial c
      u₂)).pressure n x -
      u.pressure n x = ((u₁).pressure n x - u.pressure n x +
      ((u₂).pressure n x - (u₁).pressure n x)) +
      ((rankStageState G.gauge r axial c (temporalStageState G.gauge h index axial c u₂)).pressure
          n x -
      (u₂).pressure n x)
  ring


-- @@ L9182-9182 verbatim
end MeanCycle


-- @@ L9184-9184 verbatim
end FourStageMeanComposition


-- @@ L9186-9186 verbatim
section CycleUniformComposition


-- @@ L9188-9188 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L9189-9189 verbatim
open scoped ContDiff Topology BigOperators


-- @@ L9191-9195 verbatim
theorem incrementBounds_updated {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {H : ℝ} {a b : Triple D}
    (ha : IncrementBounds s H a) (hb : IncrementBounds s H b) :
    IncrementBounds s H (updated a b) :=
  ⟨ha.radial.add hb.radial, ha.angular.add hb.angular, ha.axial.add hb.axial⟩


-- @@ L9197-9199 verbatim
theorem updated_assoc {D : Type} (a b c : Triple D) :
    updated (updated a b) c = updated a (updated b c) := by
  apply triple_ext <;> exact add_assoc _ _ _


-- @@ L9201-9201 verbatim
namespace CycleParameters

-- @@ L9202-9203 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L9205-9234 verbatim
/-- The actual two wave increments retain the cumulative bound and the
difference from the fixed primary family, with constants before labels. -/
theorem finalBlock_uniform_cumulative
    (primary : ι → HarmonicBlock CyclePoint) {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17 / 25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ - κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x)) :
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17/25)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x - (primary l).velocity n i j x)) := by
  constructor
  · intro i j
    exact ((hold i j).add ((hpart i j).mono_exponent (by linarith))).add
      ((hsigned i j).mono_exponent (by linarith))
  · intro i j
    apply (((hdiff i j).add ((hpart i j).mono_exponent (by linarith))).add
      ((hsigned i j).mono_exponent (by linarith))).congr
    intro l n x hx
    change (v.blocks l).velocity n i j x - (primary l).velocity n i j x +
      (p.particularBlock v c u l).velocity n i j x + (p.signedBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x +
      (p.signedBlock v c u l).velocity n i j x - (primary l).velocity n i j x
    ring


-- @@ L9236-9264 verbatim
theorem finalBlock_increment_bounds {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hκ : 0 ≤ κ)
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1 / 2 + σ - κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x))
    (hpp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1 + σ)
      (fun l n x => (p.particularBlock v c u l).pressure n j x))
    (hsp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1 + σ - κ)
      (fun l n x => (p.signedBlock v c u l).pressure n j x)) :
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x - (v.blocks l).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ-κ)
      (fun l n x => (p.finalBlock v c u l).pressure n j x - (v.blocks l).pressure n j x)) := by
  constructor
  · intro i j
    apply (((hpart i j).mono_exponent (by linarith)).add (hsigned i j)).congr
    intro l n x hx
    change (p.particularBlock v c u l).velocity n i j x + (p.signedBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x +
      (p.signedBlock v c u l).velocity n i j x - (v.blocks l).velocity n i j x
    ring
  · intro j
    apply (((hpp j).mono_exponent (by linarith)).add (hsp j)).congr
    intro l n x hx
    change (p.particularBlock v c u l).pressure n j x + (p.signedBlock v c u l).pressure n j x =
      (v.blocks l).pressure n j x + (p.particularBlock v c u l).pressure n j x +
      (p.signedBlock v c u l).pressure n j x - (v.blocks l).pressure n j x
    ring


-- @@ L9266-9306 verbatim
/-- Apply the complete actual mean increment once to the stored harmonic
residual. The pressure-alias refresh contributes only an angular zero mode. -/
theorem meanStages_residual_gain {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hκsmall : κ ≤ 1 / 100000)
    (ho : OperatorBounds p.strip c.operators κ)
    (hR : ∀ x ∈ p.strip.domain, 0 < c.operators.radius x)
    (hb : SmoothTriple p.strip.domain c.base)
    (hm : SmoothTriple p.strip.domain u.mean)
    (hTemporal : IncrementBounds p.strip (1 + σ - 2 * κ) (p.temporalIncrement v c u))
    (hRank : IncrementBounds p.strip (1 + σ - 2 * κ) (p.rankIncrement v c u))
    (hvelocity : UniformHarmonicInteraction.UniformVelocity p.strip P (1 / 2) (p.finalBlock v c u))
    {C : ℕ → ι → Set CyclePoint}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted p.strip C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (v.blocks l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1 / 2)) (fun n l _ => (v.blocks
        l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1 / 2))
      (fun n l _ => ((v.blocks l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.finalBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hold : UniformHarmonicInteraction.UniformVelocity p.strip P (1 / 2 + σ + 1 / 10)
      (fun l => HarmonicResidual.residualBlock c (p.afterSigned v c u) (p.finalBlock v c u l)
        ((p.nextCoefficients v c u).gaussian l) (v.aliasCoefficients l))) :
    UniformHarmonicInteraction.UniformVelocity p.strip P (1/2+(σ+1/10))
      (fun l => HarmonicResidual.residualBlock c (p.next v c u) ((p.nextCoefficients v c u).blocks
          l)
        ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l))
            := by
  have hh := incrementBounds_updated hTemporal hRank
  have he : (p.next v c u).mean = updated (p.afterSigned v c u).mean
      (updated (p.temporalIncrement v c u) (p.rankIncrement v c u)) := by
    rw [p.next_mean v c u, p.afterSigned_mean v c u, updated_assoc]
  have hms : SmoothTriple p.strip.domain (p.afterSigned v c u).mean := by
    simpa only [p.afterSigned_mean v c u] using hm
  have hout := meanStage_residual_uniform c ho (by linarith) hR (p.afterSigned v c u) (p.next v c u)
    (updated (p.temporalIncrement v c u) (p.rankIncrement v c u)) he hb hms hh (p.finalBlock v c u)
    hvelocity hNormal hFreq hAng hz ((p.nextCoefficients v c u).gaussian) v.aliasCoefficients
        v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _) hold (by linarith)
  simp only [add_assoc] at hout ⊢
  exact hout


-- @@ L9308-9308 verbatim
end CycleParameters


-- @@ L9310-9310 verbatim
end CycleUniformComposition


-- @@ L9312-9312 verbatim
section ActualMovingCovariance


-- @@ L9314-9314 verbatim
open Set MeasureTheory WeightedClasses MeanIncrementBounds CorrectionState LocalSignedRequest

-- @@ L9315-9315 verbatim
open scoped ContDiff BigOperators


-- @@ L9317-9319 verbatim
/-- Whole-fiber periodicity of the actual real oscillation. -/
def OscillationPeriodic (U : Set PressureStream.Plane) (w : Oscillation Point) : Prop :=
  ∀ n R s, s ∈ U → ∀ θ, FourierAlias.TorusPeriodic (fun Y => w n ((R,(s,Y)),θ))


-- @@ L9321-9323 verbatim
theorem OscillationPeriodic.add {U : Set PressureStream.Plane} {u w : Oscillation Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) : OscillationPeriodic U (u+w) :=
  fun n R s hs θ Y k => congrArg₂ (·+·) (hu n R s hs θ Y k) (hw n R s hs θ Y k)


-- @@ L9325-9334 verbatim
theorem OscillationPeriodic.bilinearCovariance {U : Set PressureStream.Plane} {u w : Oscillation
    Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) (i j : Fin 3) :
    MeanStateRegularity.Periodic U (bilinearCovariance u w i j) := by
  intro n R s hs Y k
  unfold CorrectionState.bilinearCovariance CorrectionState.angularAverage
  apply congrArg (fun t : ℝ => t / (2 * Real.pi))
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact congrArg₂ (· * ·) (congrFun (hu n R s hs θ Y k) i) (congrFun (hw n R s hs θ Y k) j)


-- @@ L9336-9341 verbatim
theorem OscillationPeriodic.covarianceIncrement {U : Set PressureStream.Plane} {u w : Oscillation
    Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) (i j : Fin 3) :
    MeanStateRegularity.Periodic U (SignedMeanGain.covarianceIncrement u w i j) :=
  MeanStateRegularity.Periodic.sub ((hu.add hw).bilinearCovariance (hu.add hw) i j)
    (hu.bilinearCovariance hu i j)


-- @@ L9343-9352 verbatim
theorem covarianceIncrement_moving {coord a b : ℝ} (U : SlowRegion coord)
    {u w : Oscillation Point}
    (hu : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveStateRegularity.WaveSupport U a b w)
    (hup : OscillationPeriodic U.carrier u) (hwp : OscillationPeriodic U.carrier w) (i j : Fin 3) :
    GaugeMomentBalances.MovingField U a b (SignedMeanGain.covarianceIncrement u w i j) :=
  MeanStateRegularity.MovingField.of_regular (WaveStateRegularity.covarianceIncrement_regular U hu
      hw hs i j)
    (hup.covarianceIncrement hwp i j)


-- @@ L9354-9368 verbatim
theorem symmetricCovariance_moving {coord a b : ℝ} (U : SlowRegion coord)
    {u w : Oscillation Point}
    (hu : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveStateRegularity.WaveSupport U a b w)
    (hup : OscillationPeriodic U.carrier u) (hwp : OscillationPeriodic U.carrier w) (i j : Fin 3) :
    GaugeMomentBalances.MovingField U a b (LabelSumBounds.symmetricCovariance u w i j) := by
  have h₁ : GaugeDebtIncrement.Regular U a b (bilinearCovariance u w i j) := by
    rw [bilinearCovariance_comm u w i j]
    exact WaveStateRegularity.bilinearCovariance_regular U hw hu hs j i
  exact MeanStateRegularity.MovingField.add
    (MeanStateRegularity.MovingField.of_regular h₁ (hup.bilinearCovariance hwp i j))
    (MeanStateRegularity.MovingField.of_regular
      (WaveStateRegularity.bilinearCovariance_regular U hw hu hs i j) (hwp.bilinearCovariance hup i
          j))


-- @@ L9370-9370 verbatim
end ActualMovingCovariance


-- @@ L9372-9372 verbatim
section ActualGaussianMeans


-- @@ L9374-9374 verbatim
open Set MeasureTheory WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L9375-9375 verbatim
open scoped ContDiff BigOperators


-- @@ L9377-9385 verbatim
theorem block_zeroMode_pull {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) (b : HarmonicBlock E) (hb : HarmonicWaveInteraction.ZeroMode b) :
    HarmonicWaveInteraction.ZeroMode (StateReindex.block e b) := by
  intro n i
  funext x
  change b.velocity n i 0 (e x) = 0
  rw [hb]
  rfl


-- @@ L9387-9396 verbatim
theorem block_angularMean_zero {D : Type}
    (b : HarmonicBlock D) (hb : HarmonicWaveInteraction.ZeroMode b)
    (hk : ∀ n, b.angularFrequency n ≠ 0) : angularMeanVector b.oscillation = 0 := by
  funext n x i
  change (∫ θ in (0:ℝ)..2*Real.pi,
    (HarmonicFields.field (b.velocity n i) (b.frequency n) (b.phase n) (b.angularFrequency n)
        (x,θ)).re) /
      (2*Real.pi) = 0
  rw [SignedWaveUpdate.angularAverage_re_field, HarmonicFields.angularMean_field _ _ _ (hk n), hb]
  rfl


-- @@ L9398-9411 verbatim
theorem fieldSum_angularMean_zero {D ι : Type}
    (labels : ℕ → Finset ι) (b : ι → HarmonicBlock D)
    (hb : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hk : ∀ l n, (b l).angularFrequency n ≠ 0) :
    angularMeanVector (LabelSumBounds.fieldSum labels (fun l => (b l).oscillation)) = 0 := by
  funext n x i
  change (∫ θ in (0:ℝ)..2*Real.pi, ∑ l ∈ labels n, (b l).oscillation n (x,θ) i) / (2*Real.pi) = 0
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_eq_zero
    intro l hl
    exact congrFun (congrFun (congrFun (block_angularMean_zero (b l) (hb l) (hk l)) n) x) i
  · intro l hl
    exact (block_angularContinuous (b l) n x i).intervalIntegrable _ _


-- @@ L9413-9413 verbatim
namespace CycleParameters

-- @@ L9414-9415 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L9417-9419 verbatim
theorem particularBlock_zero (l : ι) : HarmonicWaveInteraction.ZeroMode (p.particularBlock v c u l)
    :=
  block_zeroMode_pull _ _ (ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).1


-- @@ L9421-9423 verbatim
theorem particularGaussianBlock_zero (l : ι) :
    HarmonicWaveInteraction.ZeroMode (p.particularGaussianBlock v c u l) :=
  block_zeroMode_pull _ _ (ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).1


-- @@ L9425-9427 verbatim
theorem signedGaussianBlock_zero (l : ι) :
    HarmonicWaveInteraction.ZeroMode (p.signedGaussianBlock v c u l) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1


-- @@ L9429-9442 verbatim
theorem gaussianIncrement_angularMeans
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) :
    angularMeanVector (p.particularGaussian v c u) = 0 ∧
    angularMeanVector (p.signedGaussian v c u) = 0 := by
  constructor
  · exact fieldSum_angularMean_zero v.labels (p.particularGaussianBlock v c u)
      (p.particularGaussianBlock_zero v c u) hk
  · apply fieldSum_angularMean_zero v.labels (p.signedGaussianBlock v c u)
      (p.signedGaussianBlock_zero v c u)
    intro l n
    change (p.signedBlock v c u l).angularFrequency n ≠ 0
    rw [(hc l).angular]
    exact hk l n


-- @@ L9444-9447 verbatim
theorem gaussianIncrement_angularContinuous :
    AngularContinuous (p.particularGaussian v c u) ∧ AngularContinuous (p.signedGaussian v c u) :=
  ⟨LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _),
    LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _)⟩


-- @@ L9449-9458 verbatim
theorem next_gaussian_angularMean
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hu : AngularContinuous u.errors.gaussian) :
    angularMeanVector (p.next v c u).errors.gaussian = angularMeanVector u.errors.gaussian := by
  rw [p.next_gaussian_error v c u]
  have hs := p.gaussianIncrement_angularContinuous v c u
  have hz := p.gaussianIncrement_angularMeans v c u hk hc
  rw [angularMeanVector_add (hu.add hs.1) hs.2, angularMeanVector_add hu hs.1, hz.1, hz.2]
  simp only [add_zero]


-- @@ L9460-9467 verbatim
theorem next_alias_lift :
    (p.next v c u).errors.aliasError = u.errors.aliasError +
      fun n x => p.nextAxisymmetricAlias v c u 0 n x.1 := by
  rw [p.next_alias_error v c u]
  funext n x i
  simp only [nextAxisymmetricAlias, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, zero_add,
    VariableGaugeMean.temporalAliasState, VariableGaugeMean.pressureAliasState]
  ring


-- @@ L9469-9475 verbatim
theorem next_alias_angularContinuous (hu : AngularContinuous u.errors.aliasError) :
    AngularContinuous (p.next v c u).errors.aliasError := by
  rw [p.next_alias_lift v c u]
  apply hu.add
  intro n x i
  change Continuous (fun _ : ℝ => p.nextAxisymmetricAlias v c u 0 n x i)
  exact continuous_const


-- @@ L9477-9488 verbatim
theorem next_alias_angularMean (hu : AngularContinuous u.errors.aliasError) :
    angularMeanVector (p.next v c u).errors.aliasError =
      angularMeanVector u.errors.aliasError + p.nextAxisymmetricAlias v c u 0 := by
  have hs : AngularContinuous (fun n x => p.nextAxisymmetricAlias v c u 0 n x.1) := by
    intro n x i
    change Continuous (fun _ : ℝ => p.nextAxisymmetricAlias v c u 0 n x i)
    exact continuous_const
  rw [p.next_alias_lift v c u, angularMeanVector_add hu hs]
  congr 1
  funext n x i
  exact congrFun (congrFun (angularAverage_axisymmetric
    (fun n x => p.nextAxisymmetricAlias v c u 0 n x i)) n) x


-- @@ L9490-9494 verbatim
theorem nextAliasIncrement_angular (n : ℕ) (x : CyclePoint) :
    p.nextAxisymmetricAlias v c u 0 n x 1 = 0 := by
  simp only [nextAxisymmetricAlias, Pi.zero_apply, VariableGaugeMean.temporalAliasState,
    VariableGaugeMean.pressureAliasState, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero,
        sub_self]


-- @@ L9496-9502 verbatim
theorem nextAliasIncrement_axial (n : ℕ) (x : CyclePoint) :
    p.nextAxisymmetricAlias v c u 0 n x 2 =
      VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
        (p.afterSigned v c u) n (x,0) 2 := by
  simp only [nextAxisymmetricAlias, Pi.zero_apply, VariableGaugeMean.pressureAliasState,
    Matrix.cons_val_two,
    zero_add, add_zero, sub_self]


-- @@ L9504-9559 verbatim
/-- The actual good mean residual gains the requested exponent. New
Gaussian means vanish exactly, and the new temporal alias is the same
one retained by the mean-stage calculation. -/
theorem next_meanResidualBounds {σ : ℝ}
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hb : ∀ n x, x ∈ p.strip.domain → ∀ i,
      Continuous (fun θ : ℝ => u.errors.base n (x, θ) i))
    (hg : AngularContinuous u.errors.gaussian)
    (ha : AngularContinuous u.errors.aliasError)
    (hθ : MeanClass p.strip (1+σ) ((p.next v c u).thetaResidual c))
    (hz : MeanClass p.strip (1+σ) ((p.next v c u).axialResidual c - fun n x =>
      VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
        (p.afterSigned v c u) n (x,0) 2))
    (hgθ : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.gaussian n x 1))
    (hgz : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.gaussian n x 2))
    (haθ : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.aliasError n x 1))
    (haz : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.aliasError n x 2)) :
    CorrectionState.MeanResidualBounds p.strip σ c (p.next v c u) := by
  have hbn : ∀ n x, x ∈ p.strip.domain → ∀ i,
      Continuous (fun θ : ℝ => (p.next v c u).errors.base n (x, θ) i) := by
    simpa only [p.next_base_error v c u] using hb
  have hgn : AngularContinuous (p.next v c u).errors.gaussian := by
    rw [p.next_gaussian_error v c u]
    exact (hg.add (p.gaussianIncrement_angularContinuous v c u).1).add
      (p.gaussianIncrement_angularContinuous v c u).2
  have han := p.next_alias_angularContinuous v c u ha
  have he n x hx i := meanGoodResidual_at c (p.next v c u) n x i
    (hbn n x hx i) (hgn n x i) (han n x i)
  have hgm := p.next_gaussian_angularMean v c u hk hc hg
  have ham := p.next_alias_angularMean v c u ha
  constructor
  · apply class_congr (Class.sub (Class.sub hθ hgθ) haθ)
    intro n x hx
    dsimp only
    rw [he n x hx 1, hgm, ham]
    change (p.next v c u).thetaResidual c n x - angularMeanVector u.errors.gaussian n x 1 -
      (angularMeanVector u.errors.aliasError n x 1 + p.nextAxisymmetricAlias v c u 0 n x 1) = _
    rw [p.nextAliasIncrement_angular v c u, add_zero]
    rfl
  · apply class_congr (Class.sub (Class.sub hz hgz) haz)
    intro n x hx
    dsimp only
    rw [he n x hx 2, hgm, ham]
    change (p.next v c u).axialResidual c n x - angularMeanVector u.errors.gaussian n x 2 -
      (angularMeanVector u.errors.aliasError n x 2 + p.nextAxisymmetricAlias v c u 0 n x 2) = _
    rw [p.nextAliasIncrement_axial v c u]
    change (p.next v c u).axialResidual c n x - angularMeanVector u.errors.gaussian n x 2 -
      (angularMeanVector u.errors.aliasError n x 2 +
        VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
          (p.afterSigned v c u) n (x,0) 2) =
      ((p.next v c u).axialResidual c n x -
        VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
          (p.afterSigned v c u) n (x,0) 2) - angularMeanVector u.errors.gaussian n x 2 -
        angularMeanVector u.errors.aliasError n x 2
    ring


-- @@ L9561-9561 verbatim
end CycleParameters


-- @@ L9563-9563 verbatim
end ActualGaussianMeans


-- @@ L9565-9565 verbatim
section ActualCycleMeanGain


-- @@ L9567-9567 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L9568-9568 verbatim
open scoped ContDiff BigOperators

-- @@ L9569-9569 verbatim
namespace CycleParameters


-- @@ L9571-9586 verbatim
/-- One geometric choice is shared by all four literal stages. -/
noncomputable def ofGeometry {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (rank : RankData PressureStream.Plane) : CycleParameters ι where
  gauge := G.gauge
  strip := G.strip
  patch := G.patch
  coordinate := G.coord
  timeExponent := h
  commonIndex := index
  axial := axial
  particular := particular
  signed := signed
  rank := rank


-- @@ L9588-9588 verbatim
section ActualMean

-- @@ L9589-9598 verbatim
variable {ι : Type} (G : SignedMeanGain.Geometry) (B : SignedMeanGain.NativeData G)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (r : RankData PressureStream.Plane)
    (v : CycleCoefficients ι) (c : Context CyclePoint) (u : State CyclePoint)
    (primary : ι → HarmonicBlock CyclePoint) (P : ι → ℕ → CyclePoint → ℝ)
    {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (N : ℕ)
    (hprimary : ∀ l, (primary l).BandLimited N) (hband : CoefficientBands v)
    (hcp : ∀ l, SameCarrier (v.blocks l) (primary l))



-- @@ L9601-9618 verbatim
variable (hcs : ∀ l, SameCarrier (v.blocks l) ((ofGeometry G h index axial particular signed
    r).signedBlock v c u l))
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (17 / 25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2 + σ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).particularBlock v c u
          l).velocity n i j x))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2 + σ - κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedTangent v c u
          l).velocity n i j x))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 + σ - 2 * κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedCurl v c u l).velocity
          n i j x))
    (hP0 : ∀ l n x, x ∈ G.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ G.strip.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)


-- @@ L9620-9622 verbatim
local notation "F" => signedFamily (ofGeometry G h index axial particular signed r) v c u primary P
    hσ N hprimary hband hcp hcs
  hold hdiff hpart htangent hcurl hP0 hP1 hkp


-- @@ L9624-9744 verbatim
/-- The complete measured-mean gain for `next`. The signed family is
computed from this cycle's actual particular, tangent, and curl blocks;
its first covariance estimate is derived from the same finite labels. -/
theorem mean_gain_from_waves
    (a : SignedMeanGain.Assembly F) (halabels : a.labels = v.labels)
    {axis : AxisymmetricAlias} (hrep : CycleRepresentation v u axis)
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l))
    (hpartzero : ∀ l, HarmonicWaveInteraction.ZeroMode ((ofGeometry G h index axial particular
        signed r).particularBlock v c u l))
    (hsold : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => (v.blocks l).oscillation))
    (hspart : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => ((ofGeometry G h index axial particular signed r).particularBlock v c u
          l).oscillation))
    (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hop : c.operators = G.operators)
    (ho : OperatorBounds G.strip G.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation ((ofGeometry G h index axial particular
          signed r).particularVelocity v c u) i j))
    (hX₂ : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor F a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor F a i j))
    (e : ℕ → ι → SignedMeanGain.NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (v.labels n : Set ι))
    (hlabels : ∀ n, (v.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ v.labels n → (primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hpc : ∀ n l, l ∈ v.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      (primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ v.labels n → ((ofGeometry G h index axial particular signed r).signedTangent v
        c u l).velocity n =
      (B.signedBlocks c ((ofGeometry G h index axial particular signed r).afterParticular v c u) (e
          n l)).velocity n)
    (htc : ∀ n l, l ∈ v.labels n → BandReindexedSignedMeanGain.SameCarrierAt
      ((ofGeometry G h index axial particular signed r).signedTangent v c u l) (B.signedBlocks c
          ((ofGeometry G h index axial particular signed r).afterParticular v c u) (e n l)) n)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ G.slow n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^
        (1 + h))
    (hV : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c ((ofGeometry G h index axial
        particular signed r).afterTemporal v c u))
    {A₀ B₀ : ℝ} (hparam : RankStateBounds.NormalizedParameters G.coord A₀ B₀ r G.region.carrier)
    (hB : B₀ ≠ 0) (hleft : G.patch.a < r.inner) (hright : r.outer < G.patch.b) :
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).temporalIncrement v c u) ∧
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).rankIncrement v c u) ∧
    MeanClass G.strip (1+σ-2*κ) (((ofGeometry G h index axial particular signed r).next v c
        u).pressure-u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip ((ofGeometry G h index axial particular signed r).next
        v c u) ∧
    DefectBounds G.slowStrip (σ+1/10) c ((ofGeometry G h index axial particular signed r).next v c
        u) ∧
    MeanClass G.strip (1+(σ+1/10)) (((ofGeometry G h index axial particular signed r).next v c
        u).thetaResidual c) ∧
    MeanClass G.strip (1+(σ+1/10))
      (((ofGeometry G h index axial particular signed r).next v c u).axialResidual c - fun n x =>
          temporalAliasState G.gauge h index c
        ((ofGeometry G h index axial particular signed r).afterSigned v c u) n (x,0) 2) := by
  have hrep₀ : u.oscillation = LabelSumBounds.fieldSum a.labels (fun l => (v.blocks l).oscillation)
      := by
    rw [halabels]
    funext n x i
    exact hrep.velocity n x i
  have hcov := assembledCovarianceIncrement_mem (show (1:ℝ)/2 ≤ 1/2+σ by linarith)
    a.labels a.label a.injective a.level a.window a.window_continuous a.auxiliary
    v.blocks ((ofGeometry G h index axial particular signed r).particularBlock v c u)
        v.residualBand hband.velocityPressure
    ((ofGeometry G h index axial particular signed r).particularBlock_band v c u) (fun _ =>
        ⟨rfl,rfl,rfl⟩)
    (fun i j _ => hold i j) (fun i j _ => hpart i j) hzero hpartzero hP0 hP1 hkp hsold hspart u
        hrep₀
  have hcov' : SignedMeanGain.TensorClass G.strip (1+σ)
      (SignedMeanGain.covarianceIncrement u.oscillation ((ofGeometry G h index axial particular
          signed r).particularVelocity v c u)) := by
    simp only [halabels, particularVelocity, show (1:ℝ)/2+(1/2+σ) = 1+σ by ring] at hcov ⊢
    exact hcov
  have hrep₁ : ((ofGeometry G h index axial particular signed r).afterParticular v c u).oscillation
      = SignedMeanGain.oldField F a := by
    simpa only [SignedMeanGain.oldField, halabels, signedFamily] using (ofGeometry G h index axial
        particular signed r).beforeSignedBlock_represents v c u hrep
  have hw₂ : SignedMeanGain.tangentField F a + SignedMeanGain.curlField F a = (ofGeometry G h index
      axial particular signed r).signedVelocity v c u := by
    simpa only [SignedMeanGain.tangentField, SignedMeanGain.curlField, signedFamily, halabels] using
      ((ofGeometry G h index axial particular signed r).signedVelocity_split v c u).symm
  have hgain := fourStage_mean_gain G B c u ((ofGeometry G h index axial particular signed
      r).particularVelocity v c u) ((ofGeometry G h index axial particular signed
          r).particularPressure v c u)
    ((ofGeometry G h index axial particular signed r).particularGaussian v c u) F a ((ofGeometry G
        h index axial particular signed r).signedPressure v c u) ((ofGeometry G h index axial
            particular signed r).signedGaussian v c u)
    hσ hκ hκsmall H hop ho hb hu hfixed hmθ hmz hθ hz hd hX₁ hcov' hX₂ hS hrep₁ e
    (by simpa only [halabels] using he) (by simpa only [halabels] using hlabels)
    (by simpa only [signedFamily, halabels] using hp)
    (by simpa only [signedFamily, halabels] using hpc)
    (by
      have harg := ht
      simp only [signedFamily, halabels] at harg ⊢
      exact harg)
    (by
      have harg := htc
      simp only [signedFamily, halabels] at harg ⊢
      exact harg)
    r h index axial hh hscale gap hgap hv hfast hV hG
    (by erw [hw₂]; exact hg) hparam hB hleft hright
  erw [hw₂] at hgain
  obtain ⟨hi, hr, hpmean, hcum, hdebt, htheta, haxial⟩ := hgain
  exact ⟨hi, hr, hpmean, ⟨hcum.velocity, hcum.pressure⟩, hdebt, htheta, haxial⟩


-- @@ L9746-9746 verbatim
end ActualMean

-- @@ L9747-9747 verbatim
end CycleParameters


-- @@ L9749-9749 verbatim
end ActualCycleMeanGain


-- @@ L9751-9751 verbatim
section CycleRegularityPreservation


-- @@ L9753-9753 verbatim
open Set CorrectionState VariableGaugeMean LocalSignedRequest MeanStateRegularity

-- @@ L9754-9754 verbatim
namespace CycleParameters

-- @@ L9755-9756 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L9758-9783 verbatim
/-- Primitive regularity is propagated through the literal four-stage
state. The rank geometry is reused from the incoming state; its new
measured-debt smoothness is proved from the updated primitive fields. -/
theorem next_primitive {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (H : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u) :
    PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.next v c u) ∧
      reconstructState p.gauge c (p.next v c u) = p.next v c u := by
  have H₁ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterParticular v c u) :=
    H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) hX₁
  have H₂ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) :=
    H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) hX₂
  have ht := MeanStageRegularity.temporalStage_primitive H₂ ha hd hell rfl
    p.timeExponent p.commonIndex p.axial
  have hgt := MeanStageRegularity.rankGeometry_for_state ht ha p.gauge.radial.inner_lt_outer hg
  have hr := MeanStageRegularity.rankStage_primitive ht hgt hell p.axial
  exact ⟨⟨hr.operators, hr.base, hr.mean, hr.covariance, hr.virtualTheta, hr.virtualAxial⟩, rfl⟩


-- @@ L9785-9815 verbatim
theorem next_zeroMassesOn {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (H : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u)
    (hlength : ∀ n x, x ∈ U.carrier → p.rank.length n x = qLength coord x)
    (hleft : p.gauge.radial.inner ≤ p.rank.inner) (hright : p.rank.outer ≤ p.gauge.radial.outer)
    (hm : GaugeMassPreservation.ZeroMassesOn U.carrier u) :
    GaugeMassPreservation.ZeroMassesOn U.carrier (p.next v c u) := by
  have H₁ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterParticular v c u) :=
    H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) hX₁
  have H₂ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) :=
    H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) hX₂
  have ht := MeanStageRegularity.temporalStage_primitive H₂ ha hd hell rfl
    p.timeExponent p.commonIndex p.axial
  have hgt := MeanStageRegularity.rankGeometry_for_state ht ha p.gauge.radial.inner_lt_outer hg
  have hθ := H₂.theta ha p.gauge.radial.inner_lt_outer
  have hz := H₂.axial_reconstructed ha hd hell rfl
  intro n x hx
  have he := p.next_preserve_masses v c u U ha hd hell H.mean.regular.smooth
    ⟨H.mean.radial.supported,H.mean.angular.supported,H.mean.axial.supported⟩
    hθ.smooth hz.smooth hθ.periodic hz.periodic hθ.supported hz.supported
    hgt hlength hleft hright n hx
  exact ⟨he.1.trans (hm n x hx).1, he.2.trans (hm n x hx).2⟩


-- @@ L9817-9817 verbatim
end CycleParameters


-- @@ L9819-9819 verbatim
end CycleRegularityPreservation


-- @@ L9821-9821 verbatim
section CycleAssociationTransport


-- @@ L9823-9823 verbatim
open Set WeightedClasses CorrectionState

-- @@ L9824-9824 verbatim
open scoped BigOperators

-- @@ L9825-9825 verbatim
section Reindex

-- @@ L9826-9827 verbatim
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L9829-9832 verbatim
theorem reindex_addBlock (e : D ≃ₗᵢ[ℝ] E) (a b : HarmonicBlock E) :
    StateReindex.block e (HarmonicWaveInteraction.addBlock a b) =
      HarmonicWaveInteraction.addBlock (StateReindex.block e a) (StateReindex.block e b) := by
  simp only [StateReindex.block, HarmonicWaveInteraction.addBlock, StateReindex.coefficients_add]


-- @@ L9834-9838 verbatim
theorem reindex_coefficients_add (e : D ≃ₗᵢ[ℝ] E) (G A : HarmonicResidual.BlockCoefficients E) :
    StateReindex.blockCoefficients e (G+A) =
      StateReindex.blockCoefficients e G + StateReindex.blockCoefficients e A := by
  funext n i
  exact StateReindex.coefficients_add e (G n i) (A n i)


-- @@ L9840-9843 verbatim
theorem reindex_coefficients_roundtrip (e : D ≃ₗᵢ[ℝ] E) (G : HarmonicResidual.BlockCoefficients D) :
    StateReindex.blockCoefficients e (StateReindex.blockCoefficients e.symm G) = G := by
  funext n i
  exact StateReindex.coefficients_roundtrip e (G n i)


-- @@ L9845-9860 verbatim
/-- Returning the actual mixed old/new block and its new Gaussian term
commutes with the entire nonlinear residual, including all derivatives. -/
theorem residual_update_return (e : D ≃ₗᵢ[ℝ] E) (c : Context D) (u : State D)
    (a : HarmonicBlock D) (b : HarmonicBlock E)
    (G A : HarmonicResidual.BlockCoefficients D) (g : HarmonicResidual.BlockCoefficients E) :
    StateReindex.block e
      (HarmonicResidual.residualBlock (StateReindex.context e.symm c) (StateReindex.state e.symm u)
        (HarmonicWaveInteraction.addBlock (StateReindex.block e.symm a) b)
        (StateReindex.blockCoefficients e.symm G+g) (StateReindex.blockCoefficients e.symm A)) =
      HarmonicResidual.residualBlock c u (HarmonicWaveInteraction.addBlock a (StateReindex.block e
          b))
        (G+StateReindex.blockCoefficients e g) A := by
  rw [← StateReindex.residualBlock_pull, StateReindex.context_roundtrip,
      StateReindex.state_roundtrip,
    reindex_addBlock, StateReindex.block_roundtrip, reindex_coefficients_add,
    reindex_coefficients_roundtrip, reindex_coefficients_roundtrip]


-- @@ L9862-9878 verbatim
theorem residual_update_uniform_return {ι : Type} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (c : Context D) (u : State D) (a : ι → HarmonicBlock D) (b : ι → HarmonicBlock E)
    (G A : ι → HarmonicResidual.BlockCoefficients D) (g : ι → HarmonicResidual.BlockCoefficients E)
    (hh : UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n x => P l n (e.symm x)) α
      (fun l => HarmonicResidual.residualBlock (StateReindex.context e.symm c) (StateReindex.state
          e.symm u)
        (HarmonicWaveInteraction.addBlock (StateReindex.block e.symm (a l)) (b l))
        (StateReindex.blockCoefficients e.symm (G l) + g l) (StateReindex.blockCoefficients e.symm
            (A
            l)))) :
    UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u
        (HarmonicWaveInteraction.addBlock (a l) (StateReindex.block e (b l)))
        (G l+StateReindex.blockCoefficients e (g l)) (A l)) := by
  simpa only [residual_update_return] using MeanBoundsReindex.uniformVelocity_return e hh


-- @@ L9880-9880 verbatim
end Reindex


-- @@ L9882-9882 verbatim
end CycleAssociationTransport


-- @@ L9884-9884 verbatim
section CycleResidualGrouping


-- @@ L9886-9886 verbatim
open Set CorrectionState

-- @@ L9887-9887 verbatim
open scoped BigOperators

-- @@ L9888-9888 verbatim
namespace CycleRepresentation

-- @@ L9889-9889 verbatim
variable {ι : Type} {v : CycleCoefficients ι} {u : State CyclePoint} {axis : AxisymmetricAlias}


-- @@ L9891-9894 verbatim
theorem withAxis (h : CycleRepresentation v u axis) :
    AxisymmetricResidualGrouping.Representation v.labels v.blocks v.gaussian v.aliasCoefficients u
        axis :=
  ⟨h.velocity, h.pressure, h.gaussian, h.aliasError⟩


-- @@ L9896-9904 verbatim
theorem fullGoodWaveResidual_grouped (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : HarmonicResidual.ExtractionRegular U c u v.labels v.blocks v.gaussian v.aliasCoefficients
        n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullGoodWaveResidual c u n x i = ∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients
          l)).oscillation n x i :=
  AxisymmetricResidualGrouping.stateGoodWaveResidual_grouped hU h.withAxis hr hx i


-- @@ L9906-9917 verbatim
theorem fullResidual_reconstructed (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : HarmonicResidual.ExtractionRegular U c u v.labels v.blocks v.gaussian v.aliasCoefficients
        n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullResidual c u n x i = (∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients
          l)).oscillation n x i) +
      (HarmonicResidual.stateMeanCoefficientValue v.labels v.blocks v.gaussian v.aliasCoefficients
          c u n x.1 i -
        axis n x.1 i) + u.errors.total n x i :=
  AxisymmetricResidualGrouping.stateFullResidual_reconstructed hU h.withAxis hr hx i


-- @@ L9919-9927 verbatim
theorem fullGoodWaveResidual_grouped_local (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : LocalResidualGrouping.ExtractionRegular U c u v.labels v.blocks v.gaussian
        v.aliasCoefficients n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullGoodWaveResidual c u n x i = ∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients
          l)).oscillation n x i :=
  LocalResidualGrouping.stateGoodWaveResidual_grouped hU h.withAxis hr hx i


-- @@ L9929-9940 verbatim
theorem fullResidual_reconstructed_local (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : LocalResidualGrouping.ExtractionRegular U c u v.labels v.blocks v.gaussian
        v.aliasCoefficients n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullResidual c u n x i = (∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients
          l)).oscillation n x i) +
      (HarmonicResidual.stateMeanCoefficientValue v.labels v.blocks v.gaussian v.aliasCoefficients
          c u n x.1 i -
        axis n x.1 i) + u.errors.total n x i :=
  LocalResidualGrouping.stateFullResidual_reconstructed hU h.withAxis hr hx i


-- @@ L9942-9942 verbatim
end CycleRepresentation


-- @@ L9944-9944 verbatim
end CycleResidualGrouping


-- @@ L9946-9946 verbatim
section RealCoefficientStructure

-- @@ L9947-9947 verbatim
open Set Filter CorrectionState HarmonicFields

-- @@ L9948-9948 verbatim
open scoped Topology ComplexConjugate


-- @@ L9950-9956 verbatim
/-- The stored coefficients themselves represent real fields. Retaining
this algebraic invariant lets support of the real projection control the
same coefficients used in the differentiated interaction estimates. -/
structure CycleRealCoefficients {ι : Type} (v : CycleCoefficients ι) : Prop where
  velocity : ∀ l n i, ConjugateSymmetric ((v.blocks l).velocity n i)
  pressure : ∀ l n, ConjugateSymmetric ((v.blocks l).pressure n)
  gaussian : ∀ l n i, ConjugateSymmetric (v.gaussian l n i)


-- @@ L9958-9962 verbatim
private theorem conjugate_add {D : Type} {a b : Coefficients D}
    (ha : ConjugateSymmetric a) (hb : ConjugateSymmetric b) : ConjugateSymmetric (a+b) := by
  intro j x
  change a (-j) x + b (-j) x = conj (a j x + b j x)
  rw [ha j x, hb j x, map_add]


-- @@ L9964-9968 verbatim
private theorem conjugate_pull {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) {a : Coefficients E} (ha : ConjugateSymmetric a) :
    ConjugateSymmetric (StateReindex.coefficients e a) :=
  fun j x => ha j (e x)


-- @@ L9970-9970 verbatim
namespace CycleParameters

-- @@ L9971-9972 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L9974-9978 verbatim
theorem particularBlock_real (l : ι) : ErrorHarmonics.RealBlock (p.particularBlock v c u l) :=
  ⟨fun n i => conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1
      n i),
    fun n => conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2
        n)⟩


-- @@ L9980-9981 verbatim
theorem signedBlock_real (l : ι) : ErrorHarmonics.RealBlock (p.signedBlock v c u l) :=
  SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _


-- @@ L9983-9999 verbatim
theorem next_realCoefficients (h : CycleRealCoefficients v) :
    CycleRealCoefficients (p.nextCoefficients v c u) := by
  have hpv l n i : ConjugateSymmetric ((p.particularBlock v c u l).velocity n i) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i)
  have hpp l n : ConjugateSymmetric ((p.particularBlock v c u l).pressure n) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2 n)
  have hpg l n i : ConjugateSymmetric ((p.particularGaussianBlock v c u l).velocity n i) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i)
  have hsv l n i : ConjugateSymmetric ((p.signedBlock v c u l).velocity n i) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1 n i
  have hsp l n : ConjugateSymmetric ((p.signedBlock v c u l).pressure n) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).2 n
  have hsg l n i : ConjugateSymmetric ((p.signedGaussianBlock v c u l).velocity n i) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1 n i
  exact ⟨fun l n i => conjugate_add (conjugate_add (h.velocity l n i) (hpv l n i)) (hsv l n i),
    fun l n => conjugate_add (conjugate_add (h.pressure l n) (hpp l n)) (hsp l n),
    fun l n i => conjugate_add (conjugate_add (h.gaussian l n i) (hpg l n i)) (hsg l n i)⟩


-- @@ L10001-10001 verbatim
end CycleParameters


-- @@ L10003-10016 verbatim
theorem block_velocity_zero_germ_of_inputSupport {U : Set CyclePoint} {S : ℕ → Set CyclePoint}
    (hU : IsOpen U) (hS : ∀ n, IsClosed (S n))
    {b : HarmonicBlock CyclePoint} {G A : HarmonicResidual.BlockCoefficients CyclePoint}
    (hs : HarmonicSourceSupport.InputSupportOn U S b G A)
    (hr : ∀ n i, ConjugateSymmetric (b.velocity n i)) (n : ℕ) {x : CyclePoint}
    (hx : x ∈ U) (hn : x ∉ S n) (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    b.velocity n i j =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hS n))
  · have hh := (hs.velocity n i).enlarge j hj
    rw [HarmonicResidual.realCoefficients_eq_self (hr n i)] at hh
    intro z hz
    by_contra hz'
    exact hz (hh z hz')
  · simpa using And.intro hx hn


-- @@ L10018-10034 verbatim
/-- The genuine input support controls raw nonzero coefficient germs
because their real-projection identity is retained. -/
theorem velocity_zero_germ_of_inputSupport {ι : Type} {v : CycleCoefficients ι}
    {U : Set CyclePoint} {S : ι → ℕ → Set CyclePoint}
    (hU : IsOpen U) (hS : ∀ l n, IsClosed (S l n))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (v.blocks l) (v.gaussian l) (v.aliasCoefficients l))
    (hr : CycleRealCoefficients v) (l : ι) (n : ℕ) {x : CyclePoint}
    (hx : x ∈ U) (hn : x ∉ S l n) (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    (v.blocks l).velocity n i j =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hS l n))
  · have hh := ((hs l).velocity n i).enlarge j hj
    rw [HarmonicResidual.realCoefficients_eq_self (hr.velocity l n i)] at hh
    intro z hz
    by_contra hz'
    exact hz (hh z hz')
  · simpa using And.intro hx hn


-- @@ L10036-10036 verbatim
end RealCoefficientStructure


-- @@ L10038-10038 verbatim
section AnalyticInvariant


-- @@ L10040-10040 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState LocalSignedRequest

-- @@ L10041-10041 verbatim
open scoped ContDiff BigOperators


-- @@ L10043-10043 verbatim
namespace CycleRepresentation

-- @@ L10044-10044 verbatim
variable {ι : Type} {v : CycleCoefficients ι} {u : State CyclePoint} {axis : AxisymmetricAlias}


-- @@ L10046-10051 verbatim
theorem alias_eq_lift (h : CycleRepresentation v u axis) (hz : ∀ l, v.aliasCoefficients l = 0) :
    u.errors.aliasError = fun n x => axis n x.1 := by
  funext n x i
  rw [h.aliasError]
  simp only [hz, coefficientField, Pi.zero_apply, HarmonicResidual.field_zero, Complex.zero_re,
    Finset.sum_const_zero, zero_add]


-- @@ L10053-10061 verbatim
theorem gaussian_angularContinuous (h : CycleRepresentation v u axis) :
    AngularContinuous u.errors.gaussian := by
  let b : ι → HarmonicBlock CyclePoint := fun l =>
    ⟨v.gaussian l, 0, (v.blocks l).frequency, (v.blocks l).phase, (v.blocks l).angularFrequency⟩
  have he : u.errors.gaussian = LabelSumBounds.fieldSum v.labels (fun l => (b l).oscillation) := by
    funext n x i
    exact h.gaussian n x i
  rw [he]
  exact LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _)


-- @@ L10063-10063 verbatim
end CycleRepresentation


-- @@ L10065-10123 verbatim
/-- The quantitative and local regularity invariant is stated on the
actual stored fields of `CycleState`, including the independent alias.
Its definition makes no assertion that an arbitrary step preserves it. -/
structure CycleAnalyticInvariant {ι : Type} (G : SignedMeanGain.Geometry)
    (c : Context CyclePoint) (primary : ι → HarmonicBlock CyclePoint)
    (P : ι → ℕ → CyclePoint → ℝ) (labelCarrier : ι → ℕ → Set CyclePoint)
    (σ : ℝ) (x : CycleState ι) : Prop where
  representation : CycleRepresentation x.coefficients x.state x.axisymmetricAlias
  bands : CoefficientBands x.coefficients
  realCoefficients : CycleRealCoefficients x.coefficients
  inputSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (labelCarrier l)
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
  sourceBand : ∀ l, (HarmonicResidual.residualBlock c x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)).BandLimited
        x.coefficients.residualBand
  zeroVelocity : ∀ l, HarmonicWaveInteraction.ZeroMode (x.coefficients.blocks l)
  zeroPressure : ∀ l n, (x.coefficients.blocks l).pressure n 0 = 0
  carrier : ∀ l, SameCarrier (x.coefficients.blocks l) (primary l)
  phase : ∀ l n, ContDiffOn ℝ ∞ ((x.coefficients.blocks l).phase n) G.strip.domain
  frequency : ∀ l n, (x.coefficients.blocks l).frequency n ≠ 0
  angular : ∀ l n, (x.coefficients.blocks l).angularFrequency n ≠ 0
  coefficientSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    ((x.coefficients.blocks l).velocity n i)
  pressureCoefficientSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    ((x.coefficients.blocks l).pressure n)
  gaussianCoefficientSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (x.coefficients.gaussian l n i)
  solenoidal : ∀ l, HarmonicWaveInteraction.ModeSolenoidal G.strip c (x.coefficients.blocks l)
  wave : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2)
    (fun l n z => (x.coefficients.blocks l).velocity n i j z)
  pressure : ∀ j, LabelSumBounds.UniformWaveClass G.strip P 1
    (fun l n z => (x.coefficients.blocks l).pressure n j z)
  difference : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (17/25)
    (fun l n z => (x.coefficients.blocks l).velocity n i j z - (primary l).velocity n i j z)
  cumulative : CorrectionState.CumulativeBounds G.strip x.state
  covariance : ∀ i j, MeanClass G.strip 1 (x.state.covariance i j)
  residual : UniformHarmonicInteraction.UniformVelocity G.strip P (1/2+σ)
    (fun l => HarmonicResidual.residualBlock c x.state (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
  mean : MeanResidualBounds G.strip σ c x.state
  meanHypotheses : LiftedMeanResidual.MeanHypotheses G.strip.domain c x.state
  debt : DefectBounds G.slowStrip σ c x.state
  primitives : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c x.state
  reconstructed : VariableGaugeMean.reconstructState G.gauge c x.state = x.state
  masses : GaugeMassPreservation.ZeroMassesOn G.region.carrier x.state
  oscillationSmooth : WaveStateRegularity.AngularSmooth G.domain x.state.oscillation
  oscillatoryPressureSmooth : ∀ n, ContDiffOn ℝ ∞ (x.state.oscillatoryPressure n)
    (G.domain ×ˢ (Set.univ : Set ℝ))
  oscillationPeriodic : OscillationPeriodic G.region.carrier x.state.oscillation
  oscillationSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
      x.state.oscillation
  gaussianFlat : ∀ β i j, LabelSumBounds.UniformClass G.strip
    (fun _ _ z => Real.sqrt (G.strip.zeta z)) β
    (fun l n z => x.coefficients.gaussian l n i j z)
  gaussianMean : angularMeanVector x.state.errors.gaussian = 0
  aliasCoefficients : ∀ l, x.coefficients.aliasCoefficients l = 0
  axisFlat : ∀ β, MeanClass G.strip β x.axisymmetricAlias
  baseAngular : ∀ n z, z ∈ G.domain → ∀ i,
    Continuous (fun θ : ℝ => x.state.errors.base n (z, θ) i)


-- @@ L10125-10125 verbatim
namespace CycleAnalyticInvariant

-- @@ L10126-10128 verbatim
variable {ι : Type} {G : SignedMeanGain.Geometry} {c : Context CyclePoint}
    {primary : ι → HarmonicBlock CyclePoint} {P : ι → ℕ → CyclePoint → ℝ}
    {labelCarrier : ι → ℕ → Set CyclePoint} {σ : ℝ} {x : CycleState ι}


-- @@ L10130-10167 verbatim
/-- Raw residual classes required by the next signed request are derived
from the good-mean invariant and the actual all-power axis alias. -/
theorem raw_mean_bounds (H : CycleAnalyticInvariant G c primary P labelCarrier σ x) :
    MeanClass G.strip (1+σ) (x.state.thetaResidual c) ∧
    MeanClass G.strip (1+σ) (x.state.axialResidual c) := by
  have ha := H.representation.alias_eq_lift H.aliasCoefficients
  have hca : AngularContinuous x.state.errors.aliasError := by
    rw [ha]
    intro n z i
    change Continuous (fun _ : ℝ => x.axisymmetricAlias n z i)
    exact continuous_const
  have ham : angularMeanVector x.state.errors.aliasError = x.axisymmetricAlias := by
    rw [ha]
    funext n z i
    exact congrFun (congrFun (angularAverage_axisymmetric (fun n z => x.axisymmetricAlias n z i))
        n) z
  have he n z hz i := meanGoodResidual_at c x.state n z i
    (H.baseAngular n z (G.strip_subset hz) i)
    (H.representation.gaussian_angularContinuous n z i) (hca n z i)
  have haxis (i : Fin 3) : MeanClass G.strip (1+σ) (fun n z => x.axisymmetricAlias n z i) :=
    (H.axisFlat (1+σ)).map (ContinuousLinearMap.proj i)
  constructor
  · apply class_congr (H.mean.angular.add (haxis 1))
    intro n z hz
    dsimp only
    rw [he n z hz 1, H.gaussianMean, ham]
    change x.state.thetaResidual c n z = x.state.thetaResidual c n z - 0 - x.axisymmetricAlias n z
        1 +
      x.axisymmetricAlias n z 1
    ring
  · apply class_congr (H.mean.axial.add (haxis 2))
    intro n z hz
    dsimp only
    rw [he n z hz 2, H.gaussianMean, ham]
    change x.state.axialResidual c n z = x.state.axialResidual c n z - 0 - x.axisymmetricAlias n z
        2 +
      x.axisymmetricAlias n z 2
    ring


-- @@ L10169-10169 verbatim
end CycleAnalyticInvariant


-- @@ L10171-10171 verbatim
end AnalyticInvariant


-- @@ L10173-10173 verbatim
section ActualWaveCycleGain

-- @@ L10174-10174 verbatim
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L10175-10175 verbatim
open LabelSumBounds UniformHarmonicInteraction

-- @@ L10176-10176 verbatim
open scoped ContDiff Topology BigOperators


-- @@ L10178-10178 verbatim
namespace CycleParameters

-- @@ L10179-10180 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L10182-10300 verbatim
/-- The two constructed linear cancellations give the improved residual
of the literal post-signed state, including both nonlinear wave updates.
The linear estimates are the native equation/jet outputs, not estimates
on either complete updated residual. -/
theorem waveStages_residual_gain {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (ho : OperatorBounds p.strip c.operators κ)
    (hR : ∀ x ∈ p.strip.domain, 0 < c.operators.radius x)
    (hbase : BaseBounds p.strip c.base)
    (hu : MeanIncrementBounds.CumulativeBounds p.strip u.mean)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hold : ∀ i j, UniformWaveClass p.strip P (1 / 2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hpart : ∀ i j, UniformWaveClass p.strip P (1 / 2 + σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, UniformWaveClass p.strip P (1 / 2 + σ - κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain ((v.blocks l).pressure n))
    (hppart : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.particularBlock v c u l).pressure n))
    (hpsigned : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.signedBlock v c u l).pressure n))
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l))
    (hband : ∀ l, (v.blocks l).BandLimited v.residualBand)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((v.blocks l).phase n) p.strip.domain)
    (hk : ∀ l n, (v.blocks l).frequency n ≠ 0)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (v.blocks l))
    (hdivpart : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.particularBlock v c u l))
    (hdivsigned : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.signedBlock v c u l))
    {C : ℕ → ι → Set CyclePoint}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted p.strip C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (v.blocks l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1 / 2))
      (fun n l _ => (v.blocks l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1 / 2))
      (fun n l _ => ((v.blocks l).angularFrequency n : ℝ)))
    (hzpart : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.particularBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hzsigned : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.signedBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ l n x, x ∈ p.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ p.strip.domain → P l n x ≤ 1)
    (hlinearP : ∀ i j, j ≠ 0 → UniformWaveClass p.strip P (1 + σ - 3 * κ)
      (fun l n x =>
        (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients
            l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (v.blocks l) (p.particularBlock v c u l)
          (p.particularGaussianBlock v c u l).velocity).velocity n i j x))
    (hlinearS : UniformVelocity p.strip P (1 + σ - 4 * κ)
      (fun l => HarmonicWaveInteraction.linearGoodBlock c (p.beforeSignedBlock v c u l)
        (p.signedBlock v c u l) (p.signedGaussianBlock v c u l).velocity)) :
    UniformVelocity p.strip P (1/2+σ+1/10)
      (fun l => HarmonicResidual.residualBlock c (p.afterSigned v c u) (p.finalBlock v c u l)
        ((p.nextCoefficients v c u).gaussian l) (v.aliasCoefficients l)) ∧
      (∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.finalBlock v c u l)) := by
  have hκhalf : κ ≤ 1/2 := by linarith
  have hpart0 l := p.particularBlock_zero v c u l
  have hsigned0 l := (p.signed l).exactBlock_zero p.strip (p.signedRequest v c u)
  have hpartc l := p.particular_carrier v c u l
  have hpartdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c
      (HarmonicWaveInteraction.withCarrier (v.blocks l) (p.particularBlock v c u l)) := by
    rw [withCarrier_of_same (hpartc l)]
    exact hdivpart l
  have hfirst := waveStage_residual_uniform c ho hκhalf hR u (p.afterParticular v c u)
    (p.afterParticular_mean v c u) (meanIncrement_of_cumulative hu) hbase.smooth
    v.blocks (p.particularBlock v c u) (fun i j _ => hold i j) (fun i j _ => hpart i j)
    hzero hpart0 hband (p.particularBlock_band v c u) hphase hk hkp hdiv hpartdiv
    hNormal hFreq hAng hzpart hP0 hP1 hpold hppart v.gaussian
    (fun l => (p.particularGaussianBlock v c u l).velocity) v.aliasCoefficients v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hlinearP i j hj).mono_exponent (show 1/2+σ+1/10 ≤ 1+σ-3*κ by linarith))
    (by linarith) (by linarith) (by linarith)
  have hbefore : ∀ i j, UniformWaveClass p.strip P (1/2)
      (fun l n x => (p.beforeSignedBlock v c u l).velocity n i j x) := by
    intro i j
    exact (hold i j).add ((hpart i j).mono_exponent (by linarith))
  have hbzero l : HarmonicWaveInteraction.ZeroMode (p.beforeSignedBlock v c u l) :=
    HarmonicStructurePreservation.zeroMode_addBlock (hzero l) (hpart0 l)
  have hbband l : (p.beforeSignedBlock v c u l).BandLimited v.residualBand := by
    have hb := addBlock_band (hband l) (p.particularBlock_band v c u l)
    simp only [max_self] at hb
    exact hb
  have hbdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.beforeSignedBlock v c u l) :=
    HarmonicStructurePreservation.modeSolenoidal_addBlock (hpartc l).frequency (hpartc l).phase
      (hpartc l).angular (fun n i j => (hold i j).smooth l n)
      (fun n i j => (hpart i j).smooth l n) (hphase l) (hdiv l) (hdivpart l)
  have hbpressure l n : HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.beforeSignedBlock v c u l).pressure n) := by
    intro j
    exact (hpold l n j).add (hppart l n j)
  have hbsame l : SameCarrier (p.beforeSignedBlock v c u l) (p.signedBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  have hsdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c
      (HarmonicWaveInteraction.withCarrier (p.beforeSignedBlock v c u l) (p.signedBlock v c u l))
          := by
    rw [withCarrier_of_same (hbsame l)]
    exact hdivsigned l
  have hm : (p.afterSigned v c u).mean = (p.afterParticular v c u).mean := by
    rw [p.afterSigned_mean v c u, p.afterParticular_mean v c u]
  have hmean : IncrementBounds p.strip (9/10) (p.afterParticular v c u).mean := by
    rw [p.afterParticular_mean v c u]
    exact meanIncrement_of_cumulative hu
  have hsecond := waveStage_residual_uniform c ho hκhalf hR (p.afterParticular v c u)
    (p.afterSigned v c u) hm hmean hbase.smooth (p.beforeSignedBlock v c u) (p.signedBlock v c u)
    (fun i j _ => hbefore i j) (fun i j _ => hsigned i j) hbzero hsigned0 hbband
    (fun l => (p.signed l).exactBlock_band p.strip (p.signedRequest v c u))
    hphase hk hkp hbdiv hsdiv hNormal hFreq hAng hzsigned hP0 hP1 hbpressure hpsigned
    (fun l => v.gaussian l + (p.particularGaussianBlock v c u l).velocity)
    (fun l => (p.signedGaussianBlock v c u l).velocity) v.aliasCoefficients v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hfirst i j hj).add ((hlinearS i j hj).mono_exponent
      (show 1/2+σ+1/10 ≤ 1+σ-4*κ by linarith)))
    (by linarith) (by linarith) (by linarith)
  refine ⟨hsecond, ?_⟩
  intro l
  exact HarmonicStructurePreservation.modeSolenoidal_addBlock (hbsame l).frequency (hbsame l).phase
    (hbsame l).angular (fun n i j => (hbefore i j).smooth l n)
    (fun n i j => (hsigned i j).smooth l n) (hphase l) (hbdiv l) (hdivsigned l)


-- @@ L10302-10302 verbatim
end CycleParameters

-- @@ L10303-10303 verbatim
end ActualWaveCycleGain


-- @@ L10305-10305 verbatim
section DerivedRequestGain

-- @@ L10306-10306 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest

-- @@ L10307-10307 verbatim
open scoped ContDiff


-- @@ L10309-10332 verbatim
/-- The actual full signed request is controlled by the current raw
residuals. Their smoothness and support are derived from primitive state
regularity and the actual pressure reconstruction. -/
theorem fullRequest_bounds_of_primitive (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    {α : ℝ} (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    ∀ i, MeanClass (HarmonicWaveInteraction.productStrip G.strip) (α-1)
      (fun n x => fullRequest G.strip G.patch G.coord c u n x i) := by
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have ht := H.theta G.patch.a_pos G.patch.a_lt_b
  have hz' := H₀.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq hfixed
  have hs : ∀ n, MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (u.axialResidual c n)
      := by
    simpa only [G.inner_eq, G.outer_eq] using fun n =>
        MeanStateRegularity.MovingField.movingSupport hz' n
  exact fullRequest_class G.strip G.patch G.coord c u
    (normalizedRequest_class G.region G.patch G.left_pos G.right_pos G.epsilon G.slow
      G.epsilon_pos G.epsilon_le_one G.slow_ge_one c u α ht.smooth hz'.smooth (fun n =>
          MeanStateRegularity.MovingField.movingSupport ht n) hs hθ hz)


-- @@ L10334-10388 verbatim
/-- The first actual wave supplies the current raw residuals and debt
used by the signed request. No post-wave residual estimate is assumed. -/
theorem waveStage_mean_gain (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point) (w : Oscillation Point)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (ho : OperatorBounds G.strip c.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (hXC : SignedMeanGain.TensorClass G.strip (1 + σ)
      (SignedMeanGain.covarianceIncrement u.oscillation w)) :
    let next := SignedMeanGain.waveStage G.gauge c u w q gaussian
    MeanClass G.strip (1+σ-κ) (next.pressure-u.pressure) ∧
      CorrectionState.CumulativeBounds G.strip next ∧
      MeanClass G.strip (1+σ-κ) (next.thetaResidual c) ∧
      MeanClass G.strip (1+σ-κ) (next.axialResidual c) ∧
      DefectBounds G.slowStrip (σ-κ) c next ∧
      (∀ i, MeanClass (HarmonicWaveInteraction.productStrip G.strip) (σ-κ)
        (fun n x => fullRequest G.strip G.patch G.coord c next n x i)) := by
  dsimp only
  have hs : movingStripData G.region G.gauge.radial.inner G.gauge.radial.outer
      G.leftWeight G.rightWeight G.inner_pos G.left_pos G.right_pos
      G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one = G.strip := by
    simp only [SignedMeanGain.Geometry.strip, G.inner_eq, G.outer_eq]
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have HX : ∀ i j, GaugeDebtIncrement.Regular G.region G.gauge.radial.inner G.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w i j) := by
    simpa only [G.inner_eq, G.outer_eq] using
      (fun i j => MeanStateRegularity.MovingField.regular (hX i j))
  have hf := gaugeWaveStage_mean_from_covariance G.region G.gauge G.inner_pos G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    c u w q gaussian H.operators.regular H.base.smooth H₀.mean.regular
    (fun i j => MeanStateRegularity.MovingField.regular (H₀.covariance i j)) HX
    (hs.symm ▸ ho) (hs.symm ▸ hXC) hfixed (hs.symm ▸ hb) (hs.symm ▸ hu)
    (show 9/10 ≤ (1+σ)-κ by linarith) le_rfl
    (hs.symm ▸ hθ.mono_exponent (by linarith)) (hs.symm ▸ hz.mono_exponent (by linarith))
    (fun i => (hd i).mono_exponent (by linarith))
  rw [hs] at hf
  obtain ⟨hp, hcum, htheta, haxial, hdebt⟩ := hf
  have Hn := H.waveStage G.gauge w q gaussian hX
  refine ⟨hp, hcum, htheta, haxial, ?_, ?_⟩
  · simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-κ) = 1+σ-κ by ring] using hdebt
  · have hr := fullRequest_bounds_of_primitive G c _ Hn
      (congrArg (fun a : State Point => a.pressure)
        (GaugeMomentBalances.reconstructState_idempotent _ _ _)) htheta haxial
    simpa only [show (1+σ-κ)-1 = σ-κ by ring] using hr


-- @@ L10390-10390 verbatim
end DerivedRequestGain


-- @@ L10392-10392 verbatim
section FurtherPreservation

-- @@ L10393-10393 verbatim
open Set WeightedClasses MeanIncrementBounds CorrectionState

-- @@ L10394-10394 verbatim
open scoped ContDiff


-- @@ L10396-10396 verbatim
namespace CycleParameters

-- @@ L10397-10398 verbatim
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)


-- @@ L10400-10419 verbatim
/-- Mean stages and the alias refresh leave the actual wave covariance
unchanged. Both finite wave increments are retained in this identity. -/
theorem next_covariance :
    (p.next v c u).covariance = u.covariance +
      SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) +
      SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u) := by
  change bilinearCovariance (p.next v c u).oscillation (p.next v c u).oscillation = _
  rw [p.next_oscillation]
  change bilinearCovariance (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u)
      (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u) =
    bilinearCovariance u.oscillation u.oscillation +
      (bilinearCovariance (u.oscillation + p.particularVelocity v c u)
        (u.oscillation + p.particularVelocity v c u) - bilinearCovariance u.oscillation
            u.oscillation) +
      (bilinearCovariance (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u)
        (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u) -
        bilinearCovariance (u.oscillation + p.particularVelocity v c u)
          (u.oscillation + p.particularVelocity v c u))
  abel


-- @@ L10421-10432 verbatim
theorem next_covariance_mem {α β γ : ℝ}
    (hα : γ ≤ α) (hβ : γ ≤ β)
    (hold : ∀ i j, MeanClass p.strip γ (u.covariance i j))
    (hp : SignedMeanGain.TensorClass p.strip α
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u)))
    (hs : SignedMeanGain.TensorClass p.strip β
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u))) :
    ∀ i j, MeanClass p.strip γ ((p.next v c u).covariance i j) := by
  intro i j
  rw [p.next_covariance v c u]
  exact ((hold i j).add ((hp i j).mono_exponent hα)).add ((hs i j).mono_exponent hβ)


-- @@ L10434-10444 verbatim
theorem nextAxisymmetricAlias_mem (axis : AxisymmetricAlias) {β : ℝ}
    (hold : MeanClass p.strip β axis)
    (ht : MeanClass p.strip β (fun n z => VariableGaugeMean.temporalAliasState
      p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) n (z, 0)))
    (hpn : MeanClass p.strip β (fun n z => VariableGaugeMean.pressureAliasState
      p.gauge c (p.afterRank v c u) n (z, 0)))
    (hpo : MeanClass p.strip β (fun n z => VariableGaugeMean.pressureAliasState p.gauge c u n
        (z, 0))) :
    MeanClass p.strip β (p.nextAxisymmetricAlias v c u axis) := by
  have hd := hpn.add (hpo.map (-ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))
  convert! (hold.add ht).add hd using 1


-- @@ L10446-10456 verbatim
/-- The edge weight is retained in all new Gaussian coefficients. -/
theorem next_gaussian_mem {w : ι → ℕ → CyclePoint → ℝ} {β : ℝ}
    (hold : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => v.gaussian l n i j z))
    (hp : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.particularGaussianBlock v c u l).velocity n i j z))
    (hs : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.signedGaussianBlock v c u l).velocity n i j z)) :
    ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.nextCoefficients v c u).gaussian l n i j z) :=
  fun i j => ((hold i j).add (hp i j)).add (hs i j)


-- @@ L10458-10467 verbatim
theorem next_inputSupport {U : Set CyclePoint} {S : ι → ℕ → Set CyclePoint}
    (hold : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (v.blocks l) (v.gaussian l) (v.aliasCoefficients l))
    (hp : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (p.particularBlock v c u l) (p.particularGaussianBlock v c u l).velocity 0)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (p.signedBlock v c u l) (p.signedGaussianBlock v c u l).velocity 0) :
    ∀ l, HarmonicSourceSupport.InputSupportOn U (S l) ((p.nextCoefficients v c u).blocks l)
      ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l) :=
  fun l => LabelSupportPreservation.inputSupport_two_updates (hold l) (hp l) (hs l)


-- @@ L10469-10475 verbatim
theorem next_oscillation_smooth {U : Set CyclePoint}
    (hold : WaveStateRegularity.AngularSmooth U u.oscillation)
    (hp : WaveStateRegularity.AngularSmooth U (p.particularVelocity v c u))
    (hs : WaveStateRegularity.AngularSmooth U (p.signedVelocity v c u)) :
    WaveStateRegularity.AngularSmooth U (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs


-- @@ L10477-10483 verbatim
theorem next_oscillation_periodic {U : Set PressureStream.Plane}
    (hold : OscillationPeriodic U u.oscillation)
    (hp : OscillationPeriodic U (p.particularVelocity v c u))
    (hs : OscillationPeriodic U (p.signedVelocity v c u)) :
    OscillationPeriodic U (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs


-- @@ L10485-10491 verbatim
theorem next_oscillation_support {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    (hold : WaveStateRegularity.WaveSupport U a b u.oscillation)
    (hp : WaveStateRegularity.WaveSupport U a b (p.particularVelocity v c u))
    (hs : WaveStateRegularity.WaveSupport U a b (p.signedVelocity v c u)) :
    WaveStateRegularity.WaveSupport U a b (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs


-- @@ L10493-10497 verbatim
theorem finalBlock_zero (hold : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l)) :
    ∀ l, HarmonicWaveInteraction.ZeroMode (p.finalBlock v c u l) :=
  fun l => HarmonicStructurePreservation.zeroMode_addBlock
    (HarmonicStructurePreservation.zeroMode_addBlock (hold l) (p.particularBlock_zero v c u l))
    ((p.signed l).exactBlock_zero p.strip (p.signedRequest v c u))


-- @@ L10499-10507 verbatim
theorem finalBlock_pressure_zero (hold : ∀ l n, (v.blocks l).pressure n 0 = 0) :
    ∀ l n, (p.finalBlock v c u l).pressure n 0 = 0 := by
  intro l
  apply HarmonicStructurePreservation.zeroPressure_addBlock
    (HarmonicStructurePreservation.zeroPressure_addBlock (hold l) ?_)
    ((p.signed l).exactBlock_pressure_zero p.strip (p.signedRequest v c u))
  intro n
  funext x
  exact congrFun ((ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).2 n) (cycleAssoc x)


-- @@ L10509-10520 verbatim
theorem finalBlock_pressure_cumulative {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (hold : ∀ j, LabelSumBounds.UniformWaveClass p.strip P 1
      (fun l n z => (v.blocks l).pressure n j z))
    (hp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1 + σ)
      (fun l n z => (p.particularBlock v c u l).pressure n j z))
    (hs : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1 + σ - κ)
      (fun l n z => (p.signedBlock v c u l).pressure n j z)) :
    ∀ j, LabelSumBounds.UniformWaveClass p.strip P 1
      (fun l n z => (p.finalBlock v c u l).pressure n j z) :=
  fun j => ((hold j).add ((hp j).mono_exponent (by linarith))).add
    ((hs j).mono_exponent (by linarith))


-- @@ L10522-10522 verbatim
end CycleParameters

-- @@ L10523-10523 verbatim
end FurtherPreservation


-- @@ L10525-10525 verbatim
end NavierStokes.CorrectionStep
