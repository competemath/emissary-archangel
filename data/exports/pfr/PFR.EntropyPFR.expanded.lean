module

public import Mathlib.Algebra.Module.ZMod
public import PFR.TauFunctional
public import PFR.HundredPercent
public import PFR.Endgame


-- @@ L8-18 verbatim
/-!
# Entropic version of polynomial Freiman-Ruzsa conjecture

Here we prove the entropic version of the polynomial Freiman-Ruzsa conjecture.

## Main results

* `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
  subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$.

-/


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L23-23 verbatim
universe uG


-- @@ L25-25 verbatim
variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]


-- @@ L27-28 verbatim
variable {Ω Ω' : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]


-- @@ L30-31 verbatim
variable {G : Type uG} [AddCommGroup G] [Module (ZMod 2) G] [Finite G] [MeasurableSpace G]
  [MeasurableSingletonClass G]

-- @@ L32-33 verbatim
variable (p : refPackage Ω₀₁ Ω₀₂ G) {X₁ : Ω → G} {X₂ : Ω → G} (hX₁ : Measurable X₁)
  (hX₂ : Measurable X₂)


-- @@ L35-48 expanded
include hX₁ hX₂ in
/-- If $d[X_1;X_2] > 0$ then there are $G$-valued random variables $X'_1, X'_2$ such that
$\tau[X'_1;X'_2] < \tau[X_1;X_2]$. Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases (h_min : TauMinimizes p X₁ X₂) (hpη : p.η = 1 / 9) :
    rdist X₁ X₂ volume volume = 0 := by
  cases nonempty_fintype G
  let
    ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩ :=
    independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tauMinimizes p h_id2] at h_min
  apply
    tau_strictly_decreases_aux p Y₁ Y₂ Y₁' Y₂' hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
      (h_id2.trans h_id2'.symm) h_indep h_min hpη


-- @@ L50-67 expanded
/-- `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
    subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture (hpη : p.η = 1 / 9) :
    ∃ H : Submodule (ZMod 2) G,
      ∃ Ω : Type uG,
        ∃ mΩ : MeasureSpace Ω,
          ∃ U : Ω → G,
            IsProbabilityMeasure (ℙ : Measure Ω) ∧
              Measurable U ∧
                IsUniform H U ∧
                  rdist p.X₀₁ U volume volume + rdist p.X₀₂ U volume volume ≤
                    11 * rdist p.X₀₁ p.X₀₂ volume volume :=
  by
  cases nonempty_fintype G
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, _, htau_min⟩ := tau_minimizer_exists p
  have hdist : rdist X₁ X₂ volume volume = 0 := tau_strictly_decreases p hX₁ hX₂ htau_min hpη
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨AddSubgroup.toZModSubmodule _ H, Ω', inferInstance, U, inferInstance, hU, hH_unif, ?_⟩
  have h :
    tau p X₁ X₂ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume ≤
      tau p p.X₀₂ p.X₀₁ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume :=
    is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : rdist p.X₀₁ p.X₀₂ volume volume = rdist p.X₀₂ p.X₀₁ volume volume := rdist_symm
  have : rdist p.X₀₁ U volume volume ≤ rdist p.X₀₁ X₁ volume volume + rdist X₁ U volume volume :=
    rdist_triangle p.hmeas1 hX₁ hU
  have : rdist p.X₀₂ U volume volume ≤ rdist p.X₀₂ X₂ volume volume + rdist X₂ U volume volume :=
    rdist_triangle p.hmeas2 hX₂ hU
  linarith


-- @@ L69-80 expanded
theorem entropic_PFR_conjecture' (hpη : p.η = 1 / 9) :
    ∃ H : Submodule (ZMod 2) G,
      ∃ Ω : Type uG,
        ∃ mΩ : MeasureSpace Ω,
          ∃ U : Ω → G,
            IsUniform H U ∧
              rdist p.X₀₁ U volume volume ≤ 6 * rdist p.X₀₁ p.X₀₂ volume volume ∧
                rdist p.X₀₂ U volume volume ≤ 6 * rdist p.X₀₁ p.X₀₂ volume volume :=
  by
  have : rdist p.X₀₁ p.X₀₂ volume volume = rdist p.X₀₂ p.X₀₁ volume volume := rdist_symm
  obtain ⟨H, Ω, mΩ, U, H', hU, hUnif, h'⟩ := entropic_PFR_conjecture p hpη
  refine ⟨H, Ω, mΩ, U, hUnif, ?_⟩
  have :
    rdist p.X₀₁ U volume volume ≤ rdist p.X₀₁ p.X₀₂ volume volume + rdist p.X₀₂ U volume volume :=
    rdist_triangle p.hmeas1 p.hmeas2 hU
  have :
    rdist p.X₀₂ U volume volume ≤ rdist p.X₀₂ p.X₀₁ volume volume + rdist p.X₀₁ U volume volume :=
    rdist_triangle p.hmeas2 p.hmeas1 hU
  constructor
  · linarith
  · linarith

