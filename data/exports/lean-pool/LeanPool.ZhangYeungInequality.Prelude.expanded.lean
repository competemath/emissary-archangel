/-
Copyright (c) 2026 Christopher Boone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Boone
-/

/- Import surface for PFR's Shannon entropy API. Brings entropy notation (H[X], I[X:Y],
I[X:Y|Z])
into scope for downstream modules, and hosts generic helpers reusable across the
`ZhangYeung`
hierarchy. -/
module

public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Basic


-- @@ L16-20 verbatim
/-!
# LeanPool.ZhangYeungInequality.Prelude

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.Prelude`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L25-25 verbatim
open scoped ZhangYeungPFR


-- @@ L27-27 verbatim
namespace ZhangYeung


-- @@ L29-29 verbatim
/-! ### Generic Shannon helpers -/


-- @@ L31-75 expanded
/-- Substituting variables for identically-distributed ones leaves the conditional mutual
information
unchanged. PFR exposes `IdentDistrib.condEntropy_eq` and `IdentDistrib.mutualInfo_eq`
but not this
conditional-mutual-information transport. The three sub-`IdentDistrib`s for `⟨X, Z⟩`,
`⟨Y, Z⟩`, and
`⟨⟨X, Y⟩, Z⟩` are extracted from the triple by one `IdentDistrib.comp` with a measurable
projection
each. Promoted from `ZhangYeung/CopyLemma.lean` as of M5.
-/
lemma _root_.ZhangYeung.IdentDistrib.condMutualInfo_eq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    [Finite S] [Finite T] [Finite U] {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {X' : Ω' → S} {Y' : Ω' → T}
    {Z' : Ω' → U} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hX' : Measurable X')
    (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω)) (fun ω' => (X' ω', Y' ω', Z' ω')) μ μ') :
    condMutualInfo X Y Z μ = condMutualInfo X' Y' Z' μ' :=
  by
  have hXZ : IdentDistrib (fun ω => (X ω, Z ω)) (fun ω' => (X' ω', Z' ω')) μ μ' :=
    h.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hYZ : IdentDistrib (fun ω => (Y ω, Z ω)) (fun ω' => (Y' ω', Z' ω')) μ μ' :=
    h.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have hXYZ : IdentDistrib (fun ω => ((X ω, Y ω), Z ω)) (fun ω' => ((X' ω', Y' ω'), Z' ω')) μ μ' :=
    h.comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have eHX : condEntropy X Z μ = condEntropy X' Z' μ' :=
    IdentDistrib.condEntropy_eq hX hZ hX' hZ' hXZ
  have eHY : condEntropy Y Z μ = condEntropy Y' Z' μ' :=
    IdentDistrib.condEntropy_eq hY hZ hY' hZ' hYZ
  have eHXY : condEntropy ⟨X, Y⟩ Z μ = condEntropy ⟨X', Y'⟩ Z' μ' :=
    IdentDistrib.condEntropy_eq (hX.prodMk hY) hZ (hX'.prodMk hY') hZ' hXYZ
  calc
    condMutualInfo X Y Z μ = condEntropy X Z μ + condEntropy Y Z μ - condEntropy ⟨X, Y⟩ Z μ :=
      ProbabilityTheory.condMutualInfo_eq hX hY hZ μ
    _ = condEntropy X' Z' μ' + condEntropy Y' Z' μ' - condEntropy ⟨X', Y'⟩ Z' μ' := by
      rw [eHX, eHY, eHXY]
    _ = condMutualInfo X' Y' Z' μ' := (ProbabilityTheory.condMutualInfo_eq hX' hY' hZ' μ').symm


-- @@ L77-101 expanded
/-- The three-way interaction identity

  `I[X : Y] + I[X : Z] = I[X : ⟨Y, Z⟩] + I[Y : Z] - I[Y : Z | X]`.

Equivalent to a pair of chain-rule applications on `I[X : ⟨Y, Z⟩]`, together with the
defining
identity `I[Y : Z | X] = I[Y : Z] - I[X : Y : Z]` for the three-way interaction
information.
Promoted from `ZhangYeung/Theorem3.lean` as of M5. -/
lemma mutualInfo_add_three_way_identity {Ω : Type*} [MeasurableSpace Ω] {α β γ : Type*} [Finite α]
    [Finite β] [Finite γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    mutualInfo X Y μ + mutualInfo X Z μ =
      mutualInfo X ⟨Y, Z⟩ μ + mutualInfo Y Z μ - condMutualInfo Y Z X μ :=
  by
  have hYZ : Measurable (fun ω => (Y ω, Z ω)) := hY.prodMk hZ
  simp only [mutualInfo_def]
  rw [condMutualInfo_eq hY hZ hX μ, chain_rule'' μ hY hX, chain_rule'' μ hZ hX,
    chain_rule'' μ hYZ hX]
  linarith [entropy_comm hX hY μ, entropy_comm hX hZ μ, entropy_comm hX hYZ μ]


-- @@ L103-130 expanded
/-- Data processing for PFR's random-variable form of `CondIndepFun`: if `X` and `Y` are
conditionally
independent given `Z`, then `I[X : Y] ≤ I[X : Z]`. Promoted from
`ZhangYeung/Theorem3.lean` as of
M5.
-/
lemma mutualInfo_le_of_condIndepFun {Ω : Type*} [MeasurableSpace Ω] {α β γ : Type*} [Finite α]
    [Finite β] [Finite γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : CondIndepFun X Y Z μ) :
    mutualInfo X Y μ ≤ mutualInfo X Z μ :=
  by
  have h_ent : entropy ⟨X, ⟨Y, Z⟩⟩ μ = entropy ⟨X, Z⟩ μ + entropy ⟨Y, Z⟩ μ - entropy Z μ :=
    ent_of_cond_indep μ hX hY hZ h
  have h_sub : entropy ⟨X, ⟨Z, Y⟩⟩ μ + entropy Y μ ≤ entropy ⟨X, Y⟩ μ + entropy ⟨Z, Y⟩ μ :=
    entropy_triple_add_entropy_le μ hX hZ hY
  have e_inner : entropy ⟨X, ⟨Z, Y⟩⟩ μ = entropy ⟨X, ⟨Y, Z⟩⟩ μ := by
    rw [chain_rule' μ hX (hZ.prodMk hY), chain_rule' μ hX (hY.prodMk hZ), condEntropy_comm hZ hY]
  have e_ZY : entropy ⟨Z, Y⟩ μ = entropy ⟨Y, Z⟩ μ := entropy_comm hZ hY μ
  simp only [mutualInfo_def]
  linarith [h_ent, h_sub, e_inner, e_ZY]


-- @@ L132-155 verbatim
/--
Post-composition of a `CondIndepFun` statement on its two measured coordinates by
independent
measurable functions `φ` and `ψ`. The conditioner `k` is unchanged. Mathlib's
`CondIndepFun.comp`
uses the σ-algebra form of conditional independence and does not apply to PFR's
random-variable
form; this lemma fills that gap by unfolding through `condIndepFun_iff` to a fibrewise
`∀ᵐ`-family
of `IndepFun` statements, applying Mathlib's `IndepFun.comp` inside each fibre, and
repackaging.
Promoted from `ZhangYeung/CopyLemma.lean` as of M3 (the second consumer).
-/
lemma condIndepFun_comp
    {Ω α α' β β' γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β'] [MeasurableSpace γ]
    {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    {φ : α → α'} {ψ : β → β'}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : CondIndepFun f g k μ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) k μ := by
  rw [condIndepFun_iff] at h ⊢
  filter_upwards [h] with z hfg
  exact hfg.comp hφ hψ


-- @@ L157-157 verbatim
end ZhangYeung
