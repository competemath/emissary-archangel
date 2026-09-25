/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.EvalDist.TVDist


-- @@ L11-34 verbatim
/-!
# Leakage Judgments for Side-Channel Reasoning

This file defines three leakage judgments of increasing strength, enabling formal
side-channel reasoning within the VCVio framework. All three operate on observed
computations (outputs of `runObs`) that produce a result paired with an accumulated trace.

## Main Definitions

* `TraceNoninterference`: exact trace equality in every coupling (pRHL indicator).
  Two observed computations satisfy this when their trace components always match,
  regardless of the result. This is the VCVio analogue of constant-time execution.
* `ProbLeakFree`: distributional trace independence.
  The trace distribution does not depend on secrets.
* `LeakageBound`: approximate trace independence via total variation distance.
  The trace distributions differ by at most `ε`.

## Main Results

* `traceNoninterference_implies_probLeakFree`: exact trace equality implies distributional
  independence.
* `probLeakFree_iff_leakageBound_zero`: `ProbLeakFree` is the `ε = 0` case of `LeakageBound`.
* `leakageBound_triangle`: transitivity for game-hopping arguments.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L40-40 verbatim
universe u


-- @@ L42-42 verbatim
namespace OracleComp.Leakage


-- @@ L44-44 verbatim
variable {ι₁ : Type u} {ι₂ : Type u} {ι₃ : Type u}

-- @@ L45-45 verbatim
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}

-- @@ L46-46 verbatim
variable {α β γ : Type} {ω : Type}


-- @@ L48-48 verbatim
/-! ### TraceNoninterference -/


-- @@ L50-58 verbatim
/-- Exact trace noninterference: two observed computations produce equal trace components
in every coupled output. This is the strongest leakage judgment, corresponding to
constant-time execution for deterministic channels.

Defined via `RelTriple'` (the pRHL indicator pattern from `QuantitativeDefs.lean`). -/
def TraceNoninterference [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  ProgramLogic.Relational.RelTriple' oa₁ oa₂ (fun z₁ z₂ => z₁.2 = z₂.2)


-- @@ L60-60 verbatim
/-! ### ProbLeakFree -/


-- @@ L62-71 expanded
/-- Distributional trace independence: the trace distributions are identical regardless
of which computation produced them. This captures the property that an adversary observing
only the trace cannot distinguish between the two computations.

The comparison is made at the `SPMF` level via `evalSPMF`, allowing computations over
different oracle specs to be compared. -/
def ProbLeakFree [IsUniformSpec spec₁] [IsUniformSpec spec₂] (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  evalSPMF (Prod.snd <$> oa₁) = evalSPMF (Prod.snd <$> oa₂)


-- @@ L73-73 verbatim
/-! ### LeakageBound -/


-- @@ L75-81 expanded
/-- Approximate trace independence: the trace distributions differ by at most `ε` in total
variation distance. This enables game-hopping arguments where each hop introduces a small
leakage discrepancy. -/
def LeakageBound [IsUniformSpec spec₁] [IsUniformSpec spec₂] (ε : ℝ)
    (oa₁ : OracleComp spec₁ (α × ω)) (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  SPMF.tvDist (evalSPMF (Prod.snd <$> oa₁)) (evalSPMF (Prod.snd <$> oa₂)) ≤ ε


-- @@ L83-83 verbatim
/-! ### Bridge Lemmas -/


-- @@ L85-92 verbatim
/-- Exact trace noninterference implies distributional trace independence:
if traces always match in every coupling, their distributions must be equal. -/
theorem traceNoninterference_implies_probLeakFree
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  ProgramLogic.Relational.evalSPMF_map_eq_of_relTriple' h


-- @@ L94-100 verbatim
/-- `ProbLeakFree` is equivalent to `LeakageBound 0`. -/
theorem probLeakFree_iff_leakageBound_zero
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)} :
    ProbLeakFree oa₁ oa₂ ↔ LeakageBound 0 oa₁ oa₂ := by
  rw [ProbLeakFree, LeakageBound, ← SPMF.toPMF_inj, ← SPMF.tvDist_eq_zero_iff]
  exact ⟨fun h => h.le, fun h => le_antisymm h (SPMF.tvDist_nonneg _ _)⟩


-- @@ L102-114 verbatim
/-- Transitivity of `LeakageBound` for game-hopping: if the first pair of computations
has leakage at most `ε₁` and the second pair at most `ε₂`, then the outer pair has
leakage at most `ε₁ + ε₂`. -/
theorem leakageBound_triangle
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    [IsUniformSpec spec₃]
    {ε₁ ε₂ : ℝ}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {oa₃ : OracleComp spec₃ (γ × ω)}
    (h₁₂ : LeakageBound ε₁ oa₁ oa₂) (h₂₃ : LeakageBound ε₂ oa₂ oa₃) :
    LeakageBound (ε₁ + ε₂) oa₁ oa₃ := by
  unfold LeakageBound at *
  exact (SPMF.tvDist_triangle _ _ _).trans (add_le_add h₁₂ h₂₃)


-- @@ L116-119 verbatim
/-- `ProbLeakFree` is reflexive. -/
theorem probLeakFree_refl [IsUniformSpec spec₁]
    (oa : OracleComp spec₁ (α × ω)) :
    ProbLeakFree oa oa := rfl


-- @@ L121-126 verbatim
/-- `ProbLeakFree` is symmetric. -/
theorem probLeakFree_symm
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) :
    ProbLeakFree oa₂ oa₁ := h.symm


-- @@ L128-134 verbatim
/-- `LeakageBound` with `ε = 0` implies `ProbLeakFree`. -/
theorem probLeakFree_of_leakageBound_zero
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound 0 oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  probLeakFree_iff_leakageBound_zero.mpr h


-- @@ L136-141 verbatim
/-- `LeakageBound` is reflexive with bound `0`. -/
@[simp]
theorem leakageBound_refl [IsUniformSpec spec₁]
    (oa : OracleComp spec₁ (α × ω)) :
    LeakageBound 0 oa oa := by
  simp [LeakageBound]


-- @@ L143-150 verbatim
/-- `LeakageBound` is symmetric. -/
theorem leakageBound_symm
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) :
    LeakageBound ε oa₂ oa₁ := by
  unfold LeakageBound at *
  rwa [SPMF.tvDist_comm]


-- @@ L152-158 verbatim
/-- Monotonicity: a smaller leakage bound implies a larger one. -/
theorem leakageBound_mono
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε₁ oa₁ oa₂) :
    LeakageBound ε₂ oa₁ oa₂ := le_trans h hε


-- @@ L160-160 verbatim
/-! ### Compositional Lemmas: Map -/


-- @@ L162-168 verbatim
/-- Mapping the result component preserves distributional trace independence. -/
theorem probLeakFree_map_fst
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    ProbLeakFree (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simpa only [ProbLeakFree, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h


-- @@ L170-176 verbatim
/-- Mapping the result component preserves approximate trace independence. -/
theorem leakageBound_map_fst
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    LeakageBound ε (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simpa only [LeakageBound, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h


-- @@ L178-185 verbatim
/-- Mapping the result component preserves trace noninterference. -/
theorem traceNoninterference_map_fst
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    TraceNoninterference (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simp only [TraceNoninterference, ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  exact ProgramLogic.Relational.relTriple_map h


-- @@ L187-195 verbatim
/-- Mapping the trace component with the same function preserves distributional trace
independence. -/
theorem probLeakFree_map_snd
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    ProbLeakFree (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  simp only [ProbLeakFree, snd_map_prod_map_eq_map, evalSPMF_map] at h ⊢
  exact congrArg (Functor.map g) h


-- @@ L197-205 verbatim
/-- Mapping the trace component with the same function preserves approximate trace
independence. -/
theorem leakageBound_map_snd
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    LeakageBound ε (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  simp only [LeakageBound, snd_map_prod_map_eq_map, evalSPMF_map] at h ⊢
  exact le_trans (SPMF.tvDist_map_le g _ _) h


-- @@ L207-215 verbatim
/-- Mapping the trace component with the same function preserves trace noninterference. -/
theorem traceNoninterference_map_snd
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    TraceNoninterference (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  simp only [TraceNoninterference, ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  exact ProgramLogic.Relational.relTriple_map
    (ProgramLogic.Relational.relTriple_post_mono h fun {_ _} hw => congrArg g hw)


-- @@ L217-217 verbatim
/-! ### Compositional Lemmas: Bind -/


-- @@ L219-223 verbatim
private lemma snd_map_bind_snd {m : Type → Type _} [Monad m] [LawfulMonad m]
    {α' ω₁ γ' ω₂ : Type} (mx : m (α' × ω₁)) (f : ω₁ → m (γ' × ω₂)) :
    Prod.snd <$> (mx >>= fun z => f z.2) =
    (Prod.snd <$> mx) >>= fun w => Prod.snd <$> f w := by
  simp only [monad_norm, Function.comp_apply]


-- @@ L225-240 verbatim
/-- Trace noninterference is preserved by sequential composition (bind).
The continuations may depend on both the result and the trace, but whenever the
traces match, the continuations must themselves be trace noninterfering. -/
theorem traceNoninterference_bind
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {f₁ : (α × ω) → OracleComp spec₁ (γ × ω')}
    {f₂ : (β × ω) → OracleComp spec₂ (δ × ω')}
    (h : TraceNoninterference oa₁ oa₂)
    (hf : ∀ a b w, TraceNoninterference (f₁ (a, w)) (f₂ (b, w))) :
    TraceNoninterference (oa₁ >>= f₁) (oa₂ >>= f₂) := by
  simp only [TraceNoninterference, ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  refine ProgramLogic.Relational.relTriple_bind h fun ⟨a, w₁⟩ ⟨b, w₂⟩ hw => ?_
  subst hw
  exact ProgramLogic.Relational.relTriple'_iff_relTriple.mp (hf a b w₁)


-- @@ L242-253 verbatim
/-- Distributional trace independence is preserved by bind when the continuation
depends only on the trace (second component). -/
theorem probLeakFree_bind_of_trace_only
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂)
    {f : ω → OracleComp spec₁ (γ × ω')} {g : ω → OracleComp spec₂ (δ × ω')}
    (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    ProbLeakFree (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) := by
  rw [ProbLeakFree, snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalSPMF_bind, evalSPMF_bind, h]
  exact congrArg _ (funext hfg)


-- @@ L255-267 expanded
/-- Approximate trace independence is preserved by bind when the continuation depends
only on the trace and produces identical trace distributions. -/
theorem leakageBound_bind_of_trace_only [IsUniformSpec spec₁] [IsUniformSpec spec₂] {ε : ℝ}
    {δ ω' : Type} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {f : ω → OracleComp spec₁ (γ × ω')}
    {g : ω → OracleComp spec₂ (δ × ω')} (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    LeakageBound ε (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) :=
  by
  rw [LeakageBound, snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalSPMF_bind, evalSPMF_bind,
    show (fun w => evalSPMF (Prod.snd <$> f w)) = fun w => evalSPMF (Prod.snd <$> g w) from
      funext hfg]
  exact le_trans (SPMF.tvDist_bind_right_le _ _ _) h


-- @@ L269-269 verbatim
end OracleComp.Leakage
