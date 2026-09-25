/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.EvalDist.Monad.Basic


-- @@ L10-26 verbatim
/-!
# Disagreement-Aware Additive Bind Bounds

A family of bind-bound lemmas charging an exceptional set ("disagreement") to its mass
plus per-point slack. They are the workhorses behind coupled game-hopping proofs that need
to bound `Pr[q | mx >>= my]` by `Pr[q | mx >>= oc]` plus a small additive term.

These statements are framed for any monad `m` with `[HasEvalSPMF m]`; the canonical
specialisation is `m = ProbComp`.

## Main results

* `probEvent_bind_le_add_of_disagree` — 2-way base case.
* `probEvent_bind_le_add_bad_of_disagree` — 3-way with bad-event side.
* `probEvent_bind_le_add_bad_of_disagree'` — 3-way with per-step bad term in the IH.
* `probEvent_bind_le_add_bad_disagree` — 4-way merge.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
universe u v


-- @@ L32-32 verbatim
open ENNReal OracleComp.EvalDist


-- @@ L34-35 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L37-60 expanded
/-- **Disagreement-aware additive bind bound.** If the disagreement set `D` has probability at
most `ε₁` under `mx`, and off `D` the continuation `my` is within `ε₂` of the reference
continuation `oc`, then `Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + ε₁ + ε₂`. The exceptional set `D`
is charged its full mass `ε₁`; everywhere else the per-point gap `ε₂` is paid. -/
lemma probEvent_bind_le_add_of_disagree {mx : m α} {my oc : α → m β} {q : β → Prop} {D : α → Prop}
    {ε₁ ε₂ : ℝ≥0∞} (hD : probEvent mx D ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x → probEvent (my x) q ≤ probEvent (oc x) q + ε₂) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q + ε₁ + ε₂ := by
  classical
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx (fun x => probEvent (oc x) q + (if D x then 1 else 0) + ε₂) :=
      by
      gcongr with x hx
      by_cases hDx : D x
      · simp only [if_pos hDx]
        exact probEvent_le_one.trans (le_add_right (le_add_left le_rfl))
      · simp only [if_neg hDx, add_zero]; exact h x hx hDx
    _ =
        expectedValue mx (fun x => probEvent (oc x) q) + probEvent mx D +
          expectedValue mx (fun _ => ε₂) :=
      by rw [expectedValue_add, expectedValue_add, expectedValue_ite_one]
    _ ≤ expectedValue mx (fun x => probEvent (oc x) q) + ε₁ + ε₂ :=
      by
      gcongr
      exact expectedValue_le_of_le mx fun _ => le_rfl


-- @@ L62-88 expanded
/-- **Three-way disagreement-aware additive bind bound (hop A).** A coupled three-world variant of
`probEvent_bind_le_add_of_disagree`: the three worlds share the sampling computation `mx`, and at
each shared sample `x`, off the disagreement set `D` the `my`-world is bounded by the `oc`-world
plus the per-step slack `ε`, while on `D` the `ob`-world (the bad world) already fires its event
`r` with probability `1`. The conclusion charges the disagreement to `Pr[r | mx >>= ob]`. -/
lemma probEvent_bind_le_add_bad_of_disagree {mx : m α} {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → probEvent (ob x) r = 1)
    (h : ∀ x ∈ support mx, ¬D x → probEvent (my x) q ≤ probEvent (oc x) q + ε) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q + probEvent (mx >>= ob) r + ε :=
  by
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue,
    probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx (fun x => probEvent (oc x) q + probEvent (ob x) r + ε) :=
      by
      gcongr with x hx
      by_cases hDx : D x
      · rw [hbad x hx hDx]
        exact probEvent_le_one.trans (le_add_right (le_add_left le_rfl))
      · exact (h x hx hDx).trans (add_le_add (le_add_right le_rfl) le_rfl)
    _ =
        expectedValue mx (fun x => probEvent (oc x) q) +
            expectedValue mx (fun x => probEvent (ob x) r) +
          expectedValue mx (fun _ => ε) :=
      by rw [expectedValue_add, expectedValue_add]
    _ ≤
        expectedValue mx (fun x => probEvent (oc x) q) +
            expectedValue mx (fun x => probEvent (ob x) r) +
          ε :=
      by
      gcongr
      exact expectedValue_le_of_le mx fun _ => le_rfl


-- @@ L90-117 expanded
/-- **Four-way disagreement-aware additive bind bound (hop A).** A strengthening of
`probEvent_bind_le_add_bad_of_disagree`: the per-step inductive hypothesis itself carries a
bad-event term, so off the disagreement set `D` the `my`-world is bounded by the `oc`-world plus the
*per-shared-sample* bad probability `Pr[r | ob x]` plus the slack `ε`. On `D` the `ob`-world already
fires `r` with probability `1`. Both cases are charged into the aggregate `Pr[r | mx >>= ob]`, so
the conclusion is the same shape as the three-way bound. -/
lemma probEvent_bind_le_add_bad_of_disagree' {mx : m α} {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ℝ≥0∞}
    (hbad : ∀ x ∈ support mx, D x → probEvent (ob x) r = 1)
    (h :
      ∀ x ∈ support mx, ¬D x → probEvent (my x) q ≤ probEvent (oc x) q + probEvent (ob x) r + ε) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q + probEvent (mx >>= ob) r + ε :=
  by
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue,
    probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx (fun x => probEvent (oc x) q + probEvent (ob x) r + ε) :=
      by
      gcongr with x hx
      by_cases hDx : D x
      · rw [hbad x hx hDx]
        exact probEvent_le_one.trans (le_add_right (le_add_left le_rfl))
      · exact h x hx hDx
    _ =
        expectedValue mx (fun x => probEvent (oc x) q) +
            expectedValue mx (fun x => probEvent (ob x) r) +
          expectedValue mx (fun _ => ε) :=
      by rw [expectedValue_add, expectedValue_add]
    _ ≤
        expectedValue mx (fun x => probEvent (oc x) q) +
            expectedValue mx (fun x => probEvent (ob x) r) +
          ε :=
      by
      gcongr
      exact expectedValue_le_of_le mx fun _ => le_rfl


-- @@ L119-147 expanded
/-- **Four-way disagreement+bad additive bind bound.** A merge of
`probEvent_bind_le_add_of_disagree` with the three-world `probEvent_bind_le_add_bad_of_disagree`:
the disagreement set `D` (a *table-level* exceptional set, not a bad event) is charged its full
mass `ε₁`; everywhere off `D` the `my`-world is bounded by the `oc`-world plus the per-shared-sample
bad probability `Pr[r | ob x]` plus the slack `ε₂`. -/
lemma probEvent_bind_le_add_bad_disagree {mx : m α} {my : α → m β} {oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε₁ ε₂ : ℝ≥0∞} (hD : probEvent mx D ≤ ε₁)
    (h :
      ∀ x ∈ support mx, ¬D x → probEvent (my x) q ≤ probEvent (oc x) q + probEvent (ob x) r + ε₂) :
    probEvent (mx >>= my) q ≤ probEvent (mx >>= oc) q + probEvent (mx >>= ob) r + ε₁ + ε₂ := by
  classical
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue,
    probEvent_bind_eq_expectedValue]
  calc
    expectedValue mx (fun x => probEvent (my x) q) ≤
        expectedValue mx
          (fun x => probEvent (oc x) q + probEvent (ob x) r + (if D x then 1 else 0) + ε₂) :=
      by
      gcongr with x hx
      by_cases hDx : D x
      · simp only [if_pos hDx]
        exact probEvent_le_one.trans (le_add_right (le_add_left le_rfl))
      · simp only [if_neg hDx, add_zero]; exact h x hx hDx
    _ =
        expectedValue mx (fun x => probEvent (oc x) q) +
              expectedValue mx (fun x => probEvent (ob x) r) +
            probEvent mx D +
          expectedValue mx (fun _ => ε₂) :=
      by rw [expectedValue_add, expectedValue_add, expectedValue_add, expectedValue_ite_one]
    _ ≤
        expectedValue mx (fun x => probEvent (oc x) q) +
              expectedValue mx (fun x => probEvent (ob x) r) +
            ε₁ +
          ε₂ :=
      by
      gcongr
      exact expectedValue_le_of_le mx fun _ => le_rfl

