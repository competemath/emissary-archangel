/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.OracleSpec
public import Cslib.Foundations.Data.PFunctor.Free

public import VCVio.ProgramLogic.Tactics.Relational


-- @@ L14-18 verbatim
/-!
# Derived Relational Tactic Examples

This file validates relational consequence, inlining, and `@[vcspec]` lookup.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open ENNReal OracleSpec OracleComp

-- @@ L23-23 verbatim
open OracleComp.ProgramLogic

-- @@ L24-24 verbatim
open OracleComp.ProgramLogic.Relational

-- @@ L25-25 verbatim
open Lean.Order

-- @@ L26-26 verbatim
open scoped OracleComp.ProgramLogic


-- @@ L28-28 verbatim
universe u


-- @@ L30-30 verbatim
variable {ι : Type u} {spec : OracleSpec ι}

-- @@ L31-31 verbatim
variable [IsUniformSpec spec]

-- @@ L32-32 verbatim
variable {α β γ : Type}


-- @@ L34-34 verbatim
/-! ## `rel_conseq` / `rel_inline` / `rel_dist` -/


-- @@ L36-43 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} {R R' : RelPost α β}
    (h : Relational.RelTriple oa ob R) (hpost : ∀ x y, R x y → R' x y) :
    Relational.RelTriple oa ob R' :=
  by
  apply OracleComp.ProgramLogic.Relational.relTriple_post_mono
  · exact h
  · exact hpost


-- @@ L45-52 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} {R R' : RelPost α β}
    (h : Relational.RelTriple oa ob R) (hpost : ∀ x y, R x y → R' x y) :
    Relational.RelTriple oa ob R' :=
  by
  refine OracleComp.ProgramLogic.Relational.relTriple_post_mono (R := R) ?_ ?_
  · exact h
  · exact hpost


-- @@ L54-54 verbatim
private def inlineId (oa : OracleComp spec α) : OracleComp spec α := oa


-- @@ L56-58 expanded
example (oa : OracleComp spec α) : Relational.RelTriple (inlineId oa) oa (EqRel α) := by
  ( unfold inlineId
    try simp only [game_rule]
    try
      first
      | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
      | ( refine OracleComp.ProgramLogic.Relational.relTriple_post_const ?_
          intros; trivial)
      | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
      | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
      | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
      | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption))


-- @@ L60-60 verbatim
/-! ## Registered `@[vcspec]` relational theorems -/


-- @@ L62-62 verbatim
@[irreducible] def wrappedTrueLeft : OracleComp spec Bool := pure true

-- @@ L63-63 verbatim
@[irreducible] def wrappedTrueRight : OracleComp spec Bool := pure true


-- @@ L65-68 expanded
@[local vcspec]
theorem relTriple_wrappedTruePair :
    Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      (EqRel Bool) :=
  by
  unfold wrappedTrueLeft wrappedTrueRight
  rvcstep


-- @@ L70-72 expanded
example :
    Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      (EqRel Bool) :=
  by rvcstep


-- @@ L74-76 expanded
example :
    Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      fun _ _ => True :=
  by rvcstep


-- @@ L78-78 verbatim
@[irreducible] def wrappedAuxLeft : OracleComp spec Bool := pure true

-- @@ L79-79 verbatim
@[irreducible] def wrappedAuxRight : OracleComp spec Bool := pure true


-- @@ L81-84 expanded
@[local vcspec]
theorem relTriple_wrappedAuxPairStep (_haux : True) :
    Relational.RelTriple (wrappedAuxLeft (spec := spec)) (wrappedAuxRight (spec := spec))
      (EqRel Bool) :=
  by
  unfold wrappedAuxLeft wrappedAuxRight
  rvcstep


-- @@ L86-88 expanded
example :
    Relational.RelTriple (wrappedAuxLeft (spec := spec)) (wrappedAuxRight (spec := spec))
      (EqRel Bool) :=
  by rvcstep


-- @@ L90-92 expanded
example :
    Relational.RelTriple (wrappedAuxLeft (spec := spec)) (wrappedAuxRight (spec := spec)) fun _ _ =>
      True :=
  by rvcstep


-- @@ L94-100 expanded
@[local vcspec]
theorem rawRWP_wrappedTruePair :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.rwp (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
        (fun x y => if x = y then (1 : ℝ≥0∞) else 0) Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  unfold wrappedTrueLeft wrappedTrueRight
  rvcstep


-- @@ L102-108 expanded
example :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.rwp (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
        (fun _ _ => (1 : ℝ≥0∞)) Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  rvcstep
  intro a b
  split_ifs <;> simp


-- @@ L110-110 verbatim
@[irreducible] def rawAuxLeft : OracleComp spec Bool := pure true

-- @@ L111-111 verbatim
@[irreducible] def rawAuxRight : OracleComp spec Bool := pure true


-- @@ L113-119 expanded
@[local vcspec]
theorem rawRWP_wrappedAuxPairStep (_haux : True) :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.rwp (rawAuxLeft (spec := spec)) (rawAuxRight (spec := spec))
        (fun x y => if x = y then (1 : ℝ≥0∞) else 0) Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  unfold rawAuxLeft rawAuxRight
  rvcstep


-- @@ L121-127 expanded
example :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.rwp (rawAuxLeft (spec := spec)) (rawAuxRight (spec := spec)) (fun _ _ => (1 : ℝ≥0∞))
        Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  rvcstep
  intro a b
  split_ifs <;> simp


-- @@ L129-137 expanded
example :
    Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
      (EqRel Bool) :=
  by rvcstep with relTriple_wrappedTruePair


-- @@ L138-146 expanded
/-- info: Try this:

  [apply] rvcstep with relTriple_wrappedTruePair
-/
#guard_msgs in
  example :
      Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
        (EqRel Bool) :=
    by rvcstep?


-- @@ L148-164 expanded
/-- error: rvcstep: found a `RelTriple` goal, but no relational VCGen rule matched.

Registered `@[vcspec]` candidates: `relTriple_wrappedTruePair`
Try `rvcstep?` or `rvcstep with <theorem>` for an explicit replay.
Left side:
  wrappedTrueLeft
Right side:
  wrappedTrueRight
Postcondition:
  fun x x_1 ↦ False
Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step.
-/
#guard_msgs in
  example :
      Relational.RelTriple (wrappedTrueLeft (spec := spec)) (wrappedTrueRight (spec := spec))
        fun _ _ => False :=
    by rvcstep


-- @@ L166-186 expanded
/-- error: rvcstep using hf: the explicit hint did not match the current relational goal shape.
`using` is interpreted by goal shape as one of:
- bind cut relation (`α → β → Prop`)
- bind bijection coupling (`α → α`, on synchronized uniform/query binds)
- random/query bijection (`α → α`)
- `List.mapM` / `List.foldlM` input relation
- `simulateQ` state relation

Viable local `using` hints here: `S`
Goal:
  ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫
-/
#guard_msgs in
  example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
      {S : RelPost α α} {R : RelPost β γ} (hoa : Relational.RelTriple oa₁ oa₂ S)
      (hf : ∀ a₁ a₂, S a₁ a₂ → Relational.RelTriple (f₁ a₁) (f₂ a₂) R) :
      Relational.RelTriple (oa₁ >>= f₁) (oa₂ >>= f₂) R := by rvcstep using hf


-- @@ L188-188 verbatim
/-! ## Relational consequence close -/


-- @@ L190-201 expanded
/-- info: Try this:

  [apply] rvcfinish
-/
#guard_msgs in
  example {oa : OracleComp spec α} {ob : OracleComp spec β} {R R' : RelPost α β}
      (h : Relational.RelTriple oa ob R) (hpost : ∀ x y, R x y → R' x y) :
      Relational.RelTriple oa ob R' := by rvcstep?


-- @@ L203-208 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} {R R' : RelPost α β}
    (h : Relational.RelTriple oa ob R) (hpost : ∀ x y, R x y → R' x y) :
    Relational.RelTriple oa ob R' := by rvcgen!

