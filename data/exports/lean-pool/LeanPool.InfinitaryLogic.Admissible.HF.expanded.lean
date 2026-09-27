/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Admissible.Fragment.Honest
public import LeanPool.InfinitaryLogic.Lomega1omega.Theory
public import LeanPool.InfinitaryLogic.Lomega1omega.FirstOrderImage
import Mathlib.ModelTheory.Satisfiability


-- @@ L13-38 verbatim
/-!
# The HF fragment (issue #18)

`L_HF = L_ωω`: the first-order image inside `Lω₁ω`, as an honest admissible fragment, plus its
compactness theorem derived from Mathlib.

**This is the regression oracle for the interface.**  Any proposed change to `AdmissibleFragment`
must keep all four conditions:

1. the underlying formulas are exactly the `toLω`-image (`sentence_slice_hfFragment`);
2. coded families reduce to finite ones — here, to none at all;
3. the compactness theorem is `finitaryFragment_compact`;
4. no adapter widens it back to all of `Lω₁ω`.

**Where the emptiness lives.**  `hfFamily.IsFamilyCode` is `False`.  Not the index type's
cardinality, and not `einf`'s `⊤`-padding, which is legitimate for a real infinitary code.  The
forbidden move is granting the certificate to a finite code and using padding to manufacture a
primitive `iInf`.

**Universes.**  The syntax layer and `finitaryFragment_compactIn` are universe-general; the latter
returns Mathlib's canonical model in `Type (max u v)`.  The compatibility theorem
`finitaryFragment_compact` retains its published universe-zero result type.

**Not built on the legacy structures.**  `AdmissibleFragmentCore.hf := Set.univ` is a quarantined
placeholder; nothing here uses it, and nothing here may be proved from it.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
namespace FirstOrder.Language


-- @@ L44-44 verbatim
universe u v w uCode uIndex


-- @@ L46-46 verbatim
variable {L : Language.{0, 0}}


-- @@ L48-50 verbatim
/-- The all-arity first-order image: every formula containing no infinitary node. -/
def hfSet (L : Language.{u, v}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {p | p.2.IsFirstOrder}


-- @@ L52-61 verbatim
/-- **The HF fragment.**  Each field is now one appeal to the first-order-image API: three
structural equations and the two negative facts.  Compare the five hand-rolled constructor
inversions this replaces. -/
def hfFragment (L : Language.{u, v}) : Fragment L where
  toSet := hfSet L
  imp_left_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).1
  imp_right_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).2
  all_mem h := BoundedFormulaω.isFirstOrder_all_iff.mp h
  iInf_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iInf _)
  iSup_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iSup _)


-- @@ L63-65 verbatim
/-- **The finitary fragment**: the image of first-order syntax in `Lω₁ω`.  This is `L_HF = L_ωω`. -/
def finitaryFragment (L : Language.{u, v}) : Set L.Sentenceω :=
  Set.range Sentence.toLω


-- @@ L67-71 verbatim
/-- The **full preimage theory** — every first-order sentence whose image lies in `T`, not one
chosen representative per member.  Choosing representatives would need `Classical.choice` and would
make the model correspondence direction-sensitive. -/
private def foTheory {L : Language.{u, v}} (T : Set L.Sentenceω) : L.Theory :=
  {φ₀ : L.Sentence | φ₀.toLω ∈ T}


-- @@ L73-84 verbatim
/-- **Model correspondence.**  For a theory inside the finitary fragment, models of the preimage
theory are exactly models of the original. -/
private theorem model_foTheory_iff {L : Language.{u, v}} {T : Set L.Sentenceω}
    (hT : T ⊆ finitaryFragment L) (M : Type w) [L.Structure M] [Nonempty M] :
    M ⊨ foTheory T ↔ Theoryω.Model T M := by
  constructor
  · intro hM φ hφ
    obtain ⟨φ₀, rfl⟩ := hT hφ
    exact (Sentence.realize_toLω φ₀).mpr (hM.realize_of_mem φ₀ hφ)
  · intro hM
    refine ⟨fun {φ₀} hφ₀ => ?_⟩
    exact (Sentence.realize_toLω φ₀).mp (hM _ hφ₀)


-- @@ L86-110 verbatim
/-- **Universe-general compactness for the finitary fragment**, derived from Mathlib's first-order
compactness.

No `compact` field is consulted: the infinitary finite-satisfiability hypothesis is pushed through
`toLω` to the preimage theory, Mathlib supplies its canonical model in `Type (max u v)`, and the
correspondence carries it back.  Finite-subtheory witnesses may live in any fixed `Type w`; their
universe is independent of the output universe. -/
private theorem finitaryFragment_compactIn {L : Language.{u, v}} {T : L.Theoryω}
    (hT : T ⊆ finitaryFragment L) (hfin : Theoryω.IsFinitelySatisfiableIn.{u, v, w} T) :
    Theoryω.IsSatisfiableIn.{u, v, max u v} T := by
  -- every finite subset of the preimage theory is satisfiable
  have hfs : (foTheory T).IsFinitelySatisfiable := by
    intro F₀ hF₀
    obtain ⟨M, instM, neM, hM⟩ :=
      hfin (Sentence.toLω '' (F₀ : Set L.Sentence))
        (by rintro _ ⟨φ₀, hφ₀, rfl⟩; exact hF₀ hφ₀)
        (F₀.finite_toSet.image _)
    let : L.Structure M := instM
    have := neM
    have : M ⊨ (↑F₀ : L.Theory) :=
      ⟨fun {φ₀} hφ₀ => (Sentence.realize_toLω φ₀).mp (hM _ ⟨φ₀, hφ₀, rfl⟩)⟩
    exact Theory.Model.isSatisfiable M
  -- Mathlib first-order compactness
  obtain ⟨M⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfs
  exact ⟨M, inferInstance, inferInstance, (model_foTheory_iff hT M).mp M.is_model⟩


-- @@ L112-117 verbatim
/-- **Universe-zero compatibility endpoint.**  This retains the published result type while the
underlying first-order argument is universe-general; use `finitaryFragment_compactIn` when the
language or resulting carrier lives above universe zero. -/
theorem finitaryFragment_compact {T : L.Theoryω} (hT : T ⊆ finitaryFragment L)
    (hfin : T.IsFinitelySatisfiable) : T.IsSatisfiable :=
  finitaryFragment_compactIn hT hfin


-- @@ L119-123 verbatim
/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in `IsFamilyCode`,
**not** in the index type's cardinality and **not** in `einf`'s padding. -/


-- @@ L125-129 verbatim
/-! ## Step 4 — the honest HF instance

Essentially a structure literal: the base is `hfFragment`, and both upward fields are closed by
certificate absurdity. That it *is* nearly definitional is the signal that the signature is
right. -/


-- @@ L131-135 verbatim
/-- **The HF admissible fragment.**  No adapter, no widening. -/
def hfAdmissibleFragment (L : Language.{0, 0}) : AdmissibleFragment (hfFamily L) where
  toFragment := hfFragment L
  iInf_coded_mem := fun F _ => absurd F.infinitary not_false
  iSup_coded_mem := fun F _ => absurd F.infinitary not_false


-- @@ L137-150 verbatim
/-! ## The universe boundary

The structures are **language-indexed and universe-polymorphic**: `FamilyPresentation L` for
`L : Language.{u, v}`, so `FamilyPresentation L[[J]]` is well-formed for an arbitrary parameter
type `J`.  The probes below record that, at the signature level only — nothing here claims a
presentation for `L` lifts to one for `L[[J]]`.

The low-level semantic boundary is now explicit: `Theoryω.IsSatisfiableIn` selects the carrier
universe, and `finitaryFragment_compactIn` works for any language.  The ambient presentation API
still concludes the published universe-zero `Theoryω.IsSatisfiable`; that remaining boundary is
enforced separately by `scripts/check_admissible_universes.lean`.

Write the probe results as `Type _`, not `Type`: bare `Type` means `Type 0`, and that constraint
propagates *backward* onto the presentation argument. -/


-- @@ L152-152 verbatim
section UniverseGate


-- @@ L154-156 verbatim
/-- Arbitrary parameter type, arbitrary language universes: a coded family elaborates. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) (m : ℕ) : Type _ :=
  CodedFamily B m


-- @@ L158-160 verbatim
/-- …and so does the fragment wrapper. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) : Type _ :=
  AdmissibleFragment B


-- @@ L162-162 verbatim
end UniverseGate


-- @@ L164-164 verbatim
end FirstOrder.Language
