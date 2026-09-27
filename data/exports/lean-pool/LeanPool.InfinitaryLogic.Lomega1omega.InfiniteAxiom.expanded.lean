/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Operations

-- @@ L9-21 verbatim
/-!
# The infiniteness axiom of `L_ω₁ω`

`L_ω₁ω` defines infiniteness, which first-order logic cannot: `infiniteAxiom` is the countable
conjunction of Mathlib's finitary "there are at least `n` elements" sentences, embedded along
`Sentence.toLω`, and `realize_infiniteAxiom` says a nonempty structure realizes it exactly when
its carrier is infinite.

This is the standard device for restricting attention to infinite models — in particular for
transferring a statement about **coded** countable structures (whose carrier is `ℕ`, hence
infinite) to a statement about arbitrary models of a sentence, where a finite model would
otherwise escape.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace FirstOrder.Language


-- @@ L27-27 verbatim
open FirstOrder Cardinal


-- @@ L29-29 verbatim
variable (L : Language.{0, 0})


-- @@ L31-34 verbatim
/-- **The infiniteness axiom**: the countable conjunction of the finitary sentences "there are
at least `n` elements". -/
def infiniteAxiom : L.Sentenceω :=
  BoundedFormulaω.iInf fun n => (Sentence.cardGe L n).toLω


-- @@ L36-36 verbatim
variable {L} {M : Type} [L.Structure M] [Nonempty M]


-- @@ L38-54 verbatim
/-- A nonempty structure realizes the infiniteness axiom exactly when it is infinite. -/
@[simp] theorem realize_infiniteAxiom :
    Sentenceω.Realize (infiniteAxiom L) M ↔ Infinite M := by
  rw [show Sentenceω.Realize (infiniteAxiom L) M ↔ ∀ n : ℕ, (M ⊨ Sentence.cardGe L n) from by
    simp only [infiniteAxiom, Sentenceω.realize_def, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun n => Sentence.realize_toLω _]
  simp only [Sentence.realize_cardGe]
  constructor
  · intro h
    by_contra hinf
    rw [not_infinite_iff_finite] at hinf
    have := Fintype.ofFinite M
    have hlt := h (Fintype.card M + 1)
    rw [Cardinal.mk_fintype] at hlt
    exact absurd (Nat.cast_le.mp hlt) (by omega)
  · intro _ n
    exact le_of_lt ((Cardinal.natCast_lt_aleph0 (n := n)).trans_le (Cardinal.aleph0_le_mk M))


-- @@ L56-56 verbatim
end FirstOrder.Language
