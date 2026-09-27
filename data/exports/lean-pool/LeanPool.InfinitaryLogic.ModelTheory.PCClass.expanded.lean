/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Semantics


-- @@ L10-20 verbatim
/-!
# The abstract PC-class membership predicate (issue #10, Unit 4)

`PCMem g Θ M` — a structure `M` for the base language `L` is in the projective class of an
`L'`-sentence `Θ` along `g : L →ᴸ L'` iff **`M` itself** (same carrier) expands to an
`L'`-structure modelling `Θ`.  This is Marker's `PC_{ω₁ω}` notion (Corollary 4.22): membership
is existence of a *same-carrier* expansion, enforced here by `LHom.IsExpansionOn`.

Deliberately language-generic and free of any nonemptiness assumption; the López–Escobar
specialization (`baseGraphEmb`, code compatibility) lives in `Methods/LopezEscobar/PCMem.lean`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace FirstOrder.Language


-- @@ L26-26 verbatim
variable {L : Language.{u, v}} {L' : Language.{u', v'}}


-- @@ L28-31 verbatim
/-- **Projective-class membership**: `M` (as an `L`-structure) expands, on the same carrier, to
an `L'`-structure satisfying `Θ`.  No nonemptiness is built in. -/
def PCMem (g : L →ᴸ L') (Θ : L'.Sentenceω) (M : Type*) [L.Structure M] : Prop :=
  ∃ S' : L'.Structure M, @LHom.IsExpansionOn L L' g M _ S' ∧ @Sentenceω.Realize L' Θ M S'


-- @@ L33-33 verbatim
end FirstOrder.Language
