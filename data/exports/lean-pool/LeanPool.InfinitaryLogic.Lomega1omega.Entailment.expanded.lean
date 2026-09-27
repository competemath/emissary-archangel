/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Theory

-- @@ L9-18 verbatim
/-!
# Semantic entailment for `L_{ω₁ω}` (issue #8 kernel step 1)

The frozen entailment convention of the Craig interpolation arc (`docs/craig-audit.md` §2):
set-level entailment is the primitive, carriers are `Type 0`, and models are **nonempty**
(standard model theory; forced here because the fresh-constant elimination arguments expand a
base structure by constant interpretations, which no empty carrier admits).

`Language.{0,0}` throughout, per the arc's D2 freeze.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace FirstOrder


-- @@ L24-24 verbatim
namespace Language


-- @@ L26-26 verbatim
variable {L : Language.{0, 0}}


-- @@ L28-31 verbatim
/-- **Semantic entailment from a theory** (the primitive form): every nonempty `Type 0` model
of `T` realizes `ψ`. -/
def Theoryω.Entails (T : L.Theoryω) (ψ : L.Sentenceω) : Prop :=
  ∀ (M : Type) [L.Structure M] [Nonempty M], T.Model M → Sentenceω.Realize ψ M


-- @@ L33-36 verbatim
/-- **Semantic entailment between sentences** — the headline convention, derived from the
set-level primitive. -/
def Sentenceω.Entails (φ ψ : L.Sentenceω) : Prop :=
  Theoryω.Entails {φ} ψ


-- @@ L38-38 verbatim
namespace Theoryω


-- @@ L40-40 verbatim
variable {T T' : L.Theoryω} {φ ψ χ : L.Sentenceω}


-- @@ L42-43 verbatim
theorem entails_of_mem (h : φ ∈ T) : T.Entails φ :=
  fun _M _ _ hM => hM φ h


-- @@ L45-47 verbatim
/-- Entailment is monotone in the theory. -/
theorem Entails.mono (h : T.Entails φ) (hT : T ⊆ T') : T'.Entails φ :=
  fun _M _ _ hM => h _M (hM.mono hT)


-- @@ L49-54 verbatim
/-- Cut: an entailed sentence can be added to the premises without changing entailments. -/
theorem Entails.cut (hφ : T.Entails φ) (hψ : (insert φ T).Entails ψ) : T.Entails ψ :=
  fun M _ _ hM => hψ M fun χ hχ => by
    rcases Set.mem_insert_iff.mp hχ with rfl | hχ
    · exact hφ M hM
    · exact hM χ hχ


-- @@ L56-56 verbatim
end Theoryω


-- @@ L58-58 verbatim
namespace Sentenceω


-- @@ L60-60 verbatim
variable {φ ψ χ : L.Sentenceω}


-- @@ L62-63 verbatim
theorem Entails.refl (φ : L.Sentenceω) : φ.Entails φ :=
  Theoryω.entails_of_mem rfl


-- @@ L65-72 verbatim
theorem entails_iff :
    φ.Entails ψ ↔ ∀ (M : Type) [L.Structure M] [Nonempty M],
      Sentenceω.Realize φ M → Sentenceω.Realize ψ M := by
  constructor
  · intro h M _ _ hφ
    exact h M fun χ hχ => Set.mem_singleton_iff.mp hχ ▸ hφ
  · intro h M _ _ hM
    exact h M (hM φ rfl)


-- @@ L74-75 verbatim
theorem Entails.trans (h₁ : φ.Entails ψ) (h₂ : ψ.Entails χ) : φ.Entails χ :=
  entails_iff.mpr fun M _ _ hφ => entails_iff.mp h₂ M (entails_iff.mp h₁ M hφ)


-- @@ L77-77 verbatim
end Sentenceω


-- @@ L79-79 verbatim
end Language


-- @@ L81-81 verbatim
end FirstOrder
