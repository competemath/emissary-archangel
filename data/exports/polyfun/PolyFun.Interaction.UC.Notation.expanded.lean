/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.OpenSyntax.Expr


-- @@ L11-51 verbatim
/-!
# UC composition notation

Scoped notation for open-system boundaries and the free composition syntax.
All notation is scoped to `Interaction.UC`; use `open Interaction.UC`
to bring it into scope.

## Typeclasses

The notation is backed by three typeclasses (`HasPar`, `HasWire`, `HasPlug`)
with instances for `Raw`, `Expr`, and `Interp`. Each instance is accompanied
by a `@[simp]` bridge lemma that normalizes the typeclass method back to
the concrete operation, ensuring that existing simp lemmas (e.g.,
`interpret_par`, `interpret_wire`) continue to fire on notation-introduced
terms.

## Boundary-level

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `Δ₁ ⊗ᵇ Δ₂` | `PortBoundary.tensor Δ₁ Δ₂` | `\otimes ^b` |
| `Δᵛ` | `PortBoundary.swap Δ` (dual) | `\^v` |

## Expression-level

| Notation | Meaning | Precedence |
|----------|---------|------------|
| `e₁ ∥ e₂` | `HasPar.par e₁ e₂` (parallel) | 70, right |
| `e₁ ⊞ e₂` | `HasWire.wire e₁ e₂` (wire) | 65, right |
| `e ⊠ k` | `HasPlug.plug e k` (plug/close) | 60, right |

## Parsing rules

Precedence ensures natural parenthesization:
* `A ∥ B ∥ C` = `A ∥ (B ∥ C)` (right-associative)
* `A ∥ B ⊞ C` = `(A ∥ B) ⊞ C` (par binds tighter than wire)
* `A ⊞ B ⊠ C` = `(A ⊞ B) ⊠ C` (wire binds tighter than plug)
* `A ∥ B ⊞ C ∥ D ⊠ E` = `((A ∥ B) ⊞ (C ∥ D)) ⊠ E`
* `Γᵛ ⊗ᵇ Δ` = `tensor (swap Γ) Δ` (postfix `ᵛ` at max precedence)
* `(Δ₁ ⊗ᵇ Δ₂)ᵛ` = `swap (tensor Δ₁ Δ₂)` (parentheses required)
-/


-- @@ L53-53 verbatim
public section


-- @@ L55-55 verbatim
namespace Interaction.UC


-- @@ L57-57 verbatim
/-! ### Boundary-level notation -/


-- @@ L59-60 verbatim
/-- Tensor (parallel) of port boundaries: `Δ₁ ⊗ᵇ Δ₂`. -/
scoped infixr:70 " ⊗ᵇ " => PortBoundary.tensor


-- @@ L62-67 verbatim
/-- Dual (swap) of a port boundary: `Δᵛ` means `PortBoundary.swap Δ`.

The superscript v (typed `\^v`) visually suggests "flip" or "invert,"
matching the operation that swaps inputs and outputs. Avoids the
Mathlib-global `ᵒᵖ` (which denotes `Opposite`). -/
scoped notation:max Δ "ᵛ" => PortBoundary.swap Δ


-- @@ L69-69 verbatim
/-! ### Composition typeclasses -/


-- @@ L71-72 verbatim
/-- Parallel composition on boundary-indexed types. -/
class HasPar (F : PortBoundary → Type*) where
  
-- @@ L73-74 verbatim
/-- Place two boundary-indexed values side by side, tensoring their boundaries. -/
  par : {Δ₁ Δ₂ : PortBoundary} → F Δ₁ → F Δ₂ → F (PortBoundary.tensor Δ₁ Δ₂)


-- @@ L76-77 verbatim
/-- Wiring (partial internal connection) on boundary-indexed types. -/
class HasWire (F : PortBoundary → Type*) where
  
-- @@ L78-83 verbatim
/-- Connect the shared boundary `Γ` of two values internally, exposing only
  the remaining boundaries `Δ₁` and `Δ₂`. -/
  wire : {Δ₁ Γ Δ₂ : PortBoundary} →
    F (PortBoundary.tensor Δ₁ Γ) →
    F (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) →
    F (PortBoundary.tensor Δ₁ Δ₂)


-- @@ L85-86 verbatim
/-- Plugging (full closure) on boundary-indexed types. -/
class HasPlug (F : PortBoundary → Type*) where
  
-- @@ L87-90 verbatim
/-- Fully connect a value against its dual boundary, closing off both sides
  to leave the empty boundary. -/
  plug : {Δ : PortBoundary} →
    F Δ → F (PortBoundary.swap Δ) → F PortBoundary.empty


-- @@ L92-92 verbatim
/-! ### Notation -/


-- @@ L94-95 verbatim
/-- Parallel composition: `e₁ ∥ e₂`. -/
scoped infixr:70 " ∥ " => HasPar.par


-- @@ L97-98 verbatim
/-- Wiring: `e₁ ⊞ e₂`. -/
scoped infixr:65 " ⊞ " => HasWire.wire


-- @@ L100-101 verbatim
/-- Plug (full closure): `e ⊠ k`. -/
scoped infixr:60 " ⊠ " => HasPlug.plug


-- @@ L103-103 verbatim
/-! ### Instances and bridge lemmas for `Raw` -/


-- @@ L105-105 verbatim
namespace OpenSyntax.Raw


-- @@ L107-108 verbatim
instance {Atom : PortBoundary → Type*} : HasPar (Raw Atom) where
  par := Raw.par


-- @@ L110-111 verbatim
instance {Atom : PortBoundary → Type*} : HasWire (Raw Atom) where
  wire := Raw.wire


-- @@ L113-114 verbatim
instance {Atom : PortBoundary → Type*} : HasPlug (Raw Atom) where
  plug := Raw.plug


-- @@ L116-116 verbatim
variable {Atom : PortBoundary → Type*}

-- @@ L117-117 verbatim
variable {Δ₁ Δ₂ Γ : PortBoundary}


-- @@ L119-121 verbatim
@[simp]
theorem hasPar (e₁ : Raw Atom Δ₁) (e₂ : Raw Atom Δ₂) :
    HasPar.par e₁ e₂ = Raw.par e₁ e₂ := rfl


-- @@ L123-126 verbatim
@[simp]
theorem hasWire (e₁ : Raw Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Raw Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Raw.wire e₁ e₂ := rfl


-- @@ L128-131 verbatim
@[simp]
theorem hasPlug (e : Raw Atom Δ₁)
    (k : Raw Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Raw.plug e k := rfl


-- @@ L133-133 verbatim
end OpenSyntax.Raw


-- @@ L135-135 verbatim
/-! ### Instances and bridge lemmas for `Expr` -/


-- @@ L137-137 verbatim
namespace OpenSyntax.Expr


-- @@ L139-140 verbatim
instance {Atom : PortBoundary → Type*} : HasPar (Expr Atom) where
  par := Expr.par


-- @@ L142-143 verbatim
instance {Atom : PortBoundary → Type*} : HasWire (Expr Atom) where
  wire := Expr.wire


-- @@ L145-146 verbatim
instance {Atom : PortBoundary → Type*} : HasPlug (Expr Atom) where
  plug := Expr.plug


-- @@ L148-148 verbatim
variable {Atom : PortBoundary → Type*}

-- @@ L149-149 verbatim
variable {Δ₁ Δ₂ Γ : PortBoundary}


-- @@ L151-153 verbatim
@[simp]
theorem hasPar (e₁ : Expr Atom Δ₁) (e₂ : Expr Atom Δ₂) :
    HasPar.par e₁ e₂ = Expr.par e₁ e₂ := rfl


-- @@ L155-158 verbatim
@[simp]
theorem hasWire (e₁ : Expr Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Expr Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Expr.wire e₁ e₂ := rfl


-- @@ L160-163 verbatim
@[simp]
theorem hasPlug (e : Expr Atom Δ₁)
    (k : Expr Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Expr.plug e k := rfl


-- @@ L165-165 verbatim
end OpenSyntax.Expr


-- @@ L167-167 verbatim
/-! ### Instances and bridge lemmas for `Interp` -/


-- @@ L169-169 verbatim
namespace OpenSyntax.Interp


-- @@ L171-172 verbatim
instance {Atom : PortBoundary → Type*} : HasPar (Interp Atom) where
  par := Interp.par


-- @@ L174-175 verbatim
instance {Atom : PortBoundary → Type*} : HasWire (Interp Atom) where
  wire := Interp.wire


-- @@ L177-178 verbatim
instance {Atom : PortBoundary → Type*} : HasPlug (Interp Atom) where
  plug := Interp.plug


-- @@ L180-180 verbatim
variable {Atom : PortBoundary → Type*}

-- @@ L181-181 verbatim
variable {Δ₁ Δ₂ Γ : PortBoundary}


-- @@ L183-185 verbatim
@[simp]
theorem hasPar (e₁ : Interp Atom Δ₁) (e₂ : Interp Atom Δ₂) :
    HasPar.par e₁ e₂ = Interp.par e₁ e₂ := rfl


-- @@ L187-190 verbatim
@[simp]
theorem hasWire (e₁ : Interp Atom (PortBoundary.tensor Δ₁ Γ))
    (e₂ : Interp Atom (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    HasWire.wire e₁ e₂ = Interp.wire e₁ e₂ := rfl


-- @@ L192-195 verbatim
@[simp]
theorem hasPlug (e : Interp Atom Δ₁)
    (k : Interp Atom (PortBoundary.swap Δ₁)) :
    HasPlug.plug e k = Interp.plug e k := rfl


-- @@ L197-197 verbatim
end OpenSyntax.Interp


-- @@ L199-202 verbatim
/-! ### Verification

The following examples verify correct elaboration, precedence, and
that bridge lemmas fire correctly with `simp`. -/


-- @@ L204-204 verbatim
section Tests


-- @@ L206-206 verbatim
open Interaction.UC


-- @@ L208-208 verbatim
variable {Atom : PortBoundary → Type*}

-- @@ L209-211 verbatim
variable {Δ₁ Δ₂ Δ₃ Γ : PortBoundary}

-- Boundary notation

-- @@ L212-212 verbatim
example : Δ₁ ⊗ᵇ Δ₂ = PortBoundary.tensor Δ₁ Δ₂ := rfl

-- @@ L213-213 verbatim
example : Γᵛ = PortBoundary.swap Γ := rfl

-- @@ L214-214 verbatim
example : Γᵛ ⊗ᵇ Δ₂ = PortBoundary.tensor (PortBoundary.swap Γ) Δ₂ := rfl

-- @@ L215-217 verbatim
example : Δ₁ ⊗ᵇ Δ₂ᵛ = PortBoundary.tensor Δ₁ (PortBoundary.swap Δ₂) := rfl

-- Raw notation: bridge lemmas normalize to concrete constructors

-- @@ L218-219 verbatim
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Δ₂) :
    A ∥ B = OpenSyntax.Raw.par A B := by simp

-- @@ L220-222 verbatim
example (A : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Γ))
    (B : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂)) :
    A ⊞ B = OpenSyntax.Raw.wire A B := by simp

-- @@ L223-227 verbatim
example (A : OpenSyntax.Raw Atom Δ₁)
    (K : OpenSyntax.Raw Atom Δ₁ᵛ) :
    A ⊠ K = OpenSyntax.Raw.plug A K := by simp

-- Expr notation

-- @@ L228-231 verbatim
example (A : OpenSyntax.Expr Atom Δ₁) (B : OpenSyntax.Expr Atom Δ₂) :
    A ∥ B = OpenSyntax.Expr.par A B := by simp

-- Interp notation

-- @@ L232-235 verbatim
example (A : OpenSyntax.Interp Atom Δ₁) (B : OpenSyntax.Interp Atom Δ₂) :
    A ∥ B = OpenSyntax.Interp.par A B := by simp

-- Precedence: par (70) binds tighter than wire (65)

-- @@ L236-240 verbatim
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Γ)
    (C : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂)) :
    A ∥ B ⊞ C = (A ∥ B) ⊞ C := rfl

-- Precedence: wire (65) binds tighter than plug (60)

-- @@ L241-246 verbatim
example (A : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Γ))
    (B : OpenSyntax.Raw Atom (Γᵛ ⊗ᵇ Δ₂))
    (K : OpenSyntax.Raw Atom (Δ₁ ⊗ᵇ Δ₂)ᵛ) :
    A ⊞ B ⊠ K = (A ⊞ B) ⊠ K := rfl

-- Right-associativity

-- @@ L247-249 verbatim
example (A : OpenSyntax.Raw Atom Δ₁) (B : OpenSyntax.Raw Atom Δ₂)
    (C : OpenSyntax.Raw Atom Δ₃) :
    A ∥ B ∥ C = A ∥ (B ∥ C) := rfl


-- @@ L251-251 verbatim
end Tests


-- @@ L253-253 verbatim
end Interaction.UC
