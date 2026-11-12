/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.FDRep.SimpleCharacters
import RepresentationTheory.Alignment.Attribute


-- @@ L10-15 verbatim
/-!
# Virtual representations

This module defines virtual complex representations of a finite group, together with their
coefficients, characters, and dimensions.
-/


-- @@ L17-17 verbatim
open CategoryTheory

-- @@ L18-18 verbatim
open RepresentationTheory.FDRep.SimpleCharacters


-- @@ L20-20 verbatim
namespace RepresentationTheory.VirtualRepresentations.Basic


-- @@ L22-26 verbatim
/-- The type of virtual complex representations of a finite group. -/
@[source_ref "Chapter5/Introduction_5.7" (role := supporting),
  source_ref "Chapter5/Definition5.7.1" (role := supporting)]
abbrev VirtualRepresentation (G : Type) [Group G] [Fintype G] : Type _ :=
  SimpleCharacter ℂ G →₀ ℤ


-- @@ L28-28 verbatim
namespace VirtualRepresentation


-- @@ L30-30 verbatim
variable {G : Type} [Group G] [Fintype G]


-- @@ L32-34 verbatim
/-- The integer coefficient of a simple representation in a virtual representation. -/
noncomputable def coeff (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) : ℤ :=
  V (SimpleCharacter.ofSimple W hW)


-- @@ L36-39 verbatim
/-- Isomorphic simple representations have equal coefficients in a virtual representation. -/
theorem coeff_eq_of_iso (V : VirtualRepresentation G) {W W' : FDRep ℂ G}
    (hW : Simple W) (hW' : Simple W') (e : W ≅ W') : V.coeff W hW = V.coeff W' hW' := by
  rw [coeff, coeff, SimpleCharacter.ofSimple_eq_of_iso hW hW' e]


-- @@ L41-44 verbatim
/-- The coefficient of a fixed representation is independent of the proof that it is simple. -/
theorem coeff_independent_of_simple (V : VirtualRepresentation G) {W : FDRep ℂ G}
    (hW hW' : Simple W) : V.coeff W hW = V.coeff W hW' :=
  V.coeff_eq_of_iso hW hW' (Iso.refl W)


-- @@ L46-49 verbatim
/-- Every simple coefficient of the zero virtual representation is zero. -/
@[simp]
theorem coeff_zero (W : FDRep ℂ G) (hW : Simple W) :
    (0 : VirtualRepresentation G).coeff W hW = 0 := rfl


-- @@ L51-54 verbatim
/-- The coefficient of a simple representation in a sum is the sum of its coefficients. -/
@[simp]
theorem coeff_add (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V + V').coeff W hW = V.coeff W hW + V'.coeff W hW := rfl


-- @@ L56-59 verbatim
/-- The coefficient in the negative of a virtual representation is the negative coefficient. -/
@[simp]
theorem coeff_neg (V : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (-V).coeff W hW = -V.coeff W hW := rfl


-- @@ L61-64 verbatim
/-- The coefficient in a difference is the difference of the coefficients. -/
@[simp]
theorem coeff_sub (V V' : VirtualRepresentation G) (W : FDRep ℂ G) (hW : Simple W) :
    (V - V').coeff W hW = V.coeff W hW - V'.coeff W hW := rfl


-- @@ L66-71 verbatim
/-- Two virtual representations are equal when all their simple coefficients agree. -/
theorem ext {V V' : VirtualRepresentation G}
    (h : ∀ (W : FDRep ℂ G) (hW : Simple W), V.coeff W hW = V'.coeff W hW) : V = V' := by
  ext c
  induction c using SimpleCharacter.induction_on with
  | _ W hW => exact h W hW


-- @@ L73-76 verbatim
/-- The virtual representation given by an integer multiple of a simple representation. -/
noncomputable def simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    VirtualRepresentation G :=
  Finsupp.single (SimpleCharacter.ofSimple W hW) n


-- @@ L78-81 verbatim
/-- Isomorphic simple representations have equal virtual integer multiples. -/
theorem simpleMultiple_eq_of_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    (e : W ≅ W') (n : ℤ) : simpleMultiple W hW n = simpleMultiple W' hW' n := by
  rw [simpleMultiple, simpleMultiple, SimpleCharacter.ofSimple_eq_of_iso hW hW' e]


-- @@ L83-86 verbatim
/-- The zero multiple of a simple representation is the zero virtual representation. -/
@[simp]
theorem simpleMultiple_zero (W : FDRep ℂ G) (hW : Simple W) : simpleMultiple W hW 0 = 0 :=
  Finsupp.single_zero _


-- @@ L88-93 verbatim
/-- The virtual representation attached to a sum of integers is the sum of the corresponding
simple multiples. -/
@[simp]
theorem simpleMultiple_add (W : FDRep ℂ G) (hW : Simple W) (m n : ℤ) :
    simpleMultiple W hW (m + n) = simpleMultiple W hW m + simpleMultiple W hW n :=
  Finsupp.single_add _ _ _


-- @@ L95-98 verbatim
/-- The coefficient of a simple representation in its own integer multiple is that integer. -/
theorem coeff_simpleMultiple_self (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (simpleMultiple W hW n).coeff W hW = n := by
  simp [coeff, simpleMultiple]


-- @@ L100-104 verbatim
/-- An integer multiple of a simple representation is zero exactly when the integer is zero. -/
@[simp]
theorem simpleMultiple_eq_zero_iff (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    simpleMultiple W hW n = 0 ↔ n = 0 :=
  Finsupp.single_eq_zero


-- @@ L106-112 verbatim
/-- Simple representations are isomorphic when equal nonzero integer multiples of them define
the same virtual representation. -/
theorem iso_of_simpleMultiple_eq {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : simpleMultiple W hW n = simpleMultiple W' hW' n) :
    Nonempty (W ≅ W') := by
  rw [← SimpleCharacter.ofSimple_eq_iff_nonempty_iso hW hW']
  simpa [simpleMultiple, Finsupp.single_eq_single_iff, hn] using h


-- @@ L114-118 verbatim
/-- Nonzero multiples of nonisomorphic simple representations are distinct. -/
theorem simpleMultiple_ne_of_not_iso {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    {n : ℤ} (hn : n ≠ 0) (h : IsEmpty (W ≅ W')) :
    simpleMultiple W hW n ≠ simpleMultiple W' hW' n :=
  fun heq => (iso_of_simpleMultiple_eq hW hW' hn heq).elim h.elim


-- @@ L120-124 verbatim
/-- An auxiliary theorem whose formal statement is unavailable. -/
theorem auxiliary {W W' : FDRep ℂ G} (hW : Simple W) (hW' : Simple W')
    (e : W ≅ W') : simpleMultiple W hW 1 + simpleMultiple W' hW' (-1) = 0 := by
  rw [simpleMultiple_eq_of_iso hW hW' e 1, simpleMultiple, simpleMultiple,
    ← Finsupp.single_add, add_neg_cancel, Finsupp.single_zero]


-- @@ L126-130 verbatim
/-- The additive homomorphism sending a virtual representation to its complex-valued character. -/
@[source_ref "Chapter5/Definition5.7.1" (role := supporting)]
noncomputable def character : VirtualRepresentation G →+ (G → ℂ) :=
  Finsupp.liftAddHom (α := SimpleCharacter ℂ G) (M := ℤ) (N := G → ℂ)
    fun c => zmultiplesHom (G → ℂ) (SimpleCharacter.value c)


-- @@ L132-139 verbatim
/-- The character value of a virtual representation is the finite sum of its coefficients times
the associated character values. -/
@[source_ref "Chapter5/Definition5.7.1" (role := primary)]
theorem character_apply (V : VirtualRepresentation G) (g : G) :
    character V g = ∑ c ∈ V.support, (V c : ℂ) * SimpleCharacter.value c g := by
  rw [character, Finsupp.liftAddHom_apply]
  simp only [Finsupp.sum, zmultiplesHom_apply, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply,
    Pi.intCast_apply]


-- @@ L141-144 verbatim
/-- The character of the zero virtual representation is zero. -/
@[simp]
theorem character_zero : character (0 : VirtualRepresentation G) = 0 :=
  map_zero _


-- @@ L146-150 verbatim
/-- The character of a sum of virtual representations is the sum of their characters. -/
@[simp]
theorem character_add (V V' : VirtualRepresentation G) :
    character (V + V') = character V + character V' :=
  map_add _ _ _


-- @@ L152-155 verbatim
/-- The character of the negative of a virtual representation is the negative of its character. -/
@[simp]
theorem character_neg (V : VirtualRepresentation G) : character (-V) = -character V :=
  map_neg _ _


-- @@ L157-162 verbatim
/-- The character of a difference of virtual representations is the difference of their
characters. -/
@[simp]
theorem character_sub (V V' : VirtualRepresentation G) :
    character (V - V') = character V - character V' :=
  map_sub _ _ _


-- @@ L164-169 verbatim
/-- The character of a single supported coefficient is the corresponding integer multiple of
its character. -/
@[simp, source_ref "Chapter5/Definition5.7.1" (role := supporting)]
theorem character_single (c : SimpleCharacter ℂ G) (n : ℤ) :
    character (Finsupp.single c n) = n • SimpleCharacter.value c :=
  Finsupp.liftAddHom_apply_single _ _ _


-- @@ L171-176 verbatim
/-- The character of an integer multiple of a simple representation is that integer times its
character. -/
@[simp]
theorem character_simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    character (simpleMultiple W hW n) = n • W.character := by
  rw [simpleMultiple, character_single, SimpleCharacter.value_ofSimple]


-- @@ L178-182 verbatim
/-- The virtual character associated with one copy of a simple representation is its ordinary
character. -/
theorem character_simple (W : FDRep ℂ G) (hW : Simple W) :
    character (simpleMultiple W hW 1) = W.character := by
  rw [character_simpleMultiple, one_smul]


-- @@ L184-186 verbatim
/-- The integer-valued dimension of a virtual representation. -/
noncomputable def dim (V : VirtualRepresentation G) : ℤ :=
  V.sum fun c n => n * (SimpleCharacter.dimension c : ℤ)


-- @@ L188-191 verbatim
/-- The dimension is the sum over the support of each coefficient times the corresponding
dimension. -/
theorem dim_eq_sum_support (V : VirtualRepresentation G) :
    V.dim = ∑ c ∈ V.support, V c * (SimpleCharacter.dimension c : ℤ) := rfl


-- @@ L193-197 verbatim
/-- A virtual character evaluated at the identity is the integer cast of its dimension. -/
theorem character_one (V : VirtualRepresentation G) : character V 1 = (V.dim : ℂ) := by
  rw [character_apply, dim_eq_sum_support]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by rw [SimpleCharacter.value_one]


-- @@ L199-202 verbatim
/-- The dimension of the zero virtual representation is zero. -/
@[simp]
theorem dim_zero : (0 : VirtualRepresentation G).dim = 0 :=
  Finsupp.sum_zero_index


-- @@ L204-210 verbatim
/-- The dimension of an integer multiple of a simple representation is the integer times its
finite dimension. -/
@[simp]
theorem dim_simpleMultiple (W : FDRep ℂ G) (hW : Simple W) (n : ℤ) :
    (simpleMultiple W hW n).dim = n * (Module.finrank ℂ W : ℤ) := by
  rw [dim, simpleMultiple, Finsupp.sum_single_index (by rw [zero_mul]),
    SimpleCharacter.dimension_ofSimple]


-- @@ L212-212 verbatim
end VirtualRepresentation


-- @@ L214-214 verbatim
end RepresentationTheory.VirtualRepresentations.Basic
