/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import FLT.Slop.PGL2.FiniteSubgroups.TameClassification
public import FLT.Slop.PGL2.FiniteSubgroups.WildClassification


-- @@ L11-34 verbatim
/-!
# Dickson's classification of the finite subgroups of `PGL₂(𝔽̄_p)`

The main theorem `Dickson.dickson_classification`: for `p` an odd prime, every finite
subgroup of `PGL₂(𝔽̄_p)` is one of:

* cyclic;
* dihedral of order `2n`, `n ≥ 2`;
* isomorphic to `A₄`, `S₄` or `A₅`;
* a semidirect product of an elementary abelian `p`-group by a cyclic group of order
  prime to `p`;
* isomorphic to `PSL₂(𝔽_{p^m})` or `PGL₂(𝔽_{p^m})` for some `m ≥ 1`.

This is the combination of the tame case (`Dickson.classification_tame_slop`, order
coprime to `p`) and the wild case (`Dickson.classification_wild_slop`, order divisible
by `p`).

This classification (due to Dickson, 1901) is used in the proof of Fermat's Last
Theorem to analyse the image of the mod-`p` Galois representations attached to the
Frey curve.
-/

/- The code in this file was ported from Duxing Yang's `DicksonClassification` project
and does not yet follow the mathlib style conventions enforced by the linters below. -/

-- @@ L35-35 verbatim
set_option linter.style.longLine false

-- @@ L36-36 verbatim
set_option linter.style.emptyLine false

-- @@ L37-37 verbatim
set_option linter.style.whitespace false

-- @@ L38-38 verbatim
set_option linter.style.show false

-- @@ L39-39 verbatim
set_option linter.style.openClassical false

-- @@ L40-40 verbatim
set_option linter.style.cdot false

-- @@ L41-41 verbatim
set_option linter.style.multiGoal false

-- @@ L42-42 verbatim
set_option linter.style.refine false

-- @@ L43-43 verbatim
set_option linter.style.induction false

-- @@ L44-44 verbatim
set_option linter.unusedFintypeInType false


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
open scoped Classical


-- @@ L50-50 verbatim
namespace Dickson


-- @@ L52-52 verbatim
variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]


-- @@ L54-83 verbatim
theorem dickson_classification (G : Subgroup (PGLOf (K p))) [Finite G] :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) := by
  by_cases hG_nontrivial : Nontrivial G
  · by_cases h_div : p ∣ Nat.card G
    · rcases classification_wild_slop p G h_div with h1 | h2 | h3 | ⟨_, h4⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h1
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h4
    · have : Fintype G := Fintype.ofFinite G
      rcases classification_tame_slop p G h_div hG_nontrivial with h1 | h2 | h3 | h4 | h5
      · exact Or.inl h1
      · exact Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inl h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl h4
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h5
  · have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontrivial
    exact Or.inl ⟨⟨1, fun x ↦ by rw [Subsingleton.elim x 1]; exact Subgroup.mem_zpowers 1⟩⟩


-- @@ L85-85 verbatim
end Dickson
