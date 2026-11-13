import Mathlib
import Submission.MorseEventExcision


-- @@ L4-10 verbatim
/-!
# Constructors for selected component delta transport

`SelectedDeltaTransport` is the component-level input used by Morse event
excision.  This file supplies the categorical and restriction operations needed
to build those inputs from already available full `DeltaTransport`s.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open Set


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
variable {n : ℕ}


-- @@ L20-20 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L22-22 verbatim
namespace TamedField.SelectedDeltaTransport


-- @@ L24-24 verbatim
variable {X Y Z : FramedLevelSet n}

-- @@ L25-25 verbatim
variable {V : TamedField X} {W : TamedField Y} {U : TamedField Z}


-- @@ L27-48 verbatim
/-- Restrict a full component transport to corresponding selected families. -/
def ofDeltaTransport (T : V.DeltaTransport W)
    {A B : Set (Set E)}
    (hmem : ∀ O : V.OrbitIndex,
      (O : Set E) ∈ A ↔ ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∈ B) :
    V.SelectedDeltaTransport W A B where
  orbitEquiv := {
    toFun := fun O => ⟨T.orbitEquiv O.1, by
      rw [W.mem_selectedOrbitFinset]
      exact (hmem O.1).mp ((V.mem_selectedOrbitFinset O.1).mp O.2)⟩
    invFun := fun P => ⟨T.orbitEquiv.symm P.1, by
      rw [V.mem_selectedOrbitFinset]
      apply (hmem (T.orbitEquiv.symm P.1)).mpr
      simpa using (W.mem_selectedOrbitFinset P.1).mp P.2⟩
    left_inv := fun O => by
      apply Subtype.ext
      exact T.orbitEquiv.symm_apply_apply O.1
    right_inv := fun P => by
      apply Subtype.ext
      exact T.orbitEquiv.apply_symm_apply P.1
  }
  contribution_eq := fun O => T.contribution_eq O.1


-- @@ L50-54 verbatim
/-- Identity transport on a selected component family. -/
def refl (V : TamedField X) (A : Set (Set E)) :
    V.SelectedDeltaTransport V A A where
  orbitEquiv := Equiv.refl _
  contribution_eq := fun _ => rfl


-- @@ L56-64 verbatim
/-- Reverse a selected transport. -/
def symm {A B : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B) :
    W.SelectedDeltaTransport V B A where
  orbitEquiv := T.orbitEquiv.symm
  contribution_eq := by
    intro O
    have h := T.contribution_eq (T.orbitEquiv.symm O)
    simpa using h.symm


-- @@ L66-74 verbatim
/-- Compose two selected transports. -/
def trans {A B C : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B)
    (R : W.SelectedDeltaTransport U B C) :
    V.SelectedDeltaTransport U A C where
  orbitEquiv := T.orbitEquiv.trans R.orbitEquiv
  contribution_eq := by
    intro O
    exact (T.contribution_eq O).trans (R.contribution_eq (T.orbitEquiv O))


-- @@ L76-86 verbatim
/-- A full transport which respects both a containing family and a chosen local
subfamily automatically transports their set-theoretic complements. -/
def sdiffOfDeltaTransport (T : V.DeltaTransport W)
    {P Q A B : Set (Set E)}
    (hwhole : ∀ O : V.OrbitIndex,
      (O : Set E) ∈ P ↔ ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∈ Q)
    (hlocal : ∀ O : V.OrbitIndex,
      (O : Set E) ∈ A ↔ ((T.orbitEquiv O : W.OrbitIndex) : Set E) ∈ B) :
    V.SelectedDeltaTransport W (P \ A) (Q \ B) :=
  ofDeltaTransport T fun O => by
    rw [mem_sdiff, mem_sdiff, hwhole O, hlocal O]


-- @@ L88-92 verbatim
/-- Restricting a full transport to the complete orbit collections recovers a
selected transport with no membership side condition. -/
def univOfDeltaTransport (T : V.DeltaTransport W) :
    V.SelectedDeltaTransport W Set.univ Set.univ :=
  ofDeltaTransport T (fun _ => by simp)


-- @@ L94-94 verbatim
end TamedField.SelectedDeltaTransport


-- @@ L96-96 verbatim
end Submission
