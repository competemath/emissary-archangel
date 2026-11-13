import Mathlib
import Submission.MorseLedgerGeometry
import Submission.SelectedDeltaTransport


-- @@ L5-13 verbatim
/-!
# Permuting geometric Morse ledgers

`selectedFrameLedger` uses a noncanonical finite enumeration of selected
orbit components.  Event geometry naturally produces equivalences of the
underlying component types, not equalities of those enumerations.  This file
provides the adapter: a component equivalence preserving every frame class
induces `List.Perm` of the resulting ledgers.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission

-- @@ L20-20 verbatim
namespace TamedField


-- @@ L22-22 verbatim
variable {n : ℕ}

-- @@ L23-23 verbatim
variable {X Y : FramedLevelSet n}

-- @@ L24-24 verbatim
variable (V : TamedField X) (W : TamedField Y)


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L28-41 verbatim
/-- The set-membership subtype used by `selectedFrameLedger` and the finite-set
membership subtype used by `SelectedDeltaTransport` are canonically
equivalent. -/
def selectedOrbitIndexEquivFinset (A : Set (Set E)) :
    V.SelectedOrbitIndex A ≃
      {O : V.OrbitIndex // O ∈ V.selectedOrbitFinset A} where
  toFun O := ⟨O.1, (V.mem_selectedOrbitFinset O.1).2 O.2⟩
  invFun O := ⟨O.1, (V.mem_selectedOrbitFinset O.1).1 O.2⟩
  left_inv O := by
    apply Subtype.ext
    rfl
  right_inv O := by
    apply Subtype.ext
    rfl


-- @@ L43-70 verbatim
/-- Removing the orbit set underlying a distinguished selected component is
the same as taking the type-theoretic complement of that component. -/
def selectedOrbitIndexSdiffSingletonEquiv
    (B : Set (Set E)) (new : V.SelectedOrbitIndex B) :
    V.SelectedOrbitIndex (B \ {((new.1 : V.OrbitIndex) : Set E)}) ≃
      {O : V.SelectedOrbitIndex B // O ≠ new} where
  toFun O := by
    refine ⟨⟨O.1, O.2.1⟩, ?_⟩
    intro hEq
    apply O.2.2
    rw [Set.mem_singleton_iff]
    exact congrArg (fun Q : V.SelectedOrbitIndex B =>
      ((Q.1 : V.OrbitIndex) : Set E)) hEq
  invFun O := by
    refine ⟨O.1.1, O.1.2, ?_⟩
    rw [Set.mem_singleton_iff]
    intro hsets
    apply O.2
    apply Subtype.ext
    apply Subtype.ext
    exact hsets
  left_inv O := by
    apply Subtype.ext
    rfl
  right_inv O := by
    apply Subtype.ext
    apply Subtype.ext
    rfl


-- @@ L72-85 verbatim
private theorem ofFn_perm_of_equiv
    {α : Type*} {p q : ℕ}
    (e : Fin p ≃ Fin q)
    (f : Fin p → α) (g : Fin q → α)
    (hfg : ∀ i, f i = g (e i)) :
    (List.ofFn f).Perm (List.ofFn g) := by
  have hpq : p = q := by
    simpa using Fintype.card_congr e
  subst q
  have hfun : f = g ∘ e := by
    funext i
    exact hfg i
  rw [hfun]
  simpa using Equiv.Perm.ofFn_comp_perm e g


-- @@ L87-98 verbatim
private theorem enumeratedValues_perm_of_equiv
    {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (g : β → γ)
    (hfg : ∀ a, f a = g (e a)) :
    (List.ofFn fun i : Fin (Fintype.card α) =>
      f ((Fintype.equivFin α).symm i)).Perm
    (List.ofFn fun i : Fin (Fintype.card β) =>
      g ((Fintype.equivFin β).symm i)) := by
  apply ofFn_perm_of_equiv
    ((Fintype.equivFin α).symm.trans (e.trans (Fintype.equivFin β)))
  intro i
  simpa using hfg ((Fintype.equivFin α).symm i)


-- @@ L100-126 verbatim
/-- Enumerating an `Option`-indexed finite family differs only by permutation
from putting the `none` value at the head and then enumerating all `some`
values. -/
private theorem enumeratedOptionValues_perm_cons
    {α γ : Type*} [Fintype α] (head : γ) (f : α → γ) :
    (List.ofFn fun i : Fin (Fintype.card (Option α)) =>
      (Fintype.equivFin (Option α)).symm i |>.elim head f).Perm
    (head :: List.ofFn fun i : Fin (Fintype.card α) =>
      f ((Fintype.equivFin α).symm i)) := by
  let eα := Fintype.equivFin α
  let eOption := Fintype.equivFin (Option α)
  let σ : Fin (Fintype.card (Option α)) ≃
      Fin (Fintype.card α + 1) :=
    eOption.symm.trans
      ((Equiv.optionCongr eα).trans (finSuccEquiv (Fintype.card α)).symm)
  let g : Fin (Fintype.card α + 1) → γ := fun i =>
    (Equiv.optionCongr eα.symm
      (finSuccEquiv (Fintype.card α) i)).elim head f
  have hperm := ofFn_perm_of_equiv σ
    (fun i : Fin (Fintype.card (Option α)) =>
      (eOption.symm i).elim head f) g (by
        intro i
        cases hO : eOption.symm i <;>
          simp [σ, g, hO, Equiv.optionCongr])
  refine hperm.trans (List.Perm.of_eq ?_)
  rw [List.ofFn_succ]
  congr 1


-- @@ L128-142 verbatim
/-- An equivalence of selected orbit components which preserves their frame
classes induces a permutation of the arbitrarily enumerated frame ledgers. -/
theorem selectedFrameLedger_perm_of_equiv
    (A B : Set (Set E))
    (e : V.SelectedOrbitIndex A ≃ W.SelectedOrbitIndex B)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1) :
    (V.selectedFrameLedger A).Perm (W.selectedFrameLedger B) := by
  classical
  unfold selectedFrameLedger
  let eV := Fintype.equivFin (V.SelectedOrbitIndex A)
  let eW := Fintype.equivFin (W.SelectedOrbitIndex B)
  apply ofFn_perm_of_equiv (eV.symm.trans (e.trans eW))
  intro i
  simpa [eV, eW] using hclass (eV.symm i)


-- @@ L144-180 verbatim
/-- If the components after an event are an `Option`-extension of the
components before it, the new component can be placed at the head of the
arbitrarily enumerated ledger.  This is the enumeration-independent adapter
needed by definite births; reversing the resulting permutation gives deaths. -/
theorem selectedFrameLedger_perm_cons_of_option_equiv
    (A B : Set (Set E))
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = 1)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    (W.selectedFrameLedger B).Perm (1 :: V.selectedFrameLedger A) := by
  classical
  let f : Option (V.SelectedOrbitIndex A) → ZMod 2 := fun O =>
    O.elim 1 (fun P => V.orbitFrameClass P.1)
  let g : W.SelectedOrbitIndex B → ZMod 2 := fun O =>
    W.orbitFrameClass O.1
  have hequiv :
      (List.ofFn fun i : Fin
          (Fintype.card (Option (V.SelectedOrbitIndex A))) =>
        f ((Fintype.equivFin (Option (V.SelectedOrbitIndex A))).symm i)).Perm
      (W.selectedFrameLedger B) := by
    unfold selectedFrameLedger
    apply enumeratedValues_perm_of_equiv e f g
    intro O
    cases O with
    | none => exact hnone.symm
    | some O => exact hsome O
  have hcons :
      (List.ofFn fun i : Fin
          (Fintype.card (Option (V.SelectedOrbitIndex A))) =>
        f ((Fintype.equivFin (Option (V.SelectedOrbitIndex A))).symm i)).Perm
      (1 :: V.selectedFrameLedger A) := by
    unfold selectedFrameLedger
    simpa [f] using enumeratedOptionValues_perm_cons
      (α := V.SelectedOrbitIndex A) (1 : ZMod 2)
      (fun O => V.orbitFrameClass O.1)
  exact hequiv.symm.trans hcons


-- @@ L182-196 verbatim
/-- A geometric definite birth whose component set is an `Option`-extension
of the preceding set gives an actual chronological ledger trace.  The first
step inserts the class-one component and the second step forgets the arbitrary
enumeration order. -/
theorem selectedFrameLedger_birthTrace_of_option_equiv
    (A B : Set (Set E))
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = 1)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    MorseLedgerTrace (V.selectedFrameLedger A) (W.selectedFrameLedger B) := by
  have hperm : (W.selectedFrameLedger B).Perm
      (1 :: V.selectedFrameLedger A) :=
    V.selectedFrameLedger_perm_cons_of_option_equiv W A B e hnone hsome
  exact .cons (.birth _) (.cons (.perm hperm.symm) (.refl _))


-- @@ L198-207 verbatim
/-- Reading the same definite-event component equivalence backwards gives
the corresponding death trace. -/
theorem selectedFrameLedger_deathTrace_of_option_equiv
    (A B : Set (Set E))
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = 1)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    MorseLedgerTrace (W.selectedFrameLedger B) (V.selectedFrameLedger A) :=
  (V.selectedFrameLedger_birthTrace_of_option_equiv W A B e hnone hsome).symm


-- @@ L209-228 verbatim
/-- A distinguished component together with an equivalence onto its
complement gives the head-insertion permutation used by both the chronological
trace and the index-aware event move. -/
theorem selectedFrameLedger_perm_cons_of_distinguished_equiv
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new})
    (hnew : W.orbitFrameClass new.1 = 1)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1.1) :
    (W.selectedFrameLedger B).Perm (1 :: V.selectedFrameLedger A) := by
  classical
  let eOption : Option (V.SelectedOrbitIndex A) ≃
      W.SelectedOrbitIndex B :=
    (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe new)
  apply V.selectedFrameLedger_perm_cons_of_option_equiv W A B eOption
  · simpa [eOption] using hnew
  · intro O
    simpa [eOption] using hclass O


-- @@ L230-245 verbatim
/-- It is often easier geometrically to identify one distinguished newborn
component and then match every old component with the complement of that
component.  This adapter turns exactly that data into the `Option`
equivalence required by the birth trace. -/
theorem selectedFrameLedger_birthTrace_of_distinguished_equiv
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new})
    (hnew : W.orbitFrameClass new.1 = 1)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1.1) :
    MorseLedgerTrace (V.selectedFrameLedger A) (W.selectedFrameLedger B) := by
  have hperm := V.selectedFrameLedger_perm_cons_of_distinguished_equiv W
    A B new e hnew hclass
  exact .cons (.birth _) (.cons (.perm hperm.symm) (.refl _))


-- @@ L247-259 verbatim
/-- The distinguished-component formulation read backwards is a death
trace. -/
theorem selectedFrameLedger_deathTrace_of_distinguished_equiv
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new})
    (hnew : W.orbitFrameClass new.1 = 1)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1.1) :
    MorseLedgerTrace (W.selectedFrameLedger B) (V.selectedFrameLedger A) :=
  (V.selectedFrameLedger_birthTrace_of_distinguished_equiv W A B new e
    hnew hclass).symm


-- @@ L261-261 verbatim
namespace SelectedDeltaTransport


-- @@ L263-270 verbatim
/-- A geometric selected-component transport induces the membership-subtype
equivalence used by `selectedFrameLedger`. -/
def selectedOrbitIndexEquiv
    {A B : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B) :
    V.SelectedOrbitIndex A ≃ W.SelectedOrbitIndex B :=
  (V.selectedOrbitIndexEquivFinset A).trans
    (T.orbitEquiv.trans (W.selectedOrbitIndexEquivFinset B).symm)


-- @@ L272-285 verbatim
/-- Preserving the framed contribution preserves the frame class itself,
because the common tangent contribution `+1` cancels in `ZMod 2`. -/
theorem orbitFrameClass_eq
    {A B : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B)
    (O : V.SelectedOrbitIndex A) :
    V.orbitFrameClass O.1 =
      W.orbitFrameClass ((selectedOrbitIndexEquiv V W T) O).1 := by
  have h := T.contribution_eq (V.selectedOrbitIndexEquivFinset A O)
  have h' : V.orbitFrameClass O.1 + 1 =
      W.orbitFrameClass ((selectedOrbitIndexEquiv V W T) O).1 + 1 := by
    simpa [TamedField.orbitContribution, selectedOrbitIndexEquiv,
      selectedOrbitIndexEquivFinset] using h
  exact add_right_cancel h'


-- @@ L287-294 verbatim
/-- Every selected geometric delta transport therefore permutes the concrete
enumerated frame ledgers. -/
theorem selectedFrameLedger_perm
    {A B : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B) :
    (V.selectedFrameLedger A).Perm (W.selectedFrameLedger B) :=
  V.selectedFrameLedger_perm_of_equiv W A B
    (selectedOrbitIndexEquiv V W T) (orbitFrameClass_eq V W T)


-- @@ L296-313 verbatim
/-- If the target family consists of one distinguished class-one component
and a transported complement, the transport directly gives the definite-event
head insertion permutation. -/
theorem selectedFrameLedger_perm_cons_of_distinguished_complement
    {A B : Set (Set E)}
    (new : W.SelectedOrbitIndex B)
    (T : V.SelectedDeltaTransport W A
      (B \ {((new.1 : W.OrbitIndex) : Set E)}))
    (hnew : W.orbitFrameClass new.1 = 1) :
    (W.selectedFrameLedger B).Perm (1 :: V.selectedFrameLedger A) := by
  let e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new} :=
    (selectedOrbitIndexEquiv V W T).trans
      (W.selectedOrbitIndexSdiffSingletonEquiv B new)
  apply V.selectedFrameLedger_perm_cons_of_distinguished_equiv W A B new e hnew
  intro O
  simpa [e, selectedOrbitIndexEquiv, selectedOrbitIndexSdiffSingletonEquiv]
    using orbitFrameClass_eq V W T O


-- @@ L315-315 verbatim
end SelectedDeltaTransport


-- @@ L317-317 verbatim
end TamedField

-- @@ L318-318 verbatim
end Submission
