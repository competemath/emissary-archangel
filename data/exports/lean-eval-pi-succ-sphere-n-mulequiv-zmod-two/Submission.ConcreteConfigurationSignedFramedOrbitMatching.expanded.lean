import Mathlib
import Submission.ConcreteConfigurationCanonicalRematching


-- @@ L4-20 verbatim
/-!
# Signed and framed orbit matching from concrete ledger equality

`TamedField.selectedFrameLedger` enumerates selected orbit components by an
arbitrary `Fintype.equivFin`.  Literal equality of two such ledgers therefore
contains more information than equality of their lengths: matching equal list
positions gives an equivalence of the selected orbit types that preserves each
`orbitFrameClass`.

Applying this separately to the positive and negative ledgers and then using
the existing signed partition equivalence yields a full orbit equivalence.  It
preserves both the sign sheet and the stable frame class.  No geometric or
slot-order assumption is used.  In particular, this intentionally does not
claim the `slot_eq` required by `SignedFramedSlotMatch`; the arbitrary global
canonical slot enumeration is independent of the two signed ledger
enumerations.
-/


-- @@ L22-22 verbatim
set_option autoImplicit false


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-37 verbatim
private def enumeratedEquivOfListEq
    {alpha beta gamma : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → gamma) (g : beta → gamma)
    (h : (List.ofFn fun i : Fin (Fintype.card alpha) =>
      f ((Fintype.equivFin alpha).symm i)) =
      (List.ofFn fun i : Fin (Fintype.card beta) =>
      g ((Fintype.equivFin beta).symm i))) : alpha ≃ beta :=
  (Fintype.equivFin alpha).trans
    ((finCongr (by simpa using congrArg List.length h)).trans
      (Fintype.equivFin beta).symm)


-- @@ L39-63 verbatim
private theorem enumeratedEquivOfListEq_value
    {alpha beta gamma : Type*} [Fintype alpha] [Fintype beta]
    (f : alpha → gamma) (g : beta → gamma)
    (h : (List.ofFn fun i : Fin (Fintype.card alpha) =>
      f ((Fintype.equivFin alpha).symm i)) =
      (List.ofFn fun i : Fin (Fintype.card beta) =>
      g ((Fintype.equivFin beta).symm i)))
    (a : alpha) :
    f a = g (enumeratedEquivOfListEq f g h a) := by
  let p := Fintype.card alpha
  let q := Fintype.card beta
  let F : Fin p → gamma := fun i => f ((Fintype.equivFin alpha).symm i)
  let G : Fin q → gamma := fun i => g ((Fintype.equivFin beta).symm i)
  have hpq : p = q := by
    simpa [p, q, F, G] using congrArg List.length h
  have hsigma : (⟨p, F⟩ : Σ n, Fin n → gamma) = ⟨q, G⟩ := by
    apply List.ofFn_inj'.mp
    simpa [p, q, F, G] using h
  obtain ⟨hpq', hfun'⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp hsigma
  have hproof : hpq = hpq' := Subsingleton.elim _ _
  have hfun : F = G ∘ finCongr hpq := by
    rw [hproof]
    exact hfun'
  have ha := congrFun hfun (Fintype.equivFin alpha a)
  simpa [enumeratedEquivOfListEq, p, q, F, G] using ha


-- @@ L65-65 verbatim
namespace TamedField


-- @@ L67-67 verbatim
variable {n : ℕ}

-- @@ L68-68 verbatim
variable {X Y : FramedLevelSet n}

-- @@ L69-69 verbatim
variable (V : TamedField X) (W : TamedField Y)


-- @@ L71-71 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L73-83 verbatim
/-- Equal selected frame ledgers match the selected orbit components position
by position in their defining finite enumerations. -/
def selectedOrbitEquivOfFrameLedgerEq
    (A B : Set (Set E))
    (h : V.selectedFrameLedger A = W.selectedFrameLedger B) :
    V.SelectedOrbitIndex A ≃ W.SelectedOrbitIndex B := by
  classical
  exact enumeratedEquivOfListEq
    (fun O : V.SelectedOrbitIndex A => V.orbitFrameClass O.1)
    (fun O : W.SelectedOrbitIndex B => W.orbitFrameClass O.1)
    (by simpa only [selectedFrameLedger] using h)


-- @@ L85-97 verbatim
/-- The selected-orbit equivalence induced by ledger equality preserves the
frame class of every component, not merely their total delta. -/
theorem selectedOrbitEquivOfFrameLedgerEq_frameClass
    (A B : Set (Set E))
    (h : V.selectedFrameLedger A = W.selectedFrameLedger B)
    (O : V.SelectedOrbitIndex A) :
    V.orbitFrameClass O.1 =
      W.orbitFrameClass (V.selectedOrbitEquivOfFrameLedgerEq W A B h O).1 := by
  classical
  exact enumeratedEquivOfListEq_value
    (fun O : V.SelectedOrbitIndex A => V.orbitFrameClass O.1)
    (fun O : W.SelectedOrbitIndex B => W.orbitFrameClass O.1)
    (by simpa only [selectedFrameLedger] using h) O


-- @@ L99-99 verbatim
end TamedField


-- @@ L101-117 verbatim
/-- A full signed/framed matching, represented by its restrictions to the
positive and negative component types.  The unrestricted orbit equivalence is
obtained below from the signed partition of all components. -/
structure SignedFramedOrbitEquiv {n : ℕ}
    {X Y : FramedLevelSet n}
    (V : TamedField X) (W : TamedField Y)
    (S : FiberSign X) (T : FiberSign Y) where
  positiveEquiv :
    V.SelectedOrbitIndex (S.positiveOrbitCollection V) ≃
      W.SelectedOrbitIndex (T.positiveOrbitCollection W)
  negativeEquiv :
    V.SelectedOrbitIndex (S.neg.positiveOrbitCollection V) ≃
      W.SelectedOrbitIndex (T.neg.positiveOrbitCollection W)
  positive_frameClass : ∀ O,
    V.orbitFrameClass O.1 = W.orbitFrameClass (positiveEquiv O).1
  negative_frameClass : ∀ O,
    V.orbitFrameClass O.1 = W.orbitFrameClass (negativeEquiv O).1


-- @@ L119-119 verbatim
namespace SignedFramedOrbitEquiv


-- @@ L121-121 verbatim
variable {n : ℕ} {X Y : FramedLevelSet n}

-- @@ L122-122 verbatim
variable {V : TamedField X} {W : TamedField Y}

-- @@ L123-123 verbatim
variable {S : FiberSign X} {T : FiberSign Y}


-- @@ L125-146 verbatim
/-- Literal equality of the independently enumerated positive and negative
frame ledgers canonically matches components within each sign and frame class. -/
def ofSignedLedgerEq
    (hpos : S.positiveFrameLedger V = T.positiveFrameLedger W)
    (hneg : S.neg.positiveFrameLedger V = T.neg.positiveFrameLedger W) :
    SignedFramedOrbitEquiv V W S T where
  positiveEquiv :=
    V.selectedOrbitEquivOfFrameLedgerEq W
      (S.positiveOrbitCollection V) (T.positiveOrbitCollection W)
      (by simpa only [FiberSign.positiveFrameLedger] using hpos)
  negativeEquiv :=
    V.selectedOrbitEquivOfFrameLedgerEq W
      (S.neg.positiveOrbitCollection V) (T.neg.positiveOrbitCollection W)
      (by simpa only [FiberSign.positiveFrameLedger] using hneg)
  positive_frameClass O :=
    V.selectedOrbitEquivOfFrameLedgerEq_frameClass W
      (S.positiveOrbitCollection V) (T.positiveOrbitCollection W)
      (by simpa only [FiberSign.positiveFrameLedger] using hpos) O
  negative_frameClass O :=
    V.selectedOrbitEquivOfFrameLedgerEq_frameClass W
      (S.neg.positiveOrbitCollection V) (T.neg.positiveOrbitCollection W)
      (by simpa only [FiberSign.positiveFrameLedger] using hneg) O


-- @@ L148-154 verbatim
/-- Combine the two signed restrictions into an equivalence of all orbit
components. -/
def orbitEquiv (M : SignedFramedOrbitEquiv V W S T) :
    V.OrbitIndex ≃ W.OrbitIndex :=
  (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv S V).symm.trans
    ((Equiv.sumCongr M.positiveEquiv M.negativeEquiv).trans
      (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv T W))


-- @@ L156-164 verbatim
@[simp] theorem orbitEquiv_selectedSumEquiv_inl
    (M : SignedFramedOrbitEquiv V W S T)
    (P : V.SelectedOrbitIndex (S.positiveOrbitCollection V)) :
    M.orbitEquiv
        (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv
          S V (Sum.inl P)) =
      ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv
        T W (Sum.inl (M.positiveEquiv P)) := by
  simp [orbitEquiv]


-- @@ L166-174 verbatim
@[simp] theorem orbitEquiv_selectedSumEquiv_inr
    (M : SignedFramedOrbitEquiv V W S T)
    (P : V.SelectedOrbitIndex (S.neg.positiveOrbitCollection V)) :
    M.orbitEquiv
        (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv
          S V (Sum.inr P)) =
      ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv
        T W (Sum.inr (M.negativeEquiv P)) := by
  simp [orbitEquiv]


-- @@ L176-197 verbatim
/-- The full orbit equivalence preserves the stable frame class component by
component. -/
theorem orbitEquiv_frameClass (M : SignedFramedOrbitEquiv V W S T)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O = W.orbitFrameClass (M.orbitEquiv O) := by
  obtain ⟨Q, rfl⟩ :=
    (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv S V).surjective O
  cases Q with
  | inl P =>
      rw [M.orbitEquiv_selectedSumEquiv_inl P]
      simpa [
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.positiveSelectedEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.negativeSelectedEquiv]
        using M.positive_frameClass P
  | inr P =>
      rw [M.orbitEquiv_selectedSumEquiv_inr P]
      simpa [
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.positiveSelectedEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.negativeSelectedEquiv]
        using M.negative_frameClass P


-- @@ L199-207 verbatim
private theorem not_mem_positiveOrbitCollection_of_mem_neg
    (S : FiberSign X) (V : TamedField X) (O : V.OrbitIndex)
    (hneg : (O : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      S.neg.positiveOrbitCollection V) :
    (O : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∉
      S.positiveOrbitCollection V := by
  rw [S.neg.mem_positiveOrbitCollection_iff V O, FiberSign.neg_apply] at hneg
  rw [S.mem_positiveOrbitCollection_iff V O]
  linarith


-- @@ L209-250 verbatim
/-- The full orbit equivalence preserves the sign sheet of every component. -/
theorem orbitEquiv_positive_iff
    (M : SignedFramedOrbitEquiv V W S T) (O : V.OrbitIndex) :
    (O : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
        S.positiveOrbitCollection V ↔
      ((M.orbitEquiv O : W.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
          T.positiveOrbitCollection W := by
  obtain ⟨Q, rfl⟩ :=
    (ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv S V).surjective O
  cases Q with
  | inl P =>
      rw [M.orbitEquiv_selectedSumEquiv_inl P]
      constructor
      · intro _
        simpa [
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv,
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.positiveSelectedEquiv,
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.negativeSelectedEquiv]
          using (M.positiveEquiv P).2
      · intro _
        simpa [
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv,
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.positiveSelectedEquiv,
          ConcreteConfigurationCanonicalRematching.SignedOrbitCount.negativeSelectedEquiv]
          using P.2
  | inr P =>
      rw [M.orbitEquiv_selectedSumEquiv_inr P]
      have hsource :
          (P.1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∉
            S.positiveOrbitCollection V :=
        not_mem_positiveOrbitCollection_of_mem_neg S V P.1 P.2
      have htarget :
          ((M.negativeEquiv P).1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∉
            T.positiveOrbitCollection W :=
        not_mem_positiveOrbitCollection_of_mem_neg T W
          (M.negativeEquiv P).1 (M.negativeEquiv P).2
      simpa [
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.selectedSumEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.positiveSelectedEquiv,
        ConcreteConfigurationCanonicalRematching.SignedOrbitCount.negativeSelectedEquiv]
        using iff_of_false hsource htarget


-- @@ L252-257 verbatim
/-- Direct full-orbit API induced by equal positive and negative ledgers. -/
def orbitEquivOfSignedLedgerEq
    (hpos : S.positiveFrameLedger V = T.positiveFrameLedger W)
    (hneg : S.neg.positiveFrameLedger V = T.neg.positiveFrameLedger W) :
    V.OrbitIndex ≃ W.OrbitIndex :=
  (ofSignedLedgerEq hpos hneg).orbitEquiv


-- @@ L259-268 verbatim
theorem orbitEquivOfSignedLedgerEq_positive_iff
    (hpos : S.positiveFrameLedger V = T.positiveFrameLedger W)
    (hneg : S.neg.positiveFrameLedger V = T.neg.positiveFrameLedger W)
    (O : V.OrbitIndex) :
    (O : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
        S.positiveOrbitCollection V ↔
      ((orbitEquivOfSignedLedgerEq hpos hneg O : W.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
          T.positiveOrbitCollection W :=
  (ofSignedLedgerEq hpos hneg).orbitEquiv_positive_iff O


-- @@ L270-276 verbatim
theorem orbitEquivOfSignedLedgerEq_frameClass
    (hpos : S.positiveFrameLedger V = T.positiveFrameLedger W)
    (hneg : S.neg.positiveFrameLedger V = T.neg.positiveFrameLedger W)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      W.orbitFrameClass (orbitEquivOfSignedLedgerEq hpos hneg O) :=
  (ofSignedLedgerEq hpos hneg).orbitEquiv_frameClass O


-- @@ L278-278 verbatim
end SignedFramedOrbitEquiv


-- @@ L280-280 verbatim
end Submission
