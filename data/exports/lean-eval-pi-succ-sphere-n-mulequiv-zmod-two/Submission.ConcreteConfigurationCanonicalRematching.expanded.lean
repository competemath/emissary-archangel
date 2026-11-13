import Mathlib
import Submission.AmbientAffineIsotopy
import Submission.ConcreteConfigurationConfigure
import Submission.ConcreteConfigurationMorseReduction
import Submission.ConcreteConfigurationBridgeExactReduction


-- @@ L7-22 verbatim
/-!
# Affine rematching of canonical round configurations

Canonical component placement puts every orbit on a unit circle in the first
two coordinate directions.  The only dependence on the source presentation is
the common base height `fiberBoundingRadius + 3`; orbit slots are then spaced by
four units in the third coordinate direction.

Consequently, once two finite orbit families are matched slot by slot, one
global translation in the third coordinate direction sends every canonical
circle, and hence the entire canonical target union, to its partner.  This file
packages that concrete ambient rematching.  It deliberately records sign and
frame-class compatibility separately: those are the exact remaining inputs for
the subsequent common-fiber gauge normalization and are not consequences of an
ambient translation.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function

-- @@ L29-29 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L31-31 verbatim
namespace Submission

-- @@ L32-32 verbatim
namespace ConcreteConfigurationCanonicalRematching


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L38-38 verbatim
variable {X Y : FramedLevelSet n}


-- @@ L40-46 verbatim
/-- A bijection of orbit components which preserves the canonical numerical
slot.  Equality is stated on the natural-number values so that the two `Fin`
codomains need not be definitionally identical. -/
structure SlotMatch (V : TamedField X) (W : TamedField Y) where
  orbitEquiv : V.OrbitIndex ≃ W.OrbitIndex
  slot_eq : ∀ O : V.OrbitIndex,
    (V.orbitSlot O : ℕ) = (W.orbitSlot (orbitEquiv O) : ℕ)


-- @@ L48-48 verbatim
namespace SlotMatch


-- @@ L50-50 verbatim
variable {V : TamedField X} {W : TamedField Y}


-- @@ L52-62 verbatim
/-- Equal component counts canonically produce a slot match: enumerate both
orbit types by `Fin` and identify equal numerical slots. -/
def ofCardEq
    (hcard : Fintype.card V.OrbitIndex = Fintype.card W.OrbitIndex) :
    SlotMatch V W where
  orbitEquiv :=
    (Fintype.equivFin V.OrbitIndex).trans
      ((finCongr hcard).trans (Fintype.equivFin W.OrbitIndex).symm)
  slot_eq := by
    intro O
    simp [TamedField.orbitSlot]


-- @@ L64-68 verbatim
/-- The translation vector correcting the source-dependent common base
height of the canonical circles. -/
def shift (h2 : 2 ≤ n) : E :=
  (Y.fiberBoundingRadius - X.fiberBoundingRadius) •
    CanonicalRoundOrbit.e₂ h2


-- @@ L70-73 verbatim
/-- The concrete ambient isotopy which performs the canonical rematching. -/
def ambient (_M : SlotMatch V W) (h2 : 2 ≤ n) :
    SmoothAmbientIsotopy n :=
  SmoothAmbientIsotopy.translation (shift (X := X) (Y := Y) h2)


-- @@ L75-84 verbatim
/-- At the endpoint, the affine slide sends the parametrized point of every
source circle to the same parametrized point of its matched target circle. -/
theorem ambient_circlePoint (M : SlotMatch V W) (h2 : 2 ≤ n)
    (O : V.OrbitIndex) (a : AddCircle (1 : ℝ)) :
    (M.ambient h2).forward 1 (CanonicalRoundOrbit.circlePoint V h2 O a) =
      CanonicalRoundOrbit.circlePoint W h2 (M.orbitEquiv O) a := by
  rw [ambient, SmoothAmbientIsotopy.translation_forward_endpoint]
  unfold shift CanonicalRoundOrbit.circlePoint CanonicalRoundOrbit.center
  rw [M.slot_eq O]
  module


-- @@ L86-98 verbatim
/-- The endpoint translation sends each canonical circle exactly to its
slot-matched target circle. -/
theorem ambient_target (M : SlotMatch V W) (h2 : 2 ≤ n)
    (O : V.OrbitIndex) :
    (M.ambient h2).forward 1 '' CanonicalRoundOrbit.target V h2 O =
      CanonicalRoundOrbit.target W h2 (M.orbitEquiv O) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (M.ambient_circlePoint h2 O a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨CanonicalRoundOrbit.circlePoint V h2 O a, ⟨a, rfl⟩,
      M.ambient_circlePoint h2 O a⟩


-- @@ L100-126 verbatim
/-- One global translation sends the complete canonical source union exactly
to the complete canonical target union. -/
theorem ambient_targetUnion (M : SlotMatch V W) (h2 : 2 ≤ n) :
    (M.ambient h2).forward 1 '' CanonicalRoundOrbit.targetUnion V h2 =
      CanonicalRoundOrbit.targetUnion W h2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [CanonicalRoundOrbit.targetUnion] at hy ⊢
    obtain ⟨O, hyO⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨M.orbitEquiv O, ?_⟩
    have himage : (M.ambient h2).forward 1 y ∈
        (M.ambient h2).forward 1 '' CanonicalRoundOrbit.target V h2 O :=
      ⟨y, hyO, rfl⟩
    rwa [M.ambient_target h2 O] at himage
  · intro hx
    rw [CanonicalRoundOrbit.targetUnion] at hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    let O : V.OrbitIndex := M.orbitEquiv.symm P
    have hxP' : x ∈ CanonicalRoundOrbit.target W h2 (M.orbitEquiv O) := by
      simpa [O] using hxP
    rw [← M.ambient_target h2 O] at hxP'
    obtain ⟨y, hy, hyx⟩ := hxP'
    refine ⟨y, ?_, hyx⟩
    rw [CanonicalRoundOrbit.targetUnion]
    exact Set.mem_iUnion.mpr ⟨O, hy⟩


-- @@ L128-136 verbatim
/-- If a framed presentation already has the first canonical target union as
its fiber, pulling it through the affine slide gives the second canonical
target union literally. -/
theorem pullback_fiber_eq_targetUnion (M : SlotMatch V W) (h2 : 2 ≤ n)
    (Z : FramedLevelSet n)
    (hZ : Z.fiber = CanonicalRoundOrbit.targetUnion V h2) :
    ((M.ambient h2).pullback Z).fiber =
      CanonicalRoundOrbit.targetUnion W h2 := by
  rw [SmoothAmbientIsotopy.pullback_fiber, hZ, M.ambient_targetUnion h2]


-- @@ L138-138 verbatim
end SlotMatch


-- @@ L140-140 verbatim
/-! ## Recovering the component count from the signed ledgers -/


-- @@ L142-142 verbatim
namespace SignedOrbitCount


-- @@ L144-144 verbatim
variable (S : FiberSign X) (V : TamedField X)


-- @@ L146-152 verbatim
/-- Positive selected components are the subtype on which the sign at the
canonical orbit representative is positive. -/
def positiveSelectedEquiv :
    V.SelectedOrbitIndex (S.positiveOrbitCollection V) ≃
      {O : V.OrbitIndex // 0 < S (V.orbitPoint O)} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun O =>
    S.mem_positiveOrbitCollection_iff V O


-- @@ L154-168 verbatim
/-- Negative selected components are the complementary subtype.  Nonvanishing
of a `FiberSign` on the fiber is exactly what rules out a third, zero case. -/
def negativeSelectedEquiv :
    V.SelectedOrbitIndex (S.neg.positiveOrbitCollection V) ≃
      {O : V.OrbitIndex // ¬ 0 < S (V.orbitPoint O)} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun O => by
    rw [S.neg.mem_positiveOrbitCollection_iff V O, FiberSign.neg_apply]
    have hne : S (V.orbitPoint O) ≠ 0 :=
      S.nonzero _ (V.orbitPoint_mem_fiber O)
    constructor
    · intro hneg hpos
      change 0 < S (V.orbitPoint O) at hpos
      linarith
    · intro hnpos
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hnpos) hne)


-- @@ L170-178 verbatim
/-- The positive and negative selected orbit types partition all orbit
components. -/
def selectedSumEquiv :
    (V.SelectedOrbitIndex (S.positiveOrbitCollection V) ⊕
      V.SelectedOrbitIndex (S.neg.positiveOrbitCollection V)) ≃
        V.OrbitIndex :=
  (Equiv.sumCongr (positiveSelectedEquiv S V)
      (negativeSelectedEquiv S V)).trans
    (Equiv.sumCompl fun O : V.OrbitIndex => 0 < S (V.orbitPoint O))


-- @@ L180-190 verbatim
/-- The total component count is the sum of positive and negative component
counts. -/
theorem card_orbitIndex_eq_selected_add :
    Nat.card V.OrbitIndex =
      Nat.card
          (V.SelectedOrbitIndex (S.positiveOrbitCollection V)) +
        Nat.card
          (V.SelectedOrbitIndex (S.neg.positiveOrbitCollection V)) := by
  have hcard := Nat.card_congr (selectedSumEquiv S V)
  rw [Nat.card_sum] at hcard
  exact hcard.symm


-- @@ L192-197 verbatim
/-- The concrete selected ledger has one entry per selected component. -/
theorem selectedFrameLedger_length (A : Set (Set E)) :
    (V.selectedFrameLedger A).length =
      Nat.card (V.SelectedOrbitIndex A) := by
  classical
  simp [TamedField.selectedFrameLedger, Nat.card_eq_fintype_card]


-- @@ L199-211 verbatim
/-- Therefore the total orbit count can be read directly from the lengths of
the positive and negative ledger lists. -/
theorem card_orbitIndex_eq_ledger_lengths :
    Fintype.card V.OrbitIndex =
      (S.positiveFrameLedger V).length +
        (S.neg.positiveFrameLedger V).length := by
  rw [← Nat.card_eq_fintype_card,
    card_orbitIndex_eq_selected_add S V]
  congr 1
  · exact (selectedFrameLedger_length V
      (S.positiveOrbitCollection V)).symm
  · exact (selectedFrameLedger_length V
      (S.neg.positiveOrbitCollection V)).symm


-- @@ L213-213 verbatim
end SignedOrbitCount


-- @@ L215-215 verbatim
namespace SlotMatch


-- @@ L217-217 verbatim
variable {V : TamedField X} {W : TamedField Y}


-- @@ L219-231 verbatim
/-- Literal equality of the positive and negative ledger lists forces equality
of the total component counts, hence supplies a concrete canonical slot match.
This constructor concerns the embedded circle union only; the ledger-induced
signed/frame permutation is retained separately below. -/
def ofSignedLedgerEq (S : FiberSign X) (T : FiberSign Y)
    (hpos : S.positiveFrameLedger V = T.positiveFrameLedger W)
    (hneg : S.neg.positiveFrameLedger V = T.neg.positiveFrameLedger W) :
    SlotMatch V W :=
  ofCardEq <| by
    rw [SignedOrbitCount.card_orbitIndex_eq_ledger_lengths S V,
      SignedOrbitCount.card_orbitIndex_eq_ledger_lengths T W]
    exact congrArg₂ Nat.add (congrArg List.length hpos)
      (congrArg List.length hneg)


-- @@ L233-233 verbatim
end SlotMatch


-- @@ L235-247 verbatim
/-- Slotwise sign and stable frame-class compatibility.  The affine theorem
above solves the embedded-fiber part; this is precisely the discrete data left
for a signed common-fiber frame gauge. -/
structure SignedFramedSlotMatch
    (V : TamedField X) (W : TamedField Y)
    (S : FiberSign X) (T : FiberSign Y)
    extends SlotMatch V W where
  positive_iff : ∀ O : V.OrbitIndex,
    (O : Set E) ∈ S.positiveOrbitCollection V ↔
      ((orbitEquiv O : W.OrbitIndex) : Set E) ∈
        T.positiveOrbitCollection W
  frameClass_eq : ∀ O : V.OrbitIndex,
    V.orbitFrameClass O = W.orbitFrameClass (orbitEquiv O)


-- @@ L249-249 verbatim
/-! ## A directly usable post-placement normalization constructor -/


-- @@ L251-251 verbatim
namespace PlacedNormalization


-- @@ L253-253 verbatim
open ConcreteConfigurationMorseReduction


-- @@ L255-255 verbatim
variable (m : ℕ)


-- @@ L257-257 verbatim
local notation "Eₘ" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L259-259 verbatim
variable {X₀ X₁ : FramedLevelSet (m + 2)}

-- @@ L260-260 verbatim
variable (P₀ : ConcreteConfigurationConfigure.ComponentPlacementData m X₀)

-- @@ L261-261 verbatim
variable (P₁ : ConcreteConfigurationConfigure.ComponentPlacementData m X₁)

-- @@ L262-262 verbatim
variable (S₀ : FiberSign X₀) (S₁ : FiberSign X₁)


-- @@ L264-265 verbatim
local notation "V₀" =>
  (ConcreteConfigurationConfigure.field m : TamedField X₀)

-- @@ L266-267 verbatim
local notation "V₁" =>
  (ConcreteConfigurationConfigure.field m : TamedField X₁)

-- @@ L268-268 verbatim
local notation "h2" => ConcreteConfigurationConfigure.dimension_ge_two m


-- @@ L270-278 verbatim
/-- Equality of both concrete signed ledgers is the finite hypothesis needed
to put the two placed configurations on the same canonical circle union. -/
structure LedgerMatch where
  positive_eq :
    ConcreteConfigurationConfigure.positiveLedger m S₀ =
      ConcreteConfigurationConfigure.positiveLedger m S₁
  negative_eq :
    ConcreteConfigurationConfigure.negativeLedger m S₀ =
      ConcreteConfigurationConfigure.negativeLedger m S₁


-- @@ L280-280 verbatim
namespace LedgerMatch


-- @@ L282-282 verbatim
variable {m P₀ P₁ S₀ S₁}


-- @@ L284-288 verbatim
/-- The ledger equalities determine equality of total component counts and
hence the canonical numerical slot matching. -/
def slotMatch (L : LedgerMatch m S₀ S₁) :
    SlotMatch V₀ V₁ :=
  SlotMatch.ofSignedLedgerEq S₀ S₁ L.positive_eq L.negative_eq


-- @@ L290-293 verbatim
/-- The resulting concrete affine slide. -/
def ambient (L : LedgerMatch m S₀ S₁) :
    SmoothAmbientIsotopy (m + 2) :=
  L.slotMatch.ambient h2


-- @@ L295-305 verbatim
/-- After the affine slide, the first placed presentation and the second
placed presentation have literally the same zero fiber. -/
theorem ambient_pullback_fiber_eq
    (L : LedgerMatch m S₀ S₁) :
    (L.ambient.pullback P₀.endpointX).fiber = P₁.endpointX.fiber := by
  calc
    (L.ambient.pullback P₀.endpointX).fiber =
        CanonicalRoundOrbit.targetUnion V₁ h2 :=
      L.slotMatch.pullback_fiber_eq_targetUnion h2 P₀.endpointX
        P₀.endpoint_fiber
    _ = P₁.endpointX.fiber := P₁.endpoint_fiber.symm


-- @@ L307-307 verbatim
end LedgerMatch


-- @@ L309-320 verbatim
/-- Once the automatic affine fiber rematching is fixed, only a common-fiber
defining-map homotopy and the transported sign comparison remain.  This is a
strictly smaller and directly usable form of `NormalizationData`: its ambient
field is no longer an input. -/
structure CommonFiberData
    (L : LedgerMatch m S₀ S₁) where
  homotopy : DefiningMapHomotopy
    (L.ambient.pullback P₀.endpointX) P₁.endpointX
  signPattern : ∀ x ∈ P₁.endpointX.fiber,
    (0 < (L.ambient.pullbackSign (P₀.endpointSign S₀)).restrict
        homotopy.fiber_subset x ↔
      0 < P₁.endpointSign S₁ x)


-- @@ L322-322 verbatim
namespace CommonFiberData


-- @@ L324-324 verbatim
variable {m P₀ P₁ S₀ S₁}

-- @@ L325-325 verbatim
variable {L : LedgerMatch m S₀ S₁}


-- @@ L327-333 verbatim
/-- Insert the automatic affine stage into the production normalization
interface. -/
def toNormalizationData (D : CommonFiberData m P₀ P₁ S₀ S₁ L) :
    NormalizationData (P₀.endpointSign S₀) (P₁.endpointSign S₁) where
  ambient := L.ambient
  homotopy := D.homotopy
  signPattern := D.signPattern


-- @@ L335-341 verbatim
/-- The rematching plus a common-fiber gauge therefore supplies an actual
signed framed cobordism between the two placed endpoints. -/
theorem nonempty_cobordism
    (D : CommonFiberData m P₀ P₁ S₀ S₁ L) :
    Nonempty (SignedFramedLevelCobordism
      (P₀.endpointSign S₀) (P₁.endpointSign S₁)) :=
  D.toNormalizationData.nonempty_cobordism


-- @@ L343-343 verbatim
end CommonFiberData


-- @@ L345-345 verbatim
end PlacedNormalization


-- @@ L347-347 verbatim
/-! ## Entry constructor for an exact compact plan -/


-- @@ L349-349 verbatim
namespace ExactPlanEntry


-- @@ L351-351 verbatim
open ConcreteConfigurationBridgeExactReduction

-- @@ L352-352 verbatim
open ConcreteConfigurationMorseReduction

-- @@ L353-353 verbatim
open PlacedNormalization


-- @@ L355-355 verbatim
variable {m : ℕ} {z : StableSpherePi (m + 2)}

-- @@ L356-356 verbatim
variable (B : BridgeData (m + 2) z) (h3 : 3 ≤ m + 2)

-- @@ L357-357 verbatim
variable (Z : ZeroPairSaddleModel m)

-- @@ L358-360 verbatim
variable (D : DeterministicPlan m Z
  (ConcreteConfigurationConfigure.positiveLedger m B.fiberSign)
  (ConcreteConfigurationConfigure.negativeLedger m B.fiberSign))


-- @@ L362-366 verbatim
/-- Apply the same unconditional component-placement theorem to the literal
flat source of the exact plan. -/
abbrev planPlacement :
    ConcreteConfigurationConfigure.ComponentPlacementData m D.source.X :=
  ConcreteConfigurationConfigure.componentPlacementData m h3


-- @@ L368-375 verbatim
/-- Concrete input for entering an exact plan after placing both its bridge
source and its literal flat source.  The affine ambient stage is generated
from the signed ledgers; only the common-fiber frame/sign datum remains. -/
structure Data where
  ledgerMatch : LedgerMatch m B.fiberSign D.source.sign
  commonFiber : CommonFiberData m
    (canonicalPlacement m B h3) (planPlacement B h3 Z D)
    B.fiberSign D.source.sign ledgerMatch


-- @@ L377-377 verbatim
namespace Data


-- @@ L379-379 verbatim
variable {B h3 Z D}


-- @@ L381-390 verbatim
/-- Canonical rematching, followed by reversing the plan-source placement,
gives the exact post-placement connector required by `PlacedData`. -/
theorem nonempty_afterPlacement (A : Data B h3 Z D) :
    Nonempty (SignedFramedLevelCobordism
      ((canonicalPlacement m B h3).endpointSign B.fiberSign)
      D.source.sign) :=
  SignedFramedLevelCobordism.nonempty_trans
    A.commonFiber.nonempty_cobordism
    (SignedFramedLevelCobordism.nonempty_symm
      ⟨(planPlacement B h3 Z D).signedCobordism D.source.sign⟩)


-- @@ L392-397 verbatim
/-- Feed the two-sided placement/rematching construction directly into the
weakened exact-reduction bridge interface. -/
def toPlacedData (A : Data B h3 Z D) : PlacedData m B h3 where
  zeroPairSaddle := Z
  plan := D
  afterPlacement := A.nonempty_afterPlacement


-- @@ L399-399 verbatim
end Data


-- @@ L401-401 verbatim
end ExactPlanEntry


-- @@ L403-403 verbatim
end ConcreteConfigurationCanonicalRematching

-- @@ L404-404 verbatim
end Submission
