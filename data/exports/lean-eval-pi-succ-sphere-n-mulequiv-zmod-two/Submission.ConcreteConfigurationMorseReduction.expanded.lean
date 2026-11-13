import Mathlib
import Submission.CompactBirthConfiguration
import Submission.CompactSaddleConfiguration
import Submission.ConcreteConfigurationConfigure
import Submission.RelativeNormalizationProduct


-- @@ L7-29 verbatim
/-!
# Finite Morse reduction of a normalized circle configuration

This file implements the topology-changing field isolated by
`ConcreteConfigurationConfigure.Geometry.reduction` as a finite composite of
the compact definite and Cassini models.

Only two kinds of directed local events are needed.  A class-one circle is
removed by the compact death, while equal pairs are merged and the resulting
class-one circle is removed.  The existing Cassini model supplies
`1,1 -> 1`.  Its frame computation does not supply `0,0 -> 1`, so that one
spatially flat local saddle model is isolated below as the sole remaining
Morse-event input.  Deleting and pairing in this order reduces every ledger
to `MorseLedger.canonical L.delta`.

Each compact event is adjoined to an arbitrary separated flat tail by the
existing juxtaposition theorem.  The residual geometric inputs are stated as
relative ambient/defining-map normalizations from the current local state to
the exact compact-event endpoint.  They are required to be products on the
unchanged tail.  Thus the middle Morse event is concrete, not an existential
event contract, and all finite composition and parity bookkeeping are proved
here.
-/


-- @@ L31-31 verbatim
set_option autoImplicit false


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function

-- @@ L36-36 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L38-38 verbatim
namespace Submission

-- @@ L39-39 verbatim
namespace ConcreteConfigurationMorseReduction


-- @@ L41-41 verbatim
/-! ## Relative endpoint normalization -/


-- @@ L43-43 verbatim
variable {n : ℕ}


-- @@ L45-45 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L47-55 verbatim
/-- Concrete ambient-plus-common-fiber normalization between two prescribed
signed endpoints. -/
structure NormalizationData {X Y : FramedLevelSet n}
    (S : FiberSign X) (T : FiberSign Y) where
  ambient : SmoothAmbientIsotopy n
  homotopy : DefiningMapHomotopy (ambient.pullback X) Y
  signPattern : ∀ x ∈ Y.fiber,
    (0 < (ambient.pullbackSign S).restrict homotopy.fiber_subset x ↔
      0 < T x)


-- @@ L57-57 verbatim
namespace NormalizationData


-- @@ L59-59 verbatim
variable {X Y : FramedLevelSet n} {S : FiberSign X} {T : FiberSign Y}


-- @@ L61-66 verbatim
/-- The normalization primitive turns the endpoint data into an actual
signed cobordism. -/
def cobordism (D : NormalizationData S T) :
    SignedFramedLevelCobordism S T :=
  SmoothAmbientIsotopy.signedNormalizationCobordism
    D.ambient D.homotopy S T D.signPattern


-- @@ L68-70 verbatim
theorem nonempty_cobordism (D : NormalizationData S T) :
    Nonempty (SignedFramedLevelCobordism S T) :=
  ⟨D.cobordism⟩


-- @@ L72-72 verbatim
end NormalizationData


-- @@ L74-82 verbatim
/-- A normalization which is literally a product on an unchanged set `K`.
This is the local endpoint-matching contract used around every compact Morse
event. -/
structure RelativeNormalizationData {X Y : FramedLevelSet n}
    (S : FiberSign X) (T : FiberSign Y) (K : Set E)
    extends NormalizationData S T where
  ambient_fixed : ambient.FixedOn K
  homotopy_fixed : homotopy.FixedOn K X.g
  target_fixed : ∀ x ∈ K, T x = S x


-- @@ L84-84 verbatim
namespace RelativeNormalizationData


-- @@ L86-86 verbatim
variable {X Y : FramedLevelSet n} {S : FiberSign X} {T : FiberSign Y}


-- @@ L88-96 verbatim
/-- The glued normalization remains a product on the certified unchanged
set. -/
theorem cobordism_productOn
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (D : RelativeNormalizationData S T K) :
    D.toNormalizationData.cobordism.ProductOn K X.g S := by
  exact SmoothAmbientIsotopy.signedNormalizationCobordism_productOn
    (A := D.ambient) (D := D.homotopy) (S := S) (T := T)
    D.signPattern D.ambient_fixed D.homotopy_fixed D.target_fixed


-- @@ L98-98 verbatim
end RelativeNormalizationData


-- @@ L100-100 verbatim
/-! ## A spatially flat compact head event with a separated tail -/


-- @@ L102-115 verbatim
/-- A concrete signed local event, including the common spatial background
and the ball outside which it is flat. -/
structure SpatiallyFlatHeadMove (n : ℕ)
    (c : EuclideanSpace ℝ (Fin n)) where
  sourceX : FramedLevelSet n
  targetX : FramedLevelSet n
  sourceSign : FiberSign sourceX
  targetSign : FiberSign targetX
  cobordism : SignedFramedLevelCobordism sourceSign targetSign
  background_ne_zero : c ≠ 0
  center : EuclideanSpace ℝ (Fin (n + 1))
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  flatOutside : cobordism.SpatialFlatOutside c center radius


-- @@ L117-117 verbatim
namespace SpatiallyFlatHeadMove


-- @@ L119-119 verbatim
variable {c : EuclideanSpace ℝ (Fin n)}


-- @@ L121-138 verbatim
/-- Reverse a compact event without changing its spatial support. -/
def reverse (M : SpatiallyFlatHeadMove n c) :
    SpatiallyFlatHeadMove n c where
  sourceX := M.targetX
  targetX := M.sourceX
  sourceSign := M.targetSign
  targetSign := M.sourceSign
  cobordism := M.cobordism.reverse
  background_ne_zero := M.background_ne_zero
  center := M.center
  radius := M.radius
  radius_nonneg := M.radius_nonneg
  flatOutside := by
    intro v hv
    change M.cobordism.cobordism.G
      (reparamMap n (-1) 1 v) = c
    apply M.flatOutside
    simpa [reparamMap, initCLM_spaceTime] using hv


-- @@ L140-143 verbatim
/-- Place an unchanged flat configuration beyond the support ball. -/
def placedTail (M : SpatiallyFlatHeadMove n c)
    (A : FlatSignedConfiguration n c) : FlatSignedConfiguration n c :=
  FlatSignedConfiguration.placeAfterBound M.center M.radius A


-- @@ L145-151 verbatim
/-- The canonical placement leaves a unit separation gap. -/
theorem separated_placedTail (M : SpatiallyFlatHeadMove n c)
    (A : FlatSignedConfiguration n c) :
    M.radius + (M.placedTail A).radius <
      dist M.center (M.placedTail A).center :=
  FlatSignedConfiguration.separated_placeAfterBound
    M.center M.radius M.radius_nonneg A


-- @@ L153-162 verbatim
/-- Exact source sign of the compact head event with its unchanged tail. -/
def sourceWithTailSign (M : SpatiallyFlatHeadMove n c)
    (A : FlatSignedConfiguration n c) :
    FiberSign
      (M.sourceX.juxtapose (M.placedTail A).X M.background_ne_zero
        M.flatOutside.flatOutside_source (M.placedTail A).flatOutside
        (M.separated_placedTail A)) :=
  M.sourceSign.juxtapose (M.placedTail A).sign M.background_ne_zero
    M.flatOutside.flatOutside_source (M.placedTail A).flatOutside
    (M.separated_placedTail A)


-- @@ L164-173 verbatim
/-- Exact target sign of the compact head event with its unchanged tail. -/
def targetWithTailSign (M : SpatiallyFlatHeadMove n c)
    (A : FlatSignedConfiguration n c) :
    FiberSign
      (M.targetX.juxtapose (M.placedTail A).X M.background_ne_zero
        M.flatOutside.flatOutside_target (M.placedTail A).flatOutside
        (M.separated_placedTail A)) :=
  M.targetSign.juxtapose (M.placedTail A).sign M.background_ne_zero
    M.flatOutside.flatOutside_target (M.placedTail A).flatOutside
    (M.separated_placedTail A)


-- @@ L175-184 verbatim
/-- Juxtaposition supplies the actual compact event while carrying the tail
by a cylinder. -/
theorem nonempty_withTail (M : SpatiallyFlatHeadMove n c)
    (A : FlatSignedConfiguration n c) :
    Nonempty (SignedFramedLevelCobordism
      (M.sourceWithTailSign A) (M.targetWithTailSign A)) := by
  simpa [sourceWithTailSign, targetWithTailSign, placedTail] using
    (FlatSignedConfiguration.nonempty_headMove_juxtapose_tail
      M.cobordism M.background_ne_zero M.center M.radius M.radius_nonneg
      M.flatOutside A)


-- @@ L186-186 verbatim
end SpatiallyFlatHeadMove


-- @@ L188-188 verbatim
/-! ## The four concrete compact models -/


-- @@ L190-190 verbatim
variable (m : ℕ)


-- @@ L192-195 verbatim
/-- The common nonzero background of all compact models in dimension
`m + 2`. -/
abbrev compactBackground : EuclideanSpace ℝ (Fin (m + 2)) :=
  CompactBirth.background (m + 1)


-- @@ L197-209 verbatim
/-- The Cassini `1,1 -> 1` merge with positive label. -/
def positiveOneSaddleModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := CompactSaddle.sourceFLS m
  targetX := CompactSaddle.targetFLS m
  sourceSign := CompactSaddle.sourceSign m
  targetSign := CompactSaddle.targetSign m
  cobordism := CompactSaddle.signedCobordism m
  background_ne_zero := CompactSaddle.background_ne_zero m
  center := 0
  radius := 3
  radius_nonneg := by norm_num
  flatOutside := CompactSaddle.signedCobordism_spatialFlatOutside m


-- @@ L211-223 verbatim
/-- The same Cassini `1,1 -> 1` merge on the negative sheet. -/
def negativeOneSaddleModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := CompactSaddle.sourceFLS m
  targetX := CompactSaddle.targetFLS m
  sourceSign := CompactSaddle.sourceNegativeSign m
  targetSign := CompactSaddle.targetNegativeSign m
  cobordism := CompactSaddle.signedNegativeCobordism m
  background_ne_zero := CompactSaddle.background_ne_zero m
  center := 0
  radius := 3
  radius_nonneg := by norm_num
  flatOutside := CompactSaddle.signedNegativeCobordism_spatialFlatOutside m


-- @@ L225-237 verbatim
/-- The definite `1 -> empty` event with positive label. -/
def positiveDeathModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := CompactBirth.targetFLS (m + 1)
  targetX := CompactBirth.sourceFLS (m + 1)
  sourceSign := CompactBirth.targetSign (m + 1)
  targetSign := CompactBirth.sourceSign (m + 1)
  cobordism := CompactBirth.signedDeathCobordism (m + 1)
  background_ne_zero := CompactBirth.background_ne_zero (m + 1)
  center := 0
  radius := 2
  radius_nonneg := by norm_num
  flatOutside := CompactBirth.signedDeathCobordism_spatialFlatOutside (m + 1)


-- @@ L239-254 verbatim
/-- The same definite death with negative local label. -/
def negativeDeathModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := CompactBirth.targetFLS (m + 1)
  targetX := CompactBirth.sourceFLS (m + 1)
  sourceSign := (CompactBirth.targetSign (m + 1)).neg
  targetSign := (CompactBirth.sourceSign (m + 1)).neg
  cobordism := (CompactBirth.signedDeathCobordism (m + 1)).neg
  background_ne_zero := CompactBirth.background_ne_zero (m + 1)
  center := 0
  radius := 2
  radius_nonneg := by norm_num
  flatOutside := by
    change (CompactBirth.signedDeathCobordism (m + 1)).SpatialFlatOutside
      (compactBackground m) 0 2
    exact CompactBirth.signedDeathCobordism_spatialFlatOutside (m + 1)


-- @@ L256-260 verbatim
/-- Births and saddle splits are obtained without new geometry by reversing
the compact reductions. -/
def positiveBirthModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) :=
  (positiveDeathModel m).reverse


-- @@ L262-264 verbatim
def negativeBirthModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) :=
  (negativeDeathModel m).reverse


-- @@ L266-268 verbatim
def positiveSplitModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) :=
  (positiveOneSaddleModel m).reverse


-- @@ L270-272 verbatim
def negativeSplitModel :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) :=
  (negativeOneSaddleModel m).reverse


-- @@ L274-274 verbatim
/-! ## The one residual local Morse model -/


-- @@ L276-290 verbatim
/-- A spatially flat local `0,0 -> 1` saddle.

The exact ledger equalities state the missing frame computation, not merely
existence of a cobordism with unnamed endpoints.  One positive model suffices:
the negative-sheet event below is obtained by negating its label. -/
structure ZeroPairSaddleModel (m : ℕ) where
  source : SignedLedgerState (m + 2) [(0 : ZMod 2), 0]
  target : SignedLedgerState (m + 2) [(1 : ZMod 2)]
  source_positive : ∀ x ∈ source.X.fiber, 0 < source.sign x
  target_positive : ∀ x ∈ target.X.fiber, 0 < target.sign x
  cobordism : SignedFramedLevelCobordism source.sign target.sign
  center : EuclideanSpace ℝ (Fin (m + 3))
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  flatOutside : cobordism.SpatialFlatOutside (compactBackground m) center radius


-- @@ L292-292 verbatim
namespace ZeroPairSaddleModel


-- @@ L294-307 verbatim
/-- Forget only the ledger calculation and retain the positive compact head
event used by juxtaposition. -/
def positiveHeadMove (Z : ZeroPairSaddleModel m) :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := Z.source.X
  targetX := Z.target.X
  sourceSign := Z.source.sign
  targetSign := Z.target.sign
  cobordism := Z.cobordism
  background_ne_zero := CompactBirth.background_ne_zero (m + 1)
  center := Z.center
  radius := Z.radius
  radius_nonneg := Z.radius_nonneg
  flatOutside := Z.flatOutside


-- @@ L309-325 verbatim
/-- The same local saddle on the negative sheet, obtained without a second
geometric input. -/
def negativeHeadMove (Z : ZeroPairSaddleModel m) :
    SpatiallyFlatHeadMove (m + 2) (compactBackground m) where
  sourceX := Z.source.X
  targetX := Z.target.X
  sourceSign := Z.source.sign.neg
  targetSign := Z.target.sign.neg
  cobordism := Z.cobordism.neg
  background_ne_zero := CompactBirth.background_ne_zero (m + 1)
  center := Z.center
  radius := Z.radius
  radius_nonneg := Z.radius_nonneg
  flatOutside := by
    change Z.cobordism.SpatialFlatOutside
      (compactBackground m) Z.center Z.radius
    exact Z.flatOutside


-- @@ L327-327 verbatim
end ZeroPairSaddleModel


-- @@ L329-329 verbatim
/-! ## Local endpoint matching around one compact event -/


-- @@ L331-341 verbatim
/-- The only residual contract around a local event: normalize the current
source and target to the exact compact-model endpoints, preserving the
unchanged placed tail on both sides. -/
structure LocalHeadEventData {n : ℕ} {bkg : EuclideanSpace ℝ (Fin n)}
    {X Y : FramedLevelSet n} (S : FiberSign X) (T : FiberSign Y)
    (M : SpatiallyFlatHeadMove n bkg) where
  tail : FlatSignedConfiguration n bkg
  sourceNormalization : RelativeNormalizationData S
    (M.sourceWithTailSign tail) (M.placedTail tail).X.fiber
  targetNormalization : RelativeNormalizationData T
    (M.targetWithTailSign tail) (M.placedTail tail).X.fiber


-- @@ L343-343 verbatim
namespace LocalHeadEventData


-- @@ L345-345 verbatim
variable {n : ℕ} {bkg : EuclideanSpace ℝ (Fin n)}

-- @@ L346-346 verbatim
variable {X Y : FramedLevelSet n} {S : FiberSign X} {T : FiberSign Y}

-- @@ L347-347 verbatim
variable {M : SpatiallyFlatHeadMove n bkg}


-- @@ L349-358 verbatim
/-- Normalize into the compact source, run the concrete event, and reverse
the target normalization. -/
theorem nonempty_cobordism (D : LocalHeadEventData S T M) :
    Nonempty (SignedFramedLevelCobordism S T) :=
  SignedFramedLevelCobordism.nonempty_trans
    D.sourceNormalization.toNormalizationData.nonempty_cobordism
    (SignedFramedLevelCobordism.nonempty_trans
      (M.nonempty_withTail D.tail)
      (SignedFramedLevelCobordism.nonempty_symm
        D.targetNormalization.toNormalizationData.nonempty_cobordism))


-- @@ L360-360 verbatim
end LocalHeadEventData


-- @@ L362-365 verbatim
/-- Named local endpoint contracts used by the finite reducer. -/
abbrev PositiveOneSaddleData {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T (positiveOneSaddleModel m)


-- @@ L367-369 verbatim
abbrev NegativeOneSaddleData {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T (negativeOneSaddleModel m)


-- @@ L371-374 verbatim
abbrev PositiveZeroSaddleData (Z : ZeroPairSaddleModel m)
    {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T Z.positiveHeadMove


-- @@ L376-379 verbatim
abbrev NegativeZeroSaddleData (Z : ZeroPairSaddleModel m)
    {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T Z.negativeHeadMove


-- @@ L381-383 verbatim
abbrev PositiveDeathData {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T (positiveDeathModel m)


-- @@ L385-387 verbatim
abbrev NegativeDeathData {X Y : FramedLevelSet (m + 2)}
    (S : FiberSign X) (T : FiberSign Y) :=
  LocalHeadEventData S T (negativeDeathModel m)


-- @@ L389-389 verbatim
/-! ## Finite reduction of both ledgers -/


-- @@ L391-396 verbatim
/-- A signed presentation used at one node of the finite reduction.  The
ledger indices below are intentionally external: no equality to a
choice-dependent enumeration is demanded. -/
structure SignedConfigurationState (n : ℕ) where
  X : FramedLevelSet n
  sign : FiberSign X


-- @@ L398-429 verbatim
/-- Exact local models needed by the deterministic reducer.  A move may occur
after an arbitrary prefix; endpoint normalization moves the selected local
components to the compact head ball and places every other component in the
certified tail. -/
structure CompactMoveKit (m : ℕ)
    (state : MorseLedger → MorseLedger →
      SignedConfigurationState (m + 2)) where
  zeroPairSaddle : ZeroPairSaddleModel m
  zeroSaddlePos : ∀ (pre tail N : MorseLedger),
    PositiveZeroSaddleData m zeroPairSaddle
      (state (pre ++ (0 : ZMod 2) :: 0 :: tail) N).sign
      (state (pre ++ (1 : ZMod 2) :: tail) N).sign
  oneSaddlePos : ∀ (pre tail N : MorseLedger),
    PositiveOneSaddleData m
      (state (pre ++ (1 : ZMod 2) :: 1 :: tail) N).sign
      (state (pre ++ (1 : ZMod 2) :: tail) N).sign
  deathPos : ∀ (pre tail N : MorseLedger),
    PositiveDeathData m
      (state (pre ++ (1 : ZMod 2) :: tail) N).sign
      (state (pre ++ tail) N).sign
  zeroSaddleNeg : ∀ (P pre tail : MorseLedger),
    NegativeZeroSaddleData m zeroPairSaddle
      (state P (pre ++ (0 : ZMod 2) :: 0 :: tail)).sign
      (state P (pre ++ (1 : ZMod 2) :: tail)).sign
  oneSaddleNeg : ∀ (P pre tail : MorseLedger),
    NegativeOneSaddleData m
      (state P (pre ++ (1 : ZMod 2) :: 1 :: tail)).sign
      (state P (pre ++ (1 : ZMod 2) :: tail)).sign
  deathNeg : ∀ (P pre tail : MorseLedger),
    NegativeDeathData m
      (state P (pre ++ (1 : ZMod 2) :: tail)).sign
      (state P (pre ++ tail)).sign


-- @@ L431-431 verbatim
namespace CompactMoveKit


-- @@ L433-433 verbatim
variable {m : ℕ}

-- @@ L434-435 verbatim
variable {state : MorseLedger → MorseLedger →
  SignedConfigurationState (m + 2)}


-- @@ L437-511 verbatim
/-- Reduce the positive ledger using class-one deaths, the concrete
`1,1 -> 1` Cassini saddle, and the one residual `0,0 -> 1` model. -/
theorem reducePos (K : CompactMoveKit m state) :
    ∀ (P N : MorseLedger),
      Nonempty (SignedFramedLevelCobordism (state P N).sign
        (state (MorseLedger.canonical P.delta) N).sign)
  | [], N => by
      rw [MorseLedger.delta_nil, MorseLedger.canonical_zero]
      exact SignedFramedLevelCobordism.nonempty_refl _
  | [beta], N => by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta with rfl | rfl
      · have h : MorseLedger.canonical
            (MorseLedger.delta [(0 : ZMod 2)]) = [0] := by decide
        rw [h]
        exact SignedFramedLevelCobordism.nonempty_refl _
      · have h : MorseLedger.canonical
            (MorseLedger.delta [(1 : ZMod 2)]) = [] := by decide
        rw [h]
        simpa using (K.deathPos [] [] N).nonempty_cobordism
  | beta₁ :: beta₂ :: tail, N => by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₁ with rfl | rfl
      · rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₂ with rfl | rfl
        · have hsaddle :=
            (K.zeroSaddlePos [] tail N).nonempty_cobordism
          have hdeath := (K.deathPos [] tail N).nonempty_cobordism
          have htail := reducePos K tail N
          have hdelta :
              MorseLedger.delta ((0 : ZMod 2) :: 0 :: tail) =
                MorseLedger.delta tail := by
            simp only [MorseLedger.delta_cons, zero_add]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            calc
              1 + (1 + MorseLedger.delta tail) =
                  (1 + 1) + MorseLedger.delta tail := by abel
              _ = MorseLedger.delta tail := by rw [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hsaddle
            (SignedFramedLevelCobordism.nonempty_trans hdeath htail)
        · have hdeath := (K.deathPos [0] tail N).nonempty_cobordism
          have htail := reducePos K ((0 : ZMod 2) :: tail) N
          have hdelta :
              MorseLedger.delta ((0 : ZMod 2) :: 1 :: tail) =
                MorseLedger.delta ((0 : ZMod 2) :: tail) := by
            simp only [MorseLedger.delta_cons, zero_add]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hdeath htail
      · rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₂ with rfl | rfl
        · have hdeath :=
            (K.deathPos [] ((0 : ZMod 2) :: tail) N).nonempty_cobordism
          have htail := reducePos K ((0 : ZMod 2) :: tail) N
          have hdelta :
              MorseLedger.delta ((1 : ZMod 2) :: 0 :: tail) =
                MorseLedger.delta ((0 : ZMod 2) :: tail) := by
            simp only [MorseLedger.delta_cons]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            simp only [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hdeath htail
        · have hsaddle :=
            (K.oneSaddlePos [] tail N).nonempty_cobordism
          have hdeath := (K.deathPos [] tail N).nonempty_cobordism
          have htail := reducePos K tail N
          have hdelta :
              MorseLedger.delta ((1 : ZMod 2) :: 1 :: tail) =
                MorseLedger.delta tail := by
            simp only [MorseLedger.delta_cons]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            simp only [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hsaddle
            (SignedFramedLevelCobordism.nonempty_trans hdeath htail)
  termination_by P _ => P.length
  decreasing_by all_goals simp_all


-- @@ L513-586 verbatim
/-- The same deterministic reduction on the negative ledger. -/
theorem reduceNeg (K : CompactMoveKit m state) :
    ∀ (P N : MorseLedger),
      Nonempty (SignedFramedLevelCobordism (state P N).sign
        (state P (MorseLedger.canonical N.delta)).sign)
  | P, [] => by
      rw [MorseLedger.delta_nil, MorseLedger.canonical_zero]
      exact SignedFramedLevelCobordism.nonempty_refl _
  | P, [beta] => by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta with rfl | rfl
      · have h : MorseLedger.canonical
            (MorseLedger.delta [(0 : ZMod 2)]) = [0] := by decide
        rw [h]
        exact SignedFramedLevelCobordism.nonempty_refl _
      · have h : MorseLedger.canonical
            (MorseLedger.delta [(1 : ZMod 2)]) = [] := by decide
        rw [h]
        simpa using (K.deathNeg P [] []).nonempty_cobordism
  | P, beta₁ :: beta₂ :: tail => by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₁ with rfl | rfl
      · rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₂ with rfl | rfl
        · have hsaddle :=
            (K.zeroSaddleNeg P [] tail).nonempty_cobordism
          have hdeath := (K.deathNeg P [] tail).nonempty_cobordism
          have htail := reduceNeg K P tail
          have hdelta :
              MorseLedger.delta ((0 : ZMod 2) :: 0 :: tail) =
                MorseLedger.delta tail := by
            simp only [MorseLedger.delta_cons, zero_add]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            calc
              1 + (1 + MorseLedger.delta tail) =
                  (1 + 1) + MorseLedger.delta tail := by abel
              _ = MorseLedger.delta tail := by rw [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hsaddle
            (SignedFramedLevelCobordism.nonempty_trans hdeath htail)
        · have hdeath := (K.deathNeg P [0] tail).nonempty_cobordism
          have htail := reduceNeg K P ((0 : ZMod 2) :: tail)
          have hdelta :
              MorseLedger.delta ((0 : ZMod 2) :: 1 :: tail) =
                MorseLedger.delta ((0 : ZMod 2) :: tail) := by
            simp only [MorseLedger.delta_cons, zero_add]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hdeath htail
      · rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) beta₂ with rfl | rfl
        · have hdeath :=
            (K.deathNeg P [] ((0 : ZMod 2) :: tail)).nonempty_cobordism
          have htail := reduceNeg K P ((0 : ZMod 2) :: tail)
          have hdelta :
              MorseLedger.delta ((1 : ZMod 2) :: 0 :: tail) =
                MorseLedger.delta ((0 : ZMod 2) :: tail) := by
            simp only [MorseLedger.delta_cons]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hdeath htail
        · have hsaddle :=
            (K.oneSaddleNeg P [] tail).nonempty_cobordism
          have hdeath := (K.deathNeg P [] tail).nonempty_cobordism
          have htail := reduceNeg K P tail
          have hdelta :
              MorseLedger.delta ((1 : ZMod 2) :: 1 :: tail) =
                MorseLedger.delta tail := by
            simp only [MorseLedger.delta_cons]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            simp only [h11, zero_add]
          rw [hdelta]
          exact SignedFramedLevelCobordism.nonempty_trans hsaddle
            (SignedFramedLevelCobordism.nonempty_trans hdeath htail)
  termination_by _ N => N.length
  decreasing_by all_goals simp_all


-- @@ L588-588 verbatim
end CompactMoveKit


-- @@ L590-590 verbatim
/-! ## Adapter to `ConcreteConfigurationConfigure.Geometry` -/


-- @@ L592-611 verbatim
/-- Full finite-reduction data for one placed and gauge-normalized source.
The initial and final fields contain no topology change; every change of
component number occurs in `moves` through an explicit compact model. -/
structure ReductionData {X : FramedLevelSet (m + 2)} (S : FiberSign X)
    (P : ConcreteConfigurationConfigure.ComponentPlacementData m X)
    (G : ConcreteConfigurationConfigure.FrameGaugeData m P) where
  state : MorseLedger → MorseLedger → SignedConfigurationState (m + 2)
  initial : NormalizationData (G.endpointSign S)
    (state (ConcreteConfigurationConfigure.positiveLedger m S)
      (ConcreteConfigurationConfigure.negativeLedger m S)).sign
  moves : CompactMoveKit m state
  final : NormalizationData
    (state
      (MorseLedger.canonical
        (ConcreteConfigurationConfigure.positiveLedger m S).delta)
      (MorseLedger.canonical
        (ConcreteConfigurationConfigure.negativeLedger m S).delta)).sign
    (ConcreteConfigurationMoveKit.configSign m
      (ConcreteConfigurationConfigure.positiveLedger m S)
      (ConcreteConfigurationConfigure.negativeLedger m S))


-- @@ L613-613 verbatim
namespace ReductionData


-- @@ L615-615 verbatim
variable {m : ℕ} {X : FramedLevelSet (m + 2)} {S : FiberSign X}

-- @@ L616-616 verbatim
variable {P : ConcreteConfigurationConfigure.ComponentPlacementData m X}

-- @@ L617-617 verbatim
variable {G : ConcreteConfigurationConfigure.FrameGaugeData m P}


-- @@ L619-636 verbatim
/-- Initial relative normalization, all positive reductions, all negative
reductions, and final relative normalization compose to the exact diagonal
standard required by `Geometry.reduction`. -/
theorem nonempty_reduction (D : ReductionData m S P G) :
    Nonempty
      (SignedFramedLevelCobordism (G.endpointSign S)
        (ConcreteConfigurationMoveKit.configSign m
          (ConcreteConfigurationConfigure.positiveLedger m S)
          (ConcreteConfigurationConfigure.negativeLedger m S))) := by
  let PL := ConcreteConfigurationConfigure.positiveLedger m S
  let NL := ConcreteConfigurationConfigure.negativeLedger m S
  have hpos := D.moves.reducePos PL NL
  have hneg := D.moves.reduceNeg (MorseLedger.canonical PL.delta) NL
  exact SignedFramedLevelCobordism.nonempty_trans
    D.initial.nonempty_cobordism
    (SignedFramedLevelCobordism.nonempty_trans hpos
      (SignedFramedLevelCobordism.nonempty_trans hneg
        D.final.nonempty_cobordism))


-- @@ L638-644 verbatim
/-- Fill the formerly monolithic `Geometry.reduction` field with the finite
compact-Morse construction. -/
def toGeometry (D : ReductionData m S P G) :
    ConcreteConfigurationConfigure.Geometry m S where
  placement := P
  gauge := G
  reduction := D.nonempty_reduction


-- @@ L646-646 verbatim
end ReductionData


-- @@ L648-648 verbatim
end ConcreteConfigurationMorseReduction

-- @@ L649-649 verbatim
end Submission
