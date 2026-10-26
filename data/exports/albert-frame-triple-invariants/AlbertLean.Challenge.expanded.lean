import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi


-- @@ L6-24 verbatim
/-!
# The historical statement file

The coordinate data uses the explicit 27-coordinate model below.
The first form of the statement, superseded by the root `Challenge.lean` but still
imported by the proofs. It defines the 27 rational coordinates, the cubic norm
`cubicNorm` (45 monomials), the product `structuredProduct` recovered from the cubic by
the Springer construction, the trace form, frames and encoders, the ledger of 54 traces,
the word `W0` and the detector `traceCubeDetector`, the two rational configurations
`witnessTheta1` and `witnessThetaM`, unital ℚ-linear automorphisms `JordanAut`, and the
bundle `CombinedTarget` of everything proved about them.

The last declaration, `challenge : CombinedTarget := by sorry`, is a placeholder from the
original statement format. The proofs do not depend on it: `AlbertLean.solution` proves `CombinedTarget`
in `AlbertLean/Solution.lean`. It is the one `sorry` counted in `formalization.yaml`.

The Jordan identity is verified for `structuredProduct` in its linearised form
`(a⋄y)⋄(b⋄c) + (b⋄y)⋄(a⋄c) + (c⋄y)⋄(a⋄b) = a⋄(y⋄(b⋄c)) + b⋄(y⋄(a⋄c)) + c⋄(y⋄(a⋄b))`.
-/


-- @@ L26-26 verbatim
namespace AlbertLean


-- @@ L28-28 verbatim
abbrev Scalar := ℚ

-- @@ L29-29 verbatim
abbrev Slot := Fin 27

-- @@ L30-30 verbatim
abbrev Coord := Slot → Scalar


-- @@ L32-32 verbatim
def q (num : Int) (den : Nat) : ℚ := (num : ℚ) / (den : ℚ)

-- @@ L33-33 verbatim
def v (x : Coord) (i : Nat) : ℚ := if h : i < 27 then x ⟨i, h⟩ else 0

-- @@ L34-34 verbatim
def basisVec (i : Fin 27) : Coord := fun j => if j = i then 1 else 0


-- @@ L36-41 verbatim
def one : Coord := fun i =>
  match i.val with
  | 0 => q (1) 1
  | 1 => q (1) 1
  | 2 => q (1) 1
  | _ => 0


-- @@ L43-88 verbatim
def cubicNorm (x : Coord) : ℚ :=
    q (1) 1 * v x 0 * v x 1 * v x 2 +
    q (-1) 1 * v x 0 * v x 3 * v x 4 +
    q (-1) 1 * v x 0 * v x 5 * v x 10 +
    q (1) 1 * v x 0 * v x 6 * v x 9 +
    q (-1) 1 * v x 0 * v x 7 * v x 8 +
    q (-1) 1 * v x 1 * v x 11 * v x 15 +
    q (-1) 1 * v x 1 * v x 12 * v x 16 +
    q (-1) 1 * v x 1 * v x 13 * v x 17 +
    q (-1) 1 * v x 1 * v x 14 * v x 18 +
    q (-1) 1 * v x 2 * v x 19 * v x 23 +
    q (-1) 1 * v x 2 * v x 20 * v x 24 +
    q (-1) 1 * v x 2 * v x 21 * v x 25 +
    q (-1) 1 * v x 2 * v x 22 * v x 26 +
    q (1) 1 * v x 3 * v x 15 * v x 19 +
    q (1) 1 * v x 3 * v x 16 * v x 20 +
    q (1) 1 * v x 3 * v x 17 * v x 21 +
    q (1) 1 * v x 3 * v x 18 * v x 22 +
    q (1) 1 * v x 4 * v x 11 * v x 23 +
    q (1) 1 * v x 4 * v x 12 * v x 24 +
    q (1) 1 * v x 4 * v x 13 * v x 25 +
    q (1) 1 * v x 4 * v x 14 * v x 26 +
    q (1) 1 * v x 5 * v x 13 * v x 22 +
    q (-1) 1 * v x 5 * v x 14 * v x 21 +
    q (1) 1 * v x 5 * v x 15 * v x 24 +
    q (-1) 1 * v x 5 * v x 16 * v x 23 +
    q (-1) 1 * v x 6 * v x 12 * v x 22 +
    q (1) 1 * v x 6 * v x 14 * v x 20 +
    q (1) 1 * v x 6 * v x 15 * v x 25 +
    q (-1) 1 * v x 6 * v x 17 * v x 23 +
    q (1) 1 * v x 7 * v x 12 * v x 21 +
    q (-1) 1 * v x 7 * v x 13 * v x 20 +
    q (1) 1 * v x 7 * v x 15 * v x 26 +
    q (-1) 1 * v x 7 * v x 18 * v x 23 +
    q (1) 1 * v x 8 * v x 11 * v x 22 +
    q (-1) 1 * v x 8 * v x 14 * v x 19 +
    q (1) 1 * v x 8 * v x 16 * v x 25 +
    q (-1) 1 * v x 8 * v x 17 * v x 24 +
    q (-1) 1 * v x 9 * v x 11 * v x 21 +
    q (1) 1 * v x 9 * v x 13 * v x 19 +
    q (1) 1 * v x 9 * v x 16 * v x 26 +
    q (-1) 1 * v x 9 * v x 18 * v x 24 +
    q (1) 1 * v x 10 * v x 11 * v x 20 +
    q (-1) 1 * v x 10 * v x 12 * v x 19 +
    q (1) 1 * v x 10 * v x 17 * v x 26 +
    q (-1) 1 * v x 10 * v x 18 * v x 25


-- @@ L90-92 verbatim
def cubicPolar (x y z : Coord) : ℚ :=
  cubicNorm (x + y + z) - cubicNorm (x + y) - cubicNorm (x + z) -
  cubicNorm (y + z) + cubicNorm x + cubicNorm y + cubicNorm z - cubicNorm 0


-- @@ L94-94 verbatim
def traceN (x : Coord) : ℚ := cubicPolar one one x / 2

-- @@ L95-95 verbatim
def spurN (x : Coord) : ℚ := cubicPolar one x x / 2

-- @@ L96-96 verbatim
def spurBilinear (x y : Coord) : ℚ := cubicPolar one x y

-- @@ L97-97 verbatim
def traceForm (x y : Coord) : ℚ := traceN x * traceN y - spurBilinear x y


-- @@ L99-127 verbatim
def traceDualCoeffNat : Nat → Nat → ℚ
  | 0, 0 => q (1) 1
  | 1, 1 => q (1) 1
  | 2, 2 => q (1) 1
  | 3, 4 => q (1) 1
  | 4, 3 => q (1) 1
  | 5, 10 => q (1) 1
  | 6, 9 => q (-1) 1
  | 7, 8 => q (1) 1
  | 8, 7 => q (1) 1
  | 9, 6 => q (-1) 1
  | 10, 5 => q (1) 1
  | 11, 15 => q (1) 1
  | 12, 16 => q (1) 1
  | 13, 17 => q (1) 1
  | 14, 18 => q (1) 1
  | 15, 11 => q (1) 1
  | 16, 12 => q (1) 1
  | 17, 13 => q (1) 1
  | 18, 14 => q (1) 1
  | 19, 23 => q (1) 1
  | 20, 24 => q (1) 1
  | 21, 25 => q (1) 1
  | 22, 26 => q (1) 1
  | 23, 19 => q (1) 1
  | 24, 20 => q (1) 1
  | 25, 21 => q (1) 1
  | 26, 22 => q (1) 1
  | _, _ => 0

-- @@ L128-128 verbatim
def traceDualCoeff (i j : Fin 27) : ℚ := traceDualCoeffNat i.val j.val


-- @@ L130-131 verbatim
def sharp (x : Coord) : Coord := fun k =>
  ∑ j : Fin 27, (cubicPolar x x (basisVec j) / 2) * traceDualCoeff j k

-- @@ L132-132 verbatim
def cross (x y : Coord) : Coord := sharp (x + y) - sharp x - sharp y

-- @@ L133-134 verbatim
def structuredProduct (x y : Coord) : Coord :=
  (2 : ℚ)⁻¹ • (cross x y + traceN x • y + traceN y • x - spurBilinear x y • one)

-- @@ L135-135 verbatim
local infixl:70 " ⋄ " => structuredProduct


-- @@ L137-137 verbatim
def leftMulMatrixTrace (x : Coord) : ℚ := ∑ i : Slot, (structuredProduct x (basisVec i)) i

-- @@ L138-138 verbatim
def productTrace (x : Coord) : ℚ := leftMulMatrixTrace x / 9

-- @@ L139-139 verbatim
def productSpur (x : Coord) : ℚ := ((productTrace x) ^ 2 - productTrace (structuredProduct x x)) / 2

-- @@ L140-140 verbatim
def productNorm (x : Coord) : ℚ := (productTrace x) ^ 3 / 6 - productTrace x * productTrace (structuredProduct x x) / 2 + productTrace (structuredProduct x (structuredProduct x x)) / 3


-- @@ L142-146 verbatim
def IsQBilinear (mul : Coord → Coord → Coord) : Prop :=
  (∀ (x₁ x₂ y : Coord), mul (x₁ + x₂) y = mul x₁ y + mul x₂ y) ∧
  (∀ (a : ℚ) (x y : Coord), mul (a • x) y = a • mul x y) ∧
  (∀ (x y₁ y₂ : Coord), mul x (y₁ + y₂) = mul x y₁ + mul x y₂) ∧
  (∀ (a : ℚ) (x y : Coord), mul x (a • y) = a • mul x y)


-- @@ L148-151 verbatim
def leftMulLinear (h : IsQBilinear structuredProduct) (x : Coord) : Coord →ₗ[ℚ] Coord where
  toFun := structuredProduct x
  map_add' := h.2.2.1 x
  map_smul' := fun a y => h.2.2.2 a x y


-- @@ L153-153 verbatim
def NondegenerateTraceForm : Prop := ∀ x, (∀ y, traceForm x y = 0) → x = 0

-- @@ L154-154 verbatim
def TraceFormSymmetricNondegenerate : Prop := (∀ x y : Coord, traceForm x y = traceForm y x) ∧ NondegenerateTraceForm

-- @@ L155-155 verbatim
def CharacteristicIdentity : Prop := ∀ x : Coord, structuredProduct x (structuredProduct x x) - traceN x • structuredProduct x x + spurN x • x - cubicNorm x • one = 0

-- @@ L156-156 verbatim
def PrintedInvariantsAgree : Prop := (∀ x : Coord, productTrace x = traceN x) ∧ (∀ x : Coord, productSpur x = spurN x) ∧ (∀ x : Coord, productNorm x = cubicNorm x)


-- @@ L158-161 verbatim
structure WitnessTriple where
  cE : Coord
  cF : Coord
  cK : Coord


-- @@ L163-166 verbatim
def encoder (X : WitnessTriple) : Fin 3 → Coord
  | ⟨0, _⟩ => X.cE
  | ⟨1, _⟩ => X.cF
  | _ => X.cK


-- @@ L168-171 verbatim
def projector (c : Coord) : Fin 3 → Coord
  | ⟨0, _⟩ => (2 : ℚ)⁻¹ • (c ⋄ c - c)
  | ⟨1, _⟩ => one - c ⋄ c
  | _ => (2 : ℚ)⁻¹ • (c ⋄ c + c)


-- @@ L173-173 verbatim
def LawfulEncoder (c : Coord) : Prop := traceN c = 0 ∧ spurN c = -1 ∧ cubicNorm c = 0

-- @@ L174-178 verbatim
def LawfulFrame (c : Coord) : Prop :=
  LawfulEncoder c ∧ (∀ i, projector c i ⋄ projector c i = projector c i ∧ traceN (projector c i) = 1) ∧
  (∀ i j, i ≠ j → projector c i ⋄ projector c j = 0) ∧
  (projector c 0 + projector c 1 + projector c 2 = one) ∧
  (projector c 2 - projector c 0 = c)

-- @@ L179-179 verbatim
def LawfulFrameTriple (X : WitnessTriple) : Prop := ∀ r, LawfulFrame (encoder X r)


-- @@ L181-186 verbatim
structure Ledger where
  P : Fin 3 → Fin 3 → ℚ
  Q : Fin 3 → Fin 3 → ℚ
  R : Fin 3 → Fin 3 → ℚ
  C0 : Fin 3 → Fin 3 → Fin 3 → ℚ
  deriving DecidableEq


-- @@ L188-194 verbatim
def ledger (X : WitnessTriple) : Ledger :=
  let E := projector X.cE; let F := projector X.cF; let K := projector X.cK
  let P := fun i j => traceForm (E i) (F j)
  let Q := fun j l => traceForm (F j) (K l)
  let R := fun l i => traceForm (K l) (E i)
  ⟨P, Q, R, fun i j l => traceForm (E i) (F j ⋄ K l) -
    (P i j + Q j l + R l i) / 3 + 2 / 9⟩


-- @@ L196-197 verbatim
def W0 (X : WitnessTriple) : Coord :=
  X.cE ⋄ (X.cF ⋄ X.cK) - X.cF ⋄ (X.cE ⋄ X.cK)

-- @@ L198-198 verbatim
def cubicNormDetector (X : WitnessTriple) : ℚ := cubicNorm (W0 X)

-- @@ L199-199 verbatim
def traceCubeDetector (X : WitnessTriple) : ℚ := traceForm (W0 X) (W0 X ⋄ W0 X)


-- @@ L201-205 verbatim
def theta1E : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 1
  | 2 => q (1) 1
  | _ => 0


-- @@ L207-222 verbatim
def theta1F : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 3 => q (1) 1
  | 11 => q (1) 1
  | 15 => q (3) 2
  | 16 => q (-2) 1
  | 17 => q (-245) 54
  | 18 => q (-3) 2
  | 21 => q (1) 1
  | 24 => q (-2) 1
  | 25 => q (-35) 18
  | 26 => q (2) 1
  | _ => 0


-- @@ L224-239 verbatim
def theta1K : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 4 => q (1) 1
  | 12 => q (1) 1
  | 15 => q (-2) 1
  | 16 => q (1) 1
  | 17 => q (-3) 2
  | 18 => q (1) 1
  | 22 => q (1) 1
  | 23 => q (3) 2
  | 24 => q (-91) 27
  | 26 => q (-13) 9
  | _ => 0


-- @@ L241-241 verbatim
def witnessTheta1 : WitnessTriple := ⟨theta1E, theta1F, theta1K⟩


-- @@ L243-247 verbatim
def thetaME : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 1
  | 2 => q (1) 1
  | _ => 0


-- @@ L249-264 verbatim
def thetaMF : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 3 => q (1) 1
  | 11 => q (1) 1
  | 15 => q (3) 2
  | 16 => q (-2) 1
  | 17 => q (-245) 54
  | 18 => q (-8748) 410231
  | 21 => q (1) 1
  | 24 => q (-2) 1
  | 25 => q (-35) 18
  | 26 => q (11664) 410231
  | _ => 0


-- @@ L266-281 verbatim
def thetaMK : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-1) 1
  | 2 => q (4) 3
  | 4 => q (1) 1
  | 12 => q (1) 1
  | 15 => q (-2) 1
  | 16 => q (1) 1
  | 17 => q (-3) 2
  | 18 => q (5832) 410231
  | 22 => q (410231) 5832
  | 23 => q (3) 2
  | 24 => q (-91) 27
  | 26 => q (-8424) 410231
  | _ => 0


-- @@ L283-283 verbatim
def witnessThetaM : WitnessTriple := ⟨thetaME, thetaMF, thetaMK⟩


-- @@ L285-288 verbatim
structure JordanAut where
  toLinearEquiv : Coord ≃ₗ[ℚ] Coord
  map_one : toLinearEquiv one = one
  map_circle : ∀ (x y : Coord), toLinearEquiv (x ⋄ y) = toLinearEquiv x ⋄ toLinearEquiv y


-- @@ L290-290 verbatim
instance : CoeFun JordanAut (fun _ => Coord → Coord) := ⟨fun g x => g.toLinearEquiv x⟩

-- @@ L291-292 verbatim
def Transports (g : JordanAut) (X Y : WitnessTriple) : Prop :=
  g X.cE = Y.cE ∧ g X.cF = Y.cF ∧ g X.cK = Y.cK


-- @@ L294-308 verbatim
structure CombinedTarget : Prop where
  productQBilinear : IsQBilinear structuredProduct
  productCommutative : ∀ x y : Coord, structuredProduct x y = structuredProduct y x
  unitLaw : ∀ x : Coord, structuredProduct one x = x ∧ structuredProduct x one = x
  traceFormSymmetricNondegenerate : TraceFormSymmetricNondegenerate
  traceFormAssociative : ∀ x y z : Coord, traceForm (structuredProduct x y) z = traceForm x (structuredProduct y z)
  jordanIdentity : ∀ x y : Coord, structuredProduct (structuredProduct x y) (structuredProduct x x) = structuredProduct x (structuredProduct y (structuredProduct x x))
  characteristicIdentity : CharacteristicIdentity
  printedInvariantsAgree : PrintedInvariantsAgree
  witnessTheta1Lawful : LawfulFrameTriple witnessTheta1
  witnessThetaMLawful : LawfulFrameTriple witnessThetaM
  witnessSameLedger : ledger witnessTheta1 = ledger witnessThetaM
  witnessDetectorValues : traceCubeDetector witnessTheta1 = q (-2591357) 62208 ∧ traceCubeDetector witnessThetaM = q (-1782559) 62208 ∧ traceCubeDetector witnessTheta1 ≠ traceCubeDetector witnessThetaM
  detectorFactorThree : ∀ X : WitnessTriple, traceN (W0 X) = 0 → traceCubeDetector X = 3 * cubicNormDetector X
  noUnitalProductAutomorphismTransports : ¬ ∃ g : JordanAut, Transports g witnessTheta1 witnessThetaM


-- @@ L310-311 verbatim
/-- Palomar-style statement placeholder. Proof code must not use this theorem. -/
theorem challenge : CombinedTarget := by sorry


-- @@ L313-313 verbatim
end AlbertLean
