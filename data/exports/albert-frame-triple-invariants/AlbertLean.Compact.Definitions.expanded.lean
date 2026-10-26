import TauCeti.Algebra.AlbertAlgebra
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Equiv.Defs


-- @@ L5-18 verbatim
/-!
# An earlier compact presentation of the rational example (superseded)

Namespace `CompactOneBit` is an earlier, self-contained presentation of the rational
example: two fixed rational frame triples with the same 54 recorded traces but unequal
detector values, with the coordinate product identified with Tau Ceti's split Albert
algebra. It is **not** the public statement of record and none of its declarations is
selected for comparison. The public statement is the root `Challenge.lean`
(namespace `OneBit` at the released commit), whose finite theorems
`OneBit.rationalWitness` and `OneBit.rationalWitness_not_equivalent_under_relabelling` are
proved in `OneBit/Closeout/`. These files are retained because later modules
(`AlbertLean/Generic/CubicAutomorphismCompact.lean`, `AlbertLean/Generic/TauTransport.lean`)
import them. No generic, scalar-extension, relabelling or primitivity claim is made here.
-/

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
namespace CompactOneBit

-- @@ L21-21 verbatim
open scoped BigOperators

-- @@ L22-23 verbatim
/-- The source rational vector space, in the literal ordered 27-coordinate basis. -/
abbrev Coord := Fin 27 → ℚ

-- @@ L24-27 verbatim
/-- The conventional split Albert algebra supplied by the pinned Tau Ceti library. -/
abbrev Albert := TauCeti.AlbertAlgebra ℚ
-- Tau Ceti supplies the carrier and product. Result.jordan and the explicit
-- product-preserving bijection establish the Jordan law used here.

-- @@ L28-28 verbatim
local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)


-- @@ L30-31 verbatim
/-- Source unit in the fixed 27-coordinate basis. -/
def unit : Coord := fun i => if i.val < 3 then 1 else 0

-- @@ L32-48 verbatim
/-- The exact exported cubic, retaining all 45 signed monomials in order. -/
def cubic (x : Coord) : ℚ :=
  x 0 * x 1 * x 2 - x 0 * x 3 * x 4 - x 0 * x 5 * x 10
  + x 0 * x 6 * x 9 - x 0 * x 7 * x 8 - x 1 * x 11 * x 15
  - x 1 * x 12 * x 16 - x 1 * x 13 * x 17 - x 1 * x 14 * x 18
  - x 2 * x 19 * x 23 - x 2 * x 20 * x 24 - x 2 * x 21 * x 25
  - x 2 * x 22 * x 26 + x 3 * x 15 * x 19 + x 3 * x 16 * x 20
  + x 3 * x 17 * x 21 + x 3 * x 18 * x 22 + x 4 * x 11 * x 23
  + x 4 * x 12 * x 24 + x 4 * x 13 * x 25 + x 4 * x 14 * x 26
  + x 5 * x 13 * x 22 - x 5 * x 14 * x 21 + x 5 * x 15 * x 24
  - x 5 * x 16 * x 23 - x 6 * x 12 * x 22 + x 6 * x 14 * x 20
  + x 6 * x 15 * x 25 - x 6 * x 17 * x 23 + x 7 * x 12 * x 21
  - x 7 * x 13 * x 20 + x 7 * x 15 * x 26 - x 7 * x 18 * x 23
  + x 8 * x 11 * x 22 - x 8 * x 14 * x 19 + x 8 * x 16 * x 25
  - x 8 * x 17 * x 24 - x 9 * x 11 * x 21 + x 9 * x 13 * x 19
  + x 9 * x 16 * x 26 - x 9 * x 18 * x 24 + x 10 * x 11 * x 20
  - x 10 * x 12 * x 19 + x 10 * x 17 * x 26 - x 10 * x 18 * x 25

-- @@ L49-52 verbatim
/-- Full cubic polarization, with no factorial normalization. -/
def polar (x y z : Coord) : ℚ :=
  cubic (x+y+z) - cubic (x+y) - cubic (x+z) - cubic (y+z)
    + cubic x + cubic y + cubic z - cubic 0

-- @@ L53-54 verbatim
/-- The linear trace determined by the cubic and source unit. -/
def trace (x : Coord) : ℚ := polar unit unit x / 2

-- @@ L55-56 verbatim
/-- Quadratic coefficient of the cubic characteristic polynomial. -/
def spur (x : Coord) : ℚ := polar unit x x / 2

-- @@ L57-58 verbatim
/-- The symmetric trace pairing determined by the cubic and unit. -/
def pairing (x y : Coord) : ℚ := trace x * trace y - polar unit x y

-- @@ L59-63 verbatim
/-- The inverse trace Gram matrix as its explicit signed coordinate permutation. -/
def dual (x : Coord) : Coord :=
  ![x 0, x 1, x 2, x 4, x 3, x 10, -x 9, x 8, x 7, -x 6, x 5,
    x 15, x 16, x 17, x 18, x 11, x 12, x 13, x 14,
    x 23, x 24, x 25, x 26, x 19, x 20, x 21, x 22]

-- @@ L64-65 verbatim
/-- Source adjoint obtained by trace-dualizing the cubic differential. -/
def adjoint (x : Coord) : Coord := dual (fun j => polar x x (Pi.single j 1) / 2)

-- @@ L66-69 verbatim
/-- The source Springer product; it is not defined by transport from Tau Ceti. -/
def product (x y : Coord) : Coord := (2 : ℚ)⁻¹ •
  (adjoint (x+y) - adjoint x - adjoint y + trace x • y + trace y • x
    - polar unit x y • unit)

-- @@ L70-70 verbatim
local infixl:70 " ⋄ " => product

-- @@ L71-72 verbatim
/-- Normalized trace of left multiplication, in the source coordinate basis. -/
def operatorTrace (x : Coord) : ℚ := (∑ i : Fin 27, (x ⋄ Pi.single i 1) i) / 9

-- @@ L73-74 verbatim
/-- Quadratic coefficient recovered from the normalized operator trace. -/
def operatorSpur (x : Coord) : ℚ := (operatorTrace x ^ 2 - operatorTrace (x ⋄ x)) / 2

-- @@ L75-77 verbatim
/-- Cubic coefficient recovered from the normalized operator trace. -/
def operatorNorm (x : Coord) : ℚ := operatorTrace x ^ 3 / 6
  - operatorTrace x * operatorTrace (x ⋄ x) / 2 + operatorTrace (x ⋄ (x ⋄ x)) / 3


-- @@ L79-84 verbatim
/-- Literal C0-to-Zorn map: off-diagonal order is (23,31,12). -/
def toAlbert (x : Coord) : Albert :=
  ⟨![x 0, x 1, x 2],
    ![⟨x 3, x 4, ![-x 8, x 6, -x 5], ![x 7, x 9, x 10]⟩,
      ⟨x 18, x 14, ![x 15, x 16, x 17], ![-x 11, -x 12, -x 13]⟩,
      ⟨x 22, x 26, ![-x 23, -x 24, -x 25], ![x 19, x 20, x 21]⟩]⟩

-- @@ L85-91 verbatim
/-- Literal inverse coordinate reader; all basis signs remain visible. -/
def fromAlbert (a : Albert) : Coord :=
  let v := a.offDiag 0; let s := a.offDiag 1; let c := a.offDiag 2
  ![a.diag 0, a.diag 1, a.diag 2, v.a, v.b, -v.v 2, v.v 1,
    v.w 0, -v.v 0, v.w 1, v.w 2, -s.w 0, -s.w 1, -s.w 2, s.b,
    s.v 0, s.v 1, s.v 2, s.a, c.w 0, c.w 1, c.w 2, c.a,
    -c.v 0, -c.v 1, -c.v 2, c.b]

-- @@ L92-96 verbatim
/-- Conventional Hermitian cubic norm, including the cyclic scalar triple term. -/
def albertNorm (a : Albert) : ℚ :=
  let d := a.diag; let x := a.offDiag
  d 0 * d 1 * d 2 - (∑ i : Fin 3, d i * TauCeti.Octonion.norm (x i))
    + TauCeti.Octonion.trace ((x 1 * x 2) * x 0)


-- @@ L98-99 verbatim
/-- Three ordered encoders, with indices 0, 1, 2 representing E, F, K. -/
abbrev Triple := Fin 3 → Coord

-- @@ L100-102 verbatim
/-- Spectral projectors, ordered by eigenvalues -1, 0, 1. -/
def projector (x : Coord) : Fin 3 → Coord :=
  ![(2 : ℚ)⁻¹ • (x ⋄ x - x), unit - x ⋄ x, (2 : ℚ)⁻¹ • (x ⋄ x + x)]

-- @@ L103-108 verbatim
/-- Three nonzero trace-one orthogonal idempotents, with their encoder identities. -/
def Frame (x : Coord) : Prop :=
  trace x = 0 ∧ spur x = -1 ∧ cubic x = 0 ∧
  (∀ i, projector x i ⋄ projector x i = projector x i ∧ trace (projector x i) = 1) ∧
  (∀ i j, i ≠ j → projector x i ⋄ projector x j = 0) ∧
  projector x 0 + projector x 1 + projector x 2 = unit ∧ projector x 2 - projector x 0 = x

-- @@ L109-111 verbatim
/-- Cyclic pair tables: r=0,1,2 are P(E,F), Q(F,K), R(K,E), respectively. -/
def pairs (X : Triple) (r i j : Fin 3) : ℚ :=
  pairing (projector (X r) i) (projector (X (r+1)) j)

-- @@ L112-115 verbatim
/-- The complete 27-entry centered joint table. -/
def centered (X : Triple) (i j k : Fin 3) : ℚ :=
  pairing (projector (X 0) i) (projector (X 1) j ⋄ projector (X 2) k)
    - (pairs X 0 i j + pairs X 1 j k + pairs X 2 k i) / 3 + 2 / 9

-- @@ L116-117 verbatim
/-- Product word measuring the commutator of left multiplication by E and F on K. -/
def word (X : Triple) : Coord := X 0 ⋄ (X 1 ⋄ X 2) - X 1 ⋄ (X 0 ⋄ X 2)

-- @@ L118-119 verbatim
/-- The trace-cube detector, with the source trace normalization. -/
def detector (X : Triple) : ℚ := pairing (word X) (word X ⋄ word X)


-- @@ L121-123 verbatim
/-- Encoder of the common first frame. -/
def E : Coord := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- @@ L124-126 verbatim
/-- Second encoder of the first witness, in the fixed source basis. -/
def F : Coord := ![-1/3, -1, 4/3, 1, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 3/2, -2, -245/54, -3/2, 0, 0, 1, 0, 0, -2, -35/18, 2]

-- @@ L127-129 verbatim
/-- Third encoder of the first witness. -/
def K : Coord := ![-1/3, -1, 4/3, 0, 1, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 0, -2, 1, -3/2, 1, 0, 0, 0, 1, 3/2, -91/27, 0, -13/9]

-- @@ L130-131 verbatim
/-- Second witness's second encoder: exactly two coordinates differ from F. -/
def F' : Coord := Function.update (Function.update F 18 (-8748/410231)) 26 (11664/410231)

-- @@ L132-134 verbatim
/-- Second witness's third encoder: exactly three coordinates differ from K. -/
def K' : Coord := Function.update
  (Function.update (Function.update K 18 (5832/410231)) 22 (410231/5832)) 26 (-8424/410231)

-- @@ L135-136 verbatim
/-- The first ordered encoder triple. -/
def first : Triple := ![E, F, K]

-- @@ L137-138 verbatim
/-- The second ordered encoder triple; labels and frame order are fixed. -/
def second : Triple := ![E, F', K']


-- @@ L140-144 verbatim
/-- Rational-linear unital product automorphism; detector preservation is not assumed. -/
structure Aut where
  linear : Coord ≃ₗ[ℚ] Coord
  unit : linear CompactOneBit.unit = CompactOneBit.unit
  product : ∀ x y, linear (x ⋄ y) = linear x ⋄ linear y

-- @@ L145-146 verbatim
/-- A transporter respects all three ordered encoders. -/
def Transports (g : Aut) (X Y : Triple) : Prop := ∀ r, g.linear (X r) = Y r


-- @@ L148-181 verbatim
/-- All original mathematical obligations, with an explicit Tau Ceti identification. -/
structure Result : Prop where
  inverse₁ : Function.LeftInverse fromAlbert toAlbert
  inverse₂ : Function.RightInverse fromAlbert toAlbert
  linear_add : ∀ x y, toAlbert (x+y) = toAlbert x + toAlbert y
  linear_smul : ∀ (a : ℚ) x, toAlbert (a • x) = a • toAlbert x
  maps_unit : toAlbert unit = 1
  maps_cubic : ∀ x, albertNorm (toAlbert x) = cubic x
  maps_product : ∀ x y, toAlbert (x ⋄ y) = toAlbert x * toAlbert y
  add_left : ∀ x y z, (x+y) ⋄ z = x ⋄ z + y ⋄ z
  smul_left : ∀ (a : ℚ) x y, (a • x) ⋄ y = a • (x ⋄ y)
  add_right : ∀ x y z, x ⋄ (y+z) = x ⋄ y + x ⋄ z
  smul_right : ∀ (a : ℚ) x y, x ⋄ (a • y) = a • (x ⋄ y)
  commutative : ∀ x y, x ⋄ y = y ⋄ x
  unital : ∀ x, unit ⋄ x = x ∧ x ⋄ unit = x
  symmetric : ∀ x y, pairing x y = pairing y x
  nondegenerate : ∀ x, (∀ y, pairing x y = 0) → x = 0
  associative_trace : ∀ x y z, pairing (x ⋄ y) z = pairing x (y ⋄ z)
  jordan : ∀ x y, (x ⋄ y) ⋄ (x ⋄ x) = x ⋄ (y ⋄ (x ⋄ x))
  characteristic : ∀ x,
    x ⋄ (x ⋄ x) - trace x • (x ⋄ x) + spur x • x - cubic x • unit = 0
  printed_trace : ∀ x, operatorTrace x = trace x
  printed_spur : ∀ x, operatorSpur x = spur x
  printed_norm : ∀ x, operatorNorm x = cubic x
  first_frames : ∀ r, Frame (first r)
  second_frames : ∀ r, Frame (second r)
  same_pairs : pairs first = pairs second
  same_centered : centered first = centered second
  first_value : detector first = -2591357/62208
  second_value : detector second = -1782559/62208
  unequal : detector first ≠ detector second
  factor_three : ∀ X : Triple, trace (word X) = 0 → detector X = 3 * cubic (word X)
  nontransport : ¬ ∃ g : Aut, Transports g first second
  invariant : ∀ (g : Aut) (X Y : Triple), Transports g X Y → detector Y = detector X


-- @@ L183-183 verbatim
end CompactOneBit
