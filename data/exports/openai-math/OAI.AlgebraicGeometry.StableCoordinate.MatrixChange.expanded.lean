import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# The determinant-preserving change in §2

These identities are valid in every commutative ring.  The parameter `t` gives
`(I - 2t n eᵀ) M`, and composition adds parameters.  No division by two is
needed in the coordinate formulas.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.MatrixChange


-- @@ L17-17 verbatim
variable {K : Type*} [CommRing K]


-- @@ L19-20 verbatim
/-- The negative determinant of the displayed two-by-two matrix. -/
def quad (p s u F : K) : K := s ^ 2 - u ^ 2 + p * F


-- @@ L22-23 verbatim
def pChange (t p s u F J : K) : K :=
  p + 2 * t * quad p s u F * (quad p s u F * (s - u) + p * J)


-- @@ L25-26 verbatim
def sChange (t p s u F J : K) : K :=
  s + t * (2 * J * quad p s u F * u - p * J ^ 2 - (quad p s u F) ^ 2 * F)


-- @@ L28-29 verbatim
def uChange (t p s u F J : K) : K :=
  u + t * (2 * s * J * quad p s u F + p * J ^ 2 - (quad p s u F) ^ 2 * F)


-- @@ L31-32 verbatim
def FChange (t p s u F J : K) : K :=
  F + 2 * t * J * (J * (s + u) - quad p s u F * F)


-- @@ L34-36 verbatim
/-- The defining equation of the five-variable hypersurface. -/
def relation (p s u F J : K) : K :=
  (quad p s u F) ^ 2 * F - (1 + 2 * s * quad p s u F) * J - p * J ^ 2 - u


-- @@ L38-38 verbatim
section Maps

-- @@ L39-39 verbatim
variable {L : Type*} [CommRing L] {G : Type*} [FunLike G K L] [RingHomClass G K L]


-- @@ L41-43 verbatim
@[simp] lemma map_quad (h : G) (p s u F : K) :
    h (quad p s u F) = quad (h p) (h s) (h u) (h F) := by
  simp [quad]


-- @@ L45-47 verbatim
@[simp] lemma map_pChange (h : G) (t p s u F J : K) :
    h (pChange t p s u F J) = pChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [pChange, map_ofNat]


-- @@ L49-51 verbatim
@[simp] lemma map_sChange (h : G) (t p s u F J : K) :
    h (sChange t p s u F J) = sChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [sChange, map_ofNat]


-- @@ L53-55 verbatim
@[simp] lemma map_uChange (h : G) (t p s u F J : K) :
    h (uChange t p s u F J) = uChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [uChange, map_ofNat]


-- @@ L57-59 verbatim
@[simp] lemma map_FChange (h : G) (t p s u F J : K) :
    h (FChange t p s u F J) = FChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [FChange, map_ofNat]


-- @@ L61-63 verbatim
@[simp] lemma map_relation (h : G) (p s u F J : K) :
    h (relation p s u F J) = relation (h p) (h s) (h u) (h F) (h J) := by
  simp [relation, map_ofNat]


-- @@ L65-65 verbatim
end Maps


-- @@ L67-71 verbatim
lemma quad_change (t p s u F J : K) :
    quad (pChange t p s u F J) (sChange t p s u F J)
      (uChange t p s u F J) (FChange t p s u F J) = quad p s u F := by
  unfold quad pChange sChange uChange FChange
  ring


-- @@ L73-79 verbatim
lemma pChange_add (t r p s u F J : K) :
    pChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = pChange (t + r) p s u F J := by
  rw [pChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange]
  ring


-- @@ L81-87 verbatim
lemma sChange_add (t r p s u F J : K) :
    sChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = sChange (t + r) p s u F J := by
  rw [sChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange, FChange]
  ring


-- @@ L89-95 verbatim
lemma uChange_add (t r p s u F J : K) :
    uChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = uChange (t + r) p s u F J := by
  rw [uChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange, FChange]
  ring


-- @@ L97-103 verbatim
lemma FChange_add (t r p s u F J : K) :
    FChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = FChange (t + r) p s u F J := by
  rw [FChange]
  simp only [quad_change]
  simp only [sChange, uChange, FChange]
  ring


-- @@ L105-106 verbatim
@[simp] lemma pChange_zero (p s u F J : K) : pChange 0 p s u F J = p := by
  simp [pChange]

-- @@ L107-108 verbatim
@[simp] lemma sChange_zero (p s u F J : K) : sChange 0 p s u F J = s := by
  simp [sChange]

-- @@ L109-110 verbatim
@[simp] lemma uChange_zero (p s u F J : K) : uChange 0 p s u F J = u := by
  simp [uChange]

-- @@ L111-112 verbatim
@[simp] lemma FChange_zero (p s u F J : K) : FChange 0 p s u F J = F := by
  simp [FChange]


-- @@ L114-117 verbatim
lemma uChange_one (p s u F J : K) :
    uChange 1 p s u F J = -relation p s u F J - J := by
  unfold uChange relation
  ring


-- @@ L119-126 verbatim
lemma relation_change_neg_one (p s u F J : K) :
    relation (pChange (-1) p s u F J) (sChange (-1) p s u F J)
      (uChange (-1) p s u F J) (FChange (-1) p s u F J) J = -J - u := by
  have h := uChange_one (pChange (-1) p s u F J) (sChange (-1) p s u F J)
      (uChange (-1) p s u F J) (FChange (-1) p s u F J) J
  rw [uChange_add] at h
  simp only [add_neg_cancel, uChange_zero] at h
  linear_combination h


-- @@ L128-128 verbatim
end StableCoordinate.MatrixChange


-- @@ L130-130 verbatim
end OAI
