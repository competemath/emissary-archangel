import OAI.AlgebraicGeometry.StableCoordinate.NonzeroFiber
import OAI.AlgebraicGeometry.StableCoordinate.IteratedQuotient
import OAI.AlgebraicGeometry.StableCoordinate.QuotientTransport


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-15 verbatim
/-!
# Transport of the proved nonzero-fiber calculation

This module connects the simultaneous-equation calculation in `NonzeroFiber`
to the manuscript's successive quotient `A/(p-l)`, then transports it through
any proved polynomial-presentation equivalence. The eventual exact-polynomial
endpoint supplies the presentation equivalence; these generic transport lemmas
are not substituted for that endpoint.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace StableCoordinate.NonzeroFiber


-- @@ L21-21 verbatim
open MvPolynomial


-- @@ L23-23 verbatim
variable {K : Type*} [Field K]


-- @@ L25-26 verbatim
/-- The manuscript's five-generator single-relation presentation. -/
abbrev Source (K : Type*) [Field K] := P5 K ⧸ Ideal.span {(H : P5 K)}


-- @@ L28-29 verbatim
/-- The distinguished element `p` in the manuscript presentation. -/
def sourceP : Source K := Ideal.Quotient.mk _ (X 0)


-- @@ L31-34 verbatim
/-- Every nonzero fiber of the manuscript presentation is a polynomial algebra. -/
def sourceFiberEquiv (l : K) (hl : l≠0) :
    (Source K ⧸ Ideal.span {sourceP - algebraMap K (Source K) l}) ≃ₐ[K] P3 K :=
  (IteratedQuotient.fiberEquiv K (P5 K) H (X 0) l).trans (nonzeroFiberEquiv l hl)


-- @@ L36-41 verbatim
/-- Transfer the proved nonzero-fiber equivalence through a separately proved
presentation equivalence that carries `p` to a specified polynomial. -/
def transportedFiberEquiv {B : Type*} [CommRing B] [Algebra K B]
    (e : Source K ≃ₐ[K] B) (g : B) (hg : e sourceP=g) (l : K) (hl : l≠0) :
    (B ⧸ Ideal.span {g-algebraMap K B l}) ≃ₐ[K] P3 K :=
  (fiberQuotientEquiv e sourceP g hg l).symm.trans (sourceFiberEquiv l hl)


-- @@ L43-43 verbatim
end StableCoordinate.NonzeroFiber


-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
