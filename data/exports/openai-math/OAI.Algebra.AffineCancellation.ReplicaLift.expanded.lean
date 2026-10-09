import OAI.Algebra.AffineCancellation.InvariantRestriction
import OAI.Algebra.AffineCancellation.BezoutFrame
import OAI.Algebra.AffineCancellation.TorsorClearing


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace ComplexCancellation.SliceDerivative

-- @@ L10-10 verbatim
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

-- @@ L11-15 verbatim
def derivation : Derivation k (Polynomial F) (Polynomial F) :=
  Derivation.mk' ((Polynomial.derivative (R := F)).restrictScalars k) (by
    intro p q
    change (p*q).derivative=p*q.derivative+q*p.derivative
    rw [Polynomial.derivative_mul,mul_comm p.derivative q,add_comm])

-- @@ L16-16 verbatim
lemma apply_eq (p : Polynomial F) : derivation (k := k) p=p.derivative := rfl

-- @@ L17-19 verbatim
lemma locallyNilpotent : LND.LocallyNilpotent (derivation (k := k) (F := F)) := by
  intro p
  exact ⟨p.natDegree+1,Polynomial.iterate_derivative_eq_zero (by omega)⟩

-- @@ L20-20 verbatim
end ComplexCancellation.SliceDerivative


-- @@ L22-22 verbatim
namespace ComplexCancellation.Bundle

-- @@ L23-25 verbatim
instance finiteType : Algebra.FiniteType ℂ B := by
  let : Algebra.FiniteType ℂ Determinant.T := Algebra.FiniteType.quotient ℂ _
  infer_instance

-- @@ L26-26 verbatim
end ComplexCancellation.Bundle


-- @@ L28-28 verbatim
namespace ComplexCancellation.Torsor

-- @@ L29-29 verbatim
open LaurentPolynomial

-- @@ L30-30 verbatim
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]

-- @@ L31-31 verbatim
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)

-- @@ L32-32 verbatim
variable (hρ : Function.Injective ρ) (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)

-- @@ L33-33 verbatim
variable (Dp : Derivation ℂ P P) (hDp : LND.LocallyNilpotent Dp) (hder : ∀ r, Dp (ρ r)=ρ (D r))

-- @@ L34-38 verbatim
include hder in
omit [IsDomain P] in
lemma extension_base (r : Degeneration.G) : LaurentDerivation.extension Dp (base ρ r)=base ρ (D r) := by
  change LaurentDerivation.extension Dp (C (ρ r))=C (ρ (D r))
  rw [LaurentDerivation.extension_C,hder]

-- @@ L39-39 verbatim
include hρ hc hDp hder

-- @@ L40-49 verbatim
lemma invariant_replica (hf : Function.Injective (forward ρ Q)) :
    ∃ c : Degeneration.G, ∃ E : Derivation ℂ Bundle.B Bundle.B,
      D c=0 ∧ c≠0 ∧ LND.LocallyNilpotent E ∧
      ∀ b, forward ρ Q (E b)=base ρ c*LaurentDerivation.extension Dp (forward ρ Q b) := by
  have hbase (r : Degeneration.G) : forward ρ Q (Bundle.pullback r)=base ρ r :=
    DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  obtain ⟨c,E,hDc,hcn,hE,hs⟩ := InvariantRestriction.exists_restriction Bundle.pullback (forward ρ Q) hf D
    (LaurentDerivation.extension Dp) (LaurentDerivation.locallyNilpotent Dp hDp)
    (fun r => by rw [hbase,hbase,extension_base ρ D Dp hder]) (clear_laurent ρ Q D hρ hc)
  exact ⟨c,E,hDc,hcn,hE,fun b => by rw [hs,hbase]⟩

-- @@ L50-50 verbatim
end ComplexCancellation.Torsor


-- @@ L52-52 verbatim
namespace ComplexCancellation.PolynomialTorsor

-- @@ L53-53 verbatim
open PolynomialModel

-- @@ L54-54 verbatim
instance : CharZero Degeneration.G := Algebra.charZero_of_charZero ℂ Degeneration.G

-- @@ L55-55 verbatim
variable (D : Derivation ℂ Degeneration.G Degeneration.G) (hD : LND.LocallyNilpotent D)

-- @@ L56-56 verbatim
abbrev K := FractionRing Degeneration.G

-- @@ L57-57 verbatim
abbrev P := Polynomial (PolynomialModel.F D)

-- @@ L58-58 verbatim
variable {t : K} (ht : FractionDerivation.extend D t=1)

-- @@ L59-59 verbatim
noncomputable def ρ : Degeneration.G →ₐ[ℂ] P D := model D hD ht

-- @@ L60-60 verbatim
lemma ρ_injective : Function.Injective (ρ D hD ht) := model_injective D hD ht

-- @@ L61-65 verbatim
lemma exists_frame : Nonempty (Torsor.Frame (ρ D hD ht)) := by
  have h := congrArg (ρ D hD ht) Degeneration.equation
  simp only [map_mul,map_add,map_one] at h
  obtain ⟨a,d,b,c,hab,hdc,hdb,hdet⟩ := BezoutFrame.exists_frame _ _ _ h
  exact ⟨⟨a,d,b,c,hab,hdc,hdb,hdet⟩⟩

-- @@ L66-68 verbatim
def toField : K →ₐ[ℂ] Torsor.KB :=
  IsFractionRing.liftAlgHom (g := Torsor.ib.comp Bundle.pullback)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective)

-- @@ L69-69 verbatim
def inverseCoefficient : P D →ₐ[ℂ] Torsor.KB := (toField).comp (PolynomialModel.evaluation (D := D) (t := t))

-- @@ L70-76 verbatim
lemma inverseCoefficient_comp : (inverseCoefficient (D := D) (t := t)).comp (ρ D hD ht)=Torsor.ib.comp Bundle.pullback := by
  ext r
  change toField (PolynomialModel.evaluation (D := D) (t := t) (model D hD ht r))=_
  rw [evaluation_model]
  exact IsFractionRing.lift_algebraMap
    (g := (Torsor.ib.comp Bundle.pullback).toRingHom)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective) r

-- @@ L77-78 verbatim
lemma forward_injective (Q : Torsor.Frame (ρ D hD ht)) : Function.Injective (Torsor.forward (ρ D hD ht) Q) :=
  Torsor.forward_injective _ Q (inverseCoefficient (D := D) (t := t)) (inverseCoefficient_comp D hD ht)

-- @@ L79-79 verbatim
end ComplexCancellation.PolynomialTorsor


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
