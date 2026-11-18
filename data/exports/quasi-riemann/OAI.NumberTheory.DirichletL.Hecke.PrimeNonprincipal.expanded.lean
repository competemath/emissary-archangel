import OAI.NumberTheory.DirichletL.Hecke.PrimeRow
import OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.HeckePrimeNonprincipal

-- @@ L9-9 verbatim
open HeckeFamily HeckeRowClosure CanonicalRowCompletion

-- @@ L10-10 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L12-21 verbatim
theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring


-- @@ L23-40 verbatim
theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]


-- @@ L42-42 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L43-43 verbatim
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L44-44 verbatim
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L46-50 verbatim
theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp


-- @@ L52-67 verbatim
theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]


-- @@ L69-69 verbatim
end SevenEighths.HeckePrimeNonprincipal


-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
