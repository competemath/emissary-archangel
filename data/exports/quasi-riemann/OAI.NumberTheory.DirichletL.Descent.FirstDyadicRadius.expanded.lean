import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps
import OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms
import OAI.NumberTheory.DirichletL.Descent.FirstFullRapidTail


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical


-- @@ L10-10 verbatim
namespace SevenEighths.InverseMoment

-- @@ L11-11 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps

-- @@ L12-12 verbatim
open InverseSecondSourceBlocks

-- @@ L13-13 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L14-14 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L15-15 verbatim
variable {ι:Type*}[DecidableEq ι]


-- @@ L17-17 verbatim
def firstDyadicExponent (Z x:ℝ):ℝ:=dyadicExponent Z (dyadIndex x)


-- @@ L19-26 verbatim
theorem first_dyadic_bounds (Z eta x:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x):
    0≤firstDyadicExponent Z x ∧ Z^firstDyadicExponent Z x≤x ∧ x≤Z^(firstDyadicExponent Z x+eta):=by
  have hd:=dyadIndex_bounds x hx
  have he:=dyad_power_bounds Z eta x hZ hbin (dyadIndex x) ⟨hd.1,hd.2.le⟩
  refine ⟨?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Real.rpow_zero,firstDyadicExponent,rpow_dyadicExponent Z hZ]
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)


-- @@ L28-33 verbatim
def firstDyadicRadius (p:ι→O)(b:CubeCoordinates ι)(C D:Finset ι)
    (Z M r ell V eta tau:ℝ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (firstDyadicExponent Z (primeProductNorm p D))
    (firstDyadicExponent Z (primeProductNorm p C))
    (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau)


-- @@ L35-38 verbatim
def firstDyadicPhysicalCutoff (p:ι→O)(b:CubeCoordinates ι)(C:Finset ι)(I:Ideal O)
    (Z M r ell V eta tau:ℝ)(D:Finset ι):Finset O:=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (firstDyadicRadius p b C D Z M r ell V eta tau)


-- @@ L40-73 verbatim
theorem first_dyadic_radius_global_cap
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι)(C D:Finset ι)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (h₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)):
    firstDyadicRadius p b C D Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hC:=first_dyadic_bounds Z eta (primeProductNorm p C) hZ hbin (primeProductNorm_ge_one p hp C)
  have hd:=first_dyadic_bounds Z eta (primeProductNorm p D) hZ hbin (primeProductNorm_ge_one p hp D)
  have hj:=first_dyadic_bounds Z eta (‖eisEmbedding (jLabel p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) hZ hbin
    (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _))
  have hs:=cube_whole_support_dyad p hp b (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) h₁ h₂
  have hn:primeProductNorm p D≤Z^(firstDyadicExponent Z (primeProductNorm p C)+2*ell+3*eta):=by
    calc
      _≤primeProductNorm p (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):=
        primeProductNorm_mono p hp hD
      _≤primeProductNorm p C*primeProductNorm p b.support:=
        (primeProductNorm_union_le_mul p hp _ _).trans
          (mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _)) (primeProductNorm_pos p hp _).le)
      _≤Z^(firstDyadicExponent Z (primeProductNorm p C)+eta)*(Z^(ell+eta))^2:=
        mul_le_mul hC.2.2 hs (primeProductNorm_pos p hp _).le (Real.rpow_nonneg hz.le _)
      _=_:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
        congr 1
        norm_num
        ring
  have hde:= (Real.rpow_le_rpow_left_iff hZ).mp (hd.2.1.trans hn)
  unfold firstDyadicRadius firstPhysicalHeight
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith [hC.1,hj.1]


-- @@ L75-75 verbatim
end SevenEighths.InverseMoment


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
end OAI
