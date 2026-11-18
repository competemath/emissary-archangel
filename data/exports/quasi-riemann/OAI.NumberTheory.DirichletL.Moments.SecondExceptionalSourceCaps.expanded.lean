import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamilyUniform


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
open Filter


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondExceptionalSourceCaps

-- @@ L10-10 verbatim
open HeckeFamily CenteredMomentSecondExceptionalFamily

-- @@ L11-11 verbatim
open CenteredMomentSecondExceptionalFamilyUniform

-- @@ L12-12 verbatim
local notation "O" => HeckeFamily.O


-- @@ L14-38 verbatim
theorem eventually_source_caps :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(η:Character)(R0:Ideal O)(H R B:ℝ),
      0≤B → 0≤H → 0≤R → (η.modulus.absNorm:ℝ)≤Z^B →
      (R0.absNorm:ℝ)≤Z^B → H≤Z^B → R≤Z^B →
      H≤Z^(5*B+1) ∧
      (expandedFactor η:ℝ)*R0.absNorm*H^2*(4*R)≤Z^(5*B+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*fixedExpandedCost)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro η R0 H R B hB hH hR hη hR0 hHN hRN
  have hz:0<Z:=zero_lt_one.trans hZ
  have hH2:H^2≤(Z^B)^2:=pow_le_pow_left₀ hH hHN 2
  have hbig:B≤5*B+1:=by linarith
  refine ⟨hHN.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hbig),?_⟩
  rw [expandedFactor_real]
  calc
    _=(4*fixedExpandedCost)*(η.modulus.absNorm:ℝ)*R0.absNorm*H^2*R:=by ring
    _≤Z*(Z^B)*(Z^B)*(Z^B)^2*(Z^B):=by gcongr
    _=Z^(5*B+1):=by
      rw [show (Z^B)^2=Z^B*Z^B by ring]
      calc
        _=Z^(1:ℝ)*Z^B*Z^B*(Z^B*Z^B)*Z^B:=by rw [Real.rpow_one]
        _=Z^(5*B+1):=by
          repeat rw [←Real.rpow_add hz]
          congr 1
          ring


-- @@ L40-40 verbatim
end SevenEighths.CenteredMomentSecondExceptionalSourceCaps


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end OAI
