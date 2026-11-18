import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical Topology

-- @@ L8-8 verbatim
open Filter

-- @@ L9-9 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L10-10 verbatim
open HeckeFamily HeckeInverseAmplification

-- @@ L11-11 verbatim
local notation "O" => HeckeFamily.O


-- @@ L13-41 verbatim
theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)


-- @@ L43-53 verbatim
theorem ray_cube_conductor_eventually (M : Ideal O) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually
    ((conductorConstant*M.absNorm:ℕ):ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu
  calc
    _ = ((conductorConstant*M.absNorm:ℕ):ℝ)*rowNorm u := by simp [rowNorm]
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring


-- @@ L55-55 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
