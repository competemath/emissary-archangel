import OAI.NumberTheory.DirichletL.Detector.RayNormalization


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical Topology

-- @@ L7-7 verbatim
open Filter

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeRaySlots

-- @@ L9-9 verbatim
open HeckeFamily ProbePhysical

-- @@ L10-10 verbatim
local notation "Id" => Ideal HeckeFamily.O


-- @@ L12-22 verbatim
lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring


-- @@ L24-50 verbatim
theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith


-- @@ L52-61 verbatim
theorem power_pool_tuples_eventually_injective {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀P:(∀i,pool C S (a i) (b i) (Z^(ell i))),
      Function.Injective (fun i=>(P i).val) := by
  filter_upwards [power_pools_eventually_disjoint C S a b ell ha hab hell] with Z hZ P
  intro i j heq
  by_contra hn
  have hq : (P i).val=(P j).val := heq
  exact Finset.disjoint_left.mp (hZ i j hn) (P i).property (by rw [hq];exact (P j).property)

-- @@ L62-62 verbatim
end SevenEighths.ProbeRaySlots

-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end OAI
