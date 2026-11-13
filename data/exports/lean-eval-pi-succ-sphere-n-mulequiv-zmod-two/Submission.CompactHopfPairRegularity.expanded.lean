import Mathlib
import Submission.CompactHopfPairConfiguration


-- @@ L4-10 verbatim
/-!
# Regularity of the compact Hopf-pair equation

The compactification agrees with its polynomial core near every zero.  This
file proves that the core differential is onto on both coordinate-circle
branches by writing down branchwise preimages for an arbitrary target vector.
-/


-- @@ L12-12 verbatim
set_option autoImplicit false


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace Submission

-- @@ L17-17 verbatim
namespace CompactHopfPairConfiguration


-- @@ L19-19 verbatim
open Set Function Metric InnerProductSpace

-- @@ L20-20 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L22-22 verbatim
variable (m : ℕ) (hm : 0 < m)


-- @@ L24-24 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L25-25 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L27-38 verbatim
private lemma fderiv_coord_apply
    (G : E → F) (hG : ContDiff ℝ ∞ G)
    (i : Fin (m + 2)) (x h : E) :
    fderiv ℝ (fun q => G q i) x h = fderiv ℝ G x h i := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj i
  have hG' : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => G q i)
      (outProj.comp (fderiv ℝ G x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (G x) i).comp x hG'
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hcomp.fderiv
  simpa [outProj] using happ


-- @@ L40-71 verbatim
lemma fderiv_coreMap_apply_zero (x h : E) :
    fderiv ℝ (coreMap m hm) x h 0 = ⟪x, h⟫_ℝ := by
  rw [← fderiv_coord_apply m (coreMap m hm) (contDiff_coreMap m hm) 0 x h]
  have hfun : (fun q : E => coreMap m hm q 0) =
      fun q => (‖q‖ ^ 2 - 1) / 2 := by
    funext q
    rw [coreMap_apply_zero, CompactBirth.normSq_eq_norm_sq]
  rw [hfun]
  have hnorm : HasFDerivAt (fun q : E => ‖q‖ ^ 2)
      (2 • innerSL ℝ x) x := by
    have hd : DifferentiableAt ℝ (fun q : E => ‖q‖ ^ 2) x := by
      rw [show (fun q : E => ‖q‖ ^ 2) = CompactBirth.normSq from by
        funext q
        exact (CompactBirth.normSq_eq_norm_sq q).symm]
      exact CompactBirth.contDiff_normSq.differentiable
        infty_ne_zero |>.differentiableAt
    rw [← fderiv_norm_sq_apply x]
    exact hd.hasFDerivAt
  have hder' := (hnorm.sub_const 1).const_mul (1 / 2 : ℝ)
  rw [show (fun q : E => (‖q‖ ^ 2 - 1) / 2) =
      fun q => (1 / 2 : ℝ) * (‖q‖ ^ 2 - 1) from by
    funext q
    ring]
  have hder : HasFDerivAt (fun q : E =>
      (1 / 2 : ℝ) * (‖q‖ ^ 2 - 1)) (innerSL ℝ x) x := by
    have hmap : (1 / 2 : ℝ) • (2 • innerSL ℝ x) = innerSL ℝ x := by
      ext v
      simp
    rw [hmap] at hder'
    exact hder'
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hder.fderiv
  simpa [innerSL_apply_apply] using happ


-- @@ L73-99 verbatim
lemma fderiv_coreMap_apply_one (x h : E) :
    fderiv ℝ (coreMap m hm) x h 1 =
      h 0 * x 2 + x 0 * h 2 + h 1 * x 3 + x 1 * h 3 := by
  rw [← fderiv_coord_apply m (coreMap m hm) (contDiff_coreMap m hm) 1 x h]
  have hfun : (fun q : E => coreMap m hm q 1) =
      fun q => q 0 * q 2 + q 1 * q 3 := by
    funext q
    rw [coreMap_apply_one]
    rfl
  rw [hfun]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := (h0.mul h2).add (h1.mul h3)
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd.fderiv
  change fderiv ℝ (((fun q : E => q 0) * fun q => q 2) +
      ((fun q : E => q 1) * fun q => q 3)) x h = _
  calc
    _ = x 0 * h 2 + x 2 * h 0 +
        (x 1 * h 3 + x 3 * h 1) := by
      simpa [p0, p1, p2, p3] using happ
    _ = _ := by ring


-- @@ L101-127 verbatim
lemma fderiv_coreMap_apply_two (x h : E) :
    fderiv ℝ (coreMap m hm) x h 2 =
      h 1 * x 2 + x 1 * h 2 - h 0 * x 3 - x 0 * h 3 := by
  rw [← fderiv_coord_apply m (coreMap m hm) (contDiff_coreMap m hm) 2 x h]
  have hfun : (fun q : E => coreMap m hm q 2) =
      fun q => q 1 * q 2 - q 0 * q 3 := by
    funext q
    rw [coreMap_apply_two]
    rfl
  rw [hfun]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := (h1.mul h2).sub (h0.mul h3)
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd.fderiv
  change fderiv ℝ (((fun q : E => q 1) * fun q => q 2) -
      ((fun q : E => q 0) * fun q => q 3)) x h = _
  calc
    _ = x 1 * h 2 + x 2 * h 1 -
        (x 0 * h 3 + x 3 * h 0) := by
      simpa [p0, p1, p2, p3] using happ
    _ = _ := by ring


-- @@ L129-138 verbatim
lemma fderiv_coreMap_apply_tail (x h : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    fderiv ℝ (coreMap m hm) x h i = h i.succ := by
  rw [← fderiv_coord_apply m (coreMap m hm) (contDiff_coreMap m hm) i x h]
  have hfun : (fun q : E => coreMap m hm q i) = fun q => q i.succ := by
    funext q
    exact coreMap_apply_tail m hm q hi0 hi1 hi2
  rw [hfun]
  exact congrArg (fun L : E →L[ℝ] ℝ => L h)
    (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).hasFDerivAt.fderiv


-- @@ L140-166 verbatim
lemma coordinate_eq_zero_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm x = 0) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2) (hj3 : j ≠ 3) :
    x j = 0 := by
  let i : Fin (m + 2) := j.pred hj0
  have hji : i.succ = j := Fin.succ_pred j hj0
  have hi0 : i ≠ 0 := by
    intro hi
    apply hj1
    rw [← hji, hi]
    rfl
  have hi1 : i ≠ 1 := by
    intro hi
    apply hj2
    rw [← hji, hi]
    rfl
  have hi2 : i ≠ 2 := by
    intro hi
    apply hj3
    rw [← hji, hi]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have hout := congrArg (fun q : F => q i) hx
  rw [coreMap_apply_tail m hm x hi0 hi1 hi2] at hout
  simp only [PiLp.zero_apply] at hout
  rwa [hji] at hout


-- @@ L168-198 verbatim
lemma first_branch_normSq {x : E} (hx : coreMap m hm x = 0)
    (hu : x 2 = 0 ∧ x 3 = 0) : x 0 ^ 2 + x 1 ^ 2 = 1 := by
  have hn := normSq_eq_one_of_coreMap_eq_zero m hm hx
  unfold CompactBirth.normSq at hn
  have hrest : ∀ j : Fin (m + 3), j ≠ 0 → j ≠ 1 → x j ^ 2 = 0 := by
    intro j hj0 hj1
    by_cases hj2 : j = 2
    · subst j
      simp [hu.1]
    · by_cases hj3 : j = 3
      · subst j
        simp [hu.2]
      · rw [coordinate_eq_zero_of_coreMap_eq_zero m hm hx hj0 hj1 hj2 hj3]
        norm_num
  have hkey : ∀ j : Fin (m + 3), x j ^ 2 =
      (if j = 0 then x 0 ^ 2 else 0) +
        (if j = 1 then x 1 ^ 2 else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp
    · by_cases hj1 : j = 1
      · subst j
        simp [hj0]
      · rw [if_neg hj0, if_neg hj1, add_zero, hrest j hj0 hj1]
  rw [Finset.sum_congr rfl fun j _ => hkey j,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (0 : Fin (m + 3)) (fun _ => x 0 ^ 2),
    Finset.sum_ite_eq' _ (1 : Fin (m + 3)) (fun _ => x 1 ^ 2),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)] at hn
  exact hn


-- @@ L200-233 verbatim
lemma second_branch_normSq {x : E} (hx : coreMap m hm x = 0)
    (hz : x 0 = 0 ∧ x 1 = 0) : x 2 ^ 2 + x 3 ^ 2 = 1 := by
  have hn := normSq_eq_one_of_coreMap_eq_zero m hm hx
  unfold CompactBirth.normSq at hn
  have hkey : ∀ j : Fin (m + 3), x j ^ 2 =
      (if j = 2 then x 2 ^ 2 else 0) +
        (if j = 3 then x 3 ^ 2 else 0) := by
    intro j
    by_cases hj2 : j = 2
    · subst j
      have h23 : (2 : Fin (m + 3)) ≠ 3 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
          Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
      simp [h23]
    · by_cases hj3 : j = 3
      · subst j
        simp [hj2]
      · rw [if_neg hj2, if_neg hj3, add_zero]
        by_cases hj0 : j = 0
        · subst j
          simp [hz.1]
        · by_cases hj1 : j = 1
          · subst j
            simp [hz.2]
          · rw [coordinate_eq_zero_of_coreMap_eq_zero m hm hx hj0 hj1 hj2 hj3]
            norm_num
  rw [Finset.sum_congr rfl fun j _ => hkey j,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (2 : Fin (m + 3)) (fun _ => x 2 ^ 2),
    Finset.sum_ite_eq' _ (3 : Fin (m + 3)) (fun _ => x 3 ^ 2),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)] at hn
  exact hn


-- @@ L235-235 verbatim
/-! ## Explicit branchwise preimages -/


-- @@ L237-243 verbatim
/-- A preimage for the differential on the branch `x₂=x₃=0`. -/
def firstPreimage (_hm : 0 < m) (x : E) (y : F) : E :=
  WithLp.toLp 2 <| Fin.cases (x 0 * y 0) fun i =>
    if i = 0 then x 1 * y 0
    else if i = 1 then x 0 * y 1 + x 1 * y 2
    else if i = 2 then x 1 * y 1 - x 0 * y 2
    else y i


-- @@ L245-247 verbatim
@[simp] lemma firstPreimage_apply_zero (x : E) (y : F) :
    firstPreimage m hm x y 0 = x 0 * y 0 := by
  simp [firstPreimage]


-- @@ L249-255 verbatim
@[simp] lemma firstPreimage_apply_succ (x : E) (y : F) (i : Fin (m + 2)) :
    firstPreimage m hm x y i.succ =
      if i = 0 then x 1 * y 0
      else if i = 1 then x 0 * y 1 + x 1 * y 2
      else if i = 2 then x 1 * y 1 - x 0 * y 2
      else y i := by
  simp [firstPreimage]


-- @@ L257-267 verbatim
@[simp] lemma firstPreimage_apply_one (x : E) (y : F) :
    firstPreimage m hm x y 1 = x 1 * y 0 := by
  have h1 : (1 : Fin (m + 3)) = (0 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp
  calc
    firstPreimage m hm x y 1 =
        firstPreimage m hm x y (0 : Fin (m + 2)).succ :=
      congrArg (fun j => firstPreimage m hm x y j) h1
    _ = _ := by
      simpa using firstPreimage_apply_succ m hm x y (0 : Fin (m + 2))


-- @@ L269-284 verbatim
@[simp] lemma firstPreimage_apply_two (x : E) (y : F) :
    firstPreimage m hm x y 2 = x 0 * y 1 + x 1 * y 2 := by
  have h2 : (2 : Fin (m + 3)) = (1 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    firstPreimage m hm x y 2 =
        firstPreimage m hm x y (1 : Fin (m + 2)).succ :=
      congrArg (fun j => firstPreimage m hm x y j) h2
    _ = _ := by
      simpa [h10] using firstPreimage_apply_succ m hm x y (1 : Fin (m + 2))


-- @@ L286-307 verbatim
@[simp] lemma firstPreimage_apply_three (x : E) (y : F) :
    firstPreimage m hm x y 3 = x 1 * y 1 - x 0 * y 2 := by
  have h3 : (3 : Fin (m + 3)) = (2 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    firstPreimage m hm x y 3 =
        firstPreimage m hm x y (2 : Fin (m + 2)).succ :=
      congrArg (fun j => firstPreimage m hm x y j) h3
    _ = _ := by
      simpa [h20, h21] using
        firstPreimage_apply_succ m hm x y (2 : Fin (m + 2))


-- @@ L309-312 verbatim
lemma firstPreimage_apply_tail (x : E) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    firstPreimage m hm x y i.succ = y i := by
  simp [firstPreimage, hi0, hi1, hi2]


-- @@ L314-320 verbatim
/-- A preimage for the differential on the branch `x₀=x₁=0`. -/
def secondPreimage (_hm : 0 < m) (x : E) (y : F) : E :=
  WithLp.toLp 2 <| Fin.cases (x 2 * y 1 - x 3 * y 2) fun i =>
    if i = 0 then x 3 * y 1 + x 2 * y 2
    else if i = 1 then x 2 * y 0
    else if i = 2 then x 3 * y 0
    else y i


-- @@ L322-324 verbatim
@[simp] lemma secondPreimage_apply_zero (x : E) (y : F) :
    secondPreimage m hm x y 0 = x 2 * y 1 - x 3 * y 2 := by
  simp [secondPreimage]


-- @@ L326-332 verbatim
@[simp] lemma secondPreimage_apply_succ (x : E) (y : F) (i : Fin (m + 2)) :
    secondPreimage m hm x y i.succ =
      if i = 0 then x 3 * y 1 + x 2 * y 2
      else if i = 1 then x 2 * y 0
      else if i = 2 then x 3 * y 0
      else y i := by
  simp [secondPreimage]


-- @@ L334-344 verbatim
@[simp] lemma secondPreimage_apply_one (x : E) (y : F) :
    secondPreimage m hm x y 1 = x 3 * y 1 + x 2 * y 2 := by
  have h1 : (1 : Fin (m + 3)) = (0 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp
  calc
    secondPreimage m hm x y 1 =
        secondPreimage m hm x y (0 : Fin (m + 2)).succ :=
      congrArg (fun j => secondPreimage m hm x y j) h1
    _ = _ := by
      simpa using secondPreimage_apply_succ m hm x y (0 : Fin (m + 2))


-- @@ L346-361 verbatim
@[simp] lemma secondPreimage_apply_two (x : E) (y : F) :
    secondPreimage m hm x y 2 = x 2 * y 0 := by
  have h2 : (2 : Fin (m + 3)) = (1 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    secondPreimage m hm x y 2 =
        secondPreimage m hm x y (1 : Fin (m + 2)).succ :=
      congrArg (fun j => secondPreimage m hm x y j) h2
    _ = _ := by
      simpa [h10] using secondPreimage_apply_succ m hm x y (1 : Fin (m + 2))


-- @@ L363-384 verbatim
@[simp] lemma secondPreimage_apply_three (x : E) (y : F) :
    secondPreimage m hm x y 3 = x 3 * y 0 := by
  have h3 : (3 : Fin (m + 3)) = (2 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    secondPreimage m hm x y 3 =
        secondPreimage m hm x y (2 : Fin (m + 2)).succ :=
      congrArg (fun j => secondPreimage m hm x y j) h3
    _ = _ := by
      simpa [h20, h21] using
        secondPreimage_apply_succ m hm x y (2 : Fin (m + 2))


-- @@ L386-389 verbatim
lemma secondPreimage_apply_tail (x : E) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    secondPreimage m hm x y i.succ = y i := by
  simp [secondPreimage, hi0, hi1, hi2]


-- @@ L391-395 verbatim
private lemma inner_eq_sum_local (x h : E) :
    ⟪x, h⟫_ℝ = ∑ j, x j * h j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [RCLike.inner_apply, mul_comm]


-- @@ L397-420 verbatim
lemma inner_firstPreimage {x : E} (hx : coreMap m hm x = 0)
    (hu : x 2 = 0 ∧ x 3 = 0) (y : F) :
    ⟪x, firstPreimage m hm x y⟫_ℝ = y 0 := by
  rw [inner_eq_sum_local]
  have hpoint : ∀ j : Fin (m + 3),
      x j * firstPreimage m hm x y j = x j ^ 2 * y 0 := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [pow_two, mul_assoc]
    · by_cases hj1 : j = 1
      · subst j
        simp [pow_two, mul_assoc]
      · by_cases hj2 : j = 2
        · subst j
          simp [hu.1]
        · by_cases hj3 : j = 3
          · subst j
            simp [hu.2]
          · rw [coordinate_eq_zero_of_coreMap_eq_zero m hm hx hj0 hj1 hj2 hj3]
            simp
  rw [Finset.sum_congr rfl fun j _ => hpoint j, ← Finset.sum_mul]
  change CompactBirth.normSq x * y 0 = y 0
  rw [normSq_eq_one_of_coreMap_eq_zero m hm hx, one_mul]


-- @@ L422-445 verbatim
lemma inner_secondPreimage {x : E} (hx : coreMap m hm x = 0)
    (hz : x 0 = 0 ∧ x 1 = 0) (y : F) :
    ⟪x, secondPreimage m hm x y⟫_ℝ = y 0 := by
  rw [inner_eq_sum_local]
  have hpoint : ∀ j : Fin (m + 3),
      x j * secondPreimage m hm x y j = x j ^ 2 * y 0 := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [hz.1]
    · by_cases hj1 : j = 1
      · subst j
        simp [hz.2]
      · by_cases hj2 : j = 2
        · subst j
          simp [pow_two, mul_assoc]
        · by_cases hj3 : j = 3
          · subst j
            simp [pow_two, mul_assoc]
          · rw [coordinate_eq_zero_of_coreMap_eq_zero m hm hx hj0 hj1 hj2 hj3]
            simp
  rw [Finset.sum_congr rfl fun j _ => hpoint j, ← Finset.sum_mul]
  change CompactBirth.normSq x * y 0 = y 0
  rw [normSq_eq_one_of_coreMap_eq_zero m hm hx, one_mul]


-- @@ L447-476 verbatim
lemma fderiv_coreMap_firstPreimage {x : E} (hx : coreMap m hm x = 0)
    (hu : x 2 = 0 ∧ x 3 = 0) (y : F) :
    fderiv ℝ (coreMap m hm) x (firstPreimage m hm x y) = y := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_coreMap_apply_zero, inner_firstPreimage m hm hx hu y]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_coreMap_apply_one]
      simp only [firstPreimage_apply_zero, firstPreimage_apply_one,
        firstPreimage_apply_two, firstPreimage_apply_three, hu.1, hu.2,
        mul_zero, zero_mul, zero_add]
      have hn := first_branch_normSq m hm hx hu
      calc
        _ = (x 0 ^ 2 + x 1 ^ 2) * y 1 := by ring
        _ = y 1 := by rw [hn, one_mul]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_coreMap_apply_two]
        simp only [firstPreimage_apply_zero, firstPreimage_apply_one,
          firstPreimage_apply_two, firstPreimage_apply_three, hu.1, hu.2,
          mul_zero, zero_mul, zero_add, sub_zero]
        have hn := first_branch_normSq m hm hx hu
        calc
          _ = (x 0 ^ 2 + x 1 ^ 2) * y 2 := by ring
          _ = y 2 := by rw [hn, one_mul]
      · rw [fderiv_coreMap_apply_tail m hm x _ hi0 hi1 hi2,
          firstPreimage_apply_tail m hm x y hi0 hi1 hi2]


-- @@ L478-507 verbatim
lemma fderiv_coreMap_secondPreimage {x : E} (hx : coreMap m hm x = 0)
    (hz : x 0 = 0 ∧ x 1 = 0) (y : F) :
    fderiv ℝ (coreMap m hm) x (secondPreimage m hm x y) = y := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_coreMap_apply_zero, inner_secondPreimage m hm hx hz y]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_coreMap_apply_one]
      simp only [secondPreimage_apply_zero, secondPreimage_apply_one,
        secondPreimage_apply_two, secondPreimage_apply_three, hz.1, hz.2,
        mul_zero, zero_mul, zero_add]
      have hn := second_branch_normSq m hm hx hz
      calc
        _ = (x 2 ^ 2 + x 3 ^ 2) * y 1 := by ring
        _ = y 1 := by rw [hn, one_mul]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_coreMap_apply_two]
        simp only [secondPreimage_apply_zero, secondPreimage_apply_one,
          secondPreimage_apply_two, secondPreimage_apply_three, hz.1, hz.2,
          mul_zero, zero_mul, zero_add, sub_zero]
        have hn := second_branch_normSq m hm hx hz
        calc
          _ = (x 2 ^ 2 + x 3 ^ 2) * y 2 := by ring
          _ = y 2 := by rw [hn, one_mul]
      · rw [fderiv_coreMap_apply_tail m hm x _ hi0 hi1 hi2,
          secondPreimage_apply_tail m hm x y hi0 hi1 hi2]


-- @@ L509-517 verbatim
theorem surjective_fderiv_coreMap_of_eq_zero {x : E}
    (hx : coreMap m hm x = 0) :
    Function.Surjective (fderiv ℝ (coreMap m hm) x) := by
  intro y
  rcases plane_dichotomy_of_coreMap_eq_zero m hm hx with hz | hu
  · exact ⟨secondPreimage m hm x y,
      fderiv_coreMap_secondPreimage m hm hx hz y⟩
  · exact ⟨firstPreimage m hm x y,
      fderiv_coreMap_firstPreimage m hm hx hu y⟩


-- @@ L519-526 verbatim
lemma levelMap_eventuallyEq_coreMap {x : E}
    (hx : CompactBirth.normSq x < 2) :
    levelMap m hm =ᶠ[nhds x] coreMap m hm := by
  have hopen : IsOpen {z : E | CompactBirth.normSq z < 2} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => by
    rw [levelMap, CompactBirth.cutoff_eq_zero hz.le]
    simp


-- @@ L528-535 verbatim
theorem surjective_fderiv_levelMap_of_eq_zero {x : E}
    (hx : levelMap m hm x = 0) :
    Function.Surjective (fderiv ℝ (levelMap m hm) x) := by
  have hxcore := (levelMap_eq_zero_iff_coreMap_eq_zero m hm x).mp hx
  have hn := normSq_eq_one_of_coreMap_eq_zero m hm hxcore
  have hlt : CompactBirth.normSq x < 2 := by rw [hn]; norm_num
  rw [(levelMap_eventuallyEq_coreMap m hm hlt).fderiv_eq]
  exact surjective_fderiv_coreMap_of_eq_zero m hm hxcore


-- @@ L537-551 verbatim
/-- The compact Hopf pair, packaged as a genuine framed level set. -/
def X : FramedLevelSet (m + 2) where
  g := levelMap m hm
  smooth := contDiff_levelMap m hm
  fiber_bounded := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hxcore := (levelMap_eq_zero_iff_coreMap_eq_zero m hm x).mp hx
    have hn := normSq_eq_one_of_coreMap_eq_zero m hm hxcore
    rw [CompactBirth.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg x]
  regular := by
    intro x hx
    exact surjective_fderiv_levelMap_of_eq_zero m hm hx


-- @@ L553-554 verbatim
theorem X_fiber (x : E) : x ∈ (X m hm).fiber ↔ coreMap m hm x = 0 := by
  exact levelMap_eq_zero_iff_coreMap_eq_zero m hm x


-- @@ L556-560 verbatim
theorem flatOutside :
    (X m hm).FlatOutside (background m hm) 0 2 := by
  intro x hx
  have hn : 2 ≤ ‖x‖ := by simpa [dist_zero_right] using hx
  exact levelMap_flatOutside m hm hn


-- @@ L562-565 verbatim
def positiveSign : FiberSign (X m hm) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L567-567 verbatim
end CompactHopfPairConfiguration

-- @@ L568-568 verbatim
end Submission
