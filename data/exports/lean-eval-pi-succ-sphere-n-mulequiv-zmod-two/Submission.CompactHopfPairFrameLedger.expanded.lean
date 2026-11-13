import Mathlib
import Submission.CompactHopfPairFrameActual


-- @@ L4-11 verbatim
/-!
# The literal class-zero ledger of the compact Hopf pair

The exact fiber is the disjoint union of the two coordinate circles.  A
continuous quadratic sign separates them, so every tamed field has exactly
those two orbits.  The explicit intrinsic-frame calculations then identify
both orbit classes with zero and hence the all-positive ledger with `[0, 0]`.
-/


-- @@ L13-13 verbatim
set_option autoImplicit false

-- @@ L14-14 verbatim
set_option maxHeartbeats 1600000


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace Submission

-- @@ L19-19 verbatim
namespace CompactHopfPairConfiguration


-- @@ L21-21 verbatim
open Set Function Matrix InnerProductSpace

-- @@ L22-22 verbatim
open scoped Topology Matrix RealInnerProductSpace unitInterval


-- @@ L24-24 verbatim
variable (k : ℕ)


-- @@ L26-26 verbatim
local notation "hk" => Nat.succ_pos k

-- @@ L27-27 verbatim
local notation "Ek" => EuclideanSpace ℝ (Fin (k + 4))


-- @@ L29-29 verbatim
/-! ## A separating sign for the two coordinate circles -/


-- @@ L31-31 verbatim
def componentSignFun (x : Ek) : ℝ := x 0 ^ 2 + x 1 ^ 2 - 1 / 2


-- @@ L33-35 verbatim
theorem continuous_componentSignFun : Continuous (componentSignFun k) := by
  unfold componentSignFun
  fun_prop


-- @@ L37-40 verbatim
@[simp] theorem componentSignFun_first (theta : ℝ) :
    componentSignFun k (circleAt (m := k + 1) theta) = 1 / 2 := by
  simp [componentSignFun, circleAt_apply_zero, circleAt_apply_one]
  nlinarith [Real.cos_sq_add_sin_sq theta]


-- @@ L42-65 verbatim
@[simp] theorem componentSignFun_second (theta : ℝ) :
    componentSignFun k (secondCircleAt (k + 1) hk theta) = -1 / 2 := by
  have h02 : (0 : Fin (k + 4)) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv
  have h03 : (0 : Fin (k + 4)) ≠ 3 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv
  have h12 : (1 : Fin (k + 4)) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
      Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv
  have h13 : (1 : Fin (k + 4)) ≠ 3 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
      Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv
  simp [componentSignFun,
    secondCircleAt_apply_other (k + 1) hk theta h02 h03,
    secondCircleAt_apply_other (k + 1) hk theta h12 h13] <;>
    norm_num


-- @@ L67-74 verbatim
theorem componentSignFun_nonzero_of_mem_fiber {x : Ek}
    (hx : x ∈ (X (k + 1) hk).fiber) : componentSignFun k x ≠ 0 := by
  rw [X_fiber_eq_two_circles] at hx
  rcases hx with ⟨theta, rfl⟩ | ⟨theta, rfl⟩
  · rw [componentSignFun_first]
    norm_num
  · rw [componentSignFun_second]
    norm_num


-- @@ L76-79 verbatim
def componentSign : FiberSign (X (k + 1) hk) where
  toFun := componentSignFun k
  continuous := continuous_componentSignFun k
  nonzero := fun _ hx => componentSignFun_nonzero_of_mem_fiber k hx


-- @@ L81-83 verbatim
@[simp] theorem componentSign_first (theta : ℝ) :
    componentSign k (circleAt (m := k + 1) theta) = 1 / 2 :=
  componentSignFun_first k theta


-- @@ L85-87 verbatim
@[simp] theorem componentSign_second (theta : ℝ) :
    componentSign k (secondCircleAt (k + 1) hk theta) = -1 / 2 :=
  componentSignFun_second k theta


-- @@ L89-89 verbatim
/-! ## The two intrinsic orbit components -/


-- @@ L91-108 verbatim
theorem first_orbit_subset_standardCircle
    (V : TamedField (X (k + 1) hk)) :
    V.orbit (circleAt (m := k + 1) 0) ⊆
      (standardCircle : Set Ek) := by
  intro x hx
  have hp := firstCircleAt_mem_fiber k 0
  have hxfiber := V.orbit_subset_fiber hp hx
  have hbase : 0 < componentSign k (circleAt (m := k + 1) 0) := by
    rw [componentSign_first]
    norm_num
  have hxpos : 0 < componentSign k x :=
    ((componentSign k).pos_iff_of_mem_orbit V hp hx).mp hbase
  rw [X_fiber_eq_two_circles] at hxfiber
  rcases hxfiber with hfirst | hsecond
  · exact hfirst
  · rcases hsecond with ⟨theta, rfl⟩
    rw [componentSign_second] at hxpos
    norm_num at hxpos


-- @@ L110-130 verbatim
theorem second_orbit_subset_secondCircle
    (V : TamedField (X (k + 1) hk)) :
    V.orbit (secondCircleAt (k + 1) hk 0) ⊆
      secondCircle (k + 1) hk := by
  intro x hx
  have hp := secondCircleAt_mem_fiber k 0
  have hsign := (componentSign k).pos_iff_of_mem_orbit V hp hx
  have hbaseNot :
      ¬0 < componentSign k (secondCircleAt (k + 1) hk 0) := by
    rw [componentSign_second]
    norm_num
  have hxfiber := V.orbit_subset_fiber hp hx
  rw [X_fiber_eq_two_circles] at hxfiber
  rcases hxfiber with hfirst | hsecond
  · rcases hfirst with ⟨theta, rfl⟩
    have hfirstPos :
        0 < componentSign k (circleAt (m := k + 1) theta) := by
      rw [componentSign_first]
      norm_num
    exact False.elim (hbaseNot (hsign.mpr hfirstPos))
  · exact hsecond


-- @@ L132-139 verbatim
theorem first_orbit_eq_standardCircle
    (V : TamedField (X (k + 1) hk)) :
    V.orbit (circleAt (m := k + 1) 0) =
      (standardCircle : Set Ek) := by
  apply Set.Subset.antisymm
  · exact first_orbit_subset_standardCircle k V
  · rintro x ⟨theta, rfl⟩
    exact firstCircleAt_mem_orbit k V theta


-- @@ L141-148 verbatim
theorem second_orbit_eq_secondCircle
    (V : TamedField (X (k + 1) hk)) :
    V.orbit (secondCircleAt (k + 1) hk 0) =
      secondCircle (k + 1) hk := by
  apply Set.Subset.antisymm
  · exact second_orbit_subset_secondCircle k V
  · rintro x ⟨theta, rfl⟩
    exact secondCircleAt_mem_orbit k V theta


-- @@ L150-152 verbatim
def firstOrbitIndex (V : TamedField (X (k + 1) hk)) : V.OrbitIndex :=
  ⟨V.orbit (circleAt (m := k + 1) 0), V.mem_orbitFinset.mpr
    ⟨circleAt (m := k + 1) 0, firstCircleAt_mem_fiber k 0, rfl⟩⟩


-- @@ L154-156 verbatim
def secondOrbitIndex (V : TamedField (X (k + 1) hk)) : V.OrbitIndex :=
  ⟨V.orbit (secondCircleAt (k + 1) hk 0), V.mem_orbitFinset.mpr
    ⟨secondCircleAt (k + 1) hk 0, secondCircleAt_mem_fiber k 0, rfl⟩⟩


-- @@ L158-160 verbatim
@[simp] theorem firstOrbitIndex_coe (V : TamedField (X (k + 1) hk)) :
    ((firstOrbitIndex k V : V.OrbitIndex) : Set Ek) =
      V.orbit (circleAt (m := k + 1) 0) := rfl


-- @@ L162-164 verbatim
@[simp] theorem secondOrbitIndex_coe (V : TamedField (X (k + 1) hk)) :
    ((secondOrbitIndex k V : V.OrbitIndex) : Set Ek) =
      V.orbit (secondCircleAt (k + 1) hk 0) := rfl


-- @@ L166-182 verbatim
theorem firstOrbitIndex_ne_secondOrbitIndex
    (V : TamedField (X (k + 1) hk)) :
    firstOrbitIndex k V ≠ secondOrbitIndex k V := by
  intro hindex
  have hsets := congrArg (fun O : V.OrbitIndex => (O : Set Ek)) hindex
  change V.orbit (circleAt (m := k + 1) 0) =
    V.orbit (secondCircleAt (k + 1) hk 0) at hsets
  rw [first_orbit_eq_standardCircle k V,
    second_orbit_eq_secondCircle k V] at hsets
  have hfirst : circleAt (m := k + 1) 0 ∈ (standardCircle : Set Ek) :=
    ⟨0, rfl⟩
  have hsecond : circleAt (m := k + 1) 0 ∈
      secondCircle (k + 1) hk := by
    rw [← hsets]
    exact hfirst
  exact Set.disjoint_left.mp
    (standardCircle_disjoint_secondCircle (k + 1) hk) hfirst hsecond


-- @@ L184-200 verbatim
theorem orbitIndex_eq_first_or_second
    (V : TamedField (X (k + 1) hk)) (O : V.OrbitIndex) :
    O = firstOrbitIndex k V ∨ O = secondOrbitIndex k V := by
  have hp := V.orbitPoint_mem_fiber O
  rw [X_fiber_eq_two_circles] at hp
  rcases hp with ⟨theta, htheta⟩ | ⟨theta, htheta⟩
  · left
    apply Subtype.ext
    change (O : Set Ek) = V.orbit (circleAt (m := k + 1) 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (firstCircleAt_mem_orbit k V theta)
  · right
    apply Subtype.ext
    change (O : Set Ek) =
      V.orbit (secondCircleAt (k + 1) hk 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (secondCircleAt_mem_orbit k V theta)


-- @@ L202-213 verbatim
theorem orbitIndex_card (V : TamedField (X (k + 1) hk)) :
    Fintype.card V.OrbitIndex = 2 := by
  classical
  rw [← Finset.card_univ]
  have huniv : (Finset.univ : Finset V.OrbitIndex) =
      {firstOrbitIndex k V, secondOrbitIndex k V} := by
    ext O
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact orbitIndex_eq_first_or_second k V O
  rw [huniv]
  simp [firstOrbitIndex_ne_secondOrbitIndex k V]


-- @@ L215-215 verbatim
/-! ## Orbit classes and the literal ledger -/


-- @@ L217-235 verbatim
theorem first_orbitFrameClass_eq_zero
    (V : TamedField (X (k + 1) hk)) :
    V.orbitFrameClass (firstOrbitIndex k V) = 0 := by
  rw [V.orbitFrameClass_eq_fundamental]
  have hpoint : V.orbitPoint (firstOrbitIndex k V) ∈
      V.orbit (circleAt (m := k + 1) 0) := by
    rw [← firstOrbitIndex_coe k V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase := V.fundamentalFrameClass_eq_of_mem_orbit
    (firstCircleAt_mem_fiber k 0) hpoint
  calc
    V.fundamentalFrameClass
        (V.orbitPoint_mem_fiber (firstOrbitIndex k V)) =
      V.fundamentalFrameClass (firstCircleAt_mem_fiber k 0) := by
        simpa only using hbase
    _ = loopClassZ2 (firstSimpleClosedOrbitParam k V).paramFrameLoop
        (firstSimpleClosedOrbitParam k V).paramFrameLoop_closed :=
      (firstSimpleClosedOrbitParam k V).paramFrameClass_eq_fundamental.symm
    _ = 0 := first_paramFrameClass_eq_zero k V


-- @@ L237-255 verbatim
theorem second_orbitFrameClass_eq_zero
    (V : TamedField (X (k + 1) hk)) :
    V.orbitFrameClass (secondOrbitIndex k V) = 0 := by
  rw [V.orbitFrameClass_eq_fundamental]
  have hpoint : V.orbitPoint (secondOrbitIndex k V) ∈
      V.orbit (secondCircleAt (k + 1) hk 0) := by
    rw [← secondOrbitIndex_coe k V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase := V.fundamentalFrameClass_eq_of_mem_orbit
    (secondCircleAt_mem_fiber k 0) hpoint
  calc
    V.fundamentalFrameClass
        (V.orbitPoint_mem_fiber (secondOrbitIndex k V)) =
      V.fundamentalFrameClass (secondCircleAt_mem_fiber k 0) := by
        simpa only using hbase
    _ = loopClassZ2 (secondSimpleClosedOrbitParam k V).paramFrameLoop
        (secondSimpleClosedOrbitParam k V).paramFrameLoop_closed :=
      (secondSimpleClosedOrbitParam k V).paramFrameClass_eq_fundamental.symm
    _ = 0 := second_paramFrameClass_eq_zero k V


-- @@ L257-261 verbatim
theorem orbitFrameClass_eq_zero (V : TamedField (X (k + 1) hk))
    (O : V.OrbitIndex) : V.orbitFrameClass O = 0 := by
  rcases orbitIndex_eq_first_or_second k V O with h | h
  · rw [h, first_orbitFrameClass_eq_zero k V]
  · rw [h, second_orbitFrameClass_eq_zero k V]


-- @@ L263-267 verbatim
theorem allPositive_selects_orbit {Y : FramedLevelSet (k + 3)}
    (V : TamedField Y) (O : V.OrbitIndex) :
    (O : Set Ek) ∈ (FiberSign.allPositive Y).positiveOrbitCollection V := by
  rw [(FiberSign.allPositive Y).mem_positiveOrbitCollection_iff V O]
  simp


-- @@ L269-276 verbatim
def allPositiveSelectedOrbitEquiv {Y : FramedLevelSet (k + 3)}
    (V : TamedField Y) :
    V.SelectedOrbitIndex
        ((FiberSign.allPositive Y).positiveOrbitCollection V) ≃ V.OrbitIndex where
  toFun O := O.1
  invFun O := ⟨O, allPositive_selects_orbit k V O⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L278-298 verbatim
theorem positiveFrameLedger_eq_pair_zero
    (V : TamedField (X (k + 1) hk)) :
    (FiberSign.allPositive (X (k + 1) hk)).positiveFrameLedger V =
      [(0 : ZMod 2), 0] := by
  classical
  let L :=
    (FiberSign.allPositive (X (k + 1) hk)).positiveFrameLedger V
  have hlen : L.length = 2 := by
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.length_ofFn]
    rw [Fintype.card_congr (allPositiveSelectedOrbitEquiv k V),
      orbitIndex_card k V]
  have hall : ∀ z ∈ L, z = (0 : ZMod 2) := by
    intro z hz
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact orbitFrameClass_eq_zero k V _
  calc
    L = List.replicate L.length 0 := List.eq_replicate_length.mpr hall
    _ = [(0 : ZMod 2), 0] := by rw [hlen]; rfl


-- @@ L300-300 verbatim
end CompactHopfPairConfiguration

-- @@ L301-301 verbatim
end Submission
