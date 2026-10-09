import OAI.Analysis.TreePotential.RealModuli


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
open Set Filter Topology

-- @@ L9-9 verbatim
open scoped Classical


-- @@ L11-11 verbatim
namespace BoundedTreePotentials

-- @@ L12-12 verbatim
section RealEndpointTransfer

-- @@ L13-13 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L15-18 verbatim
lemma averagedModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ averagedModulus E t) : a≤ averagedModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [averagedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]


-- @@ L20-23 verbatim
lemma maximumModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ maximumModulus E t) : a≤ maximumModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [maximumModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]


-- @@ L25-29 verbatim
lemma oneSidedModulusReal_zero (h : ¬IsAUC E) {t : ℝ}
    (ht : oneSidedModulus E t=0) : oneSidedModulusReal E t=0 := by
  apply EReal.coe_eq_coe_iff.mp
  rw [oneSidedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h),ht]
  rfl

-- @@ L30-30 verbatim
end RealEndpointTransfer


-- @@ L32-32 verbatim
namespace TreeCalculus


-- @@ L34-37 verbatim
theorem four_averaged_modulus_real (r : Bool) (k : QuadraticKind)
    {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    Real.sqrt (1+t^2/4)-1≤ averagedModulusReal (TestCompletion (treeTestFamily r k)) t :=
  averagedModulusReal_lower (four_no_equivalent_AUC r k (.refl ℝ _)) (four_averaged_modulus r k ht ht1)


-- @@ L39-45 verbatim
theorem four_renorming_obstruction_real (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β)
    (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (four_no_equivalent_AUC r k e) (four_renorming_obstruction r k e hα hαβ he)


-- @@ L47-50 verbatim
theorem four_no_equivalent_AUC_real (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (four_no_equivalent_AUC r k e)

-- @@ L51-51 verbatim
end TreeCalculus


-- @@ L53-53 verbatim
namespace FreeRoot


-- @@ L55-57 verbatim
theorem freeRoot_averaged_modulus_real {t : ℝ} (ht : 0< t) (ht1 : t<1) :
    (Real.sqrt (1+t^2/576)-1)/4≤ averagedModulusReal Space t :=
  averagedModulusReal_lower (freeRoot_no_equivalent_AUC (.refl ℝ _)) (freeRoot_averaged_modulus ht ht1)


-- @@ L59-63 verbatim
theorem freeRoot_renorming_obstruction_real {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) {α β : ℝ} (hα : 0<α) (hαβ : α≤β)
    (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(4*β))=0 :=
  oneSidedModulusReal_zero (freeRoot_no_equivalent_AUC e) (freeRoot_renorming_obstruction e hα hαβ he)


-- @@ L65-67 verbatim
theorem freeRoot_no_equivalent_AUC_real {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (freeRoot_no_equivalent_AUC e)

-- @@ L68-68 verbatim
end FreeRoot


-- @@ L70-70 verbatim
section CostRealObstructions

-- @@ L71-71 verbatim
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]


-- @@ L73-77 verbatim
theorem linearOuter_renorming_obstruction_real (e : LinearOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖)
    (ht : 0< t) (htb : t≤α/β) : oneSidedModulusReal Y t=0 :=
  oneSidedModulusReal_zero (linearOuter_no_equivalent_AUC e)
    (linearOuter_renorming_obstruction e hα hαβ he ht htb)


-- @@ L79-83 verbatim
theorem quadraticOuter_renorming_obstruction_real (e : QuadraticOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖)
    (ht : 0< t) (htb : t≤α/(Real.sqrt 2*β)) : oneSidedModulusReal Y t=0 :=
  oneSidedModulusReal_zero (quadraticOuter_no_equivalent_AUC e)
    (quadraticOuter_renorming_obstruction e hα hαβ he ht htb)


-- @@ L85-86 verbatim
theorem linearOuter_no_equivalent_AUC_real (e : LinearOuter ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (linearOuter_no_equivalent_AUC e)


-- @@ L88-89 verbatim
theorem quadraticOuter_no_equivalent_AUC_real (e : QuadraticOuter ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (quadraticOuter_no_equivalent_AUC e)

-- @@ L90-90 verbatim
end CostRealObstructions


-- @@ L92-92 verbatim
namespace CostHeads


-- @@ L94-96 verbatim
theorem linear_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal LinearOuter t :=
  averagedModulusReal_lower (linearOuter_no_equivalent_AUC (.refl ℝ _)) (linear_averaged_modulus ht)


-- @@ L98-100 verbatim
theorem quadratic_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal QuadraticOuter t :=
  averagedModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_averaged_modulus ht)


-- @@ L102-104 verbatim
theorem quadratic_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ maximumModulusReal QuadraticOuter t :=
  maximumModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_maximum_modulus ht)


-- @@ L106-111 verbatim
theorem quadratic_maximum_modulus_real_positive {t : ℝ} (ht : 0< t) :
    0< maximumModulusReal QuadraticOuter t := by
  apply EReal.coe_lt_coe_iff.mp
  rw [maximumModulusReal_coe QuadraticOuter
    (infiniteDimensional_of_not_isAUC _ (quadraticOuter_no_equivalent_AUC (.refl ℝ _)))]
  exact quadratic_maximum_modulus_positive ht

-- @@ L112-112 verbatim
end CostHeads


-- @@ L114-114 verbatim
namespace Segments


-- @@ L116-118 verbatim
theorem start_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/64)-1≤ maximumModulusReal StartSpace t :=
  maximumModulusReal_lower (start_no_equivalent_AUC (.refl ℝ _)) (start_maximum_modulus ht)


-- @@ L120-131 verbatim
theorem start_unit_sphere_bound_real (x : StartSpace) (hx : ‖x‖=1)
    {t ε : ℝ} (ht : 0< t) (hε : 0<ε) :
    ∃ F : ClosedFiniteCodim StartSpace,
      Real.sqrt (1+t^2/64)-ε≤⨅ y : {y : StartSpace // y ∈ F.space ∧ ‖y‖=1},
        max ‖x+t • y.val‖ ‖x-t • y.val‖ := by
  obtain ⟨F,hF⟩ := start_completed_tail_bound x hx ht hε
  obtain ⟨y,hy,hyn⟩ := F.unit_exists StartSpace
    (infiniteDimensional_of_not_isAUC _ (start_no_equivalent_AUC (.refl ℝ _)))
  have : Nonempty {y : StartSpace // y ∈ F.space ∧ ‖y‖=1} := ⟨⟨y,hy,hyn⟩⟩
  refine ⟨F,le_ciInf fun y => ?_⟩
  have hh := hF y.val y.property.1 y.property.2.ge
  linarith


-- @@ L133-133 verbatim
section RealObstructions

-- @@ L134-134 verbatim
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]


-- @@ L136-139 verbatim
theorem start_renorming_obstruction_real (e : StartSpace ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (start_no_equivalent_AUC e) (start_renorming_obstruction e hα hαβ he)


-- @@ L141-142 verbatim
theorem start_no_equivalent_AUC_real (e : StartSpace ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (start_no_equivalent_AUC e)


-- @@ L144-148 verbatim
theorem incomparable_renorming_obstruction_real (e : Dual ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0<α) (hαβ : α≤β) (he : ∀ x,α*‖x‖≤‖e x‖ ∧ ‖e x‖≤β*‖x‖) :
    oneSidedModulusReal Y (α/(2*β))=0 :=
  oneSidedModulusReal_zero (incomparable_no_equivalent_AUC e)
    (incomparable_renorming_obstruction e hα hαβ he)


-- @@ L150-151 verbatim
theorem incomparable_no_equivalent_AUC_real (e : Dual ≃L[ℝ] Y) : ¬IsAUCReal Y :=
  not_isAUCReal_of_not_isAUC Y (incomparable_no_equivalent_AUC e)

-- @@ L152-152 verbatim
end RealObstructions

-- @@ L153-153 verbatim
end Segments

-- @@ L154-154 verbatim
end BoundedTreePotentials



-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
