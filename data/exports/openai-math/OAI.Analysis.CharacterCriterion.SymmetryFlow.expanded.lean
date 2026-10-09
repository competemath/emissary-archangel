import OAI.Analysis.CharacterCriterion.FourLegSymmetries


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L22-22 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L24-24 verbatim
open Filter Topology

-- @@ L25-25 verbatim
open Topology

-- @@ L26-26 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L27-27 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L28-28 verbatim
open NormedSpace

-- @@ L29-29 verbatim
open scoped ComplexOrder

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped InnerProductSpace


-- @@ L33-33 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L34-34 verbatim
namespace KirchbergRordam.SymmetryFlow


-- @@ L36-36 verbatim
variable {A : Type*} [CStarAlgebra A]


-- @@ L38-38 verbatim
def phase (t : ℝ) : ℂ := Complex.exp ((t * Real.pi) * Complex.I)


-- @@ L40-40 verbatim
@[fun_prop] lemma phase_continuous : Continuous phase := by unfold phase; fun_prop

-- @@ L41-41 verbatim
@[simp] lemma phase_zero : phase 0 = 1 := by simp [phase]

-- @@ L42-42 verbatim
@[simp] lemma phase_one : phase 1 = -1 := by simp [phase, Complex.exp_pi_mul_I]

-- @@ L43-47 verbatim
lemma phase_unitary (t : ℝ) : star (phase t) * phase t = 1 := by
  have hn : ‖phase t‖ = 1 := by
    simpa [phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t * Real.pi)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
  norm_num


-- @@ L49-50 verbatim
def involutionValue (U : A) (t : ℝ) : A :=
  ((1 + phase t) / 2) • (1:A) + ((1 - phase t) / 2) • U


-- @@ L52-54 verbatim
lemma involutionValue_continuous (U : A) : Continuous (involutionValue U) := by
  unfold involutionValue
  fun_prop


-- @@ L56-91 verbatim
lemma involutionValue_unitary (U : A) (hs : star U = U) (hm : U * U = 1)
    (t : ℝ) : involutionValue U t ∈ unitary A := by
  have hz := phase_unitary t
  have h1 : (star ((1:ℂ)+phase t)/2)*((1+phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1-phase t)/2)=1 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1+star (phase t)*phase t)/2 := by ring
      _ = 1 := by rw [hz]; norm_num
  have h2 : (star ((1:ℂ)+phase t)/2)*((1-phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1+phase t)/2)=0 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1-star (phase t)*phase t)/2 := by ring
      _ = 0 := by rw [hz]; norm_num
  have h : star (involutionValue U t) * involutionValue U t = 1 := by
    simp only [involutionValue, star_add, star_smul, star_one, hs, star_div₀,
      star_ofNat, star_sub, smul_add, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, one_mul, mul_one, hm]
    calc
      _ = (((1+star (phase t))/2)*((1+phase t)/2)+
            ((1-star (phase t))/2)*((1-phase t)/2)) • (1:A) +
          (((1+star (phase t))/2)*((1-phase t)/2)+
            ((1-star (phase t))/2)*((1+phase t)/2)) • U := by
              rw [add_smul, add_smul]; module
      _ = 1 := by
        simp only [star_add, star_sub, star_one] at h1 h2
        rw [h1, h2, one_smul, zero_smul, add_zero]
  refine ⟨h, ?_⟩
  have hc : Commute (involutionValue U t) (star (involutionValue U t)) := by
    unfold involutionValue
    simp only [star_add, star_smul, star_one, hs]
    exact ((Commute.one_left _).smul_left _).add_left
      ((((Commute.one_right U).smul_right _).add_right
        ((Commute.refl U).smul_right _)).smul_left _)
  exact hc.eq.trans h



-- @@ L94-96 verbatim
def flow (U : unitary A) (hs : star (U:A)=U) (t : ℝ) : unitary A :=
  ⟨involutionValue (U:A) t,
    involutionValue_unitary (U:A) hs (by simpa only [hs] using Unitary.coe_star_mul_self U) t⟩

-- @@ L97-98 verbatim
@[simp] lemma coe_flow (U : unitary A) (hs) (t : ℝ) :
    (flow U hs t : A) = involutionValue (U:A) t := rfl

-- @@ L99-101 verbatim
@[simp] lemma flow_zero (U : unitary A) (hs) : flow U hs 0=1 := by
  apply Subtype.ext
  simp [involutionValue]

-- @@ L102-104 verbatim
@[simp] lemma flow_one (U : unitary A) (hs) : flow U hs 1=U := by
  apply Subtype.ext
  simp [involutionValue]

-- @@ L105-106 verbatim
@[fun_prop] lemma flow_continuous (U : unitary A) (hs) : Continuous (flow U hs) :=
  (involutionValue_continuous _).subtype_mk _

-- @@ L107-109 verbatim
lemma phase_add (s t : ℝ) : phase (s+t)=phase s*phase t := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, add_mul, Complex.exp_add]

-- @@ L110-122 verbatim
lemma flow_add (U : unitary A) (hs) (s t : ℝ) :
    flow U hs (s+t)=flow U hs s*flow U hs t := by
  apply Subtype.ext
  have hm : (U:A)*(U:A)=1 := by simpa only [hs] using Unitary.coe_star_mul_self U
  change involutionValue (U:A) (s+t)=involutionValue (U:A) s*involutionValue (U:A) t
  simp only [involutionValue,phase_add,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    one_mul,mul_one,hm]
  have h1 : (1+phase s*phase t)/2 = (1+phase s)/2*((1+phase t)/2)+
      (1-phase s)/2*((1-phase t)/2) := by ring
  have h2 : (1-phase s*phase t)/2 = (1+phase s)/2*((1-phase t)/2)+
      (1-phase s)/2*((1+phase t)/2) := by ring
  rw [h1,h2,add_smul,add_smul]
  module

-- @@ L123-127 verbatim
lemma flow_neg (U : unitary A) (hs) (t : ℝ) :
    flow U hs (-t)=star (flow U hs t) := by
  have h := flow_add U hs (-t) t
  rw [neg_add_cancel,flow_zero] at h
  exact (eq_inv_iff_mul_eq_one.mpr h.symm).trans rfl

-- @@ L128-130 verbatim
lemma flow_commute (U : unitary A) (hs) (a : A) (ha : Commute (U:A) a) (t : ℝ) :
    Commute (flow U hs t : A) a :=
  ((Commute.one_left a).smul_left _).add_left (ha.smul_left _)

-- @@ L131-134 verbatim
lemma flow_map {B : Type*} [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B)
    (U : unitary A) (hs) (t : ℝ) :
    φ (flow U hs t) = involutionValue (φ U) t := by
  simp only [coe_flow,involutionValue,map_add,map_smul,map_one]

-- @@ L135-135 verbatim
end KirchbergRordam.SymmetryFlow



-- @@ L138-138 verbatim
namespace KirchbergRordam.UnitaryConjugacySquare

-- @@ L139-139 verbatim
open Filter Topology

-- @@ L140-140 verbatim
open scoped CStarAlgebra

-- @@ L141-141 verbatim
variable {A : Type*} [CStarAlgebra A]


-- @@ L143-147 verbatim
structure Flow (A : Type*) [CStarAlgebra A] where
  toFun : ℝ → unitary A
  continuous_toFun : Continuous toFun
  zero : toFun 0=1
  add : ∀ s t, toFun (s+t)=toFun s*toFun t

-- @@ L148-148 verbatim
instance : CoeFun (Flow A) (fun _ => ℝ → unitary A) := ⟨Flow.toFun⟩

-- @@ L149-149 verbatim
@[simp] lemma flow_zero (V : Flow A) : V 0=1 := V.zero

-- @@ L150-150 verbatim
lemma flow_add (V : Flow A) (s t : ℝ) : V (s+t)=V s*V t := V.add s t

-- @@ L151-154 verbatim
lemma flow_neg (V : Flow A) (s : ℝ) : V (-s)=star (V s) := by
  have h := V.add (-s) s
  rw [neg_add_cancel,V.zero] at h
  exact (eq_inv_iff_mul_eq_one.mpr h.symm).trans rfl

-- @@ L155-155 verbatim
@[fun_prop] lemma flow_continuous (V : Flow A) : Continuous V := V.continuous_toFun


-- @@ L157-161 verbatim
def symmetry (u : unitary A) (hu : star (u:A)=u) : Flow A where
  toFun := SymmetryFlow.flow u hu
  continuous_toFun := SymmetryFlow.flow_continuous u hu
  zero := SymmetryFlow.flow_zero u hu
  add := SymmetryFlow.flow_add u hu


-- @@ L163-163 verbatim
abbrev Square := unitInterval × unitInterval


-- @@ L165-165 verbatim
def radius (x : Square) : ℝ := (x.1:ℝ)+(x.2:ℝ)-(x.1:ℝ)*(x.2:ℝ)

-- @@ L166-166 verbatim
def ratio (x : Square) : ℝ := (x.2:ℝ)/radius x

-- @@ L167-167 verbatim
@[fun_prop] lemma radius_continuous : Continuous radius := by unfold radius; fun_prop

-- @@ L168-172 verbatim
lemma radius_nonneg (x : Square) : 0 ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith

-- @@ L173-177 verbatim
lemma fst_le_radius (x : Square) : (x.1:ℝ) ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith

-- @@ L178-182 verbatim
lemma snd_le_radius (x : Square) : (x.2:ℝ) ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith

-- @@ L183-187 verbatim
lemma radius_le_one (x : Square) : radius x ≤ 1 := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith [mul_nonneg (sub_nonneg.mpr h11) (sub_nonneg.mpr h21)]

-- @@ L188-197 verbatim
lemma radius_eq_zero_iff (x : Square) : radius x=0 ↔ x=(0,0) := by
  constructor
  · intro h
    have h1 := fst_le_radius x; have h2 := snd_le_radius x
    rw [h] at h1 h2
    apply Prod.ext <;> apply Subtype.ext
    · exact le_antisymm h1 x.1.property.1
    · exact le_antisymm h2 x.2.property.1
  · rintro rfl
    simp [radius]

-- @@ L198-199 verbatim
lemma ratio_nonneg (x : Square) : 0 ≤ ratio x :=
  div_nonneg x.2.property.1 (radius_nonneg x)

-- @@ L200-203 verbatim
lemma ratio_le_one (x : Square) : ratio x ≤ 1 := by
  by_cases h : radius x=0
  · simp [ratio,h]
  · exact (div_le_one₀ ((radius_nonneg x).lt_of_ne' h)).mpr (snd_le_radius x)

-- @@ L204-205 verbatim
lemma scaled_ratio_nonneg (x : Square) : 0 ≤ (x.1:ℝ)*ratio x :=
  mul_nonneg x.1.property.1 (ratio_nonneg x)

-- @@ L206-207 verbatim
lemma scaled_ratio_le (x : Square) : (x.1:ℝ)*ratio x ≤ (x.1:ℝ) := by
  simpa using mul_le_mul_of_nonneg_left (ratio_le_one x) x.1.property.1

-- @@ L208-211 verbatim
lemma scaled_ratio_tendsto : Tendsto (fun x : Square => (x.1:ℝ)*ratio x)
    (𝓝 (0,0)) (𝓝 0) := by
  apply squeeze_zero scaled_ratio_nonneg scaled_ratio_le
  exact (continuous_subtype_val.comp continuous_fst).continuousAt



-- @@ L214-215 verbatim
def square (V : Flow A) (U : ℝ → unitary A) (x : Square) : unitary A :=
  V (ratio x)*U (radius x)*V (-((1-(x.1:ℝ))*ratio x))


-- @@ L217-218 verbatim
lemma square_origin (V : Flow A) (U : ℝ → unitary A) (hU : U 0=1) :
    square V U (0,0)=1 := by simp [square,ratio,radius,hU]


-- @@ L220-236 verbatim
lemma square_error (V : Flow A) (U : ℝ → unitary A) (x : Square) :
    ‖(square V U x:A)-1‖ ≤
      ‖(U (radius x):A)-1‖+‖(V ((x.1:ℝ)*ratio x):A)-1‖ := by
  let a := ratio x
  let c := -((1-(x.1:ℝ))*ratio x)
  have he : a+c=(x.1:ℝ)*ratio x := by dsimp [a,c]; ring
  have hv : (V a:A)*(V c:A)=V ((x.1:ℝ)*ratio x) := by
    rw [← (unitary A).coe_mul,← flow_add,he]
  have hd : (square V U x:A)-1 =
      (V a:A)*((U (radius x):A)-1)*(V c:A)+((V a:A)*(V c:A)-1) := by
    change (V a:A)*(U (radius x):A)*(V c:A)-1=_
    noncomm_ring
  rw [hd]
  calc
    _ ≤ ‖(V a:A)*((U (radius x):A)-1)*(V c:A)‖+
        ‖(V a:A)*(V c:A)-1‖ := norm_add_le _ _
    _ = _ := by rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,hv]


-- @@ L238-268 verbatim
lemma square_continuous (V : Flow A) (U : ℝ → unitary A)
    (hU : Continuous U) (hzero : U 0=1) : Continuous (square V U) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=(0,0)
  · subst x
    have hr : Tendsto (fun x : Square => ‖(U (radius x):A)-1‖) (𝓝 (0,0)) (𝓝 0) := by
      have h := ((continuous_subtype_val.comp hU).comp radius_continuous).continuousAt (x:=(0,0))
      have h' := (h.sub (tendsto_const_nhds (x := (1:A)))).norm
      simpa [radius,hzero] using h'.tendsto
    have hv : Tendsto (fun x : Square => ‖(V ((x.1:ℝ)*ratio x):A)-1‖)
        (𝓝 (0,0)) (𝓝 0) := by
      have h := ((continuous_subtype_val.comp V.continuous_toFun).continuousAt (x:=0)).tendsto.comp scaled_ratio_tendsto
      have h' := (h.sub (tendsto_const_nhds (x := (1:A)))).norm
      simpa using h'
    have hnorm := squeeze_zero (fun x : Square => norm_nonneg ((square V U x:A)-1))
      (square_error V U) (by simpa using hr.add hv)
    change Tendsto (fun x : Square => (square V U x:A)) (𝓝 (0,0)) (𝓝 (square V U (0,0):A))
    rw [show (square V U (0,0):A)=1 by rw [square_origin V U hzero]; rfl]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  · have hr : ContinuousAt ratio x := by
      unfold ratio
      exact (continuous_subtype_val.comp continuous_snd).continuousAt.div
        radius_continuous.continuousAt (fun h => hx ((radius_eq_zero_iff x).mp h))
    have hc : ContinuousAt (fun y : Square => -((1-(y.1:ℝ))*ratio y)) x :=
      ((continuousAt_const.sub (continuous_subtype_val.comp continuous_fst).continuousAt).mul hr).neg
    apply continuous_subtype_val.continuousAt.comp
    exact ((V.continuous_toFun.continuousAt.comp hr).mul
      (hU.continuousAt.comp radius_continuous.continuousAt)).mul
      (V.continuous_toFun.continuousAt.comp hc)


-- @@ L270-271 verbatim
lemma square_bottom (V : Flow A) (U : ℝ → unitary A) (s : unitInterval) :
    square V U (s,0)=U s := by simp [square,ratio,radius]

-- @@ L272-273 verbatim
lemma square_right (V : Flow A) (U : ℝ → unitary A) (t : unitInterval) :
    square V U (1,t)=V t*U 1 := by simp [square,ratio,radius]

-- @@ L274-281 verbatim
lemma square_top (V : Flow A) (U : ℝ → unitary A) (s : unitInterval) :
    square V U (s,1)=V 1*U 1*star (V 1)*V s := by
  have hr : radius (s,1)=1 := by simp [radius]
  have ha : ratio (s,1)=1 := by simp [ratio,hr]
  have h : -((1:ℝ)-(s:ℝ)) = -1+(s:ℝ) := by ring
  change V (ratio (s,1))*U (radius (s,1))*V (-((1-(s:ℝ))*ratio (s,1)))=_
  rw [hr,ha,mul_one,h,flow_add,flow_neg,mul_assoc]
  simp only [mul_assoc]

-- @@ L282-288 verbatim
lemma square_left (V : Flow A) (U : ℝ → unitary A) (hzero : U 0=1)
    (t : unitInterval) : square V U (0,t)=V 1*U t*star (V 1) := by
  by_cases ht : (t:ℝ)=0
  · have he : t=0 := Subtype.ext ht
    subst t
    simp [square_origin V U hzero,hzero]
  · simp [square,ratio,radius,ht,flow_neg]

-- @@ L289-289 verbatim
end KirchbergRordam.UnitaryConjugacySquare



-- @@ L292-292 verbatim
namespace KirchbergRordam.SymmetryConjugacyDiagram

-- @@ L293-293 verbatim
open UnitaryConjugacySquare

-- @@ L294-294 verbatim
variable {A : Type*} [CStarAlgebra A]


-- @@ L296-304 verbatim
structure Data (A : Type*) [CStarAlgebra A] where
  H : unitary A
  K : unitary A
  hH : star (H:A)=H
  hK : star (K:A)=K
  commute : Commute H K
  L : unitInterval → unitary A
  continuous_L : Continuous L
  L_zero : L 0=1


-- @@ L306-306 verbatim
namespace Data

-- @@ L307-307 verbatim
variable (D : Data A)

-- @@ L308-308 verbatim
def Hp : Flow A := symmetry D.H D.hH

-- @@ L309-309 verbatim
def Kp : Flow A := symmetry D.K D.hK

-- @@ L310-310 verbatim
def U (r : ℝ) : unitary A := star (D.L 1)*D.Hp r*D.L 1

-- @@ L311-311 verbatim
def R (t : unitInterval) : unitary A := D.H*D.K*D.L t*star (D.H*D.K)

-- @@ L312-313 verbatim
def W (x : Square) : unitary A :=
  D.R x.2*D.H*square D.Kp D.U x*star (D.L x.1)


-- @@ L315-315 verbatim
@[simp] lemma Hp_one : D.Hp 1=D.H := SymmetryFlow.flow_one D.H D.hH

-- @@ L316-316 verbatim
@[simp] lemma Kp_one : D.Kp 1=D.K := SymmetryFlow.flow_one D.K D.hK

-- @@ L317-317 verbatim
@[simp] lemma H_star : star D.H=D.H := Subtype.ext D.hH

-- @@ L318-318 verbatim
@[simp] lemma K_star : star D.K=D.K := Subtype.ext D.hK

-- @@ L319-319 verbatim
lemma H_inv : D.H⁻¹=D.H := D.H_star

-- @@ L320-320 verbatim
lemma K_inv : D.K⁻¹=D.K := D.K_star

-- @@ L321-324 verbatim
lemma Hp_commute (r : ℝ) : Commute (D.Hp r) D.K := by
  apply Subtype.ext
  exact SymmetryFlow.flow_commute D.H D.hH (D.K:A)
    (show Commute (D.H:A) (D.K:A) from congrArg Subtype.val D.commute.eq) r

-- @@ L325-328 verbatim
lemma Kp_commute (r : ℝ) : Commute D.H (D.Kp r) := by
  apply Subtype.ext
  exact (SymmetryFlow.flow_commute D.K D.hK (D.H:A)
    (show Commute (D.K:A) (D.H:A) from congrArg Subtype.val D.commute.symm.eq) r).symm

-- @@ L329-329 verbatim
@[simp] lemma U_zero : D.U 0=1 := by simp [U]

-- @@ L330-331 verbatim
@[simp] lemma R_zero : D.R 0=1 := by
  simpa only [R,D.L_zero,mul_one,Unitary.star_eq_inv] using mul_inv_cancel (D.H*D.K)

-- @@ L332-332 verbatim
@[simp] lemma HH : D.H*D.H=1 := by simpa only [D.H_inv] using inv_mul_cancel D.H

-- @@ L333-333 verbatim
@[simp] lemma KK : D.K*D.K=1 := by simpa only [D.K_inv] using inv_mul_cancel D.K

-- @@ L334-334 verbatim
@[fun_prop] lemma U_continuous : Continuous D.U := by unfold U; fun_prop

-- @@ L335-337 verbatim
@[fun_prop] lemma R_continuous : Continuous D.R := by
  unfold R
  exact (continuous_const.mul D.continuous_L).mul continuous_const

-- @@ L338-342 verbatim
@[fun_prop] lemma W_continuous : Continuous D.W := by
  unfold W
  exact (((D.R_continuous.comp continuous_snd).mul continuous_const).mul
    (square_continuous D.Kp D.U D.U_continuous D.U_zero)).mul
      (D.continuous_L.comp continuous_fst).star


-- @@ L344-346 verbatim
lemma W_bottom (s : unitInterval) :
    D.W (s,0)=D.H*star (D.L 1)*D.Hp s*D.L 1*star (D.L s) := by
  simp only [W,R_zero,one_mul,square_bottom,U,mul_assoc]


-- @@ L348-354 verbatim
lemma W_right (t : unitInterval) :
    D.W (1,t)=D.R t*D.Kp t*(D.H*star (D.L 1)*D.H) := by
  simp only [W,square_right,U,Hp_one]
  calc
    _ = D.R t*(D.H*D.Kp t)*(star (D.L 1)*D.H) := by
      simp only [Unitary.star_eq_inv]; group
    _ = _ := by rw [(D.Kp_commute t).eq]; simp only [mul_assoc]


-- @@ L356-364 verbatim
lemma W_left (t : unitInterval) :
    D.W (0,t)=D.R t*D.H*star (D.K*D.L 1*D.K)*D.Hp t*(D.K*D.L 1*D.K) := by
  simp only [W,square_left D.Kp D.U D.U_zero,Kp_one,D.L_zero,star_one,mul_one,U]
  simp only [star_mul,D.K_star]
  calc
    _ = D.R t*D.H*D.K*star (D.L 1)*((D.Hp t*D.K)*D.K)*D.L 1*D.K := by
      rw [mul_assoc (D.Hp t),D.KK,mul_one]
      simp only [mul_assoc]
    _ = _ := by rw [(D.Hp_commute t).eq]; simp only [mul_assoc]


-- @@ L366-373 verbatim
lemma W_top (s : unitInterval) :
    D.W (s,1)=(D.K*D.L 1*D.K)*D.Kp s*star (D.L s) := by
  simp only [W,square_top,Kp_one,U,Hp_one,R]
  calc
    _ = D.H*D.K*D.H*D.L 1*star D.K*D.Kp s*star (D.L s) := by
      simp only [Unitary.star_eq_inv]; group
    _ = _ := by
      rw [D.commute.eq,mul_assoc D.K,D.HH,mul_one,D.K_star]


-- @@ L375-375 verbatim
end Data

-- @@ L376-376 verbatim
end KirchbergRordam.SymmetryConjugacyDiagram



-- @@ L379-379 verbatim
namespace KirchbergRordam.UnitaryDisplacement

-- @@ L380-380 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L381-381 verbatim
abbrev conj (u : unitary A) : A ≃⋆ₐ[ℂ] A := Unitary.conjStarAlgAut ℂ A u

-- @@ L382-382 verbatim
def displacement (u : unitary A) (a : A) : ℝ := ‖conj u a-a‖

-- @@ L383-384 verbatim
lemma conj_mul (u v : unitary A) (a : A) : conj (u*v) a=conj u (conj v a) := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Submonoid.coe_mul,star_mul,mul_assoc]

-- @@ L385-387 verbatim
lemma conj_star (u : unitary A) (a : A) : conj (star u) (conj u a)=a := by
  simp only [conj,Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star]
  rw [← mul_assoc,← mul_assoc,u.property.1,one_mul,mul_assoc,u.property.1,mul_one]

-- @@ L388-389 verbatim
lemma norm_sub (u : unitary A) (a b : A) : ‖conj u a-conj u b‖=‖a-b‖ := by
  rw [← map_sub,StarAlgEquiv.norm_map]

-- @@ L390-398 verbatim
lemma displacement_mul (u v : unitary A) (a : A) :
    displacement (u*v) a ≤ displacement u a+displacement v a := by
  have he : conj (u*v) a-a = conj u (conj v a-a)+(conj u a-a) := by
    rw [map_sub,conj_mul]; abel
  unfold displacement
  rw [he]
  have h := norm_add_le (conj u (conj v a-a)) (conj u a-a)
  rw [StarAlgEquiv.norm_map] at h
  linarith

-- @@ L399-405 verbatim
lemma displacement_star (u : unitary A) (a : A) : displacement (star u) a=displacement u a := by
  have he : conj u (conj (star u) a-a)=a-conj u a := by
    rw [map_sub]
    have h : conj u (conj (star u) a)=a := by simpa only [star_star] using conj_star (star u) a
    rw [h]
  unfold displacement
  rw [← StarAlgEquiv.norm_map (conj u),he,norm_sub_rev]


-- @@ L407-413 verbatim
lemma displacement_conjugate (u v : unitary A) (a : A) :
    displacement (star u*v*u) a=displacement v (conj u a) := by
  unfold displacement
  rw [conj_mul,conj_mul,← StarAlgEquiv.norm_map (conj u),map_sub]
  have h : conj u (conj (star u) (conj v (conj u a))) = conj v (conj u a) := by
    simpa only [star_star] using conj_star (star u) (conj v (conj u a))
  rw [h]

-- @@ L414-416 verbatim
lemma conj_eq_of_commute (u : unitary A) (a : A) (ha : Commute (u:A) a) : conj u a=a := by
  dsimp only [conj,Unitary.conjStarAlgAut_apply]
  rw [ha.eq,mul_assoc,u.property.2,mul_one]

-- @@ L417-418 verbatim
lemma displacement_zero (u : unitary A) (a : A) (ha : Commute (u:A) a) : displacement u a=0 := by
  simp [displacement,conj_eq_of_commute u a ha]

-- @@ L419-426 verbatim
lemma displacement_near_fixed (u : unitary A) (a b : A) (hb : conj u b=b) :
    displacement u a ≤ 2*‖a-b‖ := by
  have he : conj u a-a=(conj u a-conj u b)+(b-a) := by rw [hb]; abel
  unfold displacement
  rw [he]
  calc
    _ ≤ ‖conj u a-conj u b‖+‖b-a‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub,norm_sub_rev]; ring

-- @@ L427-434 verbatim
lemma transport_error (u : unitary A) (a a₀ b b₀ : A) :
    ‖conj u a-b‖ ≤ ‖a-a₀‖+‖conj u a₀-b₀‖+‖b₀-b‖ := by
  have he : conj u a-b=(conj u a-conj u a₀)+(conj u a₀-b₀)+(b₀-b) := by abel
  rw [he]
  calc
    _ ≤ ‖conj u a-conj u a₀‖+‖conj u a₀-b₀‖+‖b₀-b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by rw [norm_sub]


-- @@ L436-436 verbatim
end KirchbergRordam.UnitaryDisplacement



-- @@ L439-439 verbatim
namespace KirchbergRordam.SymmetryConjugacyDiagram

-- @@ L440-440 verbatim
section

-- @@ L441-441 verbatim
open UnitaryConjugacySquare UnitaryDisplacement

-- @@ L442-442 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L443-443 verbatim
namespace Data

-- @@ L444-444 verbatim
variable (D : Data A)

-- @@ L445-446 verbatim
lemma Kp_fixes (a : A) (ha : Commute (D.K:A) a) (r : ℝ) : conj (D.Kp r) a=a :=
  conj_eq_of_commute _ _ (SymmetryFlow.flow_commute D.K D.hK a ha r)

-- @@ L447-448 verbatim
lemma Hp_fixes (b : A) (hb : Commute (D.H:A) b) (r : ℝ) : conj (D.Hp r) b=b :=
  conj_eq_of_commute _ _ (SymmetryFlow.flow_commute D.H D.hH b hb r)


-- @@ L450-453 verbatim
lemma U_control (a b : A) (hb : Commute (D.H:A) b) (r : ℝ) :
    displacement (D.U r) a ≤ 2*‖conj (D.L 1) a-b‖ := by
  rw [U,displacement_conjugate]
  exact displacement_near_fixed _ _ b (D.Hp_fixes b hb r)


-- @@ L455-466 verbatim
lemma square_control (a b : A) (ha : Commute (D.K:A) a)
    (hb : Commute (D.H:A) b) (x : Square) :
    displacement (square D.Kp D.U x) a ≤ 2*‖conj (D.L 1) a-b‖ := by
  have hz (r : ℝ) : displacement (D.Kp r) a=0 := by
    simp [displacement,D.Kp_fixes a ha]
  unfold square
  calc
    _ ≤ displacement (D.Kp (ratio x)*D.U (radius x)) a+
        displacement (D.Kp (-((1-(x.1:ℝ))*ratio x))) a := displacement_mul _ _ _
    _ ≤ (displacement (D.Kp (ratio x)) a+displacement (D.U (radius x)) a)+0 :=
      add_le_add (displacement_mul _ _ _) (le_of_eq (hz _))
    _ ≤ _ := by simpa only [hz,zero_add,add_zero] using D.U_control a b hb (radius x)



-- @@ L469-488 verbatim
theorem half_flip_control (a : unitInterval → A) (b : A)
    (ha : Commute (D.K:A) (a 0)) (hb : Commute (D.H:A) b)
    (δ : ℝ) (hn : ∀ t, ‖a t-a 0‖ ≤ δ)
    (hend : ‖conj (D.L 1) (a 0)-b‖ ≤ δ) (s t : unitInterval) :
    ‖conj (D.W (s,t)) (conj (D.L s) (a s))-
        conj (D.R t) (conj (D.H*D.K) (a t))‖ ≤ 4*δ := by
  have he : conj (D.W (s,t)) (conj (D.L s) (a s)) =
      conj (D.R t) (conj D.H (conj (square D.Kp D.U (s,t)) (a s))) := by
    simp only [W,UnitaryDisplacement.conj_mul,conj_star]
  rw [he,UnitaryDisplacement.conj_mul,UnitaryDisplacement.norm_sub,UnitaryDisplacement.norm_sub]
  have hk : conj D.K (a 0)=a 0 := conj_eq_of_commute _ _ ha
  have hnorm : ‖a 0-conj D.K (a t)‖=‖a t-a 0‖ := by
    calc
      _ = ‖conj D.K (a 0)-conj D.K (a t)‖ := by rw [hk]
      _ = _ := by rw [UnitaryDisplacement.norm_sub,norm_sub_rev]
  have h := transport_error (square D.Kp D.U (s,t)) (a s) (a 0) (conj D.K (a t)) (a 0)
  rw [hnorm] at h
  have hc := D.square_control (a 0) b ha hb (s,t)
  change ‖conj (square D.Kp D.U (s,t)) (a 0)-a 0‖ ≤ _ at hc
  linarith [hn s,hn t]

-- @@ L489-489 verbatim
end Data

-- @@ L490-490 verbatim
end

-- @@ L491-491 verbatim
variable {A : Type*} [CStarAlgebra A]

-- @@ L492-495 verbatim
lemma symmetry_mem (S : StarSubalgebra ℂ A) (u : unitary A)
    (hu : star (u:A)=u) (hm : (u:A) ∈ S) (r : ℝ) :
    (SymmetryFlow.flow u hu r : A) ∈ S := by
  exact S.add_mem (S.smul_mem (S.one_mem) _) (S.smul_mem hm _)

-- @@ L496-496 verbatim
namespace Data

-- @@ L497-497 verbatim
variable (D : Data A)



-- @@ L500-504 verbatim
lemma W_bottom_mem (S : StarSubalgebra ℂ A) (hH : (D.H:A) ∈ S)
    (hL : ∀ t, (D.L t:A) ∈ S) (s : unitInterval) : (D.W (s,0):A) ∈ S := by
  rw [D.W_bottom]
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem hH (S.star_mem' (hL 1)))
    (symmetry_mem S D.H D.hH hH s)) (hL 1)) (S.star_mem' (hL s))

-- @@ L505-512 verbatim
lemma W_right_mem (S : StarSubalgebra ℂ A) (hK : (D.K:A) ∈ S)
    (hR : ∀ t, (D.R t:A) ∈ S) (hcross : ((D.H*D.L 1*D.H):A) ∈ S)
    (t : unitInterval) : (D.W (1,t):A) ∈ S := by
  rw [D.W_right]
  apply S.mul_mem (S.mul_mem (hR t) (symmetry_mem S D.K D.hK hK t))
  have hh := S.star_mem' hcross
  change (D.H:A) * star (D.L 1:A) * (D.H:A) ∈ S
  simpa only [star_mul,D.hH,mul_assoc,StarSubalgebra.mem_carrier] using hh

-- @@ L513-518 verbatim
lemma W_left_mem (S : StarSubalgebra ℂ A) (hH : (D.H:A) ∈ S)
    (hR : ∀ t, (D.R t:A) ∈ S) (hcross : ((D.K*D.L 1*D.K):A) ∈ S)
    (t : unitInterval) : (D.W (0,t):A) ∈ S := by
  rw [D.W_left]
  exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hR t) hH) (S.star_mem' hcross))
    (symmetry_mem S D.H D.hH hH t)) hcross

-- @@ L519-523 verbatim
lemma W_top_mem (S : StarSubalgebra ℂ A) (hK : (D.K:A) ∈ S)
    (hL : ∀ t, (D.L t:A) ∈ S) (hcross : ((D.K*D.L 1*D.K):A) ∈ S)
    (s : unitInterval) : (D.W (s,1):A) ∈ S := by
  rw [D.W_top]
  exact S.mul_mem (S.mul_mem hcross (symmetry_mem S D.K D.hK hK s)) (S.star_mem' (hL s))

-- @@ L524-524 verbatim
end Data

-- @@ L525-525 verbatim
end KirchbergRordam.SymmetryConjugacyDiagram

-- @@ L526-526 verbatim
end


-- @@ L528-528 verbatim
end OAI
