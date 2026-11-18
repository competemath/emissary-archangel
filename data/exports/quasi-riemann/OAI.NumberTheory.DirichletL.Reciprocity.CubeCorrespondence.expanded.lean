import OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L74-74 verbatim
open scoped BigOperators Classical


-- @@ L76-76 verbatim
namespace CubicKubota


-- @@ L78-78 verbatim
open scoped Classical MatrixGroups


-- @@ L80-80 verbatim
section

-- @@ L81-81 verbatim
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified

-- @@ L82-82 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L84-84 verbatim
def cubeDiagonal (p : Eis) : Matrix (Fin 2) (Fin 2) Eis := !![p^3,0;0,1]


-- @@ L86-114 verbatim
def cubeCorrespondence (p : Eis) : Subgroup (levelThree × levelThree) where
  carrier := {MN | cubeDiagonal p * (MN.1 : SL(2,Eis)).val =
    (MN.2 : SL(2,Eis)).val * cubeDiagonal p}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨M,N⟩ ⟨M',N'⟩ h h'
    change cubeDiagonal p * ((M : SL(2,Eis)).val * (M' : SL(2,Eis)).val) =
      ((N : SL(2,Eis)).val * (N' : SL(2,Eis)).val) * cubeDiagonal p
    calc
      _ = (cubeDiagonal p * (M : SL(2,Eis)).val) * (M' : SL(2,Eis)).val :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((N : SL(2,Eis)).val * cubeDiagonal p) * (M' : SL(2,Eis)).val := by rw [h]
      _ = (N : SL(2,Eis)).val * (cubeDiagonal p * (M' : SL(2,Eis)).val) := Matrix.mul_assoc _ _ _
      _ = (N : SL(2,Eis)).val * ((N' : SL(2,Eis)).val * cubeDiagonal p) := by rw [h']
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  inv_mem' := by
    rintro ⟨M,N⟩ h
    change cubeDiagonal p * ((M : SL(2,Eis))⁻¹).val =
      ((N : SL(2,Eis))⁻¹).val * cubeDiagonal p
    calc
      _ = (((N : SL(2,Eis))⁻¹).val * ((N : SL(2,Eis)).val * cubeDiagonal p)) *
          ((M : SL(2,Eis))⁻¹).val := by
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = (((N : SL(2,Eis))⁻¹).val * (cubeDiagonal p * (M : SL(2,Eis)).val)) *
          ((M : SL(2,Eis))⁻¹).val := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]


-- @@ L116-117 verbatim
def cubeCorrespondenceLeft (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.fst levelThree levelThree).comp (cubeCorrespondence p).subtype


-- @@ L119-120 verbatim
def cubeCorrespondenceRight (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.snd levelThree levelThree).comp (cubeCorrespondence p).subtype


-- @@ L122-137 verbatim
lemma cubeCorrespondence_entries (p : Eis) (MN : cubeCorrespondence p) :
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 0 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 0) * p^3 ∧
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 1 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 1) ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 0) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 0) * p^3 ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 1) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 1) := by
  have h := MN.property
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 0) h
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 1) h
  norm_num [cubeDiagonal, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00,h01,h10,h11⟩


-- @@ L139-154 verbatim
lemma cubeCorrespondenceLeft_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hM : x.1.1=y.1.1 := h
  apply Subtype.ext
  apply Prod.ext hM
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.1.symm.trans (by rw [hM]; exact hy.1))
  · exact hx.2.1.symm.trans (by rw [hM]; exact hy.2.1)
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.2.2.1.symm.trans (by rw [hM]; exact hy.2.2.1))
  · exact hx.2.2.2.symm.trans (by rw [hM]; exact hy.2.2.2)


-- @@ L156-171 verbatim
lemma cubeCorrespondenceRight_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceRight p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hN : x.1.2=y.1.2 := h
  apply Subtype.ext
  refine Prod.ext ?_ hN
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.1.trans (by rw [hN]; exact hy.1.symm))
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.2.1.trans (by rw [hN]; exact hy.2.1.symm))
  · exact hx.2.2.1.trans (by rw [hN]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.trans (by rw [hN]; exact hy.2.2.2.symm)


-- @@ L173-194 verbatim
lemma cubeCorrespondence_value (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    value (cubeCorrespondenceLeft p MN) = value (cubeCorrespondenceRight p MN) := by
  have he := cubeCorrespondence_entries p MN
  let M : levelThree := MN.1.1
  let N : levelThree := MN.1.2
  have ha : (M : SL(2,Eis)) 0 0 = (N : SL(2,Eis)) 0 0 :=
    mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
  have hc : (M : SL(2,Eis)) 1 0 = p^3 * (N : SL(2,Eis)) 1 0 :=
    he.2.2.1.trans (mul_comm _ _)
  have hd : (M : SL(2,Eis)) 0 0 * (M : SL(2,Eis)) 1 1 -
      (M : SL(2,Eis)) 0 1 * (M : SL(2,Eis)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,Eis)).property
  have hcop : IsCoprime p ((N : SL(2,Eis)) 0 0) := by
    refine ⟨-(M : SL(2,Eis)) 0 1 * p^2 * (N : SL(2,Eis)) 1 0,
      (M : SL(2,Eis)) 1 1,?_⟩
    rw [ha,hc] at hd
    linear_combination hd
  change symbol ((M : SL(2,Eis)) 1 0) ((M : SL(2,Eis)) 0 0) =
    symbol ((N : SL(2,Eis)) 1 0) ((N : SL(2,Eis)) 0 0)
  rw [ha,hc,symbol_mul_numerator _ _ _ (levelThree_primary N),
    symbol_pow_numerator _ _ (levelThree_primary N),
    symbol_cube_of_isCoprime _ _ (levelThree_primary N) hcop,one_mul]


-- @@ L196-199 verbatim
lemma cubeCorrespondence_character (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    complexCharacter (cubeCorrespondenceLeft p MN) =
      complexCharacter (cubeCorrespondenceRight p MN) := by
  exact congrArg ConcreteTraceCRT.eisEmbedding (cubeCorrespondence_value p hp MN)


-- @@ L201-201 verbatim
end


-- @@ L203-203 verbatim
section

-- @@ L204-204 verbatim
open ActualEisensteinCubic ConcreteTraceCRT

-- @@ L205-205 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L207-209 verbatim
def cubePrincipalLevel (p : Eis) : Subgroup levelThree :=
  ((Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3}))).comp levelThree.subtype).ker


-- @@ L211-221 verbatim
lemma cubePrincipalLevel_entry (p : Eis) (M : cubePrincipalLevel p) (i j : Fin 2) :
    (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) i j-(if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})) ((M.1 : levelThree) : SL(2,Eis)) = 1 := M.property
  have h := congrArg (fun N : SL(2,Eis ⧸ Ideal.span {(3:Eis)*p^3}) => N i j) hm
  change Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})
    (((M.1 : levelThree) : SL(2,Eis)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {(3:Eis)*p^3})) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h


-- @@ L223-228 verbatim
lemma cubePrincipalLevel_finiteIndex (p : Eis) (hp : p ≠ 0) :
    (cubePrincipalLevel p).FiniteIndex := by
  let : Finite (Eis ⧸ Ideal.span {(3:Eis)*p^3}) :=
    finite_quotient_span (mul_ne_zero (by norm_num) (pow_ne_zero 3 hp))
  unfold cubePrincipalLevel
  infer_instance


-- @@ L230-262 verbatim
lemma cubePrincipalLevel_left_mate (p : Eis) (M : cubePrincipalLevel p) :
    ∃ N : levelThree, ((M.1 : levelThree),N) ∈ cubeCorrespondence p := by
  obtain ⟨c,hc⟩ : (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) 1 0 := by
    simpa using cubePrincipalLevel_entry p M 1 0
  let A : SL(2,Eis) := M.1
  let N : SL(2,Eis) := ⟨!![A 0 0,p^3*A 0 1;3*c,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 1 0=(3:Eis)*p^3*c at hc
    rw [hc] at hd
    linear_combination hd⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry M.1 0 0
    · change (3:Eis)∣p^3*A 0 1-0
      simpa using dvd_mul_of_dvd_right (levelThree_upper M.1) (p^3)
    · change (3:Eis)∣3*c-0
      simp
    · exact levelThree_entry M.1 1 1
  refine ⟨⟨N,hN⟩,?_⟩
  change cubeDiagonal p*A.val=N.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,N,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 1 0=(3:Eis)*p^3*c at hc
    change A 1 0=3*c*p^3
    rw [hc]
    ring


-- @@ L264-297 verbatim
lemma cubePrincipalLevel_right_mate (p : Eis) (N : cubePrincipalLevel p) :
    ∃ M : levelThree, (M,(N.1 : levelThree)) ∈ cubeCorrespondence p := by
  obtain ⟨b,hb⟩ : (3:Eis)*p^3 ∣ ((N.1 : levelThree) : SL(2,Eis)) 0 1 := by
    simpa using cubePrincipalLevel_entry p N 0 1
  let A : SL(2,Eis) := N.1
  let M : SL(2,Eis) := ⟨!![A 0 0,3*b;p^3*A 1 0,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 0 1=(3:Eis)*p^3*b at hb
    rw [hb] at hd
    linear_combination hd⟩
  have hM : M∈levelThree := by
    apply (mem_levelThree_iff_entries M).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry N.1 0 0
    · change (3:Eis)∣3*b-0
      simp
    · change (3:Eis)∣p^3*A 1 0-0
      simpa using dvd_mul_of_dvd_right (levelThree_lower N.1) (p^3)
    · exact levelThree_entry N.1 1 1
  refine ⟨⟨M,hM⟩,?_⟩
  change cubeDiagonal p*M.val=A.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,M,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 0 1=(3:Eis)*p^3*b at hb
    change p^3*(3*b)=A 0 1
    rw [hb]
    ring
  · ring


-- @@ L299-303 verbatim
lemma cubePrincipalLevel_le_left_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceLeft p).range := by
  intro M hM
  obtain ⟨N,hN⟩ := cubePrincipalLevel_left_mate p ⟨M,hM⟩
  exact ⟨⟨(M,N),hN⟩,rfl⟩


-- @@ L305-309 verbatim
lemma cubePrincipalLevel_le_right_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceRight p).range := by
  intro N hN
  obtain ⟨M,hM⟩ := cubePrincipalLevel_right_mate p ⟨N,hN⟩
  exact ⟨⟨(M,N),hM⟩,rfl⟩


-- @@ L311-319 verbatim
lemma cubeCorrespondence_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) ∧
    Function.Injective (cubeCorrespondenceRight p) ∧
    (cubeCorrespondenceLeft p).range.FiniteIndex ∧
    (cubeCorrespondenceRight p).range.FiniteIndex := by
  let : (cubePrincipalLevel p).FiniteIndex := cubePrincipalLevel_finiteIndex p hp
  exact ⟨cubeCorrespondenceLeft_injective p hp,cubeCorrespondenceRight_injective p hp,
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_left_range p),
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_right_range p)⟩


-- @@ L321-321 verbatim
end


-- @@ L323-323 verbatim
section

-- @@ L324-324 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein

-- @@ L325-325 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L327-328 verbatim
def cubeKernelCorrespondence (p : Eis) : Subgroup (cubeCorrespondence p) :=
  (finiteCubicMultiplier.comp (cubeCorrespondenceLeft p)).ker


-- @@ L330-333 verbatim
def cubeKernelLeft (p : Eis) : cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceLeft p x.1,x.property⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceLeft p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceLeft p) x.1 y.1


-- @@ L335-339 verbatim
lemma cubeKernel_right_mem (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeCorrespondenceRight p x.1 ∈ finiteCubicMultiplier.ker := by
  apply (finiteCubicMultiplier_eq_one _).mpr
  rw [←cubeCorrespondence_character p hp x.1]
  exact (finiteCubicMultiplier_eq_one _).mp x.property


-- @@ L341-345 verbatim
def cubeKernelRight (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceRight p x.1,cubeKernel_right_mem p hp x⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceRight p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceRight p) x.1 y.1


-- @@ L347-359 verbatim
lemma cubeKernelLeft_range (p : Eis) :
    (cubeKernelLeft p).range =
      (cubeCorrespondenceLeft p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      change finiteCubicMultiplier (cubeCorrespondenceLeft p x)=1
      rw [hx]
      exact y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩


-- @@ L361-373 verbatim
lemma cubeKernelRight_range (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRight p hp).range =
      (cubeCorrespondenceRight p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      apply (finiteCubicMultiplier_eq_one _).mpr
      rw [cubeCorrespondence_character p hp x,hx]
      exact (finiteCubicMultiplier_eq_one _).mp y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩


-- @@ L375-393 verbatim
lemma cubeKernel_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeKernelLeft p) ∧ Function.Injective (cubeKernelRight p hp) ∧
    (cubeKernelLeft p).range.FiniteIndex ∧ (cubeKernelRight p hp).range.FiniteIndex := by
  have hcov := cubeCorrespondence_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply hcov.1
    exact congrArg Subtype.val h
  · intro x y h
    apply Subtype.ext
    apply hcov.2.1
    exact congrArg Subtype.val h
  · rw [cubeKernelLeft_range]
    infer_instance
  · rw [cubeKernelRight_range]
    infer_instance


-- @@ L395-396 verbatim
def cubeKernelLeftGlobal (p : Eis) : cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelLeft p))


-- @@ L398-400 verbatim
def cubeKernelRightGlobal (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelRight p hp))


-- @@ L402-405 verbatim
lemma cubeKernelLeftGlobal_le (p : Eis) :
    (cubeKernelLeftGlobal p).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelLeft p x).1,(cubeKernelLeft p x).property,rfl⟩


-- @@ L407-410 verbatim
lemma cubeKernelRightGlobal_le (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRightGlobal p hp).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelRight p hp x).1,(cubeKernelRight p hp x).property,rfl⟩


-- @@ L412-417 verbatim
private lemma finiteIndex_subtype_image {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] (J : Subgroup H) [J.FiniteIndex] : (J.map H.subtype).FiniteIndex := by
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H:=J))
    (Subgroup.FiniteIndex.index_ne_zero (H:=H))


-- @@ L419-434 verbatim
lemma cubeKernelGlobal_finite_covers (p : Eis) (hp : p ≠ 0) :
    (cubeKernelLeftGlobal p).range.FiniteIndex ∧
    (cubeKernelRightGlobal p hp).range.FiniteIndex := by
  have hcov := cubeKernel_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  have hL : ((cubeKernelLeft p).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  have hR : ((cubeKernelRight p hp).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  constructor
  · rw [cubeKernelLeftGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _
  · rw [cubeKernelRightGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _


-- @@ L436-438 verbatim
lemma cubeKernelGlobal_intertwining (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeDiagonal p * (cubeKernelLeftGlobal p x).val =
      (cubeKernelRightGlobal p hp x).val * cubeDiagonal p := x.1.property


-- @@ L440-440 verbatim
end


-- @@ L442-442 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein

-- @@ L443-443 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L445-491 verbatim
lemma cubeArchimedean_correspondence (p : Eis) (hp : p ≠ 0) :
    ∃ g : SL(2,ℂ), g 0 1=0 ∧ g 1 0=0 ∧ g 0 0/g 1 1=eisEmbedding p^3 ∧
      ∀ x : cubeKernelCorrespondence p,
        g*integralComplexMatrix (cubeKernelLeftGlobal p x)=
          integralComplexMatrix (cubeKernelRightGlobal p hp x)*g := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2)
  have hz0 : z≠0 := by
    intro he
    rw [he,zero_pow (by decide)] at hz
    exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hz.symm
  let g : SL(2,ℂ) := ⟨!![z,0;0,z⁻¹],by simp [Matrix.det_fin_two_of,hz0]⟩
  refine ⟨g,rfl,rfl,?_,?_⟩
  · change z/z⁻¹=eisEmbedding p^3
    rw [div_inv_eq_mul,←pow_two,hz]
  · intro x
    have he := cubeCorrespondence_entries p x.1
    have ha : (((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0 =
        (((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0 :=
      mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
    have he00 := congrArg eisEmbedding ha
    have he01 := congrArg eisEmbedding he.2.1
    have he10 := congrArg eisEmbedding he.2.2.1
    have he11 := congrArg eisEmbedding he.2.2.2
    simp only [map_mul,map_pow] at he01 he10
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
        integralComplexMatrix_apply]
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*0
      rw [he00]
      ring
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*z⁻¹
      rw [←he01,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*0
      rw [he10,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*z⁻¹
      rw [he11]
      ring


-- @@ L493-493 verbatim
end CubicKubota


-- @@ L495-495 verbatim
open Filter MeasureTheory Asymptotics

-- @@ L496-496 verbatim
open scoped BigOperators Classical Topology

-- @@ L497-497 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L499-499 verbatim
namespace CubicEisenstein

-- @@ L500-500 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L502-503 verbatim
def cuspBarProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerBar (fun w=>f (cuspCoordinateLift (v,w))) z


-- @@ L505-506 verbatim
def cuspZProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerZ (fun w=>f (cuspCoordinateLift (v,w))) z


-- @@ L508-510 verbatim
lemma cuspBarProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile f z v=horizontalWirtingerBar (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspBarProfile,cuspCoordinateLift_positive v _ hv]


-- @@ L512-514 verbatim
lemma cuspZProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile f z v=horizontalWirtingerZ (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspZProfile,cuspCoordinateLift_positive v _ hv]


-- @@ L516-520 verbatim
lemma horizontalWirtingerZ_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (f w)) z=star (horizontalWirtingerBar f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp [sub_eq_add_neg]


-- @@ L522-522 verbatim
namespace SubexponentialBesselCoefficients

-- @@ L523-523 verbatim
variable (coeff : SubexponentialBesselCoefficients)


-- @@ L525-526 verbatim
def directionalSeries (direction : ℂ) (p : ℝ × ℂ) : ℂ :=
  ∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h p.1 p.2 direction


-- @@ L528-538 verbatim
lemma directionalSeries_continuousOn_slab (direction : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound a b ha hab direction
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h
    have ht : ContinuousOn (coeff.term h) {p : ℝ × ℂ|p.1∈Set.Icc a b} :=
      (coeff.term_continuousOn h).mono (fun p hp=>ha.trans_le hp.1)
    exact ht.const_mul (horizontalPhaseMultiplier (cuspFrequency h) direction)
  · exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · intro h p hp
    exact hbound h p.1 p.2 hp


-- @@ L540-548 verbatim
lemma directionalSeries_continuousOn (direction : ℂ) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|0<p.1} := by
  intro p hp
  have hclosed := coeff.directionalSeries_continuousOn_slab direction (p.1/2) (2*p.1)
    (by change 0<p.1 at hp;linarith) (by change 0<p.1 at hp;linarith)
  have hnb : {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by change 0<p.1 at hp;linarith)
      (by change 0<p.1 at hp;linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt


-- @@ L550-558 verbatim
lemma cuspBarProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)+Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspBarProfile_positive _ _ _ hv,horizontalWirtingerBar]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl


-- @@ L560-568 verbatim
lemma cuspZProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)-Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspZProfile_positive _ _ _ hv,horizontalWirtingerZ]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl


-- @@ L570-577 verbatim
lemma cuspBarProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspBarProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).add (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspBarProfile_full_eq constant z v hv


-- @@ L579-586 verbatim
lemma cuspZProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspZProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).sub (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspZProfile_full_eq constant z v hv


-- @@ L588-588 verbatim
end SubexponentialBesselCoefficients


-- @@ L590-593 verbatim
lemma cuspBarProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspBarProfile_continuousOn _ z


-- @@ L595-598 verbatim
lemma cuspZProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspZProfile_continuousOn _ z


-- @@ L600-603 verbatim
lemma cuspBarProfile_conjugate_eq (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z=fun v=>star (cuspZProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerBar_star _ z


-- @@ L605-608 verbatim
lemma cuspZProfile_conjugate_eq (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z=fun v=>star (cuspBarProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerZ_star _ z


-- @@ L610-613 verbatim
lemma cuspBarProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspBarProfile_conjugate_eq]
  exact (cuspZProfile_source_continuousOn z).star


-- @@ L615-618 verbatim
lemma cuspZProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspZProfile_conjugate_eq]
  exact (cuspBarProfile_source_continuousOn z).star


-- @@ L620-628 verbatim
lemma cuspBarProfile_source_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerBar_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv


-- @@ L630-638 verbatim
lemma cuspZProfile_source_isBigO (z : ℂ) :
    cuspZProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv


-- @@ L640-646 verbatim
lemma cuspBarProfile_conjugate_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspZProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspBarProfile_conjugate_eq,norm_star] using hv


-- @@ L648-654 verbatim
lemma cuspZProfile_conjugate_isBigO (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspBarProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspZProfile_conjugate_eq,norm_star] using hv


-- @@ L656-656 verbatim
end CubicEisenstein


-- @@ L658-658 verbatim
end


-- @@ L660-660 verbatim
end OAI
