
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_24843_1.Irreducible3_1_24843_1
import IdealArithmetic.DedekindProject.Discriminant




-- @@ L10-10 verbatim
open Polynomial Module


-- @@ L12-12 verbatim
noncomputable def T : ℤ[X] := X^3 - 91 

-- @@ L13-13 verbatim
lemma T_def : T = X^3 - 91 := rfl


-- @@ L15-15 verbatim
def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)


-- @@ L17-19 verbatim
noncomputable instance : CommRing K := by
  unfold K
  infer_instance


-- @@ L21-23 verbatim
noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _ 


-- @@ L25-25 verbatim
local notation "l" => [-91, 0, 0, 1]


-- @@ L27-28 verbatim
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _


-- @@ L30-30 verbatim
local notation "θ" => Adj.root


-- @@ L32-35 expanded
lemma T_ofList : ofList [-91, 0, 0, 1] = T := by rw [T_def]; norm_num;
  ring
    -- We build the subalgebra with integral basis [1, a, 1/3*a^2 + 1/3*a + 1/3]


-- @@ L37-54 expanded
noncomputable def BQ : SubalgebraBuilderLists 3 ℤ ℚ K T [-91, 0, 0, 1]
    where
  d := 3
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := ![![3, 0, 0], ![0, 3, 0], ![1, 1, 1]]
  a :=
    ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 1, 0], ![-1, -1, 3], ![30, 0, 1]],
      ![![0, 0, 1], ![30, 0, 1], ![20, 10, 1]]]
  s := ![![[], [], []], ![[], [], [-3]], ![[], [-3], [-2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide


-- @@ L56-56 expanded
lemma T_degree : T.natDegree = 3 :=
  (SubalgebraBuilderOfList T [-91, 0, 0, 1] BQ).hdeg


-- @@ L58-60 expanded
lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList [-91, 0, 0, 1] rfl


-- @@ L62-62 verbatim
lemma T_irreducible : Irreducible T := irreducible_T


-- @@ L64-64 verbatim
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K


-- @@ L66-66 expanded
noncomputable def O :=
  subalgebraOfBuilderLists T [-91, 0, 0, 1] BQ


-- @@ L68-68 expanded
def hm : O ≤ Om :=
  le_integralClosure_of_basis O (basisOfBuilderLists T [-91, 0, 0, 1] BQ)


-- @@ L70-72 verbatim
noncomputable def B' : Basis (Fin 3) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)


-- @@ L74-74 verbatim
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'

-- @@ L75-75 verbatim
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'


-- @@ L77-78 expanded
noncomputable def timesTableO : TimesTable (Fin 3) ℤ O :=
  timesTableOfSubalgebraBuilderLists T [-91, 0, 0, 1] BQ


-- @@ L80-80 verbatim
noncomputable def B : Basis (Fin 3) ℤ O := timesTableO.basis 


-- @@ L82-85 verbatim
def Table : Fin 3 → Fin 3 → List ℤ := 
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
 ![[0, 1, 0], [-1, -1, 3], [30, 0, 1]], 
 ![[0, 0, 1], [30, 0, 1], [20, 10, 1]]]


-- @@ L87-87 verbatim
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide


-- @@ L89-90 expanded
lemma hroot_mem : Adj.root ∈ O := by
  refine root_in_subalgebra_lists T [-91, 0, 0, 1] BQ ![0, 1, 0] [] (by decide)


-- @@ L92-92 verbatim
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)

-- @@ L93-93 verbatim
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

-- @@ L94-94 verbatim
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)


-- @@ L96-110 expanded
def CD7 : CertificateDedekindCriterionLists [-91, 0, 0, 1] 7
    where
  n := 3
  a' := []
  b' := [1]
  k := [1]
  f := [13]
  g := [0, 1]
  h := [0, 0, 1]
  a := [6]
  b := []
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L112-126 expanded
def CD13 : CertificateDedekindCriterionLists [-91, 0, 0, 1] 13
    where
  n := 3
  a' := []
  b' := [1]
  k := [1]
  f := [7]
  g := [0, 1]
  h := [0, 0, 1]
  a := [2]
  b := []
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L128-146 expanded
noncomputable def D : CertificateDedekindAlmostAllLists T [-91, 0, 0, 1] [3]
    where
  n := 3
  p := ![3, 7, 13]
  exp := ![3, 2, 2]
  pdgood := [7, 13]
  hsub := by decide
  hp := by
    intro i; fin_cases i
    exact hp3.out
    exact hp7.out
    exact hp13.out
  a := [-2457]
  b := [0, 819]
  hab := by decide
  hd := by
    intro p hp
    fin_cases hp
    exact satisfiesDedekindCriterion_of_certificate_lists T [-91, 0, 0, 1] 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T [-91, 0, 0, 1] 13 T_ofList CD13


-- @@ L148-183 verbatim
noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 1
 n := 2
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [2, 2, 0], [0, 0, 1]], 
![[0, 0, 1], [0, 0, 1], [2, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 2, 0]]
 b2 := ![![1, 0, 0],![1, 0, 1]]
 v := ![![1, 2, 0]]
 w := ![![1, 0, 0],![1, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 1, 1]]
 v_ind := ![0]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![0, 2, 2],![1, 2, 0],![1, 2, 2]]
 a := ![![![-1]],![![0]],![![0]]]
 c := ![![![33, 6]],![![-5, 4]],![![33, 6]]]
 d := ![![![3],![33]],![![3],![3]],![![3],![33]]]
 e := ![![![-3, 2],![83, 6]],![![0, 0],![57, 3]],![![-2, 2],![83, 7]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inr 0, Sum.inr 0)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            


-- @@ L186-186 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L188-189 verbatim
lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ


-- @@ L191-198 verbatim
lemma B_one_repr : B.equivFun.symm ![1, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 


-- @@ L200-204 verbatim
lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


-- @@ L206-215 verbatim
instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 

--  We add these shortcuts for faster typeclass inference  
 
-- @@ L216-216 verbatim
noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 
-- @@ L217-217 verbatim
noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 
-- @@ L218-218 verbatim
noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 
-- @@ L219-219 verbatim
noncomputable instance  : Algebra ℤ O := O.algebra'  


