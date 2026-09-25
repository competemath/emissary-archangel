
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF4_0_76176_2.Irreducible4_0_76176_2
import IdealArithmetic.DedekindProject.Discriminant




-- @@ L10-10 verbatim
open Polynomial Module


-- @@ L12-12 verbatim
noncomputable def T : ℤ[X] := X^4 - 2*X^3 + 7*X^2 - 6*X + 78 

-- @@ L13-13 verbatim
lemma T_def : T = X^4 - 2*X^3 + 7*X^2 - 6*X + 78 := rfl


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
local notation "l" => [78, -6, 7, -2, 1]


-- @@ L27-28 verbatim
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _


-- @@ L30-30 verbatim
local notation "θ" => Adj.root


-- @@ L32-35 expanded
lemma T_ofList : ofList [78, -6, 7, -2, 1] = T := by rw [T_def]; norm_num;
  ring
    -- We build the subalgebra with integral basis [1, a, a^2, 1/35*a^3 + 16/35*a^2 + 3/7*a - 16/35]


-- @@ L37-55 expanded
noncomputable def BQ : SubalgebraBuilderLists 4 ℤ ℚ K T [78, -6, 7, -2, 1]
    where
  d := 35
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := ![![35, 0, 0, 0], ![0, 35, 0, 0], ![0, 0, 35, 0], ![-16, 15, 16, 1]]
  a :=
    ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
      ![![0, 1, 0, 0], ![0, 0, 1, 0], ![16, -15, -16, 35], ![6, -8, -8, 18]],
      ![![0, 0, 1, 0], ![16, -15, -16, 35], ![-46, -24, -39, 70], ![-20, -18, -24, 44]],
      ![![0, 0, 0, 1], ![6, -8, -8, 18], ![-20, -18, -24, 44], ![-10, -12, -14, 26]]]
  s :=
    ![![[], [], [], []], ![[], [], [], [-35]], ![[], [], [-1225], [-630, -35]],
      ![[], [-35], [-630, -35], [-347, -34, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide


-- @@ L57-57 expanded
lemma T_degree : T.natDegree = 4 :=
  (SubalgebraBuilderOfList T [78, -6, 7, -2, 1] BQ).hdeg


-- @@ L59-61 expanded
lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList [78, -6, 7, -2, 1] rfl


-- @@ L63-63 verbatim
lemma T_irreducible : Irreducible T := irreducible_T


-- @@ L65-65 verbatim
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K


-- @@ L67-67 expanded
noncomputable def O :=
  subalgebraOfBuilderLists T [78, -6, 7, -2, 1] BQ


-- @@ L69-69 expanded
def hm : O ≤ Om :=
  le_integralClosure_of_basis O (basisOfBuilderLists T [78, -6, 7, -2, 1] BQ)


-- @@ L71-73 verbatim
noncomputable def B' : Basis (Fin 4) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)


-- @@ L75-75 verbatim
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'

-- @@ L76-76 verbatim
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'


-- @@ L78-79 expanded
noncomputable def timesTableO : TimesTable (Fin 4) ℤ O :=
  timesTableOfSubalgebraBuilderLists T [78, -6, 7, -2, 1] BQ


-- @@ L81-81 verbatim
noncomputable def B : Basis (Fin 4) ℤ O := timesTableO.basis 


-- @@ L83-87 verbatim
def Table : Fin 4 → Fin 4 → List ℤ := 
 ![ ![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
 ![[0, 1, 0, 0], [0, 0, 1, 0], [16, -15, -16, 35], [6, -8, -8, 18]], 
 ![[0, 0, 1, 0], [16, -15, -16, 35], [-46, -24, -39, 70], [-20, -18, -24, 44]], 
 ![[0, 0, 0, 1], [6, -8, -8, 18], [-20, -18, -24, 44], [-10, -12, -14, 26]]]


-- @@ L89-89 verbatim
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide


-- @@ L91-92 expanded
lemma hroot_mem : Adj.root ∈ O := by
  refine root_in_subalgebra_lists T [78, -6, 7, -2, 1] BQ ![0, 1, 0, 0] [] (by decide)


-- @@ L94-94 verbatim
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)

-- @@ L95-95 verbatim
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)

-- @@ L96-96 verbatim
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

-- @@ L97-97 verbatim
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

-- @@ L98-98 verbatim
instance hp23: Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)


-- @@ L100-114 expanded
def CD2 : CertificateDedekindCriterionLists [78, -6, 7, -2, 1] 2
    where
  n := 2
  a' := []
  b' := [1]
  k := [1]
  f := [-39, 3, -3, 2]
  g := [0, 1, 1]
  h := [0, 1, 1]
  a := [1]
  b := [1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L116-130 expanded
def CD3 : CertificateDedekindCriterionLists [78, -6, 7, -2, 1] 3
    where
  n := 2
  a' := [2]
  b' := [2, 2]
  k := [1]
  f := [-26, 2, -1, 2]
  g := [0, 2, 1]
  h := [0, 2, 1]
  a := [1]
  b := [2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L132-146 expanded
def CD23 : CertificateDedekindCriterionLists [78, -6, 7, -2, 1] 23
    where
  n := 2
  a' := [15]
  b' := [21, 4]
  k := [1]
  f := [-3, 6, 21, 2]
  g := [3, 22, 1]
  h := [3, 22, 1]
  a := [15]
  b := [0, 16]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L148-169 expanded
noncomputable def D : CertificateDedekindAlmostAllLists T [78, -6, 7, -2, 1] [5, 7]
    where
  n := 5
  p := ![2, 3, 5, 7, 23]
  exp := ![4, 2, 2, 2, 2]
  pdgood := [2, 3, 23]
  hsub := by decide
  hp := by
    intro i; fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp5.out
    exact hp7.out
    exact hp23.out
  a := [1206672, 48576, -48576]
  b := [134136, -262200, -18216, 12144]
  hab := by decide
  hd := by
    intro p hp
    fin_cases hp
    exact satisfiesDedekindCriterion_of_certificate_lists T [78, -6, 7, -2, 1] 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T [78, -6, 7, -2, 1] 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T [78, -6, 7, -2, 1] 23 T_ofList CD23


-- @@ L171-189 verbatim
noncomputable def M5 : MaximalOrderCertificateOfUnramifiedLists 5 O Om hm where
 n := 4
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
![[0, 1, 0, 0], [0, 0, 1, 0], [1, 0, 4, 0], [1, 2, 2, 3]], 
![[0, 0, 1, 0], [1, 0, 4, 0], [4, 1, 1, 0], [0, 2, 1, 4]], 
![[0, 0, 0, 1], [1, 2, 2, 3], [0, 2, 1, 4], [0, 3, 1, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0],![1, 4, 0, 0],![1, 3, 1, 0],![0, 4, 1, 4]]
 wFrob := ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3]
 hindw := by decide
 hwFrobComp := by decide 

-- @@ L190-208 verbatim
noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 4
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
![[0, 1, 0, 0], [0, 0, 1, 0], [2, 6, 5, 0], [6, 6, 6, 4]], 
![[0, 0, 1, 0], [2, 6, 5, 0], [3, 4, 3, 0], [1, 3, 4, 2]], 
![[0, 0, 0, 1], [6, 6, 6, 4], [1, 3, 4, 2], [4, 2, 0, 5]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0],![1, 6, 0, 0],![1, 5, 1, 0],![0, 6, 1, 6]]
 wFrob := ![![1, 0, 0, 0],![0, 1, 0, 0],![0, 0, 1, 0],![0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3]
 hindw := by decide
 hwFrobComp := by decide 


-- @@ L210-210 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L212-213 verbatim
lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ


-- @@ L215-222 verbatim
lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 


-- @@ L224-228 verbatim
lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


-- @@ L230-239 verbatim
instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 

--  We add these shortcuts for faster typeclass inference  
 
-- @@ L240-240 verbatim
noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 
-- @@ L241-241 verbatim
noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 
-- @@ L242-242 verbatim
noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 
-- @@ L243-243 verbatim
noncomputable instance  : Algebra ℤ O := O.algebra'  


