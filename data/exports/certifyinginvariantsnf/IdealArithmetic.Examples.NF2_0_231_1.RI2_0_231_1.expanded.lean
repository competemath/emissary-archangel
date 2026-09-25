
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF2_0_231_1.Irreducible2_0_231_1
import IdealArithmetic.DedekindProject.Discriminant




-- @@ L10-10 verbatim
open Polynomial Module


-- @@ L12-12 verbatim
noncomputable def T : ℤ[X] := X^2 - X + 58 

-- @@ L13-13 verbatim
lemma T_def : T = X^2 - X + 58 := rfl


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
local notation "l" => [58, -1, 1]


-- @@ L27-28 verbatim
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _


-- @@ L30-30 verbatim
local notation "θ" => Adj.root


-- @@ L32-35 expanded
lemma T_ofList : ofList [58, -1, 1] = T := by rw [T_def]; norm_num;
  ring
    -- We build the subalgebra with integral basis [1, a]


-- @@ L37-53 expanded
noncomputable def BQ : SubalgebraBuilderLists 2 ℤ ℚ K T [58, -1, 1]
    where
  d := 1
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := ![![1, 0], ![0, 1]]
  a := ![![![1, 0], ![0, 1]], ![![0, 1], ![-58, 1]]]
  s := ![![[], []], ![[], [-1]]]
  h := Adj
  honed := by decide
  hd := by norm_num
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide


-- @@ L55-55 expanded
lemma T_degree : T.natDegree = 2 :=
  (SubalgebraBuilderOfList T [58, -1, 1] BQ).hdeg


-- @@ L57-59 expanded
lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList [58, -1, 1] rfl


-- @@ L61-61 verbatim
lemma T_irreducible : Irreducible T := irreducible_T


-- @@ L63-63 verbatim
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K


-- @@ L65-65 expanded
noncomputable def O :=
  subalgebraOfBuilderLists T [58, -1, 1] BQ


-- @@ L67-67 expanded
def hm : O ≤ Om :=
  le_integralClosure_of_basis O (basisOfBuilderLists T [58, -1, 1] BQ)


-- @@ L69-71 verbatim
noncomputable def B' : Basis (Fin 2) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)


-- @@ L73-73 verbatim
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'

-- @@ L74-74 verbatim
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'


-- @@ L76-77 expanded
noncomputable def timesTableO : TimesTable (Fin 2) ℤ O :=
  timesTableOfSubalgebraBuilderLists T [58, -1, 1] BQ


-- @@ L79-79 verbatim
noncomputable def B : Basis (Fin 2) ℤ O := timesTableO.basis 


-- @@ L81-83 verbatim
def Table : Fin 2 → Fin 2 → List ℤ := 
 ![ ![[1, 0], [0, 1]], 
 ![[0, 1], [-58, 1]]]


-- @@ L85-85 verbatim
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide


-- @@ L87-88 expanded
lemma hroot_mem : Adj.root ∈ O := by
  refine root_in_subalgebra_lists T [58, -1, 1] BQ ![0, 1] [] (by decide)


-- @@ L90-90 verbatim
instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

-- @@ L91-91 verbatim
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)

-- @@ L92-92 verbatim
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)


-- @@ L94-108 expanded
def CD3 : CertificateDedekindCriterionLists [58, -1, 1] 3
    where
  n := 2
  a' := []
  b' := [1]
  k := [1]
  f := [-19, 1]
  g := [1, 1]
  h := [1, 1]
  a := [1]
  b := [2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L110-124 expanded
def CD7 : CertificateDedekindCriterionLists [58, -1, 1] 7
    where
  n := 2
  a' := []
  b' := [1]
  k := [1]
  f := [-7, 1]
  g := [3, 1]
  h := [3, 1]
  a := [2]
  b := [5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L126-140 expanded
def CD11 : CertificateDedekindCriterionLists [58, -1, 1] 11
    where
  n := 2
  a' := []
  b' := [1]
  k := [1]
  f := [-3, 1]
  g := [5, 1]
  h := [5, 1]
  a := [4]
  b := [7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L142-161 expanded
noncomputable def D : CertificateDedekindAlmostAllLists T [58, -1, 1] []
    where
  n := 3
  p := ![3, 7, 11]
  exp := ![1, 1, 1]
  pdgood := [3, 7, 11]
  hsub := by decide
  hp := by
    intro i; fin_cases i
    exact hp3.out
    exact hp7.out
    exact hp11.out
  a := [4]
  b := [1, -2]
  hab := by decide
  hd := by
    intro p hp
    fin_cases hp
    exact satisfiesDedekindCriterion_of_certificate_lists T [58, -1, 1] 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T [58, -1, 1] 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T [58, -1, 1] 11 T_ofList CD11


-- @@ L164-164 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L166-167 verbatim
lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ


-- @@ L169-176 verbatim
lemma B_one_repr : B.equivFun.symm ![1, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 


-- @@ L178-182 verbatim
lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0] = n := by
  suffices B.equivFun.symm ![n, 0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


-- @@ L184-193 verbatim
instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 

--  We add these shortcuts for faster typeclass inference  
 
-- @@ L194-194 verbatim
noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 
-- @@ L195-195 verbatim
noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 
-- @@ L196-196 verbatim
noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 
-- @@ L197-197 verbatim
noncomputable instance  : Algebra ℤ O := O.algebra'  


