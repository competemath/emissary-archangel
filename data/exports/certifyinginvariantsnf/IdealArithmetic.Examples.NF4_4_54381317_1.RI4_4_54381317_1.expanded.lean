
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF4_4_54381317_1.Irreducible4_4_54381317_1
import IdealArithmetic.DedekindProject.Discriminant




-- @@ L10-10 verbatim
open Polynomial Module


-- @@ L12-12 verbatim
noncomputable def T : ℤ[X] := X^4 - X^3 - 80*X^2 - 332*X - 383 

-- @@ L13-13 verbatim
lemma T_def : T = X^4 - X^3 - 80*X^2 - 332*X - 383 := rfl


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
local notation "l" => [-383, -332, -80, -1, 1]


-- @@ L27-28 verbatim
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _


-- @@ L30-30 verbatim
local notation "θ" => Adj.root


-- @@ L32-35 expanded
lemma T_ofList : ofList [-383, -332, -80, -1, 1] = T := by rw [T_def]; norm_num;
  ring
    -- We build the subalgebra with integral basis [1, a, a^2, a^3]


-- @@ L37-55 expanded
noncomputable def BQ : SubalgebraBuilderLists 4 ℤ ℚ K T [-383, -332, -80, -1, 1]
    where
  d := 1
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
  a :=
    ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
      ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![383, 332, 80, 1]],
      ![![0, 0, 1, 0], ![0, 0, 0, 1], ![383, 332, 80, 1], ![383, 715, 412, 81]],
      ![![0, 0, 0, 1], ![383, 332, 80, 1], ![383, 715, 412, 81], ![31023, 27275, 7195, 493]]]
  s :=
    ![![[], [], [], []], ![[], [], [], [-1]], ![[], [], [-1], [-1, -1]],
      ![[], [-1], [-1, -1], [-81, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide


-- @@ L57-57 expanded
lemma T_degree : T.natDegree = 4 :=
  (SubalgebraBuilderOfList T [-383, -332, -80, -1, 1] BQ).hdeg


-- @@ L59-61 expanded
lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList [-383, -332, -80, -1, 1] rfl


-- @@ L63-63 verbatim
lemma T_irreducible : Irreducible T := irreducible_T


-- @@ L65-65 verbatim
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K


-- @@ L67-67 expanded
noncomputable def O :=
  subalgebraOfBuilderLists T [-383, -332, -80, -1, 1] BQ


-- @@ L69-69 expanded
def hm : O ≤ Om :=
  le_integralClosure_of_basis O (basisOfBuilderLists T [-383, -332, -80, -1, 1] BQ)


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
  timesTableOfSubalgebraBuilderLists T [-383, -332, -80, -1, 1] BQ


-- @@ L81-81 verbatim
noncomputable def B : Basis (Fin 4) ℤ O := timesTableO.basis 


-- @@ L83-87 verbatim
def Table : Fin 4 → Fin 4 → List ℤ := 
 ![ ![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], 
 ![[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [383, 332, 80, 1]], 
 ![[0, 0, 1, 0], [0, 0, 0, 1], [383, 332, 80, 1], [383, 715, 412, 81]], 
 ![[0, 0, 0, 1], [383, 332, 80, 1], [383, 715, 412, 81], [31023, 27275, 7195, 493]]]


-- @@ L89-89 verbatim
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide


-- @@ L91-92 expanded
lemma hroot_mem : Adj.root ∈ O := by
  refine root_in_subalgebra_lists T [-383, -332, -80, -1, 1] BQ ![0, 1, 0, 0] [] (by decide)


-- @@ L94-94 verbatim
instance hp17: Fact $ Nat.Prime 17 := fact_iff.2 (by norm_num)

-- @@ L95-95 verbatim
instance hp61: Fact $ Nat.Prime 61 := fact_iff.2 (by norm_num)

-- @@ L96-96 verbatim
instance hp229: Fact $ Nat.Prime 229 := fact_iff.2 (by norm_num)


-- @@ L98-112 expanded
def CD17 : CertificateDedekindCriterionLists [-383, -332, -80, -1, 1] 17
    where
  n := 2
  a' := [4]
  b' := [13, 10]
  k := [13, 2, 1]
  f := [25, 24, 9, 1]
  g := [6, 10, 9, 1]
  h := [7, 1]
  a := [5, 15, 8]
  b := [2, 2, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L114-128 expanded
def CD61 : CertificateDedekindCriterionLists [-383, -332, -80, -1, 1] 61
    where
  n := 2
  a' := [19, 60]
  b' := [35, 8, 41]
  k := [35, 15, 1]
  f := [28, 38, 8, 1]
  g := [25, 37, 7, 1]
  h := [53, 1]
  a := [13, 21, 37]
  b := [5, 3, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L130-144 expanded
def CD229 : CertificateDedekindCriterionLists [-383, -332, -80, -1, 1] 229
    where
  n := 2
  a' := [42]
  b' := [177, 208]
  k := [1]
  f := [48, 104, 58, 1]
  g := [103, 114, 1]
  h := [103, 114, 1]
  a := [95, 203]
  b := [38, 52, 26]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L146-165 expanded
noncomputable def D : CertificateDedekindAlmostAllLists T [-383, -332, -80, -1, 1] []
    where
  n := 3
  p := ![17, 61, 229]
  exp := ![1, 1, 2]
  pdgood := [17, 61, 229]
  hsub := by decide
  hp := by
    intro i; fin_cases i
    exact hp17.out
    exact hp61.out
    exact hp229.out
  a := [44221045, 5571112, -1520560]
  b := [-51177836, -25983943, -1487813, 380140]
  hab := by decide
  hd := by
    intro p hp
    fin_cases hp
    exact
      satisfiesDedekindCriterion_of_certificate_lists T [-383, -332, -80, -1, 1] 17 T_ofList CD17
    exact
      satisfiesDedekindCriterion_of_certificate_lists T [-383, -332, -80, -1, 1] 61 T_ofList CD61
    exact
      satisfiesDedekindCriterion_of_certificate_lists T [-383, -332, -80, -1, 1] 229 T_ofList CD229


-- @@ L168-168 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L170-171 verbatim
lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ


-- @@ L173-180 verbatim
lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 


-- @@ L182-186 verbatim
lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


-- @@ L188-197 verbatim
instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 

--  We add these shortcuts for faster typeclass inference  
 
-- @@ L198-198 verbatim
noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 
-- @@ L199-199 verbatim
noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 
-- @@ L200-200 verbatim
noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 
-- @@ L201-201 verbatim
noncomputable instance  : Algebra ℤ O := O.algebra'  


