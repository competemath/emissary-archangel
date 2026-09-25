
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF6_4_19208000_1.Irreducible6_4_19208000_1
import IdealArithmetic.DedekindProject.Discriminant




-- @@ L10-10 verbatim
open Polynomial Module


-- @@ L12-12 verbatim
noncomputable def T : ℤ[X] := X^6 - 5*X^4 - 50*X^2 + 125

-- @@ L13-13 verbatim
lemma T_def : T = X^6 - 5*X^4 - 50*X^2 + 125 := rfl


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
local notation "l" => [125, 0, -50, 0, -5, 0, 1]


-- @@ L27-28 verbatim
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _


-- @@ L30-30 verbatim
local notation "θ" => Adj.root


-- @@ L32-34 expanded
lemma T_ofList : ofList [125, 0, -50, 0, -5, 0, 1] = T := by rw [T_def]; norm_num;
  ring
    -- We build the subalgebra with integral basis [1, a, 1/5*a^2, 1/5*a^3, 1/25*a^4, 1/25*a^5]


-- @@ L36-56 expanded
noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T [125, 0, -50, 0, -5, 0, 1]
    where
  d := 25
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B :=
    ![![25, 0, 0, 0, 0, 0], ![0, 25, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0],
      ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  a :=
    ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]],
      ![![0, 1, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 5, 0],
        ![0, 0, 0, 0, 0, 1], ![-5, 0, 10, 0, 5, 0]],
      ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1],
        ![-1, 0, 2, 0, 1, 0], ![0, -1, 0, 2, 0, 1]],
      ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 5, 0], ![0, 0, 0, 0, 0, 1], ![-5, 0, 10, 0, 5, 0],
        ![0, -1, 0, 2, 0, 1], ![-5, 0, 5, 0, 15, 0]],
      ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-1, 0, 2, 0, 1, 0], ![0, -1, 0, 2, 0, 1],
        ![-1, 0, 1, 0, 3, 0], ![0, -1, 0, 1, 0, 3]],
      ![![0, 0, 0, 0, 0, 1], ![-5, 0, 10, 0, 5, 0], ![0, -1, 0, 2, 0, 1], ![-5, 0, 5, 0, 15, 0],
        ![0, -1, 0, 1, 0, 3], ![-15, 0, 25, 0, 20, 0]]]
  s :=
    ![![[], [], [], [], [], []], ![[], [], [], [], [], [-25]], ![[], [], [], [], [-5], [0, -5]],
      ![[], [], [], [-25], [0, -5], [-25, 0, -5]],
      ![[], [], [-5], [0, -5], [-5, 0, -1], [0, -5, 0, -1]],
      ![[], [-25], [0, -5], [-25, 0, -5], [0, -5, 0, -1], [-75, 0, -5, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide


-- @@ L58-58 expanded
lemma T_degree : T.natDegree = 6 :=
  (SubalgebraBuilderOfList T [125, 0, -50, 0, -5, 0, 1] BQ).hdeg


-- @@ L60-62 expanded
lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList [125, 0, -50, 0, -5, 0, 1] rfl


-- @@ L64-64 verbatim
lemma T_irreducible : Irreducible T := irreducible_T


-- @@ L66-66 verbatim
noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K


-- @@ L68-68 expanded
noncomputable def O :=
  subalgebraOfBuilderLists T [125, 0, -50, 0, -5, 0, 1] BQ


-- @@ L70-70 expanded
def hm : O ≤ Om :=
  le_integralClosure_of_basis O (basisOfBuilderLists T [125, 0, -50, 0, -5, 0, 1] BQ)


-- @@ L72-74 verbatim
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)


-- @@ L76-76 verbatim
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'

-- @@ L77-77 verbatim
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'


-- @@ L79-80 expanded
noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T [125, 0, -50, 0, -5, 0, 1] BQ


-- @@ L82-82 verbatim
noncomputable def B : Basis (Fin 6) ℤ O := timesTableO.basis

-- @@ L83-89 verbatim
def Table : Fin 6 → Fin 6 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 5, 0], [0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0]], 
 ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-1, 0, 2, 0, 1, 0], [0, -1, 0, 2, 0, 1]], 
 ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 5, 0], [0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0], [0, -1, 0, 2, 0, 1], [-5, 0, 5, 0, 15, 0]], 
 ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-1, 0, 2, 0, 1, 0], [0, -1, 0, 2, 0, 1], [-1, 0, 1, 0, 3, 0], [0, -1, 0, 1, 0, 3]], 
 ![[0, 0, 0, 0, 0, 1], [-5, 0, 10, 0, 5, 0], [0, -1, 0, 2, 0, 1], [-5, 0, 5, 0, 15, 0], [0, -1, 0, 1, 0, 3], [-15, 0, 25, 0, 20, 0]]]


-- @@ L91-91 verbatim
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide


-- @@ L93-94 expanded
lemma hroot_mem : Adj.root ∈ O := by
  refine root_in_subalgebra_lists T [125, 0, -50, 0, -5, 0, 1] BQ ![0, 1, 0, 0, 0, 0] [] (by decide)


-- @@ L95-95 verbatim
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)

-- @@ L96-96 verbatim
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

-- @@ L97-97 verbatim
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)


-- @@ L99-113 expanded
def CD2 : CertificateDedekindCriterionLists [125, 0, -50, 0, -5, 0, 1] 2
    where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1]
  f := [-62, 0, 26, 1, 3, 1]
  g := [1, 0, 1, 1]
  h := [1, 0, 1, 1]
  a := [1]
  b := [1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L115-129 expanded
def CD7 : CertificateDedekindCriterionLists [125, 0, -50, 0, -5, 0, 1] 7
    where
  n := 3
  a' := [5]
  b' := [0, 1]
  k := [1]
  f := [-17, 0, 10, 0, 2]
  g := [3, 0, 1]
  h := [2, 0, 6, 0, 1]
  a := [6]
  b := [4, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl


-- @@ L131-149 expanded
noncomputable def D : CertificateDedekindAlmostAllLists T [125, 0, -50, 0, -5, 0, 1] [5]
    where
  n := 3
  p := ![2, 5, 7]
  exp := ![6, 15, 4]
  pdgood := [2, 7]
  hsub := by decide
  hp := by
    intro i; fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp7.out
  a := [37515625000000, 0, 0, 0, -1929375000000]
  b := [0, -18757812500000, 0, -535937500000, 0, 321562500000]
  hab := by decide
  hd := by
    intro p hp
    fin_cases hp
    exact
      satisfiesDedekindCriterion_of_certificate_lists T [125, 0, -50, 0, -5, 0, 1] 2 T_ofList CD2
    exact
      satisfiesDedekindCriterion_of_certificate_lists T [125, 0, -50, 0, -5, 0, 1] 7 T_ofList CD7


-- @@ L151-188 verbatim
noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 3
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [4, 0, 2, 0, 1, 0], [0, 4, 0, 2, 0, 1]], 
![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [4, 0, 2, 0, 1, 0], [0, 4, 0, 2, 0, 1], [4, 0, 1, 0, 3, 0], [0, 4, 0, 1, 0, 3]], 
![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0], [0, 4, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0, 0],![2, 0, 0, 0, 4, 0],![3, 0, 1, 0, 4, 0]]
 v := ![![0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0, 0],![2, 0, 0, 0, 4, 0],![3, 0, 1, 0, 4, 0]]
 wFrob := ![![1, 0, 0, 0, 0, 0],![0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0]]
 v_ind := ![1, 3, 5]
 w_ind := ![0, 2, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 0, 6, 0, 4, 2],![6, 8, 0, 4, 0, 2],![0, 4, 3, 1, 0, 3],![0, 0, 0, 6, 0, 8],![0, 2, 0, 1, 0, 3],![0, 6, 0, 4, 0, 8]]
 w1 := ![0, 2, 0]
 w2 := ![0, 1, 0]
 a := ![![-48, 60, 160],![-40, 252, 380],![-40, 110, 316],![-280, 460, 680],![-60, 110, 270],![-180, 360, 760]]
 c := ![![-170, -55, 80],![-50, -5, 20],![-80, -30, 40],![-98, -25, 40],![-30, -4, 10],![-90, -15, 32]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 



-- @@ L191-191 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L193-194 verbatim
lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ


-- @@ L196-203 verbatim
lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr


-- @@ L205-209 verbatim
lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]


-- @@ L211-218 verbatim
instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O

 
-- @@ L220-220 verbatim
noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 
-- @@ L221-221 verbatim
noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 
-- @@ L222-222 verbatim
noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 
-- @@ L223-223 verbatim
noncomputable instance  : Algebra ℤ O := O.algebra'

