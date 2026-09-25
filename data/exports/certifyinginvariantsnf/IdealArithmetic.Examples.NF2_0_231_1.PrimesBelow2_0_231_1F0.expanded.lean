
import IdealArithmetic.Examples.NF2_0_231_1.RI2_0_231_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve


-- @@ L7-7 verbatim
set_option linter.all false


-- @@ L9-9 verbatim
open Classical Polynomial


-- @@ L11-11 verbatim
noncomputable section 

-- @@ L12-12 verbatim
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}


-- @@ L14-14 verbatim
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![0, 1]] i)))


-- @@ L16-23 verbatim
def SI2N0: IdealEqSpanCertificate' Table ![![2, 0], ![0, 1]] 
 ![![2, 0], ![0, 1]] where
  M :=![![![2, 0], ![0, 2]], ![![0, 1], ![-58, 1]]]
  hmulB := by decide  
  f := ![![![1, 0], ![0, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![0, 2]], ![![0, 1], ![-29, 1]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L25-26 verbatim
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)


-- @@ L28-28 verbatim
lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0


-- @@ L30-30 verbatim
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)))


-- @@ L32-39 verbatim
def SI2N1: IdealEqSpanCertificate' Table ![![2, 0], ![1, 1]] 
 ![![2, 0], ![1, 1]] where
  M :=![![![2, 0], ![0, 2]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 2]], ![![0, 1], ![-30, 2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L41-42 verbatim
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)


-- @@ L44-44 verbatim
lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

-- @@ L45-51 verbatim
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0], ![0, 1]] ![![2, 0], ![1, 1]]
  ![![2, 0]] where
 M :=  ![![![4, 0], ![2, 2]], ![![0, 2], ![-58, 2]]]
 hmul := by decide  
 g :=  ![![![![2, 0]], ![![1, 1]]], ![![![0, 1]], ![![-29, 1]]]]
 hle2 := by decide  



-- @@ L54-62 expanded
def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1]
    where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by
    simp only [← Fin.prod_ofFn]
    exact
      ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide)
        (IdealMulLeChainCertificate.cons IdealMulLeChainCertificate.nil MulI2N0)


-- @@ L64-64 verbatim
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))


-- @@ L66-73 verbatim
def SI3N0: IdealEqSpanCertificate' Table ![![3, 0], ![1, 1]] 
 ![![3, 0], ![1, 1]] where
  M :=![![![3, 0], ![0, 3]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 3]], ![![0, 1], ![-20, 2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L75-76 verbatim
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)


-- @@ L78-78 verbatim
lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

-- @@ L79-85 verbatim
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![3, 0]] where
 M :=  ![![![9, 0], ![3, 3]], ![![3, 3], ![-57, 3]]]
 hmul := by decide  
 g :=  ![![![![3, 0]], ![![1, 1]]], ![![![1, 1]], ![![-19, 1]]]]
 hle2 := by decide  


-- @@ L87-95 expanded
def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0]
    where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by
    simp only [← Fin.prod_ofFn]
    exact
      ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide)
        (IdealMulLeChainCertificate.cons IdealMulLeChainCertificate.nil MulI3N0)


-- @@ L96-96 verbatim
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}


-- @@ L98-98 verbatim
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![1, 1]] i)))


-- @@ L100-107 verbatim
def SI5N0: IdealEqSpanCertificate' Table ![![5, 0], ![1, 1]] 
 ![![5, 0], ![1, 1]] where
  M :=![![![5, 0], ![0, 5]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide  
  f := ![![![0, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 5]], ![![0, 1], ![-12, 2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L109-110 verbatim
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)


-- @@ L112-112 verbatim
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0


-- @@ L114-114 verbatim
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![3, 1]] i)))


-- @@ L116-123 verbatim
def SI5N1: IdealEqSpanCertificate' Table ![![5, 0], ![3, 1]] 
 ![![5, 0], ![3, 1]] where
  M :=![![![5, 0], ![0, 5]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 5]], ![![0, 1], ![-14, 4]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L125-126 verbatim
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)


-- @@ L128-128 verbatim
lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

-- @@ L129-135 verbatim
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0], ![1, 1]] ![![5, 0], ![3, 1]]
  ![![5, 0]] where
 M :=  ![![![25, 0], ![15, 5]], ![![5, 5], ![-55, 5]]]
 hmul := by decide  
 g :=  ![![![![5, 0]], ![![3, 1]]], ![![![1, 1]], ![![-11, 1]]]]
 hle2 := by decide  



-- @@ L138-146 expanded
def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1]
    where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by
    simp only [← Fin.prod_ofFn]
    exact
      ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide)
        (IdealMulLeChainCertificate.cons IdealMulLeChainCertificate.nil MulI5N0)


-- @@ L148-148 verbatim
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))


-- @@ L150-157 verbatim
def SI7N0: IdealEqSpanCertificate' Table ![![7, 0], ![3, 1]] 
 ![![7, 0], ![3, 1]] where
  M :=![![![7, 0], ![0, 7]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 7]], ![![0, 1], ![-10, 4]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L159-160 verbatim
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)


-- @@ L162-162 verbatim
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

-- @@ L163-169 verbatim
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0], ![3, 1]] ![![7, 0], ![3, 1]]
  ![![7, 0]] where
 M :=  ![![![49, 0], ![21, 7]], ![![21, 7], ![-49, 7]]]
 hmul := by decide  
 g :=  ![![![![7, 0]], ![![3, 1]]], ![![![3, 1]], ![![-7, 1]]]]
 hle2 := by decide  


-- @@ L171-179 expanded
def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0]
    where
  Ip := by
    intro i
    fin_cases i
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by
    simp only [← Fin.prod_ofFn]
    exact
      ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide)
        (IdealMulLeChainCertificate.cons IdealMulLeChainCertificate.nil MulI7N0)


-- @@ L182-185 verbatim
lemma PB10I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 9 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 9 (by omega)


-- @@ L187-243 verbatim
def PB10I0 : PrimesBelowBoundCertificateInterval' O 1 9 10 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![2, 3, 5, 7]
  hP := PB10I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
    · exact ![3, 3]
    · exact ![5, 5]
    · exact ![7, 7]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
  Il := ![[I2N0, I2N1], [I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
