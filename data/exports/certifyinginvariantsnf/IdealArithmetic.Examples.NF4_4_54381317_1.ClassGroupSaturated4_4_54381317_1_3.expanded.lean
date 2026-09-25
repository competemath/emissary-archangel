import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1


-- @@ L9-9 verbatim
set_option linter.all false


-- @@ L11-11 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L13-13 verbatim
noncomputable section 


-- @@ L15-15 verbatim
namespace Sat3 

-- @@ L16-16 verbatim
instance hq97 : Fact $ Nat.Prime 97 := {out := by norm_num}

-- @@ L17-17 verbatim
instance hq43 : Fact $ Nat.Prime 43 := {out := by norm_num}

-- @@ L18-18 verbatim
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}

-- @@ L19-19 verbatim
instance hq151 : Fact $ Nat.Prime 151 := {out := by norm_num}


-- @@ L21-28 expanded
def R97 : IsOrderOf (5 : ZMod 97) 96 where
  m := 2
  P := ![2, 3]
  e := ![5, 1]
  hP := fun i => by fin_cases i <;> norm_num
  hm := by rfl
  hid := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  hnid := fun i => by fin_cases i;
    repeat
      ( try simp only [Int.cast_ofNat]
        erw [← squareAndMultiply_eq_pow]
        repeat (unfold squareAndMultiply_aux; dsimp)
        try decide)


-- @@ L30-37 expanded
def R43 : IsOrderOf (3 : ZMod 43) 42 where
  m := 3
  P := ![2, 3, 7]
  e := ![1, 1, 1]
  hP := fun i => by fin_cases i <;> norm_num
  hm := by rfl
  hid := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  hnid := fun i => by fin_cases i;
    repeat
      ( try simp only [Int.cast_ofNat]
        erw [← squareAndMultiply_eq_pow]
        repeat (unfold squareAndMultiply_aux; dsimp)
        try decide)


-- @@ L39-46 expanded
def R61 : IsOrderOf (2 : ZMod 61) 60 where
  m := 3
  P := ![2, 3, 5]
  e := ![2, 1, 1]
  hP := fun i => by fin_cases i <;> norm_num
  hm := by rfl
  hid := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  hnid := fun i => by fin_cases i;
    repeat
      ( try simp only [Int.cast_ofNat]
        erw [← squareAndMultiply_eq_pow]
        repeat (unfold squareAndMultiply_aux; dsimp)
        try decide)


-- @@ L48-55 expanded
def R151 : IsOrderOf (6 : ZMod 151) 150 where
  m := 3
  P := ![2, 3, 5]
  e := ![1, 1, 2]
  hP := fun i => by fin_cases i <;> norm_num
  hm := by rfl
  hid := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  hnid := fun i => by fin_cases i;
    repeat
      ( try simp only [Int.cast_ofNat]
        erw [← squareAndMultiply_eq_pow]
        repeat (unfold squareAndMultiply_aux; dsimp)
        try decide)


-- @@ L57-57 verbatim
def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0], ![1, 1, 0, 0]] i)))

-- @@ L58-58 verbatim
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0], ![-18, 1, 0, 0]] i)))

-- @@ L59-59 verbatim
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0], ![-27, 1, 0, 0]] i)))

-- @@ L60-60 verbatim
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0], ![-8, 1, 0, 0]] i)))

-- @@ L61-61 verbatim
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0], ![-42, 1, 0, 0]] i)))


-- @@ L63-70 verbatim
def A0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0], ![1, 1, 0, 0]] 
 ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0], ![0, 43, 0, 0], ![0, 0, 43, 0], ![0, 0, 0, 43]], ![![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 0, 1, 1], ![383, 332, 80, 2]]]
  hmulB := by decide  
  f := ![![![0, -4, -4, -1], ![43, 129, 43, 0]], ![![0, 0, 1, 1], ![1, 0, -43, 0]], ![![0, -2, -2, -1], ![42, 44, 43, 0]], ![![0, 0, 1, 1], ![1, -1, -42, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 43, 0, 0], ![-42, 0, 43, 0], ![-1, 0, 0, 43]], ![![0, 1, 0, 0], ![-1, 1, 1, 0], ![-1, 0, 1, 1], ![-77, 332, 80, 2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L72-73 verbatim
lemma N0 : Nat.card (O ⧸ I0) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)


-- @@ L75-82 verbatim
def A1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0], ![-18, 1, 0, 0]] 
 ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0], ![0, 43, 0, 0], ![0, 0, 43, 0], ![0, 0, 0, 43]], ![![-18, 1, 0, 0], ![0, -18, 1, 0], ![0, 0, -18, 1], ![383, 332, 80, -17]]]
  hmulB := by decide  
  f := ![![![361, 34, 6045, -336], ![860, 129, 14448, 0]], ![![199, 25, 3670, -204], ![474, 86, 8772, 0]], ![![188, 26, 2806, -156], ![448, 87, 6708, 0]], ![![136, 18, 2249, -125], ![324, 61, 5376, 0]]]
  g := ![![![1, 0, 0, 0], ![-25, 43, 0, 0], ![-20, 0, 43, 0], ![-16, 0, 0, 43]], ![![-1, 1, 0, 0], ![10, -18, 1, 0], ![8, 0, -18, 1], ![-215, 332, 80, -17]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L84-85 verbatim
lemma N1 : Nat.card (O ⧸ I1) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)


-- @@ L87-94 verbatim
def A2: IdealEqSpanCertificate' Table ![![151, 0, 0, 0], ![-27, 1, 0, 0]] 
 ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] where
  M :=![![![151, 0, 0, 0], ![0, 151, 0, 0], ![0, 0, 151, 0], ![0, 0, 0, 151]], ![![-27, 1, 0, 0], ![0, -27, 1, 0], ![0, 0, -27, 1], ![383, 332, 80, -26]]]
  hmulB := by decide  
  f := ![![![973, 72, 92228, -3416], ![5436, 604, 515816, 0]], ![![1567, -76198, 2928, -4], ![8759, -425820, 604, 0]], ![![194, 20, 15875, -588], ![1084, 152, 88788, 0]], ![![644, 62, 59856, -2217], ![3598, 480, 334768, 0]]]
  g := ![![![1, 0, 0, 0], ![-124, 151, 0, 0], ![-26, 0, 151, 0], ![-98, 0, 0, 151]], ![![-1, 1, 0, 0], ![22, -27, 1, 0], ![4, 0, -27, 1], ![-267, 332, 80, -26]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L96-97 verbatim
lemma N2 : Nat.card (O ⧸ I2) = 151 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)


-- @@ L99-106 verbatim
def A3: IdealEqSpanCertificate' Table ![![61, 0, 0, 0], ![-8, 1, 0, 0]] 
 ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0], ![0, 61, 0, 0], ![0, 0, 61, 0], ![0, 0, 0, 61]], ![![-8, 1, 0, 0], ![0, -8, 1, 0], ![0, 0, -8, 1], ![383, 332, 80, -7]]]
  hmulB := by decide  
  f := ![![![217, -19, 3679, -460], ![1647, 61, 28060, 0]], ![![193, -16, 3311, -414], ![1465, 61, 25254, 0]], ![![210, -18, 3495, -437], ![1594, 62, 26657, 0]], ![![145, -9, 2231, -279], ![1101, 69, 17020, 0]]]
  g := ![![![1, 0, 0, 0], ![-53, 61, 0, 0], ![-58, 0, 61, 0], ![-37, 0, 0, 61]], ![![-1, 1, 0, 0], ![6, -8, 1, 0], ![7, 0, -8, 1], ![-354, 332, 80, -7]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L108-109 verbatim
lemma N3 : Nat.card (O ⧸ I3) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)


-- @@ L111-118 verbatim
def A4: IdealEqSpanCertificate' Table ![![97, 0, 0, 0], ![-42, 1, 0, 0]] 
 ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] where
  M :=![![![97, 0, 0, 0], ![0, 97, 0, 0], ![0, 0, 97, 0], ![0, 0, 0, 97]], ![![-42, 1, 0, 0], ![0, -42, 1, 0], ![0, 0, -42, 1], ![383, 332, 80, -41]]]
  hmulB := by decide  
  f := ![![![6637, -83066, 2310, -8], ![15326, -191478, 776, 0]], ![![3823, -47089, 1329, -5], ![8828, -108543, 485, 0]], ![![5395, -67622, 1901, -7], ![12458, -155878, 679, 0]], ![![1436, -17068, 490, -2], ![3316, -39340, 195, 0]]]
  g := ![![![1, 0, 0, 0], ![-55, 97, 0, 0], ![-79, 0, 97, 0], ![-20, 0, 0, 97]], ![![-1, 1, 0, 0], ![23, -42, 1, 0], ![34, 0, -42, 1], ![-241, 332, 80, -41]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L120-121 verbatim
lemma N4 : Nat.card (O ⧸ I4) = 97 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)


-- @@ L123-127 verbatim
def Log00Mem : IdealMemCertificate B I0
  ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] ![1, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 1, 0, 0]
 hmem := by decide


-- @@ L129-143 expanded
def Log00 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 1, 0, 0]
  hxeq := rfl
  m := 2
  C := ![1, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log00Mem
  k := 27
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L145-149 verbatim
def Log01Mem : IdealMemCertificate B I0
  ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] ![-148, -67, -4, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -67, -4, 1]
 hmem := by decide


-- @@ L151-165 expanded
def Log01 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-124, -67, -4, 1]
  hxeq := rfl
  m := 24
  C := ![-148, -67, -4, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log01Mem
  k := 40
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L167-171 verbatim
def Log02Mem : IdealMemCertificate B I0
  ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] ![-183, -110, -11, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![9, -110, -11, 2]
 hmem := by decide


-- @@ L173-187 expanded
def Log02 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-173, -110, -11, 2]
  hxeq := rfl
  m := 10
  C := ![-183, -110, -11, 2]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log02Mem
  k := 10
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L189-193 verbatim
def Log03Mem : IdealMemCertificate B I0
  ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] ![1, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 1, 0, 0]
 hmem := by decide


-- @@ L195-209 expanded
def Log03 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 1, 0, 0]
  hxeq := rfl
  m := 4
  C := ![1, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log03Mem
  k := 12
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L211-215 verbatim
def Log04Mem : IdealMemCertificate B I0
  ![![43, 0, 0, 0], ![1, 1, 0, 0], ![42, 0, 1, 0], ![1, 0, 0, 1]] ![2, 2, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 2, 0, 0]
 hmem := by decide


-- @@ L217-231 expanded
def Log04 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 2, 0, 0]
  hxeq := rfl
  m := 3
  C := ![2, 2, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log04Mem
  k := 1
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L233-237 verbatim
def Log10Mem : IdealMemCertificate B I1
  ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] ![-18, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L239-253 expanded
def Log10 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 1, 0, 0]
  hxeq := rfl
  m := 21
  C := ![-18, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log10Mem
  k := 36
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L255-259 verbatim
def Log11Mem : IdealMemCertificate B I1
  ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] ![-148, -67, -4, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![37, -67, -4, 1]
 hmem := by decide


-- @@ L261-275 expanded
def Log11 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-124, -67, -4, 1]
  hxeq := rfl
  m := 24
  C := ![-148, -67, -4, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log11Mem
  k := 40
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L277-281 verbatim
def Log12Mem : IdealMemCertificate B I1
  ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] ![-186, -110, -11, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![64, -110, -11, 2]
 hmem := by decide


-- @@ L283-297 expanded
def Log12 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 2
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-173, -110, -11, 2]
  hxeq := rfl
  m := 13
  C := ![-186, -110, -11, 2]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log12Mem
  k := 32
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L299-303 verbatim
def Log13Mem : IdealMemCertificate B I1
  ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] ![-18, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L305-319 expanded
def Log13 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 1, 0, 0]
  hxeq := rfl
  m := 23
  C := ![-18, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log13Mem
  k := 16
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L321-325 verbatim
def Log14Mem : IdealMemCertificate B I1
  ![![43, 0, 0, 0], ![25, 1, 0, 0], ![20, 0, 1, 0], ![16, 0, 0, 1]] ![-36, 2, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 2, 0, 0]
 hmem := by decide


-- @@ L327-341 expanded
def Log14 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 2, 0, 0]
  hxeq := rfl
  m := 41
  C := ![-36, 2, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log14Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L343-347 verbatim
def Log20Mem : IdealMemCertificate B I2
  ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] ![-27, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L349-363 expanded
def Log20 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 1, 0, 0]
  hxeq := rfl
  m := 30
  C := ![-27, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log20Mem
  k := 113
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L365-369 verbatim
def Log21Mem : IdealMemCertificate B I2
  ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] ![-160, -67, -4, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![54, -67, -4, 1]
 hmem := by decide


-- @@ L371-385 expanded
def Log21 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-124, -67, -4, 1]
  hxeq := rfl
  m := 36
  C := ![-160, -67, -4, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log21Mem
  k := 2
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L387-391 verbatim
def Log22Mem : IdealMemCertificate B I2
  ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] ![-291, -110, -11, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![89, -110, -11, 2]
 hmem := by decide


-- @@ L393-407 expanded
def Log22 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-173, -110, -11, 2]
  hxeq := rfl
  m := 118
  C := ![-291, -110, -11, 2]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log22Mem
  k := 100
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L409-413 verbatim
def Log23Mem : IdealMemCertificate B I2
  ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] ![-27, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L415-429 expanded
def Log23 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 1, 0, 0]
  hxeq := rfl
  m := 32
  C := ![-27, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log23Mem
  k := 50
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L431-435 verbatim
def Log24Mem : IdealMemCertificate B I2
  ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] ![-54, 2, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2, 2, 0, 0]
 hmem := by decide


-- @@ L437-451 expanded
def Log24 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 2, 0, 0]
  hxeq := rfl
  m := 59
  C := ![-54, 2, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log24Mem
  k := 30
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L453-457 verbatim
def Log30Mem : IdealMemCertificate B I3
  ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] ![-8, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L459-473 expanded
def Log30 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 1, 0, 0]
  hxeq := rfl
  m := 11
  C := ![-8, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log30Mem
  k := 15
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L475-479 verbatim
def Log31Mem : IdealMemCertificate B I3
  ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] ![-147, -67, -4, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![59, -67, -4, 1]
 hmem := by decide


-- @@ L481-495 expanded
def Log31 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-124, -67, -4, 1]
  hxeq := rfl
  m := 23
  C := ![-147, -67, -4, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log31Mem
  k := 57
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L497-501 verbatim
def Log32Mem : IdealMemCertificate B I3
  ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] ![-233, -110, -11, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![101, -110, -11, 2]
 hmem := by decide


-- @@ L503-517 expanded
def Log32 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-173, -110, -11, 2]
  hxeq := rfl
  m := 60
  C := ![-233, -110, -11, 2]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log32Mem
  k := 30
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L519-523 verbatim
def Log33Mem : IdealMemCertificate B I3
  ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] ![-8, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L525-539 expanded
def Log33 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 1, 0, 0]
  hxeq := rfl
  m := 13
  C := ![-8, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log33Mem
  k := 40
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L541-545 verbatim
def Log34Mem : IdealMemCertificate B I3
  ![![61, 0, 0, 0], ![53, 1, 0, 0], ![58, 0, 1, 0], ![37, 0, 0, 1]] ![-16, 2, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, 2, 0, 0]
 hmem := by decide


-- @@ L547-561 expanded
def Log34 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 2, 0, 0]
  hxeq := rfl
  m := 21
  C := ![-16, 2, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log34Mem
  k := 55
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L563-567 verbatim
def Log40Mem : IdealMemCertificate B I4
  ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] ![-42, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L569-583 expanded
def Log40 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R97) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 1, 0, 0]
  hxeq := rfl
  m := 45
  C := ![-42, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log40Mem
  k := 45
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L585-589 verbatim
def Log41Mem : IdealMemCertificate B I4
  ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] ![-198, -67, -4, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![39, -67, -4, 1]
 hmem := by decide


-- @@ L591-605 expanded
def Log41 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R97) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-124, -67, -4, 1]
  hxeq := rfl
  m := 74
  C := ![-198, -67, -4, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log41Mem
  k := 29
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L607-611 verbatim
def Log42Mem : IdealMemCertificate B I4
  ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] ![-186, -110, -11, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![69, -110, -11, 2]
 hmem := by decide


-- @@ L613-627 expanded
def Log42 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R97) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 1
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-173, -110, -11, 2]
  hxeq := rfl
  m := 13
  C := ![-186, -110, -11, 2]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log42Mem
  k := 25
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L629-633 verbatim
def Log43Mem : IdealMemCertificate B I4
  ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] ![-42, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 1, 0, 0]
 hmem := by decide


-- @@ L635-649 expanded
def Log43 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R97) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 1, 0, 0]
  hxeq := rfl
  m := 47
  C := ![-42, 1, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log43Mem
  k := 84
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L651-655 verbatim
def Log44Mem : IdealMemCertificate B I4
  ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] ![-84, 2, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-2, 2, 0, 0]
 hmem := by decide


-- @@ L657-671 expanded
def Log44 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R97) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0
    where
  r := 4
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![5, 2, 0, 0]
  hxeq := rfl
  m := 89
  C := ![-84, 2, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log44Mem
  k := 54
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L673-673 verbatim
end Sat3
