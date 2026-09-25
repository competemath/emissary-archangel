import IdealArithmetic.Examples.NF6_4_19208000_1.ClassGroupData6_4_19208000_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF6_4_19208000_1.RI6_4_19208000_1


-- @@ L9-9 verbatim
set_option linter.all false


-- @@ L11-11 verbatim
open BigOperators Classical Matrix Polynomial


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
namespace Sat2 

-- @@ L16-16 verbatim
instance hq29 : Fact $ Nat.Prime 29 := {out := by norm_num}

-- @@ L17-17 verbatim
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

-- @@ L18-18 verbatim
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}


-- @@ L20-27 expanded
def R29 : IsOrderOf (2 : ZMod 29) 28 where
  m := 2
  P := ![2, 7]
  e := ![2, 1]
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


-- @@ L29-36 expanded
def R13 : IsOrderOf (2 : ZMod 13) 12 where
  m := 2
  P := ![2, 3]
  e := ![2, 1]
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


-- @@ L38-45 expanded
def R7 : IsOrderOf (3 : ZMod 7) 6 where
  m := 2
  P := ![2, 3]
  e := ![1, 1]
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


-- @@ L47-47 verbatim
def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))

-- @@ L48-48 verbatim
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] i)))

-- @@ L49-49 verbatim
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] i)))

-- @@ L50-50 verbatim
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] i)))

-- @@ L51-51 verbatim
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] i)))

-- @@ L52-52 verbatim
def I5 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0]] i)))


-- @@ L54-61 verbatim
def A0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![0, 0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![23, -27, 46, 13, 0, -20], ![77, -56, 21, 56, 140, 0]], ![![19, -17, 24, 14, -8, -16], ![64, -28, 14, 56, 112, 0]], ![![6, 0, 1, 4, -4, -8], ![20, 10, 28, 28, 56, 0]], ![![14, -13, 20, 6, 4, -12], ![47, -22, 15, 28, 84, 0]], ![![9, -10, 18, 5, -1, -8], ![30, -20, 13, 24, 56, 0]], ![![18, -20, 34, 11, 0, -17], ![60, -40, 19, 48, 120, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 7, 0, 0, 0, 0], ![-2, 0, 7, 0, 0, 0], ![-4, 0, 0, 7, 0, 0], ![-3, 0, 0, 0, 7, 0], ![-6, 0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-4, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L63-64 verbatim
lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)


-- @@ L66-73 verbatim
def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0, 0], ![0, 2, 5, 0, 0, 0], ![0, 0, 2, 1, 0, 0], ![0, 0, 0, 2, 5, 0], ![0, 0, 0, 0, 2, 1], ![-5, 0, 10, 0, 5, 2]]]
  hmulB := by decide  
  f := ![![![11, 3, 23, 182, 546, 63], ![-65, 13, -182, -1092, -819, 0]], ![![-2, -3, 9, 35, 98, 14], ![14, 13, -91, -182, -182, 0]], ![![5, 1, 11, 105, 315, 35], ![-29, 8, -91, -637, -455, 0]], ![![8, 2, 22, 167, 511, 63], ![-46, 10, -168, -1001, -819, 0]], ![![1, -1, 3, 42, 125, 14], ![-5, 9, -42, -252, -182, 0]], ![![5, 1, 12, 98, 294, 34], ![-29, 8, -98, -588, -441, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-2, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-7, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-3, 2, 5, 0, 0, 0], ![-2, 0, 2, 1, 0, 0], ![-3, 0, 0, 2, 5, 0], ![-1, 0, 0, 0, 2, 1], ![-8, 0, 10, 0, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L75-76 verbatim
lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)


-- @@ L78-85 verbatim
def A2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-2, 1, 0, 0, 0, 0], ![0, -2, 5, 0, 0, 0], ![0, 0, -2, 1, 0, 0], ![0, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-5, 0, 10, 0, 5, -2]]]
  hmulB := by decide  
  f := ![![![19, -7, 23, 0, 91, -63], ![117, 13, 182, 91, 819, 0]], ![![17, -6, 23, 0, 77, -56], ![105, 13, 182, 91, 728, 0]], ![![13, -5, 11, 7, 35, -35], ![81, 8, 91, 91, 455, 0]], ![![3, -1, 1, -1, 14, -7], ![19, 3, 14, 0, 91, 0]], ![![5, -1, 3, 0, 20, -14], ![31, 9, 42, 21, 182, 0]], ![![10, -4, 11, 0, 42, -29], ![62, 5, 84, 42, 378, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-11, 13, 0, 0, 0, 0], ![-7, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-3, 0, 0, 0, 13, 0], ![-6, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![-1, -2, 5, 0, 0, 0], ![1, 0, -2, 1, 0, 0], ![-1, 0, 0, -2, 5, 0], ![0, 0, 0, 0, -2, 1], ![-6, 0, 10, 0, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L87-88 verbatim
lemma N2 : Nat.card (O ⧸ I2) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)


-- @@ L90-97 verbatim
def A3: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![5, 1, 0, 0, 0, 0], ![0, 5, 5, 0, 0, 0], ![0, 0, 5, 1, 0, 0], ![0, 0, 0, 5, 5, 0], ![0, 0, 0, 0, 5, 1], ![-5, 0, 10, 0, 5, 5]]]
  hmulB := by decide  
  f := ![![![21, -21, 175, 520, 520, 8], ![-52, 65, -520, -1248, -104, 0]], ![![5, -9, 70, 216, 240, 8], ![-12, 26, -208, -520, -104, 0]], ![![6, -17, 102, 344, 360, 8], ![-14, 47, -312, -832, -104, 0]], ![![14, -22, 160, 477, 480, 8], ![-34, 64, -480, -1144, -104, 0]], ![![-3, -6, 10, 40, 37, 0], ![8, 14, -40, -96, 0, 0]], ![![6, -17, 105, 320, 320, 5], ![-14, 47, -320, -768, -64, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-5, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-12, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-8, 0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0, 0], ![-5, 5, 5, 0, 0, 0], ![-4, 0, 5, 1, 0, 0], ![-5, 0, 0, 5, 5, 0], ![-1, 0, 0, 0, 5, 1], ![-10, 0, 10, 0, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L99-100 verbatim
lemma N3 : Nat.card (O ⧸ I3) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)


-- @@ L102-109 verbatim
def A4: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0, 0], ![-5, 1, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![0, 0, 0, 0, 0, 13]], ![![-5, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![0, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hmulB := by decide  
  f := ![![![96, -169, 180, 34, 0, -8], ![247, -390, 78, 104, 104, 0]], ![![66, -93, 100, 36, 0, -8], ![170, -208, 52, 104, 104, 0]], ![![66, -100, 107, 36, 0, -8], ![170, -226, 52, 104, 104, 0]], ![![22, -29, 10, 13, -10, 0], ![57, -64, -38, 26, 0, 0]], ![![12, -7, 10, 2, -3, 0], ![31, -12, 14, 8, 0, 0]], ![![45, -62, 65, 13, 0, -3], ![116, -138, 31, 40, 40, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-8, 13, 0, 0, 0, 0], ![-8, 0, 13, 0, 0, 0], ![-1, 0, 0, 13, 0, 0], ![-1, 0, 0, 0, 13, 0], ![-5, 0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0, 0], ![0, -5, 5, 0, 0, 0], ![3, 0, -5, 1, 0, 0], ![0, 0, 0, -5, 5, 0], ![0, 0, 0, 0, -5, 1], ![-5, 0, 10, 0, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L111-112 verbatim
lemma N4 : Nat.card (O ⧸ I4) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)


-- @@ L114-121 verbatim
def A5: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0, 0], ![0, 29, 0, 0, 0, 0], ![0, 0, 29, 0, 0, 0], ![0, 0, 0, 29, 0, 0], ![0, 0, 0, 0, 29, 0], ![0, 0, 0, 0, 0, 29]], ![![9, 1, 0, 0, 0, 0], ![0, 9, 5, 0, 0, 0], ![0, 0, 9, 1, 0, 0], ![0, 0, 0, 9, 5, 0], ![0, 0, 0, 0, 9, 1], ![-5, 0, 10, 0, 5, 9]]]
  hmulB := by decide  
  f := ![![![181, -1789, -1113, 2679, 3016, 169], ![-580, 5829, 348, -8671, -4901, 0]], ![![45, -553, -346, 932, 1105, 65], ![-144, 1798, 116, -3016, -1885, 0]], ![![26, -440, -273, 699, 858, 52], ![-83, 1427, 87, -2262, -1508, 0]], ![![147, -1479, -921, 2213, 2522, 143], ![-471, 4818, 291, -7163, -4147, 0]], ![![45, -567, -355, 831, 932, 52], ![-144, 1843, 120, -2691, -1508, 0]], ![![30, -384, -240, 554, 624, 35], ![-96, 1248, 80, -1794, -1014, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0], ![-9, 29, 0, 0, 0, 0], ![-7, 0, 29, 0, 0, 0], ![-24, 0, 0, 29, 0, 0], ![-9, 0, 0, 0, 29, 0], ![-6, 0, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0, 0], ![-4, 9, 5, 0, 0, 0], ![-3, 0, 9, 1, 0, 0], ![-9, 0, 0, 9, 5, 0], ![-3, 0, 0, 0, 9, 1], ![-6, 0, 10, 0, 5, 9]]]
  hle1 := by decide   
  hle2 := by decide  


-- @@ L123-124 verbatim
lemma N5 : Nat.card (O ⧸ I5) = 29 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5)


-- @@ L126-130 verbatim
def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L132-146 expanded
def Log00 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 4
  C := ![-5, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log00Mem
  k := 4
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L148-152 verbatim
def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L154-168 expanded
def Log01 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 5
  C := ![-6, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log01Mem
  k := 5
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L170-174 verbatim
def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-2, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L176-190 expanded
def Log02 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 5
  C := ![-2, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log02Mem
  k := 5
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L192-196 verbatim
def Log03Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L198-212 expanded
def Log03 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 4
  C := ![-6, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log03Mem
  k := 4
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L214-218 verbatim
def Log04Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L220-234 expanded
def Log04 : DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 6
  C := ![-7, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log04Mem
  k := 3
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L236-240 verbatim
def Log05Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0], ![4, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![2, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L242-256 expanded
def Log05 :
    DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 2
  C := ![2, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log05Mem
  k := 2
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L258-262 verbatim
def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-6, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L264-278 expanded
def Log10 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 5
  C := ![-6, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log10Mem
  k := 9
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L280-284 verbatim
def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-4, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L286-300 expanded
def Log11 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 3
  C := ![-4, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log11Mem
  k := 4
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L302-306 verbatim
def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-9, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L308-322 expanded
def Log12 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 12
  C := ![-9, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log12Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L324-328 verbatim
def Log13Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-4, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L330-344 expanded
def Log13 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 2
  C := ![-4, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log13Mem
  k := 1
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L346-350 verbatim
def Log14Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L352-366 expanded
def Log14 : DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 12
  C := ![-13, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log14Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L368-372 verbatim
def Log15Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![7, 0, 0, 0, 0, 1]] ![-8, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L374-388 expanded
def Log15 :
    DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 12
  C := ![-8, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log15Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L390-394 verbatim
def Log20Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L396-410 expanded
def Log20 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 5
  C := ![-6, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log20Mem
  k := 9
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L412-416 verbatim
def Log21Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-4, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L418-432 expanded
def Log21 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 3
  C := ![-4, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log21Mem
  k := 4
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L434-438 verbatim
def Log22Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-3, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L440-454 expanded
def Log22 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 6
  C := ![-3, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log22Mem
  k := 5
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L456-460 verbatim
def Log23Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-10, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L462-476 expanded
def Log23 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 8
  C := ![-10, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log23Mem
  k := 3
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L478-482 verbatim
def Log24Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L484-498 expanded
def Log24 : DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 12
  C := ![-13, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log24Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L500-504 verbatim
def Log25Mem : IdealMemCertificate B I2
 ![![13, 0, 0, 0, 0, 0], ![11, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![3, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-3, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L506-520 expanded
def Log25 :
    DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 7
  C := ![-3, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log25Mem
  k := 11
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L522-526 verbatim
def Log30Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L528-542 expanded
def Log30 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 4
  C := ![-5, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log30Mem
  k := 2
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L544-548 verbatim
def Log31Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-7, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L550-564 expanded
def Log31 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 6
  C := ![-7, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log31Mem
  k := 5
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L566-570 verbatim
def Log32Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![0, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L572-586 expanded
def Log32 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 3
  C := ![0, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log32Mem
  k := 4
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L588-592 verbatim
def Log33Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-10, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L594-608 expanded
def Log33 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 8
  C := ![-10, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log33Mem
  k := 3
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L610-614 verbatim
def Log34Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L616-630 expanded
def Log34 : DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 12
  C := ![-13, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log34Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L632-636 verbatim
def Log35Mem : IdealMemCertificate B I3
 ![![13, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![12, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![8, 0, 0, 0, 0, 1]] ![-8, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L638-652 expanded
def Log35 :
    DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 12
  C := ![-8, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log35Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L654-658 verbatim
def Log40Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-5, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L660-674 expanded
def Log40 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 4
  C := ![-5, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log40Mem
  k := 2
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L676-680 verbatim
def Log41Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-7, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![0, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L682-696 expanded
def Log41 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 6
  C := ![-7, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log41Mem
  k := 5
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L698-702 verbatim
def Log42Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-4, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L704-718 expanded
def Log42 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 7
  C := ![-4, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log42Mem
  k := 11
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L720-724 verbatim
def Log43Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-6, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![1, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L726-740 expanded
def Log43 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 4
  C := ![-6, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log43Mem
  k := 2
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L742-746 verbatim
def Log44Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L748-762 expanded
def Log44 : DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 12
  C := ![-13, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log44Mem
  k := 6
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L764-768 verbatim
def Log45Mem : IdealMemCertificate B I4
 ![![13, 0, 0, 0, 0, 0], ![8, 1, 0, 0, 0, 0], ![8, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![5, 0, 0, 0, 0, 1]] ![-6, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![0, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L770-784 expanded
def Log45 :
    DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 10
  C := ![-6, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log45Mem
  k := 10
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L786-790 verbatim
def Log50Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-22, 0, 1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, 1, 0, 0, 0]
 hmem := by decide


-- @@ L792-806 expanded
def Log50 :
    DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 1, 0, 0, 0]
  hxeq := rfl
  m := 21
  C := ![-22, 0, 1, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log50Mem
  k := 17
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L808-812 verbatim
def Log51Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-27, 0, -1, 0, 1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, -1, 0, 1, 0]
 hmem := by decide


-- @@ L814-828 expanded
def Log51 :
    DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, -1, 0, 1, 0]
  hxeq := rfl
  m := 26
  C := ![-27, 0, -1, 0, 1, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log51Mem
  k := 19
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L830-834 verbatim
def Log52Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-6, 2, 0, 0, -2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![0, 2, 0, 0, -2, -1]
 hmem := by decide


-- @@ L836-850 expanded
def Log52 :
    DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![3, 2, 0, 0, -2, -1]
  hxeq := rfl
  m := 9
  C := ![-6, 2, 0, 0, -2, -1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log52Mem
  k := 10
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L852-856 verbatim
def Log53Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-19, -2, -1, 0, 0, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![0, -2, -1, 0, 0, 1]
 hmem := by decide


-- @@ L858-872 expanded
def Log53 :
    DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta4 1
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-2, -2, -1, 0, 0, 1]
  hxeq := rfl
  m := 17
  C := ![-19, -2, -1, 0, 0, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log53Mem
  k := 21
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L874-878 verbatim
def Log54Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-29, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![-1, 0, 0, 0, 0, 0]
 hmem := by decide


-- @@ L880-894 expanded
def Log54 : DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 v 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![-1, 0, 0, 0, 0, 0]
  hxeq := rfl
  m := 28
  C := ![-29, 0, 0, 0, 0, 0]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log54Mem
  k := 14
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L896-900 verbatim
def Log55Mem : IdealMemCertificate B I5
 ![![29, 0, 0, 0, 0, 0], ![9, 1, 0, 0, 0, 0], ![7, 0, 1, 0, 0, 0], ![24, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 1, 0], ![6, 0, 0, 0, 0, 1]] ![-18, -2, 1, -1, -2, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A5
 g := ![1, -2, 1, -1, -2, 1]
 hmem := by decide


-- @@ L902-916 expanded
def Log55 :
    DiscreteLogCertificate N5 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0
    where
  r := 6
  hN := by infer_instance
  hpdvd := by decide
  B := B
  hone := B_one
  xcoord := ![4, -2, 1, -1, -2, 1]
  hxeq := rfl
  m := 22
  C := ![-18, -2, 1, -1, -2, 1]
  hCeq := by rfl
  hmem := mem_of_certificate _ _ _ _ Log55Mem
  k := 26
  hpow := by
    ( try simp only [Int.cast_ofNat]
      erw [← squareAndMultiply_eq_pow]
      repeat (unfold squareAndMultiply_aux; dsimp)
      try decide)
  heql := by decide


-- @@ L918-918 verbatim
end Sat2
