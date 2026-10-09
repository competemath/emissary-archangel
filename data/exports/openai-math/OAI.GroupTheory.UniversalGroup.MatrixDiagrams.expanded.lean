import OAI.GroupTheory.UniversalGroup.FiniteEnvelopes


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Metric Topology BigOperators

-- @@ L6-6 verbatim
open Set Metric Topology

-- @@ L7-7 verbatim
open Set Topology

-- @@ L8-8 verbatim
open Set Metric Topology

-- @@ L9-9 verbatim
open scoped NNReal

-- @@ L10-10 verbatim
open Set Metric Topology

-- @@ L11-11 verbatim
open scoped NNReal ENNReal

-- @@ L12-12 verbatim
open Set Metric Topology

-- @@ L13-13 verbatim
open scoped TensorProduct


-- @@ L15-15 verbatim
namespace UniversalFInfinity

-- @@ L16-16 verbatim
namespace MatrixDiagram


-- @@ L18-18 verbatim
open Matrix


-- @@ L20-20 verbatim
variable {K T : Type*} [CommRing K] [AddCommGroup T]


-- @@ L22-24 verbatim
def OrthogonallyAdditive (z : Matrix (Fin 3) (Fin 3) K → T) : Prop :=
  ∀ E P, IsIdempotentElem E → IsIdempotentElem P → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P


-- @@ L26-29 verbatim
lemma rank_one_idempotent (u l : Fin 3 → K) (h : l ⬝ᵥ u = 1) :
    IsIdempotentElem (vecMulVec u l) := by
  change vecMulVec u l * vecMulVec u l = vecMulVec u l
  rw [vecMulVec_mul_vecMulVec, h, one_smul]


-- @@ L31-33 verbatim
lemma rank_one_mul_zero (u l v m : Fin 3 → K) (h : l ⬝ᵥ v = 0) :
    vecMulVec u l * vecMulVec v m = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]


-- @@ L35-59 verbatim
lemma rank_one_difference (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (u l v m : Fin 3 → K)
    (hlu : l ⬝ᵥ u = 1) (hlv : l ⬝ᵥ v = 0)
    (hmu : m ⬝ᵥ u = 0) (hmv : m ⬝ᵥ v = 1) :
    z (vecMulVec (u + v) l) - z (vecMulVec u l) =
      z (vecMulVec v m) - z (vecMulVec v (m - l)) := by
  have hmlv : (m - l) ⬝ᵥ v = 1 := by simp [sub_dotProduct, hmv, hlv]
  have hluv : l ⬝ᵥ (u + v) = 1 := by simp [dotProduct_add, hlu, hlv]
  have hmluv : (m - l) ⬝ᵥ (u + v) = 0 := by
    simp [sub_dotProduct, dotProduct_add, hmu, hmv, hlu, hlv]
  have h₁ := hz (vecMulVec u l) (vecMulVec v m)
    (rank_one_idempotent u l hlu) (rank_one_idempotent v m hmv)
    (rank_one_mul_zero u l v m hlv) (rank_one_mul_zero v m u l hmu)
  have h₂ := hz (vecMulVec (u + v) l) (vecMulVec v (m - l))
    (rank_one_idempotent (u + v) l hluv) (rank_one_idempotent v (m - l) hmlv)
    (rank_one_mul_zero (u + v) l v (m - l) hlv)
    (rank_one_mul_zero v (m - l) (u + v) l hmluv)
  have heq : vecMulVec u l + vecMulVec v m =
      vecMulVec (u + v) l + vecMulVec v (m - l) := by
    ext i j
    simp only [Matrix.add_apply, vecMulVec_apply, Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq, h₂] at h₁
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact h₁.trans (add_comm _ _)


-- @@ L61-61 verbatim
def row (s : K) : Fin 3 → K := ![1, s, 0]

-- @@ L62-62 verbatim
def along (s t : K) : Fin 3 → K := ![1 - s * t, t, 0]

-- @@ L63-63 verbatim
def direction (s : K) : Fin 3 → K := ![-s, 1, 0]

-- @@ L64-64 verbatim
def anchor : Fin 3 → K := ![1, 0, 1]

-- @@ L65-65 verbatim
def witness (s t : K) : Fin 3 → K := ![-t, 1 - s * t, t]


-- @@ L67-73 verbatim
lemma frame_identities (s t : K) :
    row s ⬝ᵥ along s t = 1 ∧ row s ⬝ᵥ direction s = 0 ∧
    witness s t ⬝ᵥ along s t = 0 ∧ witness s t ⬝ᵥ direction s = 1 ∧
    row s ⬝ᵥ (anchor : Fin 3 → K) = 1 ∧
    witness s t ⬝ᵥ (anchor : Fin 3 → K) = 0 := by
  simp [row, along, witness, direction, anchor, dotProduct, Fin.sum_univ_three]
  constructor <;> ring


-- @@ L75-78 verbatim
lemma along_step (s t : K) : along s t + direction s = along s (t + 1) := by
  ext i
  fin_cases i <;> simp [along, direction]
  ring


-- @@ L80-92 verbatim
lemma increment_independent (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (s t : K) :
    z (vecMulVec (along s (t + 1)) (row s)) - z (vecMulVec (along s t) (row s)) =
      z (vecMulVec (along s 1) (row s)) - z (vecMulVec (along s 0) (row s)) := by
  have hd (r : K) :
      z (vecMulVec (along s (r + 1)) (row s)) - z (vecMulVec (along s r) (row s)) =
        z (vecMulVec ((anchor : Fin 3 → K) + direction s) (row s)) -
          z (vecMulVec (anchor : Fin 3 → K) (row s)) := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := frame_identities s r
    rw [← along_step]
    exact (rank_one_difference z hz _ _ _ _ h₁ h₂ h₃ h₄).trans
      (rank_one_difference z hz _ _ _ _ h₅ h₂ h₆ h₄).symm
  exact (hd t).trans (by simpa using (hd 0).symm)


-- @@ L94-116 verbatim
theorem prime_multiple_step (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] (s : K) :
    p • z (vecMulVec (along s 1) (row s)) =
      p • z (vecMulVec (along s 0) (row s)) := by
  let F (n : ℕ) := z (vecMulVec (along s (n : K)) (row s))
  let d := F 1 - F 0
  have hstep (n : ℕ) : F (n + 1) - F n = d := by
    simpa only [F, d, Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      increment_independent z hz s (n : K)
  have hF (n : ℕ) : F n = F 0 + n • d := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      rw [ih, succ_nsmul] at *
      exact (sub_eq_iff_eq_add.mp h).trans (by abel)
  have hp : F p = F 0 := by simp only [F, CharP.cast_eq_zero, Nat.cast_zero]
  have hpd : p • d = 0 := by
    have h := (hF p).symm.trans hp
    simpa only [add_eq_left] using h
  have h := sub_eq_zero.mp (show p • F 1 - p • F 0 = 0 by
    simpa only [d, nsmul_sub] using hpd)
  simpa only [F, Nat.cast_one, Nat.cast_zero] using h


-- @@ L118-129 verbatim
lemma OrthogonallyAdditive.transpose {z : Matrix (Fin 3) (Fin 3) K → T}
    (hz : OrthogonallyAdditive z) : OrthogonallyAdditive (fun E => z E.transpose) := by
  intro E P hE hP hEP hPE
  have hEt : IsIdempotentElem E.transpose := by
    change E.transpose * E.transpose = E.transpose
    rw [← transpose_mul, hE]
  have hPt : IsIdempotentElem P.transpose := by
    change P.transpose * P.transpose = P.transpose
    rw [← transpose_mul, hP]
  have hEPt : E.transpose * P.transpose = 0 := by rw [← transpose_mul, hPE, transpose_zero]
  have hPEt : P.transpose * E.transpose = 0 := by rw [← transpose_mul, hEP, transpose_zero]
  simpa only [transpose_add] using hz _ _ hEt hPt hEPt hPEt


-- @@ L131-143 verbatim
lemma OrthogonallyAdditive.comp {z : Matrix (Fin 3) (Fin 3) K → T}
    (hz : OrthogonallyAdditive z) (f : Matrix (Fin 3) (Fin 3) K →+* Matrix (Fin 3) (Fin 3) K) :
    OrthogonallyAdditive (fun E => z (f E)) := by
  intro E P hE hP hEP hPE
  have hEt : IsIdempotentElem (f E) := by
    change f E * f E = f E
    rw [← map_mul, hE]
  have hPt : IsIdempotentElem (f P) := by
    change f P * f P = f P
    rw [← map_mul, hP]
  have hEPt : f E * f P = 0 := by rw [← map_mul, hEP, map_zero]
  have hPEt : f P * f E = 0 := by rw [← map_mul, hPE, map_zero]
  simpa only [map_add] using hz _ _ hEt hPt hEPt hPEt


-- @@ L145-145 verbatim
def basisVector (i : Fin 3) : Fin 3 → K := Pi.single i 1


-- @@ L147-148 verbatim
def diagonalUnit (i : Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  vecMulVec (basisVector i) (basisVector i)


-- @@ L150-180 verbatim
theorem diagonal_zero_one (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] :
    p • z (diagonalUnit 0) = p • z (diagonalUnit 1) := by
  have hleft := prime_multiple_step (fun E => z E.transpose) hz.transpose p 0
  have hmid := prime_multiple_step z hz p 1
  let q := (Matrix.reindexRingEquiv K (Equiv.swap (0 : Fin 3) 1)).toRingHom
  have hright := prime_multiple_step (fun E => z (q E).transpose)
    (hz.transpose.comp q) p 0
  have e0 : along (0 : K) 0 = basisVector 0 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have r0 : row (0 : K) = basisVector 0 := by
    ext i; fin_cases i <;> simp [row, basisVector]
  have e1 : along (1 : K) 1 = basisVector 1 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have m0 : along (1 : K) 0 = basisVector 0 := by
    ext i; fin_cases i <;> simp [along, basisVector]
  have r1 : along (0 : K) 1 = row (1 : K) := by
    ext i; fin_cases i <;> simp [along, row]
  have q0 : q (vecMulVec (along 0 0) (row 0)) = diagonalUnit 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [q, Matrix.reindex, Matrix.submatrix, along, row,
        diagonalUnit, basisVector, Pi.single_apply, vecMulVec, Equiv.swap_apply_def]
  have q1 : (q (vecMulVec (along 0 1) (row 0))).transpose =
      vecMulVec (basisVector 1) (row 1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [q, Matrix.reindex, Matrix.submatrix, along, row,
        basisVector, Pi.single_apply, vecMulVec, Equiv.swap_apply_def]
  rw [transpose_vecMulVec, transpose_vecMulVec, e0, r0, r1] at hleft
  rw [e1, m0] at hmid
  rw [q0, q1, diagonalUnit, transpose_vecMulVec] at hright
  exact hleft.symm.trans (hmid.symm.trans hright)


-- @@ L182-192 verbatim
lemma reindex_diagonalUnit (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    reindexRingEquiv K e (diagonalUnit i) = diagonalUnit (e i) := by
  have hb (x : Fin 3) : basisVector i (e.symm x) = (basisVector (e i) x : K) := by
    by_cases hx : x = e i
    · subst x; simp [basisVector]
    · have hx' : e.symm x ≠ i := fun h => hx (by simpa using congrArg e h)
      simp [basisVector, hx, hx']
  ext x y
  change basisVector i (e.symm x) * basisVector i (e.symm y) =
    (basisVector (e i) x : K) * basisVector (e i) y
  rw [hb, hb]


-- @@ L194-212 verbatim
theorem diagonal_equality (z : Matrix (Fin 3) (Fin 3) K → T)
    (hz : OrthogonallyAdditive z) (p : ℕ) [CharP K p] (i j : Fin 3) :
    p • z (diagonalUnit i) = p • z (diagonalUnit j) := by
  have h01 := diagonal_zero_one z hz p
  let e := Equiv.swap (1 : Fin 3) 2
  let q := (reindexRingEquiv K e).toRingHom
  have h02 := diagonal_zero_one (fun E => z (q E)) (hz.comp q) p
  have hq (i : Fin 3) : q (diagonalUnit i) = diagonalUnit (e i) :=
    reindex_diagonalUnit e i
  simp only [hq] at h02
  have he0 : e 0 = 0 := by decide
  have he1 : e 1 = 2 := by decide
  rw [he0, he1] at h02
  have h0 (i : Fin 3) : p • z (diagonalUnit 0) = p • z (diagonalUnit i) := by
    fin_cases i
    · rfl
    · exact h01
    · exact h02
  exact (h0 i).symm.trans (h0 j)


-- @@ L214-217 verbatim
lemma diagonalUnit_idempotent (i : Fin 3) :
    IsIdempotentElem (diagonalUnit i : Matrix (Fin 3) (Fin 3) K) := by
  apply rank_one_idempotent
  simp [basisVector, dotProduct, Pi.single_apply]


-- @@ L219-222 verbatim
lemma diagonalUnit_orthogonal {i j : Fin 3} (hij : i ≠ j) :
    (diagonalUnit i : Matrix (Fin 3) (Fin 3) K) * diagonalUnit j = 0 := by
  apply rank_one_mul_zero
  simp [basisVector, dotProduct, Pi.single_apply, Ne.symm hij]


-- @@ L224-227 verbatim
lemma diagonalUnit_sum :
    (diagonalUnit 0 : Matrix (Fin 3) (Fin 3) K) + diagonalUnit 1 + diagonalUnit 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalUnit, basisVector, vecMulVec]


-- @@ L229-229 verbatim
end MatrixDiagram


-- @@ L231-231 verbatim
namespace PrefixAlgebra


-- @@ L233-233 verbatim
variable (K : Type*) [CommRing K]


-- @@ L235-235 verbatim
abbrev Sequences := Stream' Bool

-- @@ L236-236 verbatim
abbrev Space := Sequences →₀ K

-- @@ L237-237 verbatim
abbrev Operators := Module.End K (Space K)


-- @@ L239-240 verbatim
noncomputable def prefixOp (i : Bool) : Operators K :=
  Finsupp.linearCombination K (fun s => Finsupp.single (Stream'.cons i s) 1)


-- @@ L242-243 verbatim
noncomputable def delete (i : Bool) : Operators K :=
  Finsupp.linearCombination K (fun s => if s.head = i then Finsupp.single s.tail 1 else 0)


-- @@ L245-247 verbatim
@[simp] lemma prefix_single (i : Bool) (s : Sequences) (a : K) :
    prefixOp K i (Finsupp.single s a) = Finsupp.single (Stream'.cons i s) a := by
  simp [prefixOp]


-- @@ L249-251 verbatim
@[simp] lemma delete_single (i : Bool) (s : Sequences) (a : K) :
    delete K i (Finsupp.single s a) = if s.head = i then Finsupp.single s.tail a else 0 := by
  by_cases h : s.head = i <;> simp [delete, h]


-- @@ L253-261 verbatim
lemma delete_prefix (i j : Bool) :
    delete K i * prefixOp K j = if i = j then 1 else 0 := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [Module.End.mul_apply, prefix_single, delete_single,
    Stream'.head_cons, Stream'.tail_cons]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]


-- @@ L263-268 verbatim
lemma prefix_partition : prefixOp K false * delete K false + prefixOp K true * delete K true = 1 := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.add_apply, Module.End.mul_apply, delete_single]
  cases h : s.head <;> simp
  all_goals rw [← h, Stream'.cons_head_tail]


-- @@ L270-271 verbatim
noncomputable def algebra : Subalgebra K (Operators K) :=
  Algebra.adjoin K {prefixOp K false, prefixOp K true, delete K false, delete K true}


-- @@ L273-274 verbatim
noncomputable def left (i : Bool) : algebra K :=
  ⟨prefixOp K i, by apply Algebra.subset_adjoin; cases i <;> simp⟩

-- @@ L275-276 verbatim
noncomputable def right (i : Bool) : algebra K :=
  ⟨delete K i, by apply Algebra.subset_adjoin; cases i <;> simp⟩


-- @@ L278-281 verbatim
lemma right_left (i j : Bool) : right K i * left K j = if i = j then 1 else 0 := by
  apply Subtype.ext
  simpa only [Subalgebra.coe_mul, left, right, Subalgebra.coe_one, Subalgebra.coe_zero,
    apply_ite] using delete_prefix K i j


-- @@ L283-285 verbatim
lemma partition : left K false * right K false + left K true * right K true = 1 := by
  apply Subtype.ext
  exact prefix_partition K


-- @@ L287-289 verbatim
noncomputable def leftWord : List Bool → algebra K
  | [] => 1
  | b :: w => left K b * leftWord w


-- @@ L291-293 verbatim
noncomputable def rightWord : List Bool → algebra K
  | [] => 1
  | b :: w => rightWord w * right K b


-- @@ L295-295 verbatim
@[simp] lemma leftWord_nil : leftWord K [] = 1 := rfl

-- @@ L296-296 verbatim
@[simp] lemma rightWord_nil : rightWord K [] = 1 := rfl


-- @@ L298-303 verbatim
lemma cancel_initial (b c : Bool) (v w : List Bool) :
    rightWord K (b :: v) * leftWord K (c :: w) =
      if b = c then rightWord K v * leftWord K w else 0 := by
  simp only [rightWord, leftWord]
  rw [mul_assoc, ← mul_assoc (right K b), right_left]
  by_cases h : b = c <;> simp [h]


-- @@ L305-308 verbatim
@[simp] lemma word_cancel (w : List Bool) : rightWord K w * leftWord K w = 1 := by
  induction w with
  | nil => simp
  | cons b w ih => rw [cancel_initial, ite_eq_left rfl, ih]


-- @@ L310-313 verbatim
def words : Fin 3 → Fin 3 → List Bool :=
  ![![[false,false], [false,true], [true]],
    ![[false,false,false], [false,true], [true]],
    ![[false,false,true], [false,true], [true]]]


-- @@ L315-318 verbatim
lemma word_orthogonality (a i j : Fin 3) :
    rightWord K (words a i) * leftWord K (words a j) = if i = j then 1 else 0 := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [words, cancel_initial]


-- @@ L320-320 verbatim
noncomputable def projection (w : List Bool) : algebra K := leftWord K w * rightWord K w


-- @@ L322-325 verbatim
lemma projection_idempotent (w : List Bool) : IsIdempotentElem (projection K w) := by
  change (leftWord K w * rightWord K w) * (leftWord K w * rightWord K w) = _
  rw [mul_assoc, ← mul_assoc (rightWord K w), word_cancel, one_mul]
  rfl


-- @@ L327-341 verbatim
lemma projection_split (w : List Bool) :
    projection K w = projection K (w ++ [false]) + projection K (w ++ [true]) := by
  have hl (w v : List Bool) : leftWord K (w ++ v) = leftWord K w * leftWord K v := by
    induction w with
    | nil => simp [leftWord]
    | cons b w ih => simp only [List.cons_append, leftWord, ih, mul_assoc]
  have hr (w v : List Bool) : rightWord K (w ++ v) = rightWord K v * rightWord K w := by
    induction w with
    | nil => simp [rightWord]
    | cons b w ih => simp only [List.cons_append, rightWord, ih, mul_assoc]
  simp only [projection, hl, hr, leftWord, rightWord, mul_one, one_mul]
  calc
    _ = leftWord K w * (left K false * right K false + left K true * right K true) * rightWord K w := by
      rw [partition, mul_one]
    _ = _ := by noncomm_ring


-- @@ L343-343 verbatim
end PrefixAlgebra


-- @@ L345-345 verbatim
namespace MatrixCorners


-- @@ L347-347 verbatim
variable {K D : Type*} [CommRing K] [Ring D] [Algebra K D]

-- @@ L348-348 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L349-349 verbatim
variable (L R : ι → D) (h : ∀ i j, R i * L j = if i = j then 1 else 0)


-- @@ L351-351 verbatim
abbrev unit (i j : ι) : D := L i * R j


-- @@ L353-353 verbatim
include h


-- @@ L355-360 verbatim
omit [Fintype ι] in
lemma unit_mul (i j k m : ι) :
    unit L R i j * unit L R k m = if j = k then unit L R i m else 0 := by
  dsimp only [unit]
  rw [mul_assoc, ← mul_assoc (R j), h]
  split_ifs <;> simp


-- @@ L362-367 verbatim
omit [Fintype ι] in
lemma weighted_unit_mul (a b : K) (i j k m : ι) :
    (a • unit L R i j) * (b • unit L R k m) =
      if j = k then (a * b) • unit L R i m else 0 := by
  rw [smul_mul_smul, unit_mul L R h]
  split_ifs <;> simp


-- @@ L369-370 verbatim
noncomputable def matrixMap (A : Matrix ι ι K) : D :=
  ∑ i, ∑ j, (A i j) • unit L R i j


-- @@ L372-389 verbatim
lemma matrixMap_mul (A B : Matrix ι ι K) :
    matrixMap L R (A * B) = matrixMap L R A * matrixMap L R B := by
  classical
  have hr : matrixMap L R A * matrixMap L R B =
      ∑ i, ∑ j, ∑ m, (A i j * B j m) • unit L R i m := by
    simp only [matrixMap, Finset.sum_mul, Finset.mul_sum, weighted_unit_mul L R h]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ j, ∑ i, ∑ m, (A i j * B j m) • unit L R i m := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hr]
  simp only [matrixMap, Matrix.mul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm


-- @@ L391-396 verbatim
noncomputable def hom : Matrix ι ι K →ₙₐ[K] D where
  toFun := matrixMap L R
  map_zero' := by simp [matrixMap]
  map_add' A B := by simp [matrixMap, add_smul, Finset.sum_add_distrib]
  map_mul' := matrixMap_mul L R h
  map_smul' a A := by simp [matrixMap, Finset.smul_sum, smul_smul]


-- @@ L398-401 verbatim
lemma map_diagonal (i : ι) :
    hom L R h (Matrix.diagonal (Pi.single i (1 : K))) = L i * R i := by
  change matrixMap L R _ = _
  simp [matrixMap, Matrix.diagonal, Pi.single_apply, unit]


-- @@ L403-405 verbatim
lemma map_one : hom L R h (1 : Matrix ι ι K) = ∑ i, L i * R i := by
  change matrixMap L R _ = _
  simp [matrixMap, Matrix.one_apply, unit]


-- @@ L407-421 verbatim
lemma extract (A : Matrix ι ι K) (i j : ι) :
    R i * hom L R h A * L j = algebraMap K D (A i j) := by
  change R i * matrixMap L R A * L j = _
  have hextract (a : K) (k l : ι) :
      R i * (a • unit L R k l) * L j =
        if i = k then if l = j then algebraMap K D a else 0 else 0 := by
    rw [mul_smul_comm, smul_mul_assoc]
    dsimp only [unit]
    rw [← mul_assoc (R i), h]
    by_cases hik : i = k
    · rw [ite_eq_left hik, one_mul, h]
      by_cases hlj : l = j <;> simp [hlj, hik, Algebra.smul_def]
    · simp [hik]
  simp only [matrixMap, Finset.mul_sum, Finset.sum_mul, hextract]
  simp


-- @@ L423-423 verbatim
end MatrixCorners

-- @@ L424-424 verbatim
end UniversalFInfinity


-- @@ L426-426 verbatim
end OAI
