import OAI.RepresentationTheory.Saxl.BandMatrices


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped TensorProduct


-- @@ L9-9 verbatim
namespace Saxl.Path

-- @@ L10-10 verbatim
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

-- @@ L11-11 verbatim
abbrev Letter := Fin 4


-- @@ L13-13 verbatim
def parts (x : Letter) : Fin 2 × Fin 2 := finProdFinEquiv.symm x

-- @@ L14-14 verbatim
def J : Mat := !![0, 1; -1, 0]


-- @@ L16-16 verbatim
def leftPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val, by omega⟩

-- @@ L17-17 verbatim
def midPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 1, by omega⟩

-- @@ L18-21 verbatim
def rightPos {r : ℕ} (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 2, by omega⟩

/- EXACT coefficients of the path-ordered alternating band: the two endpoint
singletons carry letter 0, and row/column pairs have coefficients J. Here r=m-1. -/

-- @@ L22-28 verbatim
def bandWord (r : ℕ) (w : Fin (2 * r + 1) → Letter) : ℂ :=
  (if (parts (w 0)).1 = 0 then 1 else 0) *
  (if (parts (w (Fin.last (2 * r)))).2 = 0 then 1 else 0) *
  ∏ i : Fin r, J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
    J (parts (w (midPos i))).1 (parts (w (rightPos i))).1

/- Ordinary pure position tensor pairing, with no conjugation. -/

-- @@ L29-30 verbatim
def pureWord {n : ℕ} (X : Fin n → Mat) (w : Fin n → Letter) : ℂ :=
  ∏ i, X i (parts (w i)).1 (parts (w i)).2


-- @@ L32-32 verbatim
def entry (a : Letter) : Mat := Matrix.single (parts a).1 (parts a).2 1


-- @@ L34-45 verbatim
def DL (q : ℕ) : Mat →ₗ[ℂ] Mat where
  toFun := Band.D q
  map_add' X Y := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two, add_comm]
    · simp [Band.D, h]
  map_smul' c X := by
    by_cases h : q % 2 = 0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Band.D, h, Matrix.adjugate_fin_two]
    · simp [Band.D, h]


-- @@ L47-48 verbatim
def chainML (n p : ℕ) : MultilinearMap ℂ (fun _ : Fin n => Mat) Mat :=
  (MultilinearMap.mkPiAlgebraFin ℂ n Mat).compLinearMap (fun i => DL (p + i.val))


-- @@ L50-51 verbatim
lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl


-- @@ L53-57 verbatim
lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]


-- @@ L59-71 verbatim
lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl


-- @@ L73-76 verbatim
lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]


-- @@ L78-79 verbatim
lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]


-- @@ L81-96 verbatim
lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]


-- @@ L98-106 verbatim
lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl


-- @@ L108-131 verbatim
lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring


-- @@ L133-139 verbatim
lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]


-- @@ L141-159 verbatim
theorem path_contraction (r : ℕ) (X : Fin (2*r+1) → Mat) :
    dotProduct (bandWord r) (pureWord X) =
      (-1 : ℂ)^r * (List.ofFn fun q => Band.D (1+q.val) (X q)).prod 0 0 := by
  have h := congrArg (fun A : Mat => A 0 0) (chain_expand (2*r+1) 1 X)
  change chainML (2*r+1) 1 X 0 0 =
    (∑ w : Fin (2*r+1) → Letter,
      pureWord X w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 at h
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    chain_entries_endpoint] at h
  rw [← chainML_apply, h, Finset.mul_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro w hw
  have hs : (-1 : ℂ)^r * (-1 : ℂ)^r = 1 := by
    rw [← mul_pow]; norm_num
  calc
    bandWord r w * pureWord X w =
        ((-1 : ℂ)^r * (-1 : ℂ)^r) * (bandWord r w * pureWord X w) := by rw [hs, one_mul]
    _ = _ := by ring


-- @@ L161-162 verbatim
lemma J_real (i j : Fin 2) : star (J i j) = J i j := by
  fin_cases i <;> fin_cases j <;> simp [J]


-- @@ L164-169 verbatim
lemma bandWord_real (r : ℕ) : star (bandWord r) = bandWord r := by
  funext w
  change star (bandWord r w) = bandWord r w
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, h₁, h₂, star_mul, star_prod, J_real, mul_comm]

-- @@ L170-170 verbatim
end Saxl.Path


-- @@ L172-172 verbatim
end


-- @@ L174-174 verbatim
end OAI
