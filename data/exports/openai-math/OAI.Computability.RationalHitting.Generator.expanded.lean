import OAI.Computability.RationalHitting.Certificates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.Generator

-- @@ L6-6 verbatim
open Matrix MvPolynomial

-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
def D (e : ℕ) : ℕ := CyclotomicRing.dimension e * CyclotomicRing.degree e


-- @@ L12-17 verbatim
/-- Entrywise regular representation, flattening and fixed row-major reindexing. -/
def regular (e : ℕ) : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
    (CyclotomicRing.R e) →+* Mat (D e) :=
  (Matrix.reindexRingEquiv ℚ ((Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension e)).symm.toEquiv
    (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv)).toRingHom.comp
    ((Matrix.compRingEquiv _ _ ℚ).toRingHom.comp (CyclotomicRing.rho e).toRingHom.mapMatrix)


-- @@ L19-22 verbatim
/-- The fixed lexicographic three-dimensional integer grid, encoded by Fin H. -/
def grid (H : ℕ) : List (Fin 3 → Fin H) :=
  (List.finRange H).flatMap fun t => (List.finRange H).flatMap fun p =>
    (List.finRange H).map fun r => ![t,p,r]


-- @@ L24-28 verbatim
lemma mem_grid (H : ℕ) (x : Fin 3 → Fin H) : x ∈ grid H := by
  simp only [grid,List.mem_flatMap,List.mem_map]
  refine ⟨x 0,by simp, x 1,by simp,x 2,by simp,?_⟩
  funext i
  fin_cases i <;> rfl


-- @@ L30-31 verbatim
lemma grid_length (H : ℕ) : (grid H).length = H^3 := by
  simp [grid,List.length_flatMap,pow_succ,Nat.mul_assoc]


-- @@ L33-37 verbatim
/-- The polynomial lift is evaluated over the exact rational quotient. -/
def Zring (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) (CyclotomicRing.R e) :=
  (eval₂Hom (RingHom.id _) (fun j => (x j : CyclotomicRing.R e))).mapMatrix
    (PencilCertificates.lifts (CyclotomicRing.character e) N n i)


-- @@ L39-39 verbatim
def Z (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) : Mat (D e) := regular e (Zring n N e x i)


-- @@ L41-42 verbatim
def tupleAt (n N e : ℕ) (x : Fin 3 → ℕ) : Tuple n (D e) :=
  fun i => (Z n N e x 0)⁻¹ * Z n N e x i.succ


-- @@ L44-46 verbatim
/-- The filtering step tests only Z_0, and receives no formula. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (D e)) :=
  if (Z n N e x 0).det = 0 then none else some (tupleAt n N e x)


-- @@ L48-51 verbatim
def output (n N e H : ℕ) : Output n where
  dimension := D e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (grid H).filterMap (fun x => atPoint n N e (fun i => (x i).val+1))


-- @@ L53-54 verbatim
lemma length_output_le (n N e H : ℕ) : (output n N e H).tuples.length ≤ H^3 :=
  (List.length_filterMap_le _ _).trans_eq (grid_length H)


-- @@ L56-76 verbatim
/-- The actual emitted rational normalization is the homomorphic image of the
quotient normalization. Consequently every original inverse occurrence is kept. -/
lemma transfer {n N e : ℕ} (x : Fin 3 → ℕ) (f : Formula n)
    (z : (Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))ˣ)
    (hz : (z : Matrix _ _ _) = Zring n N e x 0)
    (v : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) (CyclotomicRing.R e))
    (hf : f.Eval (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _) * Zring n N e x i.succ) v)
    (hu : IsUnit v) :
    ∃ a, Evaluates f (tupleAt n N e x) a ∧ IsUnit a := by
  have hzinv : regular e (↑z⁻¹ : Matrix _ _ _) = (Z n N e x 0)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    change regular e (↑z⁻¹ : Matrix _ _ _) * regular e (Zring n N e x 0) = 1
    simp only [← map_mul,← hz,Units.inv_mul,map_one]
  refine ⟨regular e v,?_,hu.map (regular e)⟩
  have hh := hf.map (regular e)
  rw [RingHom.ext_rat ((regular e).comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh
  change f.Eval (algebraMap ℚ _) (tupleAt n N e x) (regular e v)
  change f.Eval (algebraMap ℚ _) (fun i => (regular e (Zring n N e x 0))⁻¹ * regular e (Zring n N e x i.succ)) (regular e v)
  simpa only [map_mul,hzinv,Z] using hh


-- @@ L78-85 verbatim
lemma emitted {n N e H : ℕ} (x : Fin 3 → Fin H)
    (hz : IsUnit (Zring n N e (fun i => (x i).val+1) 0)) :
    tupleAt n N e (fun i => (x i).val+1) ∈ (output n N e H).tuples := by
  apply List.mem_filterMap.mpr
  refine ⟨x,mem_grid H x,?_⟩
  have hq := (Matrix.isUnit_iff_isUnit_det _).mp (hz.map (regular e))
  have hne : (Z n N e (fun i => (x i).val+1) 0).det ≠ 0 := hq.ne_zero
  simp [atPoint,hne]


-- @@ L87-87 verbatim
end

-- @@ L88-88 verbatim
end RationalHitting.Generator


-- @@ L90-90 verbatim
namespace RationalHitting.Generator

-- @@ L91-91 verbatim
open Matrix MvPolynomial

-- @@ L92-92 verbatim
open scoped BigOperators

-- @@ L93-93 verbatim
noncomputable section


-- @@ L95-95 verbatim
abbrev WitnessField := HahnSeries QuantumLift.Exponents ℂ

-- @@ L96-98 verbatim
instance witnessCharZero : CharZero WitnessField :=
  CharZero.of_addMonoidHom (HahnSeries.C : ℂ →+* WitnessField).toAddMonoidHom
    (map_one (HahnSeries.C : ℂ →+* WitnessField)) HahnSeries.C_injective


-- @@ L100-101 verbatim
def witnessEmbedding (e : ℕ) : CyclotomicRing.R e →+* WitnessField :=
  (HahnSeries.C : ℂ →+* WitnessField).comp (CyclotomicRing.intoComplex e).toRingHom


-- @@ L103-105 verbatim
def finPencil {n : ℕ} (f : Formula n) :
    Matrix (Fin (Fintype.card f.Index)) (Fin (Fintype.card f.Index)) (Affine.Form n) :=
  (Formula.pencil f).reindex (Fintype.equivFin f.Index) (Fintype.equivFin f.Index)


-- @@ L107-114 verbatim
lemma finPencil_unit {n : ℕ} {R : Type*} [Ring R] (c : ℚ →+* R)
    (X : Fin n → R) (f : Formula n) :
    IsUnit ((finPencil f).map (Affine.eval c X)) ↔ IsUnit (Formula.realized c X f) := by
  let E := Matrix.reindexRingEquiv R (Fintype.equivFin f.Index)
  change IsUnit (E (Formula.realized c X f)) ↔ IsUnit (Formula.realized c X f)
  constructor
  · intro h; simpa using h.map E.symm
  · exact fun h => h.map E


-- @@ L116-116 verbatim
def onePencil (n : ℕ) : Matrix (Fin 1) (Fin 1) (Affine.Form n) := fun _ _ => Affine.constant 1


-- @@ L118-120 verbatim
def conditions {n : ℕ} (N e : ℕ) (f : Formula n) : List (MvPolynomial (Fin 3) (CyclotomicRing.R e)) :=
  PencilCertificates.determinant (CyclotomicRing.character e) N (onePencil n) ::
    f.certificates.map (fun h => PencilCertificates.determinant (CyclotomicRing.character e) N (finPencil h))


-- @@ L122-153 verbatim
lemma condition_nonzero {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s)
    (hnz : Nonzero f)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e) :
    ∀ p ∈ conditions N e f, p ≠ 0 := by
  obtain ⟨d,hd,W,a,ha,ha0⟩ := hnz
  obtain ⟨X,v,hv,hvu⟩ := formula_invertible_witness hd f W a ha ha0
  let C : WitnessField →+* LaurentReduction.F WitnessField := HahnSeries.C
  let Y : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField) := fun i => C.mapMatrix (X i)
  have hv' : Formula.Eval (algebraMap ℚ (Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField)))
      Y f (C.mapMatrix v) := by
    convert hv.map C.mapMatrix using 1
    exact RingHom.ext_rat _ _
  have hcert : ∀ h ∈ f.certificates, IsUnit (Formula.realized (algebraMap ℚ _) Y h) :=
    (Formula.certificates_iff (algebraMap ℚ _) Y f).mpr ⟨_,hv',hvu.map C.mapMatrix⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (onePencil n)
      (2*s+1) 1 (by omega) (by omega) hN hMN hM (by omega) (fun _ => 0)
    have heq : (onePencil n).map (Affine.eval (algebraMap ℚ (Matrix (Fin 1) (Fin 1)
        (LaurentReduction.F WitnessField))) (fun _ => 0)) = 1 := by
      ext i j
      simp [onePencil,Affine.eval_constant,Matrix.one_apply,Subsingleton.elim i j]
    rw [heq]
    exact isUnit_one
  · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
    have hb := (Formula.certificate_bounds f s hs hf).2 h hh
    apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (finPencil h)
      (2*s+1) d hb.1 hb.2 hN hMN hM hd Y
    exact (finPencil_unit _ _ h).mpr (hcert h hh)


-- @@ L155-165 verbatim
lemma condition_degree {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s) :
    (conditions N e f).length ≤ s+2 ∧
    ∀ p ∈ conditions N e f, p.totalDegree ≤ 3*(2*s+1)*(CyclotomicRing.dimension e)^2 := by
  refine ⟨?_,?_⟩
  · have hh := (Formula.certificate_bounds f s hs hf).1
    simpa only [conditions,List.length_cons,List.length_map] using Nat.succ_le_succ hh
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (PencilCertificates.degree_le _ _).trans (by gcongr; omega)
    · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
      exact (PencilCertificates.degree_le _ _).trans (by gcongr; exact (Formula.certificate_bounds f s hs hf).2 h hh |>.2)


-- @@ L167-186 verbatim
lemma integer_grid {K : Type*} [Field K] [CharZero K] (P : List (MvPolynomial (Fin 3) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d H : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (hH : P.length*d < H) :
    ∃ x : Fin 3 → Fin H, ∀ p ∈ P, eval (fun i => (((x i).val+1 : ℕ) : K)) p ≠ 0 := by
  classical
  let S : Finset K := (Finset.range H).image (fun i => ((i+1 : ℕ) : K))
  have hS : S.card = H := by
    rw [Finset.card_image_of_injective,Finset.card_range]
    intro i j h
    have hh : i+1=j+1 := Nat.cast_injective h
    omega
  obtain ⟨x,hx,hxp⟩ := FiniteGrid.simultaneous P hP d hd S (by rwa [hS])
  have hm (i : Fin 3) : ∃ k : Fin H, ((k.val+1 : ℕ) : K) = x i := by
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (hx i)
    exact ⟨⟨k,Finset.mem_range.mp hk⟩,he⟩
  choose y hy using hm
  refine ⟨y,?_⟩
  intro p hp
  have heq : (fun i => (((y i).val+1 : ℕ) : K)) = x := funext hy
  simpa only [heq] using hxp p hp


-- @@ L188-199 verbatim
lemma specialized_unit {K : Type*} [Field K] [CharZero K] {n q M N : ℕ} [NeZero M]
    (χ : AddChar (ZMod M) K) (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K)
    (hx : eval x (PencilCertificates.determinant χ N L) ≠ 0) :
    IsUnit (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
      (eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.lifts χ N n i)))) := by
  have hd : IsUnit ((eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.polynomial χ N L)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.map_det]
    exact hx
  rw [PencilCertificates.specialized] at hd
  simpa using hd.map (Matrix.compRingEquiv (Fin q) (ZMod M) K).symm


-- @@ L201-211 verbatim
lemma onePencil_unit {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Fin (n+1) → Matrix ι ι K)
    (h : IsUnit ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z))) : IsUnit (Z 0) := by
  have hh := h.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K)).toRingHom
  have heq : (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z)) = Z 0 := by
    change Affine.homogeneous (algebraMap ℚ _) Z (Affine.constant 1) = Z 0
    simp [Affine.homogeneous,Affine.coeff,Affine.constant,Fin.sum_univ_succ]
  change IsUnit ((Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) Z))) at hh
  rwa [heq] at hh


-- @@ L213-240 verbatim
/-- The finite formula-independent list hits every admissible nonzero formula
at a defined and invertible original-tree value. -/

theorem output_hits {n s N e H : ℕ} (hs : 1 ≤ s)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e)
    (hH : (s+2)*(3*(2*s+1)*(CyclotomicRing.dimension e)^2) < H) :
    Hits s (output n N e H) := by
  intro f hf _ha hnz
  have hb := condition_degree hs f hf (N := N) (e := e)
  obtain ⟨x,hx⟩ := integer_grid (conditions N e f)
    (condition_nonzero hs f hf hnz hN hMN hM) _ H hb.2 (lt_of_le_of_lt (Nat.mul_le_mul_right _ hb.1) hH)
  let t : Fin 3 → ℕ := fun i => (x i).val+1
  let Zr := Zring n N e t
  have hz : IsUnit (Zr 0) := by
    apply onePencil_unit Zr
    exact specialized_unit _ _ _ (hx _ (List.mem_cons_self ..))
  obtain ⟨z,hz'⟩ := hz
  have hcert : ∀ h ∈ f.certificates,
      IsUnit (Formula.realized (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _)*Zr i.succ) h) := by
    intro h hh
    apply (finPencil_unit _ _ h).mp
    apply Affine.normalized_pencil_unit (finPencil h) Zr z hz'
    apply specialized_unit
    exact hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨h,hh,rfl⟩))
  obtain ⟨v,hv,hu⟩ := (Formula.certificates_iff _ _ f).mp hcert
  obtain ⟨a,ha,hua⟩ := transfer t f z hz' v hv hu
  exact ⟨tupleAt n N e t,emitted x ⟨z,hz'⟩,a,ha,hua⟩


-- @@ L242-242 verbatim
end

-- @@ L243-243 verbatim
end RationalHitting.Generator


-- @@ L245-245 verbatim
namespace RationalHitting.Parameters


-- @@ L247-248 verbatim
/-- The parameters, with M the least power of two strictly above BΔ. -/
def w (n : ℕ) := n+1

-- @@ L249-249 verbatim
def B (s : ℕ) := 2*s+1

-- @@ L250-250 verbatim
def delta (n s : ℕ) := 2*(w n)^3*B s

-- @@ L251-251 verbatim
def exponent (n s : ℕ) := Nat.log 2 (B s * delta n s)

-- @@ L252-252 verbatim
def M (n s : ℕ) := 2^(exponent n s+1)

-- @@ L253-253 verbatim
def N (n s : ℕ) := M n s-delta n s

-- @@ L254-254 verbatim
def H (n s : ℕ) := 1+3*(s+2)*B s*(M n s)^3


-- @@ L256-258 verbatim
theorem threshold_pos (n s : ℕ) : 0 < B s * delta n s := by
  simp only [B,delta,w]
  positivity


-- @@ L260-261 verbatim
theorem threshold_lt (n s : ℕ) : B s * delta n s < M n s :=
  Nat.lt_pow_succ_log_self (by omega) _


-- @@ L263-268 verbatim
theorem M_le (n s : ℕ) : M n s ≤ 2*(B s*delta n s) := by
  unfold M
  rw [pow_succ]
  have h := Nat.pow_log_le_self 2 (threshold_pos n s).ne'
  unfold exponent
  omega


-- @@ L270-272 verbatim
theorem M_minimal (n s k : ℕ) (hk : B s*delta n s < 2^k) : M n s ≤ 2^k := by
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow (threshold_pos n s).ne' hk)


-- @@ L274-279 verbatim
theorem N_pos (n s : ℕ) : 1 ≤ N n s := by
  have hh := threshold_lt n s
  have hb : 1 ≤ B s := by unfold B; omega
  have hd : delta n s ≤ B s*delta n s := by nlinarith
  unfold N
  omega


-- @@ L281-284 verbatim
theorem M_eq (n s : ℕ) : M n s = N n s+delta n s := by
  have hh := N_pos n s
  unfold N at *
  omega


-- @@ L286-290 verbatim
theorem grid_large (n s : ℕ) : (s+2)*(3*B s*(M n s)^2) < H n s := by
  have hp : 1 ≤ M n s := Nat.one_le_iff_ne_zero.mpr (by unfold M; positivity)
  have hpow : (M n s)^2 ≤ (M n s)^3 := Nat.pow_le_pow_right hp (by omega)
  unfold H
  nlinarith [Nat.mul_le_mul_left (3*(s+2)*B s) hpow]


-- @@ L292-292 verbatim
theorem w_bound (n s : ℕ) : w n ≤ n+s+1 := by unfold w; omega


-- @@ L294-294 verbatim
theorem B_bound (n s : ℕ) : B s ≤ 2*(n+s+1) := by unfold B; omega


-- @@ L296-302 verbatim
theorem delta_bound (n s : ℕ) : delta n s ≤ 4*(n+s+1)^4 := by
  calc delta n s ≤ 2*(n+s+1)^3*(2*(n+s+1)) := by
         unfold delta
         gcongr
         · exact w_bound n s
         · exact B_bound n s
       _ = _ := by ring


-- @@ L304-310 verbatim
theorem polynomial_M (n s : ℕ) : M n s ≤ 16*(n+s+1)^5 := by
  calc M n s ≤ 2*(B s*delta n s) := M_le n s
       _ ≤ 2*((2*(n+s+1))*(4*(n+s+1)^4)) := by
          gcongr
          · exact B_bound n s
          · exact delta_bound n s
       _ = _ := by ring


-- @@ L312-323 verbatim
theorem polynomial_H (n s : ℕ) (hn : 1 ≤ n) : H n s ≤ 24577*(n+s+1)^17 := by
  have hp : 1 ≤ (n+s+1)^17 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc H n s ≤ 1+3*(n+s+1)*(2*(n+s+1))*(16*(n+s+1)^5)^3 := by
         unfold H
         apply Nat.add_le_add_left
         apply Nat.mul_le_mul
         · apply Nat.mul_le_mul
           · exact Nat.mul_le_mul_left 3 (by omega)
           · exact B_bound n s
         · exact Nat.pow_le_pow_left (polynomial_M n s) 3
       _ = 1+24576*(n+s+1)^17 := by ring
       _ ≤ _ := by omega


-- @@ L325-325 verbatim
end RationalHitting.Parameters


-- @@ L327-327 verbatim
namespace RationalHitting.Generator

-- @@ L328-328 verbatim
noncomputable section


-- @@ L330-332 verbatim
/-- The list with all parameters fixed by the unary inputs. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.N n s) (Parameters.exponent n s) (Parameters.H n s)


-- @@ L334-339 verbatim
theorem list_hits (n s : ℕ) (hs : 1 ≤ s) : Hits s (list n s) := by
  apply output_hits hs
  · exact Parameters.N_pos n s
  · exact Parameters.M_eq n s
  · exact Parameters.threshold_lt n s
  · exact Parameters.grid_large n s


-- @@ L341-348 verbatim
theorem list_dimension_bound (n s : ℕ) : (list n s).dimension ≤ 256*(n+s+1)^10 := by
  have hd : CyclotomicRing.degree (Parameters.exponent n s) ≤ Parameters.M n s := by
    unfold CyclotomicRing.degree Parameters.M
    exact Nat.pow_le_pow_right (by omega) (by omega)
  change Parameters.M n s * CyclotomicRing.degree (Parameters.exponent n s) ≤ _
  calc _ ≤ (16*(n+s+1)^5)*(16*(n+s+1)^5) :=
             Nat.mul_le_mul (Parameters.polynomial_M n s) (hd.trans (Parameters.polynomial_M n s))
       _ = _ := by ring


-- @@ L350-354 verbatim
theorem list_length_bound (n s : ℕ) (hn : 1 ≤ n) :
    (list n s).tuples.length ≤ 24577^3*(n+s+1)^51 := by
  calc _ ≤ (Parameters.H n s)^3 := length_output_le ..
       _ ≤ (24577*(n+s+1)^17)^3 := Nat.pow_le_pow_left (Parameters.polynomial_H n s hn) 3
       _ = _ := by rw [mul_pow,← pow_mul]


-- @@ L356-362 verbatim
/-- The algebraic hitting property and the polynomial list-cardinality bound. -/

theorem algebraic_generator : ∃ G : (n s : ℕ) → Output n,
    ∀ n s, 1 ≤ n → 1 ≤ s →
      (G n s).dimension ≤ 256*(n+s+1)^10 ∧
      (G n s).tuples.length ≤ 24577^3*(n+s+1)^51 ∧ Hits s (G n s) := by
  exact ⟨list,fun n s hn hs => ⟨list_dimension_bound n s,list_length_bound n s hn,list_hits n s hs⟩⟩


-- @@ L364-364 verbatim
end

-- @@ L365-365 verbatim
end RationalHitting.Generator


-- @@ L367-367 verbatim
end OAI
