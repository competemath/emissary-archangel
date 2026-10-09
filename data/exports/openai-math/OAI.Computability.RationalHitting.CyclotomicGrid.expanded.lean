import OAI.Computability.RationalHitting.Deformation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.CyclotomicRing

-- @@ L6-6 verbatim
open Polynomial Matrix Module

-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
def modulus (e : ℕ) : ℚ[X] := X^(2^e)+1


-- @@ L11-11 verbatim
def degree (e : ℕ) : ℕ := 2^e


-- @@ L13-13 verbatim
def dimension (e : ℕ) : ℕ := 2^(e+1)


-- @@ L15-17 verbatim
lemma modulus_eq_cyclotomic (e : ℕ) : modulus e = cyclotomic (dimension e) ℚ := by
  rw [dimension,cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [modulus,Finset.sum_range_succ,add_comm]


-- @@ L19-20 verbatim
instance modulus_irreducible (e : ℕ) : Fact (Irreducible (modulus e)) :=
  ⟨by rw [modulus_eq_cyclotomic]; exact cyclotomic.irreducible_rat (by unfold dimension; positivity)⟩


-- @@ L22-22 verbatim
abbrev R (e : ℕ) := AdjoinRoot (modulus e)


-- @@ L24-24 verbatim
lemma degree_pos (e : ℕ) : 0 < degree e := by unfold degree; positivity

-- @@ L25-25 verbatim
lemma dimension_pos (e : ℕ) : 0 < dimension e := by unfold dimension; positivity


-- @@ L27-28 verbatim
lemma modulus_monic (e : ℕ) : (modulus e).Monic := by
  simpa [modulus] using monic_X_pow_add_C (1 : ℚ) (pow_ne_zero e (by norm_num : (2 : ℕ) ≠ 0))


-- @@ L30-31 verbatim
lemma modulus_natDegree (e : ℕ) : (modulus e).natDegree = degree e := by
  simp [modulus,degree]


-- @@ L33-33 verbatim
def powerBasis (e : ℕ) : PowerBasis ℚ (R e) := AdjoinRoot.powerBasis' (modulus_monic e)


-- @@ L35-36 verbatim
def basis (e : ℕ) : Basis (Fin (degree e)) ℚ (R e) :=
  (powerBasis e).basis.reindex (finCongr (modulus_natDegree e))


-- @@ L38-41 verbatim
lemma basis_apply (e : ℕ) (i : Fin (degree e)) :
    basis e i = AdjoinRoot.root (modulus e)^i.val := by
  rw [basis,Basis.reindex_apply]
  exact (powerBasis e).basis_eq_pow _


-- @@ L43-43 verbatim
instance dimension_neZero (e : ℕ) : NeZero (dimension e) := ⟨(dimension_pos e).ne'⟩


-- @@ L45-47 verbatim
instance charZero (e : ℕ) : CharZero (R e) :=
  CharZero.of_addMonoidHom (algebraMap ℚ (R e)).toAddMonoidHom
    (map_one (algebraMap ℚ (R e))) (algebraMap ℚ (R e)).injective


-- @@ L49-50 verbatim
instance finite (e : ℕ) : Module.Finite ℚ (R e) :=
  (modulus_monic e).finite_adjoinRoot


-- @@ L52-52 verbatim
def intoComplex (e : ℕ) : R e →ₐ[ℚ] ℂ := IsAlgClosed.lift


-- @@ L54-62 verbatim
/-- The cyclotomic quotient is a field for the chosen powers of two.
Irreducibility allows regular-representation invertibility to be proved
at a single primitive root. -/
lemma root_primitive (e : ℕ) : IsPrimitiveRoot (AdjoinRoot.root (modulus e)) (dimension e) := by
  apply (Polynomial.isRoot_cyclotomic_iff).mp
  have hh := AdjoinRoot.isRoot_root (modulus e)
  rw [← Polynomial.map_cyclotomic (dimension e) (algebraMap ℚ (R e)),
    ← modulus_eq_cyclotomic e]
  exact hh


-- @@ L64-65 verbatim
def character (e : ℕ) : AddChar (ZMod (dimension e)) (R e) :=
  AddChar.zmodChar (dimension e) (root_primitive e).pow_eq_one


-- @@ L67-68 verbatim
lemma character_primitive (e : ℕ) : (character e).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root _ (root_primitive e)


-- @@ L70-71 verbatim
def rho (e : ℕ) : R e →ₐ[ℚ] Matrix (Fin (degree e)) (Fin (degree e)) ℚ :=
  Algebra.leftMulMatrix (basis e)


-- @@ L73-76 verbatim
lemma rho_root_apply (e : ℕ) (i j : Fin (degree e)) :
    rho e (AdjoinRoot.root (modulus e)) i j =
      (basis e).repr (AdjoinRoot.root (modulus e)^(j.val+1)) i := by
  rw [rho,Algebra.leftMulMatrix_eq_repr_mul,basis_apply,pow_succ']


-- @@ L78-78 verbatim
end

-- @@ L79-79 verbatim
end RationalHitting.CyclotomicRing



-- @@ L82-82 verbatim
namespace RationalHitting.FiniteGrid

-- @@ L83-83 verbatim
open MvPolynomial Matrix

-- @@ L84-84 verbatim
open scoped BigOperators

-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
variable {K : Type*} [Field K] {k : ℕ}


-- @@ L89-109 verbatim
/-- The fixed grid, independent of the coefficients, finds a nonzero value. -/
theorem exists_eval_ne_zero (p : MvPolynomial (Fin k) K) (hp : p ≠ 0)
    (S : Finset K) (hS : p.totalDegree < S.card) :
    ∃ x : Fin k → K, (∀ i, x i ∈ S) ∧ eval x p ≠ 0 := by
  classical
  by_contra! hz
  have hh := schwartz_zippel_totalDegree hp S
  have he : (Fintype.piFinset (fun _ : Fin k => S)).filter (fun x => eval x p = 0) =
      Fintype.piFinset (fun _ : Fin k => S) := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact hz x (Fintype.mem_piFinset.mp hx)
  rw [he] at hh
  have hpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
  have hpos' : (0 : ℚ≥0) < S.card := by exact_mod_cast hpos
  have hpow : (S.card : ℚ≥0)^k ≠ 0 := pow_ne_zero _ (ne_of_gt hpos')
  have hcard : (Fintype.piFinset (fun _ : Fin k => S)).card = S.card^k := by simp
  rw [hcard,Nat.cast_pow,div_self hpow] at hh
  have hlt : (p.totalDegree : ℚ≥0) / S.card < 1 :=
    (div_lt_one hpos').mpr (by exact_mod_cast hS)
  exact (not_lt_of_ge hh) hlt


-- @@ L111-122 verbatim
lemma det_totalDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial (Fin k) K)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i : ι, (A (σ i) i).totalDegree ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => hA _ _)
    _ = Fintype.card ι * d := by simp


-- @@ L124-149 verbatim
/-- The common grid specializes a list of determinant conditions
simultaneously, rather than one formula gate at a time. -/
theorem simultaneous (P : List (MvPolynomial (Fin k) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (S : Finset K) (hS : P.length * d < S.card) :
    ∃ x : Fin k → K, (∀ i, x i ∈ S) ∧ ∀ p ∈ P, eval x p ≠ 0 := by
  have hprod : P.prod ≠ 0 := List.prod_ne_zero (by intro hz; exact hP 0 hz rfl)
  have hdeg : P.prod.totalDegree ≤ P.length*d := by
    apply (totalDegree_list_prod P).trans
    clear hS hprod hP
    induction P with
    | nil => simp
    | cons p P ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hh := hd p (by simp)
      have htail := ih (fun z hz => hd z (by simp [hz]))
      rw [Nat.add_mul,Nat.one_mul]
      omega
  obtain ⟨x,hx,hxp⟩ := exists_eval_ne_zero P.prod hprod S (hdeg.trans_lt hS)
  refine ⟨x,hx,?_⟩
  intro p hp hz
  apply hxp
  change eval₂Hom (RingHom.id K) x P.prod = 0
  rw [map_list_prod]
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨p,hp,hz⟩


-- @@ L151-151 verbatim
end

-- @@ L152-152 verbatim
end RationalHitting.FiniteGrid


-- @@ L154-154 verbatim
end OAI
