import OAI.AlgebraicGeometry.StableCoordinate.DeterminantRing
import OAI.AlgebraicGeometry.StableCoordinate.RigidityCoefficients
import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure
import Mathlib.Algebra.CharP.Algebra


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-14 verbatim
/-!
# Rigidity helpers on the actual determinant quotient

These results instantiate the general derivation arguments on the exact ring
`k[a,d,b,c,u]/(ac-bd-1)`.  Generator nonvanishing is proved by an algebraic
point, not assumed or inferred from an unproved localization identification.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace StableCoordinate.DeterminantRing


-- @@ L20-20 verbatim
open MvPolynomial


-- @@ L22-22 verbatim
variable (k : Type*) [CommRing k]


-- @@ L24-25 verbatim
/-- The distinguished element of source equation `bun:v`. -/
def v : C k := a k ^ 3 * b k + a k ^ 2 * u k ^ 2 - d k ^ 2


-- @@ L27-28 verbatim
/-- A point at which the factors used by the rigidity argument are nonzero. -/
def factorPoint : C k →ₐ[k] k := lift 1 0 0 1 1 (by simp)


-- @@ L30-30 verbatim
@[simp] theorem factorPoint_a : factorPoint k (a k) = 1 := by simp [factorPoint]

-- @@ L31-31 verbatim
@[simp] theorem factorPoint_d : factorPoint k (d k) = 0 := by simp [factorPoint]

-- @@ L32-32 verbatim
@[simp] theorem factorPoint_u : factorPoint k (u k) = 1 := by simp [factorPoint]


-- @@ L34-38 verbatim
/-- The scalar inclusion is injective, witnessed by `factorPoint`. -/
theorem algebraMap_injective : Function.Injective (algebraMap k (C k)) := by
  intro x y h
  have h' := congrArg (factorPoint k) h
  simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using h'


-- @@ L40-41 verbatim
instance instCharZero [CharZero k] : CharZero (C k) :=
  charZero_of_injective_algebraMap (algebraMap_injective k)


-- @@ L43-44 verbatim
instance instNontrivial [Nontrivial k] : Nontrivial (C k) :=
  Function.Injective.nontrivial (algebraMap_injective k)


-- @@ L46-50 verbatim
/-- The first base variable is nonzero in the actual quotient. -/
theorem a_ne_zero [Nontrivial k] : a k ≠ 0 := by
  intro h
  have := congrArg (factorPoint k) h
  simp at this


-- @@ L52-56 verbatim
/-- The added base variable is nonzero in the actual quotient. -/
theorem u_ne_zero [Nontrivial k] : u k ≠ 0 := by
  intro h
  have := congrArg (factorPoint k) h
  simp at this


-- @@ L58-62 verbatim
/-- The two factors of the highest auxiliary part of `v` are nonzero. -/
theorem au_sub_d_ne_zero [Nontrivial k] : a k * u k - d k ≠ 0 := by
  intro h
  have := congrArg (factorPoint k) h
  simp at this


-- @@ L64-67 verbatim
theorem au_add_d_ne_zero [Nontrivial k] : a k * u k + d k ≠ 0 := by
  intro h
  have := congrArg (factorPoint k) h
  simp at this


-- @@ L69-71 verbatim
/-- Every element of the determinant ring has a polynomial representative. -/
theorem mk_surjective : Function.Surjective (mk k) :=
  Ideal.Quotient.mk_surjective


-- @@ L73-80 verbatim
/-- The five canonical quotient variables generate the full algebra. -/
theorem adjoin_range_generator_via_quotient :
    Algebra.adjoin k (Set.range (generator k)) = ⊤ := by
  have h : (Algebra.adjoin k (Set.range (X : Fin 5 → P k))).map (mk k) = ⊤ := by
    rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top (mk k)).mpr (mk_surjective k)
  change Algebra.adjoin k (Set.range fun i : Fin 5 => mk k (X i)) = ⊤
  simpa only [AlgHom.map_adjoin, ← Set.range_comp, Function.comp_def] using h


-- @@ L82-104 verbatim
/-- A derivation is determined by its five generator values. -/
theorem derivation_eq_zero (D : Derivation k (C k) (C k))
    (ha : D (a k) = 0) (hd : D (d k) = 0) (hb : D (b k) = 0)
    (hc : D (c k) = 0) (hu : D (u k) = 0) : D = 0 := by
  apply DFunLike.ext
  intro z
  obtain ⟨p, rfl⟩ := mk_surjective k z
  change D (mk k p) = 0
  induction p using MvPolynomial.induction_on with
  | C r =>
      change D (algebraMap k (C k) r) = 0
      exact D.map_algebraMap r
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
      rw [map_mul, D.leibniz, hp, smul_zero, add_zero]
      have hi : D (mk k (X i)) = 0 := by
        fin_cases i
        · exact ha
        · exact hd
        · exact hb
        · exact hc
        · exact hu
      rw [hi, smul_zero]


-- @@ L106-114 verbatim
/-- The coefficient of a nonzero derivation fixing `a,d,u` is nonzero. -/
theorem coefficient_ne_zero (D : Derivation k (C k) (C k))
    (hD : D ≠ 0) (ha : D (a k) = 0) (hd : D (d k) = 0) (hu : D (u k) = 0) :
    rigidityCoefficient D (b k) (c k) ≠ 0 := by
  intro hq
  obtain ⟨hb, hc⟩ := derivation_rigidityCoefficient D (a k) (d k) (b k) (c k)
    (determinant_relation k) ha hd
  rw [hq, mul_zero] at hb hc
  exact hD (derivation_eq_zero k D ha hd hb hc hu)


-- @@ L116-122 verbatim
/-- The difference-of-squares argument instantiated on the actual quotient. -/
theorem fixed_of_difference_of_squares [Nontrivial k] [IsDomain (C k)] [CharZero (C k)]
    (D : Derivation k (C k) (C k)) (hD : IsLocallyNilpotent D)
    (hv : D (a k ^ 2 * u k ^ 2 - d k ^ 2) = 0) :
    D (a k) = 0 ∧ D (d k) = 0 ∧ D (u k) = 0 :=
  lnd_fixed_of_difference_of_squares D hD (a_ne_zero k) (u_ne_zero k)
    (au_sub_d_ne_zero k) (au_add_d_ne_zero k) hv


-- @@ L124-124 verbatim
end StableCoordinate.DeterminantRing


-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end OAI
