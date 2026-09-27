/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
module


public import LeanPool.Neukirch.ExtensionOfDedekindDomains
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Measurability.Init


-- @@ L16-20 verbatim
/-!
# LeanPool.Neukirch.HilbertRamificationTheory

Imported Lean Pool material for `LeanPool.Neukirch.HilbertRamificationTheory`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Algebra


-- @@ L26-26 verbatim
open scoped BigOperators


-- @@ L28-28 verbatim
section Galois


-- @@ L30-30 verbatim
open IntermediateField AlgEquiv QuotientGroup


-- @@ L32-32 verbatim
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]


-- @@ L34-42 verbatim
/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroupEquivAut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars _, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl


-- @@ L44-55 verbatim
/-- The `AlgEquiv` induced by an `AlgHom` from the domain of definition to the `fieldRange`. -/
noncomputable def AlgHom.fieldRangeToAlgEquiv {E : IntermediateField K L} (σ : E →ₐ[K] L) :
    E ≃ₐ[K] σ.fieldRange where
  toFun x := ⟨σ x, by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]⟩
  invFun y := Classical.choose (AlgHom.mem_fieldRange.mp y.2)
  left_inv x := have hs : Function.Injective σ := RingHom.injective σ.toRingHom
    have h : σ x ∈ σ.fieldRange := by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]
    hs (Classical.choose_spec (AlgHom.mem_fieldRange.mp h))
  right_inv y := Subtype.val_inj.mp (Classical.choose_spec (mem_fieldRange.mp y.2))
  map_mul' x y := Subtype.val_inj.mp (σ.toRingHom.map_mul x y)
  map_add' x y := Subtype.val_inj.mp (σ.toRingHom.map_add x y)
  commutes' x := Subtype.val_inj.mp (commutes σ x)


-- @@ L57-57 verbatim
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}


-- @@ L59-62 verbatim
theorem AlgEquiv.liftNormal_intermediateField_commutes [Normal K L] {E F : IntermediateField K L}
    (σ : E ≃ₐ[K] F) (x : E) : (AlgEquiv.liftNormal σ L) x = σ x := by
  rw [show x.1 = algebraMap E L x from rfl, liftNormal_commutes]
  rfl


-- @@ L64-69 verbatim
/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `Gal(fixedField H/K)` is isomorphic to
`Gal(L/K)⧸H`. -/
noncomputable def IsGalois.normalAutEquivQuotientSymm [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    ((fixedField H) ≃ₐ[K] (fixedField H)) ≃* (L ≃ₐ[K] L) ⧸ H :=
  (IsGalois.normalAutEquivQuotient H).symm


-- @@ L71-71 verbatim
end Galois




-- @@ L75-75 verbatim
namespace Polynomial


-- @@ L77-77 verbatim
variable {R : Type*} (S L : Type*) [CommRing R] [CommRing S] [IsDomain S] [CommRing L] [IsDomain L]

-- @@ L78-79 verbatim
variable [Algebra R L] [Algebra S L] [Algebra R S] [IsScalarTower R S L]
  [IsIntegralClosure S R L]



-- @@ L82-82 verbatim
open Multiset


-- @@ L84-102 verbatim
/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the roots of `p` in `L`
are equal to the roots of `p` in the integral closure of `R` in `L`. -/
theorem isIntegralClosure_root_eq_ofMonic {p : R[X]} (hp : p.Monic) :
    (map (algebraMap R S) p).roots.map (algebraMap S L) = (map (algebraMap R L) p).roots := by
  classical
  ext x
  by_cases hx : ∃ y : S, algebraMap S L y = x
  · rcases hx with ⟨y, h⟩
    have hc : algebraMap R L = (algebraMap S L).comp (algebraMap R S) :=
      IsScalarTower.algebraMap_eq R S L
    have hi : Function.Injective (algebraMap S L) := IsIntegralClosure.algebraMap_injective S R L
    rw [← h, count_map_eq_count' _ _ hi _]
    rw [count_roots, count_roots, hc, ← map_map, ← eq_rootMultiplicity_map hi]
  · have h : count x ((p.map (algebraMap R S)).roots.map (algebraMap S L)) = 0 := by
      simp_all
    rw [h]
    exact Decidable.byContradiction fun h ↦ hx <| IsIntegralClosure.isIntegral_iff.mp
      ⟨p, hp, (eval₂_eq_eval_map (algebraMap R L)).trans <|
        (mem_roots (hp.map (algebraMap R L)).ne_zero).1 (count_ne_zero.mp (Ne.symm h))⟩


-- @@ L104-108 verbatim
/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the number of roots
of `p` in `L` is equal to the number of roots of `p` in the integral closure of `R` in `L`. -/
theorem isIntegralClosure_root_card_eq_ofMonic {p : R[X]} (hp : p.Monic) :
    card (map (algebraMap R S) p).roots = card (map (algebraMap R L) p).roots := by
  rw [← isIntegralClosure_root_eq_ofMonic S L hp, card_map]


-- @@ L110-116 verbatim
/-- A variant of the theorem `roots_map_of_injective_of_card_eq_natDegree` that replaces the
injectivity condition with the condition `Polynomial.map f p ≠ 0`. -/
theorem roots_map_of_card_eq_natDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0)
    (hroots : card p.roots = p.natDegree) : p.roots.map f  = (map f p).roots := by
  apply eq_of_le_of_card_le (map_roots_le h)
  simpa only [card_map, hroots] using (card_roots' (map f p)).trans natDegree_map_le


-- @@ L118-118 verbatim
end Polynomial




-- @@ L122-122 verbatim
namespace Ideal


-- @@ L124-124 verbatim
namespace IsPrime


-- @@ L126-140 verbatim
/-- If the product of a finite number of elements in the commutative semiring `R` lies in the
prime ideal `p`, then at least one of those elements is in `p`. -/
theorem prod_mem {R ι : Type*} [CommSemiring R] {p : Ideal R} [hp : p.IsPrime]
    {s : Finset ι} {x : ι → R} (h : ∏ i ∈ s, x i ∈ p) : ∃ i : s, x i ∈ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty] at h
    rw [IsEmpty.exists_iff]
    exact IsPrime.ne_top hp ((eq_top_iff_one p).mpr h)
  | insert n s nns hn =>
    rw [Finset.prod_insert nns] at h
    rcases IsPrime.mem_or_mem hp h with h | h
    · exact ⟨⟨n, Finset.mem_insert_self n s⟩, h⟩
    · simp_all


-- @@ L142-142 verbatim
end IsPrime


-- @@ L144-144 verbatim
open Module Module.Finite


-- @@ L146-146 verbatim
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (p : Ideal S)


-- @@ L148-149 verbatim
instance : IsScalarTower R (R ⧸ comap (algebraMap R S) p) (S ⧸ p) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)


-- @@ L151-154 verbatim
/-- If `S` is a finite `R`-module, then `S ⧸ p` is a finite
`R ⧸ comap (algebraMap R S) p`-module. -/
instance quotient_finite_quotient_comap : Module.Finite (R ⧸ comap (algebraMap R S) p) (S ⧸ p) :=
  Module.Finite.of_restrictScalars_finite R (R ⧸ comap (algebraMap R S) p) (S ⧸ p)


-- @@ L156-156 verbatim
end Ideal




-- @@ L160-160 verbatim
open Ideal


-- @@ L162-162 verbatim
attribute [local instance] Ideal.Quotient.field


-- @@ L164-171 verbatim
/-- If `p` is a non-zero ideal of the `ℤ`, then `ℤ ⧸ p` is finite. -/
@[reducible] noncomputable def Int.Quotient.FintypeOfNeBot {p : Ideal ℤ} (hp : p ≠ ⊥) :
    Fintype (ℤ ⧸ p) := by
  have h := Int.quotientSpanEquivZMod (Submodule.IsPrincipal.generator p)
  rw [span_singleton_generator p] at h
  have : NeZero (Int.natAbs (Submodule.IsPrincipal.generator p)) := ⟨fun eq ↦
    hp ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr (Int.natAbs_eq_zero.mp eq))⟩
  exact Fintype.ofEquiv (ZMod (Int.natAbs (Submodule.IsPrincipal.generator p))) h.symm


-- @@ L173-176 verbatim
/-- In particular, if `p` is a maximal ideal of the `ℤ`, then `ℤ ⧸ p` is a finite field. -/
noncomputable instance Int.Quotient.FintypeOfIsMaximal (p : Ideal ℤ) [hpm : p.IsMaximal] :
    Fintype (ℤ ⧸ p) :=
  FintypeOfNeBot (Ring.ne_bot_of_isMaximal_of_not_isField hpm Int.not_isField)




-- @@ L180-180 verbatim
namespace NumberField



-- @@ L183-183 verbatim
variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]


-- @@ L185-190 verbatim
/-- A finite extension of a number field is a number field. -/
theorem of_finite_extension [FiniteDimensional K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L


-- @@ L192-192 verbatim
variable [NumberField L]


-- @@ L194-196 verbatim
/-- Any extension of a Number Field is a finite extension. -/
instance Extension_FiniteDimensional : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L


-- @@ L198-199 verbatim
instance of_IntermediateField {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (E : IntermediateField K L) : NumberField E := of_finite_extension K E


-- @@ L201-201 verbatim
variable (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]


-- @@ L203-204 verbatim
instance : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)


-- @@ L206-207 verbatim
lemma ringOfIntegers_algebra_isIntegral (K : Type*) [Field K] : Algebra.IsIntegral ℤ (𝓞 K) :=
  IsIntegralClosure.isIntegral_algebra ℤ K


-- @@ L209-212 verbatim
lemma isIntegral_tower {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (x : L)
    (hx : IsIntegral (𝓞 K) x) : IsIntegral ℤ x :=
  letI := ringOfIntegers_algebra_isIntegral K
  isIntegral_trans x hx


-- @@ L214-226 verbatim
/-- The instance form of theorem `ringOfIntegers_eq_integralClosure`. -/
instance extension_ringOfIntegers_isIntegralClosure [NumberField L] :
    IsIntegralClosure (𝓞 L) (𝓞 K) L where
  algebraMap_injective := IsFractionRing.injective (𝓞 L) L
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      use ⟨x, isIntegral_tower x hx⟩
      rfl
    · intro ⟨⟨y,hy⟩, hxy⟩
      rw [← hxy]
      exact IsIntegral.tower_top hy


-- @@ L228-230 verbatim
/-- Any Extension between ring of integers is integral. -/
instance extension_ringOfIntegers_isIntegral [NumberField L] : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L


-- @@ L232-234 verbatim
/-- In particular, any Extension between ring of integers is noetherian. -/
instance extension_ringOfIntegers_isNoetherian [NumberField K] [NumberField L] :
  IsNoetherian (𝓞 K) (𝓞 L) := IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)


-- @@ L236-239 verbatim
/-- The kernel of the algebraMap between ring of integers is `⊥`. -/
theorem algebraMap_ker_eq_bot :
    RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ := by
  simp_all


-- @@ L241-243 verbatim
/-- The algebraMap between ring of integers is injective. -/
theorem algebraMap_injective_of_ringOfIntegers : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (algebraMap_ker_eq_bot K L)


-- @@ L245-246 verbatim
instance instIsScalarTower_IntermediateField_ringOfIntegers (E : IntermediateField K L) :
  IsScalarTower (𝓞 K) (𝓞 E) (𝓞 L) := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)


-- @@ L248-256 verbatim
instance instIsScalarTower_ringOfIntegers (E L : Type*) [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] :
    IsScalarTower (𝓞 K) (𝓞 E) (𝓞 L) := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  apply Subtype.val_inj.mp
  calc _ = algebraMap K L x.1 := rfl
    _ = _ := by
      rw [IsScalarTower.algebraMap_eq K E L]
      rfl


-- @@ L258-258 verbatim
variable {L : Type*} [Field L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))


-- @@ L260-261 verbatim
/-- The ideal obtained by intersecting `𝓞 K` and `P`. -/
abbrev IdealBelow : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P


-- @@ L263-263 verbatim
theorem IdealBelow_def : IdealBelow K P = comap (algebraMap (𝓞 K) (𝓞 L)) P := rfl


-- @@ L265-266 verbatim
instance IdealBelow_IsPrime [P.IsPrime] : IsPrime (IdealBelow K P) :=
  IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))


-- @@ L268-268 verbatim
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))


-- @@ L270-271 verbatim
/-- We say `P` lies over `p` if `p` is the preimage of `P` under the `algebraMap`. -/
class ideal_lies_over : Prop where liesOver_eq : p = comap (algebraMap (𝓞 K) (𝓞 L)) P


-- @@ L273-274 verbatim
/-- `P lies_over p` means the prime `p` is the preimage of `P` under the canonical algebra map. -/
infix : 50 "lies_over" => ideal_lies_over


-- @@ L276-276 expanded
instance over_IdealBelow : ideal_lies_over P (IdealBelow K P) where liesOver_eq := rfl


-- @@ L278-279 expanded
theorem over_def {p : Ideal (𝓞 K)} {P : Ideal (𝓞 L)} (h : p = IdealBelow K P) : ideal_lies_over P p
    where liesOver_eq := h


-- @@ L281-284 expanded
/-- Bridge the bespoke `lies_over` relation to Mathlib's `Ideal.LiesOver`, so that the Mathlib
ramification/inertia API applies. -/
instance (priority := 100) {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K))
    (P : Ideal (𝓞 L)) [h : ideal_lies_over P p] : P.LiesOver p :=
  ⟨h.liesOver_eq⟩


-- @@ L286-290 expanded
/-- `P` is the unique maximal ideal lying over `p`: it lies over `p` and is equal to every
maximal ideal lying over `p`. -/
class ideal_unique_lies_over : Prop extends ideal_lies_over P p where
  /-- Every maximal ideal lying over `p` is equal to `P`. -/
  unique : ∀ Q : Ideal (𝓞 L), [Q.IsMaximal] → [ideal_lies_over Q p] → Q = P


-- @@ L292-293 verbatim
/-- `P unique_lies_over p` means `P` is the unique maximal ideal lying over `p`. -/
infix : 50 "unique_lies_over" => ideal_unique_lies_over


-- @@ L295-295 verbatim
variable [NumberField L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]

-- @@ L296-296 expanded
variable [ideal_lies_over P p]


-- @@ L298-301 verbatim
/-- If `P` is a maximal ideal of `𝓞 L`, then the intersection of `P` and `𝓞 K` is also
a maximal ideal. -/
instance IdealBelow_IsMaximal : IsMaximal (IdealBelow K P) :=
  isMaximal_under_of_isIntegral_of_isMaximal P


-- @@ L303-306 verbatim
/-- In particular, if `p` is a maximal ideal of `ringOfIntegers`, then
the intersection of `p` and `ℤ` is also a maximal ideal. -/
instance Ideal_comap_int_IsMaximal (p : Ideal (𝓞 K)) [p.IsMaximal] :
  IsMaximal (comap (algebraMap ℤ (𝓞 K)) p) := isMaximal_under_of_isIntegral_of_isMaximal p


-- @@ L308-314 expanded
/-- For any maximal idela `p` in `𝓞 K`, there exists a maximal ideal in `𝓞 L` lying over `p`. -/
theorem exists_ideal_over_maximal_of_ringOfIntegers (p : Ideal (𝓞 K)) [p.IsMaximal] (L : Type*)
    [Field L] [NumberField L] [Algebra K L] :
    ∃ (P : Ideal (𝓞 L)), IsMaximal P ∧ ideal_lies_over P p :=
  by
  rcases
    exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) p
      (by simp only [algebraMap_ker_eq_bot K L, bot_le]) with
    ⟨P, hpm, hp⟩
  exact ⟨P, hpm, over_def hp.symm⟩


-- @@ L316-318 verbatim
/-- Maximal Ideals in the ring of integers are non-zero. -/
theorem ne_bot_ofIsMaximal [NumberField K] : p ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)


-- @@ L320-324 verbatim
/-- The image of a maximal ideal under the algebraMap between ring of integers is non-zero. -/
theorem map_isMaximal_ne_bot [NumberField K] (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [Algebra K L] : map (algebraMap (𝓞 K) (𝓞 L)) p ≠ ⊥ :=
  fun h ↦ (ne_bot_ofIsMaximal p)
    ((map_eq_bot_iff_of_injective (algebraMap_injective_of_ringOfIntegers K L)).mp h)


-- @@ L326-328 verbatim
theorem prime_iff_isMaximal (P : Ideal (𝓞 L)) : Prime P ↔ IsMaximal P :=
  ⟨fun hp ↦ IsPrime.isMaximal (isPrime_of_prime hp) (Prime.ne_zero hp),
    fun hp ↦ prime_of_isPrime (ne_bot_ofIsMaximal P) (IsMaximal.isPrime hp)⟩


-- @@ L330-333 verbatim
/-- The `Finset` consists of all primes lying over `p : Ideal (𝓞 K)`. -/
noncomputable abbrev primesOver {K : Type*} [Field K] (p : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : Finset (Ideal (𝓞 L)) := by
  classical exact (UniqueFactorizationMonoid.factors (map (algebraMap (𝓞 K) (𝓞 L)) p)).toFinset


-- @@ L335-335 verbatim
open UniqueFactorizationMonoid


-- @@ L337-337 verbatim
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

-- @@ L338-338 verbatim
variable [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]


-- @@ L340-352 expanded
theorem primesOver_mem : P ∈ primesOver p L ↔ P.IsMaximal ∧ ideal_lies_over P p :=
  by
  constructor
  · intro hp
    classical have hp := Multiset.mem_toFinset.mp hp
    have hpm := (prime_iff_isMaximal P).mp (prime_of_factor P hp)
    exact
      ⟨hpm,
        over_def <|
          IsMaximal.eq_of_le inferInstance (comap_ne_top _ (IsMaximal.ne_top hpm))
            (le_comap_of_map_le (le_of_dvd (dvd_of_mem_factors hp)))⟩
  · intro ⟨hpm, hp⟩
    have hd := dvd_iff_le.mpr (map_le_of_le_comap (le_of_eq hp.liesOver_eq))
    have hir := irreducible_iff_prime.mpr ((prime_iff_isMaximal P).mpr hpm)
    rcases exists_mem_factors_of_dvd (map_isMaximal_ne_bot p L) hir hd with ⟨_, hq, he⟩
    classical rwa [Multiset.mem_toFinset, associated_iff_eq.mp he]


-- @@ L354-355 verbatim
instance primesOver_instIsMaximal (Q : primesOver p L) : IsMaximal Q.1 :=
  ((primesOver_mem p Q.1).mp Q.2).1


-- @@ L357-358 expanded
instance primesOver_inst_lies_over (Q : primesOver p L) : ideal_lies_over Q.1 p :=
  ((primesOver_mem p Q.1).mp Q.2).2


-- @@ L360-363 expanded
/-- Given a maximal ideal `P lies_over p` in `𝓞 L`, `primesOverMk` sends `P` to an element of
the subset `primesOver p L` of `Ideal (𝓞 L)`. -/
abbrev primesOverMk [P.IsMaximal] [ideal_lies_over P p] : primesOver p L :=
  ⟨P, (primesOver_mem p P).mpr ⟨inferInstance, inferInstance⟩⟩


-- @@ L365-368 verbatim
theorem primesOver_card_ne_zero (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    Finset.card (primesOver p L) ≠ 0 := by
  rcases exists_ideal_over_maximal_of_ringOfIntegers p L with ⟨P, hp⟩
  exact Finset.card_ne_zero_of_mem ((primesOver_mem p P).mpr hp)


-- @@ L370-372 verbatim
/-- The `Finset` consists of all primes lying over `IdealBelow K P`, i.e., all the primes `Q` such
that `IdealBelow K Q = IdealBelow K P`. -/
noncomputable abbrev primesSameBleow : Finset (Ideal (𝓞 L)) := primesOver (IdealBelow K P) L


-- @@ L374-381 verbatim
theorem Nonsplit_iff_primesOver_card_eq_one :
    Nonsplit (algebraMap (𝓞 K) (𝓞 L)) p ↔ Finset.card (primesOver p L) = 1 := by
  have h : Finset.card (primesOver p L) = 1 ↔ Finset.card (primesOver p L) ≤ 1 :=
    ⟨fun h ↦ Nat.le_of_eq h ,
      fun h ↦ Nat.le_antisymm h (Nat.one_le_iff_ne_zero.mpr (primesOver_card_ne_zero p L))⟩
  simp only [h, Finset.card_le_one, primesOver_mem, and_imp]
  exact ⟨fun h P hpm hp Q hqm hq ↦ h.nonsplit P hpm hp.liesOver_eq Q hqm hq.liesOver_eq,
    fun h ↦ {nonsplit := fun P hpm hp Q hqm hq ↦ h P hpm (over_def hp) Q hqm (over_def hq)}⟩


-- @@ L383-389 expanded
theorem unique_lies_over_Nonsplit {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K))
    (P : Ideal (𝓞 L)) [hp : ideal_unique_lies_over P p] : Nonsplit (algebraMap (𝓞 K) (𝓞 L)) p where
  nonsplit Q1 _ hq1 Q2 _
    hq2 := by
    let := over_def hq1
    let := over_def hq2
    rw [hp.unique Q1, hp.unique Q2]


-- @@ L391-394 expanded
/-- Another form of the property `unique_lies_over`. -/
theorem unique_primesOver_card_eq_one (P : Ideal (𝓞 L)) [ideal_unique_lies_over P p] :
    Finset.card (primesOver p L) = 1 :=
  (Nonsplit_iff_primesOver_card_eq_one p).mp (unique_lies_over_Nonsplit p P)


-- @@ L398-398 verbatim
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {E : Type*} [Field E]

-- @@ L399-399 verbatim
variable [NumberField E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]

-- @@ L400-400 verbatim
variable (p : Ideal (𝓞 K)) (𝔓 : Ideal (𝓞 E)) (P : Ideal (𝓞 L))


-- @@ L402-404 expanded
omit [NumberField L] [NumberField E] in
theorem ideal_lies_over_trans [hp : ideal_lies_over 𝔓 p] [hP : ideal_lies_over P 𝔓] :
    ideal_lies_over P p where
  liesOver_eq := by rw [hp.liesOver_eq, hP.liesOver_eq, comap_comap, ← IsScalarTower.algebraMap_eq]


-- @@ L406-408 expanded
omit [NumberField L] [NumberField E] in
theorem ideal_lies_over_tower_bot [hp : ideal_lies_over P p] [hP : ideal_lies_over P 𝔓] :
    ideal_lies_over 𝔓 p where
  liesOver_eq := by rw [hp.liesOver_eq, hP.liesOver_eq, comap_comap, ← IsScalarTower.algebraMap_eq]


-- @@ L410-417 expanded
omit [NumberField L] [NumberField E] in
theorem ideal_unique_lies_over_trans [hp : ideal_unique_lies_over 𝔓 p]
    [hP : ideal_unique_lies_over P 𝔓] : ideal_unique_lies_over P p :=
  { ideal_lies_over_trans p 𝔓 P with
    unique := fun Q _ _ ↦
      letI := ideal_lies_over_tower_bot p (IdealBelow E Q) Q
      letI := over_def (hp.unique (IdealBelow E Q)).symm
      hP.unique Q }


-- @@ L419-428 expanded
omit [NumberField E] in
theorem ideal_unique_lies_over_tower_bot [hp : ideal_unique_lies_over P p]
    [hP : ideal_lies_over P 𝔓] : ideal_unique_lies_over 𝔓 p :=
  { ideal_lies_over_tower_bot p 𝔓 P with
    unique := by
      intro 𝔔 _ _
      rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔔 L with ⟨Q, ⟨hqm, hq⟩⟩
      let := ideal_lies_over_trans p 𝔔 Q
      let := hp.unique Q
      rw [hq.liesOver_eq, hp.unique Q, hP.liesOver_eq] }


-- @@ L430-439 expanded
omit [NumberField E] in
theorem ideal_unique_lies_over_tower_top [𝔓.IsMaximal] [hP : ideal_unique_lies_over P p]
    [ideal_lies_over 𝔓 p] : ideal_unique_lies_over P 𝔓
    where
  liesOver_eq :=
    by
    rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔓 L with ⟨Q, ⟨_, hq⟩⟩
    let := ideal_lies_over_trans p 𝔓 Q
    rw [← hP.unique Q, hq.liesOver_eq]
  unique := fun Q _ _ ↦
    letI := ideal_lies_over_trans p 𝔓 Q
    hP.unique Q


-- @@ L441-441 verbatim
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- @@ L442-442 expanded
variable (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [ideal_lies_over P p] (E : IntermediateField K L)


-- @@ L444-445 expanded
instance IntermediateField_ideal_lies_over : ideal_lies_over (IdealBelow E P) p :=
  ideal_lies_over_tower_bot p (IdealBelow E P) P


-- @@ L447-449 verbatim
omit [NumberField K] [NumberField L] in
theorem Ideal_comap_IntermediateField : p = comap (algebraMap (𝓞 K) (𝓞 E)) (IdealBelow E P) :=
  (IntermediateField_ideal_lies_over p P E).liesOver_eq


-- @@ L451-453 expanded
instance IntermediateField_ideal_unique_lies_over (P : Ideal (𝓞 L)) [ideal_unique_lies_over P p]
    (E : IntermediateField K L) : ideal_unique_lies_over (IdealBelow E P) p :=
  ideal_unique_lies_over_tower_bot p (IdealBelow E P) P


-- @@ L459-459 verbatim
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))

-- @@ L460-460 expanded
variable [p.IsMaximal] [hpm : P.IsMaximal] [hp : ideal_lies_over P p]


-- @@ L462-465 verbatim
/-- If `P` lies over `p`, then the residue class field of `p` has a canonical map to
the residue class field of `P`. -/
instance residueFieldInstAlgebra : Algebra ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hp.liesOver_eq)


-- @@ L467-468 verbatim
instance : IsScalarTower (𝓞 K) ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)


-- @@ L470-474 expanded
/-- The extension between residue class fields is finite. -/
instance residue_field_instFiniteDimensional {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]
    [ideal_lies_over P p] : FiniteDimensional ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  Module.Finite.of_restrictScalars_finite (𝓞 K) ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)


-- @@ L476-483 expanded
/-- A quotient by any ideal lying over a maximal ideal has positive dimension, even when the
ideal upstairs is not prime. This retains the generality of the former quotient-based inertia
degree. -/
theorem quotient_finrank_pos_of_lies_over {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]
    [ideal_lies_over P p] : 0 < Module.finrank ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  by
  let : Nontrivial ((𝓞 L) ⧸ P) := Ideal.Quotient.nontrivial_of_liesOver_of_isPrime P p
  exact Module.finrank_pos


-- @@ L485-492 expanded
theorem inertiaDeg_pos {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [ideal_lies_over P p] : P.inertiaDeg (𝓞 K) > 0 :=
  by
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
  exact quotient_finrank_pos_of_lies_over p P


-- @@ L494-502 verbatim
/-- The ring homomorphism `(𝓞 K) →+* (𝓞 L)` induced by restricting any ring homomorphism
`f : K → L` (given through a `RingHomClass`) to the rings of integers. -/
def mapRingHomOfClass {K L F : Type*} [Field K] [Field L] [FunLike F K L]
    [RingHomClass F K L] (f : F) : (𝓞 K) →+* (𝓞 L) where
  toFun k := ⟨f k, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
  map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
  map_add' x y := SetCoe.ext (map_add f x.1 y.1)
  map_mul' x y := SetCoe.ext (map_mul f x.1 y.1)


-- @@ L504-510 verbatim
/-- The algebra homomorphism `(𝓞 K) →ₐ[𝓞 k] (𝓞 L)` induced by restricting any algebra
homomorphism `f : K → L` (given through an `AlgHomClass`) to the rings of integers. -/
def mapAlgHomOfClass {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) →ₐ[𝓞 k] (𝓞 L) where
  toRingHom := mapRingHomOfClass f
  commutes' x :=
    SetCoe.ext (AlgHomClass.commutes ((AlgHom.ofClass f).restrictScalars (𝓞 k)) x)


-- @@ L512-520 verbatim
/-- The `AlgEquiv` of elements of Galois group `Gal(K/L)` restricted to `𝓞 L`. -/
def GalAlgEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) :=
  AlgEquiv.ofAlgHom (mapAlgHomOfClass σ) (mapAlgHomOfClass σ.symm)
    (by
      ext x
      exact σ.apply_symm_apply x.1)
    (by
      ext x
      exact σ.symm_apply_apply x.1)


-- @@ L522-524 verbatim
theorem GalAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) : (GalAlgEquiv σ x).1 = σ x.1 := by
  change ((mapAlgHomOfClass σ) x).1 = σ x.1
  rfl


-- @@ L526-528 verbatim
/-- Consider `GalAlgEquiv σ` as a ring homomorphism. -/
def GalRingHom (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L) :=
  (GalAlgEquiv σ).toAlgHom.toRingHom


-- @@ L530-531 verbatim
theorem GalAlgEquiv_toAlgHom_toRingHom_eq_GalRingHom (σ : L ≃ₐ[K] L) :
    (GalAlgEquiv σ).toAlgHom.toRingHom = GalRingHom σ := rfl


-- @@ L533-537 verbatim
theorem GalRingHom_mul (σ τ : L ≃ₐ[K] L) :
  (GalRingHom σ).comp (GalRingHom τ) = GalRingHom (σ * τ) := by
  ext x
  change σ (τ x.1) = (σ * τ) x.1
  rfl


-- @@ L539-541 verbatim
theorem GalRingHom_one : GalRingHom (1 : L ≃ₐ[K] L) = RingHom.id (𝓞 L) := by
  ext x
  rfl


-- @@ L543-544 verbatim
theorem GalRingHom_inv_mul_cancel (σ : L ≃ₐ[K] L) : (GalRingHom σ⁻¹).comp (GalRingHom σ)
  = RingHom.id (𝓞 L) := by rw [GalRingHom_mul, inv_mul_cancel, GalRingHom_one]


-- @@ L546-548 verbatim
theorem GalRingHom_inv_mul_cancel_mem (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    GalRingHom σ⁻¹ (GalRingHom σ x) = x := by
  rw [← RingHom.comp_apply, GalRingHom_inv_mul_cancel, RingHom.id_apply]


-- @@ L550-551 verbatim
theorem GalRingHom_mul_inv_cancel (σ : L ≃ₐ[K] L) : (GalRingHom σ).comp (GalRingHom σ⁻¹)
  = RingHom.id (𝓞 L) := by rw [GalRingHom_mul, mul_inv_cancel, GalRingHom_one]


-- @@ L553-555 verbatim
theorem GalRingHom_mul_inv_cancel_mem (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    GalRingHom σ (GalRingHom σ⁻¹ x) = x := by
  rw [← RingHom.comp_apply, GalRingHom_mul_inv_cancel, RingHom.id_apply]


-- @@ L557-562 verbatim
/-- The `GalRingHom σ` will send a maximal ideal to a maximal ideal. -/
instance GalRingHom_map_isMaximal (σ : L ≃ₐ[K] L) : IsMaximal (map (GalRingHom σ) P) :=
  Quotient.maximal_of_isField _ <| MulEquiv.isField (Field.toIsField ((𝓞 L) ⧸ P))
    (quotientEquiv P (map (GalRingHom σ) P) (GalAlgEquiv σ) rfl).symm.toMulEquiv

-- Propsition 9.1


-- @@ L564-596 expanded
/-- The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals `P` of `𝓞 L`
lying above `p`, i.e., these prime ideals are all conjugates of each other. -/
theorem IsMaximal_conjugates {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hpm : P.IsMaximal] [hp : ideal_lies_over P p]
    (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [hq : ideal_lies_over Q p] [IsGalois K L] :
    ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q :=
  by
  by_contra hs
  simp only [not_exists] at hs
  let s : Finset (L ≃ₐ[K] L) := Finset.univ
  rcases
    Submodule.mem_sup.mp <|
      (eq_top_iff_one (Q ⊔ ∏ σ ∈ s, map (GalRingHom σ) P)).mp <|
        sup_prod_eq_top <| fun σ _ ↦
          IsMaximal.coprime_of_ne hqm (GalRingHom_map_isMaximal P σ) (Ne.symm (hs σ)) with
    ⟨x, hx, y, hy, hxy⟩
  let n : 𝓞 L := ∏ σ ∈ s, (GalRingHom σ) x
  have hnx : n = (algebraMap (𝓞 K) (𝓞 L)) (RingOfIntegers.norm K x) :=
    Subtype.val_inj.mp <|
      Eq.trans
        (Submonoid.coe_finsetProd (integralClosure ℤ L).toSubmonoid (fun i ↦ (GalRingHom i) x) s)
        (Algebra.norm_eq_prod_automorphisms K x.1).symm
  have hnk : RingOfIntegers.norm K x ∈ IdealBelow K P :=
    by
    rw [IdealBelow, ← hp.liesOver_eq, hq.liesOver_eq]
    apply mem_comap.mpr
    rw [← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact
      prod_le_inf.trans <|
        (@Finset.inf_le _ _ _ _ s (fun σ ↦ span {(GalRingHom σ) x}) _
              (@Finset.mem_univ (L ≃ₐ[K] L) _ 1)).trans
          (Iff.mpr (span_singleton_le_iff_mem Q) hx)
  have hnp : n ∈ P := Eq.mpr (_root_.id (hnx ▸ Eq.refl (n ∈ P))) hnk
  rcases IsPrime.prod_mem hnp with ⟨⟨σ, _⟩, hs⟩
  have hxp : x ∈ map (GalRingHom σ⁻¹) P :=
    Eq.mpr ((GalRingHom_inv_mul_cancel_mem σ x).symm ▸ Eq.refl _)
      (mem_map_of_mem (GalRingHom σ⁻¹) hs)
  have h :=
    Ideal.add_mem (map (GalRingHom σ⁻¹) P) hxp <|
      (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ⁻¹))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top (GalRingHom_map_isMaximal P σ⁻¹) ((eq_top_iff_one _).mpr h)


-- @@ L598-603 verbatim
theorem IsMaximal_conjugates' {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {P : Ideal (𝓞 L)} [P.IsMaximal] {Q : Ideal (𝓞 L)} [Q.IsMaximal]
    [IsGalois K L] (h : IdealBelow K P = IdealBelow K Q) :
    ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q :=
  letI := over_def h
  IsMaximal_conjugates (IdealBelow K P) P Q




-- @@ L607-607 verbatim
open UniqueFactorizationMonoid IsDedekindDomain


-- @@ L609-622 verbatim
/-- The function normalizedFactors commutes with the function `map (GalRingHom σ)`. -/
theorem normalizedFactors_map_GalRingHom_commutes {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) (σ : L ≃ₐ[K] L) :
    normalizedFactors (map (GalRingHom σ) I) =
    Multiset.map (map (GalRingHom σ)) (normalizedFactors I) := by
  nth_rw 1 [← Ideal.prod_normalizedFactors_eq_self hI]
  have h := Multiset.prod_hom (normalizedFactors I) (mapHom (GalRingHom σ))
  simp only [mapHom_apply] at h
  rw [← h, normalizedFactors_prod_of_prime]
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨p, hp, hpq⟩
  have : IsMaximal p := (prime_iff_isMaximal p).mp (prime_of_normalized_factor p hp)
  rw [← hpq]
  exact (prime_iff_isMaximal (map (GalRingHom σ) p)).mpr (GalRingHom_map_isMaximal p σ)


-- @@ L624-637 verbatim
/-- The image of an ideal under the algebraMap between ring of integers remains invariant
under the action of `GalRingHom σ`. -/
theorem Ideal_map_invariant_under_GalRingHom (p : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (map (GalRingHom σ)) (map (algebraMap (𝓞 K) (𝓞 L)) p) = map (algebraMap (𝓞 K) (𝓞 L)) p := by
  apply le_antisymm <| map_le_of_le_comap <| map_le_of_le_comap <|
    fun _ h ↦ by simp only [← GalAlgEquiv_toAlgHom_toRingHom_eq_GalRingHom,
      AlgHom.toRingHom_eq_coe, mem_comap, RingHom.coe_coe, AlgHom.commutes,
      mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h]
  apply map_le_of_le_comap
  intro x h
  rw [mem_comap, map_map]
  apply Set.mem_of_eq_of_mem _ (mem_map_of_mem ((GalRingHom σ).comp (algebraMap (𝓞 K) (𝓞 L))) h)
  rw [GalRingHom, ← AlgEquiv.commutes (GalAlgEquiv σ) x]
  rfl


-- @@ L639-642 verbatim
/-- The map induced by `GalRingHom σ` on the ideals of `𝓞 L` is injective. -/
theorem GalRingHom_IdealMap_injective (σ : L ≃ₐ[K] L) : Function.Injective (map (GalRingHom σ)) :=
  fun I J h ↦ by rw [← map_id I, ← GalRingHom_inv_mul_cancel σ, ← map_map, h, map_map,
    GalRingHom_inv_mul_cancel σ, map_id]


-- @@ L644-644 verbatim
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

-- @@ L645-646 expanded
variable [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
  [hp : ideal_lies_over P p]


-- @@ L648-659 expanded
/-- In the case of Galois extension, all the `ramificationIdx` are the same. -/
theorem ramificationIdx_eq_of_isGalois (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [ideal_lies_over Q p]
    [IsGalois K L] : ramificationIdx' p P = ramificationIdx' p Q := by
  classical
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [ramificationIdx'_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) inferInstance
      (ne_bot_ofIsMaximal P),
    ramificationIdx'_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) (IsMaximal.isPrime hqm)
      (ne_bot_ofIsMaximal Q),
    ← hs]
  nth_rw 2 [← Ideal_map_invariant_under_GalRingHom p σ]
  rw [normalizedFactors_map_GalRingHom_commutes (map_isMaximal_ne_bot p L) σ,
    Multiset.count_map_eq_count' _ _ (GalRingHom_IdealMap_injective σ) _]


-- @@ L661-667 verbatim
theorem ramificationIdx_eq_of_isGalois' [IsGalois K L] {P : Ideal (𝓞 L)} [P.IsMaximal]
    {Q : Ideal (𝓞 L)} [hqm : Q.IsMaximal] (h : IdealBelow K P = IdealBelow K Q) :
    ramificationIdx' (IdealBelow K P) P =
    ramificationIdx' (IdealBelow K Q) Q := by
  let := over_def h
  rw [← h]
  exact ramificationIdx_eq_of_isGalois (IdealBelow K P) P Q


-- @@ L669-678 expanded
theorem IdealBelow_invariant_under_GalRingHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hp : ideal_lies_over P p] (σ : L ≃ₐ[K] L) :
    p = IdealBelow K (map (GalRingHom σ) P) := by
  ext x
  rw [mem_comap, hp.liesOver_eq, mem_comap]
  refine
    ⟨fun h ↦
      Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ).commutes x]; rfl)
        (mem_map_of_mem (GalRingHom σ) h),
      fun h ↦ ?_⟩
  have h := mem_map_of_mem (GalRingHom σ⁻¹) h
  rw [map_map, GalRingHom_inv_mul_cancel, map_id] at h
  exact Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ⁻¹).commutes x]; rfl) h


-- @@ L680-681 expanded
instance GalRingHom_map_lies_over (σ : L ≃ₐ[K] L) : ideal_lies_over (map (GalRingHom σ) P) p :=
  over_def (IdealBelow_invariant_under_GalRingHom p P σ)


-- @@ L683-692 expanded
/-- The algebra equiv `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ map (GalRingHom σ) P)`
induced by an algebra equiv `σ : L ≃ₐ[K] L`. -/
def residueFieldGalAlgEquiv {P : Ideal (𝓞 L)} [ideal_lies_over P p] {Q : Ideal (𝓞 L)}
    [ideal_lies_over Q p] {σ : L ≃ₐ[K] L} (hs : map (GalRingHom σ) P = Q) :
    ((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ Q) :=
  { quotientEquiv P Q (GalAlgEquiv σ) (by rw [← hs]; rfl) with
    commutes' := by
      rintro ⟨x⟩
      exact congrArg (Ideal.Quotient.mk Q) (AlgEquiv.commutes (GalAlgEquiv σ) x) }


-- @@ L694-701 expanded
omit [p.IsMaximal] in
/-- In the case of Galois extension, all the `inertiaDeg` are the same. -/
theorem inertiaDeg_eq_of_isGalois (Q : Ideal (𝓞 L)) [Q.IsMaximal] [ideal_lies_over Q p]
    [IsGalois K L] : P.inertiaDeg (𝓞 K) = Q.inertiaDeg (𝓞 K) :=
  by
  let : p.IsMaximal := Ideal.IsMaximal.of_isMaximal_liesOver P p
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [inertiaDeg_eq_of_isMaximal p P, inertiaDeg_eq_of_isMaximal p Q]
  exact LinearEquiv.finrank_eq (residueFieldGalAlgEquiv p hs).toLinearEquiv


-- @@ L703-709 verbatim
/-- In the case of Galois extension, it can be seen from the Theorem
`ramificationIdx_eq_of_IsGalois` that all `ramificationIdx` are the same, which we define as the
`ramificationIdxOfIsGalois`. -/
noncomputable def ramificationIdxOfIsGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  ramificationIdx' p <|
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)


-- @@ L711-715 verbatim
/-- In the case of Galois extension, it can be seen from the Theorem `inertiaDeg_eq_of_IsGalois`
that all `inertiaDeg` are the same, which we define as the `inertiaDegOfIsGalois`. -/
noncomputable def inertiaDegOfIsGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  Ideal.inertiaDeg (Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)) (𝓞 K)


-- @@ L717-723 verbatim
/-- In the case of Galois extension, all ramification indices are equal to the
`ramificationIdxOfIsGalois`. This completes the property mentioned in our previous definition. -/
theorem ramificationIdx_eq_ramificationIdxOfIsGalois [IsGalois K L] :
    ramificationIdx' p P = ramificationIdxOfIsGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [ramificationIdxOfIsGalois]
  exact ramificationIdx_eq_of_isGalois p P _


-- @@ L725-731 verbatim
/-- In the case of Galois extension, all inertia degrees are equal to the `inertiaDegOfIsGalois`.
This completes the property mentioned in our previous definition. -/
theorem inertiaDeg_eq_inertiaDegOfIsGalois [IsGalois K L] :
    P.inertiaDeg (𝓞 K) = inertiaDegOfIsGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [inertiaDegOfIsGalois]
  exact inertiaDeg_eq_of_isGalois p P _


-- @@ L733-750 expanded
/-- The fundamental identity `∑ P, e_P * f_P = [L : K]` over the `Finset` of primes above `p`,
in the Galois case. Restates the retired `Ideal.sum_ramification_inertia` via the current
Mathlib form `Ideal.sum_ramification_inertia_eq_card` applied to the Galois group. -/
private theorem sum_ramification_inertia_of_isGalois (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOver p L, ramificationIdx' p P * P.inertiaDeg (𝓞 K) = Module.finrank K L := by
  classical
  have : Fintype (p.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  rw [← IsGaloisGroup.card_eq_finrank (L ≃ₐ[K] L) K L, ←
    Ideal.sum_ramification_inertia_eq_card p (𝓞 L) (G := L ≃ₐ[K] L), ←
    Finset.sum_coe_sort (s := primesOver p L)]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun Q => ?_) _ _ fun Q => ?_
  · exact IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)
  · obtain ⟨Q, hQ⟩ := Q
    have h1 : Q.IsMaximal := ((primesOver_mem p Q).mp hQ).1
    have h2 : ideal_lies_over Q p := ((primesOver_mem p Q).mp hQ).2
    rw [ramificationIdx'_eq_ramificationIdx p Q hp0]
    rfl


-- @@ L752-767 verbatim
/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ramificationIdx_mul_inertiaDegOfIsGalois (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    Finset.card (primesOver p L) * (ramificationIdxOfIsGalois p L * inertiaDegOfIsGalois p L) =
    Module.finrank K L := by
  rw [← smul_eq_mul, ← Finset.sum_const,
    ← sum_ramification_inertia_of_isGalois p L (ne_bot_ofIsMaximal p)]
  apply Finset.sum_congr rfl
  intro P hp
  let := ((primesOver_mem p P).mp hp).1
  let := ((primesOver_mem p P).mp hp).2
  rw [ramificationIdx_eq_ramificationIdxOfIsGalois, inertiaDeg_eq_inertiaDegOfIsGalois p P]



-- Definition 9.2


-- @@ L769-769 verbatim
open MulAction


-- @@ L771-784 verbatim
/-- The `MulAction` of the Galois group `L ≃ₐ[K] L` on the set `primesOver p L`,
given by `σ ↦ (P ↦ σ P)`. -/
instance GalMulActionPrimes (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (primesOver p L) where
  smul σ Q := primesOverMk p (map (GalRingHom σ) Q.1)
  one_smul Q :=
    have h : primesOverMk p (map (GalRingHom (1 : L ≃ₐ[K] L)) Q.1) = Q := by
      simp only [GalRingHom_one, map_id]
    h
  mul_smul σ τ Q :=
    have h : primesOverMk p (map (GalRingHom (σ * τ)) Q.1) =
        primesOverMk p (map (GalRingHom σ) (primesOverMk p (map (GalRingHom τ) Q.1)).1) := by
      simp only [map_map, GalRingHom_mul]
    h


-- @@ L786-787 verbatim
theorem GalMulActionPrimes_mk_coe (σ : L ≃ₐ[K] L) :
  (σ • primesOverMk p P).1 = map (GalRingHom σ) P := rfl


-- @@ L789-791 verbatim
/-- The decomposition group of `P` over `K`, is the stabilizer of `primesOverMk p P`
under the action `GalMulActionPrimes`. -/
def DecompositionGroup : Subgroup (L ≃ₐ[K] L) := stabilizer _ (primesOverMk p P)


-- @@ L793-797 verbatim
/-- The `DecompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant. -/
theorem DecompositionGroup_mem (σ : L ≃ₐ[K] L) :
    σ ∈ DecompositionGroup p P ↔ map (GalRingHom σ) P = P := by
  rw [DecompositionGroup, mem_stabilizer_iff, ← Subtype.val_inj, GalMulActionPrimes_mk_coe]


-- @@ L799-799 verbatim
open IntermediateField Module FiniteDimensional


-- @@ L801-802 verbatim
/-- The decomposition field of `P` over `K` is the fixed field of `DecompositionGroup p P`. -/
def DecompositionField : IntermediateField K L := fixedField (DecompositionGroup p P)


-- @@ L804-806 verbatim
/-- DecompositionField is a Number Field. -/
instance DecompositionField_NumberField : NumberField (DecompositionField p P) :=
  of_IntermediateField (DecompositionField p P)


-- @@ L808-810 verbatim
/-- The ideal equal to the intersection of `P` and `DecompositionField p P`. -/
abbrev DecompositionIdeal : Ideal (𝓞 (DecompositionField p P)) :=
  IdealBelow (DecompositionField p P) P


-- @@ L812-818 verbatim
instance DecompositionIdeal_isMaximal : IsMaximal (DecompositionIdeal p P) :=
  IdealBelow_IsMaximal P




-- Proposition 9.3


-- @@ L820-836 verbatim
open Classical in
theorem DecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg [IsGalois K L] :
    Fintype.card (DecompositionGroup p P) =
    ramificationIdxOfIsGalois p L * inertiaDegOfIsGalois p L := by
  have : Fintype (orbit (L ≃ₐ[K] L) (primesOverMk p P)) :=
    Set.fintypeRange fun m ↦ m • primesOverMk p P
  have horbit : orbit (L ≃ₐ[K] L) (primesOverMk p P) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro Q
    obtain ⟨σ, hs⟩ := IsMaximal_conjugates p P Q.1
    exact ⟨σ, by rw [← Subtype.val_inj, ← hs]; rfl⟩
  apply mul_left_cancel₀ (primesOver_card_ne_zero p L)
  rw [ramificationIdx_mul_inertiaDegOfIsGalois, ← IsGalois.card_aut_eq_finrank,
    Nat.card_eq_fintype_card, DecompositionGroup,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (L ≃ₐ[K] L) (primesOverMk p P)]
  simp only [horbit, Fintype.card_setUniv, Fintype.card_coe]
  congr!


-- @@ L838-843 verbatim
open Classical in
theorem Extension_degree_over_DecompositionField_eq_ramificationIdx_mul_inertiaDeg
    [IsGalois K L] : finrank (DecompositionField p P) L =
    ramificationIdxOfIsGalois p L * inertiaDegOfIsGalois p L := by
  rw [DecompositionField, finrank_fixedField_eq_card (DecompositionGroup p P),
    Nat.card_eq_fintype_card, DecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg p P]


-- @@ L845-851 expanded
/-- `P` is the unique ideal lying over `DecompositionIdeal p P`. -/
theorem isMaximal_lies_over_DecompositionIdeal_unique (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [ideal_lies_over Q (DecompositionIdeal p P)] [IsGalois K L] : Q = P :=
  by
  rcases IsMaximal_conjugates (DecompositionIdeal p P) P Q with ⟨σ, hs⟩
  let τ := (subgroupEquivAut (DecompositionGroup p P)).toFun σ
  have h : GalRingHom σ = GalRingHom τ.1 := rfl
  rw [← hs, h, (DecompositionGroup_mem p P τ.1).mp τ.2]


-- @@ L853-856 expanded
/-- The instance form of `isMaximal_lies_over_DecompositionIdeal_unique`. -/
instance unique_lies_over_DecompositionIdeal [IsGalois K L] :
    ideal_unique_lies_over P (DecompositionIdeal p P) :=
  { over_IdealBelow P with unique := fun Q ↦ isMaximal_lies_over_DecompositionIdeal_unique p P Q }


-- @@ L858-860 verbatim
instance DecompositionIdeal_Nonsplit [IsGalois K L] :
    Nonsplit (algebraMap (𝓞 (DecompositionField p P)) (𝓞 L))
  (DecompositionIdeal p P) := unique_lies_over_Nonsplit (DecompositionIdeal p P) P


-- @@ L862-865 verbatim
/-- An alternative statement of `isMaximal_lies_over_DecompositionIdeal_unique`. -/
theorem primesOver_DecompositionIdeal_card_eq_one [IsGalois K L] :
  Finset.card (primesOver (DecompositionIdeal p P) L) = 1 :=
    unique_primesOver_card_eq_one (DecompositionIdeal p P) P


-- @@ L867-890 verbatim
theorem ramificationIdx_and_inertiaDeg_of_DecompositionIdeal [IsGalois K L] :
    ramificationIdxOfIsGalois (DecompositionIdeal p P) L = ramificationIdxOfIsGalois p L ∧
    inertiaDegOfIsGalois (DecompositionIdeal p P) L = inertiaDegOfIsGalois p L := by
  let Pz := IdealBelow (DecompositionField p P) P
  let E := { x // x ∈ DecompositionField p P }
  have h := ramificationIdx_mul_inertiaDegOfIsGalois Pz L
  rw [primesOver_DecompositionIdeal_card_eq_one p P, one_mul,
    Extension_degree_over_DecompositionField_eq_ramificationIdx_mul_inertiaDeg p P] at h
  have h0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx'_ne_zero
    (map_isMaximal_ne_bot p L) inferInstance (map_le_of_le_comap (le_of_eq hp.liesOver_eq))
  have hr := Nat.le_of_dvd h0 <| Dvd.intro_left _ <| Eq.symm <|
    ramificationIdx_algebra_tower_of_eq (map_isMaximal_ne_bot p E) (map_isMaximal_ne_bot Pz L)
      (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pz) (ne_bot_ofIsMaximal P) rfl
  have h0 : P.inertiaDeg (𝓞 K) > 0 := inertiaDeg_pos p P
  have hi := Nat.le_of_dvd h0 <| Dvd.intro_left _  <| Eq.symm <|
    inertiaDeg_algebra_tower_of_eq (𝓞 K) (IdealBelow_def E P)
  rw [ramificationIdx_eq_ramificationIdxOfIsGalois Pz P,
    ramificationIdx_eq_ramificationIdxOfIsGalois p P] at hr
  rw [inertiaDeg_eq_inertiaDegOfIsGalois Pz P, inertiaDeg_eq_inertiaDegOfIsGalois p P] at hi
  have hr0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx'_ne_zero
    (map_isMaximal_ne_bot Pz L) inferInstance (map_le_of_le_comap (le_of_eq rfl))
  rw [inertiaDeg_eq_inertiaDegOfIsGalois p P] at h0
  rw [ramificationIdx_eq_ramificationIdxOfIsGalois Pz P] at hr0
  exact (mul_eq_mul_iff_eq_and_eq_of_pos hr hi hr0 h0).mp h


-- @@ L892-894 verbatim
theorem ramificationIdx_of_DecompositionIdeal [IsGalois K L] :
  ramificationIdxOfIsGalois (DecompositionIdeal p P) L = ramificationIdxOfIsGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_DecompositionIdeal p P).1


-- @@ L896-898 verbatim
theorem inertiaDeg_of_DecompositionIdeal [IsGalois K L] :
  inertiaDegOfIsGalois (DecompositionIdeal p P) L = inertiaDegOfIsGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_DecompositionIdeal p P).2


-- @@ L900-912 verbatim
theorem ramificationIdx_of_DecompositionIdeal_over_bot_eq_one [IsGalois K L] :
    ramificationIdx' p (DecompositionIdeal p P) = 1 := by
  let Pz := IdealBelow (DecompositionField p P) P
  let E := { x // x ∈ DecompositionField p P }
  have h := ramificationIdx_algebra_tower_of_eq (map_isMaximal_ne_bot p E)
    (map_isMaximal_ne_bot Pz L)
    (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pz) (ne_bot_ofIsMaximal P) rfl
  rw [ramificationIdx_eq_ramificationIdxOfIsGalois Pz P,
    ramificationIdx_of_DecompositionIdeal p P,
    ← ramificationIdx_eq_ramificationIdxOfIsGalois p P] at h
  nth_rw 1 [← one_mul (ramificationIdx' p P)] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx'_ne_zero (map_isMaximal_ne_bot p L)
    inferInstance (map_le_of_le_comap (le_of_eq hp.liesOver_eq))) h.symm


-- @@ L914-927 verbatim
/-- The residue class field corresponding to `DecompositionField p P` is isomorphic to
residue class field corresponding to `p`. -/
theorem inertiaDeg_of_DecompositionIdeal_over_bot_eq_one [IsGalois K L] :
    (DecompositionIdeal p P).inertiaDeg (𝓞 K) = 1 := by
  have h := inertiaDeg_algebra_tower_of_eq (𝓞 K)
    (IdealBelow_def (DecompositionField p P) P)
  rw [inertiaDeg_eq_inertiaDegOfIsGalois (IdealBelow (DecompositionField p P) P) P,
    inertiaDeg_of_DecompositionIdeal p P, ← inertiaDeg_eq_inertiaDegOfIsGalois p P] at h
  nth_rw 1 [← one_mul (P.inertiaDeg (𝓞 K))] at h
  exact mul_right_cancel₀ (ne_of_gt (inertiaDeg_pos p P)) h.symm



-- Proposition 9.4


-- @@ L929-934 verbatim
/-- The residue class field of a number field is a finite field. -/
noncomputable instance residueFieldInstFintype : Fintype ((𝓞 K) ⧸ p) :=
  letI : Finite (ℤ ⧸ (comap (algebraMap ℤ (𝓞 K)) p)) := Finite.of_fintype _
  letI : Finite ((𝓞 K) ⧸ p) :=
    Module.finite_of_finite (R := ℤ ⧸ (comap (algebraMap ℤ (𝓞 K)) p))
  Fintype.ofFinite ((𝓞 K) ⧸ p)


-- @@ L936-938 verbatim
/-- The extension between residue class fields of number fields is a Galois extension. -/
instance extension_of_residue_fields_instIsGalois : IsGalois ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  inferInstance


-- @@ L940-952 verbatim
/-- The inertia group of `P` over `K` is the subgroup of `L ≃ₐ[K] L` that consists of all
the `σ : L ≃ₐ[K] L` that are identity modulo `P`. -/
def InertiaGroup (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) : Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : (𝓞 L), Ideal.Quotient.mk P (GalRingHom σ x) = Ideal.Quotient.mk P x }
  mul_mem' := by
    intro _ τ hs ht x
    rw [← ht x, ← hs (GalRingHom τ x)]
    rfl
  one_mem' _ := rfl
  inv_mem' := by
    intro σ hs x
    rw [← hs (GalRingHom σ⁻¹ x), GalRingHom_mul_inv_cancel_mem σ x]


-- @@ L954-962 verbatim
theorem InertiaGroup_le_DecompositionGroup : InertiaGroup K P ≤ DecompositionGroup p P := by
  refine fun σ hs ↦ (DecompositionGroup_mem p P σ).mpr <|
    le_antisymm (map_le_of_le_comap (fun x hx ↦ ?_)) (fun x hx ↦ ?_)
  · have h := add_mem (Ideal.Quotient.eq.mp (hs x)) hx
    simp_all
  · rw [← GalRingHom_mul_inv_cancel_mem σ x]
    have h := add_mem (Ideal.Quotient.eq.mp (((InertiaGroup K P).inv_mem hs) x)) hx
    rw [sub_add_cancel] at h
    exact mem_map_of_mem (GalRingHom σ) h





-- @@ L967-967 verbatim
open Module FiniteDimensional IntermediateField Polynomial


-- @@ L969-969 verbatim
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- @@ L970-971 expanded
variable (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
  [hp : ideal_unique_lies_over P p]


-- @@ L973-978 expanded
/-- If `P` is the unique ideal lying over `p`, then `P` remains invariant under the action
of `σ`. -/
theorem GalRingHom_map_eq_of_unique_lies_over {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsMaximal] [hp : ideal_unique_lies_over P p]
    (σ : L ≃ₐ[K] L) : map (GalRingHom σ) P = P :=
  hp.unique (map (GalRingHom σ) P)


-- @@ L980-986 verbatim
/-- If `P` is the unique ideal lying over `p`, then the action of each element `σ` in `L ≃ₐ[K] L`
on the residue class field is an an automorphism of `(𝓞 L) ⧸ P` fixing `(𝓞 K) ⧸ p`, inducing a
homomorphism from `L ≃ₐ[K] L` to the Galois group `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)`. -/
def ResidueGaloisHom : MonoidHom (L ≃ₐ[K] L) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) where
  toFun σ := residueFieldGalAlgEquiv p (GalRingHom_map_eq_of_unique_lies_over p P σ)
  map_one' := by ext ⟨⟩; rfl
  map_mul' _ _ := by ext ⟨⟩; rfl


-- @@ L988-992 verbatim
/-- A power basis of the residue field extension `((𝓞 L) ⧸ P) / ((𝓞 K) ⧸ p)`, obtained because
this extension is finite and separable. -/
noncomputable def powerBasisOfResidue : PowerBasis ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  letI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := IsGalois.to_isSeparable
  Field.powerBasisOfFiniteOfSeparable ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)


-- @@ L994-1063 verbatim
theorem ResidueGaloisHom_surjective [hn : Normal K L] :
    Function.Surjective (ResidueGaloisHom p P) := by
  let F := 𝓞 K ⧸ p
  let E := 𝓞 L ⧸ P
  let : Algebra E E := Algebra.id E
  intro σ
  have e : PowerBasis F E := powerBasisOfResidue p P
  let β := (PowerBasis.liftEquiv e).toFun σ.toAlgHom
  rcases Quotient.exists_rep e.gen with ⟨a, ha⟩
  let f : (𝓞 K)[X] := minpoly (𝓞 K) a
  let fl : (𝓞 L)[X] := f.map (algebraMap (𝓞 K) (𝓞 L))
  let ϕp : (𝓞 K) →+* F := Ideal.Quotient.mk p
  let ϕP : (𝓞 L) →+* E := Ideal.Quotient.mk P
  have h : Quotient.mk (Submodule.quotientRel P) a = ϕP a := rfl
  rw [h] at ha
  have hai : IsIntegral (𝓞 K) a := IsIntegral.isIntegral a
  have hm : f.Monic := minpoly.monic hai
  have h0 : (fl.map ϕP) ≠ 0 := map_monic_ne_zero (Monic.map (algebraMap (𝓞 K) (𝓞 L)) hm)
  have hbr : β.1 ∈ (fl.map ϕP).roots := by
    have h : aeval e.gen (f.map ϕp) = ϕP (aeval a f) := by
      rw [← ha]
      exact (@map_aeval_eq_aeval_map _ _ _ F E _ _ _ _ _ ϕp ϕP rfl f a).symm
    rw [minpoly.aeval, map_zero] at h
    apply (mem_roots_iff_aeval_eq_zero h0).mpr
    have hc : fl.map ϕP = (f.map ϕp).map (algebraMap F E) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    have hbz := aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd F e.gen h) β.2
    simp only [hc, aeval_map_algebraMap, ← hbz]
  have hfe : (Polynomial.map (algebraMap (𝓞 K) K) f) = minpoly K a.1 := by
    refine minpoly.eq_of_irreducible_of_monic
      ((Monic.irreducible_iff_irreducible_map_fraction_map (minpoly.monic hai)).mp
        (minpoly.irreducible hai)) ?_ (Monic.map (algebraMap (𝓞 K) K) (minpoly.monic hai))
    rw [show a.1 = algebraMap (𝓞 L) L a from rfl]
    simp only [aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, minpoly.aeval, f]
  have h : fl.roots.map ϕP = (fl.map ϕP).roots := by
    have h := (hn.splits a.1).natDegree_eq_card_roots.symm
    have hc : (algebraMap K L).comp (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) L := rfl
    have he := isIntegralClosure_root_card_eq_ofMonic (𝓞 L) L (minpoly.monic hai)
    rw [← hfe, natDegree_map, Monic.natDegree_map (minpoly.monic hai), Polynomial.map_map, hc, ← he,
      ← Monic.natDegree_map (minpoly.monic hai) (algebraMap (𝓞 K) (𝓞 L))] at h
    exact roots_map_of_card_eq_natDegree h0 h
  rw [← h] at hbr
  rcases Multiset.mem_map.mp hbr with ⟨b, ⟨hbr, hb⟩⟩
  have h : aeval b.1 (minpoly K (AdjoinSimple.gen K a.1)) = 0 := by
    have he : minpoly K (AdjoinSimple.gen K a.1) = minpoly K a.1 := by apply minpoly_eq
    have h : b.1 = algebraMap (𝓞 L) L b := rfl
    rw [he, ← hfe, h, aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, aeval_def, ← eval_map,
      ← coe_aeval_eq_eval, (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero hm)).mp hbr]
  let τ := ((IntermediateField.adjoin.powerBasis (hn.isIntegral a.1)).lift b.1
    h).fieldRangeToAlgEquiv.liftNormal L
  use τ
  apply AlgEquiv.coe_toAlgHom_injective
  apply e.algHom_ext
  change ((ResidueGaloisHom p P) τ) e.gen = σ e.gen
  simp only [← ha]
  calc _ = ϕP ((GalAlgEquiv τ) a) := rfl
    _ = β.1 := by
      rw [← hb]
      congr
      apply Subtype.val_inj.mp
      have ha : τ a.1 = τ (AdjoinSimple.gen K a.1).1 := rfl
      rw [← PowerBasis.lift_gen (IntermediateField.adjoin.powerBasis (hn.isIntegral a.1)) b.1 h,
        GalAlgEquiv_apply, ha, AlgEquiv.liftNormal_intermediateField_commutes]
      rfl
    _ = _ := congrArg σ ha.symm



-- Definition 9.5


-- @@ L1065-1065 verbatim
open IsGalois


-- @@ L1067-1083 expanded
/-- If `P` is the unique ideal lying over `p`, then the `InertiaGroup` is equal to the
kernel of the homomorphism `ResidueGaloisHom`. -/
theorem InertiaGroup_eq_ker {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K))
    (P : Ideal (𝓞 L)) [P.IsMaximal] [hp : ideal_unique_lies_over P p] :
    InertiaGroup K P = MonoidHom.ker (ResidueGaloisHom p P) :=
  by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  constructor
  · rintro h ⟨x⟩
    nth_rw 2 [Submodule.Quotient.quot_mk_eq_mk]
    rw [Quotient.mk_eq_mk, ← h x]
    rfl
  · intro h x
    have h := h (Ideal.Quotient.mk P x)
    rw [AlgEquiv.one_apply] at h
    rw [← h]
    rfl


-- @@ L1085-1090 expanded
/-- If `P` is the unique ideal lying over `p`, then the `InertiaGroup K P` is a normal subgroup. -/
theorem InertiaGroup_Normal {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K))
    (P : Ideal (𝓞 L)) [P.IsMaximal] [hp : ideal_unique_lies_over P p] :
    Subgroup.Normal (InertiaGroup K P) :=
  by
  rw [InertiaGroup_eq_ker p P]
  exact MonoidHom.normal_ker (ResidueGaloisHom p P)


-- @@ L1092-1099 verbatim
/-- The quotient of the Galois group by the inertia group is isomorphic to the Galois group of
the residue field extension. -/
noncomputable def autQuoutientInertiaGroupEquivResidueFieldAut [Normal K L] :
    @MulEquiv ((L ≃ₐ[K] L) ⧸ (InertiaGroup K P)) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))
    (letI := InertiaGroup_Normal p P; inferInstance) _ :=
  letI := InertiaGroup_Normal p P
  (QuotientGroup.quotientMulEquivOfEq (InertiaGroup_eq_ker p P)).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _ (ResidueGaloisHom_surjective p P)


-- @@ L1101-1104 verbatim
/-- The intermediate field fixed by `InertiaGroup K P`. -/
def InertiaField' (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) : IntermediateField K L :=
  fixedField (InertiaGroup K P)


-- @@ L1106-1108 verbatim
/-- `InertiaField' K P` is a Number Field. -/
instance InertiaField_NumberField : NumberField (InertiaField' K P) :=
  of_IntermediateField (InertiaField' K P)


-- @@ L1110-1113 verbatim
/-- The ideal equal to the intersection of `P` and `InertiaField' p P`. -/
abbrev InertiaIdeal' (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (P : Ideal (𝓞 L)) : Ideal (𝓞 (InertiaField' K P)) :=
  IdealBelow (InertiaField' K P) P


-- @@ L1115-1120 verbatim
/-- `InertiaIdeal' p P` is a maximal Ideal. -/
instance InertiaIdeal_IsMaxiaml : IsMaximal (InertiaIdeal' K P) := IdealBelow_IsMaximal P



-- Proposition 9.6


-- @@ L1122-1122 verbatim
variable [IsGalois K L]


-- @@ L1124-1129 expanded
/-- `(InertiaField' p P) / K` is a Galois extension. -/
theorem InertiaField_isGalois_of_unique {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsMaximal] [ideal_unique_lies_over P p] :
    IsGalois K (InertiaField' K P) :=
  letI := InertiaGroup_Normal p P
  of_fixedField_normal_subgroup (InertiaGroup K P)


-- @@ L1131-1137 verbatim
/-- The Galois group `Gal((InertiaField' p P) / K)` is isomorphic to the
Galois group `Gal((𝓞 L) ⧸ P) / (𝓞 K) ⧸ p)`. -/
noncomputable def InertiaFieldAutEquivResidueFieldAut :
    ((InertiaField' K P) ≃ₐ[K] (InertiaField' K P)) ≃* (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) :=
  letI := InertiaGroup_Normal p P
  (IsGalois.normalAutEquivQuotientSymm (InertiaGroup K P)).trans <|
    autQuoutientInertiaGroupEquivResidueFieldAut p P


-- @@ L1139-1141 verbatim
/-- The Galois group `Gal(L / (InertiaField' p P))` is isomorphic to `InertiaGroup K P`. -/
def InertiaFieldAutTowerTopEquivInertiaGroupOfUnique :
  (L ≃ₐ[InertiaField' K P] L) ≃* InertiaGroup K P := subgroupEquivAut (InertiaGroup K P)


-- @@ L1143-1149 expanded
/-- The extension degree `[L : K]` is equal to the product of the ramification index
and the inertia degree of `p` in `L`. -/
theorem finrank_eq_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 L)) [ideal_unique_lies_over P p] :
    finrank K L = ramificationIdxOfIsGalois p L * inertiaDegOfIsGalois p L :=
  by
  have h := (ramificationIdx_mul_inertiaDegOfIsGalois p L).symm
  rwa [unique_primesOver_card_eq_one p P, one_mul] at h


-- @@ L1151-1157 verbatim
/-- The extension degree `[InertiaField' p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_InertiaField_eq_inertiaDeg_of_unique :
    finrank K (InertiaField' K P) = inertiaDegOfIsGalois p L := by
  let := InertiaField_isGalois_of_unique p P
  rw [← inertiaDeg_eq_inertiaDegOfIsGalois p P, inertiaDeg_eq_of_isMaximal p P,
    ← card_aut_eq_finrank, Nat.card_congr (InertiaFieldAutEquivResidueFieldAut p P).toEquiv,
    card_aut_eq_finrank]


-- @@ L1159-1165 verbatim
/-- The extension degree `[L : InertiaField' p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_InertiaField_top_eq_ramificationIdx_of_unique :
    finrank (InertiaField' K P) L = ramificationIdxOfIsGalois p L := by
  apply mul_left_cancel₀ (a := finrank K (InertiaField' K P)) (ne_of_gt finrank_pos)
  rw [finrank_mul_finrank K (InertiaField' K P) L, finrank_eq_ramificationIdx_mul_inertiaDeg p P,
    finrank_bot_InertiaField_eq_inertiaDeg_of_unique p P, mul_comm]


-- @@ L1167-1172 verbatim
open Classical in
theorem InertiaGroup_card_eq_ramificationIdx_of_unique :
    Fintype.card (InertiaGroup K P) = ramificationIdxOfIsGalois p L := by
  rw [← Nat.card_eq_fintype_card, ← finrank_fixedField_eq_card,
    ← finrank_InertiaField_top_eq_ramificationIdx_of_unique p P]
  rfl


-- @@ L1174-1180 verbatim
theorem InertiaGroup_InertiaIdeal_top (K : Type*) {L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (P : Ideal (𝓞 L)) :
    InertiaGroup (InertiaField' K P) P = ⊤ := by
  refine (Subgroup.eq_top_iff' (InertiaGroup (InertiaField' K P) P)).mpr (fun σ x ↦ ?_)
  let τ := (subgroupEquivAut (InertiaGroup K P)).toFun σ
  have hst : (GalRingHom σ) x = (GalRingHom τ.1) x := rfl
  rw [hst, τ.2 x]


-- @@ L1182-1194 expanded
open Classical in
theorem inertiaDeg_over_InertiaIdeal_eq_one_of_unique (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
    [P.IsMaximal] [ideal_unique_lies_over P p] : inertiaDegOfIsGalois (InertiaIdeal' K P) L = 1 :=
  by
  let := ideal_unique_lies_over_tower_top p (InertiaIdeal' K P) P
  let := InertiaGroup_Normal (InertiaIdeal' K P) P
  rw [← inertiaDeg_eq_inertiaDegOfIsGalois (InertiaIdeal' K P) P,
    inertiaDeg_eq_of_isMaximal (InertiaIdeal' K P) P, ← card_aut_eq_finrank, ←
    Nat.card_congr <|
      MulEquiv.toEquiv <| autQuoutientInertiaGroupEquivResidueFieldAut (InertiaIdeal' K P) P,
    InertiaGroup_InertiaIdeal_top K P]
  let := QuotientGroup.subsingleton_quotient_top (G := L ≃ₐ[InertiaField' K P] L)
  exact Nat.card_unique


-- @@ L1196-1201 verbatim
theorem ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique :
    ramificationIdxOfIsGalois (InertiaIdeal' K P) L = ramificationIdxOfIsGalois p L := by
  let := ideal_unique_lies_over_tower_top p (InertiaIdeal' K P) P
  rw [← finrank_InertiaField_top_eq_ramificationIdx_of_unique p P,
    finrank_eq_ramificationIdx_mul_inertiaDeg (InertiaIdeal' K P) P,
    inertiaDeg_over_InertiaIdeal_eq_one_of_unique p P, mul_one]


-- @@ L1203-1217 verbatim
theorem ramificationIdx_below_InertiaIdeal_eq_one_of_unique :
    ramificationIdxOfIsGalois p (InertiaField' K P) = 1 := by
  let Pt := IdealBelow (InertiaField' K P) P
  let E := { x // x ∈ InertiaField' K P }
  let := InertiaField_isGalois_of_unique p P
  have h := ramificationIdx_algebra_tower_of_eq (map_isMaximal_ne_bot p E)
    (map_isMaximal_ne_bot Pt L)
    (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pt) (ne_bot_ofIsMaximal P) rfl
  nth_rw 1 [ramificationIdx_eq_ramificationIdxOfIsGalois Pt P,
    ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique p P,
    ← ramificationIdx_eq_ramificationIdxOfIsGalois p P,
    ← one_mul (ramificationIdx' p P),
    ramificationIdx_eq_ramificationIdxOfIsGalois p Pt] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx'_ne_zero (map_isMaximal_ne_bot p L)
    (IsMaximal.isPrime inferInstance) (map_le_of_le_comap (le_of_eq hp.liesOver_eq))) h.symm


-- @@ L1219-1235 verbatim
theorem InertiaDeg_below_InertiaIdeal_eq_inertiaDeg_of_unique :
    inertiaDegOfIsGalois p (InertiaField' K P) = inertiaDegOfIsGalois p L := by
  let := InertiaField_isGalois_of_unique p P
  have h := inertiaDeg_algebra_tower_of_eq (𝓞 K) (IdealBelow_def (InertiaField' K P) P)
  nth_rw 1 [inertiaDeg_eq_inertiaDegOfIsGalois (InertiaIdeal' K P) P,
    inertiaDeg_over_InertiaIdeal_eq_one_of_unique p P, mul_one] at h
  rw [inertiaDeg_eq_inertiaDegOfIsGalois p P,
    inertiaDeg_eq_inertiaDegOfIsGalois p (IdealBelow (InertiaField' K P) P)] at h
  exact h.symm





/- TODO : The genral version of `InertiaFieldAutEquivResidueFieldAut`, i.e.,
`((InertiaField p P) ≃ₐ[DecompositionField p P] (InertiaField p P))` is isomorphic to
`(((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))`. -/


-- @@ L1237-1237 verbatim
open IntermediateField Module FiniteDimensional


-- @@ L1239-1239 verbatim
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- @@ L1240-1241 expanded
variable (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [ideal_lies_over P p]


-- @@ L1243-1251 verbatim
theorem InertiaGroup_eq :
    Subgroup.map (subgroupEquivAut (DecompositionGroup p P)).symm.toMonoidHom
    ((InertiaGroup K P).subgroupOf (DecompositionGroup p P)) =
    InertiaGroup (DecompositionField p P) P := by
  ext σ
  rw [Subgroup.mem_map]
  refine ⟨fun ⟨τ, ht, he⟩ x ↦ by rw [← he, ← Subgroup.mem_subgroupOf.mp ht x]; rfl, fun hs ↦ ?_⟩
  refine ⟨(subgroupEquivAut (DecompositionGroup p P)).toFun σ, fun x ↦ by rw [← hs x]; rfl, ?_⟩
  simp_all


-- @@ L1253-1259 verbatim
/-- The inertia group of `P` over the decomposition field is isomorphic to the inertia group
of `P` over `K`. -/
def InertiaGroupEquiv : InertiaGroup (DecompositionField p P) P ≃* InertiaGroup K P := by
  rw [← InertiaGroup_eq p P]
  exact ((subgroupEquivAut (DecompositionGroup p P)).symm.subgroupMap
    ((InertiaGroup K P).subgroupOf (DecompositionGroup p P))).symm.trans <|
      Subgroup.subgroupOfEquivOfLe (InertiaGroup_le_DecompositionGroup p P)


-- @@ L1261-1264 verbatim
/-- The intertia field of `P` over `K` is the intermediate field of `L / DecompositionField p P`
fixed by the inertia group pf `P` over `K`. -/
def InertiaField : IntermediateField (DecompositionField p P) L :=
  fixedField (InertiaGroup (DecompositionField p P) P)


-- @@ L1266-1267 verbatim
/-- The ideal equal to the intersection of `P` and `InertiaField p P`. -/
abbrev InertiaIdeal : Ideal (𝓞 (InertiaField p P)) := IdealBelow (InertiaField p P) P


-- @@ L1269-1272 verbatim
/-- `(InertiaField p P) / (DecompositionField p P)` is a Galois extension. -/
instance InertiaField_isGalois [IsGalois K L] :
    IsGalois (DecompositionField p P) (InertiaField p P) :=
  InertiaField_isGalois_of_unique (DecompositionIdeal p P) P


-- @@ L1274-1277 verbatim
/-- The Galois group `Gal(L / (InertiaField p P))` is isomorphic to `InertiaGroup K P`. -/
def InertiaFieldAutTowerTopEquivInertiaGroup :
    (L ≃ₐ[InertiaField p P] L) ≃* InertiaGroup K P :=
  (subgroupEquivAut (InertiaGroup (DecompositionField p P) P)).trans (InertiaGroupEquiv p P)


-- @@ L1279-1283 verbatim
/-- The extension degree `[InertiaField p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_InertiaField_eq_inertiaDeg [IsGalois K L] :
    finrank (DecompositionField p P) (InertiaField p P) = inertiaDegOfIsGalois p L := by
  rw [← inertiaDeg_of_DecompositionIdeal p P]
  exact finrank_bot_InertiaField_eq_inertiaDeg_of_unique (DecompositionIdeal p P) P


-- @@ L1285-1290 verbatim
/-- The extension degree `[L : InertiaField p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_InertiaField_top_eq_ramificationIdx [IsGalois K L] :
    finrank (InertiaField p P) L = ramificationIdxOfIsGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P]
  exact finrank_InertiaField_top_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P


-- @@ L1292-1297 verbatim
open Classical in
theorem InertiaGroup_card_eq_ramificationIdx [IsGalois K L] :
    Fintype.card (InertiaGroup K P) = ramificationIdxOfIsGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P,
    Fintype.card_of_bijective (InertiaGroupEquiv p P).symm.bijective,
    InertiaGroup_card_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P]


-- @@ L1299-1301 verbatim
theorem inertiaDeg_over_InertiaIdeal_eq_one [IsGalois K L] :
    inertiaDegOfIsGalois (InertiaIdeal p P) L = 1 :=
  inertiaDeg_over_InertiaIdeal_eq_one_of_unique (DecompositionIdeal p P) P


-- @@ L1303-1306 verbatim
theorem ramificationIdx_over_InertiaIdeal_eq_ramificationIdx [IsGalois K L] :
    ramificationIdxOfIsGalois (InertiaIdeal p P) L = ramificationIdxOfIsGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P]
  exact ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P


-- @@ L1308-1310 verbatim
theorem ramificationIdx_below_InertiaIdeal_eq_one [IsGalois K L] :
    ramificationIdxOfIsGalois (DecompositionIdeal p P) (InertiaField p P) = 1 :=
  ramificationIdx_below_InertiaIdeal_eq_one_of_unique (DecompositionIdeal p P) P


-- @@ L1312-1316 verbatim
theorem InertiaDeg_below_InertiaIdeal_eq_inertiaDeg [IsGalois K L] :
    inertiaDegOfIsGalois (DecompositionIdeal p P) (InertiaField p P) =
    inertiaDegOfIsGalois p L := by
  rw [← inertiaDeg_of_DecompositionIdeal p P]
  exact InertiaDeg_below_InertiaIdeal_eq_inertiaDeg_of_unique (DecompositionIdeal p P) P




-- @@ L1320-1320 verbatim
end NumberField
