/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, contributors
-/
module

public import LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Equiv
public import LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.FieldTheory.Galois.Basic
import LeanPool.BrauerGroupNew.Mathlib.Data.DFinsupp.Submonoid
import LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs
import LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Kernel
import LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice
import LeanPool.BrauerGroupNew.TwoSidedIdeal
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


-- @@ L22-31 verbatim
/-!
# Cross product algebra

This file constructs the cross product algebra associated to a 2-cocycle of a field extension
`K / F` and shows that it is a central simple `F`-algebra of dimension `dim(K / F) ^ 2`.

## References

* [*Advanced Algebra*]
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
open groupCohomology Function Module


-- @@ L37-37 verbatim
suppress_compilation


-- @@ L39-39 expanded
variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : ((K ≃ₐ[F] K) × K ≃ₐ[F] K) → Kˣ}


-- @@ L41-45 expanded
/-- The cross product algebra attached to a multiplicative two-cocycle on `Gal(K, F)`. -/
@[ext]
structure CrossProductAlgebra (f : ((K ≃ₐ[F] K) × K ≃ₐ[F] K) → Kˣ) where
  /-- The finitely supported coefficient function on the Galois group. -/
  val : (K ≃ₐ[F] K) →₀ K


-- @@ L47-47 verbatim
namespace CrossProductAlgebra


-- @@ L49-49 verbatim
variable {x y : CrossProductAlgebra f}


-- @@ L51-51 verbatim
lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProductAlgebra.ext


-- @@ L53-53 verbatim
lemma val_surjective : Surjective (val (f := f)) := fun x ↦ ⟨⟨x⟩, rfl⟩


-- @@ L55-55 verbatim
lemma val_bijective : Bijective (val (f := f)) := ⟨val_injective, val_surjective⟩


-- @@ L57-57 verbatim
@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff


-- @@ L59-60 verbatim
lemma «forall» {P : CrossProductAlgebra f → Prop} : (∀ x, P x) ↔ ∀ x, P (mk x) := by
  rw [val_surjective.forall]


-- @@ L62-62 verbatim
instance : Nontrivial (CrossProductAlgebra f) := val_surjective.nontrivial


-- @@ L64-65 verbatim
instance : Zero (CrossProductAlgebra f) where
  zero := ⟨0⟩


-- @@ L67-68 verbatim
instance : Add (CrossProductAlgebra f) where
  add x y := ⟨x.val + y.val⟩


-- @@ L70-71 verbatim
instance : Neg (CrossProductAlgebra f) where
  neg x := ⟨-x.val⟩


-- @@ L73-74 verbatim
instance : Sub (CrossProductAlgebra f) where
  sub x y := ⟨x.val - y.val⟩


-- @@ L76-77 verbatim
instance [Semiring R] [Module R K] : SMul R (CrossProductAlgebra f) where
  smul r x := ⟨r • x.val⟩


-- @@ L79-79 verbatim
@[simp] lemma val_zero : (0 : CrossProductAlgebra f).val = 0 := rfl


-- @@ L81-81 verbatim
@[simp] lemma val_add (x y : CrossProductAlgebra f) : (x + y).val = x.val + y.val := rfl


-- @@ L83-84 verbatim
@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProductAlgebra f) :
    (r • x).val = r • x.val := rfl


-- @@ L86-86 verbatim
@[simp] lemma val_neg (x : CrossProductAlgebra f) : (-x).val = -x.val := rfl


-- @@ L88-88 verbatim
@[simp] lemma val_sub (x y : CrossProductAlgebra f) : (x - y).val = x.val - y.val := rfl


-- @@ L90-90 verbatim
@[simp] lemma mk_zero : (mk 0 : CrossProductAlgebra f) = 0 := rfl


-- @@ L92-93 expanded
@[simp]
lemma mk_add_mk (x y : (K ≃ₐ[F] K) →₀ K) : (mk x + mk y : CrossProductAlgebra f) = mk (x + y) :=
  rfl


-- @@ L95-96 expanded
@[simp]
lemma smul_mk [Semiring R] [Module R K] (r : R) (x : (K ≃ₐ[F] K) →₀ K) :
    (r • mk x : CrossProductAlgebra f) = mk (r • x) :=
  rfl


-- @@ L98-98 expanded
@[simp]
lemma neg_mk (x : (K ≃ₐ[F] K) →₀ K) : (-mk x : CrossProductAlgebra f) = mk (-x) :=
  rfl


-- @@ L100-101 expanded
@[simp]
lemma mk_sub_mk (x y : (K ≃ₐ[F] K) →₀ K) : (mk x - mk y : CrossProductAlgebra f) = mk (x - y) :=
  rfl


-- @@ L103-104 verbatim
instance addCommGroup : AddCommGroup (CrossProductAlgebra f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)


-- @@ L106-113 expanded
/-- The additive equivalence with finitely supported functions on the Galois group. -/
@[simps]
def valAddEquiv : CrossProductAlgebra f ≃+ ((K ≃ₐ[F] K) →₀ K)
    where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add


-- @@ L115-119 verbatim
@[simp]
lemma val_finsuppSum {α M : Type*} [AddCommMonoid M] (g : α →₀ M)
    (h : α → M → CrossProductAlgebra f) :
    (g.sum h).val = g.sum (fun a m ↦ (h a m).val) :=
  map_finsuppSum (valAddEquiv (f := f)).toAddMonoidHom g h


-- @@ L121-122 verbatim
instance [Semiring R] [Module R K] : Module R (CrossProductAlgebra f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul


-- @@ L124-126 verbatim
instance [Semiring R] [Semiring S] [Module R K] [Module S K] [Module R S] [IsScalarTower R S K] :
    IsScalarTower R S (CrossProductAlgebra f) where
  smul_assoc r s x := by ext; simp [smul_assoc]


-- @@ L128-133 expanded
/-- The linear equivalence with finitely supported functions on the Galois group. -/
@[simps]
def valLinearEquiv [Semiring R] [Module R K] : CrossProductAlgebra f ≃ₗ[R] ((K ≃ₐ[F] K) →₀ K)
    where
  __ := valAddEquiv
  map_smul' := val_smul


-- @@ L135-138 expanded
/-- The standard basis of the cross product algebra over `K`. -/
@[simps]
def basis : Basis (K ≃ₐ[F] K) K (CrossProductAlgebra f) where repr := valLinearEquiv


-- @@ L140-140 expanded
lemma basis_val (σ : K ≃ₐ[F] K) : (basis (f := f) σ).val = .single σ 1 :=
  rfl


-- @@ L142-142 expanded
lemma mk_single_one (σ : K ≃ₐ[F] K) : mk (.single σ 1) = basis (f := f) σ :=
  rfl


-- @@ L144-154 expanded
variable (f) in
/-- The bilinear multiplication map on the underlying finitely supported functions. -/
def mulLinearMap : ((K ≃ₐ[F] K) →₀ K) →ₗ[F] ((K ≃ₐ[F] K) →₀ K) →ₗ[F] ((K ≃ₐ[F] K) →₀ K) :=
  Finsupp.lsum F fun σ =>
    { toFun
        c :=
        Finsupp.lsum F fun τ =>
          { toFun d := .single (σ * τ) (c * σ d * f (σ, τ))
            map_add' := by simp [mul_add, add_mul]
            map_smul' := by
              simp only [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply,
                Finsupp.smul_single, implies_true] }
      map_add' _ _ := by ext; simp [add_mul]
      map_smul' _ _ := by ext; simp_all }


-- @@ L156-160 expanded
variable (f) in
@[simp]
lemma mulLinearMap_single_single (c d : K) (σ τ : K ≃ₐ[F] K) :
    mulLinearMap f (.single σ c) (.single τ d) = .single (σ * τ) (c * σ d * f (σ, τ)) := by
  simp only [mulLinearMap, Finsupp.lsum_single, LinearMap.coe_mk, AddHom.coe_mk]


-- @@ L162-169 expanded
variable (f) in
@[simp]
lemma mulLinearMap_single_left_apply (c : K) (σ : K ≃ₐ[F] K) (x : (K ≃ₐ[F] K) →₀ K)
    (τ : K ≃ₐ[F] K) : mulLinearMap f (.single σ c) x τ = c * σ (x (σ⁻¹ * τ)) * f (σ, σ⁻¹ * τ) := by
  classical
  rw [mulLinearMap, Finsupp.lsum_single]
  simp +contextual [Finsupp.single_apply, ← eq_inv_mul_iff_mul_eq]


-- @@ L171-176 expanded
variable (f) in
@[simp]
lemma mulLinearMap_single_right_apply (c : K) (σ : K ≃ₐ[F] K) (x : (K ≃ₐ[F] K) →₀ K)
    (τ : K ≃ₐ[F] K) : mulLinearMap f x (.single σ c) τ = x (τ * σ⁻¹) * τ (σ⁻¹ c) * f (τ * σ⁻¹, σ) :=
  by classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_mul_inv_iff_mul_eq]


-- @@ L178-179 verbatim
instance : One (CrossProductAlgebra f) where
  one := ⟨.single 1 (f (1, 1))⁻¹⟩


-- @@ L181-182 verbatim
instance : Mul (CrossProductAlgebra f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩


-- @@ L184-184 verbatim
lemma one_def : (1 : CrossProductAlgebra f) = ⟨.single 1 (f (1, 1))⁻¹⟩ := rfl


-- @@ L186-186 verbatim
@[simp] lemma val_one : (1 : CrossProductAlgebra f).val = .single 1 (f (1, 1))⁻¹ := rfl


-- @@ L188-189 verbatim
@[simp]
lemma val_mul (x y : CrossProductAlgebra f) : (x * y).val = mulLinearMap f x.val y.val := rfl


-- @@ L191-192 expanded
@[simp]
lemma mk_mul_mk (x y : (K ≃ₐ[F] K) →₀ K) :
    (mk x * mk y : CrossProductAlgebra f) = mk (mulLinearMap f x y) :=
  rfl


-- @@ L194-194 verbatim
variable [Fact <| IsMulCocycle₂ f]


-- @@ L196-224 verbatim
instance monoid : Monoid (CrossProductAlgebra f) where
  one_mul := by
    intro x
    ext σ
    simp [map_one_fst_of_isMulCocycle₂ Fact.out σ, mul_right_comm]
  mul_one := by
    intro x
    ext σ
    simp [map_one_snd_of_isMulCocycle₂ Fact.out σ]
  mul_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single τ b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add => simp [-mulLinearMap_single_single, *]
    | single ν c =>
    simp only [mulLinearMap_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul,
      mul_left_comm _ (σ (τ c))]
    congr 4
    simpa [mul_comm] using congr(($((Fact.out : IsMulCocycle₂ f) σ τ ν)).val)


-- @@ L226-234 verbatim
instance : Ring (CrossProductAlgebra f) where
  __ := addCommGroup
  __ := monoid
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp


-- @@ L236-238 verbatim
instance algebra [CommSemiring R] [Algebra R F] [Module R K] [IsScalarTower R F K] :
    Algebra R (CrossProductAlgebra f) := by
  refine .ofModule ?_ ?_ <;> intros <;> ext <;> simp


-- @@ L240-245 verbatim
lemma algebraMap_val [CommSemiring R] [Algebra R F] [Algebra R K] [IsScalarTower R F K] (r : R) :
    (algebraMap R (CrossProductAlgebra f) r).val =
      .single 1 (algebraMap R K r * (f (1, 1))⁻¹) := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [val_smul, val_one, Finsupp.smul_single, Units.val_inv_eq_inv_val,
    ← Algebra.smul_def]


-- @@ L247-259 expanded
omit [Fact <| IsMulCocycle₂ f] in
lemma basis_smul_comm (σ : K ≃ₐ[F] K) (k1 k2 : K) (x : CrossProductAlgebra f) :
    (k1 • basis (f := f) σ) * (k2 • x) = σ k2 • k1 • basis σ * x :=
  by
  apply val_injective
  simp only [basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, val_mul, val_smul, valAddEquiv_symm_apply_val,
    Finsupp.smul_single, smul_eq_mul, _root_.mul_one]
  induction x.val using Finsupp.induction_linear with
  | zero => simp
  | add _ _ _ _ => simp_all [smul_add]
  | single a b =>
    simp only [Finsupp.smul_single, smul_eq_mul, mulLinearMap_single_single, map_mul, ← mul_assoc,
      mul_comm k1 (σ k2)]


-- @@ L261-277 verbatim
variable (f) in
/-- The inclusion from `K` into `CrossProductAlgebra f`.

Note that this does *not* make `CrossProductAlgebra f` into a `K`-algebra, because that would
require `incl k * x = x * incl k`. -/
@[simps -isSimp]
def incl : K →ₐ[F] CrossProductAlgebra f where
  toFun k := k • 1
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by
    ext
    simp only [val_smul, val_one, Finsupp.smul_single, smul_eq_mul, mul_assoc, val_mul,
      mulLinearMap_single_single, mul_one, AlgEquiv.one_apply, mul_left_comm]
    simp
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]


-- @@ L279-281 verbatim
lemma smul_eq_incl_mul (k : K) (x : CrossProductAlgebra f) : k • x = incl f k * x := by
  ext σ
  simp [incl_apply, map_one_fst_of_isMulCocycle₂ Fact.out σ, mul_right_comm]


-- @@ L283-286 verbatim
instance [CommSemiring R] [Algebra R K] :
    IsScalarTower R (CrossProductAlgebra f) (CrossProductAlgebra f) where
  smul_assoc r x y := by
    simp only [← algebraMap_smul K r, smul_eq_mul, smul_eq_incl_mul, mul_assoc]


-- @@ L288-308 expanded
variable (f) in
/-- The canonical unit associated to an element of the Galois group. -/
@[simps]
def of (σ : K ≃ₐ[F] K) : (CrossProductAlgebra f)ˣ
    where
  val.val := .single σ 1
  inv.val := .single σ⁻¹ <| (f (σ⁻¹, σ))⁻¹ * (f (1, 1))⁻¹
  val_inv := by
    ext : 1
    simp only [Units.val_inv_eq_inv_val, mk_mul_mk, mulLinearMap_single_single, mul_inv_cancel,
      map_mul, map_inv₀, one_mul, val_one]
    congr 1
    rw [← mul_inv, ← div_eq_inv_mul, ← one_div (f (1, 1) : K)]
    apply (div_eq_div_iff (by simp) (Units.ne_zero _)).2
    simpa [map_one_fst_of_isMulCocycle₂ Fact.out σ, map_one_snd_of_isMulCocycle₂ Fact.out σ,
      mul_comm] using congr(($((Fact.out : IsMulCocycle₂ f) σ σ⁻¹ σ)).val)
  inv_val := by
    ext : 1
    simp only [Units.val_inv_eq_inv_val, mk_mul_mk, mulLinearMap_single_single, inv_mul_cancel,
      map_one, mul_right_comm _ (f _ : K)⁻¹, mul_one, ne_eq, Units.ne_zero, not_false_eq_true,
      inv_mul_cancel₀, one_mul, val_one]


-- @@ L310-310 expanded
lemma basis_eq_of (σ : K ≃ₐ[F] K) : basis σ = (of f σ).val :=
  rfl


-- @@ L312-313 verbatim
variable (f) in
@[simp] lemma of_one : of f 1 = incl f (f (1, 1)) := by ext; simp [incl_apply]


-- @@ L315-319 expanded
variable (f) in
@[simp]
lemma of_mul_of (σ τ : K ≃ₐ[F] K) : of f σ * of f τ = incl f (f (σ, τ)) * of f (σ * τ) :=
  by
  ext
  simp [incl_apply]


-- @@ L321-323 expanded
@[simp]
lemma basis_mul_basis (σ τ : K ≃ₐ[F] K) :
    basis (f := f) σ * basis τ = incl f (f (σ, τ)) * basis (σ * τ) :=
  of_mul_of ..


-- @@ L325-331 expanded
lemma of_mul_incl (σ : K ≃ₐ[F] K) (c : K) : of f σ * incl f c = incl f (σ c) * of f σ :=
  by
  ext : 1
  simp only [incl_apply, val_mul, val_of_val, val_smul, val_one, Finsupp.smul_single, smul_eq_mul,
    mulLinearMap_single_single, mul_one, map_mul, map_inv₀, one_mul,
    map_one_snd_of_isMulCocycle₂ Fact.out σ, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, ne_eq, EmbeddingLike.map_eq_zero_iff, Units.ne_zero, not_false_eq_true,
    inv_mul_cancel_right₀, smul_one_mul]


-- @@ L333-335 verbatim
lemma sum_of (x : CrossProductAlgebra f) : x.val.sum (fun σ c ↦ c • (of f σ).val) = x := by
  ext
  simp


-- @@ L337-338 expanded
lemma of_conj (σ : K ≃ₐ[F] K) (k : K) : of f σ * incl f k * (of f σ)⁻¹ = incl f (σ k) := by
  simp [of_mul_incl]


-- @@ L340-340 verbatim
variable [Module.Finite F K] [IsGalois F K]


-- @@ L342-342 verbatim
/-! ### Finite dimensionality -/


-- @@ L344-346 verbatim
@[simp] lemma dim_eq_sq : Module.finrank F (CrossProductAlgebra f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, sq]


-- @@ L348-349 verbatim
instance : Module.Finite F (CrossProductAlgebra f) :=
  Module.finite_of_finrank_pos <| by simp [pow_pos_iff two_ne_zero, Module.finrank_pos]


-- @@ L351-351 verbatim
/-! ### Centrality -/


-- @@ L353-386 expanded
instance : Algebra.IsCentral F (CrossProductAlgebra f) := by
  classical
  constructor
    -- Assume `c` is central.
    
  rintro c hc
  rw [Subalgebra.mem_center_iff] at hc
  have key (d : K) (σ τ : K ≃ₐ[F] K) :
    d * τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * σ d * f (σ, τ) := by
    simpa [incl_apply, mul_assoc] using
      congr(($(hc <| incl f d * (of f τ).val)).val (σ * τ))
        -- By substituting `d = 1` in the previous equality,
          -- we get `τ(c_{τ⁻¹στ}) f(τ, τ⁻¹στ) = c_σ f(σ, τ)`.
        
  have key₁ (σ τ : K ≃ₐ[F] K) : τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * f (σ, τ) :=
    by simpa using key 1 σ τ
  have key₁₁ (τ : K ≃ₐ[F] K) : τ (c.val 1 * f (1, 1)) = c.val 1 * f (1, 1) := by
    simpa [map_one_fst_of_isMulCocycle₂ Fact.out τ, map_one_snd_of_isMulCocycle₂ Fact.out τ] using
      key₁ 1 τ
  rw [← IsGalois.mem_bot_iff_fixed] at key₁₁
  have hc₁ {σ} (hσ : c.val σ ≠ 0) : σ = 1 := by
    ext d
    simpa [mul_assoc d, mul_assoc (σ d), mul_comm (c.val _), key₁, hσ] using (key d σ default).symm
  rw [← c.sum_of]
  obtain ⟨a, ha⟩ := key₁₁
  refine finsuppSum_mem fun σ hσ ↦ ?_
  simpa [incl_apply, hc₁ hσ, of_one, ← mul_smul, ← ha, Algebra.ofId] using
    Subalgebra.smul_mem _ (one_mem _) _


-- @@ L388-388 verbatim
/-! ### Simplicity -/


-- @@ L390-390 verbatim
variable {I : TwoSidedIdeal (CrossProductAlgebra f)}


-- @@ L392-455 expanded
variable (I) in
/-- The standard basis for `CrossProductAlgebra f` descends to a basis for any of its non-trivial
quotients. -/
private def quotientBasis (hI : I ≠ ⊤) : Basis (K ≃ₐ[F] K) K I.ringCon.Quotient := by
  -- Let `ϕ` be the quotient map.
  
  let ϕ := I.ringCon.mkL K
  refine .mk (v := ϕ ∘ basis) ?_ ?_
  swap
  · rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top_of_surjective]
    exact Quotient.mk_surjective
  classical
    -- We show that `ϕ(x_τ)` is linearly independent over `τ ∈ J` for any finset `J`.
    
  rw [linearIndependent_iff_linearIndepOn_finset]
  rintro J
  induction J using Finset.cons_induction with
    -- The case `J = ∅` is trivial.
    
  | empty =>
    simp
      -- Let's deal with the `J ∪ {σ}` case.
      
  | cons σ J hσ ih =>
    -- Assume that there is some `a : Gal(K, F) → K` such that `∑ τ ∈ J, a_τ • ϕ(x_τ) = ϕ(x_σ)`.
      -- We want to prove `∀ τ ∈ J, a_τ = 0`.
    
    rw [Finset.coe_cons, linearIndepOn_insert <| Finset.mem_coe.not.2 hσ,
      Submodule.mem_span_image_finset_iff_exists_fun']
    simp only [ih, comp_apply, not_exists, true_and, basis_eq_of]
    rintro a ha
    have key (c : K) : ∀ τ ∈ J, a τ * τ c = σ c * a τ :=
      by
      refine linearIndepOn_finset_iffₛ.1 ih _ _ ?_
      have ϕ_map_mul (x y) : ϕ (x * y) = ϕ x * ϕ y := rfl
      have aux τ : ϕ (of f τ) * ϕ (incl f c) = ϕ (incl f (τ c)) * ϕ (of f τ) :=
        congr(ϕ $(of_mul_incl (f := f) τ c))
      have aux' (d : K) (x : I.ringCon.Quotient) : d • x = ϕ (incl f d) * x :=
        by
        induction x using Quotient.ind
        change ⟦_⟧ = ⟦_⟧
        simp [smul_eq_incl_mul]
      calc
        ∑ τ ∈ J, (a τ * τ c) • ϕ (of f τ)
        _ = ∑ τ ∈ J, ϕ (incl f <| a τ) * (ϕ (incl f <| τ c) * ϕ (of f τ)) := by
          simp [mul_assoc, aux', ϕ_map_mul]
        _ = ∑ τ ∈ J, ϕ (incl f <| a τ) * (ϕ (of f τ) * ϕ (incl f c)) := by simp [aux]
        _ = ∑ τ ∈ J, ϕ (incl f <| σ c) * ϕ (incl f <| a τ) * ϕ (of f τ) := by
          calc
            ∑ τ ∈ J, ϕ (incl f <| a τ) * (ϕ (of f τ) * ϕ (incl f c)) =
                (∑ τ ∈ J, a τ • ϕ (of f τ)) * ϕ (incl f c) :=
              by
              rw [Finset.sum_mul]
              simp [mul_assoc, aux']
            _ = ϕ (of f σ) * ϕ (incl f c) := (congrArg (fun z ↦ z * ϕ (incl f c)) ha)
            _ = ϕ (incl f (σ c)) * ϕ (of f σ) := (aux σ)
            _ = ϕ (incl f (σ c)) * ∑ τ ∈ J, a τ • ϕ (of f τ) :=
              (congrArg (fun z ↦ ϕ (incl f (σ c)) * z) ha).symm
            _ = ∑ τ ∈ J, ϕ (incl f <| σ c) * ϕ (incl f <| a τ) * ϕ (of f τ) :=
              by
              rw [Finset.mul_sum]
              simp [mul_assoc, aux']
        _ = ∑ τ ∈ J, (σ c * a τ) • ϕ (of f τ) := by simp [mul_assoc, aux', ϕ_map_mul]
    have : Nontrivial I.ringCon.Quotient := by simpa
    have aux τ : ϕ (of f τ) ≠ 0 := ((of f τ).isUnit.map I.ringCon.mk').ne_zero
    obtain ⟨τ, hτ, haτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero <| ha.trans_ne <| aux _
    apply left_ne_zero_of_smul at haτ
    exact
      ne_of_mem_of_not_mem hτ hσ <| by simpa [DFunLike.ext_iff, mul_comm, haτ] using (key · τ hτ)


-- @@ L457-460 verbatim
variable (I) in
/-- `CrossProductAlgebra f` is isomorphic to any of its non-trivial quotients. -/
private def equivQuotient (hI : I ≠ ⊤) : CrossProductAlgebra f ≃ₗ[K] I.ringCon.Quotient :=
  basis.repr ≪≫ₗ (quotientBasis I hI).repr.symm


-- @@ L462-470 verbatim
omit [Module.Finite F K] [IsGalois F K] in
variable (I) in
/-- `CrossProductAlgebra f` is isomorphic to any of its non-trivial quotients along the quotient
map. -/
private lemma coe_equivQuotient (hI) : (equivQuotient I hI).toLinearMap = I.ringCon.mkL K := by
  refine basis.ext fun σ ↦ ?_
  change (quotientBasis I hI).repr.symm (basis.repr (basis σ)) = _
  rw [Basis.repr_self, Basis.repr_symm_single_one]
  simp only [quotientBasis, Basis.coe_mk, comp_apply]


-- @@ L472-476 verbatim
instance : IsSimpleRing (CrossProductAlgebra f) := by
  refine ⟨⟨fun I ↦ Classical.or_iff_not_imp_right.2 fun hI ↦ ?_⟩⟩
  rw [← I.ker_ringCon_mk', ← TwoSidedIdeal.injective_iff_ker_eq_bot]
  convert (equivQuotient I hI).injective
  exact congr(⇑$((coe_equivQuotient I hI).symm))


-- @@ L478-478 verbatim
/-! ### The cross product algebra as a central simple algebra -/


-- @@ L480-482 verbatim
variable (f) in
/-- The cross product algebra as a central simple algebra. -/
def asCSA : CSA F := ⟨.of F (CrossProductAlgebra f)⟩


-- @@ L484-484 verbatim
end CrossProductAlgebra
