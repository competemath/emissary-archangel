import DG.Derived.ExternalTensorOver
import DG.K0.LeftCorner
import DG.Positive.Kunneth


-- @@ L5-30 verbatim
/-!
# The external tensor product on `K₀`

For dg rings `A`, `B`, the derived external tensor product `- ⊠ᴸ -` is triangulated in each
variable and preserves compact objects (`DG/Derived/ExternalTensorCompact.lean`), so it induces
a biadditive map

`DG.DerivedCategory.K0ExternalTensor : K₀(A) →+ K₀(B) →+ K₀(A ᵍ⊗[ℤ] B)`,
`[X] ⊗ [Y] ↦ [X ⊠ᴸ Y]` (`DG.DerivedCategory.K0ExternalTensor_mk`).

For dg algebras over a commutative ring `R`, composing with `K₀` of the comparison morphism
`A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B` (`DG.GradedTensorProduct.intComparison`; `K₀` of a morphism of dg rings is
induced by derived induction, roadmap 5.5) gives the map induced by the derived external tensor
product over `R` (`DG.DerivedCategory.externalTensorOver`):

`DG.DerivedCategory.K0ExternalTensorOver R : K₀(A) →+ K₀(B) →+ K₀(A ᵍ⊗[R] B)`.

* On the classes of degree-`0` idempotent cocycles, `[A e] ⊗ [B f] ↦ [(A ⊗ B)(e ⊗ f)]`
  (`DG.DerivedCategory.K0ExternalTensor_leftCorner`,
  `DG.DerivedCategory.K0ExternalTensorOver_leftCorner`), from the isomorphism of dg modules
  `A e ⊠ B f ≅ (A ⊗ B)(e ⊗ f)` (`DG.ExternalTensor.leftCornerTensorIso`).
* **Compatibility with the Künneth isomorphism** (roadmap 6.5): for positive dg algebras over a
  field `k` with split semisimple degree-`0` parts, `K0ExternalTensorOver k x y` is the image of
  `x ⊗ y` under `DG.IsPositive.K0KunnethEquiv`
  (`DG.DerivedCategory.K0ExternalTensorOver_eq_K0KunnethEquiv`).
-/


-- @@ L32-32 verbatim
open CategoryTheory Limits Pretriangulated

-- @@ L33-33 verbatim
open scoped TensorProduct


-- @@ L35-35 verbatim
universe u


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
namespace DG


-- @@ L41-41 verbatim
/-! ### Tensor products of idempotents -/


-- @@ L43-43 verbatim
section Idempotent


-- @@ L45-48 verbatim
variable (R : Type*) [CommRing R]
  {A B : Type*} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]
  (e : DGIdempotent A) (f : DGIdempotent B)


-- @@ L50-63 verbatim
/-- The tensor product `e ⊗ f` of degree-`0` idempotent cocycles, an idempotent cocycle of
`A ᵍ⊗[R] B`. -/
noncomputable def DGIdempotent.tmulOver :
    DGIdempotent (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B) where
  val := e.val ᵍ⊗ₜ[R] f.val
  mem_zero := GradedTensorProduct.tmul_mem_of_eq _ _ (add_zero 0) e.mem_zero f.mem_zero
  mul_self := by
    rw [GradedTensorProduct.tmul_mul_tmul _ _ _
      (show f.val ∈ DGAlgebra.gradingSubmodule R B 0 from f.mem_zero)
      (show e.val ∈ DGAlgebra.gradingSubmodule R A 0 from e.mem_zero), zero_mul, koszulSign_zero,
      one_smul, e.mul_self, f.mul_self]
  d_eq_zero := by
    rw [GradedTensorProduct.d_tmul e.mem_zero, e.d_eq_zero, f.d_eq_zero,
      GradedTensorProduct.zero_tmul, GradedTensorProduct.tmul_zero, smul_zero, add_zero]


-- @@ L65-66 verbatim
@[simp]
theorem DGIdempotent.tmulOver_val : (e.tmulOver R f).val = e.val ᵍ⊗ₜ[R] f.val := rfl


-- @@ L68-70 verbatim
/-- The comparison `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B` takes `e ⊗ f` to `e ⊗ f`. -/
theorem DGIdempotent.map_intComparison_tmulOver :
    (e.tmulOver ℤ f).map (GradedTensorProduct.intComparison R A B) = e.tmulOver R f := rfl


-- @@ L72-72 verbatim
end Idempotent


-- @@ L74-74 verbatim
/-! ### `A e ⊠ B f ≅ (A ⊗ B)(e ⊗ f)` -/


-- @@ L76-76 verbatim
namespace ExternalTensor


-- @@ L78-79 verbatim
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]


-- @@ L81-81 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L82-82 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L83-83 verbatim
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ


-- @@ L85-95 expanded
theorem dgHom_ext_tmul_homogeneous {M N X : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [DGModule A M] [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N] [AddCommGroup X]
    [DGAddCommGroup X] [Module AB X] [DGModule AB X] {φ ψ : DGModuleHom AB (M ⊗[ℤ] N) X}
    (h : ∀ {i j : ℤ} (m : M), m ∈ grading i → ∀ n : N, n ∈ grading j → φ (m ⊗ₜ n) = ψ (m ⊗ₜ n)) :
    φ = ψ :=
  DGModuleHom.ext fun x => by
    induction x using DG.tensor_induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => exact h m.1 m.2 n.1 n.2
    | add x y hx hy => rw [map_add, map_add, hx, hy]


-- @@ L97-97 verbatim
variable (e : DGIdempotent A) (f : DGIdempotent B)


-- @@ L99-111 verbatim
/-- `A e ⊠ B f` is a retract of `A ⊠ B`. -/
def leftCornerTensorRetract :
    Retract
      (((functor A B).obj (DGModuleCat.of A e.LeftCorner)).obj (DGModuleCat.of B f.LeftCorner))
      (((functor A B).obj (DGModuleCat.of A A)).obj (DGModuleCat.of B B)) where
  i := DGModuleCat.ofHom (tensorDGHom e.leftCornerInclusion f.leftCornerInclusion)
  r := DGModuleCat.ofHom (tensorDGHom e.leftCornerProjection f.leftCornerProjection)
  retract := DGModuleCat.hom_ext (tensorDGHom_ext fun m n => by
    change e.leftCornerProjection (e.leftCornerInclusion m) ⊗ₜ
      f.leftCornerProjection (f.leftCornerInclusion n) = m ⊗ₜ n
    rw [← DGModuleHom.comp_apply, ← DGModuleHom.comp_apply, e.leftCornerProjection_comp_inclusion,
      f.leftCornerProjection_comp_inclusion]
    rfl)


-- @@ L113-118 verbatim
/-- `(A ⊗ B)(e ⊗ f)` is a retract of `A ⊗ B`. -/
def tmulLeftCornerRetract :
    Retract (DGModuleCat.of AB (e.tmulOver ℤ f).LeftCorner) (DGModuleCat.of AB AB) where
  i := DGModuleCat.ofHom (e.tmulOver ℤ f).leftCornerInclusion
  r := DGModuleCat.ofHom (e.tmulOver ℤ f).leftCornerProjection
  retract := DGModuleCat.hom_ext (e.tmulOver ℤ f).leftCornerProjection_comp_inclusion


-- @@ L120-132 verbatim
/-- **`A e ⊠ B f ≅ (A ⊗ B)(e ⊗ f)`** as dg modules over `A ⊗ B`, `m ⊗ n ↦ m ⊗ n`: the two
retracts of `A ⊠ B ≅ A ⊗ B` cut out by `a ⊗ b ↦ a e ⊗ b f` and by right multiplication with
`e ⊗ f` (which agree, since `e` has degree `0`). -/
def leftCornerTensorIso :
    ((functor A B).obj (DGModuleCat.of A e.LeftCorner)).obj (DGModuleCat.of B f.LeftCorner) ≅
      DGModuleCat.of AB (e.tmulOver ℤ f).LeftCorner :=
  Retract.isoOfConj (leftCornerTensorRetract e f) (tmulLeftCornerRetract e f)
    DerivedCategory.regularTensorIso
    (DGModuleCat.hom_ext (dgHom_ext_tmul_homogeneous (A := A) (B := B) (M := A) (N := B)
      fun {i j} a ha b hb => by
        change ((a * e.val) ᵍ⊗ₜ[ℤ] (b * f.val) : AB) = (a ᵍ⊗ₜ[ℤ] b : AB) * (e.val ᵍ⊗ₜ[ℤ] f.val)
        rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ a hb e.mem_zero f.val, mul_zero,
          koszulSign_zero, one_smul]))


-- @@ L134-134 verbatim
end ExternalTensor


-- @@ L136-136 verbatim
namespace DerivedCategory


-- @@ L138-138 verbatim
/-! ### The biadditive map on `K₀` -/


-- @@ L140-140 verbatim
section Int


-- @@ L142-143 verbatim
variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]


-- @@ L145-145 verbatim
local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A

-- @@ L146-146 verbatim
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B

-- @@ L147-147 verbatim
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ


-- @@ L149-150 verbatim
variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]


-- @@ L152-163 verbatim
variable (A B) in
/-- **The biadditive map `K₀(A) × K₀(B) → K₀(A ⊗ B)` induced by `⊠ᴸ`**, `[X] ⊗ [Y] ↦ [X ⊠ᴸ Y]`
(`DG.DerivedCategory.K0ExternalTensor_mk`). -/
def K0ExternalTensor : DGRing.K0 A →+ DGRing.K0 B →+ DGRing.K0 AB :=
  K0.lift (fun X : PerfectDerivedCategory A =>
      K0.mapCompact ((externalTensor A B).obj X.obj) fun _ h => isCompact_externalTensor X.2 h)
    fun T hT => K0.addMonoidHom_ext fun Y => by
      have h := congrArg (K0.mapCompact ((externalTensor A B).flip.obj Y.obj)
        fun _ h => isCompact_externalTensor h Y.2) (K0.mk_obj₂ T hT)
      simp only [map_add, K0.mapCompact_mk] at h
      simp only [K0.mapCompact_mk, AddMonoidHom.add_apply]
      exact h


-- @@ L165-169 verbatim
theorem K0ExternalTensor_mk (X : PerfectDerivedCategory A) (Y : PerfectDerivedCategory B) :
    K0ExternalTensor A B (K0.mk X) (K0.mk Y) =
      K0.mk (⟨((externalTensor A B).obj X.obj).obj Y.obj, isCompact_externalTensor X.2 Y.2⟩ :
        PerfectDerivedCategory AB) :=
  (DFunLike.congr_fun (K0.lift_mk _ _ X) (K0.mk Y)).trans (K0.mapCompact_mk _ _ Y)


-- @@ L171-177 verbatim
/-- **`[A e] ⊠ [B f] = [(A ⊗ B)(e ⊗ f)]`** in `K₀(A ⊗ B)`. -/
theorem K0ExternalTensor_leftCorner (e : DGIdempotent A) (f : DGIdempotent B) :
    K0ExternalTensor A B (DGRing.K0.leftCorner e) (DGRing.K0.leftCorner f) =
      DGRing.K0.leftCorner (e.tmulOver ℤ f) :=
  (K0ExternalTensor_mk _ _).trans (K0.mk_eq_of_iso_obj
    (externalTensorObjIso e.isKProjective_leftCorner f.isKProjective_leftCorner ≪≫
      Q.mapIso (ExternalTensor.leftCornerTensorIso e f)))


-- @@ L179-179 verbatim
end Int


-- @@ L181-181 verbatim
/-! ### Over a commutative ring -/


-- @@ L183-183 verbatim
section Over


-- @@ L185-187 verbatim
variable (R : Type*) [CommRing R]
  {A B : Type u} [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A] [DGAlgebra R A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [DGRing B] [DGAlgebra R B]


-- @@ L189-189 verbatim
local notation "𝒜ᵣ" => DGAlgebra.gradingSubmodule R A

-- @@ L190-190 verbatim
local notation "ℬᵣ" => DGAlgebra.gradingSubmodule R B


-- @@ L192-194 verbatim
variable [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule R A ᵍ⊗[R] DGAlgebra.gradingSubmodule R B)]


-- @@ L196-200 verbatim
variable (A B) in
/-- **The biadditive map `K₀(A) × K₀(B) → K₀(A ⊗_R B)`** induced by the derived external tensor
product over `R`: `K0ExternalTensor` followed by `K₀` of `A ᵍ⊗[ℤ] B → A ᵍ⊗[R] B`. -/
def K0ExternalTensorOver : DGRing.K0 A →+ DGRing.K0 B →+ DGRing.K0 (𝒜ᵣ ᵍ⊗[R] ℬᵣ) :=
  (K0ExternalTensor A B).compr₂ (DGRing.K0.map (GradedTensorProduct.intComparison R A B))


-- @@ L202-204 verbatim
theorem K0ExternalTensorOver_apply (x : DGRing.K0 A) (y : DGRing.K0 B) :
    K0ExternalTensorOver R A B x y =
      DGRing.K0.map (GradedTensorProduct.intComparison R A B) (K0ExternalTensor A B x y) := rfl


-- @@ L206-211 verbatim
/-- **`[A e] ⊠_R [B f] = [(A ⊗_R B)(e ⊗ f)]`** in `K₀(A ⊗_R B)`. -/
theorem K0ExternalTensorOver_leftCorner (e : DGIdempotent A) (f : DGIdempotent B) :
    K0ExternalTensorOver R A B (DGRing.K0.leftCorner e) (DGRing.K0.leftCorner f) =
      DGRing.K0.leftCorner (e.tmulOver R f) := by
  rw [K0ExternalTensorOver_apply, K0ExternalTensor_leftCorner, DGRing.K0.map_leftCorner]
  rfl


-- @@ L213-213 verbatim
end Over


-- @@ L215-215 verbatim
/-! ### Compatibility with the Künneth isomorphism -/


-- @@ L217-217 verbatim
section Kunneth


-- @@ L219-225 verbatim
variable {k : Type*} [Field k]
  {A : Type u} [Ring A] [Algebra k A] [DGAddCommGroup A] [DGRing A] [DGAlgebra k A]
  {B : Type u} [Ring B] [Algebra k B] [DGAddCommGroup B] [DGRing B] [DGAlgebra k B]
  (hA : IsPositive A) (hB : IsPositive B)
  [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]
  [HasDerivedCategory.{u, u} (DGAlgebra.gradingSubmodule k A ᵍ⊗[k] DGAlgebra.gradingSubmodule k B)]


-- @@ L227-257 verbatim
/-- **The external tensor product on `K₀` is the Künneth isomorphism** (roadmap 6.5): for positive
dg algebras `A`, `B` over a field `k` with split semisimple degree-`0` parts,
`[X] ⊠_k [Y] = K0KunnethEquiv ([X] ⊗ [Y])`. -/
theorem K0ExternalTensorOver_eq_K0KunnethEquiv
    (hsA : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k A))
    (hsB : IsSplitSemisimple k (DGAlgebra.degreeZeroSubalgebra k B))
    (x : DGRing.K0 A) (y : DGRing.K0 B) :
    K0ExternalTensorOver k A B x y = hA.K0KunnethEquiv hB hsA hsB (x ⊗ₜ y) := by
  let := HasDerivedCategory.small.{u, u} hA.degreeZeroDGSubring
  let := HasDerivedCategory.small.{u, u} hB.degreeZeroDGSubring
  let bA := hA.basis (SimpleClass.out (C := A)) SimpleClass.out_injective
    fun e => ⟨_, SimpleClass.equiv_out e⟩
  let bB := hB.basis (SimpleClass.out (C := B)) SimpleClass.out_injective
    fun f => ⟨_, SimpleClass.equiv_out f⟩
  have key : ∀ a b, K0ExternalTensorOver k A B (bA a) (bB b) =
      hA.K0KunnethEquiv hB hsA hsB (bA a ⊗ₜ bB b) := fun a b => by
    rw [show bA a = DGRing.K0.leftCorner (SimpleClass.out a).1 from
        IsPositive.basis_apply _ _ _ _ a,
      show bB b = DGRing.K0.leftCorner (SimpleClass.out b).1 from
        IsPositive.basis_apply _ _ _ _ b,
      K0ExternalTensorOver_leftCorner, IsPositive.K0KunnethEquiv_tmul]
    rfl
  have hy : ∀ a, (K0ExternalTensorOver k A B (bA a)).toIntLinearMap =
      (hA.K0KunnethEquiv hB hsA hsB).toLinearMap ∘ₗ
        TensorProduct.mk ℤ (DGRing.K0 A) (DGRing.K0 B) (bA a) :=
    fun a => bB.ext fun b => key a b
  have hx : ((K0ExternalTensorOver k A B).flip y).toIntLinearMap =
      (hA.K0KunnethEquiv hB hsA hsB).toLinearMap ∘ₗ
        (TensorProduct.mk ℤ (DGRing.K0 A) (DGRing.K0 B)).flip y :=
    bA.ext fun a => DFunLike.congr_fun (hy a) y
  exact DFunLike.congr_fun hx x


-- @@ L259-259 verbatim
end Kunneth


-- @@ L261-261 verbatim
end DerivedCategory


-- @@ L263-263 verbatim
end DG
