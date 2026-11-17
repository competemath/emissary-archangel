import TubalTensor.TransformDomain.FacewiseProduct
import TubalTensor.Modules.TensorMatrix
import TubalTensor.RingStructure.Realness


-- @@ L5-15 verbatim
/-!
  TubalTensor/TransformDomain/Transform.lean
  Transformed tensor Â := A ×₃ M, inverse transform, and Fact 25.

  Given a tubal matrix A ∈ K_M^{m×p}, the transformed tensor
  Â ∈ ℂ^{m×p×n} (viewed as n frontal slices in ℂ^{m×p}) is defined by
  applying M to each tube along the third dimension:
    Â_k[i,j] = (M · tube(A_{ij}))_k

  Fact 25: C = A ⋆_M B  ⟺  Ĉ = Â △ B̂
-/


-- @@ L17-17 verbatim
namespace TubalTensor


-- @@ L19-19 verbatim
open BigOperators Matrix


-- @@ L21-21 verbatim
variable {n : ℕ} {td : TubalData n} {m p l : ℕ}


-- @@ L23-23 verbatim
/-! ## Transform and inverse transform (Section 6) -/


-- @@ L25-29 verbatim
/-- The transformed tensor Â := A ×₃ M.
    The k-th frontal slice has entry (i,j) = (M · tube(A_{ij}))_k. -/
noncomputable def transform (A : TubalMatrix m p n td) :
    Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun k i j => td.applyM (toComplex (KM.toFun (A i j))) k


-- @@ L31-35 verbatim
/-- The inverse transform: reconstruct a TubalMatrix from frontal slices.
    For each (i,j), extract the tube across slices, apply M⁻¹, take real part. -/
noncomputable def invTransform (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ) :
    TubalMatrix m p n td :=
  fun i j => KM.ofFun (vecRe (td.applyMinv (fun k => Ahat k i j)))


-- @@ L37-39 verbatim
@[simp]
theorem transform_apply (A : TubalMatrix m p n td) (k : Fin n) (i : Fin m) (j : Fin p) :
    transform A k i j = td.applyM (toComplex (KM.toFun (A i j))) k := rfl


-- @@ L41-41 verbatim
/-! ## Transform / inverse transform are mutual inverses -/


-- @@ L43-48 verbatim
/-- Round-trip: invTransform ∘ transform = id. -/
theorem invTransform_transform (A : TubalMatrix m p n td) :
    invTransform (transform A) = A := by
  funext i j
  show KM.ofFun (vecRe (td.applyMinv (td.applyM (toComplex (KM.toFun (A i j)))))) = A i j
  rw [td.applyMinv_applyM, vecRe_toComplex, KM.ofFun_toFun]


-- @@ L50-58 verbatim
/-- Round-trip: transform ∘ invTransform = id, provided the input arises
    from a real tubal matrix (each tube through M⁻¹ gives a real vector). -/
theorem transform_invTransform
    (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (hreal : ∀ i j, IsRealVec (td.applyMinv (fun k => Ahat k i j))) :
    transform (invTransform Ahat : TubalMatrix m p n td) = Ahat := by
  funext k i j
  simp only [transform_apply, invTransform, KM.toFun_ofFun]
  rw [toComplex_vecRe _ (hreal i j), td.applyM_applyMinv]


-- @@ L60-60 verbatim
/-! ## Helper lemmas for Fact 25 -/


-- @@ L62-69 verbatim
/-- toComplex distributes over finite sums. -/
private theorem toComplex_sum {ι : Type*} (S : Finset ι) (f : ι → Fin n → ℝ) :
    toComplex (∑ s ∈ S, f s) = ∑ s ∈ S, toComplex (f s) := by
  induction S using Finset.cons_induction with
  | empty => ext i; simp [toComplex_apply]
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [toComplex_add, ih]


-- @@ L71-81 verbatim
/-- applyM distributes over finite sums. -/
private theorem applyM_sum {ι : Type*} (S : Finset ι)
    (f : ι → Fin n → ℂ) :
    td.applyM (∑ s ∈ S, f s) = ∑ s ∈ S, td.applyM (f s) := by
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.mulVec_zero _
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [td.applyM_add, ih]


-- @@ L83-93 verbatim
/-- Key tube-level lemma: M(a ⋆_M b) = Ma ∘ₕ Mb. -/
private theorem applyM_toComplex_mul (a b : KM n td) :
    td.applyM (toComplex (KM.toFun (a * b))) =
    td.applyM (toComplex (KM.toFun a)) ∘ₕ td.applyM (toComplex (KM.toFun b)) := by
  have h1 : toComplex (KM.toFun (a * b)) =
      starMC td (toComplex (KM.toFun a)) (toComplex (KM.toFun b)) := by
    change toComplex (starM td (KM.toFun a) (KM.toFun b)) = _
    exact starM_eq_starMC td (KM.toFun a) (KM.toFun b)
  rw [h1]
  show td.applyM (td.applyMinv (td.applyM _ ∘ₕ td.applyM _)) = _
  rw [td.applyM_applyMinv]


-- @@ L95-95 verbatim
/-! ## Fact 25: C = A ⋆_M B ⟺ Ĉ = Â △ B̂ -/


-- @@ L97-111 verbatim
/-- The transform of a ⋆_M-product equals the facewise product
    of the transforms: `transform (A * B) = transform A △ transform B`. -/
private theorem transform_mul (A : TubalMatrix m p n td) (B : TubalMatrix p l n td) :
    transform (A * B) = transform A △ transform B := by
  funext k i j
  simp only [transform_apply, facewise_apply, Matrix.mul_apply]
  -- KM.toFun distributes over sum (definitional for the type alias)
  change (td.applyM (toComplex (∑ s : Fin p, KM.toFun (A i s * B s j)))) k = _
  rw [toComplex_sum, applyM_sum]
  -- Pull the evaluation at k inside the sum
  rw [Finset.sum_apply]
  -- Apply the tube-level lemma to each summand
  refine Finset.sum_congr rfl fun s _ => ?_
  have := congr_fun (applyM_toComplex_mul (A i s) (B s j)) k
  simpa [vecHadamard_apply] using this


-- @@ L113-117 verbatim
/-- The transform is injective: if two tubal matrices have the same transform,
    they are equal. -/
private theorem transform_injective :
    Function.Injective (transform : TubalMatrix m p n td → _) :=
  Function.LeftInverse.injective invTransform_transform


-- @@ L119-137 verbatim
/-- A tube is zero iff all its transform-domain components are zero. -/
theorem tube_eq_zero_iff_transform {A : TubalMatrix m p n td}
    (i : Fin m) (j : Fin p) :
    A i j = 0 ↔ ∀ k, transform A k i j = 0 := by
  constructor
  · intro h k
    simp only [transform_apply, h, KM.toFun_zero, toComplex_zero]
    exact congr_fun (Matrix.mulVec_zero td.M) k
  · intro h
    have hall : td.applyM (toComplex (KM.toFun (A i j))) = 0 := funext h
    have hzero := congr_arg td.applyMinv hall
    simp only [td.applyMinv_applyM] at hzero
    rw [show td.applyMinv 0 = 0 from Matrix.mulVec_zero _] at hzero
    have hfun : KM.toFun (A i j) = 0 := by
      ext l; have := congr_fun hzero l
      simp only [toComplex, Pi.zero_apply] at this
      exact_mod_cast this
    change KM.ofFun (KM.toFun (A i j)) = 0
    rw [hfun]; rfl


-- @@ L139-145 verbatim
/-- **Fact 25**
    C = A ⋆_M B ⟺ Ĉ = Â △ B̂. -/
theorem transform_eq_facewise_iff
    (A : TubalMatrix m p n td) (B : TubalMatrix p l n td) (C : TubalMatrix m l n td) :
    C = A * B ↔ transform C = transform A △ transform B :=
  ⟨fun h => h ▸ transform_mul A B,
   fun h => transform_injective (h.trans (transform_mul A B).symm)⟩


-- @@ L147-147 verbatim
end TubalTensor
