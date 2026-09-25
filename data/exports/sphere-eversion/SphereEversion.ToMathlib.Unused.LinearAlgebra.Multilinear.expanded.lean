import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-
Multilinear map stuff that was meant as preliminaries for smooth functions gluing.

We no longer intend to use this file in the sphere eversion project.
-/

-- @@ L8-8 verbatim
namespace Function


-- @@ L10-10 verbatim
variable {ι : Sort*} [DecidableEq ι] {α β : ι → Type*}


-- @@ L12-15 verbatim
/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
theorem update_fst (g : ∀ i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
    (update g i v j).fst = update (fun k ↦ (g k).fst) i v.fst j :=
  apply_update (fun _ ↦ Prod.fst) g i v j


-- @@ L17-20 verbatim
/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
theorem update_snd (g : ∀ i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
    (update g i v j).snd = update (fun k ↦ (g k).snd) i v.snd j :=
  apply_update (fun _ ↦ Prod.snd) g i v j


-- @@ L22-22 verbatim
end Function


-- @@ L24-24 verbatim
open Function


-- @@ L26-26 verbatim
namespace MultilinearMap


-- @@ L28-28 verbatim
variable {R ι ι' M₃ M₄ : Type*} {M₁ M₂ : ι → Type*} {N : ι' → Type*}


-- @@ L30-30 verbatim
variable [Semiring R]


-- @@ L32-32 verbatim
variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]


-- @@ L34-34 verbatim
variable [∀ i, AddCommMonoid (M₂ i)] [∀ i, Module R (M₂ i)]


-- @@ L36-36 verbatim
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]


-- @@ L38-38 verbatim
variable [AddCommMonoid M₃] [Module R M₃]


-- @@ L40-40 verbatim
variable [AddCommMonoid M₄] [Module R M₄]


-- @@ L42-46 verbatim
/-- The coproduct of two multilinear maps. -/
@[simps!]
def coprod (L₁ : MultilinearMap R M₁ M₃) (L₂ : MultilinearMap R M₂ M₃) :
    MultilinearMap R (fun i ↦ M₁ i × M₂ i) M₃ :=
  (L₁.compLinearMap fun _ ↦ .fst ..) + L₂.compLinearMap fun _ ↦ .snd ..


-- @@ L48-48 verbatim
end MultilinearMap


-- @@ L50-50 verbatim
namespace ContinuousMultilinearMap


-- @@ L52-52 verbatim
variable {R ι ι' : Type*} {M₁ M₂ : ι → Type*} {M₃ M₄ : Type*} {N : ι' → Type*}


-- @@ L54-54 verbatim
variable [Semiring R]


-- @@ L56-56 verbatim
variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₂ i)] [AddCommMonoid M₃]


-- @@ L58-58 verbatim
variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₂ i)] [Module R M₃]


-- @@ L60-60 verbatim
variable [∀ i, TopologicalSpace (M₁ i)] [∀ i, TopologicalSpace (M₂ i)]


-- @@ L62-62 verbatim
variable [TopologicalSpace M₃]


-- @@ L64-64 verbatim
variable [AddCommMonoid M₄] [Module R M₄] [TopologicalSpace M₄]


-- @@ L66-66 verbatim
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] [∀ i, TopologicalSpace (N i)]


-- @@ L68-68 verbatim
variable [ContinuousAdd M₃]


-- @@ L70-73 verbatim
@[simps!]
def coprod (L₁ : ContinuousMultilinearMap R M₁ M₃) (L₂ : ContinuousMultilinearMap R M₂ M₃) :
    ContinuousMultilinearMap R (fun i ↦ M₁ i × M₂ i) M₃ :=
  (L₁.compContinuousLinearMap fun _ ↦ .fst ..) + L₂.compContinuousLinearMap fun _ ↦ .snd ..


-- @@ L75-78 verbatim
@[simp]
def zero_coprod_zero :
    (0 : ContinuousMultilinearMap R M₁ M₃).coprod (0 : ContinuousMultilinearMap R M₂ M₃) = 0 := by
  ext; simp


-- @@ L80-80 verbatim
end ContinuousMultilinearMap
