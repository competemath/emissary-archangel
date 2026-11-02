import DG.Module.Basic


-- @@ L3-14 verbatim
/-!
# Isomorphisms of dg modules

* `DGModuleEquiv A M N` (notation `M ≃ᵈᵍ[A] N`): an `A`-linear equivalence of degree `0`
  commuting with the differentials. Its inverse is automatically a morphism of dg modules
  (`DGModuleEquiv.symm`): a bijective graded map of degree `0` has a graded inverse, which is
  proved through the uniqueness of homogeneous decompositions
  (`DGModuleHom.mem_grading_of_injective`).

The API is deliberately small: `refl`, `symm`, `trans`, `toDGModuleHom` and the evaluation
lemmas.
-/


-- @@ L16-16 verbatim
open DirectSum


-- @@ L18-18 verbatim
namespace DG


-- @@ L20-20 verbatim
section Decompose


-- @@ L22-24 verbatim
variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]


-- @@ L26-38 expanded
/-- A morphism of dg modules commutes with the homogeneous decompositions. -/
theorem DGModuleHom.coe_decompose_apply (f : DGModuleHom A M N) (m : M) (j : ℤ) :
    (decompose (grading (M := N)) (f m) j : N) = f (decompose (grading (M := M)) m j) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    rw [decompose_of_mem _ (f.map_mem x.2), decompose_coe]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm hij)]
  | h_add m m' hm hm' => simp [decompose_add, hm, hm']


-- @@ L40-58 expanded
/-- An injective morphism of dg modules reflects the grading: if `f m` is homogeneous of
degree `k`, so is `m`. -/
theorem DGModuleHom.mem_grading_of_injective (f : DGModuleHom A M N) (hf : Function.Injective f)
    {k : ℤ} {m : M} (hm : f m ∈ grading k) : m ∈ grading k :=
  by
  set ℳ := grading (M := M)
  have key : ∀ j, j ≠ k → decompose ℳ m j = 0 := fun j hj =>
    by
    refine Subtype.ext (hf ?_)
    rw [← f.coe_decompose_apply, decompose_of_mem_ne _ hm (Ne.symm hj), ZeroMemClass.coe_zero,
      map_zero]
  have h : decompose ℳ m = DirectSum.of (fun i => ℳ i) k (decompose ℳ m k) :=
    by
    refine DirectSum.ext fun j => ?_
    by_cases hjk : j = k
    · subst hjk
      rw [of_eq_same]
    · rw [of_eq_of_ne _ _ _ hjk, key j hjk]
  have h' := congrArg (decompose ℳ).symm h
  rw [Equiv.symm_apply_apply, decompose_symm_of] at h'
  rw [h']
  exact (decompose ℳ m k).2


-- @@ L60-60 verbatim
end Decompose


-- @@ L62-68 verbatim
/-- An isomorphism of dg `A`-modules: an `A`-linear equivalence of degree `0` commuting with
the differentials. -/
structure DGModuleEquiv (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] extends M ≃ₗ[A] N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)


-- @@ L70-71 verbatim
@[inherit_doc]
notation:25 M " ≃ᵈᵍ[" A "] " N => DGModuleEquiv A M N


-- @@ L73-73 verbatim
namespace DGModuleEquiv


-- @@ L75-78 verbatim
variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]


-- @@ L80-89 expanded
instance : EquivLike (DGModuleEquiv A M N) M N
    where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h
    _ := by
    rcases e with ⟨e, _, _⟩
    rcases e' with ⟨e', _, _⟩
    obtain rfl : e = e' := LinearEquiv.ext (congrFun h)
    rfl


-- @@ L91-93 expanded
instance : LinearEquivClass (DGModuleEquiv A M N) A M N
    where
  map_add e := e.map_add'
  map_smulₛₗ e := e.map_smul'


-- @@ L95-96 expanded
@[simp]
theorem coe_toLinearEquiv (e : DGModuleEquiv A M N) : ⇑e.toLinearEquiv = e :=
  rfl


-- @@ L98-100 expanded
@[ext]
theorem ext {e e' : DGModuleEquiv A M N} (h : ∀ m, e m = e' m) : e = e' :=
  DFunLike.ext e e' h


-- @@ L102-103 expanded
theorem map_mem (e : DGModuleEquiv A M N) {n : ℤ} {m : M} (hm : m ∈ grading n) : e m ∈ grading n :=
  e.map_mem' hm


-- @@ L105-107 expanded
@[simp]
theorem map_d (e : DGModuleEquiv A M N) (m : M) : e (d m) = d (e m) :=
  e.map_d' m


-- @@ L109-113 expanded
/-- The underlying morphism of dg modules of an isomorphism. -/
def toDGModuleHom (e : DGModuleEquiv A M N) : DGModuleHom A M N
    where
  __ := e.toLinearEquiv.toLinearMap
  map_mem' := e.map_mem'
  map_d' := e.map_d'


-- @@ L115-116 expanded
@[simp]
theorem coe_toDGModuleHom (e : DGModuleEquiv A M N) : ⇑e.toDGModuleHom = e :=
  rfl


-- @@ L118-119 expanded
theorem injective (e : DGModuleEquiv A M N) : Function.Injective e :=
  EquivLike.injective e


-- @@ L121-122 expanded
theorem surjective (e : DGModuleEquiv A M N) : Function.Surjective e :=
  EquivLike.surjective e


-- @@ L124-128 expanded
/-- The identity isomorphism. -/
def refl : DGModuleEquiv A M M where
  __ := LinearEquiv.refl A M
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L130-131 expanded
@[simp]
theorem refl_apply (m : M) : (refl : DGModuleEquiv A M M) m = m :=
  rfl


-- @@ L133-143 expanded
/-- The inverse of an isomorphism of dg modules. -/
def symm (e : DGModuleEquiv A M N) : DGModuleEquiv A N M
    where
  __ := e.toLinearEquiv.symm
  map_mem' {_ y}
    hy := by
    refine e.toDGModuleHom.mem_grading_of_injective e.injective ?_
    change e (e.toLinearEquiv.symm y) ∈ grading _
    rwa [← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]
  map_d'
    y := by
    apply e.injective
    change e (e.toLinearEquiv.symm (d y)) = e (d (e.toLinearEquiv.symm y))
    rw [map_d, ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]


-- @@ L145-147 expanded
@[simp]
theorem apply_symm_apply (e : DGModuleEquiv A M N) (y : N) : e (e.symm y) = y :=
  e.right_inv y


-- @@ L149-151 expanded
@[simp]
theorem symm_apply_apply (e : DGModuleEquiv A M N) (m : M) : e.symm (e m) = m :=
  e.left_inv m


-- @@ L153-154 expanded
@[simp]
theorem symm_symm (e : DGModuleEquiv A M N) : e.symm.symm = e :=
  rfl


-- @@ L156-162 expanded
/-- Composition of isomorphisms of dg modules. -/
def trans (e : DGModuleEquiv A M N) (e' : DGModuleEquiv A N P) : DGModuleEquiv A M P
    where
  __ := e.toLinearEquiv.trans e'.toLinearEquiv
  map_mem' hm := e'.map_mem (e.map_mem hm)
  map_d'
    m := by
    change e' (e (d m)) = d (e' (e m))
    rw [map_d, map_d]


-- @@ L164-165 expanded
@[simp]
theorem trans_apply (e : DGModuleEquiv A M N) (e' : DGModuleEquiv A N P) (m : M) :
    e.trans e' m = e' (e m) :=
  rfl


-- @@ L167-167 verbatim
end DGModuleEquiv


-- @@ L169-169 verbatim
end DG
