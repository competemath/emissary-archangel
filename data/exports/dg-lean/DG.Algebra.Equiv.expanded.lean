import DG.Algebra.Hom


-- @@ L3-11 verbatim
/-!
# Isomorphisms of dg algebras

* `DGAlgEquiv R A B` (notation `A ≃ᵈᵍₐ[R] B`): `R`-algebra isomorphisms of degree `0`
  commuting with the differentials, the isomorphisms of dg `R`-algebras.
* `DGAlgEquiv.ofAlgEquiv`: an algebra isomorphism which maps `Aⁿ` into `Bⁿ` for every `n` and
  commutes with `d` is a dg algebra isomorphism; the inverse automatically has the same
  properties (`DG.symm_mem_of_map_mem`).
-/


-- @@ L13-13 verbatim
open DirectSum


-- @@ L15-15 verbatim
namespace DG


-- @@ L17-17 verbatim
section Inverse


-- @@ L19-19 verbatim
variable {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]


-- @@ L21-45 verbatim
/-- If a bijective additive map of degree `0` between graded abelian groups maps `Mⁿ` into `Nⁿ`
for every `n`, then its inverse maps `Nⁿ` into `Mⁿ`. -/
theorem symm_mem_of_map_mem (e : M ≃+ N) (he : ∀ {n : ℤ} {m : M}, m ∈ grading n → e m ∈ grading n)
    {n : ℤ} {x : N} (hx : x ∈ grading n) : e.symm x ∈ grading n := by
  classical
  set m := e.symm x with hm
  have hcomp : ∀ i, i ≠ n → (decompose (grading (M := M)) m i : M) = 0 := by
    intro i hi
    apply e.injective
    rw [map_zero]
    have h := decompose_map (k := 0) (e : M →+ N) (fun hm => by rw [add_zero]; exact he hm) m i
    rw [add_zero] at h
    change (e : M →+ N) _ = 0
    rw [← h, hm]
    change (decompose (grading (M := N)) (e (e.symm x)) i : N) = 0
    rw [AddEquiv.apply_symm_apply, decompose_of_mem_ne _ hx hi.symm]
  have : m = (decompose (grading (M := M)) m n : M) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (grading (M := M)) m]
    by_cases hn : n ∈ DFinsupp.support (decompose (grading (M := M)) m)
    · exact Finset.sum_eq_single_of_mem n hn fun i _ hi => hcomp i hi
    · rw [Finset.sum_eq_zero fun i hi => hcomp i fun h => hn (h ▸ hi)]
      rw [DFinsupp.notMem_support_iff] at hn
      rw [hn, ZeroMemClass.coe_zero]
  rw [this]
  exact (decompose (grading (M := M)) m n).2


-- @@ L47-47 verbatim
end Inverse


-- @@ L49-54 verbatim
/-- An isomorphism of dg `R`-algebras: an `R`-algebra isomorphism of degree `0` commuting with
the differentials. -/
structure DGAlgEquiv (R A B : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
    [Ring B] [Algebra R B] [DGAddCommGroup B] extends A ≃ₐ[R] B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)


-- @@ L56-57 verbatim
@[inherit_doc]
notation:50 A " ≃ᵈᵍₐ[" R "] " B => DGAlgEquiv R A B


-- @@ L59-59 verbatim
namespace DGAlgEquiv


-- @@ L61-62 verbatim
variable {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [Ring C] [Algebra R C] [DGAddCommGroup C]


-- @@ L64-73 expanded
instance : EquivLike (DGAlgEquiv R A B) A B
    where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁
    h₂ := by
    obtain ⟨f, _, _⟩ := f
    obtain ⟨g, _, _⟩ := g
    congr
    exact AlgEquiv.ext (congrFun h₁)


-- @@ L75-78 expanded
instance : AlgEquivClass (DGAlgEquiv R A B) R A B
    where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'


-- @@ L80-81 expanded
@[simp]
theorem coe_toAlgEquiv (e : DGAlgEquiv R A B) : ⇑e.toAlgEquiv = e :=
  rfl


-- @@ L83-85 expanded
@[ext]
theorem ext {e e' : DGAlgEquiv R A B} (h : ∀ a, e a = e' a) : e = e' :=
  DFunLike.ext e e' h


-- @@ L87-88 expanded
theorem map_mem (e : DGAlgEquiv R A B) {n : ℤ} {a : A} (ha : a ∈ grading n) : e a ∈ grading n :=
  e.map_mem' ha


-- @@ L90-92 expanded
@[simp]
theorem map_d (e : DGAlgEquiv R A B) (a : A) : e (d a) = d (e a) :=
  e.map_d' a


-- @@ L94-98 expanded
/-- The underlying morphism of dg algebras. -/
def toDGAlgHom (e : DGAlgEquiv R A B) : DGAlgHom R A B
    where
  __ := e.toAlgEquiv.toAlgHom
  map_mem' := e.map_mem'
  map_d' := e.map_d'


-- @@ L100-101 expanded
@[simp]
theorem coe_toDGAlgHom (e : DGAlgEquiv R A B) : ⇑e.toDGAlgHom = e :=
  rfl


-- @@ L103-109 expanded
/-- An algebra isomorphism which maps `Aⁿ` into `Bⁿ` and commutes with the differentials is an
isomorphism of dg algebras. -/
def ofAlgEquiv (e : A ≃ₐ[R] B) (map_mem : ∀ {n : ℤ} {a : A}, a ∈ grading n → e a ∈ grading n)
    (map_d : ∀ a : A, e (d a) = d (e a)) : DGAlgEquiv R A B
    where
  __ := e
  map_mem' := map_mem
  map_d' := map_d


-- @@ L111-113 verbatim
@[simp]
theorem coe_ofAlgEquiv (e : A ≃ₐ[R] B) (map_mem) (map_d) : ⇑(ofAlgEquiv e map_mem map_d) = e :=
  rfl


-- @@ L115-117 expanded
/-- The identity isomorphism. -/
def refl : DGAlgEquiv R A A :=
  ofAlgEquiv AlgEquiv.refl (fun ha => ha) fun _ => rfl


-- @@ L119-120 expanded
@[simp]
theorem refl_apply (a : A) : (refl : DGAlgEquiv R A A) a = a :=
  rfl


-- @@ L122-128 expanded
/-- The inverse of an isomorphism of dg algebras. -/
def symm (e : DGAlgEquiv R A B) : DGAlgEquiv R B A :=
  ofAlgEquiv e.toAlgEquiv.symm
    (fun hb => symm_mem_of_map_mem e.toAlgEquiv.toAddEquiv (fun ha => e.map_mem ha) hb) fun b =>
    e.toAlgEquiv.injective <| by
      rw [AlgEquiv.apply_symm_apply, coe_toAlgEquiv, map_d, ← coe_toAlgEquiv e,
        AlgEquiv.apply_symm_apply]


-- @@ L130-132 expanded
@[simp]
theorem apply_symm_apply (e : DGAlgEquiv R A B) (b : B) : e (e.symm b) = b :=
  e.toAlgEquiv.apply_symm_apply b


-- @@ L134-136 expanded
@[simp]
theorem symm_apply_apply (e : DGAlgEquiv R A B) (a : A) : e.symm (e a) = a :=
  e.toAlgEquiv.symm_apply_apply a


-- @@ L138-141 expanded
/-- The composition of isomorphisms of dg algebras. -/
def trans (e : DGAlgEquiv R A B) (e' : DGAlgEquiv R B C) : DGAlgEquiv R A C :=
  ofAlgEquiv (e.toAlgEquiv.trans e'.toAlgEquiv) (fun ha => e'.map_mem (e.map_mem ha)) fun a => by
    simp


-- @@ L143-145 expanded
@[simp]
theorem trans_apply (e : DGAlgEquiv R A B) (e' : DGAlgEquiv R B C) (a : A) :
    e.trans e' a = e' (e a) :=
  rfl


-- @@ L147-147 verbatim
end DGAlgEquiv


-- @@ L149-149 verbatim
end DG
