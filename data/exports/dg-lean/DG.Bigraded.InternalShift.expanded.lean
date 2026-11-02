import DG.Bigraded.Basic
import DG.Module.Shift


-- @@ L4-27 verbatim
/-!
# The internal shift of bigraded dg modules

* `DG.InternalShift k M`: the internal shift `M⟨k⟩` of a dg abelian group (or dg module) with an
  internal grading, a type synonym for `M` with the same cohomological grading, differential
  and action, and with the weight grading `(M⟨k⟩)⟨j⟩ = M⟨j + k⟩`. This is the analogue for
  weights of the convention `(M[n])ʲ = Mʲ⁺ⁿ` of `DG.Shift`. Since weights carry no signs,
  neither the differential nor the action is twisted.
* `DG.InternalShift.zeroEquiv : M⟨0⟩ ≃ M` and
  `DG.InternalShift.addEquiv k l : (M⟨l⟩)⟨k⟩ ≃ M⟨k + l⟩`, isomorphisms of dg modules which are
  the identity on elements and preserve weights (`DG.InternalShift.mem_wgrading_zeroEquiv_iff`,
  `DG.InternalShift.mem_wgrading_addEquiv_iff`).
* The cohomological shift `DG.Shift n M` of a bigraded dg module is bigraded, with the weight
  grading of `M` (`DG.Shift.instInternalGrading`, `DG.Shift.instBigradedDGModule`): the Koszul
  twist `a • m = (-1)^{n |a|} (a • m)` of the action preserves weights, because `|a|` is the
  cohomological degree of `a` only.
* `DG.InternalShift.shiftEquiv n k : (M[n])⟨k⟩ ≃ (M⟨k⟩)[n]`: the internal and cohomological
  shifts commute; the isomorphism is the identity on elements, without sign.
* `DG.DGModuleHom.internalShift k : (M →ᵈᵍ[A] N) → (M⟨k⟩ →ᵈᵍ[A] N⟨k⟩)`, the internal shift of
  morphisms (the same underlying function).

`InternalShift k M` is a `def`, not an `abbrev`, so that the weight grading of `M` is not
visible on it; its structures are declared explicitly.
-/


-- @@ L29-29 verbatim
open DirectSum


-- @@ L31-31 verbatim
namespace DG


-- @@ L33-33 verbatim
universe u


-- @@ L35-38 verbatim
/-- The internal shift `M⟨k⟩` of a dg abelian group `M` with an internal grading: the same dg
abelian group (and the same action of a dg ring), with the weight grading
`(M⟨k⟩)⟨j⟩ = M⟨j + k⟩`. -/
def InternalShift (_k : ℤ) (M : Type u) : Type u := M


-- @@ L40-40 verbatim
namespace InternalShift


-- @@ L42-42 verbatim
variable (k : ℤ) {M : Type*}


-- @@ L44-44 verbatim
section AddCommGroup


-- @@ L46-46 verbatim
variable [AddCommGroup M]


-- @@ L48-48 verbatim
instance : AddCommGroup (InternalShift k M) := inferInstanceAs (AddCommGroup M)


-- @@ L50-51 verbatim
/-- The identity `M → M⟨k⟩`, as an additive equivalence. -/
def mk : M ≃+ InternalShift k M := AddEquiv.refl M


-- @@ L53-54 verbatim
/-- The identity `M⟨k⟩ → M`, as an additive equivalence. -/
def unmk : InternalShift k M ≃+ M := AddEquiv.refl M


-- @@ L56-56 verbatim
variable {k}


-- @@ L58-58 verbatim
@[simp] theorem unmk_mk (m : M) : unmk k (mk k m) = m := rfl

-- @@ L59-59 verbatim
@[simp] theorem mk_unmk (m : InternalShift k M) : mk k (unmk k m) = m := rfl

-- @@ L60-60 verbatim
@[simp] theorem mk_symm : (mk k (M := M)).symm = unmk k := rfl

-- @@ L61-61 verbatim
@[simp] theorem unmk_symm : (unmk k (M := M)).symm = mk k := rfl


-- @@ L63-63 verbatim
theorem mk_surjective : Function.Surjective (mk k (M := M)) := (mk k).surjective


-- @@ L65-65 verbatim
end AddCommGroup


-- @@ L67-67 verbatim
section DGAddCommGroup


-- @@ L69-69 verbatim
variable {k} [AddCommGroup M] [DGAddCommGroup M]


-- @@ L71-71 verbatim
instance : DGAddCommGroup (InternalShift k M) := inferInstanceAs (DGAddCommGroup M)


-- @@ L73-73 verbatim
theorem mem_grading_iff {n : ℤ} {m : M} : mk k m ∈ grading n ↔ m ∈ grading n := Iff.rfl


-- @@ L75-76 verbatim
theorem mem_grading_iff' {n : ℤ} {m : InternalShift k M} :
    m ∈ grading n ↔ unmk k m ∈ grading n := Iff.rfl


-- @@ L78-78 verbatim
@[simp] theorem d_mk (m : M) : d (mk k m) = mk k (d m) := rfl

-- @@ L79-79 verbatim
@[simp] theorem unmk_d (m : InternalShift k M) : unmk k (d m) = d (unmk k m) := rfl


-- @@ L81-81 verbatim
variable [InternalGrading M]


-- @@ L83-96 verbatim
set_option backward.isDefEq.respectTransparency false in
instance instInternalGrading : InternalGrading (InternalShift k M) where
  wgrading j := wgrading (M := M) (j + k)
  wdecomposition := Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
  isHomogeneous_grading' n j m hm := by
    let : Decomposition fun j => wgrading (M := M) (Equiv.addRight k j) :=
      Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
    have h := Decomposition.coe_decompose_reindex (wgrading (M := M)) (Equiv.addRight k)
      (unmk k m) j
    change (decompose (fun j => wgrading (M := M) (Equiv.addRight k j)) (unmk k m) j : M) ∈
      grading (M := M) n
    rw [h]
    exact decompose_wgrading_mem_grading (M := M) hm _
  d_mem_wgrading' hm := d_mem_wgrading (M := M) hm


-- @@ L98-99 verbatim
theorem mem_wgrading_iff {j : ℤ} {m : M} : mk k m ∈ wgrading j ↔ m ∈ wgrading (j + k) :=
  Iff.rfl


-- @@ L101-102 verbatim
theorem mem_wgrading_iff' {j : ℤ} {m : InternalShift k M} :
    m ∈ wgrading j ↔ unmk k m ∈ wgrading (j + k) := Iff.rfl


-- @@ L104-111 verbatim
/-- The weight components of `M⟨k⟩` are those of `M`, reindexed. -/
theorem coe_decompose_wgrading (m : InternalShift k M) (j : ℤ) :
    unmk k (decompose (wgrading (M := InternalShift k M)) m j : InternalShift k M) =
      (decompose (wgrading (M := M)) (unmk k m) (j + k) : M) := by
  let : Decomposition fun j => wgrading (M := M) (Equiv.addRight k j) :=
    Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
  change (decompose (fun j => wgrading (M := M) (Equiv.addRight k j)) (unmk k m) j : M) = _
  exact Decomposition.coe_decompose_reindex (wgrading (M := M)) (Equiv.addRight k) (unmk k m) j


-- @@ L113-113 verbatim
end DGAddCommGroup


-- @@ L115-115 verbatim
section Module


-- @@ L117-117 verbatim
variable {k} {A : Type*} [Ring A] [AddCommGroup M] [Module A M]


-- @@ L119-119 verbatim
instance : Module A (InternalShift k M) := inferInstanceAs (Module A M)


-- @@ L121-121 verbatim
theorem smul_mk (a : A) (m : M) : a • mk k m = mk k (a • m) := rfl


-- @@ L123-123 verbatim
theorem unmk_smul (a : A) (m : InternalShift k M) : unmk k (a • m) = a • unmk k m := rfl


-- @@ L125-125 verbatim
variable [DGAddCommGroup A] [DGAddCommGroup M]


-- @@ L127-127 verbatim
instance [DGModule A M] : DGModule A (InternalShift k M) := inferInstanceAs (DGModule A M)


-- @@ L129-134 verbatim
instance [InternalGrading A] [InternalGrading M] [BigradedDGModule A M] :
    BigradedDGModule A (InternalShift k M) where
  smul_mem {i j} a m ha hm := by
    rw [mem_wgrading_iff'] at hm ⊢
    rw [vadd_eq_add, add_assoc]
    exact smul_mem_wgrading (M := M) ha hm


-- @@ L136-136 verbatim
end Module


-- @@ L138-138 verbatim
section Equivs


-- @@ L140-141 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M]


-- @@ L143-153 expanded
variable (A) in
/-- The internal shift by `0` is the identity: `M⟨0⟩ ≃ M`. -/
def zeroEquiv : DGModuleEquiv A (InternalShift 0 M) M
    where
  toFun := unmk 0
  invFun := mk 0
  left_inv := mk_unmk
  right_inv := unmk_mk
  map_add' := map_add (unmk 0)
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L155-155 verbatim
@[simp] theorem zeroEquiv_apply (m : InternalShift 0 M) : zeroEquiv A m = unmk 0 m := rfl

-- @@ L156-156 verbatim
@[simp] theorem zeroEquiv_symm_apply (m : M) : (zeroEquiv A).symm m = mk 0 m := rfl


-- @@ L158-168 expanded
variable (A) in
/-- Internal shifts compose: `(M⟨l⟩)⟨k⟩ ≃ M⟨k + l⟩`, the identity on elements. -/
def addEquiv (k l : ℤ) :
    DGModuleEquiv A (InternalShift k (InternalShift l M)) (InternalShift (k + l) M)
    where
  toFun x := mk (k + l) (unmk l (unmk k x))
  invFun y := mk k (mk l (unmk (k + l) y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L170-171 verbatim
@[simp] theorem addEquiv_apply (k l : ℤ) (x : InternalShift k (InternalShift l M)) :
    addEquiv A k l x = mk (k + l) (unmk l (unmk k x)) := rfl


-- @@ L173-174 verbatim
@[simp] theorem addEquiv_symm_apply (k l : ℤ) (y : InternalShift (k + l) M) :
    (addEquiv A k l).symm y = mk k (mk l (unmk (k + l) y)) := rfl


-- @@ L176-176 verbatim
variable [InternalGrading M]


-- @@ L178-181 verbatim
theorem mem_wgrading_zeroEquiv_iff {j : ℤ} {m : InternalShift 0 M} :
    zeroEquiv A m ∈ wgrading j ↔ m ∈ wgrading j := by
  rw [mem_wgrading_iff', add_zero]
  rfl


-- @@ L183-186 verbatim
theorem mem_wgrading_addEquiv_iff (k l : ℤ) {j : ℤ} {x : InternalShift k (InternalShift l M)} :
    addEquiv A k l x ∈ wgrading j ↔ x ∈ wgrading j := by
  rw [mem_wgrading_iff', mem_wgrading_iff', mem_wgrading_iff', add_assoc]
  rfl


-- @@ L188-188 verbatim
end Equivs


-- @@ L190-190 verbatim
end InternalShift


-- @@ L192-192 verbatim
/-! ### Cohomological shifts of bigraded dg modules -/


-- @@ L194-194 verbatim
namespace Shift


-- @@ L196-196 verbatim
variable {n : ℤ} {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M]


-- @@ L198-207 verbatim
/-- The cohomological shift `M[n]` of a dg abelian group with an internal grading has the
weight grading of `M`. -/
instance instInternalGrading : InternalGrading (Shift n M) where
  wgrading k := wgrading (M := M) k
  wdecomposition := InternalGrading.wdecomposition (M := M)
  isHomogeneous_grading' j k m hm := isHomogeneous_grading M (j + n) k hm
  d_mem_wgrading' {k m} hm := by
    change koszulSign n • d (unmk n m) ∈ wgrading (M := M) k
    rw [Units.smul_def]
    exact zsmul_mem (d_mem_wgrading (M := M) (show unmk n m ∈ wgrading (M := M) k from hm)) _


-- @@ L209-209 verbatim
theorem mem_wgrading_iff {k : ℤ} {m : M} : mk n m ∈ wgrading k ↔ m ∈ wgrading k := Iff.rfl


-- @@ L211-212 verbatim
theorem mem_wgrading_iff' {k : ℤ} {m : Shift n M} : m ∈ wgrading k ↔ unmk n m ∈ wgrading k :=
  Iff.rfl


-- @@ L214-214 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]


-- @@ L216-228 verbatim
/-- The twist `a ↦ (-1)^{n |a|} a` preserves weights. -/
theorem twist_mem_wgrading {k : ℤ} {a : A} (ha : a ∈ wgrading k) :
    twist A n a ∈ wgrading k := by
  refine induction_on_of_isHomogeneous (isHomogeneous_wgrading A k) (P := fun a =>
    twist A n a ∈ wgrading k) ?_ (fun {i b} hb hbk => ?_) (fun b b' hb hb' => ?_) ha
  · show twist A n 0 ∈ wgrading k
    rw [map_zero]
    exact zero_mem _
  · show twist A n b ∈ wgrading k
    rw [twist_of_mem hb, Units.smul_def]
    exact zsmul_mem hbk _
  · simp only [map_add]
    exact add_mem hb hb'


-- @@ L230-230 verbatim
variable [Module A M] [BigradedDGModule A M]


-- @@ L232-238 verbatim
/-- The cohomological shift `M[n]` of a bigraded dg module is a bigraded dg module: the Koszul
twist of the action does not affect weights. -/
instance instBigradedDGModule : BigradedDGModule A (Shift n M) where
  smul_mem {i j} a m ha hm := by
    rw [mem_wgrading_iff'] at hm ⊢
    rw [unmk_smul_eq]
    exact smul_mem_wgrading (twist_mem_wgrading ha) hm


-- @@ L240-240 verbatim
end Shift


-- @@ L242-242 verbatim
namespace InternalShift


-- @@ L244-245 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] {M : Type*} [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]


-- @@ L247-260 expanded
variable (A) in
/-- The internal and cohomological shifts commute: `(M[n])⟨k⟩ ≃ (M⟨k⟩)[n]`. The isomorphism is
the identity on elements; no sign appears, since the Koszul twist `(-1)^{n |a|}` of the action
on `M[n]` only involves the cohomological degree `|a|`, which the internal shift does not
change. -/
def shiftEquiv (n k : ℤ) :
    DGModuleEquiv A (InternalShift k (Shift n M)) (Shift n (InternalShift k M))
    where
  toFun x := Shift.mk n (mk k (Shift.unmk n (unmk k x)))
  invFun y := mk k (Shift.mk n (unmk k (Shift.unmk n y)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L262-263 verbatim
@[simp] theorem shiftEquiv_apply (n k : ℤ) (x : InternalShift k (Shift n M)) :
    shiftEquiv A n k x = Shift.mk n (mk k (Shift.unmk n (unmk k x))) := rfl


-- @@ L265-266 verbatim
@[simp] theorem shiftEquiv_symm_apply (n k : ℤ) (y : Shift n (InternalShift k M)) :
    (shiftEquiv A n k).symm y = mk k (Shift.mk n (unmk k (Shift.unmk n y))) := rfl


-- @@ L268-270 verbatim
theorem mem_wgrading_shiftEquiv_iff [InternalGrading M] (n k : ℤ) {j : ℤ}
    {x : InternalShift k (Shift n M)} : shiftEquiv A n k x ∈ wgrading j ↔ x ∈ wgrading j :=
  Iff.rfl


-- @@ L272-272 verbatim
end InternalShift


-- @@ L274-274 verbatim
/-! ### Internal shifts of morphisms -/


-- @@ L276-276 verbatim
namespace DGModuleHom


-- @@ L278-281 verbatim
variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]


-- @@ L283-283 verbatim
open InternalShift


-- @@ L285-291 expanded
/-- The internal shift of a morphism of dg modules: the same function `M⟨k⟩ → N⟨k⟩`. -/
def internalShift (k : ℤ) (f : DGModuleHom A M N) :
    DGModuleHom A (InternalShift k M) (InternalShift k N)
    where
  toFun m := InternalShift.mk k (f (unmk k m))
  map_add' m m' := map_add f (unmk k m) (unmk k m')
  map_smul' a m := map_smul f a (unmk k m)
  map_mem' hm := f.map_mem hm
  map_d' m := f.map_d (unmk k m)


-- @@ L293-295 expanded
@[simp]
theorem internalShift_apply (k : ℤ) (f : DGModuleHom A M N) (m : M) :
    f.internalShift k (InternalShift.mk k m) = InternalShift.mk k (f m) :=
  rfl


-- @@ L297-298 expanded
theorem unmk_internalShift_apply (k : ℤ) (f : DGModuleHom A M N) (m : InternalShift k M) :
    unmk k (f.internalShift k m) = f (unmk k m) :=
  rfl


-- @@ L300-302 expanded
@[simp]
theorem internalShift_id (k : ℤ) :
    (DGModuleHom.id : DGModuleHom A M M).internalShift k = DGModuleHom.id :=
  rfl


-- @@ L304-306 expanded
@[simp]
theorem internalShift_comp (k : ℤ) (g : DGModuleHom A N P) (f : DGModuleHom A M N) :
    (g.comp f).internalShift k = (g.internalShift k).comp (f.internalShift k) :=
  rfl


-- @@ L308-308 expanded
@[simp]
theorem internalShift_zero (k : ℤ) : (0 : DGModuleHom A M N).internalShift k = 0 :=
  rfl


-- @@ L309-310 expanded
@[simp]
theorem internalShift_add (k : ℤ) (f g : DGModuleHom A M N) :
    (f + g).internalShift k = f.internalShift k + g.internalShift k :=
  rfl


-- @@ L312-316 expanded
/-- The internal shift of a weight-preserving morphism preserves weights. -/
theorem internalShift_mem_wgrading [InternalGrading M] [InternalGrading N] (k : ℤ)
    (f : DGModuleHom A M N) (hf : ∀ {j : ℤ} {m : M}, m ∈ wgrading j → f m ∈ wgrading j) {j : ℤ}
    {m : InternalShift k M} (hm : m ∈ wgrading j) : f.internalShift k m ∈ wgrading j :=
  hf (j := j + k) hm


-- @@ L318-318 verbatim
end DGModuleHom


-- @@ L320-320 verbatim
end DG
