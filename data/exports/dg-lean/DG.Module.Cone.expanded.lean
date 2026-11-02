import DG.Module.Prod
import DG.Module.Shift


-- @@ L4-37 verbatim
/-!
# Mapping cones of morphisms of dg modules

The mapping cone of a morphism `f : M →ᵈᵍ[A] N` is the dg module
`Cone f = M⟦1⟧ ⊕ N` (as a graded `A`-module, the product `Shift 1 M × N` with the
componentwise action, where the action on `M⟦1⟧` is the twisted one) with the differential

  `d (x, y) = (d_{M⟦1⟧} x, f x + d_N y) = (-d_M x, f x + d_N y)`,
i.e. the matrix `(-d_M, 0; f, d_N)` with respect to the decomposition `M⟦1⟧ ⊕ N`. This is
the differential of Mathlib's `CochainComplex.mappingCone` (whose degree-`i` piece is
`F.X (i + 1) ⊞ G.X i`), so the order of the factors follows Mathlib. It is also the mapping
cone `N ⊕ M[1]` with `d = (d_N, f; 0, -d_M)` of `docs/CONVENTIONS.md`, with the two summands
written in the other order.

* `DG.Cone f`: the mapping cone, a `def` (a type synonym for `Shift 1 M × N`) with explicit
  `AddCommGroup`, `Module A`, `DGAddCommGroup` and `DGModule A` instances.
* `DG.Cone.inr f : N →ᵈᵍ[A] Cone f` and `DG.Cone.fstHom f : Cone f →ᵈᵍ[A] Shift 1 M`, the
  morphisms of the standard triangle `M → N → Cone f → M⟦1⟧`, with `fstHom ∘ inr = 0`.
  (Mathlib's standard triangle `CochainComplex.mappingCone.triangle` uses `-fstHom` as its
  third morphism.)
* `DG.Cone.inlLinear f : Shift 1 M →ₗ[A] Cone f` and `DG.Cone.sndLinear f : Cone f →ₗ[A] N`,
  the other two structure maps: `A`-linear, graded of degree `0`, but not chain maps. They
  satisfy `sndLinear ∘ inlLinear = 0`, `sndLinear ∘ inr = id`, `fstHom ∘ inlLinear = id`,
  `inlLinear ∘ fstHom + inr ∘ sndLinear = id`, and `d ∘ inlLinear - inlLinear ∘ d = inr ∘ f`
  (`DG.Cone.d_inlLinear`), expressing that `inlLinear` is a chain map up to the homotopy `f`.
* `DG.Cone.contraction M`: the degree `-1` map `h (x, y) = (y, 0)` on the cone of the identity
  of `M`, with `d ∘ h + h ∘ d = id`: the cone of the identity is contractible.
* `DG.Cone.map`: functoriality, a commutative square `g ∘ f = f' ∘ e` induces
  `Cone f →ᵈᵍ[A] Cone f'`.

The cochain-level structure maps with Mathlib's names and degrees (`DG.Cone.inl`, a
`(-1)`-cochain from `M`; `DG.Cone.fst`, a `1`-cocycle to `M`; `DG.Cone.snd`, a `0`-cochain) and
the universal properties of the cone in terms of them are in `DG.Homotopy.ConeCochain`.
-/


-- @@ L39-39 verbatim
namespace DG


-- @@ L41-43 verbatim
variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]


-- @@ L45-47 expanded
/-- The mapping cone of a morphism `f : M →ᵈᵍ[A] N` of dg modules: the graded `A`-module
`M⟦1⟧ × N` with the differential `d (x, y) = (-d x, f x + d y)`. -/
def Cone (_f : DGModuleHom A M N) : Type _ :=
  Shift 1 M × N


-- @@ L49-49 verbatim
namespace Cone


-- @@ L51-51 verbatim
open Shift


-- @@ L53-53 expanded
variable (f : DGModuleHom A M N)


-- @@ L55-55 verbatim
instance : AddCommGroup (Cone f) := inferInstanceAs (AddCommGroup (Shift 1 M × N))


-- @@ L57-57 verbatim
instance : Module A (Cone f) := inferInstanceAs (Module A (Shift 1 M × N))


-- @@ L59-61 verbatim
/-- The inclusion of `M⟦1⟧` into the cone, `x ↦ (x, 0)`: `A`-linear and graded of degree `0`,
but not a chain map (see `Cone.d_inl`). -/
def inlLinear : Shift 1 M →ₗ[A] Cone f := LinearMap.inl A (Shift 1 M) N


-- @@ L63-65 verbatim
/-- The projection of the cone onto `N`, `(x, y) ↦ y`: `A`-linear and graded of degree `0`,
but not a chain map (see `Cone.snd_d`). -/
def sndLinear : Cone f →ₗ[A] N := LinearMap.snd A (Shift 1 M) N


-- @@ L67-69 verbatim
/-- The inclusion of `N` into the cone, `y ↦ (0, y)`, as an `A`-linear map; see `Cone.inr` for
the morphism of dg modules. -/
def inrLinear : N →ₗ[A] Cone f := LinearMap.inr A (Shift 1 M) N


-- @@ L71-73 verbatim
/-- The projection of the cone onto `M⟦1⟧`, `(x, y) ↦ x`, as an `A`-linear map; see `Cone.fst`
for the morphism of dg modules. -/
def fstLinear : Cone f →ₗ[A] Shift 1 M := LinearMap.fst A (Shift 1 M) N


-- @@ L75-80 verbatim
/-- The differential of the mapping cone, `d (x, y) = (d_{M⟦1⟧} x, f x + d y)`, as an additive
map. -/
def dAddMonoidHom : Cone f →+ Cone f :=
  ((d : Shift 1 M →+ Shift 1 M).comp (AddMonoidHom.fst (Shift 1 M) N)).prod
    ((f : M →+ N).comp ((unmk 1).toAddMonoidHom.comp (AddMonoidHom.fst (Shift 1 M) N)) +
      (d : N →+ N).comp (AddMonoidHom.snd (Shift 1 M) N))


-- @@ L82-95 verbatim
instance : DGAddCommGroup (Cone f) where
  grading := grading (M := Shift 1 M × N)
  decomposition := DGAddCommGroup.decomposition (M := Shift 1 M × N)
  d := dAddMonoidHom f
  d_mem' {k p} hp := by
    have hp' : fstLinear f p ∈ grading k ∧ sndLinear f p ∈ grading k := hp
    exact ⟨d_mem hp'.1, add_mem (f.map_mem (unmk_mem_grading hp'.1)) (d_mem hp'.2)⟩
  d_d' p := by
    apply Prod.ext
    · exact d_d _
    · change f (unmk 1 (d (fstLinear f p))) +
        d (f (unmk 1 (fstLinear f p)) + d (sndLinear f p)) = 0
      rw [unmk_d, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul, map_neg, d_add, d_d,
        add_zero, f.map_d, neg_add_cancel]


-- @@ L97-105 expanded
/-- The inclusion of `N` into the cone, `y ↦ (0, y)`, as a morphism of dg modules. -/
def inr : DGModuleHom A N (Cone f) where
  __ := inrLinear f
  map_mem' hy := ⟨zero_mem _, hy⟩
  map_d'
    y := by
    apply Prod.ext
    · exact (d_zero (M := Shift 1 M)).symm
    · change d y = f (unmk 1 0) + d y
      rw [unmk_zero, map_zero, zero_add]


-- @@ L107-111 expanded
/-- The projection of the cone onto `M⟦1⟧`, `(x, y) ↦ x`, as a morphism of dg modules. -/
def fstHom : DGModuleHom A (Cone f) (Shift 1 M)
    where
  __ := fstLinear f
  map_mem' hp := hp.1
  map_d' _ := rfl


-- @@ L113-113 verbatim
/-! ### Evaluation lemmas -/


-- @@ L115-115 verbatim
variable {f}


-- @@ L117-117 verbatim
@[simp] theorem fstHom_inlLinear (x : Shift 1 M) : fstHom f (inlLinear f x) = x := rfl

-- @@ L118-118 verbatim
@[simp] theorem sndLinear_inlLinear (x : Shift 1 M) : sndLinear f (inlLinear f x) = 0 := rfl

-- @@ L119-119 verbatim
@[simp] theorem fstHom_inr (y : N) : fstHom f (inr f y) = 0 := rfl

-- @@ L120-120 verbatim
@[simp] theorem sndLinear_inr (y : N) : sndLinear f (inr f y) = y := rfl


-- @@ L122-122 verbatim
theorem fstLinear_apply (p : Cone f) : fstLinear f p = fstHom f p := rfl

-- @@ L123-123 verbatim
theorem inrLinear_apply (y : N) : inrLinear f y = inr f y := rfl


-- @@ L125-128 verbatim
@[ext]
theorem ext {p q : Cone f} (h₁ : fstHom f p = fstHom f q)
    (h₂ : sndLinear f p = sndLinear f q) : p = q :=
  Prod.ext h₁ h₂


-- @@ L130-132 verbatim
theorem inlLinear_fstHom_add_inr_sndLinear (p : Cone f) :
    inlLinear f (fstHom f p) + inr f (sndLinear f p) = p :=
  ext (add_zero _) (zero_add _)


-- @@ L134-136 verbatim
variable (f) in
@[simp]
theorem fstHom_comp_inr : (fstHom f).comp (inr f) = 0 := rfl


-- @@ L138-140 verbatim
theorem mem_grading_iff {k : ℤ} {p : Cone f} :
    p ∈ grading k ↔ fstHom f p ∈ grading k ∧ sndLinear f p ∈ grading k :=
  Iff.rfl


-- @@ L142-144 verbatim
theorem inlLinear_mem {k : ℤ} {x : Shift 1 M} (hx : x ∈ grading k) :
    inlLinear f x ∈ grading k :=
  ⟨hx, zero_mem _⟩


-- @@ L146-147 verbatim
theorem sndLinear_mem {k : ℤ} {p : Cone f} (hp : p ∈ grading k) : sndLinear f p ∈ grading k :=
  hp.2


-- @@ L149-150 verbatim
/-- The first component of the differential of the cone: `fstHom` is a chain map. -/
theorem fstHom_d (p : Cone f) : fstHom f (d p) = d (fstHom f p) := rfl


-- @@ L152-154 verbatim
/-- The second component of the differential of the cone. -/
theorem sndLinear_d (p : Cone f) :
    sndLinear f (d p) = f (unmk 1 (fstHom f p)) + d (sndLinear f p) := rfl


-- @@ L156-158 verbatim
theorem d_inlLinear (x : Shift 1 M) :
    d (inlLinear f x) = inlLinear f (d x) + inr f (f (unmk 1 x)) :=
  ext (by simp) (by simp [sndLinear_d])


-- @@ L160-164 verbatim
/-- `inlLinear` is a chain map up to the homotopy `f`:
`d ∘ inlLinear - inlLinear ∘ d = inr ∘ f`. -/
theorem d_inlLinear_sub_inlLinear_d (x : Shift 1 M) :
    d (inlLinear f x) - inlLinear f (d x) = inr f (f (unmk 1 x)) := by
  rw [d_inlLinear, add_sub_cancel_left]


-- @@ L166-168 verbatim
theorem d_inlLinear_add_inr (x : Shift 1 M) (y : N) :
    d (inlLinear f x + inr f y) = inlLinear f (d x) + inr f (f (unmk 1 x) + d y) :=
  ext (by simp) (by simp [sndLinear_d])


-- @@ L170-170 verbatim
/-! ### The dg module structure -/


-- @@ L172-172 verbatim
section DGModule


-- @@ L174-174 verbatim
variable [DGModule A M] [DGModule A N]


-- @@ L176-184 verbatim
instance : DGModule A (Cone f) where
  smul_mem {i j} a p ha hp :=
    ⟨smul_mem_grading ha hp.1, smul_mem_grading ha hp.2⟩
  d_smul' {i} a ha p := by
    refine ext ?_ ?_
    · simp only [fstHom_d, map_add, map_smul, Units.smul_def, map_zsmul, d_smul ha]
    · simp only [sndLinear_d, map_add, map_smul, Units.smul_def, map_zsmul, unmk_smul ha, one_mul,
        d_smul ha, smul_add]
      abel


-- @@ L186-186 verbatim
end DGModule


-- @@ L188-188 verbatim
/-! ### The cone of the identity is contractible -/


-- @@ L190-190 verbatim
section Contraction


-- @@ L192-192 verbatim
variable (M)


-- @@ L194-198 expanded
/-- The contracting homotopy `h (x, y) = (y, 0)` of the cone of the identity of `M`: a map of
degree `-1` with `d ∘ h + h ∘ d = id` (`Cone.d_contraction_add_contraction_d`). It is graded
`A`-linear up to the Koszul sign, `h (a • p) = (-1)^{|a|} a • h p` (`Cone.contraction_smul`). -/
def contraction :
    Cone (DGModuleHom.id : DGModuleHom A M M) →+ Cone (DGModuleHom.id : DGModuleHom A M M) :=
  ((inlLinear _).toAddMonoidHom.comp (Shift.mk 1).toAddMonoidHom).comp (sndLinear _).toAddMonoidHom


-- @@ L200-200 verbatim
variable {M}


-- @@ L202-203 expanded
theorem contraction_apply (p : Cone (DGModuleHom.id : DGModuleHom A M M)) :
    contraction M p = inlLinear _ (Shift.mk 1 (sndLinear _ p)) :=
  rfl


-- @@ L205-213 expanded
/-- The cone of the identity is contractible: `d ∘ h + h ∘ d = id`. -/
theorem d_contraction_add_contraction_d (p : Cone (DGModuleHom.id : DGModuleHom A M M)) :
    d (contraction M p) + contraction M (d p) = p :=
  by
  refine ext ?_ ?_
  · simp only [contraction_apply, map_add, fstHom_d, fstHom_inlLinear, sndLinear_d, d_mk,
      DGModuleHom.id_apply, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul, mk_neg,
      mk_unmk]
    abel
  · simp [contraction_apply, sndLinear_d]


-- @@ L215-218 expanded
/-- The contracting homotopy has degree `-1`. -/
theorem contraction_mem {k : ℤ} {p : Cone (DGModuleHom.id : DGModuleHom A M M)}
    (hp : p ∈ grading k) : contraction M p ∈ grading (k - 1) :=
  inlLinear_mem (mk_mem_grading (sndLinear_mem hp))


-- @@ L220-225 expanded
/-- The contracting homotopy is graded `A`-linear of degree `-1`, with the Koszul sign. -/
theorem contraction_smul {i : ℤ} {a : A} (ha : a ∈ grading i)
    (p : Cone (DGModuleHom.id : DGModuleHom A M M)) :
    contraction M (a • p) = koszulSign i • (a • contraction M p) := by
  rw [contraction_apply, contraction_apply, map_smul, mk_smul ha, one_mul, Units.smul_def,
    map_zsmul, map_smul, ← Units.smul_def]


-- @@ L227-227 verbatim
end Contraction


-- @@ L229-229 verbatim
/-! ### Functoriality -/


-- @@ L231-231 verbatim
section Map


-- @@ L233-235 expanded
variable {M' N' : Type*} [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [AddCommGroup N']
  [DGAddCommGroup N'] [Module A N'] {f' : DGModuleHom A M' N'} (e : DGModuleHom A M M')
  (g : DGModuleHom A N N')


-- @@ L237-248 expanded
/-- A commutative square `g ∘ f = f' ∘ e` induces a morphism of mapping cones,
`(x, y) ↦ (e x, g y)`. -/
def map (h : g.comp f = f'.comp e) : DGModuleHom A (Cone f) (Cone f')
    where
  __ := (e.shift 1).toLinearMap.prodMap g.toLinearMap
  map_mem' hp := ⟨(e.shift 1).map_mem hp.1, g.map_mem hp.2⟩
  map_d'
    p := by
    refine ext ?_ ?_
    · exact ((e.shift 1).map_d _)
    · change
        g (f (unmk 1 (fstHom f p)) + d (sndLinear f p)) =
          f' (unmk 1 (e.shift 1 (fstHom f p))) + d (g (sndLinear f p))
      rw [map_add, g.map_d, DGModuleHom.unmk_shift_apply, ← DGModuleHom.comp_apply, h,
        DGModuleHom.comp_apply]


-- @@ L250-252 verbatim
@[simp]
theorem fstHom_map (h : g.comp f = f'.comp e) (p : Cone f) :
    fstHom f' (map e g h p) = e.shift 1 (fstHom f p) := rfl


-- @@ L254-256 verbatim
@[simp]
theorem sndLinear_map (h : g.comp f = f'.comp e) (p : Cone f) :
    sndLinear f' (map e g h p) = g (sndLinear f p) := rfl


-- @@ L258-260 verbatim
theorem map_comp_inr (h : g.comp f = f'.comp e) :
    (map e g h).comp (inr f) = (inr f').comp g :=
  DGModuleHom.ext fun y => ext (by simp) rfl


-- @@ L262-264 verbatim
theorem fstHom_comp_map (h : g.comp f = f'.comp e) :
    (fstHom f').comp (map e g h) = (e.shift 1).comp (fstHom f) :=
  rfl


-- @@ L266-266 verbatim
end Map


-- @@ L268-268 verbatim
end Cone


-- @@ L270-270 verbatim
end DG
