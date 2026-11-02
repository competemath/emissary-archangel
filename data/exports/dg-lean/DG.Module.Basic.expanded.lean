import Mathlib.Algebra.GradedMulAction
import DG.Algebra.Basic


-- @@ L4-19 verbatim
/-!
# Differential graded modules

* `DGModule A M`: a `Prop`-valued mixin on a dg abelian group `M` (`DGAddCommGroup M`) with a
  module structure `Module A M` over a dg ring `A`, saying that the action is graded
  (`Aⁱ • Mʲ ⊆ Mⁱ⁺ʲ`) and satisfies the signed Leibniz rule
  `d (a • m) = d a • m + (-1)^{|a|} • (a • d m)`.
* `DGModuleHom A M N` (notation `M →ᵈᵍ[A] N`): `A`-linear maps of degree `0` commuting with the
  differentials — the morphisms of the category of dg modules.

A dg ring is a dg module over itself (`DG.DGModule.regular`). If `A` is a dg `R`-algebra and
`M` is a dg `A`-module with a compatible `R`-module structure (`IsScalarTower R A M`), then
`d` is `R`-linear and the graded pieces are `R`-submodules.

Right modules and bimodules are further mixins (`DG.Module.Right`).
-/


-- @@ L21-21 verbatim
open DirectSum


-- @@ L23-23 verbatim
namespace DG


-- @@ L25-32 verbatim
/-- A left differential graded module over a dg ring `A`: a dg abelian group `M` with an
`A`-module structure such that the action is graded and satisfies the signed Leibniz rule
`d (a • m) = d a • m + (-1)^{|a|} • (a • d m)`. -/
class DGModule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] : Prop
    extends SetLike.GradedSMul (grading (M := A)) (grading (M := M)) where
  d_smul' : ∀ {n : ℤ} {a : A}, a ∈ grading n → ∀ m : M,
    d (a • m) = d a • m + koszulSign n • (a • d m)


-- @@ L34-34 verbatim
section DGModule


-- @@ L36-37 verbatim
variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]


-- @@ L39-41 verbatim
theorem smul_mem_grading {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i) (hm : m ∈ grading j) :
    a • m ∈ grading (i + j) :=
  SetLike.GradedSMul.smul_mem ha hm


-- @@ L43-46 verbatim
/-- The signed Leibniz rule for the action. -/
theorem d_smul {n : ℤ} {a : A} (ha : a ∈ grading n) (m : M) :
    d (a • m) = d a • m + koszulSign n • (a • d m) :=
  DGModule.d_smul' ha m


-- @@ L48-50 verbatim
theorem d_smul_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (m : M) :
    d (a • m) = d a • m + a • d m := by
  rw [d_smul ha, koszulSign_even hn, one_smul]


-- @@ L52-54 verbatim
theorem d_smul_of_odd {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Odd n) (m : M) :
    d (a • m) = d a • m - a • d m := by
  rw [d_smul ha, koszulSign_odd hn, Units.neg_smul, one_smul, sub_eq_add_neg]


-- @@ L56-58 verbatim
theorem d_smul_of_mem_zero {a : A} (ha : a ∈ grading 0) (m : M) :
    d (a • m) = d a • m + a • d m :=
  d_smul_of_even ha Even.zero m


-- @@ L60-63 verbatim
/-- For a cocycle `a`, `d (a • m) = (-1)^{|a|} • (a • d m)`. -/
theorem d_smul_of_d_eq_zero {n : ℤ} {a : A} (ha : a ∈ grading n) (hda : d a = 0) (m : M) :
    d (a • m) = koszulSign n • (a • d m) := by
  rw [d_smul ha, hda, zero_smul, zero_add]


-- @@ L65-70 verbatim
/-- For a cocycle `m`, `d (a • m) = d a • m` for every `a`. -/
theorem d_smul_of_d_eq_zero_right {m : M} (hm : d m = 0) (a : A) : d (a • m) = d a • m := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [d_smul a.2, hm, smul_zero, smul_zero, add_zero]
  | h_add a a' ha ha' => rw [add_smul, d_add, ha, ha', d_add, add_smul]


-- @@ L72-75 verbatim
/-- A dg ring is a dg module over itself. -/
instance DGModule.regular {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] : DGModule A A where
  smul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  d_smul' ha b := d_mul ha b


-- @@ L77-77 verbatim
end DGModule


-- @@ L79-79 verbatim
section Ground


-- @@ L81-83 verbatim
variable (R : Type*) (A : Type*) {M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M] [DGModule A M] [Module R M] [IsScalarTower R A M]


-- @@ L85-85 verbatim
include A


-- @@ L87-91 verbatim
variable {R} in
theorem DGModule.ground_smul_mem {n : ℤ} (r : R) {m : M} (hm : m ∈ grading n) :
    r • m ∈ grading n := by
  rw [← algebraMap_smul A r m]
  simpa using smul_mem_grading (algebraMap_mem_grading R (A := A) r) hm


-- @@ L93-98 verbatim
variable {R} in
/-- The differential of a dg module over a dg `R`-algebra is `R`-linear. -/
theorem d_ground_smul (r : R) (m : M) : d (r • m) = r • d m := by
  rw [← algebraMap_smul A r m, d_smul (algebraMap_mem_grading R (A := A) r), d_algebraMap,
    zero_smul,
    zero_add, koszulSign, Int.negOnePow_zero, one_smul, algebraMap_smul]


-- @@ L100-100 verbatim
variable (M)


-- @@ L102-105 verbatim
/-- The graded pieces of a dg module over a dg `R`-algebra, as `R`-submodules. -/
def DGModule.gradingSubmodule (n : ℤ) : Submodule R M where
  __ := grading (M := M) n
  smul_mem' r _ hm := DGModule.ground_smul_mem A r hm


-- @@ L107-110 verbatim
@[simp]
theorem DGModule.mem_gradingSubmodule {n : ℤ} {m : M} :
    m ∈ DGModule.gradingSubmodule R A M n ↔ m ∈ grading n :=
  Iff.rfl


-- @@ L112-116 verbatim
instance DGModule.decompositionSubmodule :
    DirectSum.Decomposition (DGModule.gradingSubmodule R A M) where
  decompose' := DirectSum.decompose (grading (M := M))
  left_inv := DirectSum.Decomposition.left_inv (ℳ := grading (M := M))
  right_inv := DirectSum.Decomposition.right_inv (ℳ := grading (M := M))


-- @@ L118-121 verbatim
/-- The differential of a dg module over a dg `R`-algebra as an `R`-linear map. -/
def DGModule.dLinear : M →ₗ[R] M where
  __ := (d : M →+ M)
  map_smul' := d_ground_smul A


-- @@ L123-124 verbatim
@[simp]
theorem DGModule.dLinear_apply (m : M) : DGModule.dLinear R A M m = d m := rfl


-- @@ L126-126 verbatim
end Ground


-- @@ L128-134 verbatim
/-- A morphism of dg `A`-modules: an `A`-linear map of degree `0` commuting with the
differentials. -/
structure DGModuleHom (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] extends M →ₗ[A] N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)


-- @@ L136-137 verbatim
@[inherit_doc]
notation:25 M " →ᵈᵍ[" A "] " N => DGModuleHom A M N


-- @@ L139-139 verbatim
namespace DGModuleHom


-- @@ L141-144 verbatim
variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]


-- @@ L146-151 expanded
instance : FunLike (DGModuleHom A M N) M N
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := g
    congr


-- @@ L153-155 expanded
instance : LinearMapClass (DGModuleHom A M N) A M N
    where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'


-- @@ L157-158 expanded
@[simp]
theorem coe_toLinearMap (f : DGModuleHom A M N) : ⇑f.toLinearMap = f :=
  rfl


-- @@ L160-161 expanded
@[simp]
theorem toLinearMap_apply (f : DGModuleHom A M N) (m : M) : f.toLinearMap m = f m :=
  rfl


-- @@ L163-165 expanded
@[ext]
theorem ext {f g : DGModuleHom A M N} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h


-- @@ L167-169 expanded
theorem toLinearMap_injective :
    Function.Injective (DGModuleHom.toLinearMap : (DGModuleHom A M N) → M →ₗ[A] N) := fun _ _ h =>
  ext fun m => congrArg (fun φ : M →ₗ[A] N => φ m) h


-- @@ L171-172 expanded
theorem map_mem (f : DGModuleHom A M N) {n : ℤ} {m : M} (hm : m ∈ grading n) : f m ∈ grading n :=
  f.map_mem' hm


-- @@ L174-176 expanded
@[simp]
theorem map_d (f : DGModuleHom A M N) (m : M) : f (d m) = d (f m) :=
  f.map_d' m


-- @@ L178-182 expanded
/-- The identity morphism. -/
def id : DGModuleHom A M M where
  __ := LinearMap.id
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L184-185 expanded
@[simp]
theorem id_apply (m : M) : (DGModuleHom.id : DGModuleHom A M M) m = m :=
  rfl


-- @@ L187-191 expanded
/-- Composition of morphisms. -/
def comp (g : DGModuleHom A N P) (f : DGModuleHom A M N) : DGModuleHom A M P
    where
  __ := g.toLinearMap.comp f.toLinearMap
  map_mem' hm := g.map_mem (f.map_mem hm)
  map_d' m := by simp


-- @@ L193-194 expanded
@[simp]
theorem comp_apply (g : DGModuleHom A N P) (f : DGModuleHom A M N) (m : M) : g.comp f m = g (f m) :=
  rfl


-- @@ L196-197 expanded
@[simp]
theorem comp_id (f : DGModuleHom A M N) : f.comp DGModuleHom.id = f :=
  rfl


-- @@ L199-200 expanded
@[simp]
theorem id_comp (f : DGModuleHom A M N) : DGModuleHom.id.comp f = f :=
  rfl


-- @@ L202-204 expanded
theorem comp_assoc {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q]
    (h : DGModuleHom A P Q) (g : DGModuleHom A N P) (f : DGModuleHom A M N) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl


-- @@ L206-209 expanded
instance : Zero (DGModuleHom A M N) :=
  ⟨{ (0 : M →ₗ[A] N) with
      map_mem' := fun _ => zero_mem _
      map_d' := fun _ => by simp }⟩


-- @@ L211-215 expanded
instance : Add (DGModuleHom A M N) :=
  ⟨fun f g =>
    {
      f.toLinearMap +
        g.toLinearMap with
      map_mem' := fun hm => add_mem (f.map_mem hm) (g.map_mem hm)
      map_d' := fun m => by simp [d_add] }⟩


-- @@ L217-221 expanded
instance : Neg (DGModuleHom A M N) :=
  ⟨fun f =>
    { -f.toLinearMap with
      map_mem' := fun hm => neg_mem (f.map_mem hm)
      map_d' := fun m => by simp [d_neg] }⟩


-- @@ L223-227 expanded
instance : Sub (DGModuleHom A M N) :=
  ⟨fun f g =>
    {
      f.toLinearMap -
        g.toLinearMap with
      map_mem' := fun hm => sub_mem (f.map_mem hm) (g.map_mem hm)
      map_d' := fun m => by simp [d_sub] }⟩


-- @@ L229-229 expanded
@[simp]
theorem zero_apply (m : M) : (0 : DGModuleHom A M N) m = 0 :=
  rfl


-- @@ L230-230 expanded
@[simp]
theorem add_apply (f g : DGModuleHom A M N) (m : M) : (f + g) m = f m + g m :=
  rfl


-- @@ L231-231 expanded
@[simp]
theorem neg_apply (f : DGModuleHom A M N) (m : M) : (-f) m = -f m :=
  rfl


-- @@ L232-232 expanded
@[simp]
theorem sub_apply (f g : DGModuleHom A M N) (m : M) : (f - g) m = f m - g m :=
  rfl


-- @@ L234-238 expanded
instance : SMul ℕ (DGModuleHom A M N) :=
  ⟨fun k f =>
    { k • f.toLinearMap with
      map_mem' := fun hm => nsmul_mem (f.map_mem hm) k
      map_d' := fun m => by simp [d_nsmul] }⟩


-- @@ L240-244 expanded
instance : SMul ℤ (DGModuleHom A M N) :=
  ⟨fun k f =>
    { k • f.toLinearMap with
      map_mem' := fun hm => zsmul_mem (f.map_mem hm) k
      map_d' := fun m => by simp [d_zsmul] }⟩


-- @@ L246-246 expanded
@[simp]
theorem nsmul_apply (k : ℕ) (f : DGModuleHom A M N) (m : M) : (k • f) m = k • f m :=
  rfl


-- @@ L247-247 expanded
@[simp]
theorem zsmul_apply (k : ℤ) (f : DGModuleHom A M N) (m : M) : (k • f) m = k • f m :=
  rfl


-- @@ L249-251 expanded
instance : AddCommGroup (DGModuleHom A M N) :=
  toLinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)


-- @@ L253-253 expanded
@[simp]
theorem toLinearMap_zero : (0 : DGModuleHom A M N).toLinearMap = 0 :=
  rfl


-- @@ L254-255 expanded
@[simp]
theorem toLinearMap_add (f g : DGModuleHom A M N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl


-- @@ L256-256 expanded
@[simp]
theorem toLinearMap_neg (f : DGModuleHom A M N) : (-f).toLinearMap = -f.toLinearMap :=
  rfl


-- @@ L257-258 expanded
@[simp]
theorem toLinearMap_sub (f g : DGModuleHom A M N) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  rfl


-- @@ L260-261 expanded
theorem comp_add (g : DGModuleHom A N P) (f f' : DGModuleHom A M N) :
    g.comp (f + f') = g.comp f + g.comp f' := by ext; simp


-- @@ L262-263 expanded
theorem add_comp (g g' : DGModuleHom A N P) (f : DGModuleHom A M N) :
    (g + g').comp f = g.comp f + g'.comp f := by ext; simp


-- @@ L264-264 expanded
@[simp]
theorem comp_zero (g : DGModuleHom A N P) : g.comp (0 : DGModuleHom A M N) = 0 := by ext; simp


-- @@ L265-265 expanded
@[simp]
theorem zero_comp (f : DGModuleHom A M N) : (0 : DGModuleHom A N P).comp f = 0 := by ext; simp


-- @@ L267-271 expanded
/-- A morphism of dg modules is a graded map of degree `0`: it preserves each `Mⁿ`. -/
def restrict (f : DGModuleHom A M N) (n : ℤ) : grading (M := M) n →+ grading (M := N) n
    where
  toFun m := ⟨f m, f.map_mem m.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp


-- @@ L273-275 expanded
@[simp]
theorem coe_restrict_apply (f : DGModuleHom A M N) (n : ℤ) (m : grading (M := M) n) :
    (f.restrict n m : N) = f m :=
  rfl


-- @@ L277-279 expanded
theorem restrict_comp_dHom (f : DGModuleHom A M N) (n : ℤ) :
    (f.restrict (n + 1)).comp (dHom M n) = (dHom N n).comp (f.restrict n) := by ext; simp


-- @@ L281-281 verbatim
end DGModuleHom


-- @@ L283-283 verbatim
end DG
