import DG.Module.Basic


-- @@ L3-22 verbatim
/-!
# Morphisms of dg rings and dg algebras; restriction of scalars

* `DGRingHom A B` (notation `A →ᵈᵍ+* B`): ring homomorphisms of degree `0` commuting with the
  differentials, the morphisms of dg rings.
* `DGAlgHom R A B` (notation `A →ᵈᵍₐ[R] B`): `R`-algebra homomorphisms of degree `0` commuting
  with the differentials, the morphisms of dg `R`-algebras.
* `RestrictScalars φ M`: restriction of scalars along `φ : A →ᵈᵍ+* B`. For a dg `B`-module `M`,
  the `A`-module `Module.compHom M φ.toRingHom` is a dg `A`-module (`DG.DGModule.compHom`);
  `RestrictScalars φ M` is a type synonym for `M` carrying this structure, and
  `DGModuleHom.restrictScalars φ` is the induced map on morphisms.

## Implementation notes

`RestrictScalars φ M` follows Mathlib's `RestrictScalars R S M`: a type synonym rather than a
local instance, so that `M` can carry its dg `B`-module structure and the restricted dg
`A`-module structure simultaneously without instance diamonds. Since the restriction is along
an explicit morphism `φ` rather than along an `Algebra` instance, the synonym is indexed by `φ`.
The underlying dg abelian group of `RestrictScalars φ M` is definitionally that of `M`.
-/


-- @@ L24-24 verbatim
open DirectSum


-- @@ L26-26 verbatim
namespace DG


-- @@ L28-33 verbatim
/-- A morphism of dg rings: a ring homomorphism of degree `0` commuting with the
differentials. -/
structure DGRingHom (A B : Type*) [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
    extends A →+* B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)


-- @@ L35-36 verbatim
@[inherit_doc]
notation:25 A " →ᵈᵍ+* " B => DGRingHom A B


-- @@ L38-38 verbatim
namespace DGRingHom


-- @@ L40-41 verbatim
variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [Ring C] [DGAddCommGroup C]


-- @@ L43-50 expanded
instance : FunLike (DGRingHom A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h


-- @@ L52-56 expanded
instance : RingHomClass (DGRingHom A B) A B
    where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'


-- @@ L58-59 expanded
@[simp]
theorem coe_toRingHom (f : DGRingHom A B) : ⇑f.toRingHom = f :=
  rfl


-- @@ L61-62 expanded
@[simp]
theorem toRingHom_apply (f : DGRingHom A B) (a : A) : f.toRingHom a = f a :=
  rfl


-- @@ L64-66 expanded
@[ext]
theorem ext {f g : DGRingHom A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h


-- @@ L68-70 expanded
theorem toRingHom_injective :
    Function.Injective (DGRingHom.toRingHom : (DGRingHom A B) → A →+* B) := fun _ _ h =>
  ext fun a => congrArg (fun φ : A →+* B => φ a) h


-- @@ L72-73 expanded
theorem map_mem (f : DGRingHom A B) {n : ℤ} {a : A} (ha : a ∈ grading n) : f a ∈ grading n :=
  f.map_mem' ha


-- @@ L75-77 expanded
@[simp]
theorem map_d (f : DGRingHom A B) (a : A) : f (d a) = d (f a) :=
  f.map_d' a


-- @@ L79-84 expanded
/-- A morphism of dg rings commutes with taking homogeneous components. -/
theorem decompose_apply (f : DGRingHom A B) (a : A) (n : ℤ) :
    (decompose (grading (M := B)) (f a) n : B) = f (decompose (grading (M := A)) a n : A) :=
  by
  have h :=
    decompose_map (k := 0) f.toRingHom.toAddMonoidHom (fun ha => by simpa using f.map_mem ha) a n
  rwa [add_zero] at h


-- @@ L86-90 expanded
/-- The identity morphism. -/
def id : DGRingHom A A where
  __ := RingHom.id A
  map_mem' ha := ha
  map_d' _ := rfl


-- @@ L92-93 expanded
@[simp]
theorem id_apply (a : A) : (DGRingHom.id : DGRingHom A A) a = a :=
  rfl


-- @@ L95-99 expanded
/-- Composition of morphisms. -/
def comp (g : DGRingHom B C) (f : DGRingHom A B) : DGRingHom A C
    where
  __ := g.toRingHom.comp f.toRingHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_d' a := by simp


-- @@ L101-102 expanded
@[simp]
theorem comp_apply (g : DGRingHom B C) (f : DGRingHom A B) (a : A) : g.comp f a = g (f a) :=
  rfl


-- @@ L104-105 expanded
@[simp]
theorem comp_id (f : DGRingHom A B) : f.comp DGRingHom.id = f :=
  rfl


-- @@ L107-108 expanded
@[simp]
theorem id_comp (f : DGRingHom A B) : DGRingHom.id.comp f = f :=
  rfl


-- @@ L110-111 expanded
theorem comp_assoc {D : Type*} [Ring D] [DGAddCommGroup D] (h : DGRingHom C D) (g : DGRingHom B C)
    (f : DGRingHom A B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl


-- @@ L113-117 expanded
/-- A morphism of dg rings maps cocycles to cocycles. -/
theorem map_cocycles (f : DGRingHom A B) {n : ℤ} {a : A} (ha : a ∈ cocycles A n) :
    f a ∈ cocycles B n := by
  rw [mem_cocycles] at ha ⊢
  exact ⟨f.map_mem ha.1, by rw [← map_d, ha.2, map_zero]⟩


-- @@ L119-123 expanded
/-- A morphism of dg rings maps coboundaries to coboundaries. -/
theorem map_coboundaries (f : DGRingHom A B) {n : ℤ} {a : A} (ha : a ∈ coboundaries A n) :
    f a ∈ coboundaries B n := by
  obtain ⟨a', ha', rfl⟩ := ha
  exact ⟨f a', f.map_mem ha', (map_d f a').symm⟩


-- @@ L125-125 verbatim
end DGRingHom


-- @@ L127-132 verbatim
/-- A morphism of dg `R`-algebras: an `R`-algebra homomorphism of degree `0` commuting with the
differentials. -/
structure DGAlgHom (R A B : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
    [Ring B] [Algebra R B] [DGAddCommGroup B] extends A →ₐ[R] B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)


-- @@ L134-135 verbatim
@[inherit_doc]
notation:25 A " →ᵈᵍₐ[" R "] " B => DGAlgHom R A B


-- @@ L137-137 verbatim
namespace DGAlgHom


-- @@ L139-140 verbatim
variable {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [Ring C] [Algebra R C] [DGAddCommGroup C]


-- @@ L142-149 expanded
instance : FunLike (DGAlgHom R A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h


-- @@ L151-156 expanded
instance : AlgHomClass (DGAlgHom R A B) R A B
    where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'


-- @@ L158-159 expanded
@[simp]
theorem coe_toAlgHom (f : DGAlgHom R A B) : ⇑f.toAlgHom = f :=
  rfl


-- @@ L161-162 expanded
@[simp]
theorem toAlgHom_apply (f : DGAlgHom R A B) (a : A) : f.toAlgHom a = f a :=
  rfl


-- @@ L164-166 expanded
@[ext]
theorem ext {f g : DGAlgHom R A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h


-- @@ L168-170 expanded
theorem toAlgHom_injective :
    Function.Injective (DGAlgHom.toAlgHom : (DGAlgHom R A B) → A →ₐ[R] B) := fun _ _ h =>
  ext fun a => congrArg (fun φ : A →ₐ[R] B => φ a) h


-- @@ L172-173 expanded
theorem map_mem (f : DGAlgHom R A B) {n : ℤ} {a : A} (ha : a ∈ grading n) : f a ∈ grading n :=
  f.map_mem' ha


-- @@ L175-177 expanded
@[simp]
theorem map_d (f : DGAlgHom R A B) (a : A) : f (d a) = d (f a) :=
  f.map_d' a


-- @@ L179-183 expanded
/-- The underlying morphism of dg rings. -/
def toDGRingHom (f : DGAlgHom R A B) : DGRingHom A B
    where
  __ := f.toAlgHom.toRingHom
  map_mem' := f.map_mem'
  map_d' := f.map_d'


-- @@ L185-186 expanded
@[simp]
theorem coe_toDGRingHom (f : DGAlgHom R A B) : ⇑f.toDGRingHom = f :=
  rfl


-- @@ L188-189 expanded
@[simp]
theorem toDGRingHom_apply (f : DGAlgHom R A B) (a : A) : f.toDGRingHom a = f a :=
  rfl


-- @@ L191-193 expanded
theorem toDGRingHom_injective :
    Function.Injective (DGAlgHom.toDGRingHom : (DGAlgHom R A B) → DGRingHom A B) := fun _ _ h =>
  ext fun a => congrArg (fun φ : DGRingHom A B => φ a) h


-- @@ L195-199 expanded
/-- The identity morphism. -/
def id : DGAlgHom R A A where
  __ := AlgHom.id R A
  map_mem' ha := ha
  map_d' _ := rfl


-- @@ L201-202 expanded
@[simp]
theorem id_apply (a : A) : (DGAlgHom.id : DGAlgHom R A A) a = a :=
  rfl


-- @@ L204-208 expanded
/-- Composition of morphisms. -/
def comp (g : DGAlgHom R B C) (f : DGAlgHom R A B) : DGAlgHom R A C
    where
  __ := g.toAlgHom.comp f.toAlgHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_d' a := by simp


-- @@ L210-211 expanded
@[simp]
theorem comp_apply (g : DGAlgHom R B C) (f : DGAlgHom R A B) (a : A) : g.comp f a = g (f a) :=
  rfl


-- @@ L213-214 expanded
@[simp]
theorem comp_id (f : DGAlgHom R A B) : f.comp DGAlgHom.id = f :=
  rfl


-- @@ L216-217 expanded
@[simp]
theorem id_comp (f : DGAlgHom R A B) : DGAlgHom.id.comp f = f :=
  rfl


-- @@ L219-220 expanded
theorem comp_assoc {D : Type*} [Ring D] [Algebra R D] [DGAddCommGroup D] (h : DGAlgHom R C D)
    (g : DGAlgHom R B C) (f : DGAlgHom R A B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl


-- @@ L222-223 expanded
@[simp]
theorem toDGRingHom_id : (DGAlgHom.id : DGAlgHom R A A).toDGRingHom = DGRingHom.id :=
  rfl


-- @@ L225-227 expanded
@[simp]
theorem toDGRingHom_comp (g : DGAlgHom R B C) (f : DGAlgHom R A B) :
    (g.comp f).toDGRingHom = g.toDGRingHom.comp f.toDGRingHom :=
  rfl


-- @@ L229-229 verbatim
end DGAlgHom


-- @@ L231-231 verbatim
/-! ### Restriction of scalars -/


-- @@ L233-233 verbatim
section RestrictScalars


-- @@ L235-235 verbatim
variable {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]


-- @@ L237-247 expanded
/-- Restriction of scalars along a morphism of dg rings: for a dg `B`-module `M`, the `A`-module
`Module.compHom M φ.toRingHom` (with `a • m = φ a • m`) is a dg `A`-module. -/
theorem DGModule.compHom (φ : DGRingHom A B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M]
    [Module B M] [DGModule B M] :
    letI := Module.compHom M φ.toRingHom
    DGModule A M :=
  letI := Module.compHom M φ.toRingHom
  { smul_mem := fun _ _ _ _ ha hm => smul_mem_grading (A := B) (φ.map_mem ha) hm
    d_smul' := fun ha m =>
      by
      change d (φ _ • m) = φ (d _) • m + _ • (φ _ • d m)
      rw [DGRingHom.map_d, d_smul (φ.map_mem ha)] }


-- @@ L249-252 expanded
/-- A type synonym for `M` carrying the dg `A`-module structure obtained by restricting scalars
along `φ : A →ᵈᵍ+* B`. The underlying dg abelian group is that of `M`. -/
@[nolint unusedArguments]
def RestrictScalars (_φ : DGRingHom A B) (M : Type*) : Type _ :=
  M


-- @@ L254-254 verbatim
namespace RestrictScalars


-- @@ L256-256 verbatim
section AddCommGroup


-- @@ L258-258 expanded
variable (φ : DGRingHom A B) (M : Type*) [AddCommGroup M]


-- @@ L260-260 verbatim
instance : AddCommGroup (RestrictScalars φ M) := inferInstanceAs (AddCommGroup M)


-- @@ L262-262 verbatim
variable {M}


-- @@ L264-265 verbatim
/-- The identity map `RestrictScalars φ M → M`, as an additive equivalence. -/
def addEquiv : RestrictScalars φ M ≃+ M := AddEquiv.refl M


-- @@ L267-268 verbatim
@[simp]
theorem addEquiv_apply (m : RestrictScalars φ M) : addEquiv φ m = m := rfl


-- @@ L270-271 verbatim
@[simp]
theorem addEquiv_symm_apply (m : M) : (addEquiv φ).symm m = m := rfl


-- @@ L273-273 verbatim
end AddCommGroup


-- @@ L275-275 verbatim
section Module


-- @@ L277-277 expanded
variable (φ : DGRingHom A B) (M : Type*) [AddCommGroup M] [Module B M]


-- @@ L279-279 verbatim
instance module : Module A (RestrictScalars φ M) := Module.compHom M φ.toRingHom


-- @@ L281-281 verbatim
variable {M}


-- @@ L283-284 verbatim
theorem smul_def (a : A) (m : RestrictScalars φ M) :
    a • m = (addEquiv φ).symm (φ a • addEquiv φ m) := rfl


-- @@ L286-286 verbatim
end Module


-- @@ L288-288 expanded
variable (φ : DGRingHom A B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module B M]


-- @@ L290-291 verbatim
instance dgAddCommGroup : DGAddCommGroup (RestrictScalars φ M) :=
  inferInstanceAs (DGAddCommGroup M)


-- @@ L293-294 verbatim
instance dgModule [DGModule B M] : DGModule A (RestrictScalars φ M) :=
  DGModule.compHom φ M


-- @@ L296-296 verbatim
end RestrictScalars


-- @@ L298-300 expanded
variable (φ : DGRingHom A B) {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module B M]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [AddCommGroup P] [DGAddCommGroup P] [Module B P]


-- @@ L302-310 expanded
/-- Restriction of scalars along `φ` on morphisms: a morphism of dg `B`-modules is a morphism of
the restricted dg `A`-modules. -/
def DGModuleHom.restrictScalars (f : DGModuleHom B M N) :
    DGModuleHom A (RestrictScalars φ M) (RestrictScalars φ N)
    where
  toFun := f
  map_add' := map_add f
  map_smul' a m := f.map_smul (φ a) m
  map_mem' := f.map_mem
  map_d' := f.map_d


-- @@ L312-314 expanded
@[simp]
theorem DGModuleHom.restrictScalars_apply (f : DGModuleHom B M N) (m : RestrictScalars φ M) :
    f.restrictScalars φ m = f m :=
  rfl


-- @@ L316-318 expanded
@[simp]
theorem DGModuleHom.restrictScalars_id :
    (DGModuleHom.id : DGModuleHom B M M).restrictScalars φ = DGModuleHom.id :=
  rfl


-- @@ L320-322 expanded
@[simp]
theorem DGModuleHom.restrictScalars_comp (g : DGModuleHom B N P) (f : DGModuleHom B M N) :
    (g.comp f).restrictScalars φ = (g.restrictScalars φ).comp (f.restrictScalars φ) :=
  rfl


-- @@ L324-326 expanded
theorem DGModuleHom.restrictScalars_injective :
    Function.Injective (DGModuleHom.restrictScalars φ : (DGModuleHom B M N) → _) := fun _ _ h =>
  DGModuleHom.ext fun m => congrArg (fun g => g m) h


-- @@ L328-328 verbatim
end RestrictScalars


-- @@ L330-330 verbatim
end DG
