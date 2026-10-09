import OAI.RingTheory.Tachikawa.Corner


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa

-- @@ L8-8 verbatim
open CategoryTheory

-- @@ L9-9 verbatim
open scoped ModuleCat.Algebra

-- @@ L10-10 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L11-11 verbatim
namespace TrivialInduction


-- @@ L13-20 verbatim
@[simp] lemma map_zero {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N] :
    map (k := k) (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun Nakayama.map_zero x.2


-- @@ L22-26 verbatim
def functor : ModuleCat R ⥤ ModuleCat (TrivialExtension k R) where
  obj M := ModuleCat.of (TrivialExtension k R) (Obj k R M)
  map f := ModuleCat.ofHom (map f.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp f g := ModuleCat.hom_ext (map_comp f.hom g.hom)


-- @@ L28-38 verbatim
instance : (functor (k := k) (R := R)).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro a
      change x.2 (a.comp (f.hom+g.hom)) = x.2 (a.comp f.hom) + x.2 (a.comp g.hom)
      rw [LinearMap.comp_add, map_add]


-- @@ L40-40 verbatim
end TrivialInduction


-- @@ L42-42 verbatim
namespace C

-- @@ L43-43 verbatim
variable [CharP k 2] (q : k)

-- @@ L44-44 verbatim
abbrev T := TrivialExtension k (C k q)

-- @@ L45-45 verbatim
abbrev TSimple := TrivialInflation k (C k q) (Simple q)


-- @@ L47-48 verbatim
def inducedObj (n : ℕ) : ModuleCat (T q) :=
  ModuleCat.of (T q) (TrivialInduction.Obj k (C k q) (resObj q n))

-- @@ L49-50 verbatim
def inducedD (n : ℕ) : inducedObj q (n+1) ⟶ inducedObj q n :=
  ModuleCat.ofHom (TrivialInduction.map (resD q n).hom)


-- @@ L52-56 verbatim
lemma inducedD_comp (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    inducedD q (n+1) ≫ inducedD q n = 0 := by
  apply ModuleCat.hom_ext
  change (TrivialInduction.map (resD q n).hom).comp (TrivialInduction.map (resD q (n+1)).hom) = 0
  rw [← TrivialInduction.map_comp, (resD_exact q hp n).linearMap_comp_eq_zero, TrivialInduction.map_zero]


-- @@ L58-59 verbatim
def inducedComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : ChainComplex (ModuleCat (T q)) ℕ :=
  ChainComplex.of (inducedObj q) (inducedD q) (inducedD_comp q hp)


-- @@ L61-62 verbatim
lemma inducedComplex_d (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    (inducedComplex q hp).d (n+1) n = inducedD q n := ChainComplex.of_d _ _ _


-- @@ L64-74 verbatim
omit [CharP k 2] in
lemma inducedObj_projective (n : ℕ) : Module.Projective (T q) (inducedObj q n) := by
  cases n <;> dsimp [inducedObj, resObj]
  · let : Module.Finite k (Cf q) := Module.Finite.of_injective
      ((Cf q).subtype.restrictScalars k) Subtype.val_injective
    let : Module.Finite (C k q) (Cf q) := Module.Finite.of_restrictScalars_finite k _ _
    exact TrivialInduction.inducedProjective (k := k) (R := C k q) (M := Cf q)
  · let : Module.Finite k (Ce q) := Module.Finite.of_injective
      ((Ce q).subtype.restrictScalars k) Subtype.val_injective
    let : Module.Finite (C k q) (Ce q) := Module.Finite.of_restrictScalars_finite k _ _
    exact TrivialInduction.inducedProjective (k := k) (R := C k q) (M := Ce q)


-- @@ L76-94 verbatim
omit [CharP k 2] in
lemma inducedObj_finite (n : ℕ) : Module.Finite k (inducedObj q n) := by
  have hf : Module.Finite (T q) (inducedObj q n) := by
    cases n with
    | zero =>
      let : Module.Finite k (Cf q) := Module.Finite.of_injective
        ((Cf q).subtype.restrictScalars k) Subtype.val_injective
      let : Module.Finite k (TrivialInduction.Obj k (C k q) (Cf q)) :=
        TrivialInduction.inducedFinite (k := k) (R := C k q) (M := Cf q)
      exact Module.Finite.of_restrictScalars_finite k (T q)
        (TrivialInduction.Obj k (C k q) (Cf q))
    | succ n =>
      let : Module.Finite k (Ce q) := Module.Finite.of_injective
        ((Ce q).subtype.restrictScalars k) Subtype.val_injective
      let : Module.Finite k (TrivialInduction.Obj k (C k q) (Ce q)) :=
        TrivialInduction.inducedFinite (k := k) (R := C k q) (M := Ce q)
      exact Module.Finite.of_restrictScalars_finite k (T q)
        (TrivialInduction.Obj k (C k q) (Ce q))
  exact Module.Finite.trans (T q) (inducedObj q n)


-- @@ L96-104 verbatim
omit [CharP k 2] in

lemma induced_positive_hom_zero (n : ℕ)
    (f : inducedObj q (n+1) ⟶ ModuleCat.of (T q) (TSimple q)) : f = 0 := by
  apply ModuleCat.hom_ext
  let f₀ : TrivialInduction.Obj k (C k q) (Ce q) →ₗ[T q] TSimple q := f.hom
  change f₀ = 0
  apply (TrivialInflation.homEquiv (k := k) (R := C k q) (M := Ce q) (N := Simple q)).injective
  exact (homCeSimple_zero q (TrivialInflation.restrict f₀)).trans (map_zero _).symm


-- @@ L106-108 verbatim
lemma inducedD_exact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (hn : n ≠ 1) : Function.Exact (inducedD q (n+1)) (inducedD q n) :=
  TrivialInduction.map_exact _ _ (resD_exact q hp n) (nu_resD_exact q hq hp n hn)


-- @@ L110-111 verbatim
def inducedAug : inducedObj q 0 ⟶ ModuleCat.of (T q) (TSimple q) :=
  ModuleCat.ofHom (TrivialInflation.lift (augmentation q))


-- @@ L113-117 verbatim
omit [CharP k 2] in
lemma inducedAug_surjective : Function.Surjective (inducedAug q) := by
  intro x
  obtain ⟨y,hy⟩ := augmentation_surjective q x
  exact ⟨(y,0),hy⟩


-- @@ L119-128 verbatim
omit [CharP k 2] in
lemma inducedAug_exact (hq1 : 1+q ≠ 0) : Function.Exact (inducedD q 0) (inducedAug q) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (exact_augmentation q hq1 x.1).mp hx
    obtain ⟨ψ,hψ⟩ := nu_rhoU_surjective q x.2
    exact ⟨(a,ψ),Prod.ext ha hψ⟩
  · rintro ⟨y,rfl⟩
    exact (exact_augmentation q hq1).apply_apply_eq_zero y.1


-- @@ L130-130 verbatim
end C

-- @@ L131-131 verbatim
end Tachikawa




-- @@ L135-135 verbatim
namespace Tachikawa.TrivialExtension

-- @@ L136-136 verbatim
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]


-- @@ L138-165 verbatim
def scaleDual (H : k) (hH : H ≠ 0) : TrivialExtension k R ≃ₐ[k] TrivialExtension k R where
  toFun a := ⟨a.fst, H • a.snd⟩
  invFun a := ⟨a.fst, H⁻¹ • a.snd⟩
  left_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H⁻¹ • (H • a.snd) = a.snd
      simp [smul_smul, hH]
  right_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H • (H⁻¹ • a.snd) = a.snd
      simp [smul_smul, hH]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · ext r
      change H * (b.snd (r*a.fst) + a.snd (b.fst*r)) =
        H*b.snd (r*a.fst) + H*a.snd (b.fst*r)
      exact mul_add _ _ _
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_add H a.snd b.snd
  commutes' c := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_zero H


-- @@ L167-168 verbatim
@[simp] lemma scaleDual_fst (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).fst = a.fst := rfl

-- @@ L169-170 verbatim
@[simp] lemma scaleDual_snd (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).snd = H • a.snd := rfl

-- @@ L171-175 verbatim
@[simp] lemma scaleDual_inl (H : k) (hH : H ≠ 0) (a : R) :
    scaleDual H hH (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rfl
  · exact smul_zero H

-- @@ L176-177 verbatim
@[simp] lemma scaleDual_inr (H : k) (hH : H ≠ 0) (a : DualBimodule k R) :
    scaleDual H hH (TrivSqZeroExt.inr a) = TrivSqZeroExt.inr (H • a) := rfl


-- @@ L179-179 verbatim
end Tachikawa.TrivialExtension




-- @@ L183-183 verbatim
namespace Tachikawa.TrivialInduction

-- @@ L184-184 verbatim
open CategoryTheory

-- @@ L185-185 verbatim
open scoped ModuleCat.Algebra

-- @@ L186-187 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (H : k) (hH : H ≠ 0) (M : ModuleCat R)


-- @@ L189-190 verbatim
abbrev inverseTwist : ModuleCat (TrivialExtension k R) ⥤ ModuleCat (TrivialExtension k R) :=
  AlgebraInduction.res (TrivialExtension.scaleDual H hH).symm.toAlgHom


-- @@ L192-204 verbatim
def twistComparison : (inverseTwist (R := R) H hH).obj ((functor (k := k)).obj M) ⟶
    (functor (k := k)).obj M :=
  ModuleCat.ofHom (X := (inverseTwist (R := R) H hH).obj ((functor (k := k)).obj M))
    (Y := (functor (k := k)).obj M)
    { toFun := fun x => (x.1,H • x.2)
      map_add' := fun x y => by exact Prod.ext rfl (smul_add H x.2 y.2)
      map_smul' := fun a x => by
        apply Prod.ext
        · rfl
        · change H • (Nakayama.evaluationBilinear (H⁻¹ • a.snd) x.1 + a.fst • x.2) =
            Nakayama.evaluationBilinear a.snd x.1 + a.fst • (H • x.2)
          rw [smul_add,LinearMap.map_smul_of_tower,LinearMap.smul_apply,smul_smul,
            mul_inv_cancel₀ hH,one_smul,smul_comm H a.fst] }


-- @@ L206-214 verbatim
lemma twistComparison_natural {N : ModuleCat R} (f : M ⟶ N) :
    (inverseTwist (R := R) H hH).map ((functor (k := k)).map f) ≫ twistComparison H hH N =
      twistComparison H hH M ≫ (functor (k := k)).map f := by
  apply ModuleCat.hom_ext
  ext x
  apply Prod.ext
  · rfl
  · change H • Nakayama.map f.hom x.2 = Nakayama.map f.hom (H • x.2)
    exact (Nakayama.map f.hom).map_smul_of_tower H x.2 |>.symm


-- @@ L216-216 verbatim
end Tachikawa.TrivialInduction




-- @@ L220-220 verbatim
namespace Tachikawa

-- @@ L221-221 verbatim
open CategoryTheory

-- @@ L222-222 verbatim
open CategoryTheory.Abelian

-- @@ L223-223 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L224-224 verbatim
variable (k : Type*) [CommRing k] [Linear k C]


-- @@ L226-238 verbatim
def extShiftEquiv {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n : ℕ)
    [Subsingleton (Ext S.X₂ Y n)] [Subsingleton (Ext S.X₂ Y (n+1))] :
    Ext S.X₁ Y n ≃ₗ[k] Ext S.X₃ Y (n+1) :=
  LinearEquiv.ofBijective (hS.extClass.precompOfLinear k Y (by omega)) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS Y x (by omega) hx
      rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
      exact hy.symm
    · intro x
      exact Ext.contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _) (by omega))


-- @@ L240-259 verbatim
def extQuotientEquiv {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (h : ∀ n : ℕ, Subsingleton (Ext S.X₁ Y n)) (n : ℕ) :
    Ext S.X₃ Y n ≃ₗ[k] Ext S.X₂ Y n :=
  LinearEquiv.ofBijective ((Ext.mk₀ S.g).precompOfLinear k Y (zero_add n)) (by
    constructor
    · cases n with
      | zero =>
        let : Epi S.g := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y S.g
      | succ n =>
        apply LinearMap.ker_eq_bot.mp
        apply LinearMap.ker_eq_bot'.mpr
        intro x hx
        obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (n₀ := n) (by omega)
        let := h n
        rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
        exact hy.symm
    · intro x
      let := h n
      exact Ext.contravariant_sequence_exact₂ hS Y x (Subsingleton.elim _ _))


-- @@ L261-261 verbatim
end Tachikawa




-- @@ L265-265 verbatim
namespace Tachikawa

-- @@ L266-266 verbatim
open CategoryTheory

-- @@ L267-267 verbatim
universe u v

-- @@ L268-268 verbatim
variable {R : Type u} [Ring R]

-- @@ L269-270 verbatim
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]


-- @@ L272-275 verbatim
def linearShortComplex (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (ModuleCat.hom_ext h.linearMap_comp_eq_zero)


-- @@ L277-282 verbatim
lemma linearShortExact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (linearShortComplex f g h).ShortExact := by
  have hm : Mono (linearShortComplex f g h).f := (ModuleCat.mono_iff_injective _).mpr hf
  have he : Epi (linearShortComplex f g h).g := (ModuleCat.epi_iff_surjective _).mpr hg
  exact ⟨(ShortComplex.moduleCat_exact_iff _).mpr (fun x => (h x).mp)⟩


-- @@ L284-291 verbatim
def kernelRangeComplex (f : M →ₗ[R] N) : ShortComplex (ModuleCat R) :=
  linearShortComplex f.ker.subtype f.rangeRestrict (fun x => by
    change (⟨f x, _⟩ : f.range) = 0 ↔ ∃ y : f.ker, (y:M)=x
    constructor
    · intro h
      exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
    · rintro ⟨y,rfl⟩
      exact Subtype.ext y.property)


-- @@ L293-300 verbatim
lemma kernelRange_shortExact (f : M →ₗ[R] N) : (kernelRangeComplex f).ShortExact := by
  have hm : Mono (kernelRangeComplex f).f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have he : Epi (kernelRangeComplex f).g := (ModuleCat.epi_iff_surjective _).mpr (by
    rintro ⟨y,x,hx⟩
    exact ⟨x,Subtype.ext hx⟩)
  exact ⟨(ShortComplex.moduleCat_exact_iff _).mpr (by
    intro x hx
    exact ⟨⟨x,congrArg Subtype.val hx⟩,rfl⟩)⟩


-- @@ L302-303 verbatim
def kernelSurjectiveComplex (f : M →ₗ[R] N) : ShortComplex (ModuleCat R) :=
  linearShortComplex f.ker.subtype f f.exact_subtype_ker_map


-- @@ L305-307 verbatim
lemma kernelSurjective_shortExact (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (kernelSurjectiveComplex f).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective hf


-- @@ L309-309 verbatim
end Tachikawa




-- @@ L313-313 verbatim
namespace Tachikawa.C

-- @@ L314-314 verbatim
open CategoryTheory

-- @@ L315-315 verbatim
open scoped ModuleCat.Algebra

-- @@ L316-316 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L318-318 verbatim
abbrev InducedBoundaries := LinearMap.range (inducedD q 2).hom

-- @@ L319-319 verbatim
abbrev inducedBoundaryObj := ModuleCat.of (T q) (InducedBoundaries q)


-- @@ L321-335 verbatim
def inducedBoundaryResolution (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (inducedBoundaryObj q) :=
  resolutionOfExact _ (fun n => inducedObj q (n+3)) (fun n => inducedD q (n+3))
    (ModuleCat.ofHom (inducedD q 2).hom.rangeRestrict)
    (fun n => inducedD_exact q hq hp (n+3) (by omega))
    (fun x => by
      constructor
      · intro hx
        exact (inducedD_exact q hq hp 2 (by omega) x).mp (congrArg Subtype.val hx)
      · rintro ⟨y,rfl⟩
        exact Subtype.ext ((inducedD_exact q hq hp 2 (by omega)).apply_apply_eq_zero y))
    (by rintro ⟨x,y,hy⟩; exact ⟨y,Subtype.ext hy⟩)
    (fun n => by
      let := inducedObj_projective q (n+3)
      infer_instance)


-- @@ L337-358 verbatim
lemma inducedBoundary_ext_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Subsingleton (Abelian.Ext (inducedBoundaryObj q) (ModuleCat.of (T q) (TSimple q)) n) := by
  cases n with
  | zero =>
    have : Subsingleton (inducedBoundaryObj q ⟶ ModuleCat.of (T q) (TSimple q)) := by
      apply subsingleton_of_forall_eq 0
      intro f
      have hh : ModuleCat.ofHom (inducedD q 2).hom.rangeRestrict ≫ f = 0 :=
        induced_positive_hom_zero q 2 _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x,y,hy⟩
      subst x
      exact congrArg (fun g : inducedObj q 3 ⟶ ModuleCat.of (T q) (TSimple q) => g y) hh
    exact Abelian.Ext.addEquiv₀.injective.subsingleton
  | succ n =>
    let P := inducedBoundaryResolution q hq hp
    apply ext_subsingleton_of_boundaries P n
    intro f _hf
    refine ⟨0, ?_⟩
    rw [Limits.comp_zero]
    exact (induced_positive_hom_zero q (n+3) f).symm


-- @@ L360-360 verbatim
end Tachikawa.C




-- @@ L364-364 verbatim
namespace Tachikawa.RightCorner

-- @@ L365-365 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L366-366 verbatim
variable {p : R} (hp : p*p=p)


-- @@ L368-371 verbatim
def homEquivScalar : (LeftCorner p →ₗ[R] R) ≃ₗ[k] RightCorner p where
  toEquiv := (homEquiv hp).toEquiv
  map_add' := (homEquiv hp).map_add
  map_smul' _ _ := Subtype.ext rfl


-- @@ L373-374 verbatim
@[simp] lemma homEquivScalar_apply (f : LeftCorner p →ₗ[R] R) :
    homEquivScalar (k := k) hp f = homEquiv hp f := rfl


-- @@ L376-380 verbatim
lemma homEquivScalar_precomp {r : R} (hr : r*r=r) (b : R) (hpb : p*b=b) (hbr : b*r=b)
    (f : LeftCorner r →ₗ[R] R) :
    homEquivScalar (k := k) hp (f.comp (LeftCorner.mulRight b hbr)) =
      mulLeft b hpb (homEquivScalar (k := k) hr f) :=
  homEquiv_precomp hp hr b hpb hbr f


-- @@ L382-382 verbatim
end Tachikawa.RightCorner




-- @@ L386-386 verbatim
namespace Tachikawa.C

-- @@ L387-387 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L389-389 verbatim
def v : C k q := ![0,0,0,0,0,0,1,0,0,0]

-- @@ L390-391 verbatim
omit [CharP k 2] in
lemma e_mul_v : e q * v q = v q := by rw [e_mul]; rfl


-- @@ L393-393 verbatim
def vHom : Ce q →ₗ[C k q] C k q := LeftCorner.lift (v q) (e_mul_v q)


-- @@ L395-397 verbatim
omit [CharP k 2] in
lemma vHom_generator : vHom q (LeftCorner.generator (e_idempotent q)) = v q :=
  LeftCorner.lift_generator (e_idempotent q) _ _


-- @@ L399-401 verbatim
omit [CharP k 2] in
lemma homEquiv_vHom : RightCorner.homEquiv (e_idempotent q) (vHom q) = ec q 0 0 0 0 0 1 :=
  Subtype.ext (vHom_generator q)


-- @@ L403-406 verbatim
def nuTwoAug : Nakayama k (C k q) (Ce q) →ₗ[k] Simple q where
  toFun ψ := ψ (vHom q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L408-411 verbatim
def nuTwoCycle : Nakayama k (C k q) (Ce q) where
  toFun f := (f (LeftCorner.generator (e_idempotent q))) 6
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L413-416 verbatim
omit [CharP k 2] in
lemma nuTwoCycle_aug : nuTwoAug q (nuTwoCycle q) = (show Simple q from (1:k)) := by
  change (vHom q (LeftCorner.generator (e_idempotent q))) 6 = 1
  exact congrArg (fun a : C k q => a 6) (vHom_generator q)


-- @@ L418-425 verbatim
omit [CharP k 2] in
lemma vHom_rhoEll (z : k) : (vHom q).comp (rhoEll q z) = 0 := by
  apply (RightCorner.homEquiv (e_idempotent q)).injective
  rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q z)
    (e_mul_ell q z) (ell_mul_e q z), map_zero, homEquiv_vHom]
  change lambdaEll q z (ec q 0 0 0 0 0 1) = 0
  rw [lambdaEll_ec, ec_eq_zero]
  simp


-- @@ L427-430 verbatim
lemma lambdaEll_one_six (a : eC q) : (lambdaEll q 1 a).val 6 = 0 := by
  rw [← ec_eta q a, lambdaEll_ec]
  change (1+1:k) * _ = 0
  rw [CharTwo.add_self_eq_zero, zero_mul]


-- @@ L432-436 verbatim
lemma hom_comp_rhoEll_one_six (f : Ce q →ₗ[C k q] C k q) :
    ((f.comp (rhoEll q 1)) (LeftCorner.generator (e_idempotent q))) 6 = 0 := by
  have he := RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q 1)
    (e_mul_ell q 1) (ell_mul_e q 1) f
  exact (congrArg (fun a : eC q => a.val 6) he).trans (lambdaEll_one_six q _)


-- @@ L438-439 verbatim
lemma nuTwoCycle_closed : Nakayama.map (k := k) (rhoEll q 1) (nuTwoCycle q) = 0 :=
  LinearMap.ext (fun f => hom_comp_rhoEll_one_six q f)


-- @@ L441-444 verbatim
omit [CharP k 2] in
lemma dual_vHom_rhoEll (z : k) (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q)) :
    ψ ((vHom q).comp (rhoEll q z)) = 0 :=
  (congrArg ψ (vHom_rhoEll q z)).trans ψ.map_zero


-- @@ L446-449 verbatim
omit [CharP k 2] in
lemma nuTwoAug_boundary (z : k) (ψ : Nakayama k (C k q) (Ce q)) :
    nuTwoAug q (Nakayama.map (rhoEll q z) ψ) = 0 :=
  dual_vHom_rhoEll q z ψ


-- @@ L451-465 verbatim
lemma dualTwoCycle_decompose (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (a : LinearMap.ker (lambdaEll q q)) :
    a.val = lambdaEll q 1 (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0) + ec q 0 0 0 0 0 (a.val.val 6) := by
  obtain ⟨h0,h3,h5⟩ := dualTwoCycle_coords q hq hq1 a
  rw [lambdaEll_ec]
  have he := ec_eta q a.val
  rw [h0,h3,h5] at he
  apply he.symm.trans
  apply Subtype.ext
  change (ec q 0 (a.val.val 2) (a.val.val 2) (a.val.val 4) 0 (a.val.val 6)).val =
    (ec q 0 (a.val.val 2) (1 * a.val.val 2) (1 * a.val.val 4 + q * 0) 0 ((1+1)*0)).val +
      (ec q 0 0 0 0 0 (a.val.val 6)).val
  ext i
  rw [add_apply]
  fin_cases i <;> simp [ec]


-- @@ L467-501 verbatim
lemma hom_cycle_decompose (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (f : Ce q →ₗ[C k q] C k q) (hf : f.comp (rhoEll q q) = 0) :
    ∃ g : Ce q →ₗ[C k q] C k q,
      f = g.comp (rhoEll q 1) + ((RightCorner.homEquiv (e_idempotent q) f).val 6) • vHom q := by
  let ε := RightCorner.homEquivScalar (k := k) (e_idempotent q)
  have hz : lambdaEll q q (ε f) = 0 := by
    change lambdaEll q q (RightCorner.homEquiv (e_idempotent q) f) = 0
    have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
    simpa only [rhoEll, lambdaEll,
      RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q q)
        (e_mul_ell q q) (ell_mul_e q q), map_zero] using h
  let a : LinearMap.ker (lambdaEll q q) := ⟨ε f, hz⟩
  refine ⟨ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0), ?_⟩
  apply ε.injective
  rw [map_add, map_smul]
  have hc : ε ((ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0)).comp (rhoEll q 1)) =
      lambdaEll q 1 (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0) := by
    change RightCorner.homEquivScalar (k := k) (e_idempotent q)
      ((ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0)).comp (rhoEll q 1)) = _
    rw [rhoEll, RightCorner.homEquivScalar_precomp (e_idempotent q) (e_idempotent q) (ell q 1)
      (e_mul_ell q 1) (ell_mul_e q 1)]
    exact congrArg (lambdaEll q 1) (ε.apply_symm_apply _)
  rw [hc]
  have hv : ((RightCorner.homEquiv (e_idempotent q) f).val 6) • ε (vHom q) =
      ec q 0 0 0 0 0 ((RightCorner.homEquiv (e_idempotent q) f).val 6) := by
    change _ • RightCorner.homEquiv (e_idempotent q) (vHom q) = _
    rw [homEquiv_vHom]
    apply Subtype.ext
    change ((RightCorner.homEquiv (e_idempotent q) f).val 6) •
      (ec q 0 0 0 0 0 1).val = _
    ext i
    rw [smul_apply]
    fin_cases i <;> simp [ec]
  rw [hv]
  exact dualTwoCycle_decompose q hq hq1 a


-- @@ L503-513 verbatim
lemma dual_vHom_boundary_iff (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q))
    (hψ : ∀ g : Ce q →ₗ[C k q] C k q, ψ (g.comp (rhoEll q 1)) = 0) :
    ψ (vHom q) = 0 ↔ ψ ∈ LinearMap.range (homPrecomp (k := k) (Z := C k q) (rhoEll q q)).dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro ha f hf
    obtain ⟨g,hg⟩ := hom_cycle_decompose q hq hq1 f hf
    rw [hg, map_add, map_smul, hψ, ha, smul_zero, add_zero]
  · intro h
    exact h (vHom q) (vHom_rhoEll q q)


-- @@ L515-519 verbatim
lemma nuTwo_boundary_iff (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q))
    (hψ : Nakayama.map (rhoEll q 1) ψ = 0) :
    nuTwoAug q ψ = 0 ↔ ∃ ξ, Nakayama.map (rhoEll q q) ξ = ψ :=
  dual_vHom_boundary_iff q hq hq1 ψ (fun g => LinearMap.congr_fun hψ g)


-- @@ L521-527 verbatim
omit [CharP k 2] in
lemma homRight_vHom_six (a : C k q) :
    (RightCorner.homEquiv (e_idempotent q) (Nakayama.homRight (k := k) a (vHom q))).val 6 = a 1 := by
  change (vHom q (LeftCorner.generator (e_idempotent q)) * a) 6 = a 1
  rw [vHom_generator]
  change (0*a 6 + 1*a 1 + 0*a 5 + 0*a 5 + 0*a 9) = a 1
  simp


-- @@ L529-541 verbatim
lemma dual_vHom_action (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q))
    (hψ : ∀ g : Ce q →ₗ[C k q] C k q, ψ (g.comp (rhoEll q 1)) = 0) (a : C k q) :
    ψ (Nakayama.homRight (k := k) a (vHom q)) = (a 1) * ψ (vHom q) := by
  let h := Nakayama.homRight (k := k) a (vHom q)
  have hh : h.comp (rhoEll q q) = 0 := by
    change ((rightMultiply a).comp (vHom q)).comp (rhoEll q q) = 0
    rw [LinearMap.comp_assoc, vHom_rhoEll, LinearMap.comp_zero]
  obtain ⟨g,hg⟩ := hom_cycle_decompose q hq hq1 h hh
  rw [homRight_vHom_six q a] at hg
  change ψ h = _
  rw [hg, map_add, map_smul, hψ, zero_add]
  rfl


-- @@ L543-548 verbatim
lemma nuTwoAug_smul (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q)) (hψ : Nakayama.map (rhoEll q 1) ψ = 0)
    (a : C k q) : nuTwoAug q (a • ψ) = a • nuTwoAug q ψ := by
  change (a • ψ) (vHom q) = (a 1) * ψ (vHom q)
  rw [Nakayama.action_apply]
  exact dual_vHom_action q hq hq1 ψ (fun g => LinearMap.congr_fun hψ g) a


-- @@ L550-550 verbatim
end Tachikawa.C




-- @@ L554-554 verbatim
namespace Tachikawa.C

-- @@ L555-555 verbatim
open CategoryTheory

-- @@ L556-556 verbatim
open scoped ModuleCat.Algebra

-- @@ L557-557 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L559-563 verbatim
lemma exact_rhoEll_one (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (rhoEll q q) (rhoEll q 1) := by
  have h := resD_exact q hp 1
  change Function.Exact (rhoEll q (q^1)) (rhoEll q (q^0)) at h
  simpa only [pow_one, pow_zero] using h


-- @@ L565-565 verbatim
abbrev InducedTwoCycles := LinearMap.ker (TrivialInduction.map (k := k) (rhoEll q 1))


-- @@ L567-569 verbatim
omit [CharP k 2] in
lemma twoCycles_first (x : InducedTwoCycles q) : rhoEll q 1 x.val.1 = 0 := by
  exact congrArg Prod.fst x.property


-- @@ L571-574 verbatim
omit [CharP k 2] in
lemma twoCycles_second (x : InducedTwoCycles q) :
    Nakayama.map (rhoEll q 1) x.val.2 = 0 := by
  exact congrArg Prod.snd x.property


-- @@ L576-580 verbatim
lemma vHom_twoCycles (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (x : InducedTwoCycles q) :
    vHom q x.val.1 = 0 := by
  obtain ⟨y,hy⟩ := (exact_rhoEll_one q hp _).mp (twoCycles_first q x)
  rw [← hy]
  exact LinearMap.congr_fun (vHom_rhoEll q q) y


-- @@ L582-594 verbatim
def inducedTwoAug (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    InducedTwoCycles q →ₗ[T q] TSimple q where
  toFun x := nuTwoAug q x.val.2
  map_add' _ _ := rfl
  map_smul' a x := by
    change nuTwoAug q (Nakayama.evaluationBilinear a.snd x.val.1 + a.fst • x.val.2) =
      a.fst • nuTwoAug q x.val.2
    rw [map_add, nuTwoAug_smul q hq (by simpa only [pow_one] using hp 1 (by omega))
      x.val.2 (twoCycles_second q x)]
    have hz : nuTwoAug q (Nakayama.evaluationBilinear a.snd x.val.1) = 0 := by
      change a.snd (vHom q x.val.1) = 0
      rw [vHom_twoCycles q hp, map_zero]
    rw [hz, zero_add]


-- @@ L596-602 verbatim
def inducedTwoBoundary (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    inducedObj q 3 →ₗ[T q] InducedTwoCycles q :=
  (inducedD q 2).hom.codRestrict _ (fun x => by
    have h := congrArg (fun f : inducedObj q 3 ⟶ inducedObj q 1 => f x) (inducedD_comp q hp 1)
    change (TrivialInduction.map (rhoEll q (q^0))) ((inducedD q 2).hom x) = 0 at h
    change (TrivialInduction.map (rhoEll q 1)) ((inducedD q 2).hom x) = 0
    simpa only [pow_zero] using h)


-- @@ L604-614 verbatim
lemma inducedTwoAug_surjective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Surjective (inducedTwoAug q hq hp) := by
  intro x
  let r : k := x
  have hz : (0, r • nuTwoCycle q) ∈ InducedTwoCycles q := by
    change (rhoEll q 1 0, Nakayama.map (rhoEll q 1) (r • nuTwoCycle q)) = (0,0)
    rw [map_zero, (Nakayama.map (rhoEll q 1)).map_smul_of_tower, nuTwoCycle_closed, smul_zero]
  refine ⟨⟨(0,r • nuTwoCycle q),hz⟩, ?_⟩
  change nuTwoAug q (r • nuTwoCycle q) = x
  rw [map_smul, nuTwoCycle_aug]
  exact mul_one r


-- @@ L616-620 verbatim
omit [CharP k 2] in
lemma inducedD_two_apply (x : TrivialInduction.Obj k (C k q) (Ce q)) :
    inducedD q 2 x = (rhoEll q q x.1, Nakayama.map (rhoEll q q) x.2) := by
  change (rhoEll q (q^1) x.1, Nakayama.map (rhoEll q (q^1)) x.2) = _
  rw [pow_one]


-- @@ L622-636 verbatim
lemma inducedTwoAug_exact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (inducedTwoBoundary q hp) (inducedTwoAug q hq hp) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (exact_rhoEll_one q hp _).mp (twoCycles_first q x)
    obtain ⟨ξ,hξ⟩ := (nuTwo_boundary_iff q hq
      (by simpa only [pow_one] using hp 1 (by omega)) x.val.2 (twoCycles_second q x)).mp hx
    refine ⟨(show TrivialInduction.Obj k (C k q) (Ce q) from (a,ξ)),Subtype.ext ?_⟩
    change inducedD q 2 (show TrivialInduction.Obj k (C k q) (Ce q) from (a,ξ)) = x.val
    rw [inducedD_two_apply]
    exact Prod.ext ha hξ
  · rintro ⟨y,rfl⟩
    exact (congrArg (fun z : TrivialInduction.Obj k (C k q) (Ce q) => nuTwoAug q z.2)
      (inducedD_two_apply q y)).trans (nuTwoAug_boundary q q y.2)


-- @@ L638-639 verbatim
local instance : HasQuotient (InducedTwoCycles q) (Submodule (T q) (InducedTwoCycles q)) :=
  @Submodule.hasQuotient (T q) (InducedTwoCycles q) inferInstance inferInstance inferInstance


-- @@ L641-647 verbatim
def inducedTwoHomologyEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((InducedTwoCycles q : Type) ⧸ LinearMap.range (inducedTwoBoundary q hp)) ≃ₗ[T q] TSimple q := by
  have he : LinearMap.range (inducedTwoBoundary q hp) = LinearMap.ker (inducedTwoAug q hq hp) := by
    ext x
    exact (inducedTwoAug_exact q hq hp x).symm
  exact (Submodule.quotEquivOfEq _ _ he).trans
    ((inducedTwoAug q hq hp).quotKerEquivOfSurjective (inducedTwoAug_surjective q hq hp))


-- @@ L649-649 verbatim
end Tachikawa.C




-- @@ L653-653 verbatim
namespace Tachikawa.C

-- @@ L654-654 verbatim
open CategoryTheory

-- @@ L655-655 verbatim
open scoped ModuleCat.Algebra

-- @@ L656-656 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L658-658 verbatim
abbrev InducedRange (n : ℕ) := LinearMap.range (inducedD q n).hom

-- @@ L659-659 verbatim
abbrev inducedRangeObj (n : ℕ) := ModuleCat.of (T q) (InducedRange q n)


-- @@ L661-670 verbatim
abbrev initialShortComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (InducedRange q 0).subtype (inducedAug q).hom (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedAug_exact q (by simpa only [pow_one] using hp 1 (by omega)) x).mp hx
      exact ⟨⟨x,y,hy⟩, rfl⟩
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      change inducedAug q x = 0
      exact (congrArg (inducedAug q) hy).symm.trans
        ((inducedAug_exact q (by simpa only [pow_one] using hp 1 (by omega))).apply_apply_eq_zero y))


-- @@ L672-675 verbatim
omit [CharP k 2] in
lemma initial_shortExact (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (initialShortComplex q hp).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (inducedAug_surjective q)


-- @@ L677-688 verbatim
abbrev middleShortComplex (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (InducedRange q 1).subtype (inducedD q 0).hom.rangeRestrict (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedD_exact q hq hp 0 (by omega) x).mp (congrArg Subtype.val hx)
      exact ⟨⟨x,y,hy⟩,rfl⟩
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      apply Subtype.ext
      change inducedD q 0 x = 0
      exact (congrArg (inducedD q 0) hy).symm.trans
        ((inducedD_exact q hq hp 0 (by omega)).apply_apply_eq_zero y))


-- @@ L690-694 verbatim
lemma middle_shortExact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (middleShortComplex q hq hp).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (by
    rintro ⟨x,y,hy⟩
    exact ⟨y,Subtype.ext hy⟩)


-- @@ L696-699 verbatim
def upperInclusion : InducedTwoCycles q →ₗ[T q] inducedObj q 2 where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L701-702 verbatim
def upperRangeMap : inducedObj q 2 →ₗ[T q] InducedRange q 1 :=
  (inducedD q 1).hom.rangeRestrict


-- @@ L704-718 verbatim
omit [CharP k 2] in
lemma upper_exact : Function.Exact (upperInclusion q) (upperRangeMap q) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have h := congrArg Subtype.val hx
    change TrivialInduction.map (k := k) (rhoEll q 1) x = 0
    change TrivialInduction.map (k := k) (rhoEll q (q^0)) x = 0 at h
    simpa only [pow_zero] using h
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    change TrivialInduction.map (k := k) (rhoEll q (q^0)) y.val = 0
    have hy : TrivialInduction.map (k := k) (rhoEll q 1) y.val = 0 := y.property
    simpa only [pow_zero] using hy


-- @@ L720-721 verbatim
abbrev upperShortComplex : ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (upperInclusion q) (upperRangeMap q) (upper_exact q)


-- @@ L723-727 verbatim
omit [CharP k 2] in
lemma upper_shortExact : (upperShortComplex q).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (by
    rintro ⟨x,y,hy⟩
    exact ⟨y,Subtype.ext hy⟩)


-- @@ L729-736 verbatim
def boundaryInclusion (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    InducedBoundaries q →ₗ[T q] InducedTwoCycles q where
  toFun x := ⟨(show TrivialInduction.Obj k (C k q) (Ce q) from x.val), by
    obtain ⟨y,hy⟩ := x.property
    exact (congrArg (TrivialInduction.map (k := k) (rhoEll q 1)) hy).symm.trans
      (inducedTwoBoundary q hp y).property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl


-- @@ L738-750 verbatim
abbrev homologyShortComplex (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (boundaryInclusion q hp) (inducedTwoAug q hq hp) (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedTwoAug_exact q hq hp x).mp hx
      refine ⟨⟨x.val, y, congrArg Subtype.val hy⟩, ?_⟩
      exact Subtype.ext rfl
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      have he : boundaryInclusion q hp ⟨x,y,hy⟩ = inducedTwoBoundary q hp y :=
        Subtype.ext hy.symm
      rw [he]
      exact (inducedTwoAug_exact q hq hp).apply_apply_eq_zero y)


-- @@ L752-758 verbatim
lemma homology_shortExact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (homologyShortComplex q hq hp).ShortExact :=
  linearShortExact _ _ _ (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : InducedTwoCycles q => z.val) h)
    (inducedTwoAug_surjective q hq hp)


-- @@ L760-771 verbatim
omit [CharP k 2] in

lemma induced_positive_ext_zero (i n : ℕ) :
    Subsingleton (Abelian.Ext (inducedObj q (i+1)) (ModuleCat.of (T q) (TSimple q)) n) := by
  cases n with
  | zero =>
    have : Subsingleton (inducedObj q (i+1) ⟶ ModuleCat.of (T q) (TSimple q)) :=
      subsingleton_of_forall_eq 0 (induced_positive_hom_zero q i)
    exact Abelian.Ext.addEquiv₀.injective.subsingleton
  | succ n =>
    let := inducedObj_projective q (i+1)
    exact Abelian.Ext.subsingleton_of_projective _ _ n


-- @@ L773-773 verbatim
end Tachikawa.C




-- @@ L777-777 verbatim
namespace Tachikawa.C

-- @@ L778-778 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L779-779 verbatim
open scoped ModuleCat.Algebra

-- @@ L780-780 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L782-782 verbatim
abbrev simpleObj := ModuleCat.of (T q) (TSimple q)


-- @@ L784-793 verbatim
omit [CharP k 2] in

lemma inducedRange_hom_zero (n : ℕ) (f : inducedRangeObj q n ⟶ simpleObj q) : f = 0 := by
  have hh : ModuleCat.ofHom (inducedD q n).hom.rangeRestrict ≫ f = 0 :=
    induced_positive_hom_zero q n _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x,y,hy⟩
  subst x
  exact congrArg (fun g : inducedObj q (n+1) ⟶ simpleObj q => g y) hh


-- @@ L795-800 verbatim
omit [CharP k 2] in
lemma inducedRange_ext_zero_zero (n : ℕ) :
    Subsingleton (Ext (inducedRangeObj q n) (simpleObj q) 0) := by
  have : Subsingleton (inducedRangeObj q n ⟶ simpleObj q) :=
    subsingleton_of_forall_eq 0 (inducedRange_hom_zero q n)
  exact Ext.addEquiv₀.injective.subsingleton


-- @@ L802-815 verbatim
omit [CharP k 2] in
lemma simple_ext_one_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 1) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ (initial_shortExact q hp) (simpleObj q)
    x (Subsingleton.elim _ _) (n₀ := 0) (by omega)
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 0
  rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
  exact hy.symm


-- @@ L817-825 verbatim
lemma firstRange_ext_one_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (inducedRangeObj q 0) (simpleObj q) 1) := by
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 0) :=
    induced_positive_ext_zero q 0 0
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) 1) :=
    induced_positive_ext_zero q 0 1
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₁ (simpleObj q) 0) :=
    inducedRange_ext_zero_zero q 1
  exact (extShiftEquiv k (middle_shortExact q hq hp) (simpleObj q) 0).symm.injective.subsingleton


-- @@ L827-836 verbatim
lemma simple_ext_two_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) 2) := by
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 1) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 1) from Ext.subsingleton_of_projective _ _ 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) 2) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) 2) from Ext.subsingleton_of_projective _ _ 1
  let : Subsingleton (Ext (initialShortComplex q hp).X₁ (simpleObj q) 1) :=
    firstRange_ext_one_zero q hq hp
  exact (extShiftEquiv k (initial_shortExact q hp) (simpleObj q) 1).symm.injective.subsingleton


-- @@ L838-845 verbatim
def upperShiftEquiv (n : ℕ) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) n ≃ₗ[k]
      Ext (inducedRangeObj q 1) (simpleObj q) (n+1) := by
  let : Subsingleton (Ext (upperShortComplex q).X₂ (simpleObj q) n) :=
    induced_positive_ext_zero q 1 n
  let : Subsingleton (Ext (upperShortComplex q).X₂ (simpleObj q) (n+1)) :=
    induced_positive_ext_zero q 1 (n+1)
  exact extShiftEquiv k (upper_shortExact q) (simpleObj q) n


-- @@ L847-854 verbatim
def middleShiftEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (inducedRangeObj q 1) (simpleObj q) n ≃ₗ[k]
      Ext (inducedRangeObj q 0) (simpleObj q) (n+1) := by
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) n) :=
    induced_positive_ext_zero q 0 n
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) (n+1)) :=
    induced_positive_ext_zero q 0 (n+1)
  exact extShiftEquiv k (middle_shortExact q hq hp) (simpleObj q) n


-- @@ L856-866 verbatim
def initialShiftEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (inducedRangeObj q 0) (simpleObj q) (n+1) ≃ₗ[k]
      Ext (simpleObj q) (simpleObj q) (n+2) := by
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) (n+1)) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) (n+1)) from
      Ext.subsingleton_of_projective _ _ n
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) (n+2)) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) (n+2)) from
      Ext.subsingleton_of_projective _ _ (n+1)
  exact extShiftEquiv k (initial_shortExact q hp) (simpleObj q) (n+1)


-- @@ L868-872 verbatim
def threeShiftEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) n ≃ₗ[k]
      Ext (simpleObj q) (simpleObj q) (n+3) :=
  ((upperShiftEquiv q n).trans (middleShiftEquiv q hq hp (n+1))).trans
    (initialShiftEquiv q hp (n+1))


-- @@ L874-877 verbatim
def simpleExtPeriod (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (simpleObj q) (simpleObj q) n ≃ₗ[k] Ext (simpleObj q) (simpleObj q) (n+3) :=
  (extQuotientEquiv k (homology_shortExact q hq hp) (simpleObj q)
    (inducedBoundary_ext_zero q hq hp) n).trans (threeShiftEquiv q hp hq n)


-- @@ L879-879 verbatim
end Tachikawa.C




-- @@ L883-883 verbatim
namespace Tachikawa

-- @@ L884-884 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L885-885 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L886-886 verbatim
variable (k : Type*) [CommRing k] [Linear k C]


-- @@ L888-891 verbatim
lemma extShiftEquiv_apply {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n : ℕ)
    [Subsingleton (Ext S.X₂ Y n)] [Subsingleton (Ext S.X₂ Y (n+1))]
    (x : Ext S.X₁ Y n) :
    extShiftEquiv k hS Y n x = hS.extClass.comp x (by omega) := rfl


-- @@ L893-900 verbatim
lemma extShiftEquiv_comp {S : ShortComplex C} (hS : S.ShortExact) {Y Z : C} (n m : ℕ)
    [Subsingleton (Ext S.X₂ Y n)] [Subsingleton (Ext S.X₂ Y (n+1))]
    [Subsingleton (Ext S.X₂ Z (n+m))] [Subsingleton (Ext S.X₂ Z (n+m+1))]
    (x : Ext S.X₁ Y n) (y : Ext Y Z m) :
    extShiftEquiv k hS Z (n+m) (x.comp y rfl) =
      (extShiftEquiv k hS Y n x).comp y (by omega) := by
  simp only [extShiftEquiv_apply]
  exact (Ext.comp_assoc _ _ _ (by omega) rfl (by omega)).symm


-- @@ L902-904 verbatim
lemma extQuotientEquiv_apply {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (h : ∀ n : ℕ, Subsingleton (Ext S.X₁ Y n)) (n : ℕ) (x : Ext S.X₃ Y n) :
    extQuotientEquiv k hS Y h n x = (Ext.mk₀ S.g).comp x (zero_add _) := rfl


-- @@ L906-913 verbatim
lemma extQuotientEquiv_comp {S : ShortComplex C} (hS : S.ShortExact) {Y Z : C}
    (hY : ∀ n : ℕ, Subsingleton (Ext S.X₁ Y n))
    (hZ : ∀ n : ℕ, Subsingleton (Ext S.X₁ Z n)) (n m : ℕ)
    (x : Ext S.X₃ Y n) (y : Ext Y Z m) :
    extQuotientEquiv k hS Z hZ (n+m) (x.comp y rfl) =
      (extQuotientEquiv k hS Y hY n x).comp y rfl := by
  simp only [extQuotientEquiv_apply]
  exact (Ext.comp_assoc _ _ _ (zero_add _) rfl (by omega)).symm


-- @@ L915-915 verbatim
end Tachikawa




-- @@ L919-919 verbatim
namespace Tachikawa.C

-- @@ L920-920 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L921-921 verbatim
open scoped ModuleCat.Algebra

-- @@ L922-922 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)


-- @@ L924-925 verbatim
def initialClass (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (simpleObj q) (inducedRangeObj q 0) 1 := (initial_shortExact q hp).extClass


-- @@ L927-928 verbatim
def middleClass (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (inducedRangeObj q 0) (inducedRangeObj q 1) 1 := (middle_shortExact q hq hp).extClass


-- @@ L930-931 verbatim
def upperClass : Ext (inducedRangeObj q 1) (ModuleCat.of (T q) (InducedTwoCycles q)) 1 :=
  (upper_shortExact q).extClass


-- @@ L933-935 verbatim
def homologyClass (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) 0 :=
  Ext.mk₀ (homologyShortComplex q hq hp).g


-- @@ L937-944 verbatim
lemma simpleExtPeriod_apply (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (simpleObj q) (simpleObj q) n) :
    simpleExtPeriod q hq hp n x =
      (initialClass q hp).comp (c := n+3)
        ((middleClass q hq hp).comp (c := n+2)
          ((upperClass q).comp (c := n+1)
            ((homologyClass q hq hp).comp x (zero_add n))
            (by omega)) (by omega)) (by omega) := rfl


-- @@ L946-948 verbatim
def tau (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (simpleObj q) (simpleObj q) 3 :=
  simpleExtPeriod q hq hp 0 (Ext.mk₀ (𝟙 (simpleObj q)))


-- @@ L950-956 verbatim
lemma simpleExtPeriod_eq_tau_comp (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (simpleObj q) (simpleObj q) n) :
    simpleExtPeriod q hq hp n x = (tau q hq hp).comp x (by omega) := by
  simp only [tau, simpleExtPeriod_apply, Ext.comp_mk₀_id]
  rw [Ext.comp_assoc (a₂₃ := n+2) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n+1) _ _ _ (by omega) (by omega) (by omega),
    Ext.comp_assoc (a₂₃ := n) _ _ _ (by omega) (by omega) (by omega)]


-- @@ L958-976 verbatim
omit [CharP k 2] in

def simpleEndEquiv : (simpleObj q ⟶ simpleObj q) ≃ₗ[k] k where
  toFun f := f (show TSimple q from (1 : k))
  invFun r := r • 𝟙 (simpleObj q)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hf := f.hom.map_smul_of_tower (show k from x) (show TSimple q from (1 : k))
    change f (show TSimple q from (show k from x)*1) =
      (show k from x) * (show k from f (show TSimple q from (1 : k))) at hf
    change (show k from f (show TSimple q from (1 : k))) * (show k from x) = (show k from f x)
    have hx : (show TSimple q from (show k from x)*1) = x := mul_one (show k from x)
    rw [hx] at hf
    exact (mul_comm _ _).trans hf.symm
  right_inv r := mul_one r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L978-992 verbatim
omit [CharP k 2] in
def simpleExtZeroEquiv : Ext (simpleObj q) (simpleObj q) 0 ≃ₗ[k] k :=
  { toAddEquiv := Ext.addEquiv₀.trans (simpleEndEquiv q).toAddEquiv
    map_smul' := by
      intro r x
      obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective x
      change simpleEndEquiv q (Ext.homEquiv₀ (r • Ext.mk₀ f)) =
        r • simpleEndEquiv q (Ext.homEquiv₀ (Ext.mk₀ f))
      rw [← Ext.mk₀_smul]
      have h0 (g : simpleObj q ⟶ simpleObj q) : Ext.homEquiv₀ (Ext.mk₀ g) = g :=
        Ext.homEquiv₀.apply_symm_apply g
      rw [h0, h0]
      change (algebraMap k (T q) r) • (f (show TSimple q from (1:k))) =
        r • (f (show TSimple q from (1:k)))
      exact IsScalarTower.algebraMap_smul (T q) r _ }


-- @@ L994-1000 verbatim
def simpleExtMultiple (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (m : ℕ) → Ext (simpleObj q) (simpleObj q) (3*m) ≃ₗ[k] k
  | 0 => simpleExtZeroEquiv q
  | m+1 => by
      have h : 3*(m+1) = 3*m+3 := by omega
      rw [h]
      exact (simpleExtPeriod q hq hp (3*m)).symm.trans (simpleExtMultiple hq hp m)


-- @@ L1002-1018 verbatim
lemma simpleExt_zero_off_multiples (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (simpleObj q) (simpleObj q) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact simple_ext_one_zero q hp
    by_cases h2 : n = 2
    · subst n
      exact simple_ext_two_zero q hq hp
    have h3 : 3 ≤ n := by omega
    have hm : (n-3)%3 ≠ 0 := by omega
    have := ih (n-3) (by omega) hm
    have he : n = (n-3)+3 := by omega
    rw [he]
    exact (simpleExtPeriod q hq hp (n-3)).symm.injective.subsingleton


-- @@ L1020-1025 verbatim
lemma simple_nonprojective_T (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ¬ Module.Projective (T q) (TSimple q) := by
  intro h
  let : Subsingleton (Ext (simpleObj q) (simpleObj q) 3) := Ext.subsingleton_of_projective _ _ 2
  have : Subsingleton k := (simpleExtMultiple q hq hp 1).symm.injective.subsingleton
  exact one_ne_zero (Subsingleton.elim (1 : k) 0)


-- @@ L1027-1027 verbatim
end Tachikawa.C




-- @@ L1031-1031 verbatim
namespace Tachikawa.C

-- @@ L1032-1032 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L1033-1033 verbatim
open scoped ModuleCat.Algebra

-- @@ L1034-1034 verbatim
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)


-- @@ L1036-1036 verbatim
abbrev tTwist := TrivialInduction.inverseTwist (R := C k q) H hH


-- @@ L1038-1043 verbatim
omit [CharP k 2] in
def simpleTwistComparison : (tTwist q H hH).obj (simpleObj q) ⟶ simpleObj q :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (simpleObj q)) (Y := simpleObj q)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }


-- @@ L1045-1048 verbatim
omit [CharP k 2] in
def inducedTwistComparison (n : ℕ) :
    (tTwist q H hH).obj (inducedObj q n) ⟶ inducedObj q n :=
  TrivialInduction.twistComparison H hH (resObj q n)


-- @@ L1050-1054 verbatim
omit [CharP k 2] in
lemma inducedTwist_d (n : ℕ) :
    (tTwist q H hH).map (inducedD q n) ≫ inducedTwistComparison q H hH n =
      inducedTwistComparison q H hH (n+1) ≫ inducedD q n :=
  TrivialInduction.twistComparison_natural H hH (resObj q (n+1)) (resD q n)


-- @@ L1056-1067 verbatim
omit [CharP k 2] in
def rangeTwistComparison (n : ℕ) :
    (tTwist q H hH).obj (inducedRangeObj q n) ⟶ inducedRangeObj q n :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (inducedRangeObj q n))
    (Y := inducedRangeObj q n)
    { toFun := fun x => ⟨inducedTwistComparison q H hH n x.val, by
        obtain ⟨y,hy⟩ := x.property
        refine ⟨inducedTwistComparison q H hH (n+1) y,?_⟩
        rw [← hy]
        exact (congrArg (fun f => f y) (inducedTwist_d q H hH n)).symm⟩
      map_add' := fun x y => Subtype.ext ((inducedTwistComparison q H hH n).hom.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext ((inducedTwistComparison q H hH n).hom.map_smul r x.val) }


-- @@ L1069-1080 verbatim
omit [CharP k 2] in
def cyclesTwistComparison :
    (tTwist q H hH).obj (ModuleCat.of (T q) (InducedTwoCycles q)) ⟶
      ModuleCat.of (T q) (InducedTwoCycles q) :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (ModuleCat.of (T q) (InducedTwoCycles q)))
    (Y := ModuleCat.of (T q) (InducedTwoCycles q))
    { toFun := fun x => ⟨(x.val.1,H • x.val.2), by
        change (rhoEll q 1 x.val.1,Nakayama.map (rhoEll q 1) (H • x.val.2)) = (0,0)
        rw [twoCycles_first q x,(Nakayama.map (rhoEll q 1)).map_smul_of_tower,
          twoCycles_second q x,smul_zero]⟩
      map_add' := fun x y => Subtype.ext ((inducedTwistComparison q H hH 2).hom.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext ((inducedTwistComparison q H hH 2).hom.map_smul r x.val) }


-- @@ L1082-1089 verbatim
omit [CharP k 2] in
def twistInitialHom (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (initialShortComplex q hp).map (tTwist q H hH) ⟶ initialShortComplex q hp where
  τ₁ := rangeTwistComparison q H hH 0
  τ₂ := inducedTwistComparison q H hH 0
  τ₃ := simpleTwistComparison q H hH
  comm₁₂ := by rfl
  comm₂₃ := by rfl


-- @@ L1091-1101 verbatim
def twistMiddleHom (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (middleShortComplex q hq hp).map (tTwist q H hH) ⟶ middleShortComplex q hq hp where
  τ₁ := rangeTwistComparison q H hH 1
  τ₂ := inducedTwistComparison q H hH 1
  τ₃ := rangeTwistComparison q H hH 0
  comm₁₂ := by rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun f => f x) (inducedTwist_d q H hH 0)


-- @@ L1103-1114 verbatim
omit [CharP k 2] in
def twistUpperHom :
    (upperShortComplex q).map (tTwist q H hH) ⟶ upperShortComplex q where
  τ₁ := cyclesTwistComparison q H hH
  τ₂ := inducedTwistComparison q H hH 2
  τ₃ := rangeTwistComparison q H hH 1
  comm₁₂ := by rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun f => f x) (inducedTwist_d q H hH 1)


-- @@ L1116-1123 verbatim
lemma homology_twist_comparison (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (tTwist q H hH).map (homologyShortComplex q hq hp).g ≫
      (H • simpleTwistComparison q H hH) =
    cyclesTwistComparison q H hH ≫ (homologyShortComplex q hq hp).g := by
  apply ModuleCat.hom_ext
  ext x
  change H • nuTwoAug q x.val.2 = nuTwoAug q (H • x.val.2)
  exact ((nuTwoAug q).map_smul H x.val.2).symm


-- @@ L1125-1125 verbatim
end Tachikawa.C




-- @@ L1129-1129 verbatim
namespace Tachikawa

-- @@ L1130-1130 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L1131-1131 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]


-- @@ L1133-1140 verbatim
lemma ext_push_comparison {A B A' B' Z : C} {a n c : ℕ}
    (f : Ext A B a) (f' : Ext A' B' a) (u : A ⟶ A') (v : B ⟶ B')
    (h : f.comp (Ext.mk₀ v) (add_zero a) = (Ext.mk₀ u).comp f' (zero_add a))
    (z : Ext B' Z n) (hc : a+n=c) :
    f.comp ((Ext.mk₀ v).comp z (zero_add n)) hc =
      (Ext.mk₀ u).comp (f'.comp z hc) (zero_add c) := by
  rw [← Ext.comp_assoc_of_second_deg_zero,h]
  exact Ext.comp_assoc _ _ _ (zero_add a) hc (by omega)


-- @@ L1142-1142 verbatim
end Tachikawa




-- @@ L1146-1146 verbatim
namespace Tachikawa.C

-- @@ L1147-1147 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L1148-1148 verbatim
open scoped ModuleCat.Algebra

-- @@ L1149-1150 verbatim
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)


-- @@ L1152-1161 verbatim
omit [CharP k 2] in
lemma initial_twist_naturality :
    ((initialClass q hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (rangeTwistComparison q H hH 0)) (add_zero 1) =
    (Ext.mk₀ (simpleTwistComparison q H hH)).comp (initialClass q hp) (zero_add 1) := by
  dsimp only [initialClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((initial_shortExact q hp).map_of_exact (tTwist q H hH)).extClass_naturality
      (initial_shortExact q hp) (twistInitialHom q H hH hp)


-- @@ L1163-1171 verbatim
lemma middle_twist_naturality :
    ((middleClass q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (rangeTwistComparison q H hH 1)) (add_zero 1) =
    (Ext.mk₀ (rangeTwistComparison q H hH 0)).comp (middleClass q hq hp) (zero_add 1) := by
  dsimp only [middleClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((middle_shortExact q hq hp).map_of_exact (tTwist q H hH)).extClass_naturality
      (middle_shortExact q hq hp) (twistMiddleHom q H hH hq hp)


-- @@ L1173-1182 verbatim
omit [CharP k 2] in
lemma upper_twist_naturality :
    ((upperClass q).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (cyclesTwistComparison q H hH)) (add_zero 1) =
    (Ext.mk₀ (rangeTwistComparison q H hH 1)).comp (upperClass q) (zero_add 1) := by
  dsimp only [upperClass]
  erw [Ext.mapExactFunctor_extClass]
  exact
    ((upper_shortExact q).map_of_exact (tTwist q H hH)).extClass_naturality
      (upper_shortExact q) (twistUpperHom q H hH)


-- @@ L1184-1191 verbatim
lemma homology_twist_naturality :
    ((homologyClass q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (H • simpleTwistComparison q H hH)) (add_zero 0) =
    (Ext.mk₀ (cyclesTwistComparison q H hH)).comp (homologyClass q hq hp) (zero_add 0) := by
  dsimp only [homologyClass]
  erw [Ext.mapExactFunctor_mk₀]
  erw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (homology_twist_comparison q H hH hq hp)


-- @@ L1193-1202 verbatim
lemma tau_twist_naturality :
    ((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
      (Ext.mk₀ (H • simpleTwistComparison q H hH)) (add_zero 3) =
    (Ext.mk₀ (simpleTwistComparison q H hH)).comp (tau q hq hp) (zero_add 3) := by
  simp only [tau,simpleExtPeriod_apply,Ext.comp_mk₀_id,Ext.mapExactFunctor_comp,
    Ext.comp_assoc_of_third_deg_zero]
  rw [homology_twist_naturality q H hH hq hp]
  rw [ext_push_comparison _ _ _ _ (upper_twist_naturality q H hH),
    ext_push_comparison _ _ _ _ (middle_twist_naturality q H hH hq hp),
    ext_push_comparison _ _ _ _ (initial_twist_naturality q H hH hp)]


-- @@ L1204-1204 verbatim
end Tachikawa.C




-- @@ L1208-1208 verbatim
namespace Tachikawa.C

-- @@ L1209-1209 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L1210-1210 verbatim
open scoped ModuleCat.Algebra

-- @@ L1211-1212 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)


-- @@ L1214-1215 verbatim
def tauPower (m : ℕ) : Ext (simpleObj q) (simpleObj q) (3*m) :=
  (simpleExtMultiple q hq hp m).symm 1


-- @@ L1217-1219 verbatim
lemma tauPower_zero : tauPower q hq hp 0 = Ext.mk₀ (𝟙 (simpleObj q)) := by
  change Ext.mk₀ ((1:k) • 𝟙 (simpleObj q)) = _
  rw [one_smul]


-- @@ L1221-1225 verbatim
lemma tauPower_ne_zero (m : ℕ) : tauPower q hq hp m ≠ 0 := by
  intro h
  have he := congrArg (simpleExtMultiple q hq hp m) h
  simp only [tauPower,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero he


-- @@ L1227-1235 verbatim
lemma tauPower_succ (m : ℕ) : tauPower q hq hp (m+1) =
    (tau q hq hp).comp (tauPower q hq hp m) (by omega) := by
  unfold tauPower
  simp only [simpleExtMultiple]
  have h : 3*(m+1) = 3*m+3 := by omega
  generalize he : simpleExtMultiple q hq hp m = e
  cases h
  change simpleExtPeriod q hq hp (3*m) (e.symm 1) = _
  exact simpleExtPeriod_eq_tau_comp q hq hp (3*m) (e.symm 1)


-- @@ L1237-1252 verbatim
lemma tauPower_comp_aux (m n c : ℕ) (hc : m+n=c) :
    (tauPower q hq hp m).comp (tauPower q hq hp n) (by omega) =
      tauPower q hq hp c := by
  induction m generalizing c with
  | zero =>
    have hc' : n = c := by omega
    subst hc'
    rw [tauPower_zero]
    simpa only [Nat.zero_add] using Ext.mk₀_id_comp (tauPower q hq hp n)
  | succ m ih =>
    have hc' : c = (m+n)+1 := by omega
    subst hc'
    rw [tauPower_succ,Ext.comp_assoc (a₂₃ := 3*(m+n)) _ _ _ (by omega) (by omega) (by omega),
      ih (m+n) rfl]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (tauPower_succ q hq hp (m+n)).symm


-- @@ L1254-1256 verbatim
lemma tauPower_comp (m n : ℕ) :
    (tauPower q hq hp m).comp (tauPower q hq hp n) (by omega) =
      tauPower q hq hp (m+n) := tauPower_comp_aux q hq hp m n (m+n) rfl


-- @@ L1258-1262 verbatim
lemma eq_smul_tauPower (m : ℕ) (x : Ext (simpleObj q) (simpleObj q) (3*m)) :
    x = simpleExtMultiple q hq hp m x • tauPower q hq hp m := by
  apply (simpleExtMultiple q hq hp m).injective
  rw [map_smul]
  simp only [tauPower,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]


-- @@ L1264-1275 verbatim
lemma tau_coordinates_comp (m n : ℕ)
    (x : Ext (simpleObj q) (simpleObj q) (3*m))
    (y : Ext (simpleObj q) (simpleObj q) (3*n)) :
    simpleExtMultiple q hq hp (m+n) (x.comp y (by omega)) =
      simpleExtMultiple q hq hp m x * simpleExtMultiple q hq hp n y := by
  have he : x.comp y (show 3*m+3*n=3*(m+n) by omega) =
      (simpleExtMultiple q hq hp m x * simpleExtMultiple q hq hp n y) •
        tauPower q hq hp (m+n) := by
    nth_rw 1 [eq_smul_tauPower q hq hp m x,eq_smul_tauPower q hq hp n y]
    rw [Ext.smul_comp,Ext.comp_smul,tauPower_comp,smul_smul]
  rw [he,map_smul]
  simp only [tauPower,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]


-- @@ L1277-1277 verbatim
end Tachikawa.C




-- @@ L1281-1281 verbatim
namespace Tachikawa

-- @@ L1282-1282 verbatim
open CategoryTheory CategoryTheory.Abelian

-- @@ L1283-1283 verbatim
open scoped ModuleCat.Algebra


-- @@ L1285-1285 verbatim
section Iso

-- @@ L1286-1287 verbatim
variable {K : Type*} [Field K] {D : Type*} [Category D] [Abelian D] [HasExt D]
  [Linear K D] {X Y Z X' Y' Z' : D}

-- @@ L1288-1300 verbatim
lemma extIso_comp (e : X ≅ X') (f : Y ≅ Y') (g : Z ≅ Z')
    {a b c : ℕ} (x : Ext X Y a) (y : Ext Y Z b) (h : a+b=c) :
    extIso (k := K) e g c (x.comp y h) =
      (extIso (k := K) e f a x).comp (extIso (k := K) f g b y) h := by
  change (Ext.mk₀ e.inv).comp ((x.comp y h).comp (Ext.mk₀ g.hom) (add_zero c))
    (zero_add c) = ((Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero a))
      (zero_add a)).comp ((Ext.mk₀ f.inv).comp
        (y.comp (Ext.mk₀ g.hom) (add_zero b)) (zero_add b)) h
  rw [Ext.comp_assoc (Ext.mk₀ e.inv) (x.comp (Ext.mk₀ f.hom) (add_zero a))
    ((Ext.mk₀ f.inv).comp (y.comp (Ext.mk₀ g.hom) (add_zero b)) (zero_add b))
    (zero_add a) h (by omega)]
  simp only [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id,Ext.comp_mk₀_id,Ext.comp_assoc_of_third_deg_zero]

-- @@ L1301-1301 verbatim
end Iso


-- @@ L1303-1303 verbatim
namespace C

-- @@ L1304-1305 verbatim
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)


-- @@ L1307-1316 verbatim
omit [CharP k 2] in
def simpleTwistIso : (tTwist q H hH).obj (simpleObj q) ≅ simpleObj q where
  hom := simpleTwistComparison q H hH
  inv := ModuleCat.ofHom (X := simpleObj q)
    (Y := (tTwist q H hH).obj (simpleObj q))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl


-- @@ L1318-1322 verbatim
omit [CharP k 2] in
def simpleTwistExt (n : ℕ) : Ext (simpleObj q) (simpleObj q) n →ₗ[k]
    Ext (simpleObj q) (simpleObj q) n :=
  (extIso (simpleTwistIso q H hH) (simpleTwistIso q H hH) n).toLinearMap.comp
    ((tTwist q H hH).mapExtLinearMap k (simpleObj q) (simpleObj q) n)


-- @@ L1324-1332 verbatim
omit [CharP k 2] in
lemma simpleTwistExt_comp {a b c : ℕ}
    (x : Ext (simpleObj q) (simpleObj q) a)
    (y : Ext (simpleObj q) (simpleObj q) b) (h : a+b=c) :
    simpleTwistExt q H hH c (x.comp y h) =
      (simpleTwistExt q H hH a x).comp (simpleTwistExt q H hH b y) h := by
  simp only [simpleTwistExt,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Functor.mapExtLinearMap_apply,Ext.mapExactFunctor_comp]
  exact extIso_comp (K := k) _ _ _ _ _ h


-- @@ L1334-1343 verbatim
omit [CharP k 2] in
lemma simpleTwist_mk₀_smul : Ext.mk₀ (H • (simpleTwistIso q H hH).hom) =
    H • Ext.mk₀ (simpleTwistIso q H hH).hom := by
  have h := Ext.mk₀_smul H (simpleTwistIso q H hH).hom
  convert h using 1
  congr 1
  apply ModuleCat.hom_ext
  ext x
  change H * (show k from x) = (H * 1) * (show k from x)
  rw [mul_one]


-- @@ L1345-1366 verbatim
lemma simpleTwist_tau : simpleTwistExt q H hH 3 (tau q hq hp) = H⁻¹ • tau q hq hp := by
  have ht := tau_twist_naturality q H hH hq hp
  have hs := congrArg (fun x => (Ext.mk₀ (simpleTwistIso q H hH).inv).comp x
    (zero_add 3)) ht
  have hscalar : H • simpleTwistExt q H hH 3 (tau q hq hp) = tau q hq hp := by
    change (Ext.mk₀ (simpleTwistIso q H hH).inv).comp
      (((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
        (Ext.mk₀ (H • (simpleTwistIso q H hH).hom)) (add_zero 3)) (zero_add 3) =
      (Ext.mk₀ (simpleTwistIso q H hH).inv).comp
        ((Ext.mk₀ (simpleTwistIso q H hH).hom).comp (tau q hq hp) (zero_add 3))
        (zero_add 3) at hs
    rw [simpleTwist_mk₀_smul q H hH,Ext.comp_smul,Ext.comp_smul] at hs
    change H • ((Ext.mk₀ (simpleTwistIso q H hH).inv).comp
      (((tau q hq hp).mapExactFunctor (tTwist q H hH)).comp
        (Ext.mk₀ (simpleTwistIso q H hH).hom) (add_zero 3)) (zero_add 3)) = _
    simpa only [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id,Ext.mk₀_id_comp] using hs
  calc
    simpleTwistExt q H hH 3 (tau q hq hp) =
      H⁻¹ • (H • simpleTwistExt q H hH 3 (tau q hq hp)) := by
        rw [smul_smul,inv_mul_cancel₀ hH,one_smul]
    _ = H⁻¹ • tau q hq hp := congrArg (fun x => H⁻¹ • x) hscalar


-- @@ L1368-1377 verbatim
lemma simpleTwist_tauPower (m : ℕ) :
    simpleTwistExt q H hH (3*m) (tauPower q hq hp m) =
      (H⁻¹)^m • tauPower q hq hp m := by
  induction m with
  | zero =>
    rw [tauPower_zero]
    simp [simpleTwistExt,Functor.mapExtLinearMap_apply,Ext.mapExactFunctor_mk₀,extIso]
  | succ m ih =>
    rw [tauPower_succ,simpleTwistExt_comp,simpleTwist_tau q H hH hq hp,ih,
      Ext.smul_comp,Ext.comp_smul,smul_smul,pow_succ']


-- @@ L1379-1385 verbatim
include hq hp in

lemma simpleTwist_weight (m : ℕ) (x : Ext (simpleObj q) (simpleObj q) (3*m)) :
    simpleTwistExt q H hH (3*m) x = (H⁻¹)^m • x := by
  nth_rw 1 [eq_smul_tauPower q hq hp m x]
  rw [map_smul,simpleTwist_tauPower q H hH hq hp,smul_comm,
    ← eq_smul_tauPower q hq hp m x]


-- @@ L1387-1387 verbatim
end C

-- @@ L1388-1388 verbatim
end Tachikawa


-- @@ L1390-1390 verbatim
end


-- @@ L1392-1392 verbatim
end OAI
