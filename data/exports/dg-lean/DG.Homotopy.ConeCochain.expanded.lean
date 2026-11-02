import DG.Homotopy.Homotopy
import DG.Module.Cone
import DG.Module.HomShift


-- @@ L5-52 verbatim
/-!
# The mapping cone in terms of cochains

Let `f : M →ᵈᵍ[A] N` be a morphism of dg modules and `Cone f = M⟦1⟧ ⊕ N` its mapping cone
(`DG.Cone`). This file is a port of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`: it describes the cone through
cochains of the Hom complex (`DG.Cochain`), with Mathlib's names, degrees and signs.

## Main definitions

* `DG.Cone.inl f : Cochain A M (Cone f) (-1)`, `x ↦ (x, 0)` (Mathlib's `mappingCone.inl`);
* `DG.Cone.inr f : N →ᵈᵍ[A] Cone f`, `y ↦ (0, y)` (defined in `DG.Module.Cone`; Mathlib's
  `mappingCone.inr`);
* `DG.Cone.fst f : Cocycle A (Cone f) M 1`, `(x, y) ↦ x` (Mathlib's `mappingCone.fst`);
* `DG.Cone.snd f : Cochain A (Cone f) N 0`, `(x, y) ↦ y` (Mathlib's `mappingCone.snd`);
* `DG.Cone.descCochain`, `DG.Cone.descCocycle`, `DG.Cone.desc`: maps out of the cone;
* `DG.Cone.liftCochain`, `DG.Cone.liftCocycle`, `DG.Cone.lift`: maps into the cone;
* `DG.Cone.descHomotopy`, `DG.Cone.liftHomotopy`: homotopies between maps out of and into the
  cone, from cochain data;
* `DG.Cone.mapOfHomotopy`: the map of cones induced by a square commuting up to homotopy;
* `DG.Cone.homotopyToZeroOfId`: the cone of the identity is contractible.

## Main results

* The relations `inl_fst`, `inl_snd`, `inr_fst`, `inr_snd`, `id` between the structure maps,
  and the extensionality principles `ext_to`, `ext_from`, `ext_cochain_to_iff`,
  `ext_cochain_from_iff`.
* `δ_inl : δ (-1) 0 (inl f) = ofHom (inr f ∘ f)` and `δ_snd : δ 0 1 (snd f) = -(f ∘ fst f)`.
* `δ_descCochain`, `δ_liftCochain`, and the universal properties `inl_desc`, `inr_desc`,
  `lift_fst`, `lift_snd`, `liftCochain_descCochain`, `lift_desc_apply`.
* `DG.Cone.fstHom_eq`: the morphism `fstHom f : Cone f →ᵈᵍ[A] Shift 1 M` is the cocycle `fst f`
  shifted to degree `0` (`Cocycle.rightShift`).
* `DG.Cone.map_eq_desc`, `DG.Cone.map_id`, `DG.Cone.map_comp`: the functoriality `DG.Cone.map`
  in terms of `desc`.

## Conventions and comparison with Mathlib

The cone, its differential and the structure maps agree with Mathlib's
`CochainComplex.mappingCone` on underlying complexes, and all the signs above are Mathlib's;
no deviation is needed. As in `DG.Module.Hom`, composition of cochains is written in the usual
order: Mathlib's `γ₁.comp γ₂ h` (first `γ₁`) is `γ₂.comp γ₁ h` here, with the same degree
hypothesis `h`; morphisms compose as `g.comp f` instead of `f ≫ g`. Since cochains are
functions, Mathlib's component lemmas `inl_v_fst_v`, `inl_v_d`, `d_snd_v`, `inl_v_desc_f`,
`lift_f_fst_v`, `lift_desc_f`, ... become the evaluation lemmas `inl_fst_apply`,
`inl_d_apply`, `d_snd_apply`, `inl_desc_apply`, `lift_fst_apply`, `lift_desc_apply`, ...;
Mathlib's `id_X` is `id_X` stated on elements, and `ext_to` and `ext_from` are stated for
elements of the cone and for additive maps out of the cone.
-/


-- @@ L54-54 verbatim
namespace DG


-- @@ L56-56 verbatim
namespace Cone


-- @@ L58-58 verbatim
open Cochain Shift


-- @@ L60-65 expanded
variable {A : Type*} {M N K L : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [AddCommGroup N] [DGAddCommGroup N] [Module A N] [AddCommGroup K]
  [DGAddCommGroup K] [Module A K] [AddCommGroup L] [DGAddCommGroup L] [Module A L]
  (f : DGModuleHom A M N)


-- @@ L67-67 verbatim
/-! ### The structure maps -/


-- @@ L69-79 verbatim
/-- The left inclusion `x ↦ (x, 0)` of `M` into the cone, as a cochain of degree `-1`
(Mathlib's `mappingCone.inl`). -/
def inl : Cochain A M (Cone f) (-1) where
  toFun x := inlLinear f (Shift.mk 1 x)
  map_zero' := by simp
  map_add' x y := by rw [mk_add, map_add]
  map_mem' i x hx := inlLinear_mem (by rw [← sub_eq_add_neg]; exact mk_mem_grading hx)
  map_smul' {i b} hb x := by
    rw [mk_smul hb, Units.smul_def, _root_.map_zsmul, _root_.map_smul, ← Units.smul_def, one_mul,
      neg_one_mul,
      koszulSign, koszulSign, Int.negOnePow_neg]


-- @@ L81-84 verbatim
/-- The second projection `(x, y) ↦ y` from the cone to `N`, as a cochain of degree `0`
(Mathlib's `mappingCone.snd`). -/
def snd : Cochain A (Cone f) N 0 :=
  Cochain.ofHoms (sndLinear f) sndLinear_mem


-- @@ L86-86 verbatim
section


-- @@ L88-88 verbatim
variable {f}


-- @@ L90-90 verbatim
theorem inl_apply (x : M) : inl f x = inlLinear f (Shift.mk 1 x) := rfl


-- @@ L92-92 verbatim
theorem snd_apply (p : Cone f) : snd f p = sndLinear f p := rfl


-- @@ L94-95 verbatim
@[simp]
theorem inl_snd_apply (x : M) : snd f (inl f x) = 0 := rfl


-- @@ L97-98 verbatim
@[simp]
theorem inr_snd_apply (y : N) : snd f (inr f y) = y := rfl


-- @@ L100-102 verbatim
/-- Mathlib's `inr_f_d`. -/
theorem inr_d_apply (y : N) : d (inr f y) = inr f (d y) :=
  ((inr f).map_d y).symm


-- @@ L104-104 verbatim
end


-- @@ L106-107 verbatim
@[simp]
theorem inl_snd : (snd f).comp (inl f) (add_zero (-1)) = 0 := rfl


-- @@ L109-110 verbatim
@[simp]
theorem inr_snd : (snd f).comp (ofHom (inr f)) (zero_add 0) = Cochain.id A N := rfl


-- @@ L112-116 verbatim
@[simp]
theorem inl_snd_assoc {d e g : ℤ} (γ : Cochain A N K d) (he : 0 + d = e) (hg : -1 + e = g) :
    (γ.comp (snd f) he).comp (inl f) hg = 0 := by
  ext x
  simp


-- @@ L118-122 verbatim
@[simp]
theorem inr_snd_assoc {d e : ℤ} (γ : Cochain A N K d) (he : 0 + d = e) :
    (γ.comp (snd f) he).comp (ofHom (inr f)) (by rw [← he, zero_add, zero_add]) = γ := by
  ext y
  simp


-- @@ L124-124 verbatim
variable [DGModule A M] [DGModule A N]


-- @@ L126-139 verbatim
/-- The first projection `(x, y) ↦ x` from the cone to `M`, as a cocycle of degree `1`
(Mathlib's `mappingCone.fst`). -/
def fst : Cocycle A (Cone f) M 1 :=
  Cocycle.mk
    { toFun := fun p => unmk 1 (fstHom f p)
      map_zero' := by simp
      map_add' := fun p q => by rw [map_add, unmk_add]
      map_mem' := fun i p hp => unmk_mem_grading ((fstHom f).map_mem hp)
      map_smul' := fun {i b} hb p => by rw [_root_.map_smul, unmk_smul hb, one_mul] }
    2 one_add_one_eq_two (by
      ext p
      rw [δ_apply 1 2 one_add_one_eq_two]
      change d (unmk 1 (fstHom f p)) - koszulSign 1 • unmk 1 (fstHom f (d p)) = 0
      rw [fstHom_d, unmk_d, smul_smul, Int.units_mul_self, one_smul, sub_self])


-- @@ L141-141 verbatim
variable {f}


-- @@ L143-143 verbatim
theorem fst_apply (p : Cone f) : (fst f).1 p = unmk 1 (fstHom f p) := rfl


-- @@ L145-146 verbatim
@[simp]
theorem inl_fst_apply (x : M) : (fst f).1 (inl f x) = x := rfl


-- @@ L148-149 verbatim
@[simp]
theorem inr_fst_apply (y : N) : (fst f).1 (inr f y) = 0 := rfl


-- @@ L151-153 verbatim
/-- Every element of the cone is `inl x + inr y` (Mathlib's `id_X`). -/
theorem id_X (p : Cone f) : inl f ((fst f).1 p) + inr f (snd f p) = p :=
  inlLinear_fstHom_add_inr_sndLinear p


-- @@ L155-158 verbatim
/-- Two elements of the cone with the same projections are equal (Mathlib's `ext_to`). -/
theorem ext_to {p q : Cone f} (h₁ : (fst f).1 p = (fst f).1 q) (h₂ : snd f p = snd f q) :
    p = q :=
  ext h₁ h₂


-- @@ L160-161 verbatim
theorem ext_to_iff {p q : Cone f} : p = q ↔ (fst f).1 p = (fst f).1 q ∧ snd f p = snd f q :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext_to h.1 h.2⟩


-- @@ L163-169 verbatim
/-- Two additive maps out of the cone agreeing on the images of `inl` and `inr` are equal
(Mathlib's `ext_from`). -/
theorem ext_from {P F : Type*} [AddCommGroup P] [FunLike F (Cone f) P]
    [AddMonoidHomClass F (Cone f) P] {g₁ g₂ : F}
    (h₁ : ∀ x, g₁ (inl f x) = g₂ (inl f x)) (h₂ : ∀ y, g₁ (inr f y) = g₂ (inr f y)) :
    g₁ = g₂ :=
  DFunLike.ext g₁ g₂ fun p => by rw [← id_X p, map_add, map_add, h₁, h₂]


-- @@ L171-174 verbatim
theorem ext_from_iff {P F : Type*} [AddCommGroup P] [FunLike F (Cone f) P]
    [AddMonoidHomClass F (Cone f) P] {g₁ g₂ : F} :
    g₁ = g₂ ↔ (∀ x, g₁ (inl f x) = g₂ (inl f x)) ∧ ∀ y, g₁ (inr f y) = g₂ (inr f y) :=
  ⟨fun h => h ▸ ⟨fun _ => rfl, fun _ => rfl⟩, fun h => ext_from h.1 h.2⟩


-- @@ L176-176 verbatim
/-! ### The differential of the cone -/


-- @@ L178-181 verbatim
/-- Mathlib's `d_fst_v`. -/
theorem d_fst_apply (p : Cone f) : (fst f).1 (d p) = -d ((fst f).1 p) := by
  rw [fst_apply, fst_apply, fstHom_d, unmk_d, koszulSign, Int.negOnePow_one, Units.neg_smul,
    one_smul]


-- @@ L183-185 verbatim
/-- Mathlib's `d_snd_v`. -/
theorem d_snd_apply (p : Cone f) : snd f (d p) = f ((fst f).1 p) + d (snd f p) :=
  sndLinear_d p


-- @@ L187-192 verbatim
/-- Mathlib's `inl_v_d`. -/
theorem inl_d_apply (x : M) : d (inl f x) = inr f (f x) - inl f (d x) := by
  refine ext_to ?_ ?_
  · rw [d_fst_apply, map_sub, inl_fst_apply, inr_fst_apply, inl_fst_apply, zero_sub]
  · rw [d_snd_apply, map_sub, inl_fst_apply, inl_snd_apply, inr_snd_apply, inl_snd_apply,
      d_zero, add_zero, sub_zero]


-- @@ L194-194 verbatim
/-! ### Relations between the structure maps -/


-- @@ L196-196 verbatim
variable (f)


-- @@ L198-199 verbatim
@[simp]
theorem inl_fst : (fst f).1.comp (inl f) (neg_add_cancel 1) = Cochain.id A M := rfl


-- @@ L201-202 verbatim
@[simp]
theorem inr_fst : (fst f).1.comp (ofHom (inr f)) (zero_add 1) = 0 := rfl


-- @@ L204-206 verbatim
@[simp]
theorem inl_fst_assoc {d e : ℤ} (γ : Cochain A M K d) (he : 1 + d = e) :
    (γ.comp (fst f).1 he).comp (inl f) (by rw [← he, neg_add_cancel_left]) = γ := rfl


-- @@ L208-212 verbatim
@[simp]
theorem inr_fst_assoc {d e g : ℤ} (γ : Cochain A M K d) (he : 1 + d = e) (hg : 0 + e = g) :
    (γ.comp (fst f).1 he).comp (ofHom (inr f)) hg = 0 := by
  ext y
  simp


-- @@ L214-219 verbatim
theorem ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j) {γ₁ γ₂ : Cochain A K (Cone f) i} :
    γ₁ = γ₂ ↔ (fst f).1.comp γ₁ hij = (fst f).1.comp γ₂ hij ∧
      (snd f).comp γ₁ (add_zero i) = (snd f).comp γ₂ (add_zero i) := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => Cochain.ext fun x => ext_to ?_ ?_⟩
  · exact congrArg (fun γ : Cochain A K M j => γ x) h₁
  · exact congrArg (fun γ : Cochain A K N i => γ x) h₂


-- @@ L221-226 verbatim
theorem ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j) {γ₁ γ₂ : Cochain A (Cone f) K j} :
    γ₁ = γ₂ ↔ γ₁.comp (inl f) (show -1 + j = i by omega) = γ₂.comp (inl f) (by omega) ∧
      γ₁.comp (ofHom (inr f)) (zero_add j) = γ₂.comp (ofHom (inr f)) (zero_add j) := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => ext_from (fun x => ?_) (fun y => ?_)⟩
  · exact congrArg (fun γ : Cochain A M K i => γ x) h₁
  · exact congrArg (fun γ : Cochain A N K j => γ y) h₂


-- @@ L228-232 verbatim
/-- `inl ∘ fst + inr ∘ snd = id` (Mathlib's `mappingCone.id`). -/
theorem id :
    (inl f).comp (fst f).1 (add_neg_cancel 1) + (ofHom (inr f)).comp (snd f) (add_zero 0) =
      Cochain.id A (Cone f) :=
  Cochain.ext id_X


-- @@ L234-238 verbatim
/-- The differential of `inl` (Mathlib's `δ_inl`): `inl` is a chain map up to `inr ∘ f`. -/
@[simp]
theorem δ_inl : δ (-1) 0 (inl f) = ofHom ((inr f).comp f) := by
  refine Cochain.ext fun x => ?_
  rw [δ_neg_one_apply, inl_d_apply, ofHom_apply, DGModuleHom.comp_apply, sub_add_cancel]


-- @@ L240-245 verbatim
/-- The differential of `snd` (Mathlib's `δ_snd`). -/
@[simp]
theorem δ_snd : δ 0 1 (snd f) = -(ofHom f).comp (fst f).1 (add_zero 1) := by
  ext p
  rw [δ_zero_cochain_apply, d_snd_apply, Cochain.neg_apply, comp_apply, ofHom_apply]
  abel


-- @@ L247-250 verbatim
/-- The morphism `fstHom f : Cone f →ᵈᵍ[A] Shift 1 M` is the `1`-cocycle `fst f` shifted to
degree `0`. The third morphism of Mathlib's standard triangle `mappingCone.triangle` is
`Cocycle.homOf ((-fst f).rightShift 1 0 _) = -fstHom f`. -/
theorem fstHom_eq : fstHom f = Cocycle.homOf ((fst f).rightShift 1 0 (zero_add 1)) := rfl


-- @@ L252-252 verbatim
theorem ofHom_fstHom : ofHom (fstHom f) = (fst f).1.rightShift 1 0 (zero_add 1) := rfl


-- @@ L254-254 verbatim
/-! ### Maps out of the cone -/


-- @@ L256-256 verbatim
section Desc


-- @@ L258-258 verbatim
variable {n m : ℤ}


-- @@ L260-264 verbatim
/-- The cochain `Cochain A (Cone f) K n` given by `α : Cochain A M K m` (with `m + 1 = n`) on
`M⟦1⟧` and `β : Cochain A N K n` on `N`: `α ∘ fst + β ∘ snd` (Mathlib's `descCochain`). -/
def descCochain (α : Cochain A M K m) (β : Cochain A N K n) (h : m + 1 = n) :
    Cochain A (Cone f) K n :=
  α.comp (fst f).1 (by rw [← h, add_comm]) + β.comp (snd f) (zero_add n)


-- @@ L266-266 verbatim
variable (α : Cochain A M K m) (β : Cochain A N K n) (h : m + 1 = n)


-- @@ L268-269 verbatim
theorem descCochain_apply (p : Cone f) :
    descCochain f α β h p = α ((fst f).1 p) + β (snd f p) := rfl


-- @@ L271-275 verbatim
@[simp]
theorem inl_descCochain :
    (descCochain f α β h).comp (inl f) (by omega) = α := by
  ext x
  simp [descCochain_apply]


-- @@ L277-281 verbatim
@[simp]
theorem inr_descCochain :
    (descCochain f α β h).comp (ofHom (inr f)) (zero_add n) = β := by
  ext y
  simp [descCochain_apply]


-- @@ L283-286 verbatim
/-- Mathlib's `inl_v_descCochain_v`. -/
@[simp]
theorem inl_descCochain_apply (x : M) : descCochain f α β h (inl f x) = α x := by
  simp [descCochain_apply]


-- @@ L288-291 verbatim
/-- Mathlib's `inr_f_descCochain_v`. -/
@[simp]
theorem inr_descCochain_apply (y : N) : descCochain f α β h (inr f y) = β y := by
  simp [descCochain_apply]


-- @@ L293-293 verbatim
variable [DGModule A K]


-- @@ L295-309 verbatim
theorem δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (descCochain f α β h) =
      (δ m n α + koszulSign n' • β.comp (ofHom f) (zero_add n)).comp (fst f).1
          (by omega) +
        (δ n n' β).comp (snd f) (zero_add n') := by
  ext p
  have hm : koszulSign m = -koszulSign n := by
    rw [← h, koszulSign, koszulSign, Int.negOnePow_succ, neg_neg]
  have hn : koszulSign n' = -koszulSign n := by
    rw [← hn', koszulSign, koszulSign, Int.negOnePow_succ]
  simp only [δ_apply _ _ hn', δ_apply _ _ h, descCochain_apply, Cochain.add_apply, comp_apply,
    units_smul_apply, Cochain.neg_apply, ofHom_apply, d_fst_apply, d_snd_apply, map_add, map_neg,
    hm, hn,
    Units.neg_smul, smul_add, smul_neg, sub_eq_add_neg, neg_neg]
  abel


-- @@ L311-311 verbatim
end Desc


-- @@ L313-313 verbatim
section DescCocycle


-- @@ L315-315 verbatim
variable [DGModule A K]


-- @@ L317-324 verbatim
/-- The cocycle `Cocycle A (Cone f) K n` given by `α : Cochain A M K m` (with `m + 1 = n`) and
a cocycle `β : Cocycle A N K n` satisfying `δ α = (-1)^n • β ∘ f` (Mathlib's `descCocycle`). -/
@[simps!]
def descCocycle {n m : ℤ} (α : Cochain A M K m) (β : Cocycle A N K n) (h : m + 1 = n)
    (eq : δ m n α = koszulSign n • (β.1.comp (ofHom f) (zero_add n))) :
    Cocycle A (Cone f) K n :=
  Cocycle.mk (descCochain f α β.1 h) (n + 1) rfl (by
    simp [δ_descCochain _ _ _ _ _ rfl, eq, koszulSign, Int.negOnePow_succ])


-- @@ L326-326 verbatim
section


-- @@ L328-328 expanded
variable (α : Cochain A M K (-1)) (β : DGModuleHom A N K) (eq : δ (-1) 0 α = ofHom (β.comp f))


-- @@ L330-334 expanded
/-- The morphism `Cone f →ᵈᵍ[A] K` given by a `(-1)`-cochain `α : Cochain A M K (-1)` and a
morphism `β : N →ᵈᵍ[A] K` with `δ α = β ∘ f`: `(x, y) ↦ α x + β y` (Mathlib's `desc`). -/
def desc : DGModuleHom A (Cone f) K :=
  Cocycle.homOf
    (descCocycle f α (Cocycle.ofHom β) (neg_add_cancel 1)
      (by rw [eq, koszulSign, Int.negOnePow_zero, one_smul]; rfl))


-- @@ L336-337 verbatim
@[simp]
theorem ofHom_desc : ofHom (desc f α β eq) = descCochain f α (ofHom β) (neg_add_cancel 1) := rfl


-- @@ L339-340 verbatim
/-- Mathlib's `desc_f`. -/
theorem desc_apply (p : Cone f) : desc f α β eq p = α ((fst f).1 p) + β (snd f p) := rfl


-- @@ L342-345 verbatim
/-- Mathlib's `inl_v_desc_f`. -/
@[simp]
theorem inl_desc_apply (x : M) : desc f α β eq (inl f x) = α x := by
  simp [desc_apply]


-- @@ L347-349 verbatim
theorem inl_desc : (ofHom (desc f α β eq)).comp (inl f) (add_zero _) = α := by
  ext x
  simp


-- @@ L351-354 verbatim
/-- Mathlib's `inr_f_desc_f`. -/
@[simp]
theorem inr_desc_apply (y : N) : desc f α β eq (inr f y) = β y := by
  simp [desc_apply]


-- @@ L356-359 verbatim
@[simp]
theorem inr_desc : (desc f α β eq).comp (inr f) = β := by
  ext y
  simp


-- @@ L361-361 verbatim
end


-- @@ L363-385 expanded
/-- Constructor for homotopies between morphisms out of a mapping cone (Mathlib's
`descHomotopy`). -/
def descHomotopy (f₁ f₂ : DGModuleHom A (Cone f) K) (γ₁ : Cochain A M K (-2))
    (γ₂ : Cochain A N K (-1))
    (h₁ :
      (ofHom f₁).comp (inl f) (add_zero (-1)) =
        δ (-2) (-1) γ₁ + γ₂.comp (ofHom f) (zero_add (-1)) +
          (ofHom f₂).comp (inl f) (add_zero (-1)))
    (h₂ : ofHom (f₁.comp (inr f)) = δ (-1) 0 γ₂ + ofHom (f₂.comp (inr f))) : DGHomotopy f₁ f₂
    where
  hom := descCochain f γ₁ γ₂ (by norm_num)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp] at h₂
    rw [ext_cochain_from_iff f (-1) 0 (neg_add_cancel 1)]
    refine ⟨?_, ?_⟩
    · ext x
      have := congrArg (fun γ : Cochain A M K (-1) => γ x) h₁
      simp only [comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_descCochain f γ₁ γ₂ (by norm_num) 0 (neg_add_cancel 1)]
      simp [koszulSign]
    · ext y
      have := congrArg (fun γ : Cochain A N K 0 => γ y) h₂
      simp only [comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_descCochain f γ₁ γ₂ (by norm_num) 0 (neg_add_cancel 1)]
      simp


-- @@ L387-387 verbatim
end DescCocycle


-- @@ L389-389 verbatim
/-! ### Maps into the cone -/


-- @@ L391-391 verbatim
section Lift


-- @@ L393-393 verbatim
variable {n m : ℤ}


-- @@ L395-399 verbatim
/-- The cochain `Cochain A K (Cone f) n` given by `α : Cochain A K M m` (with `n + 1 = m`) and
`β : Cochain A K N n`: `inl ∘ α + inr ∘ β` (Mathlib's `liftCochain`). -/
def liftCochain (α : Cochain A K M m) (β : Cochain A K N n) (h : n + 1 = m) :
    Cochain A K (Cone f) n :=
  (inl f).comp α (by omega) + (ofHom (inr f)).comp β (add_zero n)


-- @@ L401-401 verbatim
variable (α : Cochain A K M m) (β : Cochain A K N n) (h : n + 1 = m)


-- @@ L403-404 verbatim
omit [DGModule A M] [DGModule A N] in
theorem liftCochain_apply (k : K) : liftCochain f α β h k = inl f (α k) + inr f (β k) := rfl


-- @@ L406-409 verbatim
@[simp]
theorem liftCochain_fst : (fst f).1.comp (liftCochain f α β h) h = α := by
  ext k
  simp [liftCochain_apply]


-- @@ L411-415 verbatim
omit [DGModule A M] [DGModule A N] in
@[simp]
theorem liftCochain_snd : (snd f).comp (liftCochain f α β h) (add_zero n) = β := by
  ext k
  simp [liftCochain_apply]


-- @@ L417-420 verbatim
/-- Mathlib's `liftCochain_v_fst_v`. -/
@[simp]
theorem liftCochain_fst_apply (k : K) : (fst f).1 (liftCochain f α β h k) = α k := by
  simp [liftCochain_apply]


-- @@ L422-426 verbatim
omit [DGModule A M] [DGModule A N] in
/-- Mathlib's `liftCochain_v_snd_v`. -/
@[simp]
theorem liftCochain_snd_apply (k : K) : snd f (liftCochain f α β h k) = β k := by
  simp [liftCochain_apply]


-- @@ L428-428 verbatim
variable [DGModule A K]


-- @@ L430-446 verbatim
theorem δ_liftCochain (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (liftCochain f α β h) = -(inl f).comp (δ m m' α) (by omega) +
      (ofHom (inr f)).comp (δ n m β + (ofHom f).comp α (add_zero m)) (add_zero m) := by
  refine Cochain.ext fun k => ?_
  have hm : koszulSign m = -koszulSign n := by
    rw [← h, koszulSign, koszulSign, Int.negOnePow_succ]
  refine ext_to ?_ ?_
  · simp only [δ_apply _ _ h, δ_apply _ _ hm', liftCochain_apply, Cochain.add_apply,
      Cochain.neg_apply, comp_apply, map_add, map_sub, map_neg, map_units_smul,
      inl_d_apply, inr_d_apply, inl_fst_apply, inr_fst_apply, hm, Units.neg_smul,
      ofHom_apply, smul_zero, add_zero]
    abel
  · simp only [δ_apply _ _ h, δ_apply _ _ hm', liftCochain_apply, Cochain.add_apply,
      Cochain.neg_apply, comp_apply, ofHom_apply, map_add, map_sub, map_neg,
      map_units_smul, inl_d_apply, inr_d_apply, inl_snd_apply, inr_snd_apply, zero_add,
      smul_zero]
    abel


-- @@ L448-448 verbatim
end Lift


-- @@ L450-450 verbatim
section LiftCocycle


-- @@ L452-452 verbatim
variable [DGModule A K]


-- @@ L454-463 verbatim
/-- The cocycle `Cocycle A K (Cone f) n` given by a cocycle `α : Cocycle A K M m` (with
`n + 1 = m`) and `β : Cochain A K N n` satisfying `δ β + f ∘ α = 0` (Mathlib's
`liftCocycle`). -/
@[simps!]
def liftCocycle {n m : ℤ} (α : Cocycle A K M m) (β : Cochain A K N n) (h : n + 1 = m)
    (eq : δ n m β + (ofHom f).comp α.1 (add_zero m) = 0) :
    Cocycle A K (Cone f) n :=
  Cocycle.mk (liftCochain f α.1 β h) m h (by
    simp only [δ_liftCochain f α.1 β h (m + 1) rfl, eq, Cocycle.δ_eq_zero, Cochain.comp_zero,
      neg_zero, zero_add])


-- @@ L465-465 verbatim
section


-- @@ L467-468 verbatim
variable (α : Cocycle A K M 1) (β : Cochain A K N 0)
  (eq : δ 0 1 β + (ofHom f).comp α.1 (add_zero 1) = 0)


-- @@ L470-473 expanded
/-- The morphism `K →ᵈᵍ[A] Cone f` given by a `1`-cocycle `α : Cocycle A K M 1` and a
`0`-cochain `β : Cochain A K N 0` with `δ β + f ∘ α = 0`: `k ↦ (α k, β k)` (Mathlib's `lift`). -/
def lift : DGModuleHom A K (Cone f) :=
  Cocycle.homOf (liftCocycle f α β (zero_add 1) eq)


-- @@ L475-476 verbatim
@[simp]
theorem ofHom_lift : ofHom (lift f α β eq) = liftCochain f α.1 β (zero_add 1) := rfl


-- @@ L478-479 verbatim
/-- Mathlib's `lift_f`. -/
theorem lift_apply (k : K) : lift f α β eq k = inl f (α.1 k) + inr f (β k) := rfl


-- @@ L481-484 verbatim
/-- Mathlib's `lift_f_fst_v`. -/
@[simp]
theorem lift_fst_apply (k : K) : (fst f).1 (lift f α β eq k) = α.1 k := by
  simp [lift_apply]


-- @@ L486-488 verbatim
theorem lift_fst : (fst f).1.comp (ofHom (lift f α β eq)) (zero_add 1) = α.1 := by
  ext k
  simp


-- @@ L490-493 verbatim
/-- Mathlib's `lift_f_snd_v`. -/
@[simp]
theorem lift_snd_apply (k : K) : snd f (lift f α β eq k) = β k := by
  simp [lift_apply]


-- @@ L495-497 verbatim
theorem lift_snd : (snd f).comp (ofHom (lift f α β eq)) (zero_add 0) = β := by
  ext k
  simp


-- @@ L499-499 verbatim
end


-- @@ L501-522 expanded
/-- Constructor for homotopies between morphisms into a mapping cone (Mathlib's
`liftHomotopy`). -/
def liftHomotopy (f₁ f₂ : DGModuleHom A K (Cone f)) (α : Cochain A K M 0) (β : Cochain A K N (-1))
    (h₁ :
      (fst f).1.comp (ofHom f₁) (zero_add 1) = -δ 0 1 α + (fst f).1.comp (ofHom f₂) (zero_add 1))
    (h₂ :
      (snd f).comp (ofHom f₁) (zero_add 0) =
        δ (-1) 0 β + (ofHom f).comp α (zero_add 0) + (snd f).comp (ofHom f₂) (zero_add 0)) :
    DGHomotopy f₁ f₂ where
  hom := liftCochain f α β (neg_add_cancel 1)
  ofHom_eq := by
    rw [ext_cochain_to_iff f 0 1 (zero_add 1)]
    refine ⟨?_, ?_⟩
    · ext k
      have := congrArg (fun γ : Cochain A K M 1 => γ k) h₁
      simp only [comp_apply, Cochain.add_apply, Cochain.neg_apply] at this ⊢
      rw [this, δ_liftCochain f α β (neg_add_cancel 1) 1 (zero_add 1)]
      simp
    · ext k
      have := congrArg (fun γ : Cochain A K N 0 => γ k) h₂
      simp only [comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_liftCochain f α β (neg_add_cancel 1) 1 (zero_add 1)]
      simp


-- @@ L524-524 verbatim
end LiftCocycle


-- @@ L526-526 verbatim
section


-- @@ L528-530 verbatim
variable {n m : ℤ} (α : Cochain A K M m) (β : Cochain A K N n) {n' m' : ℤ}
  (α' : Cochain A M L m') (β' : Cochain A N L n') (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ)
  (hp : n + n' = p)


-- @@ L532-538 verbatim
/-- Mathlib's `liftCochain_descCochain`. -/
@[simp]
theorem liftCochain_descCochain :
    (descCochain f α' β' h').comp (liftCochain f α β h) hp =
      α'.comp α (by omega) + β'.comp β (by omega) := by
  ext k
  simp [liftCochain_apply, descCochain_apply]


-- @@ L540-540 verbatim
end


-- @@ L542-549 expanded
variable [DGModule A L] in
/-- Mathlib's `lift_desc_f`. -/
theorem lift_desc_apply [DGModule A K] (α : Cocycle A K M 1) (β : Cochain A K N 0)
    (eq : δ 0 1 β + (ofHom f).comp α.1 (add_zero 1) = 0) (α' : Cochain A M L (-1))
    (β' : DGModuleHom A N L) (eq' : δ (-1) 0 α' = ofHom (β'.comp f)) (k : K) :
    desc f α' β' eq' (lift f α β eq k) = α' (α.1 k) + β' (β k) := by simp [desc_apply]


-- @@ L551-551 verbatim
/-! ### Maps between cones -/


-- @@ L553-553 verbatim
section Map


-- @@ L555-563 expanded
variable {M₁ N₁ M₂ N₂ M₃ N₃ : Type*} [AddCommGroup M₁] [DGAddCommGroup M₁] [Module A M₁]
  [DGModule A M₁] [AddCommGroup N₁] [DGAddCommGroup N₁] [Module A N₁] [DGModule A N₁]
  [AddCommGroup M₂] [DGAddCommGroup M₂] [Module A M₂] [DGModule A M₂] [AddCommGroup N₂]
  [DGAddCommGroup N₂] [Module A N₂] [DGModule A N₂] [AddCommGroup M₃] [DGAddCommGroup M₃]
  [Module A M₃] [DGModule A M₃] [AddCommGroup N₃] [DGAddCommGroup N₃] [Module A N₃] [DGModule A N₃]
  {f₁ : DGModuleHom A M₁ N₁} {f₂ : DGModuleHom A M₂ N₂} {f₃ : DGModuleHom A M₃ N₃}
  {a : DGModuleHom A M₁ M₂} {b : DGModuleHom A N₁ N₂}


-- @@ L565-574 expanded
/-- The morphism `Cone f₁ →ᵈᵍ[A] Cone f₂` induced by a square `b ∘ f₁ ≃ f₂ ∘ a` commuting up to
a homotopy `H` (Mathlib's `mapOfHomotopy`): `(x, y) ↦ (a x, H x + b y)`. -/
def mapOfHomotopy (H : DGHomotopy (b.comp f₁) (f₂.comp a)) : DGModuleHom A (Cone f₁) (Cone f₂) :=
  desc f₁ ((inl f₂).comp (ofHom a) (zero_add _) + (ofHom (inr f₂)).comp H.hom (add_zero _))
    ((inr f₂).comp b)
    (by
      have hH : δ (-1) 0 H.hom = ofHom (b.comp f₁) - ofHom (f₂.comp a) :=
        eq_sub_of_add_eq H.ofHom_eq.symm
      rw [δ_add, δ_ofHom_comp, δ_comp_ofHom, δ_inl, hH]
      refine Cochain.ext fun x => ?_
      simp)


-- @@ L576-580 verbatim
theorem mapOfHomotopy_apply (H : DGHomotopy (b.comp f₁) (f₂.comp a)) (p : Cone f₁) :
    mapOfHomotopy H p =
      inl f₂ (a ((fst f₁).1 p)) + inr f₂ (H.hom ((fst f₁).1 p) + b (snd f₁ p)) := by
  simp [mapOfHomotopy, desc_apply, map_add]
  abel


-- @@ L582-585 verbatim
/-- Mathlib's `triangleMapOfHomotopy_comm₂`. -/
theorem mapOfHomotopy_comp_inr (H : DGHomotopy (b.comp f₁) (f₂.comp a)) :
    (mapOfHomotopy H).comp (inr f₁) = (inr f₂).comp b :=
  inr_desc _ _ _ _


-- @@ L587-592 verbatim
/-- Mathlib's `triangleMapOfHomotopy_comm₃`, stated for `fstHom` (the third morphism of the
standard triangle is `-fstHom`). -/
theorem fstHom_comp_mapOfHomotopy (H : DGHomotopy (b.comp f₁) (f₂.comp a)) :
    (fstHom f₂).comp (mapOfHomotopy H) = (a.shift 1).comp (fstHom f₁) := by
  ext p
  simp [mapOfHomotopy, desc_apply, fstHom_eq]


-- @@ L594-596 verbatim
@[simp]
theorem map_fst_apply (h : b.comp f₁ = f₂.comp a) (p : Cone f₁) :
    (fst f₂).1 (map a b h p) = a ((fst f₁).1 p) := rfl


-- @@ L598-601 verbatim
omit [DGModule A M₁] [DGModule A N₁] [DGModule A M₂] [DGModule A N₂] in
@[simp]
theorem map_snd_apply (h : b.comp f₁ = f₂.comp a) (p : Cone f₁) :
    snd f₂ (map a b h p) = b (snd f₁ p) := rfl


-- @@ L603-611 verbatim
/-- `Cone.map` is the morphism induced by the commutative square, as in Mathlib's
`mappingCone.map`: `Cone.map a b h = desc f₁ (inl f₂ ∘ a) (inr f₂ ∘ b)`. -/
theorem map_eq_desc (h : b.comp f₁ = f₂.comp a) :
    map a b h = desc f₁ ((inl f₂).comp (ofHom a) (zero_add _)) ((inr f₂).comp b) (by
      rw [δ_ofHom_comp, δ_inl]
      change _ = ofHom ((inr f₂).comp (b.comp f₁))
      rw [h]
      rfl) := by
  refine DGModuleHom.ext fun p => ext_to ?_ ?_ <;> simp [desc_apply]


-- @@ L613-616 verbatim
/-- Mathlib's `map_eq_mapOfHomotopy`. -/
theorem map_eq_mapOfHomotopy (h : b.comp f₁ = f₂.comp a) :
    map a b h = mapOfHomotopy (DGHomotopy.ofEq h) := by
  refine DGModuleHom.ext fun p => ext_to ?_ ?_ <;> simp [mapOfHomotopy_apply]


-- @@ L618-622 expanded
omit [DGModule A M] [DGModule A N] in
/-- Mathlib's `map_id`. -/
@[simp]
theorem map_id :
    map (DGModuleHom.id : DGModuleHom A M M) (DGModuleHom.id : DGModuleHom A N N)
        (show DGModuleHom.id.comp f = f.comp DGModuleHom.id from rfl) =
      DGModuleHom.id :=
  rfl


-- @@ L624-632 expanded
omit [DGModule A M₁] [DGModule A N₁] [DGModule A M₂] [DGModule A N₂] [DGModule A M₃]
    [DGModule A N₃] in
/-- Mathlib's `map_comp`. -/
theorem map_comp {a' : DGModuleHom A M₂ M₃} {b' : DGModuleHom A N₂ N₃} (h : b.comp f₁ = f₂.comp a)
    (h' : b'.comp f₂ = f₃.comp a') :
    map (a'.comp a) (b'.comp b)
        (by rw [DGModuleHom.comp_assoc, h, ← DGModuleHom.comp_assoc, h', DGModuleHom.comp_assoc]) =
      (map a' b' h').comp (map a b h) :=
  rfl


-- @@ L634-634 verbatim
end Map


-- @@ L636-636 verbatim
/-! ### The cone of the identity -/


-- @@ L638-644 expanded
variable (M) in
/-- The mapping cone of the identity is contractible (Mathlib's `homotopyToZeroOfId`): the
homotopy is `inl ∘ snd`, `(x, y) ↦ (y, 0)`. -/
def homotopyToZeroOfId :
    DGHomotopy (DGModuleHom.id : DGModuleHom A (Cone (DGModuleHom.id : DGModuleHom A M M)) _) 0 :=
  descHomotopy DGModuleHom.id _ _ 0 (inl DGModuleHom.id) (by refine Cochain.ext fun x => ?_; simp)
    (by refine Cochain.ext fun y => ?_; simp)


-- @@ L646-649 expanded
variable (M) in
/-- The mapping cone of the identity is contractible. -/
theorem isContractible_id : IsContractible A (Cone (DGModuleHom.id : DGModuleHom A M M)) :=
  ⟨homotopyToZeroOfId M⟩


-- @@ L651-651 verbatim
end Cone


-- @@ L653-653 verbatim
end DG
