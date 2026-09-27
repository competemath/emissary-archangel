/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.Tactics


-- @@ L11-13 verbatim
/-!
# LeanPool.LowDimSolvClassification.Semidirect
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
section lie_semidirect


-- @@ L19-21 verbatim
variable {K : Type*} (L J : Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L]
    [LieAlgebra K J]
  (φ : L →ₗ⁅K⁆ LieDerivation K J J)


-- @@ L23-27 verbatim
/-- The semidirect product of two Lie algebras `L` and `J`, defined by specifying a homomorphism
from `L` to the Lie algebra of derivations of `J`. The homomorphism `φ` indexes the type, but does
not appear in the underlying carrier; consuming it via `id` keeps the linter happy. -/
def LieSemidirectProduct (φ : L →ₗ⁅K⁆ LieDerivation K J J) : Type _ :=
  (id φ : L →ₗ⁅K⁆ LieDerivation K J J) |> fun _ ↦ L × J

-- @@ L28-28 verbatim
attribute [local implicit_reducible] LieSemidirectProduct


-- @@ L30-32 verbatim
variable {K : Type*} {L J : Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L]
    [LieAlgebra K J]
  {φ : L →ₗ⁅K⁆ LieDerivation K J J}


-- @@ L34-35 verbatim
@[inherit_doc]
notation:35 L " ⋉[" φ:35 "] " J:35 => LieSemidirectProduct L J φ


-- @@ L37-37 verbatim
namespace LieSemidirectProduct


-- @@ L39-42 expanded
@[ext]
theorem ext {a b : LieSemidirectProduct L J φ} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b :=
  by
  unfold LieSemidirectProduct
  ext <;> assumption


-- @@ L44-44 verbatim
instance : AddCommGroup (LieSemidirectProduct L J φ) := (inferInstance : AddCommGroup (L × J))


-- @@ L46-46 verbatim
instance : Module K (LieSemidirectProduct L J φ) := (inferInstance : Module K (L × J))


-- @@ L48-49 expanded
@[simp]
theorem add_left (a b : LieSemidirectProduct L J φ) : (a + b).1 = a.1 + b.1 :=
  rfl


-- @@ L51-52 expanded
@[simp]
theorem add_right (a b : LieSemidirectProduct L J φ) : (a + b).2 = a.2 + b.2 :=
  rfl


-- @@ L54-55 expanded
@[simp]
theorem zero_left : (0 : LieSemidirectProduct L J φ).1 = 0 :=
  rfl


-- @@ L57-58 expanded
@[simp]
theorem zero_right : (0 : LieSemidirectProduct L J φ).2 = 0 :=
  rfl


-- @@ L60-61 expanded
@[simp]
theorem neg_left (a : LieSemidirectProduct L J φ) : (-a).1 = -a.1 :=
  rfl


-- @@ L63-64 expanded
@[simp]
theorem neg_right (a : LieSemidirectProduct L J φ) : (-a).2 = -a.2 :=
  rfl


-- @@ L66-67 expanded
@[simp]
theorem smul_left (k : K) (a : LieSemidirectProduct L J φ) : (k • a).1 = k • a.1 :=
  rfl


-- @@ L69-70 expanded
@[simp]
theorem smul_right (k : K) (a : LieSemidirectProduct L J φ) : (k • a).2 = k • a.2 :=
  rfl


-- @@ L72-74 expanded
instance : Bracket (LieSemidirectProduct L J φ) (LieSemidirectProduct L J φ) :=
  { bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩ }


-- @@ L76-77 expanded
lemma bracket_def (a b : LieSemidirectProduct L J φ) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩ :=
  rfl


-- @@ L79-107 expanded
instance : LieRing (LieSemidirectProduct L J φ) :=
  {
    (inferInstance :
      AddCommGroup
        (LieSemidirectProduct L J
          φ)) with
    add_lie := by
      intro x y z
      simp only [bracket_def, add_left, add_right]
      congr 1
      · simp only [add_lie]
      · simp only [LieDerivation.coe_add, Pi.add_apply, map_add, add_lie]
        module
    lie_add := by
      intro x y z
      simp only [bracket_def, add_left, add_right]
      congr 1
      · simp only [lie_add]
      · simp only [map_add, LieDerivation.coe_add, Pi.add_apply, lie_add]
        module
    lie_self := by
      intro x
      simp only [bracket_def, lie_self, sub_self, add_zero]
      congr
    leibniz_lie := by
      intro x y z
      simp only [bracket_def]
      congr 1
      · simp only [lie_lie, sub_add_cancel]
      · simp only [map_add, map_sub, LieDerivation.apply_lie_eq_sub, LieHom.map_lie,
          LieDerivation.lie_apply, lie_add, lie_sub, add_lie, sub_lie, lie_lie]
        { try simp only [lie_add, add_lie, lie_smul, smul_lie, lie_neg, neg_lie, sub_lie, lie_sub]
          match_scalars_lie <;> try ring
        } }


-- @@ L109-117 expanded
instance : LieAlgebra K (LieSemidirectProduct L J φ) :=
  {
    lie_smul := by
      intro k y z
      simp only [bracket_def, smul_left, lie_smul, smul_right, map_smul, LieDerivation.coe_smul,
        Pi.smul_apply]
      ext
      · simp []
      · simp [smul_sub] }


-- @@ L119-137 expanded
/-- TODO. -/
def inl : L →ₗ⁅K⁆ LieSemidirectProduct L J φ :=
  { toFun := fun x ↦ ⟨x, 0⟩,
    map_add' := by
      intro x y
      ext
      · simp only [add_left]
      · simp only [add_right, add_zero]
    map_smul' := by
      intro k x
      ext
      · simp only [RingHom.id_apply, smul_left]
      · simp only [RingHom.id_apply, smul_right, smul_zero]
    map_lie' := by
      intro x y
      ext
      · simp only [bracket_def]
      · simp only [bracket_def, map_zero, sub_self, lie_self, add_zero] }


-- @@ L139-157 expanded
/-- TODO. -/
def inr : J →ₗ⁅K⁆ LieSemidirectProduct L J φ :=
  { toFun := fun x ↦ ⟨0, x⟩,
    map_add' := by
      intro x y
      ext
      · simp only [add_left, add_zero]
      · simp only [add_right]
    map_smul' := by
      intro k x
      ext
      · simp only [RingHom.id_apply, smul_left, smul_zero]
      · simp only [RingHom.id_apply, smul_right]
    map_lie' := by
      intro x y
      ext <;>
        simp only [bracket_def, lie_self, map_zero, LieDerivation.coe_zero, Pi.zero_apply, sub_self,
          zero_add] }


-- @@ L159-169 expanded
/-- TODO. -/
def fst : LieSemidirectProduct L J φ →ₗ⁅K⁆ L :=
  { toFun := fun x ↦ x.1, map_add' := by simp_all
    map_smul' := by simp_all
    map_lie' := by
      intro x y
      simp only [bracket_def] }


-- @@ L171-172 expanded
@[simp]
theorem fst_inl (x : L) : fst (inl x : LieSemidirectProduct L J φ) = x :=
  rfl


-- @@ L174-175 expanded
@[simp]
theorem fst_inr (x : J) : fst (inr x : LieSemidirectProduct L J φ) = 0 :=
  rfl


-- @@ L177-178 expanded
@[simp]
theorem fst_inl' (x : L) : (inl x : LieSemidirectProduct L J φ).1 = x :=
  rfl


-- @@ L180-181 expanded
@[simp]
theorem fst_inr' (x : J) : (inr x : LieSemidirectProduct L J φ).1 = 0 :=
  rfl


-- @@ L183-184 expanded
@[simp]
theorem snd_inl' (x : L) : (inl x : LieSemidirectProduct L J φ).2 = 0 :=
  rfl


-- @@ L186-187 expanded
@[simp]
theorem snd_inr' (x : J) : (inr x : LieSemidirectProduct L J φ).2 = x :=
  rfl


-- @@ L189-193 expanded
@[simp]
theorem inl_left_add_inr_right (x : LieSemidirectProduct L J φ) : inl x.1 + inr x.2 = x :=
  by
  ext
  · simp only [add_left, fst_inl', fst_inr', add_zero]
  · simp only [add_right, snd_inl', snd_inr', zero_add]


-- @@ L195-195 verbatim
variable (φ : L →ₗ⁅K⁆ LieDerivation K J J)


-- @@ L197-198 expanded
/-- TODO. -/
def leftSubalgebra : LieSubalgebra K (LieSemidirectProduct L J φ) :=
  LieHom.range inl


-- @@ L200-201 expanded
/-- TODO. -/
def rightIdeal : LieIdeal K (LieSemidirectProduct L J φ) :=
  LieHom.ker fst


-- @@ L203-223 expanded
/-- TODO. -/
def rightIdealEquivRight : rightIdeal φ ≃ₗ⁅K⁆ J :=
  { toFun := fun x ↦ x.val.2
    map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, add_right]
    map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, smul_right, RingHom.id_apply]
    map_lie' := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      change x.1 = 0 at hx
      change y.1 = 0 at hy
      change
        (⁅(⟨x, hx⟩ : rightIdeal φ).val, (⟨y, hy⟩ : rightIdeal φ).val⁆ :
              LieSemidirectProduct L J φ).2 =
          ⁅x.2, y.2⁆
      simp only [bracket_def]
      simp_all
    invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
    left_inv := by
      intro x
      have : x.val.1 = 0 := x.prop
      ext
      · rw [this]
      · rfl
    right_inv := fun _ ↦ rfl }


-- @@ L225-238 expanded
theorem range_inr_eq_ker_fst : LieHom.range inr = (rightIdeal φ).toLieSubalgebra :=
  by
  ext x
  unfold rightIdeal
  rw [← LieSubalgebra.mem_coe (LieIdeal.toLieSubalgebra K (LieSemidirectProduct L J φ) fst.ker),
    LieIdeal.coe_toLieSubalgebra, SetLike.mem_coe, LieHom.mem_ker]
  constructor
  · intro ⟨y, h⟩
    rw [← h, LieHom.coe_toLinearMap, fst_inr]
  · intro h
    use x.2
    rw [LieHom.coe_toLinearMap]
    nth_rw 2 [← inl_left_add_inr_right x]
    simp only [fst, LieHom.coe_mk] at h
    simp_all


-- @@ L240-246 expanded
theorem finrank_eq [StrongRankCondition K] [Module.Free K L] [Module.Free K J] [Module.Finite K L]
    [Module.Finite K J] :
    Module.finrank K (LieSemidirectProduct L J φ) = Module.finrank K L + Module.finrank K J :=
  Module.finrank_prod


-- @@ L247-247 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L249-256 expanded
/-- Any semidirect product of the base field with an abelian Lie algebra is almost abelian. -/
theorem isAlmostAbelian {φ : K →ₗ⁅K⁆ LieDerivation K L L} [IsLieAbelian L] [StrongRankCondition K]
    [Module.Free K L] [Module.Finite K L] :
    LieAlgebra.IsAlmostAbelian K (LieSemidirectProduct K L φ) :=
  by
  refine ⟨rightIdeal φ, ?_, ?_⟩
  · exact (rightIdealEquivRight φ).injective.isLieAbelian (by assumption)
  ·
    rw [finrank_eq, Module.finrank_self,
      LinearEquiv.finrank_eq (rightIdealEquivRight φ).toLinearEquiv, add_comm]


-- @@ L258-258 verbatim
end LieSemidirectProduct


-- @@ L260-260 verbatim
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]


-- @@ L262-262 verbatim
end lie_semidirect


-- @@ L264-266 verbatim
section lie_direct

/- Direct product/sum of Lie algebra -/


-- @@ L268-268 verbatim
variable {K L J : Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]


-- @@ L270-272 verbatim
instance instBracketProdLeanPool : Bracket (L × J) (L × J) := {
  bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩
}


-- @@ L274-275 verbatim
lemma Prod.bracket_def (a b : L × J) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩ := rfl


-- @@ L277-286 verbatim
instance instLieRingProdLeanPool : LieRing (L × J) := {
  (inferInstance : AddCommGroup (L × J)) with
  add_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, add_lie, Prod.snd_add,
    Prod.mk_add_mk]
  lie_add := fun _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, lie_add, Prod.snd_add,
    Prod.mk_add_mk, implies_true]
  lie_self := fun _ ↦ by simp only [Prod.bracket_def, lie_self, Prod.mk_zero_zero]
  leibniz_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, lie_lie, Prod.mk_add_mk,
    sub_add_cancel]
}


-- @@ L288-291 verbatim
instance instLieAlgebraProdLeanPool : LieAlgebra K (L × J) := {
  lie_smul := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.smul_fst, lie_smul, Prod.smul_snd,
    Prod.smul_mk]
}


-- @@ L293-293 verbatim
variable (K L J : Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]


-- @@ L295-305 verbatim
/-- TODO. -/
def LieHom.inl : L →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨x, 0⟩,
  map_add' := by
    simp_all
  map_smul' := by
    simp_all
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}


-- @@ L307-317 verbatim
/-- TODO. -/
def LieHom.inr : J →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨0, x⟩,
  map_add' := by
    simp_all
  map_smul' := by
    simp_all
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}


-- @@ L319-327 verbatim
/-- TODO. -/
def LieHom.fst : L × J →ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.1,
  map_add' := by
    simp_all
  map_smul' := by
    simp_all
  map_lie' := rfl
}


-- @@ L329-337 verbatim
/-- TODO. -/
def LieHom.snd : L × J →ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.2,
  map_add' := by
    simp_all
  map_smul' := by
    simp_all
  map_lie' := rfl
}


-- @@ L339-340 verbatim
/-- TODO. -/
def leftIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.snd K L J)


-- @@ L342-361 verbatim
/-- TODO. -/
def leftIdealEquivLeft : leftIdeal K L J ≃ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.val.1
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.fst_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_fst,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    change (⁅(⟨x, hx⟩ : leftIdeal K L J).val, (⟨y, hy⟩ : leftIdeal K L J).val⁆ : L × J).1 = ⁅x.1,
      y.1⁆
    rfl
  invFun := fun x ↦ ⟨⟨x, 0⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.2 = 0 := x.prop
    ext
    · rfl
    · rw [this]
  right_inv := fun _ ↦ rfl
}


-- @@ L363-364 verbatim
/-- TODO. -/
def rightIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.fst K L J)


-- @@ L366-385 verbatim
/-- TODO. -/
def rightIdealEquivRight : rightIdeal K L J ≃ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.val.2
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.snd_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_snd,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    change (⁅(⟨x, hx⟩ : rightIdeal K L J).val, (⟨y, hy⟩ : rightIdeal K L J).val⁆ : L × J).2 = ⁅x.2,
      y.2⁆
    rfl
  invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.1 = 0 := x.prop
    ext
    · rw [this]
    · rfl
  right_inv := fun _ ↦ rfl
}


-- @@ L387-396 expanded
/-- TODO. -/
def Prod.toLieSemidirectProduct :
    (L × J) ≃ₗ⁅K⁆ LieSemidirectProduct L J (0 : L →ₗ⁅K⁆ LieDerivation K J J) :=
  { LinearEquiv.refl K (L × J) with
    map_lie' := by
      rintro x y
      change (⁅x.1, y.1⁆, ⁅x.2, y.2⁆) = (⁅x.1, y.1⁆, _)
      simp only [LinearEquiv.refl_toLinearMap, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.id_coe, id_eq, FunLike.coe_zero, Pi.zero_apply, LieDerivation.coe_zero, sub_self,
        zero_add] }


-- @@ L398-398 verbatim
end lie_direct
