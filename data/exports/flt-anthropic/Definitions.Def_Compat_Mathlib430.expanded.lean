/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section MulAction), names suffixed `Finsupp` -/


-- @@ L22-22 verbatim
namespace Representation


-- @@ L24-24 verbatim
section MulAction


-- @@ L26-26 verbatim
variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]


-- @@ L28-35 verbatim
noncomputable def ofMulActionFinsupp : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]


-- @@ L37-37 verbatim
noncomputable abbrev leftRegularFinsupp := ofMulActionFinsupp k G G


-- @@ L39-39 verbatim
noncomputable abbrev diagonalFinsupp (n : ℕ) := ofMulActionFinsupp k G (Fin n → G)


-- @@ L41-41 verbatim
variable {k G H}


-- @@ L43-44 verbatim
theorem ofMulActionFinsupp_def (g : G) : ofMulActionFinsupp k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl


-- @@ L46-49 verbatim
@[simp]
theorem ofMulActionFinsupp_single (g : G) (x : H) (r : k) :
    ofMulActionFinsupp k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single


-- @@ L51-51 verbatim
end MulAction


-- @@ L53-53 verbatim
/-! ## Block B — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:472-483 (section Group) -/


-- @@ L55-55 verbatim
section Group


-- @@ L57-58 verbatim
variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

-- @@ L59-68 verbatim
@[simp]
theorem ofMulActionFinsupp_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulActionFinsupp k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulActionFinsupp k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]


-- @@ L70-70 verbatim
end Group


-- @@ L72-72 verbatim
section Bridge


-- @@ L74-74 verbatim
variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]


-- @@ L76-80 verbatim
noncomputable def ofMulActionFinsuppEquiv : (ofMulActionFinsupp k G H).Equiv (ofMulAction k G H) :=
  Equiv.mk (MonoidAlgebra.coeffLinearEquiv k).symm fun g => by
    rw [ofMulAction_def, ofMulActionFinsupp_def]
    ext
    simp


-- @@ L82-82 verbatim
end Bridge


-- @@ L84-84 verbatim
end Representation


-- @@ L86-86 verbatim
/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and 404-412, names suffixed `Finsupp` -/


-- @@ L88-88 verbatim
namespace Rep


-- @@ L90-90 verbatim
open CategoryTheory


-- @@ L92-92 verbatim
universe w' u v


-- @@ L94-94 verbatim
variable {k : Type u} {G : Type v} [Ring k] [Monoid G]


-- @@ L96-96 verbatim
section


-- @@ L98-98 verbatim
variable (k G)


-- @@ L100-101 verbatim
noncomputable abbrev ofMulActionFinsupp (H : Type w') [MulAction G H] : Rep k G := -- [port] `noncomputable` added (4.30 file had a noncomputable section)
  of <| Representation.ofMulActionFinsupp k G H


-- @@ L103-104 verbatim
noncomputable abbrev leftRegularFinsupp : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G G


-- @@ L106-107 verbatim
noncomputable abbrev diagonalFinsupp (n : ℕ) : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G (Fin n → G)


-- @@ L109-111 verbatim
noncomputable def ofMulActionFinsuppIso (H : Type w') [MulAction G H] :
    ofMulActionFinsupp k G H ≅ ofMulAction k G H :=
  mkIso (Representation.ofMulActionFinsuppEquiv k G H)


-- @@ L113-113 verbatim
end


-- @@ L115-116 verbatim
noncomputable abbrev leftRegularHomFinsupp (A : Rep k G) (x : A) : leftRegularFinsupp k G ⟶ A := -- [port] noncomputable
  Rep.ofHom ⟨Finsupp.lift A k G fun g ↦ A.ρ g x, fun g ↦ by ext; simp⟩


-- @@ L118-120 verbatim
theorem leftRegularHomFinsupp_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHomFinsupp A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHomFinsupp]


-- @@ L122-122 verbatim
end Rep


-- @@ L124-124 verbatim
/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/


-- @@ L126-126 verbatim
namespace AddAut


-- @@ L128-128 verbatim
section Compat430


-- @@ L130-130 verbatim
variable (A : Type*) [Add A]


-- @@ L132-142 verbatim
instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/


-- @@ L144-146 verbatim
@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl


-- @@ L148-150 verbatim
@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl


-- @@ L152-153 verbatim
@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl


-- @@ L155-156 verbatim
theorem mul_def' (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl


-- @@ L158-159 verbatim
theorem one_def' : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl


-- @@ L161-162 verbatim
theorem inv_def' (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl


-- @@ L164-166 verbatim
@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl


-- @@ L168-170 verbatim
@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl


-- @@ L172-173 verbatim
@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl


-- @@ L175-176 verbatim
@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl


-- @@ L178-179 verbatim
@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl


-- @@ L181-182 verbatim
theorem inv_apply_self' (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _


-- @@ L184-185 verbatim
theorem apply_inv_self' (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _


-- @@ L187-187 verbatim
example (e₁ e₂ : AddAut A) : e₁ * e₂ = e₁ + e₂ := rfl

-- @@ L188-188 verbatim
example : (1 : AddAut A) = 0 := rfl

-- @@ L189-189 verbatim
example (e : AddAut A) : e⁻¹ = -e := rfl


-- @@ L191-191 verbatim
end Compat430


-- @@ L193-193 verbatim
end AddAut


-- @@ L195-200 verbatim
@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)


-- @@ L202-204 verbatim
@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _


-- @@ L206-208 verbatim
/-! ### Block D (continued) — Mathlib v4.30.0 Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction (AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0 together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/


-- @@ L210-210 verbatim
namespace AddAut

-- @@ L211-216 verbatim
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add


-- @@ L218-218 verbatim
@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl


-- @@ L220-221 verbatim
instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩

-- @@ L222-222 verbatim
end AddAut


-- @@ L224-227 verbatim
/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r, IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the NEW predicates. -/


-- @@ L229-229 verbatim
section IsEllDivSequence430


-- @@ L231-231 verbatim
universe u


-- @@ L233-233 verbatim
variable {R : Type u} [CommRing R]


-- @@ L235-235 verbatim
variable (W : ℤ → R)


-- @@ L237-239 verbatim
def IsEllSequence' : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2


-- @@ L241-242 verbatim
def IsDivSequence' : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n


-- @@ L244-245 verbatim
def IsEllDivSequence' : Prop :=
  IsEllSequence' W ∧ IsDivSequence' W


-- @@ L247-248 verbatim
lemma isEllSequence'_id : IsEllSequence' id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1


-- @@ L250-251 verbatim
lemma isDivSequence'_id : IsDivSequence' id :=
  fun _ _ => Int.ofNat_dvd.mpr


-- @@ L253-254 verbatim
theorem isEllDivSequence'_id : IsEllDivSequence' id :=
  ⟨isEllSequence'_id, isDivSequence'_id⟩


-- @@ L256-256 verbatim
variable {W}


-- @@ L258-260 verbatim
lemma IsEllSequence'.smul (h : IsEllSequence' W) (x : R) : IsEllSequence' (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r


-- @@ L262-263 verbatim
lemma IsDivSequence'.smul (h : IsDivSequence' W) (x : R) : IsDivSequence' (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r


-- @@ L265-266 verbatim
lemma IsEllDivSequence'.smul (h : IsEllDivSequence' W) (x : R) : IsEllDivSequence' (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩


-- @@ L268-268 verbatim
end IsEllDivSequence430



-- @@ L271-273 verbatim
/-! ## Block F — notation `α ^+ M` for `FixedPoints.addSubgroup M α`: Mathlib v4.30.0 Mathlib/Algebra/Ring/Action/Submonoid.lean:43
(verbatim). Mathlib v4.33.0 removed the notation line; the definition itself is unchanged, so re-declaring the notation keeps
every tree statement that uses it textually and semantically identical. -/


-- @@ L275-275 verbatim
notation α "^+" M:51 => FixedPoints.addSubgroup M α


-- @@ L277-279 verbatim
/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis (adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/


-- @@ L281-281 verbatim
namespace Ideal


-- @@ L283-283 verbatim
section inertia430


-- @@ L285-286 verbatim
variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]


-- @@ L288-288 verbatim
open scoped Pointwise



-- @@ L291-303 verbatim
attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) *
      Module.finrank (R ⧸ p) (S ⧸ P) := by
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finite_of_isInvariant G p P
  have : Subgroup.index _ = _ := Nat.card_congr
    (Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]


-- @@ L305-311 verbatim
lemma ncard_primesOver_mul_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank',
    ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)


-- @@ L313-327 verbatim
attribute [local instance] Ideal.Quotient.field in
lemma card_inertia_eq_ramificationIdxIn'
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥)
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  have H := ncard_primesOver_mul_card_inertia_mul_finrank' (G := G) p P
  refine mul_right_injective₀ (IsDedekindDomain.primesOver_ncard_ne_zero p S) ?_
  refine mul_left_injective₀ (b := Module.finrank (R ⧸ p) (S ⧸ P)) ?_ ?_
  · intro e; simp [e, eq_comm, Nat.card_eq_zero, ‹Finite G›.not_infinite] at H
  dsimp only
  rw [H, mul_assoc, ← inertiaDeg_eq_of_isMaximal p P, ← inertiaDegIn_eq_inertiaDeg p P G,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G]


-- @@ L329-336 verbatim
attribute [local instance] Ideal.Quotient.field in
lemma card_stabilizer_eq' [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S] (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  rw [card_stabilizer_eq_card_inertia_mul_finrank' p P, card_inertia_eq_ramificationIdxIn' p hp,
    inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_eq_of_isMaximal p P]


-- @@ L338-338 verbatim
end inertia430


-- @@ L340-340 verbatim
end Ideal
