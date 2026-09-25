/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Subadditive
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Tactic
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open scoped Topology


-- @@ L28-61 verbatim
/-- A `ResourcePretheory` is a family of Hilbert spaces closed under tensor products, with an
  instance of `Fintype` and `DecidableEq` for each. It forms a pre-structure then on which to
  discuss resource theories. For instance, to talk about "two-party scenarios", we could write
  `ResourcePretheory (ℕ × ℕ)`, with `H (a,b) := (Fin a) × (Fin b)`.

The `Semigroup ι` structure means we have a way to take products of our labels of Hilbert spaces
in a way that is associative (with actual equality). The `prodEquiv` lets us reinterpret between
a product-labelled Hilbert spaces, and an actual pair of Hilbert spaces.
-/
class ResourcePretheory (ι : Type*) extends Semigroup ι where
  /-- The indexing of each Hilbert space -/
  H : ι → Type*
  /-- Each space is finite -/
  [FinH : ∀ i, Fintype (H i)]
  /-- Each object has decidable equality -/
  [DecEqH : ∀ i, DecidableEq (H i)]
  /-- Each space is nonempty (dimension at least 1) -/
  [NonemptyH : ∀ i, Nonempty (H i)]
  /-- The product structure induces an isomorphism of Hilbert spaces -/
  prodEquiv i j : H (i * j) ≃ (H i) × (H j)
  --Possible we want some fact like the associativity of `prod` or the existence of an identity space,
  -- which would then imply MonoidalCategory structure later (instead of just Category). For now we
  -- take the (logically equivalent, in the appropriate model) assumption that the associator is
  -- actually an equality. This is captured in the `Semigroup ι` assumption. If we wanted to turn
  -- this into something more flexible, we would replace that with `Mul ι` (dropping `mul_assoc`)
  -- and get an appropriate associator `Equiv` here.
  hAssoc i j k :
    ((prodEquiv (i * j) k).trans <|
      ((prodEquiv i j).prodCongr (Equiv.refl (H k))).trans <|
      (Equiv.prodAssoc _ _ _).trans <|
      ((Equiv.refl (H i)).prodCongr ((prodEquiv j k).symm)).trans
      (prodEquiv i (j * k)).symm
    )
     = Equiv.cast (congrArg H <| mul_assoc i j k)


-- @@ L63-63 verbatim
attribute [reducible] ResourcePretheory.FinH

-- @@ L64-64 verbatim
attribute [instance] ResourcePretheory.FinH

-- @@ L65-65 verbatim
attribute [reducible] ResourcePretheory.DecEqH

-- @@ L66-66 verbatim
attribute [instance] ResourcePretheory.DecEqH

-- @@ L67-67 verbatim
attribute [instance] ResourcePretheory.NonemptyH


-- @@ L69-69 verbatim
namespace ResourcePretheory


-- @@ L71-71 verbatim
variable {ι : Type*} [ResourcePretheory ι] {i j k l : ι}


-- @@ L73-76 expanded
/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `MState`s
that puts us in a new Hilbert space of the category. Accessible by the notation `ρ₁ ⊗ᵣ ρ₂`. -/
noncomputable def prodRelabel (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) : MState (H (i * j)) :=
  (MState.prod ρ₁ ρ₂).relabel (prodEquiv i j)


-- @@ L78-79 verbatim
@[inherit_doc]
scoped infixl:65 " ⊗ᵣ " => prodRelabel


-- @@ L81-94 expanded
theorem prodRelabel_assoc (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) (ρ₃ : MState (H k)) :
    prodRelabel (prodRelabel ρ₁ ρ₂) ρ₃ ≍ prodRelabel ρ₁ (prodRelabel ρ₂ ρ₃) :=
  by
  simp [prodRelabel, MState.relabel_kron]
  have h_equiv := hAssoc i j k
  rw [← Equiv.trans_assoc, Equiv.trans_cancel_right] at h_equiv
  have h_cong := congrArg (MState.relabel (MState.prod (MState.prod ρ₁ ρ₂) ρ₃)) h_equiv
  rw [← eq_cast_iff_heq]; swap
  · rw [mul_assoc]
  convert h_cong; clear h_equiv h_cong
  rw [← MState.relabel_cast]; swap
  · rw [mul_assoc]
  rw [MState.kron_relabel, MState.prod_assoc]
  rw [MState.relabel_comp, MState.relabel_comp, MState.relabel_comp]
  rfl


-- @@ L96-105 expanded
/--
A `MState.relabel` can be distributed across a `prodRelabel`, if you have proofs that the factors
correspond correctly. -/
theorem prodRelabel_relabel_cast_prod (ρ₁ : MState (H i)) (ρ₂ : MState (H j))
    (h : H (k * l) = H (i * j)) (hik : k = i) (hlj : l = j) :
    (prodRelabel ρ₁ ρ₂).relabel (Equiv.cast h) =
      prodRelabel (ρ₁.relabel (Equiv.cast (congrArg H hik)))
        (ρ₂.relabel (Equiv.cast (congrArg H hlj))) :=
  by
  subst hik
  subst hlj
  rfl


-- @@ L107-111 expanded
/--
The `prod` operation of `ResourcePretheory` gives the natural product operation on `CPTPMap`s. Accessible
by the notation `M₁ ⊗ᶜᵖᵣ M₂`. -/
noncomputable def prodCPTPMap (M₁ : CPTPMap (H i) (H j)) (M₂ : CPTPMap (H k) (H l)) :
    CPTPMap (H (i * k)) (H (j * l)) :=
  (CPTPMap.ofEquiv (prodEquiv j l).symm).compose
    ((CPTPMap.prod M₁ M₂).compose (CPTPMap.ofEquiv (prodEquiv i k)))


-- @@ L113-114 verbatim
@[inherit_doc]
scoped notation M₁ " ⊗ᶜᵖᵣ " M₂ => prodCPTPMap M₁ M₂


-- @@ L116-152 expanded
open ComplexOrder in
theorem PosDef.prod {ρ : MState (H i)} {σ : MState (H j)} (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef) :
    (prodRelabel ρ σ).m.PosDef :=
  by
  have : (MState.prod ρ σ).m.PosDef := MState.PosDef.kron hρ hσ
  rw [prodRelabel]
  exact
    MState.PosDef.relabel this
      (prodEquiv i j)
        --BAD old attempt at PNat powers
        -- /-- Powers of spaces. Defined for `PNat` so that we don't have zeroth powers. -/
        -- noncomputable def spacePow (i : ι) (n : ℕ+) : ι :=
        --   n.natPred.rec i (fun _ j ↦ prod j i)
        
        -- scoped notation i "⊗^H[" n "]" => spacePow i n
        
        -- @[simp]
        -- theorem spacePow_one (i : ι) : i⊗^H[1] = i :=
        --   rfl
        
        -- theorem spacePow_succ (i : ι) (n : ℕ+) : i⊗^H[n + 1] = prod (i⊗^H[n]) i := by
        --   rcases n with ⟨_|n, hn⟩
        --   · contradiction
        --   · rfl
        
        -- /-- Powers of states. Defined for `PNat`, so that we don't have zeroth powers -/
        -- noncomputable def statePow {i : ι} (ρ : MState (H i)) (n : ℕ+) : MState (H (i⊗^H[n])) :=
        --   (n.natPred.rec ρ (fun _ σ ↦ σ ⊗ᵣ ρ) : MState (H (i⊗^H[n.natPred.succPNat])))
        
        -- scoped notation ρ " ⊗ᵣ^[" n "]" => statePow ρ n
        
        -- @[simp]
        -- theorem statePow_one {i : ι} (ρ : MState (H i)) : ρ ⊗ᵣ^[1] = ρ :=
        --   rfl
        
        -- theorem statePow_succ {i : ι} (ρ : MState (H i)) (n : ℕ+) : ρ ⊗ᵣ^[n + 1] = ρ ⊗ᵣ^[n] ⊗ᵣ ρ := by
        --   rcases n with ⟨_|n, hn⟩
        --   · contradiction
        --   · rfl


-- @@ L154-157 expanded
@[simp]
theorem qRelEntropy_prodRelabel (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)) :
    qRelativeEnt (prodRelabel ρ₁ σ₁) (prodRelabel ρ₂ σ₂) =
      qRelativeEnt ρ₁ ρ₂ + qRelativeEnt σ₁ σ₂ :=
  by simp [prodRelabel]


-- @@ L159-162 expanded
@[simp]
theorem sandwichedRelRentropy_prodRelabel {α : ℝ} (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)) :
    SandwichedRelRentropy α (prodRelabel ρ₁ σ₁) (prodRelabel ρ₂ σ₂) =
      SandwichedRelRentropy α ρ₁ ρ₂ + SandwichedRelRentropy α σ₁ σ₂ :=
  by simp [prodRelabel]


-- @@ L164-164 verbatim
end ResourcePretheory


-- @@ L166-166 verbatim
open ResourcePretheory


-- @@ L168-173 verbatim
/-- A ResourcePretheory is `Unital` if it has a Hilbert space of size 1, i.e. `ℂ`. -/
class UnitalPretheory (ι : Type*) extends ResourcePretheory ι, MulOneClass ι, Unique (H 1) where
  prod_default {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel ρ (Inhabited.default : MState (H 1))) ≍ ρ
  default_prod {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel (Inhabited.default : MState (H 1)) ρ) ≍ ρ


-- @@ L175-175 verbatim
namespace UnitalPretheory


-- @@ L177-177 verbatim
variable {ι : Type*} [UnitalPretheory ι] {i j : ι}


-- @@ L179-179 verbatim
instance : Monoid ι where


-- @@ L181-192 verbatim
/-- Powers of spaces.

We define it for `Nat` in a `UnitalPretheory`. In principal this could be done for any
`ResourcePretheory` and be defined for `PNat` so that we don't have zeroth powers. In
anticipation that we might some day want that, and that we might do everything with a
non-equality associator, we keep this as its own definition and keep our own names for
rewriting theorems where possible.-/
noncomputable def spacePow (i : ι) (n : ℕ) : ι :=
  i ^ n

--This notation is less necessary now since we can just write `i ^ n` as long as it's
--a monoid.

-- @@ L193-193 verbatim
scoped notation i "⊗^H[" n "]" => spacePow i n


-- @@ L195-197 verbatim
@[simp]
theorem spacePow_zero (i : ι) : i ^ 0 = 1 := by
  rfl


-- @@ L199-201 verbatim
@[simp]
theorem spacePow_one (i : ι) : i ^ 1 = i := by
  simp


-- @@ L203-204 verbatim
theorem spacePow_succ (i : ι) (n : ℕ) : i ^ (n + 1) = (i ^ n) * i := by
  rfl


-- @@ L206-211 verbatim
theorem spacePow_add (m n : ℕ) :
    i ^ (m + n) = (i ^ m) * (i ^ n) := by
  induction n
  · simp
  · rename_i n ih
    rw [spacePow_succ, ← mul_assoc, ← add_assoc, ← ih, spacePow_succ]


-- @@ L213-215 verbatim
theorem spacePow_mul (m n : ℕ) :
    i ^ (m * n) = (i ^ m) ^ n :=
  pow_mul i m n


-- @@ L217-220 expanded
/-- Powers of states, using the resource theory's notion of product. Accessible via the notation
`ρ ⊗ᵣ^[n]`.-/
noncomputable def statePow (ρ : MState (H i)) (n : ℕ) : MState (H (i ^ n)) :=
  n.rec default (fun _ σ ↦ prodRelabel σ ρ)


-- @@ L222-223 verbatim
@[inherit_doc]
scoped notation ρ " ⊗ᵣ^[" n "]" => statePow ρ n


-- @@ L225-227 expanded
@[simp]
theorem statePow_zero (ρ : MState (H i)) : statePow ρ 0 = default :=
  rfl


-- @@ L229-234 expanded
@[simp]
theorem statePow_one (ρ : MState (H i)) : statePow ρ 1 ≍ ρ :=
  by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_one]
  · rw [eq_cast_iff_heq, statePow]
    exact default_prod ρ


-- @@ L236-237 expanded
theorem statePow_succ (ρ : MState (H i)) (n : ℕ) :
    statePow ρ (n + 1) = prodRelabel (statePow ρ n) ρ := by rfl


-- @@ L239-250 expanded
theorem statePow_add (ρ : MState (H i)) (m n : ℕ) :
    statePow ρ (m + n) ≍ prodRelabel (statePow ρ m) (statePow ρ n) :=
  by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_add]
  rw [eq_cast_iff_heq]
  induction n
  · rw [add_zero, statePow_zero]
    exact (prod_default _).symm
  · rename_i n ih
    rw [statePow_succ, ← add_assoc, statePow_succ]
    refine HEq.trans ?_ (prodRelabel_assoc _ _ _)
    congr
    apply spacePow_add


-- @@ L252-257 expanded
theorem statePow_add_relabel (ρ : MState (H i)) (m n : ℕ) :
    statePow ρ (m + n) =
      (prodRelabel (statePow ρ m) (statePow ρ n)).relabel
        (Equiv.cast (by congr; exact pow_add i m n)) :=
  by
  have h := statePow_add ρ m n
  rw [heq_iff_exists_eq_cast] at h
  obtain ⟨h, h₂⟩ := h
  rw [h₂, MState.relabel_cast]


-- @@ L259-283 expanded
set_option backward.isDefEq.respectTransparency false in
theorem statePow_mul (ρ : MState (H i)) (m n : ℕ) :
    statePow ρ (m * n) ≍ statePow (statePow ρ m) n :=
  by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_mul]
  rw [eq_cast_iff_heq]
  induction n
  · simp
  · rename_i n ih
    rw [statePow_succ, mul_add]
      --This is TERRIBLE. There has to be a better way. TODO Cleanup
      
    trans prodRelabel (statePow ρ (m * n)) (statePow ρ (m * 1))
    · apply statePow_add
    · rw [← eq_cast_iff_heq] at ih; swap
      · congr 2 <;> simp [pow_mul]
      rw [← eq_cast_iff_heq]; swap
      · congr 2 <;> simp [pow_mul]
      rw [← MState.relabel_cast _ (by simp [pow_mul])]
      rw [prodRelabel_relabel_cast_prod]
      · congr
        · rw [ih, MState.relabel_cast]
        · rw [MState.relabel_cast]
          rw [eq_cast_iff_heq]
          · rw [mul_one]
      · rw [pow_mul]
      · rw [mul_one]


-- @@ L285-290 expanded
theorem statePow_mul_relabel {i : ι} (ρ : MState (H i)) (m n : ℕ) :
    statePow ρ (m * n) =
      (statePow (statePow ρ m) n).relabel (Equiv.cast (congrArg H (pow_mul i m n))) :=
  by
  have h := statePow_mul ρ m n
  rw [heq_iff_exists_eq_cast] at h
  obtain ⟨h, h₂⟩ := h
  rw [h₂, MState.relabel_cast]


-- @@ L292-298 expanded
open ComplexOrder in
theorem PosDef.npow {ρ : MState (H i)} (hρ : ρ.m.PosDef) (n : ℕ) : (statePow ρ n).m.PosDef :=
  by
  induction n
  · rw [statePow_zero, spacePow_zero]
    exact MState.posDef_of_unique default
  · apply ResourcePretheory.PosDef.prod ‹_› hρ


-- @@ L300-303 expanded
theorem statePow_rw {n m : ℕ} (h : n = m) (ρ : MState (H i)) :
    statePow ρ n = (statePow ρ m).relabel (Equiv.cast (by congr)) :=
  by
  subst n
  simp


-- @@ L305-313 expanded
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem qRelEntropy_statePow (ρ σ : MState (H i)) (n : ℕ) :
    qRelativeEnt (statePow ρ n) (statePow σ n) = n * qRelativeEnt ρ σ :=
  by
  induction n
  · simp
  · rename_i n ih
    rw [statePow_succ, statePow_succ, qRelEntropy_prodRelabel]
    simp [ih, add_mul]


-- @@ L315-317 expanded
theorem sInf_spectrum_rprod {j : ι} (ρ : MState (H i)) (σ : MState (H j)) :
    sInf (spectrum ℝ (prodRelabel ρ σ).m) = sInf (spectrum ℝ ρ.m) * sInf (spectrum ℝ σ.m) := by
  rw [← MState.sInf_spectrum_prod, prodRelabel, MState.spectrum_relabel]


-- @@ L319-331 expanded
set_option backward.isDefEq.respectTransparency false in
lemma sInf_spectrum_spacePow (σ : MState (H i)) (n : ℕ) :
    sInf (spectrum ℝ (statePow σ n).m) = sInf (spectrum ℝ σ.m) ^ n :=
  by
  induction n
  · simp only [statePow_zero, pow_zero]
    conv =>
      enter [1, 1, 2]
      equals 1 =>
        ext1
        simp [default, MState.uniform, MState.ofClassical, MState.m, HermitianMat.diagonal]
    rw [spectrum.one_eq, csInf_singleton]
  · rename_i n ih
    rw [statePow_succ, sInf_spectrum_rprod, ih, pow_succ]


-- @@ L333-342 expanded
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sandwichedRelRentropy_statePow {α : ℝ} (ρ σ : MState (H i)) (n : ℕ) :
    SandwichedRelRentropy α (statePow ρ n) (statePow σ n) = n * SandwichedRelRentropy α ρ σ :=
  by
  induction n
  · rw [statePow_zero, statePow_zero, spacePow_zero]
    simp
  · rename_i n ih
    rw [statePow_succ, statePow_succ, sandwichedRelRentropy_prodRelabel]
    simp [ih, add_mul]


-- @@ L344-346 verbatim
end UnitalPretheory

/- FreeStateTheories: theories defining some sets of "free states" within a collection of Hilbert spaces. -/


-- @@ L348-364 expanded
/--
A `FreeStateTheory` is a collection of mixed states (`MState`s) in a `ResourcePretheory` that obeys
some necessary axioms:
 * For each Hilbert space `H i`, the free states are a closed, convex set
 * For each Hilbert space `H i`, there is a free state of full rank
 * If `ρᵢ ∈ H i` and `ρⱼ ∈ H j` are free, then `ρᵢ ⊗ ρⱼ` is free in `H (prod i j)`.
-/
class FreeStateTheory (ι : Type*) extends ResourcePretheory ι where
  /-- The set of states we're calling "free" -/
  IsFree : Set (MState (toResourcePretheory.H i))
  /-- The set F(H) of free states is closed -/
  free_closed : IsClosed (@IsFree i)
  /-- The set F(H) of free states is convex (more precisely, their matrices are) -/
  free_convex : Convex ℝ (MState.M '' (@IsFree i))
  /-- The set of free states is closed under tensor product -/
  free_prod {ρ₁ : MState (H i)} {ρ₂ : MState (H j)} (h₁ : IsFree ρ₁) (h₂ : IsFree ρ₂) :
    IsFree (prodRelabel ρ₁ ρ₂)
  /--
  The set F(H) of free states contains a full-rank state `ρfull`, equivalently `ρfull` is positive definite. -/
  free_fullRank (i : ι) : open ComplexOrder in ∃ (ρ : MState (H i)), ρ.m.PosDef ∧ IsFree ρ


-- @@ L366-366 verbatim
namespace FreeStateTheory


-- @@ L368-368 verbatim
variable {ι : Type*} [FreeStateTheory ι] {i : ι}


-- @@ L370-371 verbatim
noncomputable instance Inhabited_IsFree : Inhabited (IsFree (i := i)) :=
  ⟨⟨(free_fullRank i).choose, (free_fullRank i).choose_spec.right⟩⟩


-- @@ L373-376 verbatim
theorem IsFree.of_unique [Unique (H i)] (ρ : MState (H i)) : ρ ∈ IsFree := by
  obtain ⟨σ, h₁, h₂⟩ := free_fullRank i
  convert! h₂
  apply Subsingleton.allEq


-- @@ L378-384 verbatim
/--The set of free states is compact because it's a closed subset of a compact space. -/
theorem IsCompact_IsFree : IsCompact (IsFree (i := i)) :=
  .of_isClosed_subset isCompact_univ free_closed (Set.subset_univ _)

--Also this needs to be generalized to other convex sets. I think it should work for any
--(well-behaved?) Mixable instance, it certainly works for any `Convex` set (of which `IsFree`
-- is one, the only relevant property here is `free_convex`.

-- @@ L385-390 expanded
theorem IsFree.mix {ι : Type*} [FreeStateTheory ι] {i : ι} {σ₁ σ₂ : MState (H i)} (hσ₁ : IsFree σ₁)
    (hσ₂ : IsFree σ₂) (p : Prob) : IsFree (p [σ₁ ↔ σ₂]) :=
  by
  obtain ⟨m, hm₁, hm₂⟩ :=
    free_convex (i := i) ⟨σ₁, hσ₁, rfl⟩ ⟨σ₂, hσ₂, rfl⟩ p.zero_le (1 - p).zero_le (by simp)
  simp [Mixable.mix, Mixable.mix_ab, MState.instMixable]
  simp at hm₂
  convert! ← hm₁


-- @@ L392-392 verbatim
end FreeStateTheory


-- @@ L394-394 verbatim
open UnitalPretheory

-- @@ L395-395 verbatim
open FreeStateTheory


-- @@ L397-397 verbatim
class UnitalFreeStateTheory (ι : Type*) extends FreeStateTheory ι, UnitalPretheory ι


-- @@ L399-402 verbatim
namespace UnitalFreeStateTheory

--Things like asymptotically free operations, measures of non-freeness, etc. that can be stated
--entirely in terms of the free states (without referring to operations) go here.


-- @@ L404-404 verbatim
variable {ι : Type*} [UnitalFreeStateTheory ι] {i : ι}


-- @@ L406-412 expanded
theorem _root_.FreeStateTheory.IsFree.npow {i : ι} {ρ : MState (H i)} (hρ : IsFree ρ) (n : ℕ) :
    IsFree (statePow ρ n) := by
  induction n
  · rw [statePow_zero, spacePow_zero]
    apply IsFree.of_unique
  · rw [statePow_succ]
    exact FreeStateTheory.free_prod ‹_› hρ


-- @@ L414-418 verbatim
@[simp]
theorem relabel_cast_isFree {i j : ι} (ρ : MState (H i)) (h : j = i) {h' : H j = H i}:
    ρ.relabel (Equiv.cast h') ∈ IsFree ↔ ρ ∈ IsFree := by
  subst h
  simp


-- @@ L420-420 verbatim
open NNReal


-- @@ L422-436 expanded
/-- In a `FreeStateTheory`, we have free states of full rank, therefore the minimum relative entropy
of any state `ρ` to a free state is finite. -/
@[aesop (rule_sets := [finiteness]) safe]
lemma relativeEntResource_ne_top (ρ : MState (H i)) : ⨅ σ ∈ IsFree, qRelativeEnt ρ σ ≠ ⊤ :=
  by
  let ⟨w, h⟩ := free_fullRank i
  apply ne_top_of_le_ne_top _ (iInf_le _ w)
  simp only [ne_eq, iInf_eq_top, Classical.not_imp]
  constructor
  · exact h.2
  · refine ne_of_apply_ne ENNReal.toEReal (qRelativeEnt_ker (ρ := ρ) (?_) ▸ EReal.coe_ne_top _)
    convert @bot_le _ _ (Submodule.instOrderBot) _
    have := h.1.toLin_ker_eq_bot
    simp [LinearMap.ker_eq_bot', HermitianMat.ker] at this ⊢
    intro m hm
    simpa only [WithLp.ofLp_eq_zero] using this m congr($hm)


-- @@ L438-439 expanded
noncomputable def RelativeEntResource : MState (H i) → ℝ≥0 := fun ρ ↦
  (⨅ σ ∈ IsFree, qRelativeEnt ρ σ).untop (relativeEntResource_ne_top ρ)


-- @@ L441-441 verbatim
scoped notation "𝑅ᵣ" => RelativeEntResource


-- @@ L443-450 expanded
set_option backward.isDefEq.respectTransparency false in
theorem exists_isFree_relativeEntResource (ρ : MState (H i)) :
    ∃ σ ∈ IsFree, qRelativeEnt ρ σ = 𝑅ᵣ ρ :=
  by
  obtain ⟨σ, hσ₁, hσ₂⟩ :=
    IsCompact_IsFree.exists_isMinOn_lowerSemicontinuousOn (s := IsFree (i := i)) (f := fun σ ↦
      qRelativeEnt ρ σ) Set.Nonempty.of_subtype (by fun_prop)
  use σ, hσ₁
  rw [RelativeEntResource, ← hσ₂.iInf_eq hσ₁, ENNReal.ofNNReal, WithTop.coe_untop, iInf_subtype']


-- @@ L452-470 expanded
set_option backward.isDefEq.respectTransparency false in
theorem RelativeEntResource.Subadditive (ρ : MState (H i)) :
    Subadditive fun n ↦ 𝑅ᵣ (statePow ρ n) := by
  intro m n
  obtain ⟨σ₂, hσ₂f, hσ₂d⟩ := exists_isFree_relativeEntResource (statePow ρ m)
  obtain ⟨σ₃, hσ₃f, hσ₃d⟩ := exists_isFree_relativeEntResource (statePow ρ n)
  simp only [RelativeEntResource, ← NNReal.coe_add, coe_le_coe]
  rw [← ENNReal.coe_le_coe]
  simp [RelativeEntResource, ENNReal.ofNNReal] at hσ₂d hσ₃d ⊢
  rw [← hσ₂d, ← hσ₃d]
  clear hσ₂d hσ₃d
  have ht₁ : i ^ (m + n) = i ^ m * i ^ n := spacePow_add m n
  have ht := congrArg H ht₁
  refine le_trans (biInf_le (i := (prodRelabel σ₂ σ₃).relabel (Equiv.cast ht)) _ ?_) ?_
  · simp only [ht₁, relabel_cast_isFree]
    exact free_prod hσ₂f hσ₃f
  · apply le_of_eq
    rw [← qRelEntropy_prodRelabel]
    exact
      qRelEntropy_heq_congr ht (statePow_add ρ m n)
        (by rw [MState.relabel_cast]; exact cast_heq _ _)


-- @@ L472-477 verbatim
noncomputable def RegularizedRelativeEntResource (ρ : MState (H i)) : ℝ≥0 :=
  ⟨(RelativeEntResource.Subadditive ρ).lim, by
    rw [Subadditive.lim]
    apply Real.sInf_nonneg
    rintro x ⟨x, hx, rfl⟩
    positivity⟩


-- @@ L479-479 verbatim
scoped notation "𝑅ᵣ∞" => RegularizedRelativeEntResource


-- @@ L481-488 expanded
/-- Lemma 5 -/
theorem RelativeEntResource.tendsto (ρ : MState (H i)) :
    Filter.atTop.Tendsto (fun n ↦ 𝑅ᵣ (statePow ρ n) / n) (𝓝 (𝑅ᵣ∞ ρ)) :=
  by
  rw [← NNReal.tendsto_coe]
  apply (RelativeEntResource.Subadditive ρ).tendsto_lim
  use 0
  rintro _ ⟨y, rfl⟩
  positivity


-- @@ L490-499 expanded
/-- Alternate version of Lemma 5 which states the convergence with the `ENNReal`
expression for `RelativeEntResource`, as opposed its `untop`-ped `NNReal` value. -/
theorem RelativeEntResource.tendsto_ennreal (ρ : MState (H i)) :
    Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, qRelativeEnt (statePow ρ n) σ) / ↑n) (𝓝 (𝑅ᵣ∞ ρ)) :=
  by
  refine Filter.Tendsto.congr' ?_ (ENNReal.tendsto_coe.mpr <| RelativeEntResource.tendsto ρ)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  use 1; intros
  rw [RelativeEntResource, ENNReal.coe_div (by positivity), ENNReal.coe_natCast]
  congr
  apply WithTop.coe_untop


-- @@ L501-502 expanded
noncomputable def GlobalRobustness {i : ι} : MState (H i) → ℝ≥0 := fun ρ ↦
  sInf {s | ∃ σ, (⟨1 / (1 + s), by bound⟩ [ρ ↔ σ]) ∈ IsFree}


-- @@ L504-510 expanded
/--
A sequence of operations `f_n` is asymptotically nongenerating if `lim_{n→∞} RG(f_n(ρ_n)) = 0`, where
RG is `GlobalRobustness` and `ρ_n` is any sequence of free states. Equivalently, we can take the `max` (
over operations and states) on the left-hand side inside the limit.
-/
def IsAsymptoticallyNongenerating (dI dO : ι)
    (f : (n : ℕ) → CPTPMap (H (spacePow dI n)) (H (spacePow dO n))) : Prop :=
  ∀ (ρs : (n : ℕ) → MState (H (spacePow dI n))),
    (∀ n, IsFree (ρs n)) → Filter.atTop.Tendsto (fun n ↦ GlobalRobustness ((f n) (ρs n))) (𝓝 0)


-- @@ L512-512 verbatim
end UnitalFreeStateTheory
