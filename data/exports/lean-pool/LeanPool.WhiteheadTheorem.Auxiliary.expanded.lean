/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.TopCat.Basic


-- @@ L12-16 verbatim
/-!
# LeanPool.WhiteheadTheorem.Auxiliary

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Auxiliary`.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
namespace CategoryTheory


-- @@ L23-25 verbatim
lemma eq_of_comp_right_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : X ⟶ Y) [IsIso h] {f g : Y ⟶ Z} (e : h ≫ f = h ≫ g) : f = g := by
  simpa only [IsIso.inv_hom_id_assoc] using congrArg (inv h ≫ ·) e

-- @@ L26-28 verbatim
lemma eq_of_comp_left_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : Y ⟶ Z) [IsIso h] {f g : X ⟶ Y} (e : f ≫ h = g ≫ h) : f = g := by
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using congrArg (· ≫ inv h) e


-- @@ L30-30 verbatim
end CategoryTheory



-- @@ L33-33 verbatim
namespace TopCat


-- @@ L35-35 verbatim
open CategoryTheory


-- @@ L37-40 verbatim
instance isIso_of_isEmpty {X Y : TopCat.{u}} [IsEmpty X] [IsEmpty Y] (f : X ⟶ Y) : IsIso f := by
  use ofHom ⟨isEmptyElim, by fun_prop⟩
  constructor
  all_goals ext x; exact isEmptyElim x


-- @@ L42-45 verbatim
instance isEmpty_sigmaObj_of_isEmpty_dom
    {β : Type w} (f : β → TopCat.{u}) [Limits.HasCoproduct f] [IsEmpty β] : IsEmpty ↑(∐ f) :=
  have i : ∐ f ⟶ TopCat.of PEmpty.{u + 1} := Limits.Sigma.desc isEmptyElim
  ⟨fun z ↦ isEmptyElim (i z)⟩


-- @@ L47-47 verbatim
end TopCat



-- @@ L50-50 verbatim
namespace ContinuousMap


-- @@ L52-54 verbatim
lemma eq_of_topCat_ofHom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (e : TopCat.ofHom f = TopCat.ofHom g) : f = g :=
  TopCat.hom_ext_iff.mp e


-- @@ L56-56 verbatim
namespace Homotopic


-- @@ L58-60 verbatim
lemma of_eq (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (hfg : f = g) : f.Homotopic g :=
  hfg ▸ ContinuousMap.Homotopic.refl f


-- @@ L62-62 verbatim
end Homotopic


-- @@ L64-64 verbatim
end ContinuousMap



-- @@ L67-69 verbatim
/-!
Auxiliary lemmas used in `largeCubeHomeoPDisk` and `largeCubeBoundaryHomeoPDiskBoundary`
-/


-- @@ L71-75 verbatim
lemma Real.forall_le_of_iSup_le_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := fun i ↦ by
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact Real.isLUB_sSup ‹_› hbdd |>.left (Set.mem_range_self i) |>.trans hf


-- @@ L77-79 verbatim
lemma Real.range_bddAbove_of_finite_domain {ι : Type*} (f : ι → ℝ) [Finite ι] :
    BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove


-- @@ L81-83 verbatim
lemma Real.forall_le_of_iSup_le_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a :=
  forall_le_of_iSup_le_of_bddAbove (range_bddAbove_of_finite_domain f) hf


-- @@ L85-90 verbatim
lemma Real.le_iSup_of_exists_ge_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i := by
  obtain ⟨i, hi⟩ := hf
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact hi.trans <| (Real.isLUB_sSup ‹_› hbdd).left (Set.mem_range_self i)


-- @@ L92-94 verbatim
lemma Real.le_iSup_of_exists_ge_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i :=
  le_iSup_of_exists_ge_of_bddAbove (range_bddAbove_of_finite_domain f) hf


-- @@ L96-110 verbatim
lemma Real.exists_eq_of_iSup_eq_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hfz : ∃ i, f i ≥ 0) (hf : ⨆ i, f i = a) : ∃ i, f i = a := by
  have : Nonempty ι := hfz.nonempty
  have iSup_lt_iff : ⨆ i ∈ (Set.univ : Set ι), f i < a ↔ ∀ i ∈ Set.univ, f i < a := by
    apply Set.Finite.ciSup_lt_iff Set.finite_univ
    simp_all
  have lt_iSup_iff : a < ⨆ i, f i ↔ ∃ i, a < f i :=
    lt_ciSup_iff (range_bddAbove_of_finite_domain f)
  by_contra nex; simp only [not_exists] at nex
  have : ∀ (i : ι), f i < a := fun i ↦ by
    obtain h | h | h := lt_trichotomy (f i) a
    · exact h
    · exfalso; exact nex i h
    · exfalso; exact ne_of_lt (lt_iSup_iff.mpr ⟨i, h⟩) hf.symm
  simp_all




-- @@ L114-114 verbatim
namespace ContinuousMap


-- @@ L116-116 verbatim
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]


-- @@ L118-118 verbatim
variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))

-- @@ L119-122 verbatim
variable
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j),
    φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))


-- @@ L124-140 verbatim
/-- `liftCoverClosed` -/
noncomputable def liftCoverClosed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_inter_iff]
      conv => lhs; rhs; ext hxi; arg 2; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
      tauto
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv_rhs => ext x; arg 1; ext i; rw [this]
      conv_rhs => ext x; rw [← Set.iUnion_inter, H, Set.univ_inter]
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)


-- @@ L142-144 verbatim
theorem liftCoverClosed_coe {i : ι} (x : S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i x := by
  rw [liftCoverClosed, ContinuousMap.coe_mk, Set.liftCover_coe _]


-- @@ L146-148 verbatim
theorem liftCoverClosed_coe' {i : ι} (x : α) (hx : x ∈ S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i ⟨x, hx⟩ := by
  rw [← liftCoverClosed_coe]


-- @@ L150-150 verbatim
end ContinuousMap
