/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.Shapes.UnitInterval
public import Mathlib.Topology.Homotopy.HomotopyGroup


-- @@ L11-15 verbatim
/-!
# LeanPool.WhiteheadTheorem.Shapes.Cube

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.Cube`.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
open scoped unitInterval Topology Topology.Homotopy



-- @@ L23-23 verbatim
namespace Cube


-- @@ L25-30 verbatim
/-- `Cube.boundaryJar (n + 1) = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹` -/
def boundaryJar (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | (∃ i, y i = 0 ∨ y i = 1) ∧
      (y (Fin.last _) = 1 → ∃ i < Fin.last _, y i = 0 ∨ y i = 1) }


-- @@ L32-36 verbatim
/-- `Cube.boundaryLid (n + 1) = Iⁿ × {1} ⊆ Iⁿ⁺¹` -/
def boundaryLid (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | y (Fin.last _) = 1}


-- @@ L38-39 verbatim
/-- `«term∂I^_»` -/
scoped[Topology.Homotopy] notation "∂I^" n => Cube.boundary (Fin n)

-- @@ L40-41 verbatim
/-- `«term⊔I^_»` -/
scoped[Topology.Homotopy] notation "⊔I^" n => Cube.boundaryJar n


-- @@ L43-44 expanded
/-- `boundaryIncl` -/
def boundaryIncl (n : ℕ) : C(Cube.boundary (Fin n), I^(Fin n)) :=
  ⟨Subtype.val, continuous_subtype_val⟩


-- @@ L45-46 expanded
/-- `boundaryJarIncl` -/
def boundaryJarIncl (n : ℕ) : C(Cube.boundaryJar n, I^(Fin n)) :=
  ⟨Subtype.val, continuous_subtype_val⟩


-- @@ L48-49 expanded
instance isEmpty_boundary_zero : IsEmpty (Cube.boundary (Fin 0)) :=
  Set.isEmpty_coe_sort.mpr <| Set.subset_empty_iff.mp fun _ ⟨i, _⟩ ↦ isEmptyElim i


-- @@ L50-51 expanded
instance isEmpty_boundaryJar_zero : IsEmpty (Cube.boundaryJar 0) := by rw [Set.isEmpty_coe_sort];
  rfl


-- @@ L53-56 expanded
lemma boundaryJar_subset_boundary (n : ℕ) : (Cube.boundaryJar n) ⊆ (Cube.boundary (Fin n)) :=
  match n with
  | 0 => fun y hy ↦ isEmptyElim (⟨y, hy⟩ : Cube.boundaryJar 0)
  | _ + 1 => fun _ ⟨hy1, _⟩ ↦ hy1


-- @@ L58-61 expanded
/-- `boundaryJarInclToBoundary` -/
def boundaryJarInclToBoundary (n : ℕ) : C(Cube.boundaryJar n, Cube.boundary (Fin n))
    where
  toFun := fun ⟨y, hy⟩ ↦ ⟨y, boundaryJar_subset_boundary n hy⟩
  continuous_toFun := by fun_prop


-- @@ L63-68 expanded
lemma mem_boundaryJar_of_lt_last {n : ℕ} (y : I^(Fin (n + 1)))
    (hy : ∃ i < Fin.last _, y i = 0 ∨ y i = 1) : y ∈ Cube.boundaryJar (n + 1) :=
  by
  obtain ⟨i, ⟨hi, hyi⟩⟩ := hy
  constructor
  · exact ⟨i, hyi⟩
  · intro _; exact ⟨i, ⟨hi, hyi⟩⟩


-- @@ L70-81 expanded
lemma mem_boundaryJar_of_exists_eq_zero {n : ℕ} (y : I^Fin n) (hy : ∃ i, y i = 0) :
    y ∈ Cube.boundaryJar n :=
  match n with
  | 0 => isEmptyElim hy.choose
  | n + 1 => by
    obtain ⟨i, hi⟩ := hy
    constructor
    · use i; left; exact hi
    · intro hn1
      by_cases h : i = Fin.last _
      · rw [← h] at hn1; exfalso; exact (by norm_num : (1 : I) ≠ 0) (hn1.symm.trans hi)
      · use i; exact ⟨Fin.lt_last_iff_ne_last.mpr h, Or.inl hi⟩


-- @@ L83-93 expanded
lemma mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary {n : ℕ} (y : I^Fin n)
    (hy : y ∈ Cube.boundary (Fin n)) : y ∈ Cube.boundaryLid n ∨ y ∈ Cube.boundaryJar n :=
  match n with
  | 0 => isEmptyElim (⟨y, hy⟩ : Cube.boundary (Fin 0))
  | n + 1 => by
    by_cases hyn : y (Fin.last _) = 1
    · left; exact hyn
    · right
      constructor
      · exact hy
      · intro hyn'; exfalso; exact hyn hyn'


-- @@ L95-109 expanded
/-- `⊔I^1 = {0}` is a singleton -/
instance uniqueBoundaryJarOne : Unique (Cube.boundaryJar 1)
    where
  default :=
    ⟨0,
      ⟨by use 0; simp only [Pi.zero_apply, zero_ne_one, or_false], by intro h;
        simp only [Pi.zero_apply, zero_ne_one] at h⟩⟩
  uniq := fun ⟨y, ⟨⟨i, hi⟩, hy2⟩⟩ ↦ by
    ext j
    have : Unique (Fin 1) := by infer_instance
    have iz : i = 0 := Subsingleton.eq_zero i
    have jz : j = 0 := Subsingleton.eq_zero j
    rw [iz] at hi
    obtain h0 | h1 := hi
    all_goals simp only [Pi.zero_apply, Set.Icc.coe_zero, Set.Icc.coe_eq_zero]; rw [jz]
    · exact h0
    · exfalso; obtain ⟨k, hk⟩ := hy2 h1; exact Nat.not_succ_le_zero k hk.left


-- @@ L111-122 verbatim
/-- `homeoNeqLast` -/
def homeoNeqLast {n : ℕ} : (I^ Fin n) ≃ₜ I^{ j : Fin (n + 1) // j ≠ Fin.last _ } :=
  Homeomorph.piCongr
    { toFun i := ⟨i.castSucc, by
        simp_all ⟩
      invFun i := ⟨i, by
        have := i.2
        simp only [ne_eq] at this
        exact Fin.lt_last_iff_ne_last.mpr this ⟩
      left_inv i := by simp only [Fin.val_castSucc, Fin.eta]
      right_inv i := by simp only [ne_eq, Fin.castSucc_mk, Fin.eta, Subtype.coe_eta] }
    fun _ ↦ Homeomorph.refl _


-- @@ L124-127 verbatim
/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `(yₙ, (y₀, y₁, …, yₙ₋₁))` -/
def splitAtLast {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ I × (I^ Fin n) :=
  splitAt (Fin.last _) |>.trans <|
    Homeomorph.prodCongr (Homeomorph.refl _) homeoNeqLast.symm


-- @@ L129-131 verbatim
/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `((y₀, y₁, …, yₙ₋₁), yₙ)` -/
def splitAtLastComm {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ (I^ Fin n) × I :=
  splitAtLast.trans <| Homeomorph.prodComm I (I^ Fin n)


-- @@ L133-136 verbatim
lemma splitAtLast_fst_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).fst = y (Fin.last n) := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]


-- @@ L138-142 verbatim
lemma splitAtLastComm_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLastComm y).snd = y (Fin.last n) := by
  simp only [splitAtLastComm, splitAtLast, ne_eq, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.coe_prodComm, Prod.swap_prod_mk]


-- @@ L144-148 verbatim
lemma splitAtLast_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).snd = (splitAtLastComm y).fst := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
    splitAtLastComm, Homeomorph.coe_prodComm, Prod.swap_prod_mk]


-- @@ L150-155 verbatim
lemma splitAtLast_snd_apply_eq {n : ℕ} (y : I^Fin (n + 1)) (i : Fin n) :
    (splitAtLast y).snd i = y i.castSucc := by
  simp only [splitAtLast, ne_eq, homeoNeqLast, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq]
  rfl


-- @@ L157-161 verbatim
lemma splitAtLast_symm_apply_last {n : ℕ} (t : I) (y : I^Fin n) :
    (splitAtLast.symm ⟨t, y⟩) (Fin.last _) = t := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]


-- @@ L163-171 verbatim
lemma splitAtLast_symm_apply_eq_of_neq_last {n : ℕ} (t : I) (y : I^Fin n) (i : Fin (n + 1))
    (hi : i ≠ Fin.last _) :
    (splitAtLast.symm ⟨t, y⟩) i = y ⟨i, Fin.lt_last_iff_ne_last.mpr hi⟩ := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply]
  simp only [homeoNeqLast, ne_eq, Homeomorph.piCongr_apply]
  simp_all only []
  rfl


-- @@ L173-209 expanded
/-- `y ∈ ⊔I^(n+1)` if and only if either `y` is on the bottom face,
or its first `n` coordinates constitute a point in `∂I^n`.
Note that `(splitAtLast y).fst` is the last (`n`-th) coordinate. -/
lemma mem_boundaryJar_iff_splitAtLast {n : ℕ} {y : I^Fin (n + 1)} :
    y ∈ (Cube.boundaryJar (n + 1)) ↔
      (splitAtLast y).fst = 0 ∨ (splitAtLast y).snd ∈ Cube.boundary (Fin n) :=
  by
  constructor
  · intro hy
    simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
      Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]
    by_cases h0 : y (Fin.last n) = 0
    · left; exact h0
    · right
      by_cases h1 : y (Fin.last n) = 1
      · have := hy.right h1
        obtain ⟨i, hi, h⟩ := hy.right h1
        use ⟨i, hi⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
      · obtain ⟨i, h⟩ := hy.left
        have : i ≠ (Fin.last n) := fun hn ↦ by rw [hn] at h; rcases h with h | h;
          exacts [h0 h, h1 h]
        use ⟨i.val, Fin.lt_last_iff_ne_last.mpr this⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
  · intro hy
    rcases hy with hy | ⟨i, hi⟩
    · rw [splitAtLast_fst_eq] at hy
      apply mem_boundaryJar_of_exists_eq_zero
      use Fin.last n
    · rw [splitAtLast_snd_apply_eq] at hi
      constructor
      · use i.castSucc
      · intro hyn
        use i.castSucc
        exact ⟨Fin.castSucc_lt_last i, hi⟩


-- @@ L211-218 expanded
/-- An easy corrolary of `mem_boundaryJar_iff_splitAtLast` -/
lemma splitAtLast_snd_mem_boundary_of_last_neq_zero {n : ℕ} {y : I^Fin (n + 1)}
    (hy : y ∈ Cube.boundaryJar (n + 1)) (hyn : y (Fin.last _) ≠ 0) :
    (splitAtLast y).snd ∈ Cube.boundary (Fin n) :=
  by
  rw [← splitAtLast_fst_eq y] at hyn
  cases mem_boundaryJar_iff_splitAtLast.mp hy
  · exfalso; exact hyn ‹_›
  · assumption


-- @@ L220-226 expanded
lemma splitAtLast_symm_mem_boundary_of_mem_boundary {n : ℕ} {y : I^Fin n} (t : I)
    (hy : y ∈ Cube.boundary (Fin n)) : splitAtLast.symm ⟨t, y⟩ ∈ Cube.boundary (Fin (n + 1)) :=
  by
  obtain ⟨i, hi⟩ := hy
  use i.castSucc
  rw [splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
  exact hi


-- @@ L228-235 verbatim
/-- The inclusion from the n-dimensional cube to the top face of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, 1).
(Although `1` appears first in this definition, it is actually the last coordinate
in `(I^ Fin (n + 1))`, due to `Cube.insertAt`). -/
def inclToTop {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := splitAtLast.symm ⟨1, y⟩
  continuous_toFun := splitAtLast.symm.continuous.comp <|
    Continuous.prodMk continuous_const continuous_id


-- @@ L237-237 verbatim
namespace inclToTop


-- @@ L239-246 expanded
/-- (y, 1) is in the `boundary`. -/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToTop y ∈ Cube.boundary (Fin (n + 1)) :=
  by
  use Fin.last _
  right
  simp only [inclToTop, splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, ContinuousMap.coe_mk, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]


-- @@ L248-267 expanded
/-- If y is in the `boundary`, then (y, 1) is in the `boundaryJar`. -/
lemma mem_boundaryJar_of {n : ℕ} {y : I^Fin n} (hy : y ∈ Cube.boundary (Fin n)) :
    inclToTop y ∈ Cube.boundaryJar (n + 1) :=
  by
  obtain ⟨i, hi⟩ := hy
  simp only [inclToTop, ContinuousMap.coe_mk]
  constructor
  · use
      Fin.last
        _ -- the n-th coordinate of (y, 1) is 1
          
    simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
      Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
      Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte, one_ne_zero, or_true]
  · intro _
    use i.castSucc
    constructor
    · simp only [Fin.castSucc_lt_last]
    ·
      simpa only [splitAtLast, ne_eq, homeoNeqLast, Fin.coe_eq_castSucc,
        Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
        Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply,
        id_eq, Homeomorph.funSplitAt_symm_apply, Fin.natCast_eq_last, Fin.castSucc_ne_last,
        ↓reduceDIte, Homeomorph.piCongr_apply, Equiv.coe_fn_symm_mk, Fin.val_castSucc, Fin.eta]


-- @@ L269-269 verbatim
end inclToTop


-- @@ L271-276 verbatim
lemma splitAtLast_inclToTop_eq {n : ℕ} {y : I^Fin n} :
    splitAtLast (inclToTop y) = ⟨1, y⟩ := by
  simp only [splitAtLast, ne_eq, inclToTop, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, ContinuousMap.coe_mk, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]


-- @@ L278-281 verbatim
/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁)` -/
def discardLast {n : ℕ} : C(I^ Fin (n + 1), I^ Fin n) where
  toFun y := fun i ↦ y ⟨i.val, i.prop.trans (by omega : n < n + 1)⟩
  continuous_toFun := by fun_prop


-- @@ L283-287 verbatim
/-- (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) -/
def inclToBot {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := Cube.insertAt (Fin.last _) ⟨0, Cube.homeoNeqLast y⟩
  continuous_toFun := (Cube.insertAt _).continuous.comp <|
    Continuous.prodMk continuous_const Cube.homeoNeqLast.continuous


-- @@ L289-289 verbatim
namespace inclToBot


-- @@ L291-296 expanded
/-- (y, 0) is in the `boundary`. -/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToBot y ∈ Cube.boundary (Fin (n + 1)) :=
  by
  use Fin.last _
  left
  simp only [inclToBot, ne_eq, ContinuousMap.coe_mk, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]


-- @@ L298-304 expanded
/-- (y, 0) is in the `boundaryJar`. -/
lemma mem_boundaryJar {n : ℕ} (y : I^Fin n) : inclToBot y ∈ Cube.boundaryJar (n + 1) :=
  by
  constructor
  · exact mem_boundary y
  · intro h; exfalso
    have : inclToBot y (Fin.last n) = (0 : ℝ) := by simp [inclToBot]
    simp_all


-- @@ L306-306 verbatim
end inclToBot


-- @@ L308-311 expanded
/-- The inclusion (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) to the bottom face of `⊔I^(n+1)` -/
def inclToBoundaryJarBot {n : ℕ} : C(I^Fin n, Cube.boundaryJar (n + 1))
    where
  toFun y := ⟨inclToBot y, inclToBot.mem_boundaryJar y⟩
  continuous_toFun := Continuous.subtype_mk inclToBot.continuous _


-- @@ L313-332 expanded
/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to
the sides of `⊔I^(n+1)`, i.e.,
the closure of the complement of the top and bottom faces of `∂I^(n+1)`. -/
def inclToBoundaryJarSides {n : ℕ} : C((Cube.boundary (Fin n)) × I, Cube.boundaryJar (n + 1))
    where
  toFun := fun yt ↦
    ⟨(toContinuousMap splitAtLastComm.symm |>.comp <|
          ContinuousMap.prodMap (boundaryIncl n) (ContinuousMap.id _))
        yt,
      by
      obtain ⟨⟨y, ⟨i, hyi⟩⟩, t⟩ := yt
      constructor
      · use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last]
      · intro _; use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last, Fin.castSucc_lt_last]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Homeomorph.comp_continuous_iff]
    apply ContinuousMapClass.map_continuous


-- @@ L334-338 expanded
/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to the sides of
the $(n+1)$-dimensional cube. -/
def inclToSides {n : ℕ} : C((Cube.boundary (Fin n)) × I, I^Fin (n + 1))
    where
  toFun := Subtype.val ∘ inclToBoundaryJarSides
  continuous_toFun := Continuous.subtype_val inclToBoundaryJarSides.continuous


-- @@ L340-340 verbatim
end Cube



-- @@ L343-343 verbatim
namespace TopCat


-- @@ L345-346 verbatim
/-- `cube` -/
def cube (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| I^ Fin n


-- @@ L348-349 verbatim
/-- `cubeBoundary` -/
def cubeBoundary (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundary (Fin n)


-- @@ L351-352 verbatim
/-- `cubeBoundaryJar` -/
def cubeBoundaryJar (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundaryJar n


-- @@ L354-355 verbatim
/-- `𝕀 n` denotes the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "𝕀 " => cube


-- @@ L357-358 verbatim
/-- `∂𝕀 n` denotes the boundary of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "∂𝕀 " => cubeBoundary


-- @@ L360-362 verbatim
/-- `⊔𝕀 n` denotes the "boundary jar" ($⊔Iⁿ⁺¹ = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹$)
of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "⊔𝕀 " => cubeBoundaryJar


-- @@ L364-369 verbatim
/-- The inclusion `∂𝕀 n ⟶ 𝕀 n` of the boundary of the `n`-cube. -/
def cubeBoundaryIncl (n : ℕ) : cubeBoundary.{u} n ⟶ cube.{u} n :=
  ofHom
    { toFun := fun ⟨⟨p, _⟩⟩ ↦ ⟨p⟩
      continuous_toFun :=
        continuous_uliftUp.comp <| continuous_subtype_val.comp continuous_induced_dom }


-- @@ L371-375 verbatim
/-- `cubeBoundaryJarInclToBoundary` -/
def cubeBoundaryJarInclToBoundary (n : ℕ) : cubeBoundaryJar.{u} n ⟶ cubeBoundary.{u} n :=
  ofHom
    { toFun := fun ⟨p⟩ ↦ ⟨Cube.boundaryJarInclToBoundary n p⟩
      continuous_toFun := by fun_prop }


-- @@ L377-379 expanded
@[simp↓]
lemma cubeBoundaryIncl_apply_down_eq {n : ℕ} (y : I^Fin n) (hy : y ∈ Cube.boundary (Fin n)) :
    (cubeBoundaryIncl n ⟨⟨y, hy⟩⟩).down = y :=
  rfl


-- @@ L381-396 verbatim
/-- `cubeSplitAtLast` -/
def cubeSplitAtLast {n : ℕ} : 𝕀 (n + 1) ≅ TopCat.of (I × 𝕀 n) where
  hom := ofHom ⟨fun ⟨y⟩ ↦ ⟨(Cube.splitAtLast y).fst, ⟨(Cube.splitAtLast y).snd⟩⟩, by fun_prop⟩
  inv := ofHom ⟨fun ⟨t, ⟨y⟩⟩ ↦ ⟨Cube.splitAtLast.symm ⟨t, y⟩⟩, by fun_prop⟩
  hom_inv_id := by
    ext ⟨y⟩
    change ULift.up (Cube.splitAtLast.symm (Cube.splitAtLast y)) = ULift.up y
    exact congrArg ULift.up (Cube.splitAtLast.symm_apply_apply y)
  inv_hom_id := by
    ext ⟨t, ⟨y⟩⟩
    all_goals simp only [hom_id, ContinuousMap.id_apply]
    · congr 1
      change (Cube.splitAtLast (Cube.splitAtLast.symm _)).fst = _
      simp only [Homeomorph.apply_symm_apply]
    · change ({ down := (Cube.splitAtLast (Cube.splitAtLast.symm (t, y))).2 } : ULift _) = _
      simp only [Homeomorph.apply_symm_apply]


-- @@ L398-401 verbatim
/-- This lemma should be applied before expanding the `match` expression. -/
@[simp↓]
lemma cubeSplitAtLast_inv_down_eq {n : ℕ} (t : I) (y : 𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, y⟩).down = Cube.splitAtLast.symm ⟨t, y.down⟩ := rfl


-- @@ L403-406 expanded
lemma cubeSplitAtLast_inv_mem_boundary_of_mem_boundary {n : ℕ} (t : I) (y : ∂𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩).down ∈ Cube.boundary (Fin (n + 1)) :=
  by
  simp only [↓cubeSplitAtLast_inv_down_eq]
  apply Cube.splitAtLast_symm_mem_boundary_of_mem_boundary t y.down.property


-- @@ L409-409 verbatim
namespace cubeBoundary


-- @@ L411-425 verbatim
/-- The inclusion from the n-dimensional cube to the top or bottom face
of the boundary of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, t). -/
def cubeInclToBotOrTop {n : ℕ} (t : unitInterval.zeroOne) : 𝕀 n ⟶ ∂𝕀 (n + 1) :=
  ofHom
    { toFun := fun ⟨y⟩ ↦ ⟨Cube.splitAtLast.symm ⟨unitInterval.zeroOneIncl t, y⟩, by
        use Fin.last _
        simp only [Cube.splitAtLast, ne_eq, ContinuousMap.coe_mk,
          Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
          Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply,
          id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]
        obtain ht | ht := unitInterval.zeroOne.val_eq_zero_or_val_eq_one t
        · left; simp_all only [Set.Icc.mk_zero]
        · right; simp_all only [Set.Icc.mk_one] ⟩
      continuous_toFun := by fun_prop }


-- @@ L427-429 verbatim
/-- `botOrTop` -/
abbrev botOrTop (n : ℕ) (t : unitInterval.zeroOne) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | y (Fin.last _) = unitInterval.zeroOneIncl t}


-- @@ L431-433 verbatim
/-- `sides` -/
abbrev sides (n : ℕ) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | ∃ i < Fin.last _, y i = 0 ∨ y i = 1}


-- @@ L435-440 verbatim
lemma cubeInclToBotOrTop_mem_botOrTop
    {n : ℕ} (t : unitInterval.zeroOne) (y : 𝕀 n) :
    cubeInclToBotOrTop t y ∈ botOrTop n t := by
  change (Cube.splitAtLast.symm (unitInterval.zeroOneIncl t, y.down)) (Fin.last n) =
    unitInterval.zeroOneIncl t
  rw [Cube.splitAtLast_symm_apply_last]


-- @@ L442-447 verbatim
/-- Given a point on the boundary of the `n`-dimensional cube,
cast it as a point on the boundary of the `(n + 1)`-dimensional cube
by specifying the height `t : I`. -/
def castSucc {n : ℕ} (t : I) (y : ∂𝕀 n) : ∂𝕀 (n + 1) :=
  ⟨cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩ |>.down,
    cubeSplitAtLast_inv_mem_boundary_of_mem_boundary t y⟩


-- @@ L449-458 verbatim
lemma castSucc_mem_sides {n : ℕ} (t : I) (y : ∂𝕀 n) :
    castSucc t y ∈ sides n := by
  obtain ⟨⟨y, ⟨i, hi⟩⟩⟩ := y
  use i.castSucc
  constructor
  · exact Fin.castSucc_lt_last i
  · change Cube.splitAtLast.symm (t, y) i.castSucc = 0 ∨
      Cube.splitAtLast.symm (t, y) i.castSucc = 1
    rw [Cube.splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
    exact hi


-- @@ L460-460 verbatim
end cubeBoundary


-- @@ L462-462 verbatim
end TopCat
