/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.Cograph


-- @@ L8-8 verbatim
set_option linter.unusedSectionVars false

-- @@ L9-9 verbatim
set_option linter.unusedFintypeInType false

-- @@ L10-10 verbatim
set_option linter.unusedDecidableInType false


-- @@ L12-12 verbatim
open scoped BigOperators Pointwise

-- @@ L13-13 verbatim
open Set

-- @@ L14-14 verbatim
open MeasureTheory

-- @@ L15-15 verbatim
open SimpleGraph


-- @@ L17-17 verbatim
universe u v w


-- @@ L19-19 verbatim
namespace HansenCograph


-- @@ L21-23 verbatim
/-!
## Hansen polytope
-/


-- @@ L25-25 verbatim
section HansenPolytope


-- @@ L27-27 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L29-40 verbatim
/--
Hansen polytope

    H(G) = conv( (1, STAB(G)) ∪ (-1, -STAB(G)) ).

Ambient space is `ℝ × (V → ℝ)`.
-/
def hansen (G : SimpleGraph V) :
    Set (ℝ × (V → ℝ)) :=
  convexHull ℝ
    (((fun p : V → ℝ => ((1 : ℝ), p)) '' stab G) ∪
     ((fun p : V → ℝ => ((-1 : ℝ), -p)) '' stab G))


-- @@ L42-44 verbatim
theorem convex_hansen (G : SimpleGraph V) :
    Convex ℝ (hansen G) := by
  exact convex_convexHull ℝ _


-- @@ L46-50 verbatim
private theorem convex_hansen_top_image (G : SimpleGraph V) :
    Convex ℝ ((fun p : V → ℝ => ((1 : ℝ), p)) '' stab G) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, (convex_stab G) hp hq ha hb hab, ?_⟩
  ext <;> simp [hab]


-- @@ L52-62 verbatim
private theorem convex_hansen_bottom_image (G : SimpleGraph V) :
    Convex ℝ ((fun p : V → ℝ => ((-1 : ℝ), -p)) '' stab G) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, (convex_stab G) hp hq ha hb hab, ?_⟩
  dsimp
  apply Prod.ext
  · change (-1 : ℝ) = a * (-1) + b * (-1)
    linarith
  · funext v
    change -(a * p v + b * q v) = a * (-p v) + b * (-q v)
    ring


-- @@ L64-76 verbatim
private theorem hansen_eq_convexJoin (G : SimpleGraph V) :
    hansen G =
      convexJoin ℝ
        ((fun p : V → ℝ => ((1 : ℝ), p)) '' stab G)
        ((fun p : V → ℝ => ((-1 : ℝ), -p)) '' stab G) := by
  unfold hansen
  apply Convex.convexHull_union
  · exact convex_hansen_top_image G
  · exact convex_hansen_bottom_image G
  · exact ⟨((1 : ℝ), (0 : V → ℝ)),
      ⟨(0 : V → ℝ), zero_mem_stab G, rfl⟩⟩
  · exact ⟨((-1 : ℝ), (0 : V → ℝ)),
      ⟨(0 : V → ℝ), zero_mem_stab G, by simp⟩⟩


-- @@ L78-122 verbatim
theorem mem_hansen_iff (G : SimpleGraph V)
    (r : ℝ) (z : V → ℝ) :
    (r, z) ∈ hansen G ↔
      r ∈ Set.Icc (-1 : ℝ) 1 ∧
        z ∈ sectionSet G ((r + 1) / 2) := by
  rw [hansen_eq_convexJoin, mem_convexJoin]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, hrz⟩
    change
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
        a • ((1 : ℝ), p) + b • ((-1 : ℝ), -q) = (r, z) at hrz
    rcases hrz with ⟨a, b, ha, hb, hab, hrz⟩
    have hr := congrArg Prod.fst hrz
    have hz := congrArg Prod.snd hrz
    have ha_formula : (r + 1) / 2 = a := by
      dsimp at hr
      linarith
    constructor
    · constructor <;> dsimp at hr <;> linarith
    · rw [ha_formula]
      unfold sectionSet
      refine ⟨a • p, ⟨p, hp, rfl⟩,
        (-(1 - a)) • q, ⟨q, hq, rfl⟩, ?_⟩
      dsimp at hz ⊢
      rw [← hz]
      have hb_formula : b = 1 - a := by linarith
      rw [hb_formula]
      module
  · rintro ⟨hr, hz⟩
    let a : ℝ := (r + 1) / 2
    have ha0 : 0 ≤ a := by dsimp [a]; linarith [hr.1]
    have ha1 : a ≤ 1 := by dsimp [a]; linarith [hr.2]
    unfold sectionSet at hz
    rcases hz with ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨((1 : ℝ), p), ⟨p, hp, rfl⟩,
      ((-1 : ℝ), -q), ⟨q, hq, rfl⟩, ?_⟩
    refine ⟨a, 1 - a, ha0, sub_nonneg.mpr ha1, by ring, ?_⟩
    apply Prod.ext
    · change a * 1 + (1 - a) * (-1) = r
      dsimp [a]
      ring
    · funext v
      change a * p v + (1 - a) * (-q v) =
        a * p v + (-(1 - a)) * q v
      ring


-- @@ L124-143 verbatim
private theorem sectionSet_subset_centeredCube (G : SimpleGraph V)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    sectionSet G x ⊆ Set.Icc (fun _ : V => (-1 : ℝ)) (fun _ => 1) := by
  intro z hz
  unfold sectionSet at hz
  rcases hz with ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
  constructor <;> intro v
  all_goals
    have hp0 := stab_coordinate_nonneg G hp v
    have hp1 := stab_coordinate_le_one G hp v
    have hq0 := stab_coordinate_nonneg G hq v
    have hq1 := stab_coordinate_le_one G hq v
    have hxp0 : 0 ≤ x * p v := mul_nonneg hx0 hp0
    have hxp1 : x * p v ≤ x := by
      simpa using mul_le_mul_of_nonneg_left hp1 hx0
    have hxq0 : 0 ≤ (1 - x) * q v := mul_nonneg (sub_nonneg.mpr hx1) hq0
    have hxq1 : (1 - x) * q v ≤ 1 - x :=
      by simpa using mul_le_mul_of_nonneg_left hq1 (sub_nonneg.mpr hx1)
    dsimp
    linarith


-- @@ L145-150 verbatim
private theorem sectionSet_volume_ne_top (G : SimpleGraph V)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    volume (sectionSet G x) ≠ ⊤ := by
  exact ne_of_lt <| lt_of_le_of_lt
    (measure_mono (sectionSet_subset_centeredCube G hx0 hx1))
    isCompact_Icc.measure_lt_top


-- @@ L152-158 verbatim
/-!
## The antiblocker identity for cographs

The generic perfect-graph version of this identity is the weighted perfect
graph theorem.  For cographs, the cotree recursion gives a short direct proof:
products and free sums are exchanged by antiblocking.
-/


-- @@ L160-164 verbatim
/-- Coordinate description of the antiblocker of a stable-set polytope. -/
def StabAntiblockerCondition {X : Type*} [Fintype X]
    (G : SimpleGraph X) (y : X → ℝ) : Prop :=
  (∀ v, 0 ≤ y v) ∧
    ∀ s : Finset X, G.IsIndepSet (↑s : Set X) → ∑ v ∈ s, y v ≤ 1


-- @@ L166-169 verbatim
/-- The complement stable-set polytope realizes this antiblocker. -/
def HasStabAntiblocker {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) : Prop :=
  ∀ y : X → ℝ, StabAntiblockerCondition G y → y ∈ stab Gᶜ


-- @@ L171-185 verbatim
private theorem hasStabAntiblocker_bot_of_subsingleton
    {X : Type*} [Fintype X] [DecidableEq X] [Subsingleton X] :
    HasStabAntiblocker (⊥ : SimpleGraph X) := by
  classical
  intro y hy
  have hc : (⊥ : SimpleGraph X)ᶜ = ⊥ := by
    ext u v
    simp [Subsingleton.elim u v]
  rw [hc, stab_bot]
  constructor
  · exact hy.1
  · intro v
    have hs : (⊥ : SimpleGraph X).IsIndepSet (↑({v} : Finset X) : Set X) := by
      simp
    simpa using hy.2 {v} hs


-- @@ L187-214 expanded
private theorem hasStabAntiblocker_join {X : Type u} {Y : Type v} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (A : SimpleGraph X) (B : SimpleGraph Y) (hA : HasStabAntiblocker A)
    (hB : HasStabAntiblocker B) : HasStabAntiblocker (graphJoin A B) := by
  classical
  intro z hz
  let x : X → ℝ := fun a => z (.inl a)
  let y : Y → ℝ := fun b => z (.inr b)
  have hxcond : StabAntiblockerCondition A x :=
    by
    constructor
    · intro a
      exact hz.1 (.inl a)
    · intro s hs
      have hs' := join_sumFinset_left_indep A B hs
      have h := hz.2 (sumFinset s (∅ : Finset Y)) hs'
      simpa [x, sumFinset] using h
  have hycond : StabAntiblockerCondition B y :=
    by
    constructor
    · intro b
      exact hz.1 (.inr b)
    · intro t ht
      have ht' := join_sumFinset_right_indep A B ht
      have h := hz.2 (sumFinset (∅ : Finset X) t) ht'
      simpa [y, sumFinset] using h
  rw [compl_join_eq_sum, stab_sum_eq_split_preimage]
  exact ⟨hA x hxcond, hB y hycond⟩


-- @@ L216-344 verbatim
private theorem hasStabAntiblocker_sum
    {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : SimpleGraph X) (B : SimpleGraph Y)
    (hA : HasStabAntiblocker A) (hB : HasStabAntiblocker B) :
    HasStabAntiblocker (A ⊕g B) := by
  classical
  intro z hz
  let x : X → ℝ := fun a => z (.inl a)
  let y : Y → ℝ := fun b => z (.inr b)
  let stableA : Finset (Finset X) :=
    Finset.univ.powerset.filter
      (fun s => A.IsIndepSet (↑s : Set X))
  have hstableA : stableA.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [stableA]
  obtain ⟨sA, hsA_mem, hsAmax⟩ :=
    Finset.exists_max_image stableA (fun s => ∑ a ∈ s, x a) hstableA
  have hsA : A.IsIndepSet (↑sA : Set X) := by
    simpa [stableA] using hsA_mem
  let a : ℝ := ∑ u ∈ sA, x u
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact Finset.sum_nonneg fun u _ => hz.1 (.inl u)
  have ha1 : a ≤ 1 := by
    have hs := sumFinset_indep A B hsA
      (by simp : B.IsIndepSet (↑(∅ : Finset Y) : Set Y))
    have h := hz.2 (sumFinset sA (∅ : Finset Y)) hs
    simpa [a, x, sumFinset] using h
  let p : X → ℝ := if a = 0 then 0 else fun u => x u / a
  let q : Y → ℝ := if 1 - a = 0 then 0 else fun v => y v / (1 - a)
  have hpcond : StabAntiblockerCondition A p := by
    constructor
    · intro u
      dsimp [p]
      split_ifs with ha
      · simp
      · exact div_nonneg (hz.1 (.inl u)) ha0
    · intro s hs
      have hs_mem : s ∈ stableA := by simp [stableA, hs]
      have hmax := hsAmax s hs_mem
      change (∑ u ∈ s, x u) ≤ a at hmax
      dsimp [p]
      split_ifs with ha
      · simp
      · change (∑ u ∈ s, x u / a) ≤ 1
        rw [← Finset.sum_div]
        exact (div_le_one (lt_of_le_of_ne ha0 (Ne.symm ha))).mpr hmax
  have hqcond : StabAntiblockerCondition B q := by
    constructor
    · intro v
      dsimp [q]
      split_ifs with hrema
      · simp
      · exact div_nonneg (hz.1 (.inr v)) (sub_nonneg.mpr ha1)
    · intro t ht
      have hsumIndep := sumFinset_indep A B hsA ht
      have hbound := hz.2 (sumFinset sA t) hsumIndep
      have hsplit : (∑ w ∈ sumFinset sA t, z w) =
          (∑ u ∈ sA, x u) + ∑ v ∈ t, y v := by
        have hdisj : Disjoint
            (sA.map ⟨Sum.inl, Sum.inl_injective⟩)
            (t.map ⟨Sum.inr, Sum.inr_injective⟩) := by
          apply Finset.disjoint_left.mpr
          intro w hwL hwR
          simp only [Finset.mem_map] at hwL hwR
          rcases hwL with ⟨u, hu, rfl⟩
          simp at hwR
        unfold sumFinset
        rw [Finset.sum_union hdisj]
        simp [x, y]
      have hyt : ∑ v ∈ t, y v ≤ 1 - a := by
        rw [hsplit] at hbound
        dsimp [a]
        linarith
      dsimp [q]
      split_ifs with hrema
      · simp
      · change (∑ v ∈ t, y v / (1 - a)) ≤ 1
        rw [← Finset.sum_div]
        exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr ha1)
          (Ne.symm hrema))).mpr hyt
  have hxle (u : X) : x u ≤ a := by
    have hu_mem : ({u} : Finset X) ∈ stableA := by simp [stableA]
    simpa using hsAmax {u} hu_mem
  have hyle (v : Y) : y v ≤ 1 - a := by
    have hv_indep : B.IsIndepSet (↑({v} : Finset Y) : Set Y) := by simp
    have hsumIndep := sumFinset_indep A B hsA hv_indep
    have hbound := hz.2 (sumFinset sA {v}) hsumIndep
    have hsplit : (∑ w ∈ sumFinset sA {v}, z w) =
        (∑ u ∈ sA, x u) + y v := by
      have hdisj : Disjoint
          (sA.map ⟨Sum.inl, Sum.inl_injective⟩)
          (({v} : Finset Y).map ⟨Sum.inr, Sum.inr_injective⟩) := by
        apply Finset.disjoint_left.mpr
        intro w hwL hwR
        simp only [Finset.mem_map] at hwL hwR
        rcases hwL with ⟨u, hu, rfl⟩
        simp at hwR
      unfold sumFinset
      rw [Finset.sum_union hdisj]
      simp [x, y]
    rw [hsplit] at hbound
    dsimp [a]
    linarith
  have hp : p ∈ stab Aᶜ := hA p hpcond
  have hq : q ∈ stab Bᶜ := hB q hqcond
  rw [compl_sum_eq_join, stab_join_eq_split_preimage]
  change (x, y) ∈ convexJoin ℝ (productAxisLeft '' stab Aᶜ)
    (productAxisRight '' stab Bᶜ)
  rw [mem_convexJoin]
  refine ⟨(p, 0), ⟨p, hp, rfl⟩, (0, q), ⟨q, hq, rfl⟩,
    a, 1 - a, ha0, sub_nonneg.mpr ha1, by ring, ?_⟩
  apply Prod.ext
  · funext u
    dsimp [p, x]
    split_ifs with ha
    · simp only [Pi.zero_apply, mul_zero, zero_add]
      exact le_antisymm (hz.1 (.inl u)) (by simpa [x, ha] using hxle u)
    · simp
      field_simp
  · funext v
    dsimp [q, y]
    split_ifs with hrema
    · have ha : a = 1 := by linarith
      simp only [Pi.zero_apply, mul_zero, add_zero]
      exact le_antisymm (hz.1 (.inr v)) (by simpa [y, ha] using hyle v)
    · simp
      field_simp


-- @@ L346-376 verbatim
/--
Cotree induction proves the stable-set antiblocker condition simultaneously
for a cotree evaluation and its complement.
-/
theorem cotree_hasStabAntiblocker_both :
    ∀ T : Cotree,
      HasStabAntiblocker (Cotree.eval T) ∧
        HasStabAntiblocker (Cotree.eval T)ᶜ := by
  intro T
  induction T with
  | leaf =>
      have hbot : HasStabAntiblocker (⊥ : SimpleGraph PUnit) :=
        hasStabAntiblocker_bot_of_subsingleton
      constructor
      · exact hbot
      · change HasStabAntiblocker (⊥ : SimpleGraph PUnit)ᶜ
        rw [show (⊥ : SimpleGraph PUnit)ᶜ = ⊥ by ext u v; simp]
        exact hbot
  | compl A ih =>
      constructor
      · exact ih.2
      · change HasStabAntiblocker ((Cotree.eval A)ᶜ)ᶜ
        rw [compl_compl]
        exact ih.1
  | sum A B ihA ihB =>
      constructor
      · exact hasStabAntiblocker_sum _ _ ihA.1 ihB.1
      · change HasStabAntiblocker (Cotree.eval A ⊕g Cotree.eval B)ᶜ
        rw [compl_sum_eq_join]
        exact hasStabAntiblocker_join
          (Cotree.eval A)ᶜ (Cotree.eval B)ᶜ ihA.2 ihB.2


-- @@ L378-411 verbatim
private theorem stab_compl_subset_antiblockerCondition
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {y : X → ℝ} (hy : y ∈ stab Gᶜ) :
    StabAntiblockerCondition G y := by
  classical
  constructor
  · intro v
    exact stab_coordinate_nonneg Gᶜ hy v
  · intro s hs
    change y ∈ {z : X → ℝ | ∑ v ∈ s, z v ≤ 1}
    apply (convexHull_min ?_ ?_) hy
    · rintro z ⟨t, ht, rfl⟩
      have hcard : (s ∩ t).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u hu v hv
        by_contra huv
        have hu' := Finset.mem_inter.mp hu
        have hv' := Finset.mem_inter.mp hv
        have hnadj := hs hu'.1 hv'.1 huv
        have hncadj := ht hu'.2 hv'.2 huv
        exact hncadj (by simpa [SimpleGraph.compl_adj, huv] using hnadj)
      change ∑ v ∈ s, indicator t v ≤ 1
      calc
        (∑ v ∈ s, indicator t v) = ((s ∩ t).card : ℝ) := by
          simp [indicator]
        _ ≤ 1 := by exact_mod_cast hcard
    · intro p hp q hq a b ha hb hab
      change ∑ v ∈ s, p v ≤ 1 at hp
      change ∑ v ∈ s, q v ≤ 1 at hq
      change ∑ v ∈ s, (a • p + b • q) v ≤ 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      nlinarith


-- @@ L413-421 verbatim
/--
An antiblocker realization upgrades the elementary stable-set inclusion to an
exact membership characterization.  This is the reusable dual interface for
subsequent cotree and deletion arguments.
-/
theorem mem_stab_compl_iff_antiblockerCondition_of_hasStabAntiblocker
    (G : SimpleGraph V) (hG : HasStabAntiblocker G) (y : V → ℝ) :
    y ∈ stab Gᶜ ↔ StabAntiblockerCondition G y :=
  ⟨stab_compl_subset_antiblockerCondition G, hG y⟩


-- @@ L423-449 verbatim
private theorem hasStabAntiblocker_iso
    {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H)
    (hG : HasStabAntiblocker G) : HasStabAntiblocker H := by
  classical
  intro y hy
  let x : X → ℝ := fun v => y (e v)
  have hxcond : StabAntiblockerCondition G x := by
    constructor
    · intro v
      exact hy.1 (e v)
    · intro s hs
      have hs' := isIndepSet_relabel e hs
      have h := hy.2 (relabelFinset e.toEquiv s) hs'
      simpa [x, relabelFinset] using h
  have hx := hG x hxcond
  let ec : Gᶜ ≃g Hᶜ :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by intro u v; simp [e.map_rel_iff] }
  have hy' := coordinateRelabel_mem_stab ec hx
  dsimp [ec] at hy'
  have heq : coordinateRelabel e.toEquiv x = y := by
    ext w
    change y (e.toEquiv (e.toEquiv.symm w)) = y w
    rw [e.toEquiv.apply_symm_apply]
  rwa [heq] at hy'


-- @@ L451-456 verbatim
/-- Every cograph satisfies the stable-set antiblocker condition. -/
theorem hasStabAntiblocker_of_cograph (G : SimpleGraph V)
    (hG : IsCograph G) : HasStabAntiblocker G := by
  rcases hG with ⟨T, ⟨e⟩⟩
  exact hasStabAntiblocker_iso e.symm
    (cotree_hasStabAntiblocker_both T).1


-- @@ L458-459 verbatim
private def dot {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ v, p v * q v


-- @@ L461-481 verbatim
private theorem dot_le_one_of_cond
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) {q p : X → ℝ} (hq : StabAntiblockerCondition G q) (hp : p ∈ stab G) :
    dot p q ≤ 1 := by
  classical
  change p ∈ {p : X → ℝ | dot p q ≤ 1}
  apply (convexHull_min ?_ ?_) hp
  · rintro z ⟨s, hs, rfl⟩
    change ∑ v, indicator s v * q v ≤ 1
    simpa [indicator] using hq.2 s hs
  · intro x hx y hy a b ha hb hab
    change dot x q ≤ 1 at hx
    change dot y q ≤ 1 at hy
    change dot (a • x + b • y) q ≤ 1
    have heq : dot (a • x + b • y) q = a * dot x q + b * dot y q := by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_mul, Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;> intro v _ <;> ring
    rw [heq]
    nlinarith


-- @@ L483-487 verbatim
private theorem dot_nonneg_of_nonneg
    {X : Type*} [Fintype X] {p q : X → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v) : 0 ≤ dot p q := by
  unfold dot
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hp v) (hq v)


-- @@ L489-491 verbatim
private def polarPoint {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) (y : ℝ × (X → ℝ)) : Prop :=
  ∀ x ∈ hansen G, x.1 * y.1 + dot x.2 y.2 ≤ 1


-- @@ L493-568 verbatim
private theorem hansenPolar_forward {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X)
    (hanti : ∀ y, y ∈ stab Gᶜ ↔ StabAntiblockerCondition G y)
    (s : ℝ) (w : X → ℝ)
    (hh : (s, fun v => -w v / 2) ∈ hansen Gᶜ) :
    polarPoint G (s, w) := by
  intro ξ hξ
  rw [mem_hansen_iff] at hh hξ
  let a : ℝ := (s + 1) / 2
  let b : ℝ := (ξ.1 + 1) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [hh.1.1]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [hh.1.2]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith [hξ.1.1]
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hξ.1.2]
  unfold sectionSet at hh hξ
  rcases hh.2 with ⟨_, ⟨q, hq, rfl⟩, _, ⟨r, hr, rfl⟩, hzw⟩
  rcases hξ.2 with ⟨_, ⟨p, hp, rfl⟩, _, ⟨t, ht, rfl⟩, hzx⟩
  have hqcond := (hanti q).mp hq
  have hrcond := (hanti r).mp hr
  have hp0 : ∀ v, 0 ≤ p v := fun v => stab_coordinate_nonneg G hp v
  have ht0 : ∀ v, 0 ≤ t v := fun v => stab_coordinate_nonneg G ht v
  have hpq0 := dot_nonneg_of_nonneg hp0 hqcond.1
  have hpr0 := dot_nonneg_of_nonneg hp0 hrcond.1
  have htq0 := dot_nonneg_of_nonneg ht0 hqcond.1
  have htr0 := dot_nonneg_of_nonneg ht0 hrcond.1
  have hpq1 := dot_le_one_of_cond G hqcond hp
  have hpr1 := dot_le_one_of_cond G hrcond hp
  have htq1 := dot_le_one_of_cond G hqcond ht
  have htr1 := dot_le_one_of_cond G hrcond ht
  have hs : s = 2 * a - 1 := by dsimp [a]; ring
  have hξs : ξ.1 = 2 * b - 1 := by dsimp [b]; ring
  have hw : w = fun v => -2 * (a * q v - (1 - a) * r v) := by
    funext v
    have hv := congrFun hzw v
    change ((s + 1) / 2) * q v + (-(1 - (s + 1) / 2)) * r v = -w v / 2 at hv
    dsimp [a]
    linarith
  have hξw : ξ.2 = fun v => b * p v - (1 - b) * t v := by
    funext v
    have hv := congrFun hzx v
    change ((ξ.1 + 1) / 2) * p v + (-(1 - (ξ.1 + 1) / 2)) * t v = ξ.2 v at hv
    dsimp [b]
    linarith
  rw [hs, hξs, hw, hξw]
  simp only [dot]
  have hsum :
      (∑ v, (b * p v - (1 - b) * t v) *
        (-2 * (a * q v - (1 - a) * r v))) =
      -2 * (b * a * dot p q - b * (1 - a) * dot p r -
        (1 - b) * a * dot t q + (1 - b) * (1 - a) * dot t r) := by
    calc
      _ = ∑ v, -2 * (b * a * (p v * q v) -
          b * (1 - a) * (p v * r v) -
          (1 - b) * a * (t v * q v) +
          (1 - b) * (1 - a) * (t v * r v)) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        unfold dot
        have hin :
            (∑ v, (b * a * (p v * q v) - b * (1 - a) * (p v * r v) -
              (1 - b) * a * (t v * q v) +
              (1 - b) * (1 - a) * (t v * r v))) =
            b * a * (∑ v, p v * q v) - b * (1 - a) * (∑ v, p v * r v) -
              (1 - b) * a * (∑ v, t v * q v) +
              (1 - b) * (1 - a) * (∑ v, t v * r v) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib]
          simp only [← Finset.mul_sum]
        rw [← hin, Finset.mul_sum]
  rw [hsum]
  nlinarith [mul_nonneg (mul_nonneg hb0 ha0) hpq0,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr ha1)) htr0,
    mul_nonneg (mul_nonneg hb0 (sub_nonneg.mpr ha1)) (sub_nonneg.mpr hpr1),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hb1) ha0) (sub_nonneg.mpr htq1)]


-- @@ L570-720 verbatim
private theorem hansenPolar_reverse {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X)
    (hanti : ∀ y, y ∈ stab Gᶜ ↔ StabAntiblockerCondition G y)
    (s : ℝ) (w : X → ℝ)
    (hpol : polarPoint G (s, w)) :
    (s, fun v => -w v / 2) ∈ hansen Gᶜ := by
  classical
  have htop (p : X → ℝ) (hp : p ∈ stab G) : (1, p) ∈ hansen G := by
    apply subset_convexHull ℝ
    exact Or.inl ⟨p, hp, rfl⟩
  have hbottom (p : X → ℝ) (hp : p ∈ stab G) : (-1, -p) ∈ hansen G := by
    apply subset_convexHull ℝ
    exact Or.inr ⟨p, hp, rfl⟩
  have hs1 : s ≤ 1 := by
    have h := hpol (1, 0) (htop 0 (zero_mem_stab G))
    simpa [polarPoint, dot] using h
  have hsm1 : -1 ≤ s := by
    have hm : (-1, (0 : X → ℝ)) ∈ hansen G := by
      simpa using hbottom 0 (zero_mem_stab G)
    have h := hpol (-1, 0) hm
    norm_num [dot] at h
    linarith
  let a : ℝ := (s + 1) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hnegBound (t : Finset X) (ht : G.IsIndepSet (↑t : Set X)) :
      ∑ v ∈ t, max (-w v) 0 ≤ 2 * a := by
    let tn : Finset X := t.filter fun v => w v < 0
    have htn : G.IsIndepSet (↑tn : Set X) := by
      intro u hu v hv huv
      exact ht (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 huv
    have h := hpol (-1, -indicator tn) (hbottom (indicator tn)
      (indicator_mem_stab G htn))
    have hdot : dot (-indicator tn) w = ∑ v ∈ tn, -w v := by
      simp [dot, indicator]
    have hsum : (∑ v ∈ t, max (-w v) 0) = ∑ v ∈ tn, -w v := by
      calc
        (∑ v ∈ t, max (-w v) 0) =
            ∑ v ∈ t, if w v < 0 then -w v else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hvw : w v < 0
          · simp [hvw, le_of_lt (neg_pos.mpr hvw)]
          · have hvw0 : 0 ≤ w v := le_of_not_gt hvw
            simp [hvw, hvw0]
        _ = ∑ v ∈ tn, -w v := by rw [Finset.sum_filter]
    change (-1) * s + dot (-indicator tn) w ≤ 1 at h
    rw [hdot] at h
    rw [hsum]
    dsimp [a]
    linarith
  have hposBound (t : Finset X) (ht : G.IsIndepSet (↑t : Set X)) :
      ∑ v ∈ t, max (w v) 0 ≤ 2 * (1 - a) := by
    let tp : Finset X := t.filter fun v => 0 < w v
    have htp : G.IsIndepSet (↑tp : Set X) := by
      intro u hu v hv huv
      exact ht (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 huv
    have h := hpol (1, indicator tp) (htop (indicator tp)
      (indicator_mem_stab G htp))
    have hdot : dot (indicator tp) w = ∑ v ∈ tp, w v := by
      simp [dot, indicator]
    have hsum : (∑ v ∈ t, max (w v) 0) = ∑ v ∈ tp, w v := by
      calc
        (∑ v ∈ t, max (w v) 0) =
            ∑ v ∈ t, if 0 < w v then w v else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hvw : 0 < w v
          · simp [hvw, hvw.le]
          · have hvw0 : w v ≤ 0 := le_of_not_gt hvw
            simp [hvw, hvw0]
        _ = ∑ v ∈ tp, w v := by rw [Finset.sum_filter]
    change 1 * s + dot (indicator tp) w ≤ 1 at h
    rw [hdot] at h
    rw [hsum]
    dsimp [a]
    linarith
  let q : X → ℝ := if a = 0 then 0 else fun v => max (-w v) 0 / (2 * a)
  let r : X → ℝ := if 1 - a = 0 then 0 else fun v => max (w v) 0 / (2 * (1 - a))
  have hqcond : StabAntiblockerCondition G q := by
    constructor
    · intro v
      dsimp [q]
      split_ifs
      · simp
      · positivity
    · intro t ht
      dsimp [q]
      split_ifs with ha
      · simp
      · change (∑ v ∈ t, max (-w v) 0 / (2 * a)) ≤ 1
        rw [← Finset.sum_div]
        apply (div_le_one (by positivity)).mpr
        exact hnegBound t ht
  have hrcond : StabAntiblockerCondition G r := by
    constructor
    · intro v
      dsimp [r]
      split_ifs
      · simp
      · positivity
    · intro t ht
      dsimp [r]
      split_ifs with hra
      · simp
      · change (∑ v ∈ t, max (w v) 0 / (2 * (1 - a))) ≤ 1
        rw [← Finset.sum_div]
        apply (div_le_one (by positivity)).mpr
        exact hposBound t ht
  have hq : q ∈ stab Gᶜ := (hanti q).mpr hqcond
  have hr : r ∈ stab Gᶜ := (hanti r).mpr hrcond
  rw [mem_hansen_iff]
  constructor
  · exact ⟨hsm1, hs1⟩
  · unfold sectionSet
    refine ⟨a • q, ⟨q, hq, rfl⟩, (-(1 - a)) • r,
      ⟨r, hr, rfl⟩, ?_⟩
    funext v
    have hnegv := hnegBound {v} (by simp)
    have hposv := hposBound {v} (by simp)
    simp only [Finset.sum_singleton] at hnegv hposv
    have hmax : max (-w v) 0 - max (w v) 0 = -w v := by
      by_cases hw0 : 0 ≤ w v
      · rw [max_eq_left hw0, max_eq_right (neg_nonpos.mpr hw0)]
        simp
      · have hw0' : w v ≤ 0 := le_of_not_ge hw0
        rw [max_eq_right hw0', max_eq_left (neg_nonneg.mpr hw0')]
        simp
    dsimp [q, r]
    have haq : a * (if a = 0 then 0 else max (-w v) 0 / (2 * a)) =
        max (-w v) 0 / 2 := by
      split_ifs with hza
      · have hn : max (-w v) 0 = 0 :=
          le_antisymm (by nlinarith) (le_max_right _ _)
        simp [hn]
      · field_simp
    have hbr : (1 - a) *
          (if 1 - a = 0 then 0 else max (w v) 0 / (2 * (1 - a))) =
        max (w v) 0 / 2 := by
      split_ifs with hzra
      · have hpv : max (w v) 0 = 0 :=
          le_antisymm (by nlinarith) (le_max_right _ _)
        simp [hpv]
      · field_simp
    simp only [ite_apply, Pi.zero_apply]
    have hbrneg : -(1 - a) *
          (if 1 - a = 0 then 0 else max (w v) 0 / (2 * (1 - a))) =
        -(max (w v) 0 / 2) := by
      rw [neg_mul, hbr]
    rw [haq, hbrneg]
    linarith


-- @@ L722-725 verbatim
/-- The linear map identifying the Hansen polar with the complementary Hansen body. -/
def hansenPolarMap :
    (ℝ × (V → ℝ)) →ₗ[ℝ] (ℝ × (V → ℝ)) :=
  LinearMap.prodMap LinearMap.id ((-2 : ℝ) • LinearMap.id)


-- @@ L727-755 verbatim
/--
The polar of a Hansen body is the image of the complementary Hansen body
whenever the stable-set antiblocker condition holds.
-/
theorem hansen_polar_eq_image_of_hasStabAntiblocker
    (G : SimpleGraph V) (hanti : HasStabAntiblocker G) :
    {y : ℝ × (V → ℝ) | ∀ x ∈ hansen G,
        x.1 * y.1 + dot x.2 y.2 ≤ 1} =
      hansenPolarMap '' hansen Gᶜ := by
  let hiff :=
    mem_stab_compl_iff_antiblockerCondition_of_hasStabAntiblocker G hanti
  ext y
  constructor
  · intro hy
    let z : ℝ × (V → ℝ) := (y.1, fun v => -y.2 v / 2)
    have hz : z ∈ hansen Gᶜ := hansenPolar_reverse G hiff y.1 y.2 hy
    refine ⟨z, hz, ?_⟩
    apply Prod.ext
    · rfl
    · funext v
      dsimp [z, hansenPolarMap]
      ring
  · rintro ⟨z, hz, rfl⟩
    apply hansenPolar_forward G hiff z.1 (fun v => -2 * z.2 v)
    convert hz using 1
    apply Prod.ext
    · rfl
    · funext v
      ring


-- @@ L757-768 verbatim
private theorem hansen_volume_ne_top (G : SimpleGraph V) :
    volume (hansen G) ≠ ⊤ := by
  have hsub : hansen G ⊆
      Set.Icc ((-1 : ℝ), fun _ : V => -1) (1, fun _ => 1) := by
    rintro ⟨r, z⟩ hz
    rw [mem_hansen_iff] at hz
    have hx0 : 0 ≤ (r + 1) / 2 := by linarith [hz.1.1]
    have hx1 : (r + 1) / 2 ≤ 1 := by linarith [hz.1.2]
    exact ⟨⟨hz.1.1, sectionSet_subset_centeredCube G hx0 hx1 hz.2 |>.1⟩,
      ⟨hz.1.2, sectionSet_subset_centeredCube G hx0 hx1 hz.2 |>.2⟩⟩
  exact ne_of_lt <| lt_of_le_of_lt (measure_mono hsub)
    isCompact_Icc.measure_lt_top


-- @@ L770-792 verbatim
/--
The polar volume of a Hansen body under the stable-set antiblocker condition.
This is the measure-theoretic half of the Hansen graph-ratio bridge.
-/
theorem polar_volume_toReal_of_hasStabAntiblocker
    (G : SimpleGraph V) (hanti : HasStabAntiblocker G) :
    (volume {y : ℝ × (V → ℝ) | ∀ x ∈ hansen G,
        x.1 * y.1 + ∑ v : V, x.2 v * y.2 v ≤ 1}).toReal =
      (2 : ℝ) ^ Fintype.card V * (volume (hansen Gᶜ)).toReal := by
  change (volume {y : ℝ × (V → ℝ) | polarPoint G y}).toReal = _
  unfold polarPoint
  rw [hansen_polar_eq_image_of_hasStabAntiblocker G hanti]
  rw [Measure.volume_eq_prod ℝ (V → ℝ)]
  rw [Measure.addHaar_image_linearMap
    ((volume : Measure ℝ).prod (volume : Measure (V → ℝ)))
      (hansenPolarMap (V := V))]
  have hdet : LinearMap.det (hansenPolarMap (V := V)) =
      (-2 : ℝ) ^ Fintype.card V := by
    rw [hansenPolarMap, LinearMap.det_prodMap, LinearMap.det_smul]
    simp
  rw [hdet, abs_pow, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
  rw [ENNReal.toReal_mul]
  · simp




-- @@ L796-804 verbatim
/-- The normalized Mahler ratio in dimension `|V| + 1`. -/
noncomputable def mahlerRho
    (K : Set (ℝ × (V → ℝ))) : ℝ :=
  let n := Fintype.card V + 1
  let polarK : Set (ℝ × (V → ℝ)) :=
    {y | ∀ x ∈ K,
      x.1 * y.1 + ∑ v : V, x.2 v * y.2 v ≤ 1}
  (n.factorial : ℝ) * (volume K).toReal * (volume polarK).toReal /
    (4 : ℝ) ^ n


-- @@ L806-880 verbatim
/--
Cavalieri/Fubini section formula:

    vol_{m+1} H(G) = 2 ∫_0^1 q_G(x) dx.
-/
theorem volume_hansen_spec (G : SimpleGraph V) :
    (volume (hansen G)).toReal
      = 2 * ∫ x in (0 : ℝ)..1, q G x := by
  have hnull : NullMeasurableSet (hansen G)
      ((volume : Measure ℝ).prod (volume : Measure (V → ℝ))) := by
    exact (convex_hansen G).nullMeasurableSet
      ((volume : Measure ℝ).prod (volume : Measure (V → ℝ)))
  have hvolume :
      volume (hansen G) =
        ∫⁻ r : ℝ in Set.Icc (-1 : ℝ) 1,
          ENNReal.ofReal (q G ((r + 1) / 2)) := by
    rw [Measure.volume_eq_prod ℝ (V → ℝ)]
    rw [Measure.prod_apply_nullMeasurableSet
      (volume : Measure ℝ) (volume : Measure (V → ℝ)) hnull]
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro r
    rw [Set.indicator]
    by_cases hr : r ∈ Set.Icc (-1 : ℝ) 1
    · simp only [hr, ↓reduceIte]
      have hx0 : 0 ≤ (r + 1) / 2 := by linarith [hr.1]
      have hx1 : (r + 1) / 2 ≤ 1 := by linarith [hr.2]
      have hsec : {z : V → ℝ | (r, z) ∈ hansen G} =
          sectionSet G ((r + 1) / 2) := by
        ext z
        simp [mem_hansen_iff, hr]
      rw [hsec, q_eq_section_volume G hx0 hx1]
      exact (ENNReal.ofReal_toReal
        (sectionSet_volume_ne_top G hx0 hx1)).symm
    · simp only [hr, ↓reduceIte]
      have hsec : {z : V → ℝ | (r, z) ∈ hansen G} = ∅ := by
        ext z
        simp [mem_hansen_iff, hr]
      simp [hsec]
  let f : ℝ → ℝ := fun r => q G ((r + 1) / 2)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_q G).comp (by fun_prop)
  have hfint : Integrable f (volume.restrict (Set.Icc (-1 : ℝ) 1)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hfcont.continuousOn
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    change 0 ≤ q G ((r + 1) / 2)
    exact q_nonneg_on_unit G (by linarith [hr.1]) (by linarith [hr.2])
  have hrealIntegral :
      ENNReal.ofReal (∫ r in Set.Icc (-1 : ℝ) 1, f r) =
        ∫⁻ r in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (f r) :=
    ofReal_integral_eq_lintegral_ofReal hfint hfnn
  have hinterval :
      (∫ r in Set.Icc (-1 : ℝ) 1, f r) =
        2 * ∫ x in (0 : ℝ)..1, q G x := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hcongr :
        (∫ r in (-1 : ℝ)..1, f r) =
          ∫ r in (-1 : ℝ)..1, q G ((1 / 2 : ℝ) + r / 2) := by
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [f]
      congr 1
      ring
    rw [hcongr]
    rw [intervalIntegral.integral_comp_add_div (f := q G)
      (c := (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 0) (d := (1 / 2 : ℝ))]
    norm_num
  rw [hvolume]
  rw [← hrealIntegral]
  rw [ENNReal.toReal_ofReal]
  · exact hinterval
  · exact integral_nonneg_of_ae hfnn


-- @@ L882-891 verbatim
/--
Equivalent normalized volume statement:

    N(G) = (m+1)! vol(H(G)).
-/
theorem N_eq_factorial_mul_volume_hansen_spec (G : SimpleGraph V) :
    N G = ((Fintype.card V + 1).factorial : ℝ) *
      (volume (hansen G)).toReal := by
  rw [volume_hansen_spec, N_eq_two_factorial_mul_integral_q]
  ring


-- @@ L893-919 verbatim
/--
Hansen polarity identifies the geometric and graph-side ratios whenever the
stable-set antiblocker condition holds.
-/
theorem mahlerRho_hansen_eq_graphRho_of_hasStabAntiblocker
    (G : SimpleGraph V) (hanti : HasStabAntiblocker G) :
    mahlerRho (hansen G) = graphRho G := by
  have hvol := N_eq_factorial_mul_volume_hansen_spec G
  have hvolc := N_eq_factorial_mul_volume_hansen_spec Gᶜ
  have hpolar := polar_volume_toReal_of_hasStabAntiblocker G hanti
  have hv : (volume (hansen G)).toReal =
      N G / ((Fintype.card V + 1).factorial : ℝ) := by
    rw [hvol]
    field_simp
  have hvc : (volume (hansen Gᶜ)).toReal =
      N Gᶜ / ((Fintype.card V + 1).factorial : ℝ) := by
    rw [hvolc]
    field_simp
  have hpow : (4 : ℝ) ^ (Fintype.card V + 1) =
      (2 : ℝ) ^ Fintype.card V * 2 ^ (Fintype.card V + 2) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    simp only [pow_add]
    ring
  unfold mahlerRho graphRho
  dsimp
  rw [hpolar, hv, hvc, hpow]
  field_simp


-- @@ L921-927 verbatim
/-- Hansen polarity identifies the geometric and graph-side ratios for cographs. -/
theorem mahlerRho_hansen_eq_graphRho_of_cograph
    (G : SimpleGraph V)
    (hG : IsCograph G) :
    mahlerRho (hansen G) = graphRho G := by
  exact mahlerRho_hansen_eq_graphRho_of_hasStabAntiblocker G
    (hasStabAntiblocker_of_cograph G hG)


-- @@ L929-929 verbatim
end HansenPolytope


-- @@ L931-933 verbatim
/-!
## Final geometric cograph theorem
-/


-- @@ L935-935 verbatim
section FinalTheorem


-- @@ L937-937 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L939-947 verbatim
/--
Sharp Mahler inequality for Hansen polytopes of cographs.
-/
theorem hansen_cograph_mahler'
    (G : SimpleGraph V)
    (hG : IsCograph G) :
    1 ≤ mahlerRho (hansen G) := by
  rw [mahlerRho_hansen_eq_graphRho_of_cograph G hG]
  exact cograph_graphRho_ge_one G hG


-- @@ L949-957 verbatim
/--
Equality characterization in cotree-threshold language.
-/
theorem hansen_cograph_mahler_eq_one_iff_threshold'
    (G : SimpleGraph V)
    (hG : IsCograph G) :
    mahlerRho (hansen G) = 1 ↔ IsThresholdGraph G := by
  rw [mahlerRho_hansen_eq_graphRho_of_cograph G hG]
  exact cograph_graphRho_eq_one_iff_threshold G hG


-- @@ L959-968 verbatim
/--
Equality characterization in the standard isolated/dominating-vertex
threshold language.
-/
theorem hansen_cograph_mahler_eq_one_iff_thresholdStandard
    (G : SimpleGraph V)
    (hG : IsCograph G) :
    mahlerRho (hansen G) = 1 ↔ IsThresholdStandard G := by
  rw [hansen_cograph_mahler_eq_one_iff_threshold' G hG]
  exact threshold_cotree_iff_standard G


-- @@ L970-970 verbatim
end FinalTheorem


-- @@ L972-983 verbatim
/-!
## Exact benchmark: K2 and 2K2 give 81/80

This is not needed for the theorem, but it is a useful regression test for
all normalizations:

    q_K2(x) = 1/2 + x(1-x)
    ∫q_K2 = 2/3
    ∫q_K2^2 = 9/20
    rho(H(2K2)) = 81/80.

-/


-- @@ L985-985 verbatim
section Benchmark


-- @@ L987-989 verbatim
/-- A concrete two-vertex edge graph. -/
abbrev K2 : SimpleGraph (Fin 2) :=
  completeGraph (Fin 2)


-- @@ L991-1082 expanded
theorem q_K2_formula (x : ℝ) : q K2 x = 1 / 2 + x * (1 - x) := by
  classical
  let f : Fin 2 ≃ (PUnit.{1} ⊕ PUnit.{1}) := finTwoEquiv.trans Equiv.boolEquivPUnitSumPUnit
  have hjoin :
    (graphJoin (⊥ : SimpleGraph PUnit.{1}) (⊥ : SimpleGraph PUnit.{1})) =
      completeGraph (PUnit.{1} ⊕ PUnit.{1}) :=
    by
    ext a b
    cases a <;> cases b
    · rw [graphJoin_adj_inl_inl]
      simp
    · constructor
      · intro h
        simp
      · intro h
        exact graphJoin_adj_inl_inr _ _ _ _
    · constructor
      · intro h
        simp
      · intro h
        exact (graphJoin_adj_inl_inr _ _ _ _).symm
    · rw [graphJoin_adj_inr_inr]
      simp
  have e : K2 ≃g (graphJoin (⊥ : SimpleGraph PUnit.{1}) (⊥ : SimpleGraph PUnit.{1})) :=
    by
    rw [hjoin]
    exact SimpleGraph.Iso.completeGraph f
  have hnuK2 : nu K2 = 1 := by
    rw [nu_iso e, nu_join, nu_bot]
    norm_num
  have hnu (s : Finset (Fin 2)) : nuInduced K2 s = 1 :=
    by
    have hsle : s.card ≤ 2 := by simpa using Finset.card_le_univ s
    have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have hs : s = ∅ := Finset.card_eq_zero.mp hzero
      subst s
      unfold nuInduced inducedFinset
      have hg : SimpleGraph.induce (↑(∅ : Finset (Fin 2)) : Set (Fin 2)) K2 = ⊥ :=
        by
        ext u v
        have hu : False := by simpa using u.property
        exact hu.elim
      rw [hg, nu_bot]
      simp
    · unfold nuInduced inducedFinset
      have hg : SimpleGraph.induce (↑s : Set (Fin 2)) K2 = ⊥ :=
        by
        ext u v
        have huv : u = v := by
          apply Subtype.ext
          by_contra huv
          have htwo_mem : ({ u.1, v.1 } : Finset (Fin 2)) ⊆ s :=
            by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact u.property
            · exact v.property
          have hcard_two : ({ u.1, v.1 } : Finset (Fin 2)).card = 2 := by simp [huv]
          have := Finset.card_le_card htwo_mem
          omega
        subst v
        simp
      rw [hg, nu_bot, Set.fintypeCard_eq_ncard, Set.ncard_coe_finset, hone]
      norm_num
    · have hs : s = Finset.univ :=
        by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
        simp [htwo]
      subst s
      unfold nuInduced inducedFinset
      have eu : SimpleGraph.induce (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) K2 ≃g K2 :=
        by
        have hset : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)) = Set.univ :=
          by
          ext v
          simp
        rw [hset]
        exact SimpleGraph.induceUnivIso K2
      rw [nu_iso eu, hnuK2]
  unfold q qCoeff
  simp_rw [hnu, one_mul]
  simp only [Fintype.card_fin]
  let term : ℕ → ℝ := fun k =>
    1 / ((k.factorial : ℝ) * ((2 - k).factorial : ℝ)) * x ^ k * (1 - x) ^ (2 - k)
  change (∑ s ∈ Finset.univ.powerset, term s.card) = _
  rw [Finset.sum_powerset_apply_card]
  norm_num [term, Finset.sum_range_succ]
  ring


-- @@ L1084-1097 verbatim
theorem integral_q_K2 :
    (∫ x in (0 : ℝ)..1, q K2 x) = 2 / 3 := by
  rw [show (fun x => q K2 x) =
      (fun x : ℝ => 1 / 2 + x * (1 - x)) by
        funext x
        exact q_K2_formula x]
  rw [intervalIntegral.integral_add]
  · rw [show (fun x : ℝ => x * (1 - x)) =
        (fun x => x ^ 1 * (1 - x) ^ 1) by funext x; ring]
    rw [integral_pow_mul_one_sub_pow]
    norm_num
  · exact continuous_const.intervalIntegrable (μ := volume) 0 1
  · exact (by fun_prop : Continuous
      (fun x : ℝ => x * (1 - x))).intervalIntegrable (μ := volume) 0 1


-- @@ L1099-1119 verbatim
theorem integral_q_K2_sq :
    (∫ x in (0 : ℝ)..1, q K2 x * q K2 x) = 9 / 20 := by
  have hfun : (fun x : ℝ => q K2 x * q K2 x) =
      (fun x => 1 / 4 + x * (1 - x) + x ^ 2 * (1 - x) ^ 2) := by
    funext x
    rw [q_K2_formula]
    ring
  rw [hfun, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_add]
    · rw [show (fun x : ℝ => x * (1 - x)) =
          (fun x => x ^ 1 * (1 - x) ^ 1) by funext x; ring]
      rw [integral_pow_mul_one_sub_pow 1 1,
        integral_pow_mul_one_sub_pow 2 2]
      norm_num
    · exact continuous_const.intervalIntegrable (μ := volume) 0 1
    · exact (by fun_prop : Continuous
        (fun x : ℝ => x * (1 - x))).intervalIntegrable (μ := volume) 0 1
  · exact (by fun_prop : Continuous
      (fun x : ℝ => 1 / 4 + x * (1 - x))).intervalIntegrable (μ := volume) 0 1
  · exact (by fun_prop : Continuous
      (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)).intervalIntegrable (μ := volume) 0 1


-- @@ L1121-1151 verbatim
theorem graphRho_twoK2 :
    graphRho (K2 ⊕g K2) = 81 / 80 := by
  have hbot :
      ((⊥ : SimpleGraph PUnit) ⊕g (⊥ : SimpleGraph PUnit)) =
        (⊥ : SimpleGraph (PUnit ⊕ PUnit)) := by
    apply bot_unique
    intro x y h
    cases x <;> cases y <;> simp [SimpleGraph.sum_adj] at h
  let f : Fin 2 ≃ (PUnit ⊕ PUnit) :=
    Fintype.equivOfCardEq (by simp)
  have e : K2 ≃g
      (((⊥ : SimpleGraph PUnit) ⊕g (⊥ : SimpleGraph PUnit))ᶜ) := by
    rw [hbot]
    simpa [K2, SimpleGraph.completeGraph_eq_top] using
      (SimpleGraph.Iso.completeGraph f)
  have eleaf : (⊥ : SimpleGraph PUnit) ≃g Cotree.eval .leaf :=
    SimpleGraph.Iso.refl
  have hleaf : graphRho (⊥ : SimpleGraph PUnit) = 1 := by
    rw [graphRho_iso eleaf]
    exact Cotree.graphRho_leaf
  have hsum :
      graphRho ((⊥ : SimpleGraph PUnit) ⊕g (⊥ : SimpleGraph PUnit)) = 1 := by
    rw [(graphRho_sum_eq_mul_iff
      (⊥ : SimpleGraph PUnit) (⊥ : SimpleGraph PUnit)).mpr
      (Or.inl rfl), hleaf]
    norm_num
  have hK2 : graphRho K2 = 1 := by
    rw [graphRho_iso e, graphRho_compl]
    exact hsum
  rw [graphRho_sum_eq, hK2, integral_q_K2, integral_q_K2_sq]
  norm_num


-- @@ L1153-1153 verbatim
end Benchmark


-- @@ L1155-1155 verbatim
end HansenCograph
