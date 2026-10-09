import OAI.Geometry.PinnedDistances.ArithmeticVariance


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5 u6 u7 u8 u9


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open NumberField

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open scoped Topology ENNReal

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
open MeasureTheory NumberField

-- @@ L19-19 verbatim
open scoped BigOperators

-- @@ L20-20 verbatim
noncomputable section

-- @@ L21-21 verbatim
open scoped BigOperators

-- @@ L22-22 verbatim
open MeasureTheory


-- @@ L24-24 verbatim
namespace WeakPinned.Hierarchy.Depth

-- @@ L25-25 verbatim
open MeasureTheory

-- @@ L26-26 verbatim
variable {P : Type u1} [Fintype P] [DecidableEq P]

-- @@ L27-27 verbatim
variable (d : Depth P)


-- @@ L29-29 verbatim
def sourceGiant (x : P) (r : ℝ) : Prop := Fintype.card P < 2*(d.cell r x).card

-- @@ L30-30 verbatim
instance (x : P) (r : ℝ) : Decidable (d.sourceGiant x r) := Classical.propDecidable _


-- @@ L32-38 verbatim
omit [DecidableEq P] in
lemma sourceGiant_mono (x : P) {r t : ℝ} (htr : t ≤ r) (hr : d.sourceGiant x r) :
    d.sourceGiant x t := by
  classical
  have hc := Finset.card_le_card (d.cell_mono htr x)
  unfold sourceGiant at *
  omega


-- @@ L40-50 verbatim
omit [DecidableEq P] in
lemma sourceGiant_iff (x : P) (r : ℝ) : d.sourceGiant x r ↔
    ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  classical
  constructor
  · intro h; exact ⟨d.cell r x,h,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨C,hc,hC⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hC y hy)
    have := Finset.card_le_card hsub
    unfold sourceGiant
    omega


-- @@ L52-68 verbatim
lemma isClosed_sourceGiant (x : P) : IsClosed {r : ℝ | d.sourceGiant x r} := by
  classical
  simp_rw [d.sourceGiant_iff, Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x = y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const


-- @@ L70-70 verbatim
def sourceM (x : P) : ℝ := sSup {r : ℝ | d.sourceGiant x r}


-- @@ L72-87 verbatim
lemma sourceGiant_cutoff (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    d.sourceGiant x r ↔ r ≤ d.sourceM x := by
  classical
  have hlo : d.sourceGiant x (-d.radius) := by
    classical
    unfold sourceGiant
    rw [d.cell_of_low le_rfl,Finset.card_univ]
    omega
  have hle : ∀ t, d.sourceGiant x t → t ≤ d.radius := by
    classical
    intro t ht
    exact d.giants_le_radius hn ⟨d.cell t x, (d.mem_giants t _).mpr ⟨d.cell_mem_cells t x,ht⟩⟩
  have hne : Set.Nonempty {t : ℝ | d.sourceGiant x t} := ⟨-d.radius,hlo⟩
  have hbd : BddAbove {t : ℝ | d.sourceGiant x t} := ⟨d.radius, fun t ht => hle t ht⟩
  have hmem : d.sourceGiant x (d.sourceM x) := (d.isClosed_sourceGiant x).csSup_mem hne hbd
  exact ⟨fun hr => le_csSup hbd hr, fun hr => d.sourceGiant_mono x hr hmem⟩


-- @@ L89-93 verbatim
lemma sourceM_le_M (hn : 2 ≤ Fintype.card P) (x : P) : d.sourceM x ≤ d.M := by
  classical
  apply (d.giants_cutoff hn _).mp
  exact ⟨d.cell (d.sourceM x) x, (d.mem_giants _ _).mpr
    ⟨d.cell_mem_cells _ x,(d.sourceGiant_cutoff hn x _).mpr le_rfl⟩⟩


-- @@ L95-105 verbatim
lemma sourceGiant_mem_giant (x : P) (r : ℝ) :
    d.sourceGiant x r ↔ (d.giants r).Nonempty ∧ x ∈ d.giant r := by
  classical
  constructor
  · intro hs
    have hc : d.cell r x ∈ d.giants r := (d.mem_giants r _).mpr ⟨d.cell_mem_cells r x,hs⟩
    exact ⟨⟨_,hc⟩,by rw [d.giant_eq hc]; exact d.self_mem_cell r x⟩
  · rintro ⟨⟨G,hG⟩,hx⟩
    rw [d.giant_eq hG] at hx
    obtain ⟨hGc,hGm⟩ := (d.mem_giants r G).mp hG
    rwa [d.cell_of_mem hGc hx] at hGm


-- @@ L107-115 verbatim
lemma outsideIndicator_source (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    d.outsideIndicator r x = if d.sourceM x < r ∧ r ≤ d.M then 1 else 0 := by
  classical
  have he : ((d.giants r).Nonempty ∧ x ∉ d.giant r) ↔ d.sourceM x < r ∧ r ≤ d.M := by
    classical
    rw [← not_le, ← d.sourceGiant_cutoff hn x r, d.sourceGiant_mem_giant,
      ← d.giants_cutoff hn r]
    tauto
  simp only [outsideIndicator,he]


-- @@ L117-127 verbatim
lemma potential_source (hn : 2 ≤ Fintype.card P) (x : P) :
    d.potential x = d.M - d.sourceM x := by
  classical
  have he : (fun r => d.outsideIndicator r x) =
      (Set.Ioc (d.sourceM x) d.M).indicator (fun _ : ℝ => (1:ℝ)) := by
    classical
    funext r
    simp only [d.outsideIndicator_source hn, Set.indicator_apply, Set.mem_Ioc]
  rw [potential,he,integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (d.sourceM_le_M hn x), intervalIntegral.integral_const]
  simp


-- @@ L129-145 verbatim
/-- The level set is an interval of length 2H, regardless of the fiber center-level h. -/

lemma straddle_integral (hn : 2 ≤ Fintype.card P) (x : P) (h H : ℝ) (hH : 0 ≤ H) :
    (∫ r : ℝ, if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then (1:ℝ) else 0) = 2*H := by
  classical
  have he : (fun r : ℝ => if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then (1:ℝ) else 0) =
      (Set.Ico (h-H-d.sourceM x) (h+H-d.sourceM x)).indicator (fun _ => (1:ℝ)) := by
    classical
    funext r
    simp only [d.sourceGiant_cutoff hn, not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he,integral_indicator measurableSet_Ico]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : h-H-d.sourceM x ≤ h+H-d.sourceM x), intervalIntegral.integral_const]
  simp
  ring


-- @@ L147-149 verbatim
def smallCells (y : P) (T : ℝ) : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun C => ∃ r : ℝ, C = d.cell r y ∧ (C.card : ℝ) < T)


-- @@ L151-151 verbatim
def smallNeighbors (y : P) (T : ℝ) : Finset P := (d.smallCells y T).biUnion id


-- @@ L153-161 verbatim
omit [DecidableEq P] in
lemma smallCells_chain (y : P) (T : ℝ) {C E : Finset P}
    (hC : C ∈ d.smallCells y T) (hE : E ∈ d.smallCells y T) : C ⊆ E ∨ E ⊆ C := by
  classical
  obtain ⟨r,rfl,hr⟩ := (Finset.mem_filter.mp hC).2
  obtain ⟨t,rfl,ht⟩ := (Finset.mem_filter.mp hE).2
  rcases le_total t r with h | h
  · exact Or.inl (d.cell_mono h y)
  · exact Or.inr (d.cell_mono h y)


-- @@ L163-184 verbatim
lemma smallNeighbors_card (y : P) (T : ℝ) (hT : 0 < T) :
    ((d.smallNeighbors y T).card : ℝ) < T := by
  classical
  by_cases hne : (d.smallCells y T).Nonempty
  · obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image (d.smallCells y T) Finset.card hne
    have he : d.smallNeighbors y T = C := by
      classical
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨E,hE,hx⟩ := Finset.mem_biUnion.mp hx
        change x ∈ E at hx
        rcases d.smallCells_chain y T hE hC with h | h
        · exact h hx
        · have he : C = E := Finset.eq_of_subset_of_card_le h (hmax E hE)
          simpa only [he] using hx
      · intro x hx
        exact Finset.mem_biUnion.mpr ⟨C,hC,hx⟩
    rw [he]
    obtain ⟨r,hr,ht⟩ := (Finset.mem_filter.mp hC).2
    exact ht
  · rw [smallNeighbors,Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using hT


-- @@ L186-194 verbatim
lemma source_mem_smallNeighbors (y x : P) (r T : ℝ)
    (hxy : y ∈ d.cell r x) (hT : ((d.cell r x).card : ℝ) < T) :
    x ∈ d.smallNeighbors y T := by
  classical
  have he := d.cell_eq_of_share ((d.mem_cell r x y).mp hxy)
  apply Finset.mem_biUnion.mpr
  refine ⟨d.cell r y, ?_, (d.mem_cell r y x).mpr (d.share_symm ((d.mem_cell r x y).mp hxy))⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,r,rfl,by rwa [← he]⟩

-- @@ L195-195 verbatim
end WeakPinned.Hierarchy.Depth


-- @@ L197-197 verbatim
namespace WeakPinned.Hierarchy.Depth

-- @@ L198-198 verbatim
open MeasureTheory

-- @@ L199-199 verbatim
variable {P : Type u2} [Fintype P] [DecidableEq P]

-- @@ L200-200 verbatim
variable (d : Depth P)


-- @@ L202-209 verbatim
lemma smallNeighbors_self (y : P) (T : ℝ) (hne : (d.smallNeighbors y T).Nonempty) :
    y ∈ d.smallNeighbors y T := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨C,hC,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨r,rfl,hr⟩ := (Finset.mem_filter.mp hC).2
  apply Finset.mem_biUnion.mpr
  exact ⟨d.cell r y,hC,d.self_mem_cell r y⟩


-- @@ L211-226 verbatim
lemma smallNeighbors_erase_bound (hn : 2 ≤ Fintype.card P) (y : P)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ((d.smallNeighbors y (τ*Fintype.card P)).erase y).card ≤ τ*((Fintype.card P : ℝ)-1) := by
  classical
  have hn0 : 0 < (Fintype.card P : ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hn1 : 0 ≤ (Fintype.card P : ℝ)-1 := by
    have : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
    linarith
  by_cases hne : (d.smallNeighbors y (τ*Fintype.card P)).Nonempty
  · have hy := d.smallNeighbors_self y _ hne
    have hc := d.smallNeighbors_card y (τ*Fintype.card P) (mul_pos hτ hn0)
    rw [Finset.card_erase_of_mem hy,Nat.cast_sub (Finset.one_le_card.mpr hne),Nat.cast_one]
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.erase_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hτ.le hn1


-- @@ L228-259 verbatim
/-- All candidate sources for each target lie in one small neighborhood,
    allowing a level-dependent fiber reparametrization. -/

lemma smallNeighbors_pair_bound (hn : 2 ≤ Fintype.card P)
    (q : P → P → ℝ) (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hq : ∀ x y, x ≠ y → q x y ≤ B / ((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1)))
    (C : Finset P) :
    (∑ y ∈ C, ∑ x ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, q x y) ≤
      B*τ*((C.card : ℝ)/Fintype.card P) := by
  classical
  have hn0 : 0 < (Fintype.card P : ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hn1 : 0 < (Fintype.card P : ℝ)-1 := by
    have : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
    linarith
  have hden : 0 ≤ B / ((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1)) :=
    div_nonneg hB (mul_pos hn0 hn1).le
  have hy (y : P) : (∑ x ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, q x y) ≤
      B*τ/Fintype.card P := by
    classical
    calc
      _ ≤ ∑ x ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y,
          B / ((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1)) :=
        Finset.sum_le_sum (fun x hx => hq x y (Finset.ne_of_mem_erase hx))
      _ = (((d.smallNeighbors y (τ*Fintype.card P)).erase y).card : ℝ) *
          (B / ((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1))) := by simp
      _ ≤ (τ*((Fintype.card P : ℝ)-1)) *
          (B / ((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1))) :=
        mul_le_mul_of_nonneg_right (d.smallNeighbors_erase_bound hn y τ hτ hτ1) hden
      _ = B*τ/Fintype.card P := by field_simp
  calc
    _ ≤ ∑ y ∈ C, B*τ/Fintype.card P := Finset.sum_le_sum (fun y _ => hy y)
    _ = _ := by simp; ring


-- @@ L261-261 verbatim
end WeakPinned.Hierarchy.Depth


-- @@ L263-263 verbatim
namespace WeakPinned.SmallFiber

-- @@ L264-264 verbatim
open MeasureTheory

-- @@ L265-265 verbatim
variable {P : Type u3} [Fintype P] [DecidableEq P]


-- @@ L267-269 verbatim
/-- Probability of a finite subset; the fiber weights used below will be the
    exact uniform probabilities on the original retained distance fibers. -/
def mass (p : P → ℝ) (C : Finset P) : ℝ := ∑ y ∈ C, p y


-- @@ L271-273 verbatim
omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun y _ => hp y)


-- @@ L275-277 verbatim
omit [Fintype P] [DecidableEq P] in
lemma mass_mono {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) {C D : Finset P} (h : C ⊆ D) :
    mass p C ≤ mass p D := Finset.sum_le_sum_of_subset_of_nonneg h (fun y _ _ => hp y)


-- @@ L279-281 verbatim
omit [DecidableEq P] in
lemma mass_le_one {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (C : Finset P) :
    mass p C ≤ 1 := by rw [← h1]; exact mass_mono hp (Finset.subset_univ C)


-- @@ L283-291 verbatim
omit [Fintype P] in
lemma mass_diff_inter (p : P → ℝ) (C D : Finset P) :
    mass p C = mass p (C \ D) + mass p (C ∩ D) := by
  classical
  symm
  have hh := Finset.sum_sdiff (f:=p) (Finset.inter_subset_left (s₁:=C) (s₂:=D))
  have he : C \ (C ∩ D) = C \ D := by ext y; simp
  rw [he] at hh
  exact hh


-- @@ L293-301 verbatim
lemma mass_cover (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (C D : Finset P) : 1 ≤ mass p C + mass p D + mass p (C ∪ D)ᶜ := by
  classical
  rw [← h1]
  have he := Finset.sum_compl_add_sum (C ∪ D) p
  have hu := (Finset.sum_union_inter (s₁:=C) (s₂:=D) (f:=p))
  have hn := mass_nonneg hp (C ∩ D)
  unfold mass at *
  linarith


-- @@ L303-313 verbatim
lemma small_case_one (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (C D : Finset P) (lam : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hC : mass p C ≤ lam) :
    mass p C ≤ 2*lam*mass p D + mass p (C ∪ D)ᶜ := by
  classical
  have hc := mass_cover p hp h1 C D
  have hnC := mass_nonneg hp C
  have hnD := mass_nonneg hp D
  have hnE := mass_nonneg hp (C∪D)ᶜ
  have hp2 : mass p C ≤ 1/2 := hC.trans hlam2
  nlinarith


-- @@ L315-315 verbatim
end WeakPinned.SmallFiber


-- @@ L317-317 verbatim
namespace WeakPinned.Hierarchy.Depth

-- @@ L318-318 verbatim
open MeasureTheory

-- @@ L319-319 verbatim
variable {P : Type u4} [Fintype P] [DecidableEq P]

-- @@ L320-320 verbatim
variable (d : Depth P)


-- @@ L322-336 verbatim
lemma nongiant_share_overlap {r : ℝ} {x y : P} (hg : ¬ d.sourceGiant x r)
    (hy : y ∈ d.cell r x) : 1 ≤ d.pairOverlap r x y := by
  classical
  have hs := (d.mem_cell r x y).mp hy
  rw [d.pairOverlap_formula, ite_eq_left hs]
  by_cases he : (d.giants r).Nonempty
  · have hx : x ∉ d.giant r := by
      intro hx
      exact hg ((d.sourceGiant_mem_giant x r).mpr ⟨he,hx⟩)
    have hy' : y ∉ d.giant r := by
      intro hy'
      have hgy := (d.sourceGiant_mem_giant y r).mpr ⟨he,hy'⟩
      exact hg (by simpa only [sourceGiant, d.cell_eq_of_share hs] using hgy)
    simp [giantIndicator,outsideIndicator,he,hx,hy']
  · simp [giantIndicator,outsideIndicator,he]


-- @@ L338-338 verbatim
end WeakPinned.Hierarchy.Depth


-- @@ L340-340 verbatim
namespace WeakPinned.SmallFiber

-- @@ L341-341 verbatim
open MeasureTheory Hierarchy

-- @@ L342-342 verbatim
variable {P : Type u5} [Fintype P] [DecidableEq P]


-- @@ L344-347 verbatim
lemma mass_as_sum (p : P → ℝ) (C : Finset P) :
    mass p C = ∑ y, if y ∈ C then p y else 0 := by
  classical
  simp [mass]


-- @@ L349-357 verbatim
lemma mass_as_sum_off (p : P → ℝ) (x : P) (hx : p x = 0) (C : Finset P) :
    mass p C = ∑ y, if x ≠ y ∧ y ∈ C then p y else 0 := by
  classical
  rw [mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp [hxy]


-- @@ L359-374 verbatim
lemma nongiant_mass_bound (d : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (r : ℝ) :
    (if ¬d.sourceGiant x r then mass p (d.cell r x) else 0) ≤
      ∑ y, p y * d.pairOverlap r x y := by
  classical
  by_cases hg : d.sourceGiant x r
  · simp only [hg,not_true_eq_false,ite_false]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp y) (d.pairOverlap_bounds r x y).1)
  · simp only [hg,not_false_eq_true,ite_true]
    rw [mass_as_sum]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : y ∈ d.cell r x
    · simp only [hy,ite_true]
      nlinarith [d.nongiant_share_overlap hg hy, hp y]
    · simpa only [hy,ite_false] using mul_nonneg (hp y) (d.pairOverlap_bounds r x y).1


-- @@ L376-382 verbatim
lemma integral_open_interval (a b : ℝ) :
    (∫ r : ℝ, if a < r ∧ r < b then (1:ℝ) else 0) = max (b-a) 0 := by
  have he : (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Ioo]
  simp [integral_const,measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal']


-- @@ L384-390 verbatim
lemma integral_closed_interval (a b : ℝ) :
    (∫ r : ℝ, if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) = max (b-a) 0 := by
  have he : (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Icc]
  simp [integral_const,measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal']


-- @@ L392-398 verbatim
lemma integrable_open_interval (a b : ℝ) :
    Integrable (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) := by
  have he : (fun r : ℝ => if a < r ∧ r < b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integrable_indicator_iff measurableSet_Ioo]
  exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)


-- @@ L400-406 verbatim
lemma integrable_closed_interval (a b : ℝ) :
    Integrable (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) := by
  have he : (fun r : ℝ => if a ≤ r ∧ r ≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r; simp [Set.indicator_apply]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)


-- @@ L408-409 verbatim
def minusError (d d' : Depth P) (p : P → ℝ) (x : P) (h H r : ℝ) : ℝ :=
  mass p (d.cell r x ∪ d'.cell (h-r-H) x)ᶜ


-- @@ L411-412 verbatim
def plusError (d d' : Depth P) (p : P → ℝ) (x : P) (h H r : ℝ) : ℝ :=
  mass p (d.cell r x ∩ d'.cell (h-r+H) x)


-- @@ L414-428 verbatim
lemma minusError_formula (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H r : ℝ) :
    minusError d d' p x h H r = ∑ y, p y *
      (if d.value x y < r ∧ r < h-H-d'.value x y then (1:ℝ) else 0) := by
  classical
  rw [minusError,mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp only [Finset.mem_compl,Finset.mem_union,Depth.mem_cell,Depth.share,hxy,false_or,not_or,not_le]
    have he : (d.value x y < r ∧ d'.value x y < h-r-H) ↔
        d.value x y < r ∧ r < h-H-d'.value x y := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp


-- @@ L430-444 verbatim
lemma plusError_formula (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H r : ℝ) :
    plusError d d' p x h H r = ∑ y, p y *
      (if h+H-d'.value x y ≤ r ∧ r ≤ d.value x y then (1:ℝ) else 0) := by
  classical
  rw [plusError,mass_as_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x = y
  · subst y; simp [hx]
  · simp only [Finset.mem_inter,Depth.mem_cell,Depth.share,hxy,false_or]
    have he : (r ≤ d.value x y ∧ h-r+H ≤ d'.value x y) ↔
        h+H-d'.value x y ≤ r ∧ r ≤ d.value x y := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp


-- @@ L446-450 verbatim
lemma minusError_integrable (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : Integrable (minusError d d' p x h H) := by
  change Integrable (fun r => minusError d d' p x h H r)
  simp_rw [minusError_formula d d' p x hx]
  exact integrable_finsetSum _ (fun y _ => (integrable_open_interval _ _).const_mul (p y))


-- @@ L452-456 verbatim
lemma plusError_integrable (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : Integrable (plusError d d' p x h H) := by
  change Integrable (fun r => plusError d d' p x h H r)
  simp_rw [plusError_formula d d' p x hx]
  exact integrable_finsetSum _ (fun y _ => (integrable_closed_interval _ _).const_mul (p y))


-- @@ L458-466 verbatim
lemma minusError_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : (∫ r, minusError d d' p x h H r) =
      ∑ y, p y * max (h-d.value x y-d'.value x y-H) 0 := by
  simp_rw [minusError_formula d d' p x hx]
  rw [integral_finsetSum _ (fun y _ => (integrable_open_interval _ _).const_mul (p y))]
  simp_rw [integral_const_mul,integral_open_interval]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring


-- @@ L468-476 verbatim
lemma plusError_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) : (∫ r, plusError d d' p x h H r) =
      ∑ y, p y * max (d.value x y+d'.value x y-h-H) 0 := by
  simp_rw [plusError_formula d d' p x hx]
  rw [integral_finsetSum _ (fun y _ => (integrable_closed_interval _ _).const_mul (p y))]
  simp_rw [integral_const_mul,integral_closed_interval]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring


-- @@ L478-482 verbatim
lemma two_truncations (a H : ℝ) (hH : 0 ≤ H) :
    max (-a-H) 0 + max (a-H) 0 = max (|a|-H) 0 := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha,max_eq_right (by linarith : -a-H ≤ 0),zero_add]
  · rw [abs_of_nonpos ha,max_eq_right (by linarith : a-H ≤ 0),add_zero]


-- @@ L484-493 verbatim
lemma errors_integral (d d' : Depth P) (p : P → ℝ) (x : P) (hx : p x = 0)
    (h H : ℝ) (hH : 0 ≤ H) :
    (∫ r, minusError d d' p x h H r + plusError d d' p x h H r) =
      ∑ y, p y * max (|d.value x y+d'.value x y-h|-H) 0 := by
  rw [integral_add (minusError_integrable d d' p x hx h H) (plusError_integrable d d' p x hx h H),
    minusError_integral d d' p x hx, plusError_integral d d' p x hx,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have he : h-d.value x y-d'.value x y-H = -(d.value x y+d'.value x y-h)-H := by ring
  rw [he,← mul_add,two_truncations _ H hH]


-- @@ L495-495 verbatim
end WeakPinned.SmallFiber


-- @@ L497-497 verbatim
namespace WeakPinned.SmallFiber

-- @@ L498-498 verbatim
open MeasureTheory Hierarchy

-- @@ L499-499 verbatim
variable {P : Type u6} [Fintype P] [DecidableEq P]


-- @@ L501-505 verbatim
/-- Actual source cell, not a giant-complement occurrence. -/
def activeMass (d : Depth P) (p : P → ℝ) (x : P) (T lam r : ℝ) : ℝ := by
  classical
  exact if ¬d.sourceGiant x r ∧ ((d.cell r x).card : ℝ) < T ∧ mass p (d.cell r x) < lam
    then mass p (d.cell r x) else 0


-- @@ L507-508 verbatim
def nongiantMass (d : Depth P) (p : P → ℝ) (x : P) (r : ℝ) : ℝ :=
  if ¬d.sourceGiant x r then mass p (d.cell r x) else 0


-- @@ L510-511 verbatim
def straddle (d : Depth P) (x : P) (h H r : ℝ) : ℝ :=
  if d.sourceGiant x (h-r-H) ∧ ¬d.sourceGiant x (h-r+H) then 1 else 0


-- @@ L513-515 verbatim
def neighborMass (d d' : Depth P) (p : P → ℝ) (x : P) (T t : ℝ) : ℝ := by
  classical
  exact ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.outsideIndicator t y else 0)


-- @@ L517-520 verbatim
lemma neighborMass_nonneg (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (T t : ℝ) : 0 ≤ neighborMass d d' p x T t := by
  classical
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (hp y) (by split_ifs; exact (d'.outsideIndicator_bounds t y).1; rfl))


-- @@ L522-526 verbatim
omit [DecidableEq P] in
lemma nongiantMass_nonneg (d : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (r : ℝ) : 0 ≤ nongiantMass d p x r := by
  unfold nongiantMass
  split_ifs <;> first | exact mass_nonneg hp _ | rfl


-- @@ L528-547 verbatim
lemma case_three_bound (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (x : P) (hx : p x = 0) (r t T : ℝ)
    (hT : ((d.cell r x).card : ℝ) < T) (hg : d'.sourceGiant x t) :
    mass p (d.cell r x \ d'.cell t x) ≤ neighborMass d d' p x T t := by
  classical
  rw [mass_as_sum_off p x hx]
  unfold neighborMass
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : x ≠ y ∧ y ∈ d.cell r x \ d'.cell t x
  · obtain ⟨hxy,hyD⟩ := hy
    obtain ⟨hyU,hyV⟩ := Finset.mem_sdiff.mp hyD
    have hn : x ∈ (d.smallNeighbors y T).erase y :=
      Finset.mem_erase.mpr ⟨hxy, d.source_mem_smallNeighbors y x r T hyU hT⟩
    have hG : d'.cell t x ∈ d'.giants t := (d'.mem_giants t _).mpr ⟨d'.cell_mem_cells t x,hg⟩
    have he : (d'.giants t).Nonempty := ⟨_,hG⟩
    have hyo : y ∉ d'.giant t := by rwa [d'.giant_eq hG]
    simp [hxy,hyD,hn,Depth.outsideIndicator,he,hyo]
  · simp only [hy,ite_false]
    exact mul_nonneg (hp y) (by split_ifs; exact (d'.outsideIndicator_bounds t y).1; rfl)


-- @@ L549-582 verbatim
/-- The pointwise small-fiber bound. The only independent error is the exact
    pair of intervals already evaluated. -/
lemma active_pointwise (d d' : Depth P) (p : P → ℝ) (hp : ∀ y, 0 ≤ p y)
    (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) (h H T lam r : ℝ)
    (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2) :
    activeMass d p x T lam r ≤
      2*lam*nongiantMass d' p x (h-r-H) + lam*straddle d' x h H r +
      minusError d d' p x h H r + plusError d d' p x h H r +
      neighborMass d d' p x T (h-r+H) := by
  classical
  have hminus : 0 ≤ minusError d d' p x h H r := mass_nonneg hp _
  have hplus : 0 ≤ plusError d d' p x h H r := mass_nonneg hp _
  have hnbr := neighborMass_nonneg d d' p hp x T (h-r+H)
  have hng := nongiantMass_nonneg d' p hp x (h-r-H)
  have hstr : 0 ≤ straddle d' x h H r := by unfold straddle; split_ifs <;> norm_num
  unfold activeMass
  split_ifs with ha
  · obtain ⟨haG,haT,haP⟩ := ha
    by_cases hg : d'.sourceGiant x (h-r-H)
    · by_cases hg' : d'.sourceGiant x (h-r+H)
      · have hthree := case_three_bound d d' p hp x hx r (h-r+H) T haT hg'
        have he := mass_diff_inter p (d.cell r x) (d'.cell (h-r+H) x)
        change mass p (d.cell r x) = _ + plusError d d' p x h H r at he
        nlinarith
      · have hs : straddle d' x h H r = 1 := by simp [straddle,hg,hg']
        rw [hs]
        nlinarith
    · have hone := small_case_one p hp h1 (d.cell r x) (d'.cell (h-r-H) x) lam hlam hlam2 haP.le
      have hnge : nongiantMass d' p x (h-r-H) = mass p (d'.cell (h-r-H) x) := by
        simp [nongiantMass,hg]
      rw [hnge]
      change mass p (d.cell r x) ≤ _ + minusError d d' p x h H r at hone
      nlinarith
  · positivity


-- @@ L584-596 verbatim
omit [DecidableEq P] in
lemma nongiantMass_measurable (d : Depth P) (p : P → ℝ) (x : P) :
    Measurable (nongiantMass d p x) := by
  classical
  let f : Finset P → ℝ := fun C => if ¬Fintype.card P < 2*C.card then mass p C else 0
  have h := (measurable_of_finite f).comp (d.measurable_cell x)
  have he : nongiantMass d p x = f ∘ (fun r => d.cell r x) := by
    funext r
    by_cases hg : Fintype.card P < 2*(d.cell r x).card
    · simp [nongiantMass,f,Depth.sourceGiant,hg]
    · simp [nongiantMass,f,Depth.sourceGiant,hg]
  rw [he]
  exact h


-- @@ L598-611 verbatim
omit [DecidableEq P] in
lemma activeMass_measurable (d : Depth P) (p : P → ℝ) (x : P) (T lam : ℝ) :
    Measurable (activeMass d p x T lam) := by
  classical
  let f : Finset P → ℝ := fun C => if ¬Fintype.card P < 2*C.card ∧ (C.card : ℝ) < T ∧ mass p C < lam
      then mass p C else 0
  have h := (measurable_of_finite f).comp (d.measurable_cell x)
  have he : activeMass d p x T lam = f ∘ (fun r => d.cell r x) := by
    funext r
    by_cases hg : Fintype.card P < 2*(d.cell r x).card
    · simp [activeMass,f,Depth.sourceGiant,hg]
    · simp [activeMass,f,Depth.sourceGiant,hg,Nat.not_lt.mp hg]
  rw [he]
  exact h


-- @@ L613-636 verbatim
omit [DecidableEq P] in
lemma nongiantMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) :
    Integrable (nongiantMass d p x) := by
  classical
  apply Depth.integrable_supported_Icc (nongiantMass_measurable d p x) (a:=-d.radius) (b:=d.radius) (C:=1)
  · intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (nongiantMass_nonneg d p hp x r)]
    unfold nongiantMass
    split_ifs <;> first | exact mass_le_one hp h1 _ | norm_num
  · intro r hr
    by_cases hlo : r ≤ -d.radius
    · have hG : d.sourceGiant x r := by
        unfold Depth.sourceGiant
        rw [d.cell_of_low hlo x,Finset.card_univ]
        omega
      simp [nongiantMass,hG]
    · have hhi : d.radius < r := by
        by_contra! hhi
        exact hr ⟨(not_le.mp hlo).le,hhi⟩
      simp only [nongiantMass]
      rw [d.cell_of_high hhi x]
      have he : mass p {x} = 0 := by simp [mass,hx]
      split_ifs <;> simp [he]


-- @@ L638-647 verbatim
omit [DecidableEq P] in
lemma activeMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0)
    (T lam : ℝ) : Integrable (activeMass d p x T lam) := by
  classical
  apply (nongiantMass_integrable d hn p hp h1 x hx).mono'
    (activeMass_measurable d p x T lam).aestronglyMeasurable
  filter_upwards with r
  unfold activeMass nongiantMass
  split_ifs <;> simp_all [abs_of_nonneg (mass_nonneg hp (d.cell r x)),mass_nonneg hp]


-- @@ L649-660 verbatim
lemma straddle_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P) (x : P) (h H : ℝ) :
    Integrable (straddle d x h H) := by
  classical
  have he : straddle d x h H =
      (Set.Ico (h-H-d.sourceM x) (h+H-d.sourceM x)).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r
    simp only [straddle,d.sourceGiant_cutoff hn,not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
  rw [he,integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)


-- @@ L662-672 verbatim
lemma neighborMass_integrable (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (T : ℝ) : Integrable (neighborMass d d' p x T) := by
  classical
  unfold neighborMass
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  by_cases h : x ∈ (d.smallNeighbors y T).erase y
  · simpa only [h,ite_true] using d'.integrable_outsideIndicator hn y
  · simp only [h,ite_false]
    exact integrable_zero _ _ _


-- @@ L674-691 verbatim
lemma neighborMass_integral (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (T : ℝ) :
    (∫ r, neighborMass d d' p x T r) =
      ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.potential y else 0) := by
  classical
  unfold neighborMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul]
    by_cases hh : x ∈ (d.smallNeighbors y T).erase y
    · simp only [hh,ite_true,Depth.potential]
    · simp only [hh,ite_false,integral_zero]
  · intro y _
    apply Integrable.const_mul
    by_cases hh : x ∈ (d.smallNeighbors y T).erase y
    · simpa only [hh,ite_true] using d'.integrable_outsideIndicator hn y
    · simp only [hh,ite_false]; exact integrable_zero _ _ _


-- @@ L693-693 verbatim
end WeakPinned.SmallFiber


-- @@ L695-695 verbatim
namespace WeakPinned.SmallFiber

-- @@ L696-696 verbatim
open MeasureTheory Hierarchy

-- @@ L697-697 verbatim
variable {P : Type u7} [Fintype P] [DecidableEq P]


-- @@ L699-706 verbatim
lemma pairMass_integrable (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (x : P) (hx : p x = 0) :
    Integrable (fun r => ∑ y, p y * d.pairOverlap r x y) := by
  apply integrable_finsetSum
  intro y _
  by_cases hxy : x = y
  · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
  · exact (d.integrable_pairOverlap hn x y hxy).const_mul _


-- @@ L708-721 verbatim
lemma integral_nongiantMass_bound (d : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) (x : P) (hx : p x = 0) :
    (∫ r, nongiantMass d p x r) ≤ ∑ y, p y * ∫ r, d.pairOverlap r x y := by
  calc
    _ ≤ ∫ r : ℝ, ∑ y, p y * d.pairOverlap r x y :=
      integral_mono (nongiantMass_integrable d hn p hp h1 x hx) (pairMass_integrable d hn p x hx)
        (fun r => nongiant_mass_bound d p hp x r)
    _ = _ := by
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun y _ => integral_const_mul (p y) _)
      · intro y _
        by_cases hxy : x = y
        · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
        · exact (d.integrable_pairOverlap hn x y hxy).const_mul _


-- @@ L723-765 verbatim
/-- The local small-fiber bound for two entire realized hierarchies. This
    includes the exact signed-depth error; it will vanish at finite places
    and have an exponentially small grid mean at archimedean places. -/
lemma active_integral (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1)
    (x : P) (hx : p x = 0) (h H T lam : ℝ)
    (hH : 0 ≤ H) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2) :
    (∫ r, activeMass d p x T lam r) ≤
      2*lam*(∑ y, p y * ∫ r, d'.pairOverlap r x y) + 2*lam*H +
      (∑ y, p y * max (|d.value x y+d'.value x y-h|-H) 0) +
      ∑ y, p y * (if x ∈ (d.smallNeighbors y T).erase y then d'.potential y else 0) := by
  classical
  have hshift₁ (r : ℝ) : h-r-H = (h-H)-r := by ring
  have hshift₂ (r : ℝ) : h-r+H = (h+H)-r := by ring
  have hi₁ : Integrable (fun r => 2*lam*nongiantMass d' p x (h-r-H)) := by
    simp_rw [hshift₁]
    exact ((integrable_comp_sub_left _ (h-H)).mpr (nongiantMass_integrable d' hn p hp h1 x hx)).const_mul _
  have hi₂ : Integrable (fun r => lam*straddle d' x h H r) :=
    (straddle_integrable d' hn x h H).const_mul _
  have hi₃ := (minusError_integrable d d' p x hx h H).add (plusError_integrable d d' p x hx h H)
  have hi₄ : Integrable (fun r => neighborMass d d' p x T (h-r+H)) := by
    simp_rw [hshift₂]
    exact (integrable_comp_sub_left _ (h+H)).mpr (neighborMass_integrable d d' hn p x T)
  have hb := integral_mono (activeMass_integrable d hn p hp h1 x hx T lam)
    (((hi₁.add hi₂).add hi₃).add hi₄) (fun r => by
      have hh := active_pointwise d d' p hp h1 x hx h H T lam r hlam hlam2
      dsimp only [Pi.add_apply]
      linarith)
  simp only [Pi.add_apply] at hb
  have he₁ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have he₂ := integral_add (hi₁.add hi₂) hi₃
  have he₃ := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at he₁ he₂ he₃
  rw [he₁,he₂,he₃] at hb
  rw [integral_const_mul,integral_const_mul] at hb
  simp_rw [hshift₁,hshift₂] at hb
  rw [integral_sub_left_eq_self,integral_sub_left_eq_self,
    neighborMass_integral d d' hn p x T,errors_integral d d' p x hx h H hH] at hb
  have hs : (∫ r, straddle d' x h H r) = 2*H := d'.straddle_integral hn x h H hH
  rw [hs] at hb
  have hng := mul_le_mul_of_nonneg_left (integral_nongiantMass_bound d' hn p hp h1 x hx)
    (show 0 ≤ 2*lam by positivity)
  linarith


-- @@ L767-770 verbatim
/-- Exact edge law induced by fiber sampling; no independence of fiber
    labels or levels is postulated. -/
def edgeLaw {I : Type u8} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (a b : P) : ℝ :=
  ∑ i, if x i = a then w i * p i b else 0


-- @@ L772-815 verbatim
lemma fiber_neighbor_bound {I : Type u9} [Fintype I]
    (d d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ i, w i * ∑ y, p i y *
      (if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then d'.potential y else 0)) ≤
      B*τ/Fintype.card P * ∑ y, d'.potential y := by
  classical
  have hn0 : 0 < (Fintype.card P:ℝ) := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have hn1 : 0 < (Fintype.card P:ℝ)-1 := by
    have : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
    linarith
  have hid (y : P) :
      (∑ i, w i * (p i y * (if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then d'.potential y else 0))) =
      (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, edgeLaw w p x a y) * d'.potential y := by
    rw [Finset.sum_mul]
    simp only [edgeLaw,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    have he : (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y,
        if x i = a then w i*p i y else 0) =
        if x i ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y then w i*p i y else 0 := by
      simp [eq_comm]
    rw [he]
    split_ifs <;> ring
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hid]
  have hb (y : P) : (∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y, edgeLaw w p x a y) ≤ B*τ/Fintype.card P := by
    calc
      _ ≤ ((d.smallNeighbors y (τ*Fintype.card P)).erase y).card *
          (B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) := by
        calc
          _ ≤ ∑ a ∈ (d.smallNeighbors y (τ*Fintype.card P)).erase y,
              B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)) :=
            Finset.sum_le_sum (fun a ha => hdom a y (Finset.ne_of_mem_erase ha))
          _ = _ := by simp
      _ ≤ (τ*((Fintype.card P:ℝ)-1)) * (B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :=
        mul_le_mul_of_nonneg_right (d.smallNeighbors_erase_bound hn y τ hτ hτ1) (by positivity)
      _ = _ := by field_simp
  exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hb y) (d'.potential_nonneg y))


-- @@ L817-817 verbatim
end WeakPinned.SmallFiber


-- @@ L819-819 verbatim
end

-- @@ L820-820 verbatim
end

-- @@ L821-821 verbatim
end

-- @@ L822-822 verbatim
end

-- @@ L823-823 verbatim
end

-- @@ L824-824 verbatim
end


-- @@ L826-826 verbatim
end OAI
