/-
# Sofa/PolyGraph.lean — polygon caps and niches as regions between graphs (blueprint §11)

For `h : ℝ → ℝ` (support values on `Θ^⋄`) we define
* the cap roof `U_h = min_{s ∈ Θ^⋄} ℓ_{s,h(s)}`, the fan floor `f_h = max_{s ∈ {ω,π/2}} ℓ_{s,h(s)-1}`,
  the niche roof `R_h = max_{t ∈ Θ} min(ℓ_{t,h(t)-1}, ℓ_{t+π/2,h(t+π/2)-1})`;
* `C_Θ(h) = {f_h ≤ y ≤ U_h}` (`capH`), `N_Θ(h) = {f_h ≤ y < R_h}` (`nicheH`) and
  `A_Θ(h) = ∫ ((U_h - f_h)⁺ - (R_h - f_h)⁺)` (`areaH`);
* the half-plane descriptions, the identification with `polyCap`, `polyNiche`, `polySofaArea`
  for caps, and a uniform bound on the supports.

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.Graph
import Sofa.PolyCap


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Real Set Filter Topology MeasureTheory

-- @@ L20-20 verbatim
open scoped EuclideanGeometry RealInnerProductSpace


-- @@ L22-22 verbatim
namespace Sofa


-- @@ L24-28 verbatim
/-- Standing hypotheses on the rotation angle and the angle set. -/
structure PolySetup (ω : ℝ) (Θ : Finset ℝ) : Prop where
  pos : 0 < ω
  le : ω ≤ π / 2
  angles : IsAngleSet ω Θ


-- @@ L30-31 verbatim
/-- `Θ^⋄ = Θ ∪ (Θ + π/2) ∪ {ω, π/2}` as a finset. -/
def diamondFin (ω : ℝ) (Θ : Finset ℝ) : Finset ℝ := Θ ∪ Θ.image (· + π / 2) ∪ {ω, π / 2}


-- @@ L33-34 verbatim
/-- The two fan angles `{ω, π/2}`. -/
def fanFin (ω : ℝ) : Finset ℝ := {ω, π / 2}


-- @@ L36-36 verbatim
variable {ω : ℝ} {Θ : Finset ℝ}


-- @@ L38-38 verbatim
lemma mem_fanFin {s : ℝ} : s ∈ fanFin ω ↔ s = ω ∨ s = π / 2 := by simp [fanFin]


-- @@ L40-40 verbatim
lemma self_mem_fanFin (ω : ℝ) : ω ∈ fanFin ω := mem_fanFin.2 (Or.inl rfl)


-- @@ L42-42 verbatim
lemma pi_div_two_mem_fanFin (ω : ℝ) : π / 2 ∈ fanFin ω := mem_fanFin.2 (Or.inr rfl)


-- @@ L44-44 verbatim
lemma fanFin_nonempty (ω : ℝ) : (fanFin ω).Nonempty := ⟨ω, self_mem_fanFin ω⟩


-- @@ L46-47 verbatim
lemma fanFin_subset (ω : ℝ) (Θ : Finset ℝ) : fanFin ω ⊆ diamondFin ω Θ :=
  Finset.subset_union_right


-- @@ L49-50 verbatim
lemma diamondFin_nonempty (ω : ℝ) (Θ : Finset ℝ) : (diamondFin ω Θ).Nonempty :=
  (fanFin_nonempty ω).mono (fanFin_subset ω Θ)


-- @@ L52-54 verbatim
lemma mem_diamondFin {s : ℝ} :
    s ∈ diamondFin ω Θ ↔ s ∈ Θ ∨ (∃ t ∈ Θ, t + π / 2 = s) ∨ s ∈ fanFin ω := by
  simp only [diamondFin, fanFin, Finset.mem_union, Finset.mem_image, or_assoc]


-- @@ L56-57 verbatim
lemma mem_diamondFin_of_mem {t : ℝ} (ht : t ∈ Θ) : t ∈ diamondFin ω Θ :=
  mem_diamondFin.2 (Or.inl ht)


-- @@ L59-60 verbatim
lemma add_mem_diamondFin {t : ℝ} (ht : t ∈ Θ) : t + π / 2 ∈ diamondFin ω Θ :=
  mem_diamondFin.2 (Or.inr (Or.inl ⟨t, ht, rfl⟩))


-- @@ L62-63 verbatim
lemma mem_diamondFin_of_fan {s : ℝ} (hs : s ∈ fanFin ω) : s ∈ diamondFin ω Θ :=
  fanFin_subset ω Θ hs


-- @@ L65-68 verbatim
lemma coe_diamondFin : (diamondFin ω Θ : Set ℝ) = diamondAngles ω Θ := by
  ext s
  simp only [Finset.mem_coe, mem_diamondFin, diamondAngles, mem_union, mem_image,
    Finset.mem_coe, mem_insert_iff, mem_singleton_iff, mem_fanFin, or_assoc]


-- @@ L70-70 verbatim
namespace PolySetup


-- @@ L72-72 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L73-73 verbatim
include hP


-- @@ L75-75 verbatim
lemma nonempty : Θ.Nonempty := hP.angles.1


-- @@ L77-77 verbatim
lemma mem_Θ {t : ℝ} (ht : t ∈ Θ) : 0 < t ∧ t < ω := hP.angles.2 t ht


-- @@ L79-79 verbatim
lemma lt_pi_div_two {t : ℝ} (ht : t ∈ Θ) : t < π / 2 := (hP.mem_Θ ht).2.trans_le hP.le


-- @@ L81-82 verbatim
lemma sin_pos_Θ {t : ℝ} (ht : t ∈ Θ) : 0 < sin t :=
  sin_pos_of_pos_of_lt_pi (hP.mem_Θ ht).1 ((hP.lt_pi_div_two ht).trans (by linarith [pi_pos]))


-- @@ L84-85 verbatim
lemma cos_pos_Θ {t : ℝ} (ht : t ∈ Θ) : 0 < cos t :=
  cos_pos_of_mem_Ioo ⟨by linarith [(hP.mem_Θ ht).1, pi_pos], hP.lt_pi_div_two ht⟩


-- @@ L87-97 verbatim
lemma bounds {s : ℝ} (hs : s ∈ diamondFin ω Θ) : 0 < s ∧ s < π := by
  have h0 := hP.pos
  have h1 := hP.le
  rcases mem_diamondFin.1 hs with hs | ⟨t, ht, rfl⟩ | hs
  · have := hP.mem_Θ hs
    exact ⟨this.1, by linarith [pi_pos]⟩
  · have := hP.mem_Θ ht
    exact ⟨by linarith [pi_pos], by linarith⟩
  · rcases mem_fanFin.1 hs with rfl | rfl
    · exact ⟨h0, by linarith [pi_pos]⟩
    · exact ⟨by linarith [pi_pos], by linarith [pi_pos]⟩


-- @@ L99-100 verbatim
lemma sin_pos {s : ℝ} (hs : s ∈ diamondFin ω Θ) : 0 < sin s :=
  sin_pos_of_pos_of_lt_pi (hP.bounds hs).1 (hP.bounds hs).2


-- @@ L102-103 verbatim
lemma sin_pos_fan {s : ℝ} (hs : s ∈ fanFin ω) : 0 < sin s :=
  hP.sin_pos (mem_diamondFin_of_fan hs)


-- @@ L105-110 verbatim
lemma cot_injOn : Set.InjOn (fun s => cos s / sin s) (diamondFin ω Θ : Set ℝ) := by
  intro s hs s' hs' hss'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (cot_lt_cot (hP.bounds hs).1 hlt (hP.bounds hs').2).ne' hss'
  · exact (cot_lt_cot (hP.bounds hs').1 hlt (hP.bounds hs).2).ne hss'


-- @@ L112-116 verbatim
lemma ne_fan {t : ℝ} (ht : t ∈ Θ) {s : ℝ} (hs : s ∈ fanFin ω) : t ≠ s := by
  have := hP.mem_Θ ht
  rcases mem_fanFin.1 hs with rfl | rfl
  · exact this.2.ne
  · exact (hP.lt_pi_div_two ht).ne


-- @@ L118-123 verbatim
lemma add_ne_fan {t : ℝ} (ht : t ∈ Θ) {s : ℝ} (hs : s ∈ fanFin ω) : t + π / 2 ≠ s := by
  have := hP.mem_Θ ht
  have h1 := hP.le
  rcases mem_fanFin.1 hs with rfl | rfl
  · exact ne_of_gt (by linarith)
  · exact ne_of_gt (by linarith)


-- @@ L125-128 verbatim
lemma add_ne {t t' : ℝ} (ht : t ∈ Θ) (ht' : t' ∈ Θ) : t + π / 2 ≠ t' := by
  have := hP.mem_Θ ht
  have := hP.lt_pi_div_two ht'
  exact ne_of_gt (by linarith)


-- @@ L130-130 verbatim
end PolySetup


-- @@ L132-132 verbatim
/-! ## The three graphs -/


-- @@ L134-134 verbatim
variable (ω Θ)


-- @@ L136-138 verbatim
/-- The cap roof `U_h = min_{s ∈ Θ^⋄} ℓ_{s, h(s)}`. -/
def roofU (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (diamondFin ω Θ).inf' (diamondFin_nonempty ω Θ) fun s => lineFn s (h s) x


-- @@ L140-142 verbatim
/-- The fan floor `f_h = max_{s ∈ {ω, π/2}} ℓ_{s, h(s) - 1}`. -/
def floorF (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (fanFin ω).sup' (fanFin_nonempty ω) fun s => lineFn s (h s - 1) x


-- @@ L144-146 verbatim
/-- The niche roof `R_h = max_{t ∈ Θ} min(ℓ_{t, h(t)-1}, ℓ_{t+π/2, h(t+π/2)-1})`. -/
def roofR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  Θ.sup' hΘ fun t => min (lineFn t (h t - 1) x) (lineFn (t + π / 2) (h (t + π / 2) - 1) x)


-- @@ L148-149 expanded
/-- The polygon cap `C_Θ(h)`. -/
def capH (h : ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | floorF ω h (p 0) ≤ p 1 ∧ p 1 ≤ roofU ω Θ h (p 0)}


-- @@ L151-153 expanded
/-- The polygon niche `N_Θ(h)`. -/
def nicheH (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | floorF ω h (p 0) ≤ p 1 ∧ p 1 < roofR Θ hΘ h (p 0)}


-- @@ L155-157 verbatim
/-- The integrand of `A_Θ(h)`. -/
def areaIntegrand (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (roofU ω Θ h x - floorF ω h x) 0 - max (roofR Θ hΘ h x - floorF ω h x) 0


-- @@ L159-160 verbatim
/-- The polygon sofa area functional `A_Θ(h)` (Def 3.3.3). -/
def areaH (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : ℝ := ∫ x, areaIntegrand ω Θ hΘ h x


-- @@ L162-162 verbatim
variable {ω Θ}


-- @@ L164-165 verbatim
lemma continuous_roofU (h : ℝ → ℝ) : Continuous (roofU ω Θ h) :=
  Continuous.finset_inf'_apply (diamondFin_nonempty ω Θ) fun s _ => continuous_lineFn s (h s)


-- @@ L167-168 verbatim
lemma continuous_floorF (h : ℝ → ℝ) : Continuous (floorF ω h) :=
  Continuous.finset_sup'_apply (fanFin_nonempty ω) fun s _ => continuous_lineFn s (h s - 1)


-- @@ L170-172 verbatim
lemma continuous_roofR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : Continuous (roofR Θ hΘ h) :=
  Continuous.finset_sup'_apply hΘ fun t _ =>
    (continuous_lineFn t (h t - 1)).min (continuous_lineFn (t + π / 2) (h (t + π / 2) - 1))


-- @@ L174-180 verbatim
lemma continuous_areaIntegrand (hΘ : Θ.Nonempty) (h : ℝ → ℝ) :
    Continuous (areaIntegrand ω Θ hΘ h) := by
  have h1 := continuous_roofU (ω := ω) (Θ := Θ) h
  have h2 := continuous_floorF (ω := ω) h
  have h3 := continuous_roofR hΘ h
  unfold areaIntegrand
  fun_prop


-- @@ L182-182 verbatim
/-! ## Half-plane descriptions -/


-- @@ L184-184 verbatim
section HalfPlane


-- @@ L186-186 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L187-187 verbatim
include hP


-- @@ L189-192 expanded
lemma floorF_le_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    floorF ω h (p 0) ≤ p 1 ↔ ∀ s ∈ fanFin ω, h s - 1 ≤ ⟪p, u s⟫ :=
  by
  rw [floorF, Finset.sup'_le_iff]
  exact forall₂_congr fun s hs => lineFn_le_iff (hP.sin_pos_fan hs) _ _


-- @@ L194-197 expanded
lemma floorF_lt_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    floorF ω h (p 0) < p 1 ↔ ∀ s ∈ fanFin ω, h s - 1 < ⟪p, u s⟫ :=
  by
  rw [floorF, Finset.sup'_lt_iff]
  exact forall₂_congr fun s hs => lineFn_lt_iff (hP.sin_pos_fan hs) _ _


-- @@ L199-202 expanded
lemma le_roofU_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    p 1 ≤ roofU ω Θ h (p 0) ↔ ∀ s ∈ diamondFin ω Θ, ⟪p, u s⟫ ≤ h s :=
  by
  rw [roofU, Finset.le_inf'_iff]
  exact forall₂_congr fun s hs => le_lineFn_iff (hP.sin_pos hs) _ _


-- @@ L204-210 expanded
lemma lt_roofR_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    p 1 < roofR Θ hP.nonempty h (p 0) ↔
      ∃ t ∈ Θ, ⟪p, u t⟫ < h t - 1 ∧ ⟪p, u (t + π / 2)⟫ < h (t + π / 2) - 1 :=
  by
  rw [roofR, Finset.lt_sup'_iff]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  rw [lt_min_iff, lt_lineFn_iff (hP.sin_pos (mem_diamondFin_of_mem ht)),
    lt_lineFn_iff (hP.sin_pos (add_mem_diamondFin ht))]


-- @@ L212-215 expanded
lemma mem_capH_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    p ∈ capH ω Θ h ↔ (∀ s ∈ fanFin ω, h s - 1 ≤ ⟪p, u s⟫) ∧ ∀ s ∈ diamondFin ω Θ, ⟪p, u s⟫ ≤ h s :=
  and_congr (floorF_le_iff hP) (le_roofU_iff hP)


-- @@ L217-221 expanded
lemma mem_nicheH_iff {h : ℝ → ℝ} {p : EuclideanSpace ℝ (Fin 2)} :
    p ∈ nicheH ω Θ hP.nonempty h ↔
      (∀ s ∈ fanFin ω, h s - 1 ≤ ⟪p, u s⟫) ∧
        ∃ t ∈ Θ, ⟪p, u t⟫ < h t - 1 ∧ ⟪p, u (t + π / 2)⟫ < h (t + π / 2) - 1 :=
  and_congr (floorF_le_iff hP) (lt_roofR_iff hP)


-- @@ L223-225 verbatim
omit hP in
lemma forall_fanFin {P : ℝ → Prop} : (∀ s ∈ fanFin ω, P s) ↔ P ω ∧ P (π / 2) := by
  simp [fanFin]


-- @@ L227-237 verbatim
omit hP in
lemma forall_diamondFin {P : ℝ → Prop} :
    (∀ s ∈ diamondFin ω Θ, P s) ↔
      (∀ t ∈ Θ, P t) ∧ (∀ t ∈ Θ, P (t + π / 2)) ∧ P ω ∧ P (π / 2) := by
  simp only [mem_diamondFin, mem_fanFin]
  constructor
  · intro H
    exact ⟨fun t ht => H t (Or.inl ht), fun t ht => H _ (Or.inr (Or.inl ⟨t, ht, rfl⟩)),
      H ω (Or.inr (Or.inr (Or.inl rfl))), H _ (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨H1, H2, H3, H4⟩ s (hs | ⟨t, ht, rfl⟩ | rfl | rfl)
    exacts [H1 s hs, H2 t ht, H3, H4]


-- @@ L239-239 verbatim
end HalfPlane


-- @@ L241-241 verbatim
/-! ## Identification with the Chapter 2/3 definitions for caps -/


-- @@ L243-243 verbatim
section Caps


-- @@ L245-245 expanded
variable {K : Set (EuclideanSpace ℝ (Fin 2))} (hP : PolySetup ω Θ)


-- @@ L246-246 verbatim
include hP


-- @@ L248-253 verbatim
omit hP in
lemma fan_eq {h : ℝ → ℝ} (h1 : h ω = 1) (h2 : h (π / 2) = 1) :
    fan ω = {p | ∀ s ∈ fanFin ω, h s - 1 ≤ ⟪p, u s⟫} := by
  ext p
  rw [mem_ofPred_eq, forall_fanFin, h1, h2, sub_self, inner_u_pi_div_two]
  exact ⟨fun hp => ⟨hp.2, hp.1⟩, fun hp => ⟨hp.2, hp.1⟩⟩


-- @@ L255-265 verbatim
lemma polyCap_eq_capH (hK : IsCap K ω) : polyCap ω Θ K = capH ω Θ (supportFn K) := by
  ext p
  rw [mem_capH_iff hP, forall_fanFin, forall_diamondFin, hK.supportFn_ω,
    hK.supportFn_pi_div_two, sub_self, inner_u_pi_div_two]
  simp only [polyCap, mem_inter_iff, mem_iInter₂, para, Hstrip, Vstrip, mem_ofPred_eq, QplusS,
    hpLe]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact ⟨⟨h3, h1⟩, fun t ht => (h5 t ht).1, fun t ht => (h5 t ht).2, h4, h2⟩
  · rintro ⟨⟨h3, h1⟩, h5, h6, h4, h2⟩
    exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, fun t ht => ⟨h5 t ht, h6 t ht⟩⟩


-- @@ L267-273 verbatim
lemma polyNiche_eq_nicheH (hK : IsCap K ω) :
    polyNiche ω Θ K = nicheH ω Θ hP.nonempty (supportFn K) := by
  have hfan := fan_eq hK.supportFn_ω hK.supportFn_pi_div_two
  ext p
  rw [mem_nicheH_iff hP]
  simp only [polyNiche, mem_inter_iff, hfan, mem_iUnion₂, QminusS, hpLt, mem_ofPred_eq,
    exists_prop]


-- @@ L275-275 verbatim
end Caps


-- @@ L277-277 verbatim
/-! ## A uniform window containing the supports -/


-- @@ L279-279 verbatim
section Bound


-- @@ L281-281 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L282-282 verbatim
include hP


-- @@ L284-289 verbatim
lemma lineFn_Θ_le {t : ℝ} (ht : Θ.Nonempty → t ∈ Θ) {c K₀ x : ℝ}
    (hx : (c - K₀ * sin t) / cos t ≤ x) : lineFn t c x ≤ K₀ := by
  have ht' := ht hP.nonempty
  rw [div_le_iff₀ (hP.cos_pos_Θ ht')] at hx
  rw [lineFn, div_le_iff₀ (hP.sin_pos_Θ ht')]
  linarith


-- @@ L291-295 verbatim
lemma lineFn_Θ_add_le {t : ℝ} (ht : t ∈ Θ) {c K₀ x : ℝ}
    (hx : (c - K₀ * cos t) / sin t ≤ -x) : lineFn (t + π / 2) c x ≤ K₀ := by
  rw [div_le_iff₀ (hP.sin_pos_Θ ht)] at hx
  rw [lineFn, sin_add_pi_div_two, cos_add_pi_div_two, div_le_iff₀ (hP.cos_pos_Θ ht)]
  linarith


-- @@ L297-348 verbatim
/-- Outside a fixed window `[-M, M]`, all perturbations (by at most `1`) of `h` have
`U ≤ f` and `R ≤ f`. -/
theorem exists_window (h : ℝ → ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ h' : ℝ → ℝ, (∀ s ∈ diamondFin ω Θ, |h' s - h s| ≤ 1) →
      ∀ x, M ≤ |x| → roofU ω Θ h' x ≤ floorF ω h' x ∧
        roofR Θ hP.nonempty h' x ≤ floorF ω h' x := by
  obtain ⟨t₁, ht₁⟩ := hP.nonempty
  set K₀ := h (π / 2) - 2 with hK₀
  set Mp := Θ.sup' hP.nonempty fun t => (h t + 1 - K₀ * sin t) / cos t with hMp
  set Mm := Θ.sup' hP.nonempty fun t => (h (t + π / 2) + 1 - K₀ * cos t) / sin t with hMm
  refine ⟨max (max Mp Mm) 1, lt_max_of_lt_right one_pos, fun h' hh' x hx => ?_⟩
  have hbd : ∀ s ∈ diamondFin ω Θ, h' s ≤ h s + 1 := fun s hs => by
    have := (abs_le.1 (hh' s hs)).2; linarith
  have hfl : K₀ ≤ floorF ω h' x := by
    refine le_trans ?_ (Finset.le_sup' (fun s => lineFn s (h' s - 1) x)
      (pi_div_two_mem_fanFin ω))
    simp only [lineFn, sin_pi_div_two, cos_pi_div_two, mul_zero, sub_zero, div_one]
    have := (abs_le.1 (hh' (π / 2) (mem_diamondFin_of_fan (pi_div_two_mem_fanFin ω)))).1
    rw [hK₀]
    linarith
  have hkey : ∃ s ∈ diamondFin ω Θ, lineFn s (h' s) x ≤ K₀ ∧ ∀ t ∈ Θ,
      min (lineFn t (h' t - 1) x) (lineFn (t + π / 2) (h' (t + π / 2) - 1) x) ≤ K₀ := by
    rcases le_abs'.1 hx with hx | hx
    · -- far left
      have hx' : x ≤ -Mm := by
        have : Mm ≤ max (max Mp Mm) 1 := (le_max_right _ _).trans (le_max_left _ _)
        linarith
      have hM : ∀ t ∈ Θ, (h (t + π / 2) + 1 - K₀ * cos t) / sin t ≤ -x := fun t ht =>
        (Finset.le_sup' (fun t => (h (t + π / 2) + 1 - K₀ * cos t) / sin t) ht).trans
          (by linarith)
      refine ⟨t₁ + π / 2, add_mem_diamondFin ht₁, ?_, fun t ht => ?_⟩
      · refine (lineFn_mono (by rw [sin_add_pi_div_two]; exact hP.cos_pos_Θ ht₁)
          (hbd _ (add_mem_diamondFin ht₁)) x).trans ?_
        exact lineFn_Θ_add_le hP ht₁ (hM t₁ ht₁)
      · refine (min_le_right _ _).trans ((lineFn_mono
          (by rw [sin_add_pi_div_two]; exact hP.cos_pos_Θ ht)
          (by linarith [hbd _ (add_mem_diamondFin ht)] :
            h' (t + π / 2) - 1 ≤ h (t + π / 2) + 1) x).trans ?_)
        exact lineFn_Θ_add_le hP ht (hM t ht)
    · -- far right
      have hx' : Mp ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
      have hM : ∀ t ∈ Θ, (h t + 1 - K₀ * sin t) / cos t ≤ x := fun t ht =>
        (Finset.le_sup' (fun t => (h t + 1 - K₀ * sin t) / cos t) ht).trans hx'
      refine ⟨t₁, mem_diamondFin_of_mem ht₁, ?_, fun t ht => ?_⟩
      · refine (lineFn_mono (hP.sin_pos_Θ ht₁) (hbd _ (mem_diamondFin_of_mem ht₁)) x).trans ?_
        exact lineFn_Θ_le hP (fun _ => ht₁) (hM t₁ ht₁)
      · refine (min_le_left _ _).trans ((lineFn_mono (hP.sin_pos_Θ ht)
          (by linarith [hbd _ (mem_diamondFin_of_mem ht)] : h' t - 1 ≤ h t + 1) x).trans ?_)
        exact lineFn_Θ_le hP (fun _ => ht) (hM t ht)
  obtain ⟨s, hs, hsK, hR⟩ := hkey
  refine ⟨((Finset.inf'_le _ hs).trans hsK).trans hfl, ?_⟩
  exact ((Finset.sup'_le_iff _ _).2 hR).trans hfl


-- @@ L350-352 verbatim
lemma areaIntegrand_eq_zero {h : ℝ → ℝ} {x : ℝ} (hU : roofU ω Θ h x ≤ floorF ω h x)
    (hR : roofR Θ hP.nonempty h x ≤ floorF ω h x) : areaIntegrand ω Θ hP.nonempty h x = 0 := by
  rw [areaIntegrand, max_eq_right (by linarith), max_eq_right (by linarith), sub_self]


-- @@ L354-361 verbatim
omit hP in
lemma hasCompactSupport_posPart {φ : ℝ → ℝ} {M : ℝ} (hM : ∀ x, M ≤ |x| → φ x ≤ 0) :
    HasCompactSupport fun x => max (φ x) 0 := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -M) (b := M)) fun x hx => ?_
  have : M ≤ |x| := by
    by_contra hlt
    exact hx (abs_le.1 (not_le.1 hlt).le)
  exact max_eq_right (hM x this)


-- @@ L363-371 verbatim
lemma integrable_posPart_U (h : ℝ → ℝ) :
    Integrable fun x => max (roofU ω Θ h x - floorF ω h x) 0 := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  refine Continuous.integrable_of_hasCompactSupport (by
    have := continuous_roofU (ω := ω) (Θ := Θ) h
    have := continuous_floorF (ω := ω) h
    fun_prop) (hasCompactSupport_posPart (M := M) fun x hx => ?_)
  have := (hM h (fun s _ => by simp) x hx).1
  linarith


-- @@ L373-381 verbatim
lemma integrable_posPart_R (h : ℝ → ℝ) :
    Integrable fun x => max (roofR Θ hP.nonempty h x - floorF ω h x) 0 := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  refine Continuous.integrable_of_hasCompactSupport (by
    have := continuous_roofR hP.nonempty h
    have := continuous_floorF (ω := ω) h
    fun_prop) (hasCompactSupport_posPart (M := M) fun x hx => ?_)
  have := (hM h (fun s _ => by simp) x hx).2
  linarith


-- @@ L383-386 verbatim
lemma measureReal_capH (h : ℝ → ℝ) :
    volume.real (capH ω Θ h) = ∫ x, max (roofU ω Θ h x - floorF ω h x) 0 :=
  measureReal_between_Icc (continuous_floorF h).measurable (continuous_roofU h).measurable
    (integrable_posPart_U hP h)


-- @@ L388-392 verbatim
lemma measureReal_nicheH (h : ℝ → ℝ) :
    volume.real (nicheH ω Θ hP.nonempty h) =
      ∫ x, max (roofR Θ hP.nonempty h x - floorF ω h x) 0 :=
  measureReal_between_Ico (continuous_floorF h).measurable
    (continuous_roofR hP.nonempty h).measurable (integrable_posPart_R hP h)


-- @@ L394-399 verbatim
theorem areaH_eq (h : ℝ → ℝ) :
    areaH ω Θ hP.nonempty h =
      volume.real (capH ω Θ h) - volume.real (nicheH ω Θ hP.nonempty h) := by
  rw [measureReal_capH hP, measureReal_nicheH hP, areaH, ← integral_sub
    (integrable_posPart_U hP h) (integrable_posPart_R hP h)]
  rfl


-- @@ L401-404 expanded
theorem polySofaArea_eq_areaH {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCap K ω) :
    polySofaArea ω Θ K = areaH ω Θ hP.nonempty (supportFn K) :=
  by
  rw [areaH_eq hP, ← polyCap_eq_capH hP hK, ← polyNiche_eq_nicheH hP hK, polySofaArea]
  rfl


-- @@ L406-406 verbatim
end Bound


-- @@ L408-408 verbatim
/-! ## Pushing one support value -/


-- @@ L410-411 verbatim
/-- `h` with its value at `t` raised by `ε`. -/
def pushH (h : ℝ → ℝ) (t ε : ℝ) : ℝ → ℝ := Function.update h t (h t + ε)


-- @@ L413-417 verbatim
lemma pushH_apply (h : ℝ → ℝ) (t ε s : ℝ) :
    pushH h t ε s = h s + if s = t then ε else 0 := by
  by_cases hs : s = t
  · subst hs; simp [pushH]
  · simp [pushH, hs]


-- @@ L419-420 verbatim
@[simp] lemma pushH_zero (h : ℝ → ℝ) (t : ℝ) : pushH h t 0 = h := by
  simp [pushH]


-- @@ L422-425 verbatim
lemma abs_pushH_sub_pushH (h : ℝ → ℝ) (t ε ε' s : ℝ) :
    |pushH h t ε s - pushH h t ε' s| ≤ |ε - ε'| := by
  rw [pushH_apply, pushH_apply]
  split_ifs <;> simp


-- @@ L427-428 verbatim
lemma abs_pushH_sub (h : ℝ → ℝ) (t ε s : ℝ) : |pushH h t ε s - h s| ≤ |ε| := by
  simpa using abs_pushH_sub_pushH h t ε 0 s


-- @@ L430-430 verbatim
/-! ### The combined line family and its tie set -/


-- @@ L432-433 verbatim
/-- Offsets of the combined family `ℓ_{s, h(s) - k}` (`s ∈ Θ^⋄`, `k ∈ {0, 1}`). -/
def famA (h : ℝ → ℝ) (q : ℝ × ℕ) : ℝ := (h q.1 - q.2) / sin q.1


-- @@ L435-436 verbatim
/-- Slopes of the combined family. -/
def famB (q : ℝ × ℕ) : ℝ := -(cos q.1 / sin q.1)


-- @@ L438-440 verbatim
variable (ω Θ) in
/-- Index set of the combined family. -/
def famS : Finset (ℝ × ℕ) := diamondFin ω Θ ×ˢ {0, 1}


-- @@ L442-444 verbatim
variable (ω Θ) in
/-- The tie set of all defining lines of `C_Θ(h)` and `N_Θ(h)`. -/
def tieAll (h : ℝ → ℝ) : Set ℝ := tieSet (famS ω Θ) (famA h) famB


-- @@ L446-448 verbatim
lemma famA_add_famB (h : ℝ → ℝ) (s : ℝ) (k : ℕ) (x : ℝ) :
    famA h (s, k) + famB (s, k) * x = lineFn s (h s - k) x := by
  simp only [famA, famB, lineFn]; ring


-- @@ L450-454 verbatim
lemma mem_famS {s : ℝ} {k : ℕ} : (s, k) ∈ famS ω Θ ↔ s ∈ diamondFin ω Θ ∧ k ≤ 1 := by
  simp only [famS, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩


-- @@ L456-456 verbatim
section Ties


-- @@ L458-458 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L459-459 verbatim
include hP


-- @@ L461-474 verbatim
lemma affDistinct_fam (h : ℝ → ℝ) : AffDistinct (famS ω Θ) (famA h) famB := by
  rintro ⟨s, k⟩ hq ⟨s', k'⟩ hq' hne
  rw [mem_famS] at hq hq'
  by_cases hss : s = s'
  · subst hss
    left
    have hk : k ≠ k' := fun hk => hne (by rw [hk])
    simp only [famA]
    intro heq
    rw [div_left_inj' (hP.sin_pos hq.1).ne'] at heq
    exact hk (by exact_mod_cast (by linarith : (k : ℝ) = k'))
  · right
    simp only [famB]
    exact fun h => hss (hP.cot_injOn hq.1 hq'.1 (neg_inj.1 h))


-- @@ L476-477 verbatim
lemma tieAll_finite (h : ℝ → ℝ) : (tieAll ω Θ h).Finite :=
  tieSet_finite (affDistinct_fam hP h)


-- @@ L479-480 verbatim
lemma volume_tieAll (h : ℝ → ℝ) : volume (tieAll ω Θ h) = 0 :=
  (tieAll_finite hP h).measure_zero volume


-- @@ L482-482 verbatim
variable {h : ℝ → ℝ} {x : ℝ}


-- @@ L484-496 verbatim
omit hP in
lemma lineFn_ne (hx : x ∉ tieAll ω Θ h) {s s' : ℝ} (hs : s ∈ diamondFin ω Θ)
    (hs' : s' ∈ diamondFin ω Θ) {k k' : ℕ} (hk : k ≤ 1) (hk' : k' ≤ 1) (hne : s ≠ s' ∨ k ≠ k') :
    lineFn s (h s - k) x ≠ lineFn s' (h s' - k') x := by
  intro heq
  refine hx ⟨(s, k), mem_famS.2 ⟨hs, hk⟩, (s', k'), mem_famS.2 ⟨hs', hk'⟩, ?_, ?_⟩
  · intro hq
    simp only [Prod.mk.injEq] at hq
    rcases hne with hne | hne
    · exact hne hq.1
    · exact hne hq.2
  · rw [famA_add_famB, famA_add_famB]
    exact heq


-- @@ L498-501 verbatim
omit hP in
lemma lineFn_ne_00 (hx : x ∉ tieAll ω Θ h) {s s' : ℝ} (hs : s ∈ diamondFin ω Θ)
    (hs' : s' ∈ diamondFin ω Θ) (hne : s ≠ s') : lineFn s (h s) x ≠ lineFn s' (h s') x := by
  simpa using lineFn_ne hx hs hs' (k := 0) (k' := 0) (by omega) (by omega) (Or.inl hne)


-- @@ L503-507 verbatim
omit hP in
lemma lineFn_ne_11 (hx : x ∉ tieAll ω Θ h) {s s' : ℝ} (hs : s ∈ diamondFin ω Θ)
    (hs' : s' ∈ diamondFin ω Θ) (hne : s ≠ s') :
    lineFn s (h s - 1) x ≠ lineFn s' (h s' - 1) x := by
  simpa using lineFn_ne hx hs hs' (k := 1) (k' := 1) le_rfl le_rfl (Or.inl hne)


-- @@ L509-512 verbatim
omit hP in
lemma lineFn_ne_01 (hx : x ∉ tieAll ω Θ h) {s s' : ℝ} (hs : s ∈ diamondFin ω Θ)
    (hs' : s' ∈ diamondFin ω Θ) : lineFn s (h s) x ≠ lineFn s' (h s' - 1) x := by
  simpa using lineFn_ne hx hs hs' (k := 0) (k' := 1) (by omega) le_rfl (Or.inr (by omega))


-- @@ L514-514 verbatim
end Ties


-- @@ L516-516 verbatim
/-! ### Each graph selects one line -/


-- @@ L518-520 verbatim
lemma roofU_mem (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ diamondFin ω Θ, roofU ω Θ h x = lineFn s (h s) x :=
  (diamondFin ω Θ).exists_mem_eq_inf' (diamondFin_nonempty ω Θ) fun s => lineFn s (h s) x


-- @@ L522-524 verbatim
lemma floorF_mem (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ fanFin ω, floorF ω h x = lineFn s (h s - 1) x :=
  (fanFin ω).exists_mem_eq_sup' (fanFin_nonempty ω) fun s => lineFn s (h s - 1) x


-- @@ L526-533 verbatim
lemma roofR_mem (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (x : ℝ) :
    ∃ t ∈ Θ, ∃ r, (r = t ∨ r = t + π / 2) ∧ roofR Θ hΘ h x = lineFn r (h r - 1) x := by
  obtain ⟨t, ht, he⟩ := Θ.exists_mem_eq_sup' hΘ
    fun t => min (lineFn t (h t - 1) x) (lineFn (t + π / 2) (h (t + π / 2) - 1) x)
  refine ⟨t, ht, ?_⟩
  rcases min_choice (lineFn t (h t - 1) x) (lineFn (t + π / 2) (h (t + π / 2) - 1) x) with hm | hm
  · exact ⟨t, Or.inl rfl, he.trans hm⟩
  · exact ⟨t + π / 2, Or.inr rfl, he.trans hm⟩


-- @@ L535-540 verbatim
lemma roofR_mem' (hP : PolySetup ω Θ) (h : ℝ → ℝ) (x : ℝ) :
    ∃ r ∈ diamondFin ω Θ, r ∉ fanFin ω ∧ roofR Θ hP.nonempty h x = lineFn r (h r - 1) x := by
  obtain ⟨t, ht, r, hr, he⟩ := roofR_mem hP.nonempty h x
  rcases hr with rfl | rfl
  · exact ⟨_, mem_diamondFin_of_mem ht, fun hs => hP.ne_fan ht hs rfl, he⟩
  · exact ⟨_, add_mem_diamondFin ht, fun hs => hP.add_ne_fan ht hs rfl, he⟩


-- @@ L542-542 verbatim
/-! ### Active sets, `σ` and `τ` -/


-- @@ L544-546 verbatim
variable (ω Θ) in
/-- Where the cap roof uses the line with normal `t`. -/
def actU (h : ℝ → ℝ) (t : ℝ) : Set ℝ := {x | roofU ω Θ h x = lineFn t (h t) x}


-- @@ L548-550 verbatim
variable (ω) in
/-- Where the fan floor uses the line with normal `t`. -/
def actF (h : ℝ → ℝ) (t : ℝ) : Set ℝ := {x | floorF ω h x = lineFn t (h t - 1) x}


-- @@ L552-555 verbatim
variable (Θ) in
/-- Where the niche roof uses the line with normal `t`. -/
def actR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  {x | roofR Θ hΘ h x = lineFn t (h t - 1) x}


-- @@ L557-559 verbatim
variable (ω Θ) in
/-- `I = {f < U}`: the projection of the (open) cap. -/
def posU (h : ℝ → ℝ) : Set ℝ := {x | floorF ω h x < roofU ω Θ h x}


-- @@ L561-563 verbatim
variable (ω Θ) in
/-- `J = {f < R}`: the projection of the niche. -/
def posR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : Set ℝ := {x | floorF ω h x < roofR Θ hΘ h x}


-- @@ L565-567 verbatim
variable (ω Θ) in
/-- `σ(t)`: the length of the cap edge with normal `t` (`|{x ∈ I : U = ℓ_t}| / sin t`). -/
def sigmaH (h : ℝ → ℝ) (t : ℝ) : ℝ := volume.real (actU ω Θ h t ∩ posU ω Θ h) / sin t


-- @@ L569-573 verbatim
variable (ω Θ) in
/-- `τ(t)`: the total length of the edges of the niche polyline with normal `t`. -/
def tauH (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  (volume.real (actR Θ hΘ h t ∩ posR ω Θ hΘ h) + volume.real (actF ω h t ∩ posU ω Θ h) -
    volume.real (actF ω h t ∩ posR ω Θ hΘ h)) / sin t


-- @@ L575-581 verbatim
variable (ω Θ) in
/-- The `ε`-derivative of `areaIntegrand` (see `hasDerivAt_areaIntegrand_push`). -/
def dIntegrand (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (posU ω Θ h).indicator (fun x => (actU ω Θ h t).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t).indicator (fun _ => (sin t)⁻¹) x) x -
    (posR ω Θ hΘ h).indicator (fun x => (actR Θ hΘ h t).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t).indicator (fun _ => (sin t)⁻¹) x) x


-- @@ L583-584 verbatim
lemma isOpen_posU (h : ℝ → ℝ) : IsOpen (posU ω Θ h) :=
  isOpen_lt (continuous_floorF h) (continuous_roofU h)


-- @@ L586-587 verbatim
lemma isOpen_posR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : IsOpen (posR ω Θ hΘ h) :=
  isOpen_lt (continuous_floorF h) (continuous_roofR hΘ h)


-- @@ L589-590 verbatim
lemma isClosed_actU (h : ℝ → ℝ) (t : ℝ) : IsClosed (actU ω Θ h t) :=
  isClosed_eq (continuous_roofU h) (continuous_lineFn _ _)


-- @@ L592-593 verbatim
lemma isClosed_actF (h : ℝ → ℝ) (t : ℝ) : IsClosed (actF ω h t) :=
  isClosed_eq (continuous_floorF h) (continuous_lineFn _ _)


-- @@ L595-596 verbatim
lemma isClosed_actR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t : ℝ) : IsClosed (actR Θ hΘ h t) :=
  isClosed_eq (continuous_roofR hΘ h) (continuous_lineFn _ _)


-- @@ L598-598 verbatim
/-! ### Differentiating the graphs in `ε` -/


-- @@ L600-601 verbatim
/-- Offsets of the combined family, as affine functions of `ε` at a fixed `x`. -/
def epsA (h : ℝ → ℝ) (x : ℝ) (q : ℝ × ℕ) : ℝ := lineFn q.1 (h q.1 - q.2) x


-- @@ L603-604 verbatim
/-- Slopes in `ε` of the combined family. -/
def epsB (t : ℝ) (q : ℝ × ℕ) : ℝ := if q.1 = t then (sin q.1)⁻¹ else 0


-- @@ L606-609 verbatim
lemma lineFn_pushH_eq (h : ℝ → ℝ) (t ε x s : ℝ) (k : ℕ) :
    lineFn s (pushH h t ε s - k) x = epsA h x (s, k) + epsB t (s, k) * ε := by
  simp only [epsA, epsB, pushH_apply]
  split_ifs <;> simp only [lineFn] <;> ring


-- @@ L611-619 verbatim
lemma continuous_lineFn_pushH (h : ℝ → ℝ) (t x s c : ℝ) :
    Continuous fun ε => lineFn s (pushH h t ε s - c) x := by
  have e : (fun ε => lineFn s (pushH h t ε s - c) x) =
      fun ε => lineFn s (h s - c) x + (if s = t then (sin s)⁻¹ else 0) * ε := by
    funext ε
    simp only [pushH_apply]
    split_ifs <;> simp only [lineFn] <;> ring
  rw [e]
  fun_prop


-- @@ L621-624 verbatim
lemma continuous_roofU_push (h : ℝ → ℝ) (t x : ℝ) :
    Continuous fun ε => roofU ω Θ (pushH h t ε) x :=
  Continuous.finset_inf'_apply (diamondFin_nonempty ω Θ) fun s _ => by
    simpa using continuous_lineFn_pushH h t x s 0


-- @@ L626-628 verbatim
lemma continuous_floorF_push (h : ℝ → ℝ) (t x : ℝ) :
    Continuous fun ε => floorF ω (pushH h t ε) x :=
  Continuous.finset_sup'_apply (fanFin_nonempty ω) fun s _ => continuous_lineFn_pushH h t x s 1


-- @@ L630-633 verbatim
lemma continuous_roofR_push (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t x : ℝ) :
    Continuous fun ε => roofR Θ hΘ (pushH h t ε) x :=
  Continuous.finset_sup'_apply hΘ fun τ _ =>
    (continuous_lineFn_pushH h t x τ 1).min (continuous_lineFn_pushH h t x (τ + π / 2) 1)


-- @@ L635-635 verbatim
section DerivEps


-- @@ L637-637 verbatim
variable (hP : PolySetup ω Θ) {h : ℝ → ℝ} {t x : ℝ}

-- @@ L638-638 verbatim
include hP


-- @@ L640-648 verbatim
omit hP in
lemma zero_not_mem_tieSet_eps (hx : x ∉ tieAll ω Θ h) :
    (0 : ℝ) ∉ tieSet (famS ω Θ) (epsA h x) (epsB t) := by
  rintro ⟨⟨s, k⟩, hq, ⟨s', k'⟩, hq', hne, heq⟩
  apply hx
  refine ⟨(s, k), hq, (s', k'), hq', hne, ?_⟩
  simp only [mul_zero, add_zero, epsA] at heq
  rw [famA_add_famB, famA_add_famB]
  exact heq


-- @@ L650-658 verbatim
omit hP in
lemma selU (h : ℝ → ℝ) (t x : ℝ) : ∀ ε, ∃ q ∈ famS ω Θ,
    ε ∈ activeSet (fun ε => roofU ω Θ (pushH h t ε) x) (epsA h x) (epsB t) q := by
  intro ε
  obtain ⟨s, hs, he⟩ := roofU_mem (ω := ω) (Θ := Θ) (pushH h t ε) x
  refine ⟨(s, 0), mem_famS.2 ⟨hs, Nat.zero_le _⟩, ?_⟩
  show roofU ω Θ (pushH h t ε) x = epsA h x (s, 0) + epsB t (s, 0) * ε
  rw [← lineFn_pushH_eq, he]
  simp


-- @@ L660-668 verbatim
omit hP in
lemma selF (h : ℝ → ℝ) (t x : ℝ) : ∀ ε, ∃ q ∈ famS ω Θ,
    ε ∈ activeSet (fun ε => floorF ω (pushH h t ε) x) (epsA h x) (epsB t) q := by
  intro ε
  obtain ⟨s, hs, he⟩ := floorF_mem (ω := ω) (pushH h t ε) x
  refine ⟨(s, 1), mem_famS.2 ⟨mem_diamondFin_of_fan hs, le_rfl⟩, ?_⟩
  show floorF ω (pushH h t ε) x = epsA h x (s, 1) + epsB t (s, 1) * ε
  rw [← lineFn_pushH_eq, he]
  simp


-- @@ L670-677 verbatim
lemma selR (h : ℝ → ℝ) (t x : ℝ) : ∀ ε, ∃ q ∈ famS ω Θ,
    ε ∈ activeSet (fun ε => roofR Θ hP.nonempty (pushH h t ε) x) (epsA h x) (epsB t) q := by
  intro ε
  obtain ⟨r, hr, -, he⟩ := roofR_mem' hP (pushH h t ε) x
  refine ⟨(r, 1), mem_famS.2 ⟨hr, le_rfl⟩, ?_⟩
  show roofR Θ hP.nonempty (pushH h t ε) x = epsA h x (r, 1) + epsB t (r, 1) * ε
  rw [← lineFn_pushH_eq, he]
  simp


-- @@ L679-697 verbatim
omit hP in
lemma hasDerivAt_roofU_push (ht : t ∈ diamondFin ω Θ) (hx : x ∉ tieAll ω Θ h) :
    HasDerivAt (fun ε => roofU ω Θ (pushH h t ε) x)
      ((actU ω Θ h t).indicator (fun _ => (sin t)⁻¹) x) 0 := by
  obtain ⟨s₀, hs₀, he⟩ := roofU_mem (ω := ω) (Θ := Θ) h x
  have hact : (0 : ℝ) ∈ activeSet (fun ε => roofU ω Θ (pushH h t ε) x) (epsA h x) (epsB t)
      (s₀, 0) := by
    show roofU ω Θ (pushH h t 0) x = epsA h x (s₀, 0) + epsB t (s₀, 0) * 0
    simp [he, epsA]
  have hd := hasDerivAt_of_selection (continuous_roofU_push h t x) (selU h t x)
    (zero_not_mem_tieSet_eps hx) (mem_famS.2 ⟨hs₀, Nat.zero_le _⟩) hact
  convert hd using 1
  simp only [epsB]
  by_cases hst : s₀ = t
  · subst hst
    rw [if_pos rfl, indicator_of_mem (show x ∈ actU ω Θ h s₀ from he)]
  · rw [if_neg hst, indicator_of_notMem]
    intro hxt
    exact lineFn_ne_00 hx hs₀ ht hst (he.symm.trans hxt)


-- @@ L699-717 verbatim
omit hP in
lemma hasDerivAt_floorF_push (ht : t ∈ diamondFin ω Θ) (hx : x ∉ tieAll ω Θ h) :
    HasDerivAt (fun ε => floorF ω (pushH h t ε) x)
      ((actF ω h t).indicator (fun _ => (sin t)⁻¹) x) 0 := by
  obtain ⟨s₀, hs₀, he⟩ := floorF_mem (ω := ω) h x
  have hact : (0 : ℝ) ∈ activeSet (fun ε => floorF ω (pushH h t ε) x) (epsA h x) (epsB t)
      (s₀, 1) := by
    show floorF ω (pushH h t 0) x = epsA h x (s₀, 1) + epsB t (s₀, 1) * 0
    simp [he, epsA]
  have hd := hasDerivAt_of_selection (continuous_floorF_push h t x) (selF (Θ := Θ) h t x)
    (zero_not_mem_tieSet_eps hx) (mem_famS.2 ⟨mem_diamondFin_of_fan hs₀, le_rfl⟩) hact
  convert hd using 1
  simp only [epsB]
  by_cases hst : s₀ = t
  · subst hst
    rw [if_pos rfl, indicator_of_mem (show x ∈ actF ω h s₀ from he)]
  · rw [if_neg hst, indicator_of_notMem]
    intro hxt
    exact lineFn_ne_11 hx (mem_diamondFin_of_fan hs₀) ht hst (he.symm.trans hxt)


-- @@ L719-736 verbatim
lemma hasDerivAt_roofR_push (ht : t ∈ diamondFin ω Θ) (hx : x ∉ tieAll ω Θ h) :
    HasDerivAt (fun ε => roofR Θ hP.nonempty (pushH h t ε) x)
      ((actR Θ hP.nonempty h t).indicator (fun _ => (sin t)⁻¹) x) 0 := by
  obtain ⟨r₀, hr₀, -, he⟩ := roofR_mem' hP h x
  have hact : (0 : ℝ) ∈ activeSet (fun ε => roofR Θ hP.nonempty (pushH h t ε) x) (epsA h x)
      (epsB t) (r₀, 1) := by
    show roofR Θ hP.nonempty (pushH h t 0) x = epsA h x (r₀, 1) + epsB t (r₀, 1) * 0
    simp [he, epsA]
  have hd := hasDerivAt_of_selection (continuous_roofR_push hP.nonempty h t x) (selR hP h t x)
    (zero_not_mem_tieSet_eps hx) (mem_famS.2 ⟨hr₀, le_rfl⟩) hact
  convert hd using 1
  simp only [epsB]
  by_cases hst : r₀ = t
  · subst hst
    rw [if_pos rfl, indicator_of_mem (show x ∈ actR Θ hP.nonempty h r₀ from he)]
  · rw [if_neg hst, indicator_of_notMem]
    intro hxt
    exact lineFn_ne_11 hx hr₀ ht hst (he.symm.trans hxt)


-- @@ L738-743 verbatim
omit hP in
lemma roofU_ne_floorF (hx : x ∉ tieAll ω Θ h) : roofU ω Θ h x ≠ floorF ω h x := by
  obtain ⟨s₀, hs₀, he⟩ := roofU_mem (ω := ω) (Θ := Θ) h x
  obtain ⟨σ₀, hσ₀, hf⟩ := floorF_mem (ω := ω) h x
  rw [he, hf]
  exact lineFn_ne_01 hx hs₀ (mem_diamondFin_of_fan hσ₀)


-- @@ L745-749 verbatim
lemma roofR_ne_floorF (hx : x ∉ tieAll ω Θ h) : roofR Θ hP.nonempty h x ≠ floorF ω h x := by
  obtain ⟨r₀, hr₀, hr₀f, he⟩ := roofR_mem' hP h x
  obtain ⟨σ₀, hσ₀, hf⟩ := floorF_mem (ω := ω) h x
  rw [he, hf]
  exact lineFn_ne_11 hx hr₀ (mem_diamondFin_of_fan hσ₀) fun h => hr₀f (h ▸ hσ₀)


-- @@ L751-777 verbatim
/-- The pointwise `ε`-derivative of the area integrand off the tie set. -/
theorem hasDerivAt_areaIntegrand_push (ht : t ∈ diamondFin ω Θ) (hx : x ∉ tieAll ω Θ h) :
    HasDerivAt (fun ε => areaIntegrand ω Θ hP.nonempty (pushH h t ε) x)
      (dIntegrand ω Θ hP.nonempty h t x) 0 := by
  have hU := hasDerivAt_roofU_push ht hx
  have hF := hasDerivAt_floorF_push ht hx
  have hR := hasDerivAt_roofR_push hP ht hx
  have h1 : HasDerivAt (fun ε => max (roofU ω Θ (pushH h t ε) x - floorF ω (pushH h t ε) x) 0)
      ((posU ω Θ h).indicator (fun x => (actU ω Θ h t).indicator (fun _ => (sin t)⁻¹) x -
        (actF ω h t).indicator (fun _ => (sin t)⁻¹) x) x) 0 := by
    rcases lt_or_gt_of_ne (roofU_ne_floorF hx) with hlt | hlt
    · rw [indicator_of_notMem (show x ∉ posU ω Θ h from fun h' => (lt_asymm hlt) h')]
      exact hasDerivAt_max_zero_of_neg (hU.sub hF) (by simpa using hlt)
    · rw [indicator_of_mem (show x ∈ posU ω Θ h from hlt)]
      exact hasDerivAt_max_zero_of_pos (hU.sub hF) (by simpa using hlt)
  have h2 : HasDerivAt
      (fun ε => max (roofR Θ hP.nonempty (pushH h t ε) x - floorF ω (pushH h t ε) x) 0)
      ((posR ω Θ hP.nonempty h).indicator
        (fun x => (actR Θ hP.nonempty h t).indicator (fun _ => (sin t)⁻¹) x -
          (actF ω h t).indicator (fun _ => (sin t)⁻¹) x) x) 0 := by
    rcases lt_or_gt_of_ne (roofR_ne_floorF hP hx) with hlt | hlt
    · rw [indicator_of_notMem (show x ∉ posR ω Θ hP.nonempty h from
        fun h' => (lt_asymm hlt) h')]
      exact hasDerivAt_max_zero_of_neg (hR.sub hF) (by simpa using hlt)
    · rw [indicator_of_mem (show x ∈ posR ω Θ hP.nonempty h from hlt)]
      exact hasDerivAt_max_zero_of_pos (hR.sub hF) (by simpa using hlt)
  exact h1.sub h2


-- @@ L779-779 verbatim
end DerivEps


-- @@ L781-781 verbatim
/-! ### The derivative of `A_Θ` (G2) -/


-- @@ L783-783 verbatim
section DerivArea


-- @@ L785-785 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L786-786 verbatim
include hP


-- @@ L788-798 verbatim
lemma abs_lineFn_push_sub {h : ℝ → ℝ} {t s : ℝ} (ht : t ∈ diamondFin ω Θ)
    (hs : s ∈ diamondFin ω Θ) (c ε ε' x : ℝ) :
    |lineFn s (pushH h t ε s - c) x - lineFn s (pushH h t ε' s - c) x| ≤ |ε - ε'| / sin t := by
  rw [abs_lineFn_sub_lineFn (hP.sin_pos hs), pushH_apply, pushH_apply]
  by_cases hst : s = t
  · subst hst
    simp only [if_true]
    rw [show h s + ε - c - (h s + ε' - c) = ε - ε' by ring]
  · simp only [hst, if_false]
    rw [show h s + 0 - c - (h s + 0 - c) = 0 by ring, abs_zero, zero_div]
    exact div_nonneg (abs_nonneg _) (hP.sin_pos ht).le


-- @@ L800-843 verbatim
theorem abs_areaIntegrand_push_sub (h : ℝ → ℝ) {t : ℝ} (ht : t ∈ diamondFin ω Θ)
    (ε ε' x : ℝ) :
    |areaIntegrand ω Θ hP.nonempty (pushH h t ε) x -
        areaIntegrand ω Θ hP.nonempty (pushH h t ε') x| ≤ 4 / sin t * |ε - ε'| := by
  set c := |ε - ε'| / sin t with hc
  have hc0 : 0 ≤ c := div_nonneg (abs_nonneg _) (hP.sin_pos ht).le
  have hU : |roofU ω Θ (pushH h t ε) x - roofU ω Θ (pushH h t ε') x| ≤ c :=
    abs_inf'_sub_inf'_le _ fun s hs => by
      simpa using abs_lineFn_push_sub hP (h := h) ht hs 0 ε ε' x
  have hF : |floorF ω (pushH h t ε) x - floorF ω (pushH h t ε') x| ≤ c :=
    abs_sup'_sub_sup'_le _ fun s hs => abs_lineFn_push_sub hP ht (mem_diamondFin_of_fan hs) 1 ε ε' x
  have hR : |roofR Θ hP.nonempty (pushH h t ε) x - roofR Θ hP.nonempty (pushH h t ε') x| ≤ c :=
    abs_sup'_sub_sup'_le _ fun τ hτ =>
      (abs_min_sub_min_le_max _ _ _ _).trans (max_le
        (abs_lineFn_push_sub hP ht (mem_diamondFin_of_mem hτ) 1 ε ε' x)
        (abs_lineFn_push_sub hP ht (add_mem_diamondFin hτ) 1 ε ε' x))
  have h1 := abs_max_sub_max_le_abs (roofU ω Θ (pushH h t ε) x - floorF ω (pushH h t ε) x)
    (roofU ω Θ (pushH h t ε') x - floorF ω (pushH h t ε') x) 0
  have h2 := abs_max_sub_max_le_abs
    (roofR Θ hP.nonempty (pushH h t ε) x - floorF ω (pushH h t ε) x)
    (roofR Θ hP.nonempty (pushH h t ε') x - floorF ω (pushH h t ε') x) 0
  have h3 : 4 / sin t * |ε - ε'| = 4 * c := by rw [hc]; ring
  rw [h3]
  unfold areaIntegrand
  have e1 : |roofU ω Θ (pushH h t ε) x - floorF ω (pushH h t ε) x -
      (roofU ω Θ (pushH h t ε') x - floorF ω (pushH h t ε') x)| ≤ 2 * c := by
    rw [show roofU ω Θ (pushH h t ε) x - floorF ω (pushH h t ε) x -
      (roofU ω Θ (pushH h t ε') x - floorF ω (pushH h t ε') x) =
      (roofU ω Θ (pushH h t ε) x - roofU ω Θ (pushH h t ε') x) -
      (floorF ω (pushH h t ε) x - floorF ω (pushH h t ε') x) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have e2 : |roofR Θ hP.nonempty (pushH h t ε) x - floorF ω (pushH h t ε) x -
      (roofR Θ hP.nonempty (pushH h t ε') x - floorF ω (pushH h t ε') x)| ≤ 2 * c := by
    rw [show roofR Θ hP.nonempty (pushH h t ε) x - floorF ω (pushH h t ε) x -
      (roofR Θ hP.nonempty (pushH h t ε') x - floorF ω (pushH h t ε') x) =
      (roofR Θ hP.nonempty (pushH h t ε) x - roofR Θ hP.nonempty (pushH h t ε') x) -
      (floorF ω (pushH h t ε) x - floorF ω (pushH h t ε') x) by ring]
    exact (abs_sub _ _).trans (by linarith)
  set A := max (roofU ω Θ (pushH h t ε) x - floorF ω (pushH h t ε) x) 0
  set A' := max (roofU ω Θ (pushH h t ε') x - floorF ω (pushH h t ε') x) 0
  set B := max (roofR Θ hP.nonempty (pushH h t ε) x - floorF ω (pushH h t ε) x) 0
  set B' := max (roofR Θ hP.nonempty (pushH h t ε') x - floorF ω (pushH h t ε') x) 0
  rw [show A - B - (A' - B') = (A - A') - (B - B') by ring]
  exact (abs_sub _ _).trans (by linarith)


-- @@ L845-853 verbatim
omit hP in
lemma posU_subset_window {h : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, M ≤ |x| → roofU ω Θ h x ≤ floorF ω h x) : posU ω Θ h ⊆ Icc (-M) M := by
  intro x hx
  by_contra hxM
  have : M ≤ |x| := by
    by_contra hlt
    exact hxM (abs_le.1 (not_le.1 hlt).le)
  exact (not_lt.2 (hM x this)) hx


-- @@ L855-863 verbatim
lemma posR_subset_window {h : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, M ≤ |x| → roofR Θ hP.nonempty h x ≤ floorF ω h x) :
    posR ω Θ hP.nonempty h ⊆ Icc (-M) M := by
  intro x hx
  by_contra hxM
  have : M ≤ |x| := by
    by_contra hlt
    exact hxM (abs_le.1 (not_le.1 hlt).le)
  exact (not_lt.2 (hM x this)) hx


-- @@ L865-882 verbatim
omit hP in
lemma indicator_sub_indicator (S A B : Set ℝ) (c : ℝ) :
    S.indicator (fun x => A.indicator (fun _ => c) x - B.indicator (fun _ => c) x) =
      fun x => (A ∩ S).indicator (fun _ => c) x - (B ∩ S).indicator (fun _ => c) x := by
  funext x
  by_cases hS : x ∈ S
  · rw [indicator_of_mem hS]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B
    · rw [indicator_of_mem hA, indicator_of_mem hB, indicator_of_mem (show x ∈ A ∩ S from ⟨hA, hS⟩),
        indicator_of_mem (show x ∈ B ∩ S from ⟨hB, hS⟩)]
    · rw [indicator_of_mem hA, indicator_of_notMem hB, indicator_of_mem (show x ∈ A ∩ S from ⟨hA, hS⟩),
        indicator_of_notMem (fun hc => hB hc.1)]
    · rw [indicator_of_notMem hA, indicator_of_mem hB, indicator_of_notMem (fun hc => hA hc.1),
        indicator_of_mem (show x ∈ B ∩ S from ⟨hB, hS⟩)]
    · rw [indicator_of_notMem hA, indicator_of_notMem hB,
        indicator_of_notMem (fun hc => hA hc.1), indicator_of_notMem (fun hc => hB hc.1)]
  · rw [indicator_of_notMem hS, indicator_of_notMem (fun hc => hS hc.2),
      indicator_of_notMem (fun hc => hS hc.2), sub_self]


-- @@ L884-894 verbatim
lemma dIntegrand_eq (h : ℝ → ℝ) (t : ℝ) :
    dIntegrand ω Θ hP.nonempty h t = fun x =>
      (actU ω Θ h t ∩ posU ω Θ h).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t ∩ posU ω Θ h).indicator (fun _ => (sin t)⁻¹) x -
      ((actR Θ hP.nonempty h t ∩ posR ω Θ hP.nonempty h).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t ∩ posR ω Θ hP.nonempty h).indicator (fun _ => (sin t)⁻¹) x) := by
  funext x
  simp only [dIntegrand]
  rw [indicator_sub_indicator (posU ω Θ h) (actU ω Θ h t) (actF ω h t) ((sin t)⁻¹),
    indicator_sub_indicator (posR ω Θ hP.nonempty h) (actR Θ hP.nonempty h t) (actF ω h t)
      ((sin t)⁻¹)]


-- @@ L896-928 verbatim
theorem integral_dIntegrand (h : ℝ → ℝ) (t : ℝ) :
    ∫ x, dIntegrand ω Θ hP.nonempty h t x = sigmaH ω Θ h t - tauH ω Θ hP.nonempty h t := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  have hM' := hM h (fun s _ => by simp)
  have hU := posU_subset_window fun x hx => (hM' x hx).1
  have hR := posR_subset_window hP fun x hx => (hM' x hx).2
  have hfin : ∀ {A B : Set ℝ}, B ⊆ Icc (-M) M → volume (A ∩ B) ≠ ⊤ := fun hB =>
    ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono (inter_subset_right.trans hB))
  have hmU := (isOpen_posU (ω := ω) (Θ := Θ) h).measurableSet
  have hmR := (isOpen_posR (ω := ω) hP.nonempty h).measurableSet
  have hm1 := ((isClosed_actU (ω := ω) (Θ := Θ) h t).measurableSet).inter hmU
  have hm2 := ((isClosed_actF (ω := ω) h t).measurableSet).inter hmU
  have hm3 := ((isClosed_actR hP.nonempty h t).measurableSet).inter hmR
  have hm4 := ((isClosed_actF (ω := ω) h t).measurableSet).inter hmR
  have hi : ∀ {S : Set ℝ}, MeasurableSet S → volume S ≠ ⊤ →
      Integrable (S.indicator fun _ => (sin t)⁻¹) := fun hS hSf =>
    (integrableOn_const hSf).integrable_indicator hS
  have i1 := hi hm1 (hfin hU)
  have i2 := hi hm2 (hfin hU)
  have i3 := hi hm3 (hfin hR)
  have i4 := hi hm4 (hfin hR)
  have i12 : Integrable fun x =>
      (actU ω Θ h t ∩ posU ω Θ h).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t ∩ posU ω Θ h).indicator (fun _ => (sin t)⁻¹) x := i1.sub i2
  have i34 : Integrable fun x =>
      (actR Θ hP.nonempty h t ∩ posR ω Θ hP.nonempty h).indicator (fun _ => (sin t)⁻¹) x -
      (actF ω h t ∩ posR ω Θ hP.nonempty h).indicator (fun _ => (sin t)⁻¹) x := i3.sub i4
  simp only [dIntegrand_eq hP]
  rw [integral_sub i12 i34, integral_sub i1 i2,
    integral_sub i3 i4, integral_indicator_const _ hm1, integral_indicator_const _ hm2,
    integral_indicator_const _ hm3, integral_indicator_const _ hm4]
  simp only [sigmaH, tauH, smul_eq_mul]
  ring


-- @@ L930-984 verbatim
/-- **G2 (replaces Thm 3.1.2 and Lemma 3.4.7).** The two-sided derivative of
`ε ↦ A_Θ(h + ε e_t)` at `0` is `σ(t) - τ(t)`. -/
theorem hasDerivAt_areaH_push (h : ℝ → ℝ) {t : ℝ} (ht : t ∈ diamondFin ω Θ) :
    HasDerivAt (fun ε => areaH ω Θ hP.nonempty (pushH h t ε))
      (sigmaH ω Θ h t - tauH ω Θ hP.nonempty h t) 0 := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  have hsin := hP.sin_pos ht
  have hzero : ∀ ε ∈ Metric.ball (0 : ℝ) 1, ∀ x, M ≤ |x| →
      areaIntegrand ω Θ hP.nonempty (pushH h t ε) x = 0 := by
    intro ε hε x hx
    have hε' : |ε| ≤ 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
      exact hε.le
    have := hM (pushH h t ε) (fun s _ => (abs_pushH_sub h t ε s).trans hε') x hx
    exact areaIntegrand_eq_zero hP this.1 this.2
  set bound : ℝ → ℝ := (Icc (-M) M).indicator fun _ => 4 / sin t with hbound
  have hmeas' : Measurable (dIntegrand ω Θ hP.nonempty h t) := by
    rw [dIntegrand_eq hP]
    have hmU := (isOpen_posU (ω := ω) (Θ := Θ) h).measurableSet
    have hmR := (isOpen_posR (ω := ω) hP.nonempty h).measurableSet
    refine ((Measurable.indicator measurable_const
      (((isClosed_actU (ω := ω) (Θ := Θ) h t).measurableSet).inter hmU)).sub
      (Measurable.indicator measurable_const
      (((isClosed_actF (ω := ω) h t).measurableSet).inter hmU))).sub
      ((Measurable.indicator measurable_const
      (((isClosed_actR hP.nonempty h t).measurableSet).inter hmR)).sub
      (Measurable.indicator measurable_const
      (((isClosed_actF (ω := ω) h t).measurableSet).inter hmR)))
  have hint0 : Integrable (areaIntegrand ω Θ hP.nonempty (pushH h t 0)) := by
    rw [pushH_zero]
    exact (integrable_posPart_U hP h).sub (integrable_posPart_R hP h)
  have hlip : ∀ᵐ x ∂volume, LipschitzOnWith (Real.nnabs (bound x))
      (fun ε => areaIntegrand ω Θ hP.nonempty (pushH h t ε) x) (Metric.ball 0 1) := by
    refine Eventually.of_forall fun x => LipschitzOnWith.of_dist_le_mul fun ε hε ε' hε' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs]
    by_cases hx : x ∈ Icc (-M) M
    · rw [hbound, indicator_of_mem hx, abs_of_pos (div_pos four_pos hsin)]
      exact abs_areaIntegrand_push_sub hP h ht ε ε' x
    · have hx' : M ≤ |x| := by
        by_contra hlt
        exact hx (abs_le.1 (not_le.1 hlt).le)
      rw [hzero ε hε x hx', hzero ε' hε' x hx', sub_self, abs_zero]
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbint : Integrable bound :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hdiff : ∀ᵐ x ∂volume, HasDerivAt
      (fun ε => areaIntegrand ω Θ hP.nonempty (pushH h t ε) x)
      (dIntegrand ω Θ hP.nonempty h t x) 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 (volume_tieAll hP h)
    exact this.mono fun x hx => hasDerivAt_areaIntegrand_push hP ht hx
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun ε => (continuous_areaIntegrand hP.nonempty _).aestronglyMeasurable)
    hint0 hmeas'.aestronglyMeasurable hlip hbint hdiff
  rw [← integral_dIntegrand hP h t]
  exact key.2


-- @@ L986-986 verbatim
end DerivArea


-- @@ L988-988 verbatim
/-! ### The identity `Σ (σ(t) - τ(t)) sin t = 0` (G3) -/


-- @@ L990-990 verbatim
section Balance


-- @@ L992-993 verbatim
/-- Offsets of the upper lines as an affine family. -/
def famA0 (h : ℝ → ℝ) (s : ℝ) : ℝ := h s / sin s


-- @@ L995-996 verbatim
/-- Offsets of the lower lines as an affine family. -/
def famA1 (h : ℝ → ℝ) (s : ℝ) : ℝ := (h s - 1) / sin s


-- @@ L998-999 verbatim
/-- Common slopes. -/
def famBs (s : ℝ) : ℝ := -(cos s / sin s)


-- @@ L1001-1002 verbatim
lemma famA0_add (h : ℝ → ℝ) (s x : ℝ) : famA0 h s + famBs s * x = lineFn s (h s) x := by
  simp only [famA0, famBs, lineFn]; ring


-- @@ L1004-1005 verbatim
lemma famA1_add (h : ℝ → ℝ) (s x : ℝ) : famA1 h s + famBs s * x = lineFn s (h s - 1) x := by
  simp only [famA1, famBs, lineFn]; ring


-- @@ L1007-1007 verbatim
variable (hP : PolySetup ω Θ)

-- @@ L1008-1008 verbatim
include hP


-- @@ L1010-1012 verbatim
lemma affDistinct0 (h : ℝ → ℝ) : AffDistinct (diamondFin ω Θ) (famA0 h) famBs := by
  intro s hs s' hs' hne
  exact Or.inr fun hb => hne (hP.cot_injOn hs hs' (neg_inj.1 hb))


-- @@ L1014-1016 verbatim
lemma affDistinct1 (h : ℝ → ℝ) : AffDistinct (diamondFin ω Θ) (famA1 h) famBs := by
  intro s hs s' hs' hne
  exact Or.inr fun hb => hne (hP.cot_injOn hs hs' (neg_inj.1 hb))


-- @@ L1018-1021 verbatim
omit hP in
lemma actU_eq (h : ℝ → ℝ) (t : ℝ) :
    actU ω Θ h t = activeSet (roofU ω Θ h) (famA0 h) famBs t := by
  ext x; simp only [actU, activeSet, mem_ofPred_eq, famA0_add]


-- @@ L1023-1026 verbatim
omit hP in
lemma actF_eq (h : ℝ → ℝ) (t : ℝ) :
    actF ω h t = activeSet (floorF ω h) (famA1 h) famBs t := by
  ext x; simp only [actF, activeSet, mem_ofPred_eq, famA1_add]


-- @@ L1028-1031 verbatim
omit hP in
lemma actR_eq (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t : ℝ) :
    actR Θ hΘ h t = activeSet (roofR Θ hΘ h) (famA1 h) famBs t := by
  ext x; simp only [actR, activeSet, mem_ofPred_eq, famA1_add]


-- @@ L1033-1037 verbatim
omit hP in
lemma selection_roofU (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ diamondFin ω Θ, x ∈ activeSet (roofU ω Θ h) (famA0 h) famBs s := by
  obtain ⟨s, hs, he⟩ := roofU_mem (ω := ω) (Θ := Θ) h x
  exact ⟨s, hs, by rw [← actU_eq]; exact he⟩


-- @@ L1039-1043 verbatim
omit hP in
lemma selection_floorF (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ diamondFin ω Θ, x ∈ activeSet (floorF ω h) (famA1 h) famBs s := by
  obtain ⟨s, hs, he⟩ := floorF_mem (ω := ω) h x
  exact ⟨s, mem_diamondFin_of_fan hs, by rw [← actF_eq]; exact he⟩


-- @@ L1045-1048 verbatim
lemma selection_roofR (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ diamondFin ω Θ, x ∈ activeSet (roofR Θ hP.nonempty h) (famA1 h) famBs s := by
  obtain ⟨r, hr, -, he⟩ := roofR_mem' hP h x
  exact ⟨r, hr, by rw [← actR_eq]; exact he⟩


-- @@ L1050-1052 verbatim
omit hP in
lemma measurableSet_posU (h : ℝ → ℝ) : MeasurableSet (posU ω Θ h) :=
  (isOpen_posU h).measurableSet


-- @@ L1054-1055 verbatim
lemma measurableSet_posR (h : ℝ → ℝ) : MeasurableSet (posR ω Θ hP.nonempty h) :=
  (isOpen_posR hP.nonempty h).measurableSet


-- @@ L1057-1060 verbatim
lemma volume_posU_ne_top (h : ℝ → ℝ) : volume (posU ω Θ h) ≠ ⊤ := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  exact ne_top_of_le_ne_top measure_Icc_lt_top.ne
    (measure_mono (posU_subset_window fun x hx => (hM h (fun s _ => by simp) x hx).1))


-- @@ L1062-1065 verbatim
lemma volume_posR_ne_top (h : ℝ → ℝ) : volume (posR ω Θ hP.nonempty h) ≠ ⊤ := by
  obtain ⟨M, -, hM⟩ := exists_window hP h
  exact ne_top_of_le_ne_top measure_Icc_lt_top.ne
    (measure_mono (posR_subset_window hP fun x hx => (hM h (fun s _ => by simp) x hx).2))


-- @@ L1067-1071 verbatim
lemma sum_measureReal_actU (h : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) (hAf : volume A ≠ ⊤) :
    ∑ t ∈ diamondFin ω Θ, volume.real (actU ω Θ h t ∩ A) = volume.real A := by
  simp only [actU_eq]
  exact sum_measureReal_activeSet_inter (affDistinct0 hP h) (continuous_roofU h)
    (selection_roofU h) hA hAf


-- @@ L1073-1077 verbatim
lemma sum_measureReal_actF (h : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) (hAf : volume A ≠ ⊤) :
    ∑ t ∈ diamondFin ω Θ, volume.real (actF ω h t ∩ A) = volume.real A := by
  simp only [actF_eq]
  exact sum_measureReal_activeSet_inter (affDistinct1 hP h) (continuous_floorF h)
    (selection_floorF h) hA hAf


-- @@ L1079-1083 verbatim
lemma sum_measureReal_actR (h : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) (hAf : volume A ≠ ⊤) :
    ∑ t ∈ diamondFin ω Θ, volume.real (actR Θ hP.nonempty h t ∩ A) = volume.real A := by
  simp only [actR_eq]
  exact sum_measureReal_activeSet_inter (affDistinct1 hP h) (continuous_roofR hP.nonempty h)
    (selection_roofR hP h) hA hAf


-- @@ L1085-1089 verbatim
theorem sum_sigmaH (h : ℝ → ℝ) :
    ∑ t ∈ diamondFin ω Θ, sigmaH ω Θ h t * sin t = volume.real (posU ω Θ h) := by
  rw [← sum_measureReal_actU hP h (measurableSet_posU h) (volume_posU_ne_top hP h)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [sigmaH, div_mul_cancel₀ _ (hP.sin_pos ht).ne']


-- @@ L1091-1102 verbatim
theorem sum_tauH (h : ℝ → ℝ) :
    ∑ t ∈ diamondFin ω Θ, tauH ω Θ hP.nonempty h t * sin t = volume.real (posU ω Θ h) := by
  have e : ∀ t ∈ diamondFin ω Θ, tauH ω Θ hP.nonempty h t * sin t =
      volume.real (actR Θ hP.nonempty h t ∩ posR ω Θ hP.nonempty h) +
      volume.real (actF ω h t ∩ posU ω Θ h) -
      volume.real (actF ω h t ∩ posR ω Θ hP.nonempty h) := fun t ht => by
    rw [tauH, div_mul_cancel₀ _ (hP.sin_pos ht).ne']
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_measureReal_actR hP h (measurableSet_posR hP h) (volume_posR_ne_top hP h),
    sum_measureReal_actF hP h (measurableSet_posU h) (volume_posU_ne_top hP h),
    sum_measureReal_actF hP h (measurableSet_posR hP h) (volume_posR_ne_top hP h)]
  ring


-- @@ L1104-1109 verbatim
/-- **G3 (replaces Lemma 3.4.6).** -/
theorem sum_sigmaH_sub_tauH (h : ℝ → ℝ) :
    ∑ t ∈ diamondFin ω Θ, (sigmaH ω Θ h t - tauH ω Θ hP.nonempty h t) * sin t = 0 := by
  have e : ∀ t ∈ diamondFin ω Θ, (sigmaH ω Θ h t - tauH ω Θ hP.nonempty h t) * sin t =
      sigmaH ω Θ h t * sin t - tauH ω Θ hP.nonempty h t * sin t := fun t _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, sum_sigmaH hP, sum_tauH hP, sub_self]


-- @@ L1111-1125 verbatim
/-- If `h` is not balanced, some angle has `σ(t) > τ(t)`. -/
theorem exists_tauH_lt_sigmaH (h : ℝ → ℝ)
    (hne : ∃ t ∈ diamondFin ω Θ, sigmaH ω Θ h t ≠ tauH ω Θ hP.nonempty h t) :
    ∃ t ∈ diamondFin ω Θ, tauH ω Θ hP.nonempty h t < sigmaH ω Θ h t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀, hne'⟩ := hne
  have hzero := sum_sigmaH_sub_tauH hP h
  have hnonpos : ∀ t ∈ diamondFin ω Θ,
      (sigmaH ω Θ h t - tauH ω Θ hP.nonempty h t) * sin t ≤ 0 := fun t ht =>
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hcon t ht]) (hP.sin_pos ht).le
  have := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hzero t₀ ht₀
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hne' (by linarith [sub_eq_zero.1 h1])
  · exact absurd h1 (hP.sin_pos ht₀).ne'


-- @@ L1127-1127 verbatim
end Balance


-- @@ L1129-1129 verbatim
end Sofa
