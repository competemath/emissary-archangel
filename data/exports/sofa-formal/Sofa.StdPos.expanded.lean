/-
# Sofa/StdPos.lean — Baek's moving sofas with a rotation angle; standard position
(M2 batch 3: Baek Def 1.1.2, Def 2.3.3, Def 2.3.4, Prop 1.2.1 = Prop 2.3.1, Prop 1.2.2)

* `tr c S` — the translate `S + c`, and how support functions, supporting hallways, strips and
  the monotone hull transform under it;
* `StdPos S ω` — standard position `h_S(ω) = h_S(π/2) = 1` (Def 2.3.4), and the translation
  `stdVec S ω` achieving it (Prop 2.3.1, existence part);
* `IsSofaWithAngle S ω` — some translate of `S` is an upstream moving sofa whose motion has
  continuous rotation angle `θ` with `θ 1 = -ω` (Baek's "moving sofa with rotation angle ω");
* `IsSofaWithAngle.subset` — Prop 1.2.2 in normalised form:
  `S ⊆ P_ω` and `S ⊆ L_S(t)` for all `t ∈ [0, ω]`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5), no `sorry`.
-/
import Sofa.Monotone
import Sofa.Motion


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Real Set MovingSofa MeasureTheory

-- @@ L22-22 verbatim
open scoped EuclideanGeometry RealInnerProductSpace unitInterval


-- @@ L24-24 verbatim
namespace Sofa


-- @@ L26-26 verbatim
/-! ## Translations -/


-- @@ L28-29 expanded
/-- The translate `S + c`. -/
def tr (c : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (· + c) '' S


-- @@ L31-31 expanded
variable {S : Set (EuclideanSpace ℝ (Fin 2))} {ω : ℝ}


-- @@ L33-38 expanded
lemma mem_tr {c p : EuclideanSpace ℝ (Fin 2)} : p ∈ tr c S ↔ p - c ∈ S :=
  by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨p - c, h, by simp⟩


-- @@ L40-40 expanded
lemma add_mem_tr {c p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ S) : p + c ∈ tr c S :=
  ⟨p, hp, rfl⟩


-- @@ L42-45 expanded
lemma tr_tr (c d : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    tr d (tr c S) = tr (c + d) S := by
  ext p
  simp only [mem_tr]
  rw [show p - d - c = p - (c + d) by abel]


-- @@ L47-48 expanded
lemma tr_zero (S : Set (EuclideanSpace ℝ (Fin 2))) : tr 0 S = S := by ext p; simp [mem_tr]


-- @@ L50-51 expanded
lemma tr_neg_tr (c : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    tr (-c) (tr c S) = S := by rw [tr_tr, add_neg_cancel, tr_zero]


-- @@ L53-53 expanded
lemma tr_mono {c : EuclideanSpace ℝ (Fin 2)} {S T : Set (EuclideanSpace ℝ (Fin 2))} (h : S ⊆ T) :
    tr c S ⊆ tr c T :=
  Set.image_mono h


-- @@ L55-56 expanded
lemma tr_inter (c : EuclideanSpace ℝ (Fin 2)) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    tr c (S ∩ T) = tr c S ∩ tr c T :=
  Set.image_inter (add_left_injective c)


-- @@ L58-59 expanded
lemma tr_sdiff (c : EuclideanSpace ℝ (Fin 2)) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    tr c (S \ T) = tr c S \ tr c T :=
  Set.image_sdiff (add_left_injective c) S T


-- @@ L61-64 expanded
lemma tr_biInter {ι : Type*} (c : EuclideanSpace ℝ (Fin 2)) (A : Set ι)
    (F : ι → Set (EuclideanSpace ℝ (Fin 2))) : tr c (⋂ i ∈ A, F i) = ⋂ i ∈ A, tr c (F i) :=
  by
  ext p
  simp only [mem_tr, Set.mem_iInter₂]


-- @@ L66-67 expanded
lemma isCompact_tr (hS : IsCompact S) (c : EuclideanSpace ℝ (Fin 2)) : IsCompact (tr c S) :=
  hS.image (by fun_prop)


-- @@ L69-69 expanded
lemma nonempty_tr (hS : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) : (tr c S).Nonempty :=
  hS.image _


-- @@ L71-72 expanded
lemma isConnected_tr (hS : IsConnected S) (c : EuclideanSpace ℝ (Fin 2)) : IsConnected (tr c S) :=
  hS.image _ (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin 2) => p + c).continuousOn


-- @@ L74-75 expanded
lemma isClosed_tr (hS : IsClosed S) (c : EuclideanSpace ℝ (Fin 2)) : IsClosed (tr c S) :=
  (Homeomorph.addRight c).isClosedMap _ hS


-- @@ L77-78 expanded
lemma volume_tr (c : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (tr c S) = volume S := by rw [tr, Set.image_add_right, measure_preimage_add_right]


-- @@ L80-82 expanded
lemma supportFn_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    supportFn (tr c S) t = supportFn S t + ⟪c, u t⟫ :=
  supportFn_translate hS hne c t


-- @@ L84-88 expanded
/-- Half-planes under translation. -/
lemma tr_hpLe (c : EuclideanSpace ℝ (Fin 2)) (t h : ℝ) : tr c (hpLe t h) = hpLe t (h + ⟪c, u t⟫) :=
  by
  ext p
  simp only [mem_tr, hpLe, Set.mem_ofPred_eq, inner_sub_left]
  constructor <;> intro hp <;> linarith


-- @@ L90-93 expanded
lemma tr_hpGe (c : EuclideanSpace ℝ (Fin 2)) (t h : ℝ) : tr c (hpGe t h) = hpGe t (h + ⟪c, u t⟫) :=
  by
  ext p
  simp only [mem_tr, hpGe, Set.mem_ofPred_eq, inner_sub_left]
  constructor <;> intro hp <;> linarith


-- @@ L95-100 expanded
lemma suppMap_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : suppMap (tr c S) t p = suppMap S t p + c :=
  by
  unfold suppMap
  rw [supportFn_tr hS hne, supportFn_tr hS hne, u_add_pi_div_two]
  conv_rhs => rw [decomp_u_v t c]
  module


-- @@ L102-106 expanded
lemma suppHallway_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    suppHallway (tr c S) t = tr c (suppHallway S t) :=
  by
  unfold suppHallway tr
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p


-- @@ L108-113 expanded
lemma QplusS_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    QplusS (tr c S) t = tr c (QplusS S t) :=
  by
  rw [← suppMap_image_Qplus, ← suppMap_image_Qplus]
  show _ = (· + c) '' (suppMap S t '' Qplus)
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p


-- @@ L115-120 expanded
lemma QminusS_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    QminusS (tr c S) t = tr c (QminusS S t) :=
  by
  rw [← suppMap_image_Qminus, ← suppMap_image_Qminus]
  show _ = (· + c) '' (suppMap S t '' Qminus)
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p


-- @@ L122-126 expanded
lemma strips_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (ω : ℝ) :
    strips (tr c S) ω = tr c (strips S ω) :=
  by
  unfold strips
  simp only [tr_inter, tr_hpLe, tr_hpGe, supportFn_tr hS hne]
  congr 3 <;> ring


-- @@ L128-132 expanded
lemma monotoneHull_tr (hS : IsCompact S) (hne : S.Nonempty) (c : EuclideanSpace ℝ (Fin 2)) (ω : ℝ) :
    monotoneHull (tr c S) ω = tr c (monotoneHull S ω) :=
  by
  ext p
  simp only [monotoneHull, strips_tr hS hne, suppHallway_tr hS hne, Set.mem_inter_iff,
    Set.mem_iInter₂, mem_tr]


-- @@ L134-134 verbatim
/-! ## Standard position -/


-- @@ L136-137 expanded
/-- **Def 2.3.4.** `S` is in standard position for the rotation angle `ω`. -/
def StdPos (S : Set (EuclideanSpace ℝ (Fin 2))) (ω : ℝ) : Prop :=
  supportFn S ω = 1 ∧ supportFn S (π / 2) = 1


-- @@ L139-141 expanded
/-- The translation vector putting `S` in standard position (for `ω ∈ (0, π/2]`). -/
def stdVec (S : Set (EuclideanSpace ℝ (Fin 2))) (ω : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  pt ((1 - supportFn S ω - (1 - supportFn S (π / 2)) * sin ω) / cos ω) (1 - supportFn S (π / 2))


-- @@ L143-156 verbatim
/-- **Prop 2.3.1 (existence).** -/
lemma stdPos_tr_stdVec (hS : IsCompact S) (hne : S.Nonempty) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) :
    StdPos (tr (stdVec S ω) S) ω := by
  constructor
  · rw [supportFn_tr hS hne, inner_eq, stdVec, pt_zero, pt_one, u_coord_zero, u_coord_one]
    rcases hω1.lt_or_eq with h | h
    · have hc : cos ω ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, h⟩).ne'
      field_simp
      ring
    · subst h
      simp only [cos_pi_div_two, sin_pi_div_two, div_zero, zero_mul, mul_one, zero_add]
      ring
  · rw [supportFn_tr hS hne, inner_u_pi_div_two, stdVec, pt_one]
    ring


-- @@ L158-163 verbatim
/-- In standard position the strips of Fable's `monotoneHull` are Baek's `P_ω = H ∩ V_ω`. -/
lemma strips_of_stdPos (h : StdPos S ω) : strips S ω = para ω := by
  ext p
  simp only [strips, para, Hstrip, Vstrip, h.1, h.2, hpLe, hpGe, Set.mem_inter_iff,
    Set.mem_ofPred_eq, inner_u_pi_div_two, sub_self]
  tauto


-- @@ L165-165 verbatim
/-! ## Baek's moving sofas with a rotation angle -/


-- @@ L167-172 expanded
/-- **Def 1.1.2 + Def 2.3.3.** Some translate of `S` is an upstream moving sofa whose motion has a
continuous rotation angle `θ` (`θ 0 = 0`) ending at `θ 1 = -ω`, i.e. the sofa turns *clockwise*
by `ω`. -/
def IsSofaWithAngle (S : Set (EuclideanSpace ℝ (Fin 2))) (ω : ℝ) : Prop :=
  ∃ (c : EuclideanSpace ℝ (Fin 2)) (m :
    I → EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (θ : I → ℝ),
    IsMovingSofa (tr c S) m ∧
      Continuous θ ∧ θ 0 = 0 ∧ (∀ t p, m t p = rot (θ t) p + m t 0) ∧ θ 1 = -ω


-- @@ L174-178 expanded
/-- Every upstream moving sofa is a Baek sofa, with the angle of its (unique) continuous lift. -/
lemma isSofaWithAngle_of_isMovingSofa {s : Set (EuclideanSpace ℝ (Fin 2))}
    {m : I → EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)} (hm : IsMovingSofa s m) :
    ∃ ω, IsSofaWithAngle s ω :=
  by
  obtain ⟨θ, hθc, hθ0, hθ⟩ := exists_rotationAngle hm.continuous hm.zero
  exact ⟨-θ 1, 0, m, θ, by rwa [tr_zero], hθc, hθ0, hθ, by ring⟩


-- @@ L180-180 verbatim
namespace IsSofaWithAngle


-- @@ L182-185 expanded
lemma tr' (h : IsSofaWithAngle S ω) (d : EuclideanSpace ℝ (Fin 2)) : IsSofaWithAngle (tr d S) ω :=
  by
  obtain ⟨c, m, θ, hm, hθc, hθ0, hθ, hθ1⟩ := h
  refine ⟨c - d, m, θ, ?_, hθc, hθ0, hθ, hθ1⟩
  rwa [tr_tr, show d + (c - d) = c by abel]


-- @@ L187-189 verbatim
lemma isCompact (h : IsSofaWithAngle S ω) : IsCompact S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isCompact_tr hm.isCompact (-c)


-- @@ L191-193 verbatim
lemma isConnected (h : IsSofaWithAngle S ω) : IsConnected S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isConnected_tr hm.isConnected (-c)


-- @@ L195-197 verbatim
lemma isClosed (h : IsSofaWithAngle S ω) : IsClosed S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isClosed_tr hm.isClosed (-c)


-- @@ L199-199 verbatim
lemma nonempty (h : IsSofaWithAngle S ω) : S.Nonempty := h.isConnected.nonempty


-- @@ L201-208 verbatim
/-- **Prop 1.2.2 (via Fable's normalisation-free hull).** -/
lemma subset_monotoneHull (h : IsSofaWithAngle S ω) : S ⊆ monotoneHull S ω := by
  have hS := h.isCompact
  have hne := h.nonempty
  obtain ⟨c, m, θ, hm, hθc, hθ0, hθ, hθ1⟩ := h
  have h1 := hm.subset_monotoneHull hθc hθ0 hθ hθ1
  have h2 := tr_mono (c := -c) h1
  rwa [tr_neg_tr, monotoneHull_tr hS hne, tr_neg_tr] at h2


-- @@ L210-218 verbatim
/-- **Prop 1.2.2.** A moving sofa with rotation angle `ω` in standard position lies in `P_ω` and
in every supporting hallway `L_S(t)`, `t ∈ [0, ω]`. -/
theorem subset (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) :
    S ⊆ para ω ∧ ∀ t ∈ Icc (0 : ℝ) ω, S ⊆ suppHallway S t := by
  have hsub := h.subset_monotoneHull
  refine ⟨fun p hp => ?_, fun t ht p hp => ?_⟩
  · have := (hsub hp).1
    rwa [strips_of_stdPos hstd] at this
  · exact monotoneHull_subset_suppHallway S ht (hsub hp)


-- @@ L220-220 verbatim
end IsSofaWithAngle


-- @@ L222-222 verbatim
end Sofa
