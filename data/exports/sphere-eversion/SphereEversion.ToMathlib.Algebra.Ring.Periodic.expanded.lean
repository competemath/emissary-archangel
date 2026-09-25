import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Separation.Hausdorff

-- TODO: the file this references doesn't exist in mathlib any more; rename this one appropriately!


-- @@ L7-22 verbatim
/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma Continuous.bounded_of_onePeriodic_of_isCompact {f : X → ℝ → E} (cont : Continuous ↿f)
  (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space.
Patrick is not sure this is the optimal version.

In the first part, generalize many lemmas to any period and add to `Algebra.Ring.Periodic.lean`?
-/



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function Filter TopologicalSpace Int


-- @@ L29-29 verbatim
open scoped Topology


-- @@ L31-31 verbatim
section OnePeriodic


-- @@ L33-33 verbatim
variable {α : Type*}


-- @@ L35-36 verbatim
/-- The integers as an additive subgroup of the reals. -/
def ℤSubℝ : AddSubgroup ℝ := AddMonoidHom.range (Int.castAddHom ℝ)


-- @@ L38-40 verbatim
/-- The equivalence relation on `ℝ` corresponding to its partition as cosets of `ℤ`. -/
@[implicit_reducible]
def transOne : Setoid ℝ := QuotientAddGroup.leftRel ℤSubℝ


-- @@ L42-43 verbatim
/-- The proposition that a function on `ℝ` is periodic with period `1`. -/
def OnePeriodic (f : ℝ → α) : Prop := Periodic f 1


-- @@ L45-46 verbatim
theorem OnePeriodic.add_nat {f : ℝ → α} (h : OnePeriodic f) (k : ℕ) (x : ℝ) : f (x + k) = f x := by
  simpa using h.nat_mul k x


-- @@ L48-49 verbatim
theorem OnePeriodic.add_int {f : ℝ → α} (h : OnePeriodic f) (k : ℤ) (x : ℝ) : f (x + k) = f x := by
  simpa using h.int_mul k x


-- @@ L51-56 verbatim
/-- The circle `𝕊₁ := ℝ/ℤ`.

TODO [Yury]: use `AddCircle`. -/
def 𝕊₁ :=
  Quotient transOne
deriving TopologicalSpace, Inhabited


-- @@ L58-60 verbatim
theorem transOne_rel_iff {a b : ℝ} : transOne.r a b ↔ ∃ k : ℤ, b = a + k := by
  refine QuotientAddGroup.leftRel_apply.trans (exists_congr fun k ↦ ?_)
  rw [coe_castAddHom, eq_neg_add_iff_add_eq, eq_comm]


-- @@ L62-62 verbatim
section


-- @@ L64-64 verbatim
attribute [local instance] transOne


-- @@ L66-68 verbatim
/-- The quotient map from the reals to the circle `ℝ ⧸ ℤ`. -/
def proj𝕊₁ : ℝ → 𝕊₁ :=
  Quotient.mk'


-- @@ L70-72 verbatim
@[simp]
theorem proj𝕊₁_add_int (t : ℝ) (k : ℤ) : proj𝕊₁ (t + k) = proj𝕊₁ t :=
  (Quotient.sound (transOne_rel_iff.mpr ⟨k, rfl⟩)).symm


-- @@ L74-78 verbatim
/-- The unique representative in the half-open interval `[0, 1)` for each coset of `ℤ` in `ℝ`,
regarded as a map from the circle `𝕊₁ → ℝ`. -/
def 𝕊₁.repr (x : 𝕊₁) : ℝ :=
  let t := Quotient.out x
  fract t


-- @@ L80-81 verbatim
theorem 𝕊₁.repr_mem (x : 𝕊₁) : x.repr ∈ (Ico 0 1 : Set ℝ) :=
  ⟨fract_nonneg _, fract_lt_one _⟩


-- @@ L83-87 verbatim
theorem 𝕊₁.proj_repr (x : 𝕊₁) : proj𝕊₁ x.repr = x := by
  symm
  conv_lhs => rw [← Quotient.out_eq x]
  rw [← fract_add_floor (Quotient.out x)]
  apply proj𝕊₁_add_int


-- @@ L89-91 verbatim
theorem image_proj𝕊₁_Ico : proj𝕊₁ '' Ico 0 1 = univ := by
  rw [eq_univ_iff_forall]
  exact fun x ↦ ⟨x.repr, x.repr_mem, x.proj_repr⟩


-- @@ L93-94 verbatim
theorem image_proj𝕊₁_Icc : proj𝕊₁ '' Icc 0 1 = univ :=
  eq_univ_of_subset (image_mono Ico_subset_Icc_self) image_proj𝕊₁_Ico


-- @@ L96-96 verbatim
theorem isOpenQuotientMap_proj𝕊₁ : IsOpenQuotientMap proj𝕊₁ := QuotientAddGroup.isOpenQuotientMap_mk


-- @@ L98-99 verbatim
@[continuity, fun_prop]
theorem continuous_proj𝕊₁ : Continuous proj𝕊₁ := isOpenQuotientMap_proj𝕊₁.continuous


-- @@ L101-101 verbatim
theorem isOpenMap_proj𝕊₁ : IsOpenMap proj𝕊₁ := isOpenQuotientMap_proj𝕊₁.isOpenMap


-- @@ L103-106 verbatim
theorem quotientMap_id_proj𝕊₁ {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap fun p : X × ℝ ↦ (p.1, proj𝕊₁ p.2) :=
  (IsOpenMap.id.prodMap isOpenMap_proj𝕊₁).isQuotientMap (by fun_prop)
    (surjective_id.prodMap Quotient.exists_rep)


-- @@ L108-110 verbatim
/-- A one-periodic function on `ℝ` descends to a function on the circle `ℝ ⧸ ℤ`. -/
def OnePeriodic.lift {f : ℝ → α} (h : OnePeriodic f) : 𝕊₁ → α :=
  Quotient.lift f (by intro a b hab; rcases transOne_rel_iff.mp hab with ⟨k, rfl⟩; rw [h.add_int])


-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
@[inherit_doc] local notation "π" => proj𝕊₁


-- @@ L116-117 verbatim
instance : CompactSpace 𝕊₁ :=
  ⟨by rw [← image_proj𝕊₁_Icc]; exact isCompact_Icc.image continuous_proj𝕊₁⟩


-- @@ L119-120 verbatim
theorem isClosed_int : IsClosed (range ((↑) : ℤ → ℝ)) :=
  Int.isClosedEmbedding_coe_real.isClosed_range


-- @@ L122-134 verbatim
instance : T2Space 𝕊₁ := by
  rw [t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_proj𝕊₁]
  have : {q : ℝ × ℝ | π q.fst = π q.snd} = {q : ℝ × ℝ | ∃ k : ℤ, q.2 = q.1 + k} := by
    ext ⟨a, b⟩
    exact Quotient.eq''.trans transOne_rel_iff
  have : {q : ℝ × ℝ | π q.fst = π q.snd} =
      (fun q : ℝ × ℝ ↦ q.2 - q.1) ⁻¹' (range <| ((↑) : ℤ → ℝ)) := by
    rw [this]
    ext ⟨a, b⟩
    refine exists_congr fun k ↦ ?_
    conv_rhs => rw [eq_comm, sub_eq_iff_eq_add']
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) isClosed_int


-- @@ L136-136 verbatim
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]


-- @@ L138-149 verbatim
theorem Continuous.bounded_on_compact_of_onePeriodic {f : X → ℝ → E} (cont : Continuous ↿f)
    (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ t, ‖f x t‖ ≤ C := by
  let F : X × 𝕊₁ → E := fun p : X × 𝕊₁ ↦ (hper p.1).lift p.2
  have Fcont : Continuous F := by
    have qm : Topology.IsQuotientMap fun p : X × ℝ ↦ (p.1, π p.2) := quotientMap_id_proj𝕊₁
    -- avoid weird elaboration issue
    have : ↿f = F ∘ fun p : X × ℝ ↦ (p.1, π p.2) := by ext p; rfl
    rwa [this, ← qm.continuous_iff] at cont
  obtain ⟨C, hC⟩ :=
    (hK.prod isCompact_univ).bddAbove_image (continuous_norm.comp Fcont).continuousOn
  exact ⟨C, fun x x_in t ↦ hC ⟨(x, π t), ⟨x_in, mem_univ _⟩, rfl⟩⟩


-- @@ L151-158 verbatim
theorem Continuous.bounded_of_onePeriodic_of_compact {f : X → ℝ → E} (cont : Continuous ↿f)
    (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K)
    (hfK : ∀ x ∉ K, f x = 0) : ∃ C, ∀ x t, ‖f x t‖ ≤ C := by
  obtain ⟨C, hC⟩ := cont.bounded_on_compact_of_onePeriodic hper hK
  refine ⟨max C 0, fun x t ↦ ?_⟩
  by_cases hx : x ∈ K
  · exact le_max_of_le_left (hC x hx t)
  · simp [hfK, hx]


-- @@ L160-160 verbatim
end OnePeriodic
