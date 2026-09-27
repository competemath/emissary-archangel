/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import LeanPool.QuasiBorelSpaces.Hom
public import LeanPool.QuasiBorelSpaces.MeasureTheory.ProbabilityMeasure
public import LeanPool.QuasiBorelSpaces.MeasureTheory.Pack
public import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.MeasureTheory.Cases
import LeanPool.QuasiBorelSpaces.MeasureTheory.Measure
import LeanPool.QuasiBorelSpaces.Prop
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-23 verbatim
/-!
# LeanPool.QuasiBorelSpaces.PreProbabilityMeasure

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.PreProbabilityMeasure`.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open MeasureTheory

-- @@ L28-28 verbatim
open scoped unitInterval


-- @@ L30-30 verbatim
namespace QuasiBorelSpace


-- @@ L32-36 verbatim
variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]


-- @@ L38-49 expanded
/-- A precursor to the type of probability measures. Intuitively, a
_(quasi-borel) probability measure_ is just a variable applied to a normal
probability measure on `ℝ`. A `PreProbabilityMeasure` holds the underlying
variable and probability measure.
-/
@[ext]
structure PreProbabilityMeasure (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with the probability measure. -/
  eval : QuasiBorelHom ℝ A
  /-- The base `ProbabilityMeasure`. -/
  base : ProbabilityMeasure ℝ


-- @@ L51-51 verbatim
namespace PreProbabilityMeasure


-- @@ L53-55 verbatim
/-- The integral of a function relative to a probability measure. -/
noncomputable def lintegral (f : A → ENNReal) : PreProbabilityMeasure A → ENNReal
  | ⟨φ, μ⟩ => ∫⁻ x, f (φ x) ∂μ


-- @@ L57-58 verbatim
@[simp]
alias lintegral_mk := PreProbabilityMeasure.lintegral.eq_1


-- @@ L60-62 verbatim
/-- TODO -/
noncomputable def measureOf : PreProbabilityMeasure A → Set A → ENNReal
  | ⟨φ, μ⟩, s => μ { x | φ x ∈ s }


-- @@ L64-65 verbatim
@[simp]
alias measureOf_mk := PreProbabilityMeasure.measureOf.eq_1


-- @@ L67-76 verbatim
@[simp]
lemma lintegral_eq_measureOf
    (μ : PreProbabilityMeasure A) (s : Set A) (hp : IsHom (· ∈ s))
    : lintegral (s.indicator 1) μ = measureOf μ s := by
  rcases μ with ⟨φ, μ⟩
  simp only [lintegral_mk, measureOf_mk, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [←MeasureTheory.lintegral_indicator_one]
  · rfl
  · have := isHom_comp' hp φ.isHom_coe
    simpa only [measurableSet_setOfPred, isHom_ofMeasurableSpace] using this


-- @@ L78-89 expanded
/-- A `PreProbabilityMeasure` can be constructed from any `ProbabilityMeasure` on a
standard borel space.
-/
noncomputable def mk' [MeasurableSpace A] [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    (eval : QuasiBorelHom A B) (base : ProbabilityMeasure A) : PreProbabilityMeasure B
    where
  eval :=
    have : Nonempty A := base.nonempty
    .mk fun x ↦ eval (unpack x)
  base := base.map pack


-- @@ L91-102 expanded
@[simp]
lemma lintegral_mk' [MeasurableSpace A] [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    {k : B → ENNReal} (hk : IsHom k) (φ : QuasiBorelHom A B) (μ : ProbabilityMeasure A) :
    lintegral k (mk' φ μ) = ∫⁻ (x : A), k (φ x) ∂μ.toMeasure :=
  by
  simp only [mk', lintegral_mk, ProbabilityMeasure.toMeasure_map, QuasiBorelHom.coe_mk]
  rw [lintegral_map]
  · simp only [unpack_pack]
  · apply measurable_of_isHom
    fun_prop
  · fun_prop


-- @@ L104-112 verbatim
lemma lintegral_add_left
    {f : A → ENNReal} (hf : IsHom f)
    (g : A → ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_left
  apply measurable_of_isHom
  fun_prop


-- @@ L114-123 verbatim
lemma lintegral_add_right
    (f : A → ENNReal)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_right
  apply measurable_of_isHom
  fun_prop


-- @@ L125-131 verbatim
instance setoid (A : Type*) [QuasiBorelSpace A] : Setoid (PreProbabilityMeasure A) where
  r μ₁ μ₂ := ∀⦃f⦄, IsHom f → μ₁.lintegral f = μ₂.lintegral f
  iseqv := {
    refl _ _ _ := rfl
    symm h₁ _ h₂ := (h₁ h₂).symm
    trans h₁ h₂ _ h₃ := (h₁ h₃).trans (h₂ h₃)
  }


-- @@ L133-140 verbatim
lemma lintegral_mul_left
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ c * f x) μ = c * lintegral f μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_const_mul
  apply measurable_of_isHom
  fun_prop


-- @@ L142-149 verbatim
lemma lintegral_mul_right
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ f x * c) μ = lintegral f μ * c := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_mul_const
  apply measurable_of_isHom
  fun_prop


-- @@ L151-156 verbatim
@[simp]
lemma lintegral_const
    (c : ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral (fun _ ↦ c) μ = c := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, MeasureTheory.lintegral_const, measure_univ, mul_one]


-- @@ L158-163 verbatim
@[simp]
lemma lintegral_mono
    {f g : A → ENNReal} (h : f ≤ g) (μ : PreProbabilityMeasure A)
    : lintegral f μ ≤ lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simpa only [lintegral_mk] using MeasureTheory.lintegral_mono fun a ↦ h _


-- @@ L165-173 verbatim
lemma lintegral_iSup
    (f : ℕ → A → ENNReal) (hf₁ : Monotone f) (hf₂ : ∀ n, IsHom (f n)) (μ : PreProbabilityMeasure A)
    : ⨆n, lintegral (f n) μ = lintegral (⨆n, f n) μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, iSup_apply]
  rw [MeasureTheory.lintegral_iSup]
  · intro n
    simpa only [isHom_ofMeasurableSpace] using isHom_comp' (hf₂ n) eval.isHom_coe
  · exact fun i j h x ↦ hf₁ h _


-- @@ L175-183 verbatim
lemma lintegral_finset_sum {A}
    (s : Finset A) {f : A → B → ENNReal}
    (hf : ∀ b ∈ s, IsHom (f b)) (μ : PreProbabilityMeasure B) :
    lintegral (fun a ↦ ∑ b ∈ s, f b a) μ = ∑ b ∈ s, lintegral (f b) μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  rw [MeasureTheory.lintegral_finsetSum]
  intro b hb
  simpa only [isHom_ofMeasurableSpace] using isHom_comp' (hf b hb) eval.isHom_coe


-- @@ L185-193 verbatim
lemma lintegral_sub_le
    (f : A → ENNReal)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral f μ - lintegral g μ ≤ lintegral (f - g) μ := by
  simp only [lintegral, Pi.sub_apply]
  apply MeasureTheory.lintegral_sub_le
  have : IsHom fun x ↦ g (μ.eval x) := by fun_prop
  simpa only [isHom_ofMeasurableSpace] using this


-- @@ L195-204 verbatim
theorem lintegral_lintegral_swap
    {μ : PreProbabilityMeasure A} {ν : PreProbabilityMeasure B}
    ⦃f : A → B → ENNReal⦄ (hf : IsHom (Function.uncurry f)) :
    lintegral (fun x ↦ lintegral (f x) ν) μ =
    lintegral (fun x ↦ lintegral (f · x) μ) ν := by
  simp only [lintegral]
  rw [MeasureTheory.lintegral_lintegral_swap]
  apply Measurable.aemeasurable
  apply measurable_of_isHom
  fun_prop


-- @@ L206-211 verbatim
@[simp]
lemma measureOf_empty (μ : PreProbabilityMeasure B) : measureOf μ ∅ = 0 := by
  rcases μ
  simp only [
    measureOf_mk, Set.mem_empty_iff_false, Set.ofPred_false,
    ProbabilityMeasure.coeFn_empty, ENNReal.coe_zero]


-- @@ L213-218 verbatim
@[simp]
lemma measureOf_mono (μ : PreProbabilityMeasure B) : Monotone (measureOf μ) := by
  intro p q h
  rcases μ
  simp only [measureOf_mk, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact measure_mono fun r hr ↦ h hr


-- @@ L220-227 verbatim
lemma measureOf_iUnion_le {ι : Type*} [Countable ι]
    (μ : PreProbabilityMeasure A) (s : ι → Set A)
    : μ.measureOf (⋃ i, s i) ≤ ∑' (i : ι), μ.measureOf (s i) := by
  rcases μ
  simp only [
    measureOf_mk, Set.mem_iUnion, Set.ofPred_exists,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  apply measure_iUnion_le


-- @@ L229-230 verbatim
@[simp]
lemma setoid_r (μ₁ μ₂ : PreProbabilityMeasure A) : (setoid A).r μ₁ μ₂ ↔ μ₁ ≈ μ₂ := by rfl


-- @@ L232-234 verbatim
lemma equiv_def (μ₁ μ₂ : PreProbabilityMeasure A)
    : μ₁ ≈ μ₂ ↔ (∀{f}, IsHom f → μ₁.lintegral f = μ₂.lintegral f) := by
  rfl


-- @@ L236-282 expanded
lemma equiv_def' (μ₁ μ₂ : PreProbabilityMeasure A) :
    μ₁ ≈ μ₂ ↔ (∀ {p}, IsHom (· ∈ p) → μ₁.measureOf p = μ₂.measureOf p) := by
  classical
  apply Iff.intro
  · intro h p hp
    simp (disch := fun_prop) only [← lintegral_eq_measureOf]
    apply h
    simp +unfoldPartialApp only [Set.indicator, Pi.one_apply]
    apply «Prop».isHom_ite <;> fun_prop
  · intro h k hk
    rcases μ₁ with ⟨φ₁, μ₁⟩
    rcases μ₂ with ⟨φ₂, μ₂⟩
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, measureOf_mk,
      lintegral_mk] at ⊢ h
    let := toMeasurableSpace (A := A)
    have (φ : QuasiBorelHom ℝ A) (μ : Measure ℝ) :
      ∫⁻ (x : ℝ), k (φ x) ∂μ = ∫⁻ (x : A), k x ∂(μ.map φ) :=
      by
      rw [lintegral_map]
      · intro X hX φ hφ
        have := isHom_comp' hk hφ
        simp only [isHom_ofMeasurableSpace] at this
        apply this hX
      · intro X hX
        apply hX
        fun_prop
    simp only [this]
    have (p : Set A) (hp : IsHom (· ∈ p)) (φ : QuasiBorelHom ℝ A) (μ : Measure ℝ) :
      μ {x | φ x ∈ p} = μ.map φ p := by
      rw [Measure.map_apply]
      · simp only [Set.preimage]
      · intro X hX
        apply hX
        simp only [QuasiBorelHom.isHom_coe]
      · intro φ hφ
        have := isHom_comp' hp hφ
        simpa only [Set.preimage, measurableSet_setOfPred, isHom_ofMeasurableSpace] using this
    simp +contextual only [this] at h
    congr 1
    ext X hX
    apply h
    rw [isHom_def]
    intro φ hφ
    specialize hX hφ
    simpa only [Set.preimage, measurableSet_setOfPred, isHom_ofMeasurableSpace] using hX


-- @@ L284-284 verbatim
lemma nonempty (μ : PreProbabilityMeasure A) : Nonempty A := ⟨μ.eval 0⟩


-- @@ L286-293 expanded
/-- The type of variables for probability measures. -/
structure Var (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with each probability measure. -/
  eval : QuasiBorelHom ℝ A
  /-- The family of base `ProbabilityMeasures`. -/
  base : ℝ → ProbabilityMeasure ℝ
  /-- The family of base measures is measurable. -/
  measurable_base : Measurable base := by fun_prop


-- @@ L295-295 verbatim
namespace Var


-- @@ L297-297 verbatim
attribute [fun_prop] measurable_base


-- @@ L299-301 verbatim
/-- Evaluates a `Var`. -/
def apply : Var A → ℝ → PreProbabilityMeasure A
  | ⟨φ, μ, _⟩, r => ⟨φ, μ r⟩


-- @@ L303-304 verbatim
@[simp]
alias measureOf_mk := apply.eq_1


-- @@ L306-307 verbatim
instance : CoeFun (Var A) (fun _ ↦ ℝ → PreProbabilityMeasure A) where
  coe := apply


-- @@ L309-312 verbatim
/-- The constant variable. -/
def const (μ : PreProbabilityMeasure A) : Var A where
  eval := μ.eval
  base _ := μ.base


-- @@ L314-315 verbatim
@[simp]
lemma apply_const (μ : PreProbabilityMeasure A) (r : ℝ) : apply (const μ) r = μ := rfl


-- @@ L317-320 verbatim
/-- Precomposition of variables by measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) : Var A where
  eval := φ.eval
  base r := φ.base (f r)


-- @@ L322-326 verbatim
@[simp]
lemma apply_comp
    {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) (r : ℝ)
    : apply (comp hf φ) r = apply φ (f r) :=
  rfl


-- @@ L328-351 verbatim
/-- Gluing of a countable number of variables. -/
noncomputable def cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) : Var A where
  eval := {
    toFun r := (φ (unpack r : ℕ × ℝ).1).eval (unpack r : ℕ × ℝ).2
    property := by
      apply isHom_cases
          (ix := fun r ↦ (unpack r : ℕ × ℝ).1)
          (f := fun n r ↦ (φ n).eval (unpack r : ℕ × ℝ).2)
      · fun_prop
      · fun_prop
  }
  base r := ((φ (ix r)).base r).map (fun x ↦ pack (ix r, x))
  measurable_base := by
    apply measurable_cases (f := fun n r ↦
        ((φ n).base r).map (fun x ↦ pack (n, x)))
    · exact hix
    · intro i
      apply Measurable.subtype_mk
      apply Measure.measurable_map'
      · fun_prop
      · apply Measurable.subtype_val
        fun_prop


-- @@ L353-370 verbatim
lemma apply_cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) (r : ℝ)
    : apply (cases hix φ) r ≈ φ (ix r) r := by
  simp only [cases, measureOf_mk, equiv_def, lintegral_mk, QuasiBorelHom.coe_mk]
  intro f hf
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [lintegral_map]
  · simp only [unpack_pack]
    simp only [lintegral, apply]
  · apply measurable_cases (f := fun n r ↦ f ((φ n).eval (unpack r : ℕ × ℝ).2))
    · fun_prop
    · intro i
      apply Measurable.fun_comp (g := fun r ↦ f _) (f := fun r ↦ (unpack r : ℕ × ℝ).2)
      · apply measurable_of_isHom
        fun_prop
      · fun_prop
  · fun_prop


-- @@ L372-372 verbatim
end Var


-- @@ L374-393 verbatim
instance : QuasiBorelSpace (PreProbabilityMeasure A) where
  IsVar φ := ∃(ψ : Var A), ∀r, φ r ≈ ψ r
  isVar_const μ := by
    use Var.const μ
    simp only [Var.apply_const, Setoid.refl, implies_true]
  isVar_comp hf := by
    rintro ⟨μ, hμ⟩
    use Var.comp hf μ
    simp only [Var.apply_comp]
    intro r
    apply hμ
  isVar_cases' hix hφ := by
    choose φ hφ using hφ
    use Var.cases hix φ
    simp only
    intro r
    trans
    · apply hφ
    · symm
      apply Var.apply_cases


-- @@ L395-398 verbatim
@[local simp]
lemma isHom_def (φ : ℝ → PreProbabilityMeasure A) : IsHom φ ↔ ∃(ψ : Var A), ∀r, φ r ≈ ψ r := by
  rw [← isVar_iff_isHom]
  rfl


-- @@ L400-400 verbatim
namespace Var


-- @@ L402-406 verbatim
@[simp, fun_prop]
lemma isHom_apply (φ : Var A) : IsHom φ.apply := by
  simp only [isHom_def]
  use φ
  simp only [Setoid.refl, implies_true]


-- @@ L408-408 verbatim
end Var


-- @@ L410-415 expanded
/-- The variable associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subeval (φ : ℝ → PreProbabilityMeasure A) : QuasiBorelHom ℝ A :=
  open Classical in
    if hφ : IsHom φ then (Classical.choose ((isVar_iff_isHom _).2 hφ)).eval
    else .mk fun _ ↦ Classical.choice ((φ 0).nonempty)


-- @@ L417-422 verbatim
/-- The measure associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subbase (φ : ℝ → PreProbabilityMeasure A) : ℝ → ProbabilityMeasure ℝ :=
  open Classical in
  if hφ : IsHom φ
  then (Classical.choose ((isVar_iff_isHom _).2 hφ)).base
  else fun _ ↦ default


-- @@ L424-429 verbatim
@[simp, fun_prop]
lemma measurable_subbase (φ : ℝ → PreProbabilityMeasure A) : Measurable (subbase φ) := by
  by_cases hφ : IsHom φ
  · simp only [subbase, hφ, ↓reduceDIte]
    apply (Classical.choose ((isVar_iff_isHom _).2 hφ)).measurable_base
  · simp only [subbase, hφ, ↓reduceDIte, measurable_const]


-- @@ L431-435 verbatim
lemma sub_eq
    {φ : ℝ → PreProbabilityMeasure A} (hφ : IsHom φ)
    : ∀r, φ r ≈ .mk (subeval φ) (subbase φ r) := by
  simp only [subeval, hφ, ↓reduceDIte, subbase]
  exact Classical.choose_spec ((isVar_iff_isHom _).2 hφ)


-- @@ L437-474 verbatim
@[fun_prop]
lemma isHom_lintegral
    {k : A → B → ENNReal} (hk : IsHom fun (x, y) ↦ k x y)
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    : IsHom (fun x ↦ lintegral (k x) (f x)) := by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  simp only [lintegral, isHom_ofMeasurableSpace]
  have {r} := sub_eq (hf hφ) r (f := k (φ r)) (by fun_prop)
  simp only [lintegral] at this
  simp only [this]
  let κ : ProbabilityTheory.Kernel ℝ ℝ := {
    toFun x := ↑(subbase (fun x ↦ f (φ x)) x)
    measurable' := by
      apply Measurable.subtype_val
      fun_prop
  }
  have : ProbabilityTheory.IsFiniteKernel κ := by
    constructor
    use 1
    refine ⟨ENNReal.one_lt_top, fun a ↦ ?_⟩
    change (subbase (fun x ↦ f (φ x)) a : Measure ℝ) Set.univ ≤ 1
    simp
  have κ_apply (x : ℝ) : κ x = ↑(subbase (fun x ↦ f (φ x)) x) := rfl
  have hmeas : Measurable fun x ↦
      ∫⁻ y, k (φ x) ((subeval fun x ↦ f (φ x)) y) ∂κ x := by
    apply Measurable.lintegral_kernel_prod_left
    unfold Function.uncurry
    dsimp only
    replace hk := hk
      (φ := fun r ↦
        (φ (unpack r : ℝ × ℝ).2, ((subeval fun x ↦ f (φ x)) (unpack r : ℝ × ℝ).1)))
      (by fun_prop)
    simp only [isHom_ofMeasurableSpace] at hk
    have := Measurable.fun_comp hk (by fun_prop : Measurable (pack (A := ℝ × ℝ)))
    simp only [unpack_pack] at this
    exact this
  simpa only [κ_apply] using hmeas


-- @@ L476-481 verbatim
@[gcongr]
lemma lintegral_congr
    {k : A → ENNReal} (hk : IsHom k)
    {μ₁ μ₂ : PreProbabilityMeasure A} (hμ : μ₁ ≈ μ₂)
    : lintegral k μ₁ = lintegral k μ₂ := by
  apply hμ hk


-- @@ L483-489 verbatim
@[gcongr]
lemma measureOf_congr
    {p : Set A} (hk : IsHom (· ∈ p))
    {μ₁ μ₂ : PreProbabilityMeasure A} (hμ : μ₁ ≈ μ₂)
    : measureOf μ₁ p = measureOf μ₂ p := by
  rw [equiv_def'] at hμ
  apply hμ hk


-- @@ L491-501 verbatim
@[gcongr]
lemma isHom_congr {f g : A → PreProbabilityMeasure B} (h : ∀ x, f x ≈ g x) : IsHom f ↔ IsHom g := by
  apply Iff.intro <;>
  · intro h'
    rw [QuasiBorelSpace.isHom_def] at ⊢ h'
    simp only [isHom_def] at ⊢ h'
    intro ψ hψ
    rcases h' hψ with ⟨φ, hφ⟩
    use φ
    intro r
    grw [←hφ r, h]


-- @@ L503-506 verbatim
/-- The unit operation, a.k.a. the dirac measure. -/
noncomputable def unit (x : A) : PreProbabilityMeasure A where
  eval := .mk (fun _ ↦ x)
  base := default


-- @@ L508-512 verbatim
@[simp]
lemma lintegral_unit (f : A → ENNReal) (x : A) : lintegral f (unit x) = f x := by
  simp only [
    unit, lintegral_mk, QuasiBorelHom.coe_mk,
    MeasureTheory.lintegral_const, measure_univ, mul_one]


-- @@ L514-514 verbatim
namespace Var


-- @@ L516-522 verbatim
/-- The dirac measure, lifted to variables. -/
noncomputable def unit {φ : ℝ → A} (hφ : IsHom φ) : Var A where
  eval := .mk φ hφ
  base := diracProba
  measurable_base := by
    apply Measurable.subtype_mk
    fun_prop


-- @@ L524-531 verbatim
@[simp]
lemma apply_unit
    {φ : ℝ → A} (hφ : IsHom φ) (r : ℝ)
    : apply (unit hφ) r ≈ PreProbabilityMeasure.unit (φ r) := by
  intro ψ hψ
  rw [PreProbabilityMeasure.lintegral_unit]
  rw [show apply (unit hφ) r = ⟨⟨φ, hφ⟩, diracProba r⟩ by rfl]
  simp [lintegral, diracProba]


-- @@ L533-533 verbatim
end Var


-- @@ L535-543 verbatim
@[fun_prop]
lemma isHom_unit : IsHom (unit (A := A)) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  use Var.unit hφ
  intro r
  symm
  simp only [Var.apply_unit]


-- @@ L545-550 verbatim
/-- The monadic bind operation for probability measures. -/
noncomputable def bind
    (f : A → PreProbabilityMeasure B) (μ : PreProbabilityMeasure A)
    : PreProbabilityMeasure B where
  eval := subeval (f ∘ μ.eval)
  base := ProbabilityMeasure.bind μ.base (subbase (f ∘ μ.eval))


-- @@ L552-568 verbatim
@[simp]
lemma lintegral_bind
    {f : B → ENNReal} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral f (bind g μ) = lintegral (fun x ↦ lintegral f (g x)) μ := by
  simp only [lintegral, bind]
  rw [ProbabilityMeasure.lintegral_bind]
  · have : IsHom (g ∘ μ.eval) := by fun_prop
    congr 1
    ext r
    replace := sub_eq this r hf
    simp only [lintegral, Function.comp_apply] at this
    rw [this]
  · fun_prop
  · apply measurable_of_isHom
    fun_prop


-- @@ L570-588 verbatim
@[gcongr]
lemma bind_congr
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (h₁ : ∀ x, f x ≈ g x)
    {μ ν : PreProbabilityMeasure A} (h₂ : μ ≈ ν)
    : bind f μ ≈ bind g ν := by
  intro k hk
  rw [lintegral_bind, lintegral_bind]
  · trans
    · apply h₂
      fun_prop
    · congr
      ext x
      apply h₁ x hk
  · exact hk
  · exact hg
  · exact hk
  · exact hf


-- @@ L590-590 verbatim
namespace Var


-- @@ L592-595 verbatim
/-- The monadic bind, lifted to variables. -/
noncomputable def bind (f : A → PreProbabilityMeasure B) (φ : Var A) : Var B where
  eval := subeval fun x ↦ f (φ.eval x)
  base := fun r ↦ (φ.base r).bind (subbase fun x ↦ f (φ.eval x))


-- @@ L597-610 verbatim
lemma apply_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) (φ : Var A) (r : ℝ)
    : apply (bind f φ) r ≈ PreProbabilityMeasure.bind f (φ r) := by
  intro k hk
  simp only [bind, measureOf_mk, lintegral_mk]
  rw [lintegral_bind, ProbabilityMeasure.lintegral_bind]
  · congr 1
    ext x
    have : IsHom (fun x ↦ f (φ.eval x)) := by fun_prop
    simp only [sub_eq this x hk, lintegral_mk]
  · fun_prop
  · apply measurable_of_isHom
    fun_prop
  · fun_prop
  · fun_prop


-- @@ L612-612 verbatim
end Var


-- @@ L614-622 verbatim
@[fun_prop]
lemma isHom_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) : IsHom (bind f) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ ⟨ψ, hψ⟩
  use Var.bind f ψ
  intro r
  grw [Var.apply_bind, hψ]
  · fun_prop


-- @@ L624-627 verbatim
/-- The functorial `str`ength operation. -/
def str (x : A) (μ : PreProbabilityMeasure B) : PreProbabilityMeasure (A × B) where
  eval := .mk fun r ↦ (x, μ.eval r)
  base := μ.base


-- @@ L629-634 verbatim
@[simp]
lemma lintegral_str
    (k : A × B → ENNReal)
    (x : A) (μ : PreProbabilityMeasure B)
    : lintegral k (str x μ) = lintegral (fun y ↦ k (x, y)) μ := by
  simp only [lintegral, str, QuasiBorelHom.coe_mk]


-- @@ L636-641 verbatim
@[gcongr]
lemma str_congr (x : A) {μ₁ μ₂ : PreProbabilityMeasure B} (hμ : μ₁ ≈ μ₂) : str x μ₁ ≈ str x μ₂ := by
  intro k hk
  simp only [lintegral_str]
  apply hμ
  fun_prop


-- @@ L643-643 verbatim
namespace Var


-- @@ L645-654 verbatim
/-- The functorial `str`ength operation, lifted to variables. -/
noncomputable def str {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) : Var (A × B) where
  eval := .mk fun r ↦ (φ (unpack r : ℝ × ℝ).1, ψ.eval (unpack r : ℝ × ℝ).2)
  base r := (ψ r).base.map (fun x ↦ pack (r, x))
  measurable_base := by
    apply Measurable.subtype_mk
    apply Measure.measurable_map'
    · fun_prop
    · apply Measurable.subtype_val
      fun_prop


-- @@ L656-668 verbatim
lemma apply_str
    {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) (r : ℝ)
    : apply (str hφ ψ) r ≈ PreProbabilityMeasure.str (φ r) (ψ r) := by
  intro χ hχ
  rw [PreProbabilityMeasure.lintegral_str]
  change lintegral χ (apply (str hφ ψ) r) = _
  simp only [str, apply, lintegral, ProbabilityMeasure.toMeasure_map, QuasiBorelHom.coe_mk]
  rw [MeasureTheory.lintegral_map]
  · rcases ψ
    simp only [unpack_pack]
  · apply measurable_of_isHom
    fun_prop
  · fun_prop


-- @@ L670-670 verbatim
end Var


-- @@ L672-680 verbatim
@[fun_prop, simp]
lemma isHom_str : IsHom (fun x : A × PreProbabilityMeasure B ↦ str x.1 x.2) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp, forall_exists_index]
  intro φ hφ ψ hψ
  have : IsHom (fun x ↦ (φ x).1) := by fun_prop
  use Var.str this ψ
  intro r
  grw [Var.apply_str, hψ]


-- @@ L682-703 verbatim
/-- The Bernoulli measure. -/
noncomputable def coin (p : I) : PreProbabilityMeasure Bool where
  eval := {
    toFun := fun r ↦ r = 0
    property := by
      apply Prop.isHom_decide
      simp only [isHom_ofMeasurableSpace]
      change Measurable fun x ↦ x ∈ ({0} : Set ℝ)
      simp only [measurable_mem, MeasurableSet.singleton]
  }
  base := {
    val :=
      ENNReal.ofReal p • Measure.dirac 0 +
      ENNReal.ofReal (σ p) • Measure.dirac 1
    property := by
      constructor
      rcases p with ⟨p, hp⟩
      simp only [Set.mem_Icc] at hp
      simp only [unitInterval.coe_symm_eq, hp, ENNReal.ofReal_sub, ENNReal.ofReal_one,
        Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul,
        mul_one, ENNReal.ofReal_le_one, add_tsub_cancel_of_le]
  }


-- @@ L705-711 verbatim
@[simp]
lemma lintegral_coin
    (k : Bool → ENNReal) (p : I)
    : lintegral k (coin p) = ENNReal.ofReal p * k true + ENNReal.ofReal (1 - p) * k false := by
  change (∫⁻ r : ℝ, k ((coin p).eval r) ∂(coin p).base) = _
  simp only [coin]
  simp


-- @@ L713-713 verbatim
end QuasiBorelSpace.PreProbabilityMeasure
