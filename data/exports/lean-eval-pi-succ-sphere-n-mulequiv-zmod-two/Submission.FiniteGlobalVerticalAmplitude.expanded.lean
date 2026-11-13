import Mathlib
import Submission.MorsePerturb


-- @@ L4-18 verbatim
/-!
# A single small vertical amplitude from finitely many local jets

Local Morse modifications are useful only after they have been assembled into
one ambient map.  This file performs the analytic part of that assembly.  A
finite sum of smooth, compactly supported, collar-zero scalar amplitudes has
the same three properties, and hence admits the common small scaling supplied
by `SmallVerticalAmplitude.exists_scaled`.

The optional `core` and `noninterference` hypotheses record the exact local
content of the construction: on a core owned by one index, every other raw
amplitude vanishes, so the global sum agrees there with the owner's raw jet.
Thus the resulting small amplitude installs all local jets with one and the
same positive scale.
-/


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace ContDiff Topology BigOperators


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {n : ℕ}


-- @@ L29-29 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L31-31 verbatim
namespace FiniteGlobalVerticalAmplitude


-- @@ L33-33 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L35-37 verbatim
/-- The pointwise sum of a finite family of raw scalar amplitudes. -/
def totalRaw (raw : ι → E' → ℝ) : E' → ℝ :=
  ∑ i, raw i


-- @@ L39-47 verbatim
theorem contDiff_totalRaw (raw : ι → E' → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i)) :
    ContDiff ℝ ∞ (totalRaw raw) := by
  classical
  have heq : totalRaw raw = fun v => ∑ i, raw i v := by
    funext v
    simp [totalRaw]
  rw [heq]
  exact ContDiff.sum (s := Finset.univ) (fun i _ => hsmooth i)


-- @@ L49-58 verbatim
theorem hasCompactSupport_totalRaw (raw : ι → E' → ℝ)
    (hsupp : ∀ i, HasCompactSupport (raw i)) :
    HasCompactSupport (totalRaw raw) := by
  classical
  unfold totalRaw
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (HasCompactSupport.zero :
      HasCompactSupport (0 : E' → ℝ))
  | @insert i s hi ih =>
      simpa [Finset.sum_insert hi] using (hsupp i).add ih


-- @@ L60-84 verbatim
/-- Lipschitz constants add under finite global assembly. -/
theorem lipschitzWith_totalRaw (raw : ι → E' → ℝ) (K : ι → NNReal)
    (hlip : ∀ i, LipschitzWith (K i) (raw i)) :
    LipschitzWith (∑ i, K i) (totalRaw raw) := by
  classical
  unfold totalRaw
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have heq : raw i + ∑ j ∈ s, raw j =
          (fun v => raw i v + ∑ j ∈ s, raw j v) := by
        funext v
        simp
      have heqTail : (∑ j ∈ s, raw j) =
          (fun v => ∑ j ∈ s, raw j v) := by
        funext v
        simp
      have ih' : LipschitzWith (∑ j ∈ s, K j)
          (fun v => ∑ j ∈ s, raw j v) := by
        rw [← heqTail]
        exact ih
      rw [heq]
      exact (hlip i).add ih'


-- @@ L86-93 verbatim
theorem totalRaw_collar_zero (raw : ι → E' → ℝ)
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0) :
    ∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → totalRaw raw v = 0 := by
  classical
  intro v hv
  rw [totalRaw, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hcollar i v hv)


-- @@ L95-110 verbatim
/-- On an owned core the global raw sum is literally the owner's raw jet. -/
theorem totalRaw_eq_on_core (raw : ι → E' → ℝ) (core : ι → Set E')
    (noninterference : ∀ i v, v ∈ core i → ∀ j, j ≠ i → raw j v = 0)
    (i : ι) {v : E'} (hv : v ∈ core i) :
    totalRaw raw v = raw i v := by
  classical
  rw [totalRaw, Finset.sum_apply]
  calc
    ∑ j, raw j v = ∑ j, if j = i then raw i v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, noninterference i v hv j hji]
    _ = raw i v := by simp


-- @@ L112-136 verbatim
/-- If the unscaled finite sum already has Lipschitz constant below one, it is
itself a `SmallVerticalAmplitude`.  This is the exact-installation form needed
when the generic local jets have been chosen quantitatively small. -/
def ofLipschitzTotal
    (raw : ι → E' → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (K : NNReal) (hK : K < 1)
    (hlip : LipschitzWith K (totalRaw raw)) :
    SmallVerticalAmplitude (n := n) := by
  have hsmoothTotal := contDiff_totalRaw raw hsmooth
  have hsmall : ∀ v, ‖fderiv ℝ (totalRaw raw) v‖ < 1 := by
    intro v
    have hderiv : ‖fderiv ℝ (totalRaw raw) v‖ ≤ (K : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hlip
    have hKreal : (K : ℝ) < 1 := by exact_mod_cast hK
    exact hderiv.trans_lt hKreal
  exact {
    toVerticalAmplitude := VerticalAmplitude.ofNormFDerivLtOne
      (totalRaw raw) hsmoothTotal (totalRaw_collar_zero raw hcollar) hsmall
    K := K
    K_lt_one := hK
    lipschitz := hlip
  }


-- @@ L138-146 verbatim
@[simp] theorem ofLipschitzTotal_apply
    (raw : ι → E' → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (K : NNReal) (hK : K < 1)
    (hlip : LipschitzWith K (totalRaw raw)) (v : E') :
    ofLipschitzTotal raw hsmooth hcollar K hK hlip v = totalRaw raw v :=
  rfl


-- @@ L148-161 verbatim
/-- The exact unscaled global installation agrees with each local owner on its
core. -/
theorem ofLipschitzTotal_eq_on_core
    (raw : ι → E' → ℝ) (core : ι → Set E')
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (noninterference : ∀ i v, v ∈ core i → ∀ j, j ≠ i → raw j v = 0)
    (K : NNReal) (hK : K < 1)
    (hlip : LipschitzWith K (totalRaw raw))
    (i : ι) {v : E'} (hv : v ∈ core i) :
    ofLipschitzTotal raw hsmooth hcollar K hK hlip v = raw i v := by
  rw [ofLipschitzTotal_apply]
  exact totalRaw_eq_on_core raw core noninterference i hv


-- @@ L163-174 verbatim
/-- A convenient quantitative constructor: it is enough to bound every local
jet separately and make the finite sum of those bounds smaller than one. -/
def ofFiniteLipschitz
    (raw : ι → E' → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (K : ι → NNReal) (hK : (∑ i, K i) < 1)
    (hlip : ∀ i, LipschitzWith (K i) (raw i)) :
    SmallVerticalAmplitude (n := n) :=
  ofLipschitzTotal raw hsmooth hcollar (∑ i, K i) hK
    (lipschitzWith_totalRaw raw K hlip)


-- @@ L176-184 verbatim
@[simp] theorem ofFiniteLipschitz_apply
    (raw : ι → E' → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (K : ι → NNReal) (hK : (∑ i, K i) < 1)
    (hlip : ∀ i, LipschitzWith (K i) (raw i)) (v : E') :
    ofFiniteLipschitz raw hsmooth hcollar K hK hlip v = totalRaw raw v :=
  rfl


-- @@ L186-197 verbatim
theorem ofFiniteLipschitz_eq_on_core
    (raw : ι → E' → ℝ) (core : ι → Set E')
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (noninterference : ∀ i v, v ∈ core i → ∀ j, j ≠ i → raw j v = 0)
    (K : ι → NNReal) (hK : (∑ i, K i) < 1)
    (hlip : ∀ i, LipschitzWith (K i) (raw i))
    (i : ι) {v : E'} (hv : v ∈ core i) :
    ofFiniteLipschitz raw hsmooth hcollar K hK hlip v = raw i v := by
  rw [ofFiniteLipschitz_apply]
  exact totalRaw_eq_on_core raw core noninterference i hv


-- @@ L199-218 verbatim
/-- A finite compatible family of local raw jets produces one global small
vertical amplitude.  The positive scale is common to every installed core. -/
theorem exists_small_of_finite
    (raw : ι → E' → ℝ) (core : ι → Set E')
    (hsmooth : ∀ i, ContDiff ℝ ∞ (raw i))
    (hsupp : ∀ i, HasCompactSupport (raw i))
    (hcollar : ∀ i v,
      tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v → raw i v = 0)
    (noninterference : ∀ i v, v ∈ core i → ∀ j, j ≠ i → raw j v = 0) :
    ∃ ε > 0, ∃ a : SmallVerticalAmplitude (n := n),
      a.toFun = (fun v => ε * totalRaw raw v) ∧
      ∀ i v, v ∈ core i → a v = ε * raw i v := by
  obtain ⟨ε, hε, a, ha⟩ := SmallVerticalAmplitude.exists_scaled
    (totalRaw raw) (contDiff_totalRaw raw hsmooth)
      (hasCompactSupport_totalRaw raw hsupp)
      (totalRaw_collar_zero raw hcollar)
  refine ⟨ε, hε, a, ha, ?_⟩
  intro i v hv
  rw [show a.toFun v = ε * totalRaw raw v by rw [ha]]
  rw [totalRaw_eq_on_core raw core noninterference i hv]


-- @@ L220-220 verbatim
end FiniteGlobalVerticalAmplitude


-- @@ L222-222 verbatim
end Submission
