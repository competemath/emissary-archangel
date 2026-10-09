import OAI.Analysis.Unitarizability.Cocycle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-8 verbatim
/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace Dixmier

-- @@ L11-11 verbatim
namespace HilbertSum

-- @@ L12-12 verbatim
variable {G I : Type*} [Group G] {E : I → Type*}

-- @@ L13-13 verbatim
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

-- @@ L14-14 verbatim
local instance : DecidableEq I := Classical.decEq I

-- @@ L15-15 verbatim
abbrev Space (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] := lp E 2


-- @@ L17-17 verbatim
def inclusion (i : I) : E i →L[ℂ] Space E := lp.singleContinuousLinearMap ℂ E 2 i


-- @@ L19-19 verbatim
def evaluation (i : I) : Space E →L[ℂ] E i := lp.evalCLM ℂ E 2 i


-- @@ L21-21 verbatim
@[simp] theorem inclusion_apply (i : I) (x : E i) : inclusion i x = lp.single 2 i x := rfl

-- @@ L22-22 verbatim
@[simp] theorem evaluation_apply (i : I) (x : Space E) : evaluation i x = x i := rfl


-- @@ L24-25 verbatim
def boundedSum (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ} (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) :
    Space E →L[ℂ] Space E := lp.mapCLM 2 T hκ hT


-- @@ L27-29 verbatim
@[simp] theorem boundedSum_apply (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) (x : Space E) (i : I) :
    boundedSum T hκ hT x i = T i (x i) := rfl


-- @@ L31-33 verbatim
theorem boundedSum_norm_le (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) : ‖boundedSum T hκ hT‖ ≤ κ :=
  lp.norm_mapCLM_le 2 T hκ hT


-- @@ L35-40 verbatim
theorem unitary_bound {index : I} (U : G →* (E index →L[ℂ] E index))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) :
    ‖U g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [hU]


-- @@ L42-49 verbatim
def representation (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) : G →* (Space E →L[ℂ] Space E) where
  toFun g := boundedSum (fun i => U i g) zero_le_one (fun i => unitary_bound (U i) (hU i) g)
  map_one' := by ext x i; change U i 1 (x i) = x i; simp
  map_mul' g h := by
    ext x i
    change U i (g*h) (x i) = U i g (U i h (x i))
    rw [map_mul]; rfl


-- @@ L51-53 verbatim
@[simp] theorem representation_apply (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) (i : I) :
    representation U hU g x i = U i g (x i) := rfl


-- @@ L55-62 verbatim
theorem representation_norm_map (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) :
    ‖representation U hU g x‖ = ‖x‖ := by
  have hs : ‖representation U hU g x‖^2 = ‖x‖^2 := by
    have norm_sq (y : Space E) : ‖y‖^2 = ∑' i, ‖y i‖^2 := by
      simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) y
    simp only [norm_sq, representation_apply, hU]
  nlinarith [norm_nonneg (representation U hU g x), norm_nonneg x]


-- @@ L64-66 verbatim
def cocycle (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) : Space E →L[ℂ] Space E :=
  boundedSum (fun i => D i g) hκ (fun i => hb i g)


-- @@ L68-71 verbatim
omit [Group G] in
@[simp] theorem cocycle_apply (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) (x : Space E) (i : I) :
    cocycle D hκ hb g x i = D i g (x i) := rfl


-- @@ L73-75 verbatim
theorem cocycle_one (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (h1 : ∀ i, D i 1 = 0) :
    cocycle D hκ hb 1 = 0 := by ext x i; simp [h1]


-- @@ L77-86 verbatim
theorem cocycle_identity (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ)
    (hD : ∀ i g h, D i (g*h) = D i g + conjugate (U i) g (D i h)) (g h : G) :
    cocycle D hκ hb (g*h) = cocycle D hκ hb g +
      conjugate (representation U hU) g (cocycle D hκ hb h) := by
  ext x i
  change D i (g*h) (x i) = D i g (x i) + U i g (D i h (U i g⁻¹ (x i)))
  rw [hD]
  rfl


-- @@ L88-94 verbatim
theorem representation_inclusion (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (i : I) (x : E i) :
    representation U hU g (inclusion i x) = inclusion i (U i g x) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]


-- @@ L96-97 verbatim
def compression (B : Space E →L[ℂ] Space E) (i : I) : E i →L[ℂ] E i :=
  (evaluation i).comp (B.comp (inclusion i))


-- @@ L99-106 verbatim
theorem compression_norm_le (B : Space E →L[ℂ] Space E) (i : I) : ‖compression B i‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖B (lp.single 2 i x) i‖ ≤ ‖B‖ * ‖x‖
  calc
    _ ≤ ‖B (lp.single 2 i x)‖ := lp.norm_apply_le_norm (by norm_num) _ i
    _ ≤ ‖B‖ * ‖lp.single 2 i x‖ := B.le_opNorm _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]


-- @@ L108-115 verbatim
theorem compression_conjugate (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (B : Space E →L[ℂ] Space E) (i : I) (g : G) :
    compression (conjugate (representation U hU) g B) i =
      conjugate (U i) g (compression B i) := by
  ext x
  change (representation U hU g (B (representation U hU g⁻¹ (inclusion i x)))) i = _
  rw [representation_inclusion, representation_apply]
  rfl


-- @@ L117-129 verbatim
theorem compression_implementer (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (B : Space E →L[ℂ] Space E)
    (hB : ∀ g, cocycle D hκ hb g = coboundary (representation U hU) B g) (i : I) (g : G) :
    D i g = coboundary (U i) (compression B i) g := by
  have h := congrArg (fun T => compression T i) (hB g)
  have hc : compression (cocycle D hκ hb g) i = D i g := by
    ext x
    change D i g (lp.single 2 i x i) = D i g x
    rw [lp.single_apply_self]
  have hs (A C : Space E →L[ℂ] Space E) : compression (A-C) i = compression A i - compression C i := by
    ext x; rfl
  rwa [hc, coboundary, hs, compression_conjugate] at h



-- @@ L132-151 verbatim
/-- Countably many separable fibres have a separable Hilbert sum. The proof
uses the dense span of coordinate inclusions and convergence of finite sums. -/
theorem separableSpace [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by
  let s : Set (Space E) := ⋃ i, Set.range (inclusion (E := E) i)
  let V : Submodule ℂ (Space E) := Submodule.span ℂ s
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (inclusion (E := E) i).continuous)
  have hv : TopologicalSpace.IsSeparable (V : Set (Space E)) := hs.span
  have hd : Dense (V : Set (Space E)) := by
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro F
    apply subset_closure
    apply V.sum_mem
    intro i hi
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x i, rfl⟩⟩)
  exact hd.isSeparable_iff.mp hv



-- @@ L154-154 verbatim
end HilbertSum

-- @@ L155-155 verbatim
end Dixmier


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
