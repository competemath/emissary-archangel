/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Order.Filter.Ring
import Mathlib.Tactic.Cases
import Mathlib.Topology.Germ


-- @@ L15-20 verbatim
/-!
## Germs of smooth functions
under construction: might need further refactoring to be usable!
-/

-- TODO: please confirm authorship and copyright are appropriate


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Filter Set


-- @@ L26-28 verbatim
open scoped Manifold Topology ContDiff

-- FIXME: move to `Manifold/Algebra/SmoothFunctions`, around line 46

-- @@ L29-29 verbatim
section


-- @@ L31-39 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' ∞ G]


-- @@ L41-44 verbatim
@[to_additive]
theorem SmoothMap.coe_prod {ι : Type*} (f : ι → C^∞⟮I, N; I', G⟯) (s : Finset ι) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, ⇑(f i) :=
  map_prod (ContMDiffMap.coeFnMonoidHom : C^∞⟮I, N; I', G⟯ →* N → G) f s


-- @@ L46-46 verbatim
end


-- @@ L48-48 verbatim
section


-- @@ L50-58 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Type*) [AddCommGroup G] [Module ℝ G]


-- @@ L60-62 verbatim
/-- The map `C^∞(N, ℝ) → Germ (𝓝 x) ℝ` as a ring homomorphism. -/
def RingHom.germOfContMDiffMap (x : N) : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ →+* Germ (𝓝 x) ℝ :=
  RingHom.comp (Germ.coeRingHom _) ContMDiffMap.coeFnRingHom


-- @@ L64-66 verbatim
/-- All germs of smooth functions `N → ℝ` at `x : N`, as a subring of `Germ (𝓝 x) ℝ`. -/
def smoothGerm (x : N) : Subring (Germ (𝓝 x) ℝ) :=
  (RingHom.germOfContMDiffMap I x).range


-- @@ L68-69 verbatim
instance (x : N) : Coe C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ (smoothGerm I x) :=
  ⟨fun f ↦ ⟨(f : N → ℝ), ⟨f, rfl⟩⟩⟩


-- @@ L71-74 verbatim
@[simp]
theorem smoothGerm.coe_coe (f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (x : N) :
    ((f : smoothGerm I x) : (𝓝 x).Germ ℝ) = (f : (𝓝 x).Germ ℝ) :=
  rfl


-- @@ L76-79 verbatim
@[simp]
theorem smoothGerm.coe_sum {ι} (f : ι → C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (s : Finset ι) (x : N) :
    ((∑ i ∈ s, f i : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) : smoothGerm I x) = ∑ i ∈ s, (f i : smoothGerm I x) :=
  map_sum (RingHom.rangeRestrict (RingHom.germOfContMDiffMap I x)) f s


-- @@ L81-86 verbatim
@[simp]
theorem smoothGerm.coe_eq_coe (f g : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) {x : N} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I x) = (g : smoothGerm I x) := by
  ext
  apply Quotient.sound
  exact h


-- @@ L88-88 verbatim
example (x : N) : Module (smoothGerm I x) (Germ (𝓝 x) G) := by infer_instance


-- @@ L90-139 verbatim
example (x : N) : Module (Germ (𝓝 x) ℝ) (Germ (𝓝 x) F) := by infer_instance

-- def linear_map.germ_of_cont_mdiff_map (x : N) :
--   C^∞⟮I, N; 𝓘(ℝ, F), F⟯ →ₛₗ[(germ.coe_ring_hom (𝓝 x) : (N → ℝ) →+*
--    germ (𝓝 x) ℝ).comp (pi.const_ring_hom N ℝ)] germ (𝓝 x) F :=
-- sorry -- linear_map.comp (germ.coe_linear_map _) smooth_map.coe_fn_linear_map
/-
def smooth_germ_vec (x : N) : submodule (smooth_germ I x) (germ (𝓝 x) F) :=
-- linear_map.range (linear_map.germ_of_cont_mdiff_map I F x)
{ carrier := {φ : germ (𝓝 x) F | ∃ f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, φ = (f : N → F)},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

instance (x : N) : has_coe C^∞⟮I, N; 𝓘(ℝ, F), F⟯ (smooth_germ_vec I F x) :=
⟨λ f, ⟨(f : N → F), ⟨f, rfl⟩⟩⟩

variables {I F}

@[elab_as_eliminator]
lemma smooth_germ_vec.induction_on {x : N} {P : germ (𝓝 x) F → Prop}
  (h : ∀ f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, P (f : N → F)) :
  ∀ φ ∈ smooth_germ_vec I F x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

@[elab_as_eliminator]
lemma smooth_germ.induction_on {x : N} {P : germ (𝓝 x) ℝ → Prop}
  (h : ∀ f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯, P (f : N → ℝ)) :
  ∀ φ ∈ smooth_germ I x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

-- We may also need versions of the above two lemmas for using the coe_to_sort
-- `∀ φ : smooth_germ I x`, maybe even a tactic, but let's wait to see if they are really needed.

lemma convex_smooth_germ_vec (x : N) : convex (smooth_germ I x)
  (smooth_germ_vec I F x : Set $ germ (𝓝 x) F) :=
begin
  refine smooth_germ_vec.induction_on _,
  intros f,
  refine smooth_germ_vec.induction_on _,
  rintros g ⟨_, ⟨b, rfl⟩⟩ ⟨_, ⟨c, rfl⟩⟩ hb hc hbc,
  exact ⟨b • f + c • g, rfl⟩,
end
-/

-- @@ L140-140 verbatim
end


-- @@ L142-142 verbatim
section


-- @@ L144-144 verbatim
variable {ι : Type*}


-- @@ L146-148 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]


-- @@ L150-150 verbatim
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L152-154 verbatim
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type*} [TopologicalSpace N] [ChartedSpace HG N]
  [IsManifold IG ∞ N]


-- @@ L156-157 verbatim
def smoothGerm.valueOrderRingHom (x : N) : smoothGerm IG x →+*o ℝ :=
  Filter.Germ.valueOrderRingHom.comp <| Subring.orderedSubtype _


-- @@ L159-160 verbatim
def smoothGerm.valueRingHom (x : N) : smoothGerm IG x →+* ℝ :=
  Filter.Germ.valueRingHom.comp <| Subring.subtype _


-- @@ L162-165 verbatim
omit [IsManifold IG ∞ N] in
theorem smoothGerm.valueOrderRingHom_toRingHom (x : N) :
    (smoothGerm.valueOrderRingHom IG x).toRingHom = smoothGerm.valueRingHom IG x :=
  rfl


-- @@ L167-167 verbatim
namespace Filter.Germ


-- @@ L169-173 verbatim
def valueₛₗ {F} [AddCommMonoid F] [Module ℝ F] (x : N) :
    Germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom IG x] F :=
  { Filter.Germ.valueAddHom with
    toFun := Filter.Germ.value
    map_smul' := fun φ ψ ↦ (φ : Germ (𝓝 x) ℝ).value_smul ψ }


-- @@ L175-175 verbatim
variable (I)


-- @@ L177-182 verbatim
protected def ContMDiffAt' {x : M} (φ : Germ (𝓝 x) N) (n : WithTop ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ CMDiffAt n f x) fun f g h ↦
    propext <| by
      constructor
      all_goals refine fun H ↦ H.congr_of_eventuallyEq ?_
      exacts [h.symm, h]


-- @@ L184-189 verbatim
/-- The predicate selecting germs of `ContMDiffAt` functions.
TODO: merge with the next def that generalizes target space -/
protected nonrec def ContMDiffAt {x : M} (φ : Germ (𝓝 x) F) (n : WithTop ℕ∞) : Prop :=
  φ.ContMDiffAt' I 𝓘(ℝ, F) n

-- currently unused

-- @@ L190-194 verbatim
nonrec def mfderiv {x : M} (φ : Germ (𝓝 x) N) :
    TangentSpace% x →L[ℝ] TangentSpace% φ.value :=
  @Quotient.hrecOn _ (germSetoid (𝓝 x) N)
    (fun φ : Germ (𝓝 x) N ↦ TangentSpace% x →L[ℝ] TangentSpace% φ.value) φ
    (fun f ↦ mfderiv% f x) fun _f _g hfg ↦ heq_of_eq (EventuallyEq.mfderiv_eq hfg : _)


-- @@ L196-196 verbatim
variable {I}


-- @@ L198-198 verbatim
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]


-- @@ L200-203 verbatim
theorem _root_.smoothGerm.contMDiffAt {x : M} (φ : smoothGerm I x) {n : ℕ∞} :
    (φ : Germ (𝓝 x) ℝ).ContMDiffAt I n := by
  rcases φ with ⟨_, g, rfl⟩
  apply g.contMDiff.of_le (mod_cast le_top)


-- @@ L205-207 verbatim
protected nonrec theorem ContMDiffAt.add {x : M} {φ ψ : Germ (𝓝 x) F} {n : ℕ∞} :
    φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ + ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.add hg


-- @@ L209-211 verbatim
protected nonrec theorem ContMDiffAt.smul {x : M} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) F}
    {n : ℕ∞} : φ.ContMDiffAt I n → ψ.ContMDiffAt I n → (φ • ψ).ContMDiffAt I n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg ↦ hf.smul hg


-- @@ L213-221 verbatim
theorem ContMDiffAt.sum {x : M} {ι} {s : Finset ι} {n : ℕ∞} {f : ι → Germ (𝓝 x) F}
    (h : ∀ i ∈ s, (f i).ContMDiffAt I n) : (∑ i ∈ s, f i).ContMDiffAt I n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contMDiffAt_const
  | insert φ s hφs hs =>
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)


-- @@ L223-223 verbatim
end Filter.Germ


-- @@ L225-225 verbatim
end


-- @@ L227-227 verbatim
section


-- @@ L229-237 verbatim
variable {E₁ E₂ F H₁ M₁ H₂ M₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁]
  [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]


-- @@ L239-239 verbatim
open scoped Filter


-- @@ L241-241 verbatim
open Function


-- @@ L243-245 verbatim
namespace Filter.Germ

-- TODO: generalize the next def?

-- @@ L246-280 verbatim
def ContMDiffAtProd {x : M₁} (φ : Germ (𝓝 x) (M₂ → F)) (n : ℕ∞) : Prop :=
  Quotient.liftOn' φ (fun f ↦ ∀ y : M₂, ContMDiffAt (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y))
    fun f g h ↦ propext <| by
        change {x' | f x' = g x'} ∈ 𝓝 x at h
        constructor
        all_goals
          refine fun H y ↦ (H y).congr_of_eventuallyEq ?_
          clear H
          replace h : {x' | f x' = g x'} ×ˢ (univ : Set M₂) ∈ 𝓝 x ×ˢ 𝓝 y := prod_mem_prod h univ_mem
          rw [← nhds_prod_eq] at h
          apply mem_of_superset h
          rintro ⟨x', y'⟩ ⟨hx' : f x' = g x', -⟩
          simp only [mem_ofPred_eq, uncurry_apply_pair]
          apply congr_fun
        exacts [hx'.symm, hx']

/- potential generalization of the above.
note(grunweg): fixed some names for Lean 4, but not the core syntax
def contMDiffAt_comp {x : M₁} (φ : germ (𝓝 x) M₂) (n : ℕ∞)
  (g : M₂ → M₃) (h : M₄ → M₁) : Prop :=
quotient.lift_on' φ (λ f, ∀ y ∈ h⁻¹' {x}, ContMDiffAt I₄ I₃ n (g ∘ f ∘ h) y) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventuallyEq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : Set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_ofPred_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)
-/

-- @@ L281-281 verbatim
variable {I₁ I₂}


-- @@ L283-284 verbatim
omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁] [IsManifold I₂ ∞ M₂]


-- @@ L286-288 verbatim
theorem ContMDiffAtProd.add {x : M₁} {φ ψ : Germ (𝓝 x) <| M₂ → F} {n : ℕ∞} :
    φ.ContMDiffAtProd I₁ I₂ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ + ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦ (hf y).add (hg y)


-- @@ L290-293 verbatim
theorem ContMDiffAtProd.smul {x : M₁} {φ : Germ (𝓝 x) <| M₂ → ℝ}
    {ψ : Germ (𝓝 x) <| M₂ → F} {n : ℕ∞} :
    φ.ContMDiffAtProd I₁ I₂ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ • ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦ (hf y).smul (hg y)


-- @@ L295-298 verbatim
theorem ContMDiffAt.smul_prod {x : M₁} {φ : Germ (𝓝 x) ℝ} {ψ : Germ (𝓝 x) (M₂ → F)}
    {n : ℕ∞} : φ.ContMDiffAt I₁ n → ψ.ContMDiffAtProd I₁ I₂ n → (φ • ψ).ContMDiffAtProd I₁ I₂ n :=
  Germ.inductionOn φ fun _f hf ↦ Germ.inductionOn ψ fun _g hg y ↦
    .smul (.comp _ hf contMDiffAt_fst) (hg y)


-- @@ L300-311 verbatim
theorem ContMDiffAtProd.sum {x : M₁} {ι} {s : Finset ι} {n : ℕ∞}
    {f : ι → Germ (𝓝 x) (M₂ → F)} (h : ∀ i ∈ s, (f i).ContMDiffAtProd I₁ I₂ n) :
    (∑ i ∈ s, f i).ContMDiffAtProd I₁ I₂ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]; intro y
    exact contMDiffAt_const (x := (x, y)) (c := (0 : F))
  | insert φ s hφs hs =>
  simp only [Finset.mem_insert, forall_eq_or_imp] at h
  rw [Finset.sum_insert hφs]
  exact h.1.add (hs h.2)


-- @@ L313-313 verbatim
end Filter.Germ


-- @@ L315-315 verbatim
end
