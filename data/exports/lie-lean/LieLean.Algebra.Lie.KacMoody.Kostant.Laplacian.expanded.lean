/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Euler


-- @@ L8-54 verbatim
/-!
# Codifferentials and Laplacians on the Chevalley–Eilenberg complex

Let `L` be a Lie algebra and `M` an `L`-module over a commutative ring `R`. On the chains
`⋀L ⊗ M` we have the Chevalley–Eilenberg differential `d` (`LieModule.ChevalleyEilenberg.diff`),
characterized by `d(1 ⊗ m) = 0` and `d ∘ ε(y) = -θ(y) - ε(y) ∘ d`, where `ε(y)` is left
multiplication by `y ∈ L` and `θ(y)` the action of `y`. In the same way, given
* a linear map `δ₀ : M → ⋀L ⊗ M`, and
* a linear family `G(y)` of operators on `⋀L ⊗ M` with `G(y) ε(y) = ε(y) G(y)`,

there is a unique operator `δ` on `⋀L ⊗ M` with `δ(1 ⊗ m) = δ₀ m` and
`δ ∘ ε(y) = -G(y) - ε(y) ∘ δ` (`LieModule.ChevalleyEilenberg.coDiff`). This is the shape of
Kostant's coboundary operator, transported to `⋀𝔫₋ ⊗ V` ([Kostant 1961, Prop. 3.13, Lemma 4.1];
the `𝔫₋`-homology differential corresponds to its adjoint `d*`, Lemma 4.2): for `𝔫₋`-homology,
`δ₀ m = -∑ f_a ⊗ e_a m` and `G(y) = ½ ∑ ε(f_a) ε(π[e_a, y])` (see
`LieLean.Algebra.Lie.KacMoody.Kostant.Identity`).

We compute the commutation of the *Laplacian* `□ = dδ + δd` with the operators `ε(y)`:
`□ ε(y) = ε(y) □ + R(y)` with `R(y) = [θ(y), δ] - d G(y) + G(y) d` (`laplacian_wedge`), and, if
the `G(y)` commute with all `ε(z)`,
`R(y) ε(z) = -ε(z) R(y) + G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)]` (`laplacianComm_wedge`).
These reduce Kostant's identity to computations in degrees `0` and `1`. Finally, if `□` acts on
a cycle `c` of degree `k` by an invertible scalar, then `c` is a boundary, since
`c = d(s⁻¹ δ c)` (`mem_boundaries_of_laplacian_eq_smul`).

## Main definitions

* `LieModule.ChevalleyEilenberg.coDiff`: the operator `δ` determined by `δ₀` and `G`.
* `LieModule.ChevalleyEilenberg.laplacian`: `□ = dδ + δd`.
* `LieModule.ChevalleyEilenberg.laplacianComm`: the operator `R(y) = [θ(y), δ] - d G(y) + G(y) d`.

## Main results

* `LieModule.ChevalleyEilenberg.laplacian_wedge`, `laplacianComm_wedge`: the commutation rules.
* `LieModule.ChevalleyEilenberg.coDiff_mem_chainsIn`: `δ` raises the degree by one.
* `LieModule.ChevalleyEilenberg.mem_boundaries_of_laplacian_eq_smul`: cycles on which `□` acts by
  an invertible scalar are boundaries.
* `LieModule.ChevalleyEilenberg.DerivAction.laplacian_eq_smul_of_mem_chainWeightSpace`: a
  criterion for `□` to act on each weight space of the chains by a scalar.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387.
* The recursive definition and the commutation rules are reconstructed by us, in the style of
  `LieLean.Algebra.Lie.Homology.ChevalleyEilenberg`.
-/


-- @@ L56-56 verbatim
open Module TensorProduct ExteriorAlgebra


-- @@ L58-58 verbatim
noncomputable section


-- @@ L60-60 verbatim
namespace LieModule.ChevalleyEilenberg


-- @@ L62-62 verbatim
/-! ### The codifferential -/


-- @@ L64-64 verbatim
section CoDiff


-- @@ L66-67 verbatim
variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]


-- @@ L69-69 verbatim
local notation "E" => ExteriorAlgebra R L ⊗[R] M


-- @@ L71-72 verbatim
variable (δ₀ : M →ₗ[R] ExteriorAlgebra R L ⊗[R] M)
  (G : L →ₗ[R] Module.End R (ExteriorAlgebra R L ⊗[R] M))


-- @@ L74-81 verbatim
/-- The recursion step for `coDiff`: `(y, ω, g) ↦ (m ↦ -G(y)(ω ⊗ m) - y ∧ g m)`. -/
def coDiffStep : L →ₗ[R] ExteriorAlgebra R L × (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
  LinearMap.mk₂ R
    (fun y p ↦ -(G y ∘ₗ TensorProduct.mk R _ M p.1) - wedge R L M y ∘ₗ p.2)
    (fun y y' p ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])
    (fun y p p' ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])


-- @@ L83-84 verbatim
lemma coDiffStep_apply (y : L) (p : ExteriorAlgebra R L × (M →ₗ[R] E)) (m : M) :
    coDiffStep G y p m = -G y (p.1 ⊗ₜ m) - wedge R L M y (p.2 m) := rfl


-- @@ L86-92 verbatim
omit G in
/-- Left multiplications by elements of `L` anticommute on `⋀L ⊗ M`. -/
lemma wedge_wedge_comm (a b : L) (c : E) :
    wedge R L M a (wedge R L M b c) = -wedge R L M b (wedge R L M a c) := by
  have h := wedge_wedge (R := R) (M := M) (a + b) c
  simp only [map_add, LinearMap.add_apply, wedge_wedge, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)


-- @@ L94-98 verbatim
omit G in
lemma wedge_wedge_wedge_comm (a b z : L) (c : E) :
    wedge R L M a (wedge R L M b (wedge R L M z c)) =
      wedge R L M z (wedge R L M a (wedge R L M b c)) := by
  rw [wedge_wedge_comm b z, map_neg, wedge_wedge_comm a z, neg_neg]


-- @@ L100-104 verbatim
omit G in
lemma ι_tmul_mem_chainsIn_one (y : L) (m : M) :
    (ι R y : ExteriorAlgebra R L) ⊗ₜ m ∈ chainsIn R L M 1 := by
  have := wedge_mem_chainsIn (M := M) y (one_tmul_mem_chainsIn (R := R) (L := L) m)
  rwa [wedge_tmul, mul_one] at this


-- @@ L106-106 verbatim
variable (hG : ∀ y, G y ∘ₗ wedge R L M y = wedge R L M y ∘ₗ G y)

-- @@ L107-107 verbatim
include hG


-- @@ L109-114 verbatim
lemma coDiffStep_step (y : L) (ω : ExteriorAlgebra R L) (g : M →ₗ[R] E) :
    coDiffStep G y (ι R y * ω, coDiffStep G y (ω, g)) =
      (0 : QuadraticForm R L) y • g := by
  ext m
  rw [coDiffStep_apply, coDiffStep_apply, ← wedge_tmul, ← LinearMap.comp_apply (G y), hG y]
  simp


-- @@ L116-119 verbatim
/-- Auxiliary for `coDiff`: the fold over `⋀L`. -/
def coDiffFold : ExteriorAlgebra R L →ₗ[R] M →ₗ[R] E :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (coDiffStep G)
    (fun y ω g ↦ by exact coDiffStep_step G hG y ω g) δ₀


-- @@ L121-123 verbatim
/-- The operator `δ` on `⋀L ⊗ M` determined by `δ(1 ⊗ m) = δ₀ m` and
`δ(y ∧ c) = -G(y) c - y ∧ δ c`. -/
def coDiff : Module.End R E := TensorProduct.lift (coDiffFold δ₀ G hG)


-- @@ L125-127 verbatim
lemma coDiffFold_ι_mul (y : L) (ω : ExteriorAlgebra R L) :
    coDiffFold δ₀ G hG (ι R y * ω) = coDiffStep G y (ω, coDiffFold δ₀ G hG ω) :=
  CliffordAlgebra.foldr'_ι_mul _ _ _ _ _ _


-- @@ L129-133 verbatim
@[simp] lemma coDiff_one_tmul (m : M) : coDiff δ₀ G hG (1 ⊗ₜ m) = δ₀ m := by
  have h := CliffordAlgebra.foldr'_algebraMap (0 : QuadraticForm R L) (coDiffStep G)
    (fun y ω g ↦ by exact coDiffStep_step G hG y ω g) δ₀ (1 : R)
  rw [map_one, one_smul] at h
  exact LinearMap.congr_fun h m


-- @@ L135-140 verbatim
/-- The recursion formula `δ(y ∧ c) = -G(y) c - y ∧ δ c`. -/
lemma coDiff_wedge (y : L) (c : E) :
    coDiff δ₀ G hG (wedge R L M y c) = -G y c - wedge R L M y (coDiff δ₀ G hG c) := by
  induction c with
  | add c c' hc hc' => simp only [map_add, hc, hc']; abel
  | tmul ω m => exact LinearMap.congr_fun (coDiffFold_ι_mul δ₀ G hG y ω) m


-- @@ L142-157 verbatim
/-- `δ` raises the degree by one if `δ₀` has values in degree `1` and the `G(y)` raise the degree
by two. -/
theorem coDiff_mem_chainsIn (hδ₀ : ∀ m, δ₀ m ∈ chainsIn R L M 1)
    (hGk : ∀ y k c, c ∈ chainsIn R L M k → G y c ∈ chainsIn R L M (k + 2))
    {k : ℕ} {c : E} (hc : c ∈ chainsIn R L M k) : coDiff δ₀ G hG c ∈ chainsIn R L M (k + 1) := by
  induction k generalizing c with
  | zero =>
    refine chainsIn_zero_le (S := (chainsIn R L M 1).comap (coDiff δ₀ G hG))
      (fun m ↦ ?_) hc
    rw [Submodule.mem_comap, coDiff_one_tmul]
    exact hδ₀ m
  | succ k ih =>
    refine chainsIn_succ_le (S := (chainsIn R L M (k + 2)).comap (coDiff δ₀ G hG))
      (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, coDiff_wedge]
    exact sub_mem (neg_mem (hGk y k c hc)) (wedge_mem_chainsIn y (ih hc))


-- @@ L159-159 verbatim
/-! ### The Laplacian -/


-- @@ L161-161 verbatim
variable [LieRingModule L M] [LieModule R L M]


-- @@ L163-165 verbatim
/-- The Laplacian `□ = dδ + δd`. -/
def laplacian : Module.End R E :=
  diff R L M ∘ₗ coDiff δ₀ G hG + coDiff δ₀ G hG ∘ₗ diff R L M


-- @@ L167-171 verbatim
/-- The operator `R(y) = [θ(y), δ] - d G(y) + G(y) d` measuring the failure of `□` to commute
with `ε(y)`. -/
def laplacianComm (y : L) : Module.End R E :=
  lieAction R L M y ∘ₗ coDiff δ₀ G hG - coDiff δ₀ G hG ∘ₗ lieAction R L M y -
    diff R L M ∘ₗ G y + G y ∘ₗ diff R L M


-- @@ L173-174 verbatim
lemma laplacian_apply (c : E) :
    laplacian δ₀ G hG c = diff R L M (coDiff δ₀ G hG c) + coDiff δ₀ G hG (diff R L M c) := rfl


-- @@ L176-178 verbatim
lemma laplacianComm_apply (y : L) (c : E) :
    laplacianComm δ₀ G hG y c = lieAction R L M y (coDiff δ₀ G hG c) -
      coDiff δ₀ G hG (lieAction R L M y c) - diff R L M (G y c) + G y (diff R L M c) := rfl


-- @@ L180-182 verbatim
@[simp] lemma laplacian_one_tmul (m : M) :
    laplacian δ₀ G hG (1 ⊗ₜ m) = diff R L M (δ₀ m) := by
  simp [laplacian_apply]


-- @@ L184-187 verbatim
lemma laplacianComm_one_tmul (y : L) (m : M) :
    laplacianComm δ₀ G hG y (1 ⊗ₜ m) =
      lieAction R L M y (δ₀ m) - δ₀ ⁅y, m⁆ - diff R L M (G y (1 ⊗ₜ m)) := by
  simp [laplacianComm_apply]


-- @@ L189-195 verbatim
/-- `□ ε(y) = ε(y) □ + R(y)`. -/
theorem laplacian_wedge (y : L) (c : E) :
    laplacian δ₀ G hG (wedge R L M y c) =
      wedge R L M y (laplacian δ₀ G hG c) + laplacianComm δ₀ G hG y c := by
  simp only [laplacian_apply, laplacianComm_apply, coDiff_wedge, diff_wedge, map_sub, map_neg,
    map_add]
  abel


-- @@ L197-209 verbatim
/-- `R(y) ε(z) = -ε(z) R(y) + G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)]`, if the `G(y)` commute
with the `ε(z)`. -/
theorem laplacianComm_wedge (hGε : ∀ y z, G y ∘ₗ wedge R L M z = wedge R L M z ∘ₗ G y)
    (y z : L) (c : E) :
    laplacianComm δ₀ G hG y (wedge R L M z c) =
      -wedge R L M z (laplacianComm δ₀ G hG y c) + (G ⁅y, z⁆ c -
        (lieAction R L M y (G z c) - G z (lieAction R L M y c)) +
        (lieAction R L M z (G y c) - G y (lieAction R L M z c))) := by
  have h (c : E) : G y (wedge R L M z c) = wedge R L M z (G y c) :=
    LinearMap.congr_fun (hGε y z) c
  simp only [laplacianComm_apply, coDiff_wedge, diff_wedge, lieAction_wedge, map_sub, map_neg,
    map_add, h]
  abel


-- @@ L211-211 verbatim
end CoDiff


-- @@ L213-213 verbatim
section Formulas


-- @@ L215-216 verbatim
variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]


-- @@ L218-218 verbatim
local notation "E" => ExteriorAlgebra R L ⊗[R] M


-- @@ L220-223 verbatim
lemma lieAction_wedge_one_tmul (y a : L) (m : M) :
    lieAction R L M y (wedge R L M a (1 ⊗ₜ m)) =
      wedge R L M ⁅y, a⁆ (1 ⊗ₜ m) + wedge R L M a (1 ⊗ₜ ⁅y, m⁆) := by
  rw [lieAction_wedge, lieAction_one_tmul]


-- @@ L225-229 verbatim
lemma wedge_one_tmul_sub_lieAction (y a : L) (m m' : M) :
    wedge R L M a (1 ⊗ₜ m') - lieAction R L M y (wedge R L M a (1 ⊗ₜ m)) =
      wedge R L M a (1 ⊗ₜ (m' - ⁅y, m⁆)) - wedge R L M ⁅y, a⁆ (1 ⊗ₜ m) := by
  rw [lieAction_wedge_one_tmul, tmul_sub, map_sub]
  abel


-- @@ L231-235 verbatim
lemma lieAction_wedge_wedge (y a b : L) (c : E) :
    lieAction R L M y (wedge R L M a (wedge R L M b c)) =
      wedge R L M ⁅y, a⁆ (wedge R L M b c) + wedge R L M a (wedge R L M ⁅y, b⁆ c) +
        wedge R L M a (wedge R L M b (lieAction R L M y c)) := by
  rw [lieAction_wedge, lieAction_wedge, map_add, add_assoc]


-- @@ L237-239 verbatim
lemma diff_wedge_one_tmul (a : L) (m : M) :
    diff R L M (wedge R L M a (1 ⊗ₜ m)) = -(1 ⊗ₜ ⁅a, m⁆) := by
  rw [wedge_tmul, mul_one, diff_ι_tmul]


-- @@ L241-246 verbatim
lemma diff_wedge_wedge_one_tmul (a b : L) (m : M) :
    diff R L M (wedge R L M a (wedge R L M b (1 ⊗ₜ m))) =
      -wedge R L M b (1 ⊗ₜ ⁅a, m⁆) + wedge R L M a (1 ⊗ₜ ⁅b, m⁆) -
        wedge R L M ⁅a, b⁆ (1 ⊗ₜ m) := by
  simp only [wedge_tmul, mul_one]
  exact diff_ι_mul_ι_tmul a b m


-- @@ L248-248 verbatim
end Formulas


-- @@ L250-250 verbatim
/-! ### Cycles on which the Laplacian is invertible -/


-- @@ L252-252 verbatim
section Boundaries


-- @@ L254-257 verbatim
variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  (δ₀ : M →ₗ[K] ExteriorAlgebra K L ⊗[K] M) (G : L →ₗ[K] Module.End K (ExteriorAlgebra K L ⊗[K] M))
  (hG : ∀ y, G y ∘ₗ wedge K L M y = wedge K L M y ∘ₗ G y)


-- @@ L259-269 verbatim
/-- A cycle `c` of degree `k` with `□ c = s c`, `s ≠ 0`, is a boundary: `c = d(s⁻¹ δ c)`. This is
the algebraic core of Kostant's argument: over a general field there is no harmonic theory, but
`δ` is a contracting homotopy on the eigenspaces of `□` for nonzero eigenvalues. -/
theorem mem_boundaries_of_laplacian_eq_smul
    (hδ : ∀ k c, c ∈ chainsIn K L M k → coDiff δ₀ G hG c ∈ chainsIn K L M (k + 1))
    {k : ℕ} {c : ExteriorAlgebra K L ⊗[K] M} (hc : c ∈ cycles K L M k) {s : K} (hs : s ≠ 0)
    (hL : laplacian δ₀ G hG c = s • c) : c ∈ boundaries K L M k := by
  have hdc : diff K L M c = 0 := hc.2
  rw [laplacian_apply, hdc, map_zero, add_zero] at hL
  refine ⟨s⁻¹ • coDiff δ₀ G hG c, Submodule.smul_mem _ _ (hδ k c hc.1), ?_⟩
  rw [map_smul, hL, smul_smul, inv_mul_cancel₀ hs, one_smul]


-- @@ L271-271 verbatim
end Boundaries


-- @@ L273-273 verbatim
/-! ### Operators acting by scalars on the weight spaces of the chains -/


-- @@ L275-275 verbatim
namespace DerivAction


-- @@ L277-286 verbatim
variable {K H L M : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] {ρ : DerivAction K H L M}
  {I J : Type*} [LinearOrder I] (bL : Basis I K L) (bM : Basis J K M)
  {γ : I → Dual K H} {ν : J → Dual K H}
  (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
  (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j))
  (T : Module.End K (ExteriorAlgebra K L ⊗[K] M)) (s : Dual K H → K)
  (hbase : ∀ j, T (1 ⊗ₜ bM j) = s (ν j) • (1 ⊗ₜ bM j))
  (hstep : ∀ i μ c, c ∈ ρ.chainWeightSpace μ → T c = s μ • c →
    T (wedge K L M (bL i) c) = s (γ i + μ) • wedge K L M (bL i) c)

-- @@ L287-287 verbatim
include hbL hbM hbase hstep


-- @@ L289-298 verbatim
omit [LinearOrder I] in
lemma apply_ιMulti_tmul_eq_smul (n : ℕ) (f : Fin n → I) (j : J) :
    T (ιMulti K n (bL ∘ f) ⊗ₜ bM j) = s (∑ k, γ (f k) + ν j) • (ιMulti K n (bL ∘ f) ⊗ₜ bM j) := by
  induction n with
  | zero => simpa using hbase j
  | succ n ih =>
    have hc := ιMulti_tmul_mem_chainWeightSpace (ρ := ρ) (bL ∘ Matrix.vecTail f)
      (γ ∘ Matrix.vecTail f) (fun k ↦ hbL _) (hbM j)
    rw [ιMulti_succ_apply, ← wedge_tmul, Fin.sum_univ_succ, add_assoc]
    exact hstep (f 0) _ _ hc (ih (Matrix.vecTail f))


-- @@ L300-318 verbatim
/-- **A criterion for an operator to act by scalars on the weight spaces of the chains**: if `T`
acts on `1 ⊗ m_j` by `s(ν_j)`, and `T (y_i ∧ c) = s(γ_i + μ) (y_i ∧ c)` whenever `c` has weight
`μ` and `T c = s(μ) c`, then `T` acts on the weight-`μ` chains by `s(μ)`, for all `μ`. -/
theorem apply_eq_smul_of_mem_chainWeightSpace {μ : Dual K H} {c : ExteriorAlgebra K L ⊗[K] M}
    (hc : c ∈ ρ.chainWeightSpace μ) : T c = s μ • c := by
  rw [chainWeightSpace_eq_span bL bM hbL hbM μ] at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [← Set.mem_ofPred_eq (p := fun t ↦ chainWt γ ν t = μ).mp ht, chainBasis_apply,
      basis_exteriorAlgebra_eq]
    convert apply_ιMulti_tmul_eq_smul bL bM hbL hbM T s hbase hstep _
      (t.1.orderEmbOfFin rfl) t.2 using 3
    rw [chainWt]
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ t.1 rfl]
    rw [Finset.sum_image fun _ _ _ _ h ↦ (t.1.orderEmbOfFin rfl).injective h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]


-- @@ L320-320 verbatim
end DerivAction


-- @@ L322-322 verbatim
end LieModule.ChevalleyEilenberg
