import OAI.Geometry.Zonotope.Euclidean


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace


-- @@ L9-9 verbatim
namespace DiagonalZonotope


-- @@ L11-14 verbatim
/-- The two-block product of explicit Euclidean zonotopes. -/
def euclideanProduct (n m : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + m))) :=
  EuclideanSpace.finAddEquivProd ⁻¹'
    ((euclidean c : Set (EuclideanSpace ℝ (Fin n))) ×ˢ euclidean c)


-- @@ L16-20 verbatim
lemma finAddEquivProd_apply (n m : ℕ) (x : EuclideanSpace ℝ (Fin (n + m))) :
    EuclideanSpace.finAddEquivProd x =
      (WithLp.toLp 2 (fun i : Fin n => x (Fin.castAdd m i)),
       WithLp.toLp 2 (fun i : Fin m => x (Fin.natAdd n i))) := by
  rfl


-- @@ L22-27 verbatim
lemma inner_finAdd (n m : ℕ) (u x : EuclideanSpace ℝ (Fin (n + m))) :
    ⟪u, x⟫ =
      ⟪(EuclideanSpace.finAddEquivProd u).1, (EuclideanSpace.finAddEquivProd x).1⟫ +
      ⟪(EuclideanSpace.finAddEquivProd u).2, (EuclideanSpace.finAddEquivProd x).2⟫ := by
  simp only [inner_eq_coordinates, finAddEquivProd_apply]
  exact Fin.sum_univ_add (fun i => u i * x i)


-- @@ L29-33 verbatim
lemma isCompact_euclideanProduct (n m : ℕ) (c : ℝ) : IsCompact (euclideanProduct n m c) := by
  let e := (@EuclideanSpace.finAddEquivProd ℝ _ n m).toHomeomorph
  change IsCompact (e ⁻¹' _)
  rw [← e.image_symm]
  exact ((isCompact_euclidean c).prod (isCompact_euclidean c)).image e.symm.continuous


-- @@ L35-37 verbatim
lemma convex_euclideanProduct (n m : ℕ) (c : ℝ) : Convex ℝ (euclideanProduct n m c) :=
  ((convex_euclidean c).prod (convex_euclidean c)).linear_preimage
    EuclideanSpace.finAddEquivProd.toLinearMap


-- @@ L39-45 verbatim
lemma euclideanProduct_interior_nonempty (n m : ℕ) (c : ℝ) (hc : c ≠ 0) :
    (interior (euclideanProduct n m c)).Nonempty := by
  let e := (@EuclideanSpace.finAddEquivProd ℝ _ n m).toHomeomorph
  change (interior (e ⁻¹' _)).Nonempty
  rw [← e.preimage_interior, interior_prod_eq]
  exact ((euclidean_interior_nonempty c hc).prod
    (euclidean_interior_nonempty c hc)).preimage e.surjective


-- @@ L47-75 verbatim
/-- Product support is the sum of the two independently attainable supports. -/
theorem euclideanProduct_eq_halfspaces (n m : ℕ) (c : ℝ) (hc : 0 < c) :
    euclideanProduct n m c =
      {x | ∀ u : EuclideanSpace ℝ (Fin (n + m)), ⟪u, x⟫ ≤ c *
        (support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
         support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2))} := by
  ext x
  constructor
  · intro hx u
    obtain ⟨hx₁, hx₂⟩ := hx
    rw [euclidean_eq_halfspaces c hc] at hx₁ hx₂
    rw [inner_finAdd, mul_add]
    exact add_le_add (hx₁ _) (hx₂ _)
  · intro hx
    change (EuclideanSpace.finAddEquivProd x).1 ∈ euclidean c ∧
      (EuclideanSpace.finAddEquivProd x).2 ∈ euclidean c
    constructor
    · rw [euclidean_eq_halfspaces c hc]
      intro u
      have h := hx (EuclideanSpace.finAddEquivProd.symm (u, 0))
      rw [inner_finAdd] at h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
        add_zero, WithLp.ofLp_zero, support_zero] using h
    · rw [euclidean_eq_halfspaces c hc]
      intro u
      have h := hx (EuclideanSpace.finAddEquivProd.symm (0, u))
      rw [inner_finAdd] at h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, inner_zero_left,
        zero_add, WithLp.ofLp_zero, support_zero] using h


-- @@ L77-92 verbatim
theorem euclideanProduct_support_attained (n m : ℕ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + m))) :
    ∃ x ∈ euclideanProduct n m c, ⟪u, x⟫ = c *
      (support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
       support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2)) := by
  obtain ⟨x₁, hx₁, heq₁⟩ := euclidean_support_attained c (EuclideanSpace.finAddEquivProd u).1
  obtain ⟨x₂, hx₂, heq₂⟩ := euclidean_support_attained c (EuclideanSpace.finAddEquivProd u).2
  refine ⟨EuclideanSpace.finAddEquivProd.symm (x₁, x₂), ?_, ?_⟩
  · change EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm (x₁, x₂)) ∈
      ((euclidean c : Set (EuclideanSpace ℝ (Fin n))) ×ˢ
        (euclidean c : Set (EuclideanSpace ℝ (Fin m))))
    simpa only [ContinuousLinearEquiv.apply_symm_apply, Set.mem_prod] using And.intro hx₁ hx₂
  · rw [inner_finAdd]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [heq₁, heq₂, mul_add]


-- @@ L94-94 verbatim
end DiagonalZonotope


-- @@ L96-96 verbatim
end


-- @@ L98-98 verbatim
end OAI
