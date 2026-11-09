import ModularCurves.ForMathlib.TotalComplexUpNatLowDegrees


-- @@ L3-8 verbatim
/-!
# The horizontal edge map into a first-quadrant total complex

An augmentation into the zeroth horizontal degree of a bicomplex induces a map from the
augmenting cochain complex to the total complex.
-/


-- @@ L10-10 verbatim
open CategoryTheory CategoryTheory.Preadditive


-- @@ L12-12 verbatim
universe v u


-- @@ L14-14 verbatim
namespace HomologicalComplex₂


-- @@ L16-16 verbatim
variable {C : Type u} [Category.{v} C] [Preadditive C]

-- @@ L17-17 verbatim
variable (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

-- @@ L18-18 verbatim
variable [K.HasTotal (.up ℕ)]


-- @@ L20-58 verbatim
/-- The horizontal edge map from an augmented zeroth column to the total complex. -/
noncomputable def totalUpNatHorizontalEdge
    (A : CochainComplex C ℕ) (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0) :
    A ⟶ K.total (.up ℕ) where
  f q := e q ≫ K.ιTotal (.up ℕ) q 0 q rfl
  comm' q q' h := by
    change q + 1 = q' at h
    subst q'
    calc
      (e q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫
          (K.total (.up ℕ)).d q (q + 1) =
        e q ≫ (K.ιTotal (.up ℕ) q 0 q rfl ≫
          (K.total (.up ℕ)).d q (q + 1)) := by rw [Category.assoc]
      _ = e q ≫
          ((K.d q (q + 1)).f 0 ≫
              K.ιTotal (.up ℕ) (q + 1) 0 (q + 1)
                (by change q + 1 + 0 = q + 1; omega) +
            ((-1 : ℤˣ) ^ q) • ((K.X q).d 0 1 ≫
              K.ιTotal (.up ℕ) q 1 (q + 1)
                (by change q + 1 = q + 1; rfl))) := by
        exact congrArg (fun f ↦ e q ≫ f) (by
          simpa only [Nat.add_zero] using K.ιTotal_d_upNat q 0)
      _ = (e q ≫ (K.d q (q + 1)).f 0) ≫
            K.ιTotal (.up ℕ) (q + 1) 0 (q + 1) rfl +
          ((-1 : ℤˣ) ^ q) • ((e q ≫ (K.X q).d 0 1) ≫
            K.ιTotal (.up ℕ) q 1 (q + 1) rfl) := by
        simp only [Preadditive.comp_add, Category.assoc, Linear.comp_units_smul]
      _ = (e q ≫ (K.d q (q + 1)).f 0) ≫
            K.ιTotal (.up ℕ) (q + 1) 0 (q + 1) rfl := by
        rw [w q, CategoryTheory.Limits.zero_comp, smul_zero, add_zero]
      _ = (A.d q (q + 1) ≫ e (q + 1)) ≫
            K.ιTotal (.up ℕ) (q + 1) 0 (q + 1) rfl := by
        rw [he q (q + 1) rfl]
      _ = A.d q (q + 1) ≫
          (e (q + 1) ≫ K.ιTotal (.up ℕ) (q + 1) 0 (q + 1) rfl) := by
        rw [Category.assoc]


-- @@ L60-68 verbatim
@[simp]
theorem totalUpNatHorizontalEdge_f
    (A : CochainComplex C ℕ) (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0) (q : ℕ) :
    (K.totalUpNatHorizontalEdge A e he w).f q =
      e q ≫ K.ιTotal (.up ℕ) q 0 q rfl :=
  rfl


-- @@ L70-70 verbatim
end HomologicalComplex₂
