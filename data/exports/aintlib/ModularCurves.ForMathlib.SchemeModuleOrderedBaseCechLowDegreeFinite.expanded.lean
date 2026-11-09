/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`WellFoundedSheafCohomologyCodesvissage.lean` in Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFinite
import ModularCurves.ForMathlib.SchemeModuleSupport


-- @@ L12-17 verbatim
/-!
# Low-degree ordered base-Cech finiteness

Finiteness of ordered base-Cech homology in degrees zero and one is stable
under the two exact-sequence operations needed by closed-support codévissage.
-/


-- @@ L19-19 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L27-35 verbatim
/-- Ordered base-Cech homology of `M` is finite in degrees zero and one. -/
def OrderedBaseCechLowDegreeFinite
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) : Prop :=
  Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 0) ∧
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 1)


-- @@ L37-37 verbatim
namespace OrderedBaseCechLowDegreeFinite


-- @@ L39-39 verbatim
variable {X S : Scheme.{u}} (π : X ⟶ S)

-- @@ L40-40 verbatim
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)


-- @@ L42-47 verbatim
/-- A zero scheme module has finite ordered base-Cech homology in degrees
zero and one. -/
theorem of_isZero {M : X.Modules} (hM : IsZero M) :
    OrderedBaseCechLowDegreeFinite π U M :=
  ⟨OrderedBaseCechHomologyFinite.of_isZero π U hM 0,
    OrderedBaseCechHomologyFinite.of_isZero π U hM 1⟩


-- @@ L49-49 verbatim
variable [IsNoetherianRing Γ(S, (⊤ : S.Opens))] [X.IsSeparated]

-- @@ L50-50 verbatim
variable (hU : ∀ i, IsAffineOpen (U i))


-- @@ L52-52 verbatim
include hU


-- @@ L54-95 verbatim
/-- Low-degree finiteness is closed under extensions. -/
theorem middle
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent]
    (h₁ : OrderedBaseCechLowDegreeFinite π U T.X₁)
    (h₃ : OrderedBaseCechLowDegreeFinite π U T.X₃) :
    OrderedBaseCechLowDegreeFinite π U T.X₂ := by
  let F := orderedBaseCechComplexFunctor π U
  have hTF : (T.map F).ShortExact :=
    hT.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU
  constructor
  · letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₁.homology 0) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₁ U).homology 0)
      exact h₁.1
    letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₃.homology 0) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₃ U).homology 0)
      exact h₃.1
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₂.homology 0)
    exact
      ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X2
        hTF 0
  · letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₁.homology 1) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₁ U).homology 1)
      exact h₁.2
    letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₃.homology 1) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₃ U).homology 1)
      exact h₃.2
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₂.homology 1)
    exact
      ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X2
        hTF 1


-- @@ L97-135 verbatim
/-- Low-degree finiteness for the middle and quotient terms implies
low-degree finiteness for the subobject term. -/
theorem left
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent]
    (h₂ : OrderedBaseCechLowDegreeFinite π U T.X₂)
    (h₃ : OrderedBaseCechLowDegreeFinite π U T.X₃) :
    OrderedBaseCechLowDegreeFinite π U T.X₁ := by
  let F := orderedBaseCechComplexFunctor π U
  have hTF : (T.map F).ShortExact :=
    hT.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU
  constructor
  · letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₂.homology 0) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₂ U).homology 0)
      exact h₂.1
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₁.homology 0)
    apply
      ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X1_of_not_rel
        hTF 0
    simp [ComplexShape.up_Rel]
  · letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₃.homology 0) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₃ U).homology 0)
      exact h₃.1
    letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((T.map F).X₂.homology 1) := by
      change Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π T.X₂ U).homology 1)
      exact h₂.2
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₁.homology 1)
    exact
      ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X1
        hTF 0 1 (by simp [ComplexShape.up_Rel])


-- @@ L137-231 verbatim
/-- Well-founded low-degree ordered base-Cech finiteness codévissage for
comparisons `M ⟶ E`. -/
theorem of_wellFounded_comodels
    {α : Type*} (r : α → α → Prop) [IsWellFounded α r]
    (rank : X.Modules → α)
    (P Good : X.Modules → Prop)
    (hPqc : ∀ M, P M → M.IsQuasicoherent)
    (hGoodqc : ∀ E, Good E → E.IsQuasicoherent)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            r (rank (kernel (Abelian.factorThruImage f))) (rank M)) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            r (rank (cokernel (Abelian.image.ι f))) (rank M)))
    (hgood :
      ∀ E, Good E → OrderedBaseCechLowDegreeFinite π U E) :
    ∀ M, P M → OrderedBaseCechLowDegreeFinite π U M := by
  let rel : X.Modules → X.Modules → Prop :=
    fun A B ↦ r (rank A) (rank B)
  haveI : IsWellFounded X.Modules rel :=
    inferInstanceAs (IsWellFounded X.Modules (InvImage r rank))
  intro M hM
  induction M using IsWellFounded.induction rel with
  | ind M ih =>
      letI : M.IsQuasicoherent := hPqc M hM
      obtain ⟨E, f, hE, hPK, hPQ, hKsmaller, hQsmaller⟩ :=
        hcomodel M hM
      let K := kernel (Abelian.factorThruImage f)
      let I := Abelian.image f
      let Q := cokernel (Abelian.image.ι f)
      have hK : OrderedBaseCechLowDegreeFinite π U K := by
        rcases hKsmaller with hKzero | hKlt
        · exact of_isZero π U hKzero
        · exact ih K hKlt hPK
      have hQ : OrderedBaseCechLowDegreeFinite π U Q := by
        rcases hQsmaller with hQzero | hQlt
        · exact of_isZero π U hQzero
        · exact ih Q hQlt hPQ
      have hEfinite : OrderedBaseCechLowDegreeFinite π U E :=
        hgood E hE
      letI : E.IsQuasicoherent := hGoodqc E hE
      letI : K.IsQuasicoherent := hPqc K hPK
      letI : Q.IsQuasicoherent := hPqc Q hPQ
      letI : I.IsQuasicoherent := by
        dsimp only [I]
        exact isQuasicoherent_image f
      let S₂ := ShortComplex.cokernelSequence (Abelian.image.ι f)
      haveI : Mono S₂.f := by
        dsimp [S₂, ShortComplex.cokernelSequence]
        infer_instance
      have hS₂ : S₂.ShortExact :=
        { exact := ShortComplex.cokernelSequence_exact (Abelian.image.ι f) }
      letI : S₂.X₁.IsQuasicoherent := by
        change I.IsQuasicoherent
        infer_instance
      letI : S₂.X₂.IsQuasicoherent := by
        change E.IsQuasicoherent
        infer_instance
      letI : S₂.X₃.IsQuasicoherent := by
        change Q.IsQuasicoherent
        infer_instance
      have hI : OrderedBaseCechLowDegreeFinite π U I := by
        change OrderedBaseCechLowDegreeFinite π U S₂.X₁
        apply left π U hU hS₂
        · change OrderedBaseCechLowDegreeFinite π U E
          exact hEfinite
        · change OrderedBaseCechLowDegreeFinite π U Q
          exact hQ
      let S₁ :=
        ShortComplex.kernelSequence (Abelian.factorThruImage f)
      haveI : Epi S₁.g := by
        dsimp [S₁, ShortComplex.kernelSequence]
        infer_instance
      have hS₁ : S₁.ShortExact :=
        { exact :=
            ShortComplex.kernelSequence_exact (Abelian.factorThruImage f) }
      letI : S₁.X₁.IsQuasicoherent := by
        change K.IsQuasicoherent
        infer_instance
      letI : S₁.X₂.IsQuasicoherent := by
        change M.IsQuasicoherent
        infer_instance
      letI : S₁.X₃.IsQuasicoherent := by
        change I.IsQuasicoherent
        infer_instance
      change OrderedBaseCechLowDegreeFinite π U S₁.X₂
      apply middle π U hU hS₁
      · change OrderedBaseCechLowDegreeFinite π U K
        exact hK
      · change OrderedBaseCechLowDegreeFinite π U I
        exact hI


-- @@ L233-259 verbatim
/-- Closed-stalk-support induction for low-degree ordered base-Cech homology
finiteness. -/
theorem of_closedStalkSupport_comodels
    [NoetherianSpace X]
    (P Good : X.Modules → Prop)
    (hPqc : ∀ M, P M → M.IsQuasicoherent)
    (hGoodqc : ∀ E, Good E → E.IsQuasicoherent)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            closedStalkSupport
                (kernel (Abelian.factorThruImage f)) <
              closedStalkSupport M) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            closedStalkSupport
                (cokernel (Abelian.image.ι f)) <
              closedStalkSupport M))
    (hgood :
      ∀ E, Good E → OrderedBaseCechLowDegreeFinite π U E) :
    ∀ M, P M → OrderedBaseCechLowDegreeFinite π U M :=
  of_wellFounded_comodels π U hU
    (fun Z W : Closeds X ↦ Z < W)
    closedStalkSupport P Good hPqc hGoodqc hcomodel hgood


-- @@ L261-261 verbatim
end OrderedBaseCechLowDegreeFinite


-- @@ L263-263 verbatim
end AlgebraicGeometry.Scheme.Modules
