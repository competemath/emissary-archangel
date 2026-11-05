import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_SemistableCharts


-- @@ L7-7 verbatim
set_option autoImplicit false

-- @@ L8-8 verbatim
set_option quotPrecheck false


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open AlgebraicCurve IsLocalRing ModularCurve

-- @@ L13-13 verbatim
open scoped MatrixGroups


-- @@ L15-15 verbatim
namespace ModularCurve

-- @@ L16-16 verbatim
namespace JHPlaceSpecialization


-- @@ L18-18 verbatim
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

-- @@ L19-19 verbatim
variable (A : ValuationSubring (AlgebraicClosure ℚ))

-- @@ L20-20 verbatim
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]


-- @@ L22-22 verbatim
local notation "κ" => ResidueField ↥A

-- @@ L23-23 verbatim
local notation "FM" => ↥(xHFunctionFieldBar M H)

-- @@ L24-24 verbatim
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))

-- @@ L25-25 verbatim
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)


-- @@ L27-27 verbatim
variable {p M H hpM A}


-- @@ L29-29 verbatim
namespace ProlongationDatum


-- @@ L31-31 verbatim
variable {P : JHPlaceSpecialization p M H hpM A}

-- @@ L32-32 verbatim
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}


-- @@ L34-48 verbatim
def nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Subring FM where
  carrier := {f | f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun V _ => zero_mem _⟩
  one_mem' := ⟨one_mem _, one_mem _, fun V _ => one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨add_mem hf₁ hg₁, add_mem hf₂ hg₂, fun V hV => add_mem (hf V hV) (hg V hV)⟩
  neg_mem' := by
    rintro f ⟨hf₁, hf₂, hf⟩
    exact ⟨neg_mem hf₁, neg_mem hf₂, fun V hV => neg_mem (hf V hV)⟩
  mul_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨mul_mem hf₁ hg₁, mul_mem hf₂ hg₂, fun V hV => mul_mem (hf V hV) (hg V hV)⟩


-- @@ L50-55 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_nodeIntegers_iff (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : FM) :
    f ∈ R.nodeIntegers α hα w ↔ f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
      ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → f ∈ V.toValuationSubring :=
  Iff.rfl


-- @@ L57-62 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem mem_toValuationSubring_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    f ∈ V.toValuationSubring :=
  hf.2.2 V hV


-- @@ L64-70 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in

theorem ord_nonneg_of_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    {w : Place κ Fb} {f : FM} (hf : f ∈ R.nodeIntegers α hα w)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : P.reduceFst α hα V = w) :
    0 ≤ V.ord f :=
  V.ord_nonneg_of_mem (hf.2.2 V hV)


-- @@ L72-75 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersFst (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₁.integers.toSubring :=
  fun _ hf => hf.1


-- @@ L77-80 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeIntegers_le_integersSnd (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : R.nodeIntegers α hα w ≤ R.R₂.integers.toSubring :=
  fun _ hf => hf.2.1


-- @@ L82-84 verbatim
def nodeResidue₁ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₁.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersFst α hα w))


-- @@ L86-88 verbatim
def nodeResidue₂ (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : ↥(R.nodeIntegers α hα w) →+* Fb :=
  R.R₂.residue.comp (Subring.inclusion (R.nodeIntegers_le_integersSnd α hα w))


-- @@ L90-93 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₁_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₁ α hα w f = R.R₁.residue ⟨f, f.2.1⟩ := rfl


-- @@ L95-98 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem nodeResidue₂_apply (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (f : ↥(R.nodeIntegers α hα w)) :
    R.nodeResidue₂ α hα w f = R.R₂.residue ⟨f, f.2.2.1⟩ := rfl


-- @@ L100-105 verbatim
omit [NeZero M] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] in
theorem algebraMap_mem_nodeIntegers (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) (c : A) :
    algebraMap (AlgebraicClosure ℚ) FM (c : AlgebraicClosure ℚ) ∈ R.nodeIntegers α hα w :=
  ⟨(R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2, (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2,
    fun V _ => V.algebraMap_mem' _⟩


-- @@ L107-110 verbatim
def ValueIntegralityLaw (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (w : Place κ Fb) : Prop :=
  ∀ f : FM, f ∈ R.nodeIntegers α hα w →
    ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = w → V.evalAt f ∈ A


-- @@ L112-112 verbatim
end ProlongationDatum


-- @@ L114-119 verbatim
def AnnulusDepthLaw (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (s : Place κ Fb × Place κ Fb) (An : AlgebraicCurve.Annulus A FM)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = s.1 →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
    A.valuation (V.evalAt An.param) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V


-- @@ L121-123 verbatim
def depthDiv (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor κ Fb :=
  D.sum fun V n => Finsupp.single (P.reduceFst α hα V) (n * (depth V : ℤ))


-- @@ L125-129 verbatim
def depthDual (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (SS : Finset (Place κ Fb × Place κ Fb))
    (depth : Place (AlgebraicClosure ℚ) FM → ℕ) (D : Divisor (AlgebraicClosure ℚ) FM) :
    Module.Dual ℤ (characterLattice ↥SS) :=
  ∑ s : ↥SS, P.depthDiv α hα depth D (s : Place κ Fb × Place κ Fb).1 • crossingCoord s


-- @@ L131-146 verbatim
def DepthCompLaw (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb))
    (e : ↥SS → ℕ) (depth : Place (AlgebraicClosure ℚ) FM → ℕ)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)))
    (hH : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
    (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) FM).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) ∧
        (P.IsStrictFst α β hα hβ δ V ∨ P.IsStrictSnd α β hα hβ δ V ∨ ∃ s ∈ SS, P.reduceFst α hα V = s.1)) →
    ∀ s₀ : ↥SS,
      comp ⟨Pic0.mk D, hH⟩ =
        componentGroupProj e
          (P.depthDual α hα SS depth (D : Divisor (AlgebraicClosure ℚ) FM) +
            Divisor.degree (P.sndDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM)) •
              ((e s₀ : ℤ) • crossingCoord s₀))


-- @@ L148-148 verbatim
end JHPlaceSpecialization

-- @@ L149-149 verbatim
end ModularCurve


-- @@ L151-151 verbatim
end
