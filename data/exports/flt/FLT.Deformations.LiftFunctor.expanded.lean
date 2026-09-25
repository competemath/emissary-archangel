/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Deformations.Categories
public import FLT.Deformations.Subfunctor
public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter


-- @@ L13-19 verbatim
/-!
# The functor of continuous representations

For a profinite group `G` and a proartinian local ring `𝓞`, the functor
`repnFunctor n G 𝓞` sends a proartinian `𝓞`-algebra `R` to the set of
continuous representations `G → GLₙ(R)`.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open CategoryTheory IsLocalRing


-- @@ L25-25 verbatim
namespace Deformation


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
variable {n : Type} [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]

-- @@ L30-30 verbatim
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

-- @@ L31-31 verbatim
variable {K : Type u} [Field K] [NumberField K]


-- @@ L33-33 verbatim
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

-- @@ L34-34 verbatim
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

-- @@ L35-35 verbatim
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)


-- @@ L37-37 verbatim
open scoped TypeCat

-- @@ L38-42 verbatim
variable (n) in
/-- `repnFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)`. -/
def repnFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := G →ₜ* GL n R
  map {R S} f := ↾ (fun ρ ↦ .comp (Units.mapₜ f.hom.mapMatrix.toContinuousMonoidHom) ρ)


-- @@ L44-48 verbatim
omit [IsLocalRing 𝓞] in
@[simp]
lemma repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl


-- @@ L50-54 verbatim
variable {G 𝓞} in
/-- Turn an element in `repnFunctor` into an actual `Representation`. -/
def toRepresentation {R} (ρ : (repnFunctor n G 𝓞).obj R) :
    Representation R G (n → R) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.toMonoidHom)


-- @@ L56-61 verbatim
variable {G 𝓞} in
/-- Turn an element in `repnFunctor` into an actual `GaloisRep`. -/
noncomputable
def toFramedGaloisRep {R} (ρ : (repnFunctor n (Γ K) 𝓞).obj R) :
    FramedGaloisRep K R n :=
  FramedGaloisRep.GL.symm ρ


-- @@ L63-71 verbatim
set_option backward.isDefEq.respectTransparency.types false in
omit [IsLocalRing 𝓞] [NumberField K] in
lemma toFramedGaloisRep_map {R S : ProartinianCat 𝓞} (f : R ⟶ S)
    (ρ : (repnFunctor n (Γ K) 𝓞).obj R) :
    toFramedGaloisRep ((repnFunctor n (Γ K) 𝓞).map f ρ) =
      (toFramedGaloisRep ρ).baseChange f.hom f.hom.cont := by
  apply FramedGaloisRep.GL.injective
  ext
  simp [toFramedGaloisRep]


-- @@ L73-73 verbatim
variable (n)


-- @@ L75-94 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `repnQuotFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)` up to
conjugation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def repnQuotFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := MulAction.orbitRel.Quotient ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))
    (G →ₜ* GL n R)
  map {R S} f := ↾Quotient.map ((repnFunctor n G 𝓞).map f) (by
    rintro _ ρ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨.toConjAct (Matrix.GeneralLinearGroup.map f.hom.toRingHom g.ofConjAct), ?_⟩, ?_⟩
    · simpa [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
        ← RingHom.coe_comp, ← ContinuousAlgHom.coe_comp,
        -AlgHomClass.toRingHom_toAlgHom, ← AlgHom.comp_toRingHom, ← ProartinianCat.hom_comp,
        Subsingleton.elim _ R.toResidueField]
    · obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
      ext1 γ
      simp [ConjAct.toConjAct_smul, ← map_inv, -ConjAct.ofConjAct_inv, ← map_mul])
  map_id _ := by ext ⟨_⟩; rfl
  map_comp _ _ := by ext ⟨_⟩; rfl


-- @@ L96-100 verbatim
/-- The quotient map taking representations to "representations up to equivalence". -/
noncomputable
def toRepnQuot : repnFunctor n G 𝓞 ⟶ repnQuotFunctor n G 𝓞 where
  app _ := ↾Quotient.mk''
  naturality _ _ _ := rfl


-- @@ L102-105 verbatim
/-- `liftFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`. -/
noncomputable
def liftFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) : Subfunctor (repnFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {ρ}


-- @@ L107-112 verbatim
/-- `deformationFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`,
up to conjugation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def deformationFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) :
    Subfunctor (repnQuotFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {(toRepnQuot n G 𝓞).app _ ρ}


-- @@ L114-117 verbatim
/-- The subfunctor of flat lifts. This probably only makes sense when `𝓞` is `v`-adic. -/
def flatFunctor (v : Ω K) : Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | (toFramedGaloisRep ρ).IsFlatAt v }
  map := sorry -- See e.g. Conrad Theorem 1.6 of CSS


-- @@ L119-127 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of unramified (at `v`) representations. -/
def unramifiedFunctor (v : Ω K) : Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | (toFramedGaloisRep ρ).IsUnramifiedAt v }
  map {R S} f ρ hρ := by
    have : (toFramedGaloisRep ρ).IsUnramifiedAt v := hρ
    simp only [Set.preimage_ofPred_eq, toFramedGaloisRep_map, FramedGaloisRep.baseChange_def,
      GaloisRep.frame, Set.mem_ofPred_eq] at ⊢
    infer_instance


-- @@ L129-138 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations whose trace is `2` on `ker(Iᵥ → k(v)ˣ)`. -/
def traceConditionFunctor (v : Ω K) : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ ∈ localTameAbelianInertiaGroup v,
    LinearMap.trace _ _ ((toFramedGaloisRep ρ).toLocal v σ) = 2 }
  map {R S} f ρ hρ σ hσ := by
    have := hρ σ hσ
    simp only [GaloisRep.toLocal, toFramedGaloisRep_map, FramedGaloisRep.baseChange_map] at this ⊢
    simp [FramedGaloisRep.baseChange, ← Matrix.toLin'_apply', ← AddMonoidHom.map_trace,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.trace_eq_matrix_trace, this, map_ofNat]


-- @@ L140-149 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations whose trace is `2` on `Iᵥ`. -/
def narrowTraceConditionFunctor (v : Ω K) : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ ∈ localInertiaGroup v,
    LinearMap.trace _ _ ((toFramedGaloisRep ρ).toLocal v σ) = 2 }
  map {R S} f ρ hρ σ hσ := by
    have := hρ σ hσ
    simp only [GaloisRep.toLocal, toFramedGaloisRep_map, FramedGaloisRep.baseChange_map] at this ⊢
    simp [FramedGaloisRep.baseChange, ← Matrix.toLin'_apply', ← AddMonoidHom.map_trace,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.trace_eq_matrix_trace, this, map_ofNat]


-- @@ L151-163 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations with `det = εₗ`. -/
def detConditionFunctor (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] 𝓞] :
    Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ, (toFramedGaloisRep ρ).det σ =
    algebraMap 𝓞 R (algebraMap ℤ_[l] 𝓞 (cyclotomicCharacter (Kᵃˡᵍ) l σ)) }
  map {R S} f ρ hρ σ := by
    have := hρ σ
    simp only [toFramedGaloisRep_map, FramedGaloisRep.det_baseChange,
      ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_mk, MonoidHom.coe_coe,
      RingHom.coe_coe] at this ⊢
    rw [this]
    exact f.hom.commutes ..


-- @@ L165-165 verbatim
end Deformation
