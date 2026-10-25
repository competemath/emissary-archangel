import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank


-- @@ L10-14 verbatim
/-! # Pullback of locally free sheaves and their rank

The pullback of a locally free sheaf is locally free, and its rank at `x` equals the rank of the
original sheaf at `f(x)`.
-/


-- @@ L16-16 verbatim
set_option autoImplicit false

-- @@ L17-17 verbatim
set_option maxHeartbeats 400000


-- @@ L19-19 verbatim
universe u v w u' v'


-- @@ L21-21 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L22-22 verbatim
open scoped AlgebraicGeometry TensorProduct


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace ModulesPullbackRankInfinite


-- @@ L28-30 verbatim
open Classical

/- Coordinate projections force the standard residue-fiber family to be linearly independent. -/

-- @@ L31-46 verbatim
private theorem fiber_standard_li {A K M I : Type*} [CommRing A] [Field K]
    [AddCommGroup M] [Module A M] [Algebra A K]
    (b : I → M) (p : I → (M →ₗ[A] A))
    (hp : ∀ i j, p i (b j) = if j = i then 1 else 0) :
    LinearIndependent K
      (fun i => (TensorProduct.mk A K M) 1 (b i)) := by
  let q : I → (M →ₗ[A] K) :=
    fun i => (Algebra.linearMap A K).comp (p i)
  let L : I → ((K ⊗[A] M) →ₗ[K] K) := fun i =>
    TensorProduct.AlgebraTensorModule.lift (A := K)
      (LinearMap.smulRight (LinearMap.id : K →ₗ[K] K) (q i))
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (L i) hg
  rw [map_sum] at h
  simpa [L, q, hp, hi] using h


-- @@ L48-49 verbatim
private abbrev freeM (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) : Y.Modules :=
  MiyaokaMori.FreeStalk.freeM Y I


-- @@ L51-52 verbatim
private abbrev freeStalk (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) : Type u :=
  (freeM Y I).presheaf.stalk y


-- @@ L54-55 verbatim
private abbrev astalk (Y : AlgebraicGeometry.Scheme.{u}) (y : Y) : Type u :=
  Y.presheaf.stalk y


-- @@ L57-59 verbatim
private instance free_stalk_module (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) :
    Module (astalk Y y) (freeStalk Y I y) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (freeM Y I) y


-- @@ L61-63 verbatim
private instance unit_stalk_module (Y : AlgebraicGeometry.Scheme.{u}) (y : Y) :
    Module (astalk Y y) ((AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.stalk y) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkModule Y (AlgebraicGeometry.Scheme.Modules.unitModule Y) y


-- @@ L65-68 verbatim
private def freeProj (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y) (i : I) :
    freeStalk Y I y →ₗ[astalk Y y] astalk Y y :=
  (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Y y).toLinearMap.comp
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y (MiyaokaMori.FreeStalk.proj Y I i))


-- @@ L70-86 verbatim
private lemma freeProj_basis (Y : AlgebraicGeometry.Scheme.{u}) (I : Type u) (y : Y)
    (i j : I) :
    freeProj Y I y i (MiyaokaMori.FreeStalk.b I j y) = if j = i then 1 else 0 := by
  classical
  rw [freeProj, LinearMap.comp_apply, MiyaokaMori.FreeStalk.stalkMap_proj_b]
  split_ifs with h
  · subst h
    have hu :
        (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv Y y)
            ((ConcreteCategory.hom
              ((AlgebraicGeometry.Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial))
              (MiyaokaMori.FreeStalk.uSec ⊤ 1)) = 1 := by
      simpa [AlgebraicGeometry.Scheme.Modules.unitModule, MiyaokaMori.FreeStalk.uSec] using
        (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv_germ Y y ⊤ trivial
          (1 : Γ(Y, ⊤)))
    exact hu
  · simp


-- @@ L88-105 verbatim
private def transportedProj
    {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (S : M ≃ₛₗ[(σ : A →+* B)] N) (p : M →ₗ[A] A) :
    N →ₗ[B] B := by
  let psl : M →ₛₗ[(RingHom.id A)] A := p
  let q : N →ₛₗ[(σ.symm : B →+* A)] A := psl.comp S.symm.toLinearMap
  exact LinearMap.mk
    { toFun := fun n => σ (q n)
      map_add' := by intro x y; simp }
    (by
      intro b n
      dsimp [q, psl]
      rw [map_smulₛₗ, map_smulₛₗ]
      simp [smul_eq_mul])


-- @@ L107-116 verbatim
private lemma transportedProj_apply
    {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (σ : A ≃+* B)
    [RingHomInvPair (σ : A →+* B) (σ.symm : B →+* A)]
    [RingHomInvPair (σ.symm : B →+* A) (σ : A →+* B)]
    (S : M ≃ₛₗ[(σ : A →+* B)] N) (p : M →ₗ[A] A)
    (m : M) :
    transportedProj σ S p (S m) = σ (p m) := by
  simp [transportedProj]


-- @@ L118-171 verbatim
private theorem rank_zero_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) (hI : Infinite I) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = 0 := by
  let y : U.toScheme := ⟨x, hx⟩
  let e' : E.restrict U.ι ≅ freeM U.toScheme I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  letI : Module (U.toScheme.presheaf.stalk y)
      ((E.restrict U.ι).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  letI : Module (U.toScheme.presheaf.stalk y)
      (freeStalk U.toScheme I y) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (freeM U.toScheme I) y
  letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L : (E.restrict U.ι).presheaf.stalk y ≃ₗ[U.toScheme.presheaf.stalk y]
      freeStalk U.toScheme I y :=
    ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  let σ : U.toScheme.presheaf.stalk y ≃+* X.presheaf.stalk x :=
    (U.stalkIso y).commRingCatIsoToRingEquiv
  letI : RingHomInvPair
      (σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x)
      (σ.symm : X.presheaf.stalk x →+* U.toScheme.presheaf.stalk y) :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair
      (σ.symm : X.presheaf.stalk x →+* U.toScheme.presheaf.stalk y)
      (σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x) :=
    RingHomInvPair.of_ringEquiv σ.symm
  let S : (E.restrict U.ι).presheaf.stalk y ≃ₛₗ[(σ : _)] E.presheaf.stalk x := by
    simpa [σ] using
      (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y)
  let T : freeStalk U.toScheme I y ≃ₛₗ[
      (σ : U.toScheme.presheaf.stalk y →+* X.presheaf.stalk x)]
      E.presheaf.stalk x := by
    simpa [σ] using L.symm.trans S
  let bE : I → E.presheaf.stalk x := fun i =>
    T (MiyaokaMori.FreeStalk.b (Y := U.toScheme) I i y)
  let pE : I → (E.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :=
    fun i => transportedProj σ T (freeProj U.toScheme I y i)
  have hpE : ∀ i j, pE i (bE j) = if j = i then 1 else 0 := by
    intro i j
    dsimp [pE, bE]
    rw [transportedProj_apply]
    rw [freeProj_basis]
    split_ifs with h
    · subst h
      simp
    · simp
  unfold AlgebraicGeometry.Scheme.Modules.rankAtStalk
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  exact (fiber_standard_li bE pE hpE).finrank_eq_zero_of_infinite


-- @@ L173-173 verbatim
end ModulesPullbackRankInfinite


-- @@ L175-228 verbatim
/-- The pullback of a locally free sheaf is locally free, with `rankAtStalk (f^*F) x = rankAtStalk F (f x)`. -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [F.IsLocallyFree] :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F).IsLocallyFree ∧
      ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F) x =
        AlgebraicGeometry.Scheme.Modules.rankAtStalk F (f.base x) := by
  constructor
  · apply AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free
    intro x
    obtain ⟨U, I, hy, ⟨e⟩⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree F (f.base x)
    refine ⟨f ⁻¹ᵁ U, I, ?_, ?_⟩
    · exact hy
    · exact ⟨
        (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app F ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app F ≪≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app F).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
          e ≪≫
        AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso (f ∣_ U) I⟩
  · intro x
    obtain ⟨U, I, hy, ⟨e⟩⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree F (f.base x)
    let P := (AlgebraicGeometry.Scheme.Modules.pullback f).obj F
    let eP : (AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj P ≅
        SheafOfModules.free (R := (f ⁻¹ᵁ U).toScheme.ringCatSheaf) I :=
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app F ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app F ≪≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app F).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
        AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso (f ∣_ U) I
    classical
    by_cases hI : Finite I
    · letI : Finite I := hI
      letI : Fintype I := Fintype.ofFinite I
      have hP := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
        P (f ⁻¹ᵁ U) I eP x hy
      have hF := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
        F U I e (f.base x) hy
      have hP' : AlgebraicGeometry.Scheme.Modules.rankAtStalk
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F) x = Fintype.card I := by
        simpa [P] using hP
      exact hP'.trans hF.symm
    · have hInf : Infinite I := not_finite_iff_infinite.mp hI
      have hP := ModulesPullbackRankInfinite.rank_zero_of_restrict_iso_free
        P (f ⁻¹ᵁ U) I eP x hy hInf
      have hF := ModulesPullbackRankInfinite.rank_zero_of_restrict_iso_free
        F U I e (f.base x) hy hInf
      have hP' : AlgebraicGeometry.Scheme.Modules.rankAtStalk
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F) x = 0 := by
        simpa [P] using hP
      exact hP'.trans hF.symm


-- @@ L230-230 verbatim
end
