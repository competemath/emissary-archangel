import OAI.RingTheory.Tachikawa.StableShift


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa.AlgebraInduction

-- @@ L8-8 verbatim
open CategoryTheory

-- @@ L9-9 verbatim
open scoped ModuleCat.Algebra

-- @@ L10-10 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]


-- @@ L12-12 verbatim
def Bimod (_φ : R →ₐ[k] S) := S

-- @@ L13-13 verbatim
instance (φ : R →ₐ[k] S) : AddCommGroup (Bimod φ) := inferInstanceAs (AddCommGroup S)

-- @@ L14-14 verbatim
instance (φ : R →ₐ[k] S) : Module S (Bimod φ) := inferInstanceAs (Module S S)

-- @@ L15-15 verbatim
instance (φ : R →ₐ[k] S) : Module k (Bimod φ) := inferInstanceAs (Module k S)

-- @@ L16-16 verbatim
instance (φ : R →ₐ[k] S) : IsScalarTower k S (Bimod φ) := inferInstanceAs (IsScalarTower k S S)

-- @@ L17-18 verbatim
instance (φ : R →ₐ[k] S) : Module Rᵐᵒᵖ (Bimod φ) :=
  Module.compHom S φ.op.toRingHom

-- @@ L19-20 verbatim
instance (φ : R →ₐ[k] S) : SMulCommClass S Rᵐᵒᵖ (Bimod φ) where
  smul_comm s r x := (mul_assoc s x (φ r.unop)).symm

-- @@ L21-24 verbatim
instance (φ : R →ₐ[k] S) : IsScalarTower k Rᵐᵒᵖ (Bimod φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (show S from x) * φ (algebraMap k R c) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def, Algebra.commutes]

-- @@ L25-26 verbatim
instance (φ : R →ₐ[k] S) : Module.Projective S (Bimod φ) :=
  inferInstanceAs (Module.Projective S S)

-- @@ L27-28 verbatim
instance (φ : R →ₐ[k] S) [FiniteDimensional k S] : FiniteDimensional k (Bimod φ) :=
  inferInstanceAs (FiniteDimensional k S)


-- @@ L30-30 verbatim
variable (φ : R →ₐ[k] S)

-- @@ L31-32 verbatim
abbrev functor : ModuleCat.{0} R ⥤ ModuleCat.{0} S :=
  BalancedTensor.functor (k := k) (R := R) (S := S) (M := Bimod φ)

-- @@ L33-33 verbatim
abbrev res : ModuleCat.{0} S ⥤ ModuleCat.{0} R := ModuleCat.restrictScalars φ.toRingHom


-- @@ L35-41 verbatim
lemma mk_one_smul (N : ModuleCat.{0} R) (s : S) (n : N) :
    BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from s) n =
      s • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n := by
  have h := LinearMap.congr_fun ((BalancedTensor.mk (k := k) (R := R) (S := S) (N := N)).map_smul s (show Bimod φ from (1 : S))) n
  have hs : s • (show Bimod φ from (1 : S)) = (show Bimod φ from s) := mul_one s
  rw [hs] at h
  exact h


-- @@ L43-53 verbatim
def unit (N : ModuleCat.{0} R) : N ⟶ (res φ).obj ((functor φ).obj N) := ModuleCat.ofHom (Y := (res φ).obj ((functor φ).obj N))
  { toFun := fun n => BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
    map_add' := by intro x y; exact (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S))).map_add x y
    map_smul' := by
      intro r n
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) (r • n) =
        φ r • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
      rw [← BalancedTensor.balance]
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 * φ r : S)) n = _
      rw [one_mul]
      exact mk_one_smul φ N (φ r) n }


-- @@ L55-76 verbatim
def extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    (functor φ).obj N ⟶ P := ModuleCat.ofHom (BalancedTensor.lift
  { toFun := fun s =>
      { toFun := fun n => (show S from s) • (show P from f n)
        map_add' := by
          intro x y
          exact (congrArg (fun z : P => (show S from s) • z) (f.hom.map_add x y)).trans
            (smul_add (show S from s) (show P from f x) (show P from f y))
        map_smul' := by
          intro c n
          have hc := f.hom.map_smul (algebraMap k R c) n
          change (show P from f ((algebraMap k R c) • n)) = φ (algebraMap k R c) • (show P from f n) at hc
          rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at hc
          change (show S from s) • (show P from f (c • n)) = c • ((show S from s) • (show P from f n))
          rw [hc, smul_comm] }
    map_add' := by intro s t; ext n; exact add_smul (show S from s) (show S from t) (show P from f n)
    map_smul' := by intro s t; ext n; exact mul_smul s (show S from t) (show P from f n) }
  (by
    intro r s n
    change ((show S from s) * φ r) • f n = (show S from s) • (show P from f (r • n))
    rw [mul_smul, f.hom.map_smul]
    rfl))


-- @@ L78-79 verbatim
@[simp] lemma extend_mk {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P)
    (s : Bimod φ) (n : N) : extend φ f (BalancedTensor.mk s n) = (show S from s) • (show P from f n) := rfl


-- @@ L81-85 verbatim
lemma unit_extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    unit φ N ≫ (res φ).map (extend φ f) = f := by
  ext n
  change (1:S) • f n = f n
  exact one_smul S (f n)


-- @@ L87-96 verbatim
lemma extend_unit {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : (functor φ).obj N ⟶ P) :
    extend φ (unit φ N ≫ (res φ).map f) = f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro s n
  change (show S from s) • f.hom (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n) =
    f.hom (BalancedTensor.mk s n)
  trans f.hom ((show S from s) • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n)
  · exact (f.hom.map_smul _ _).symm
  exact congrArg f.hom (mk_one_smul φ N (show S from s) n).symm


-- @@ L98-103 verbatim
def homEquiv (N : ModuleCat.{0} R) (P : ModuleCat.{0} S) :
    ((functor φ).obj N ⟶ P) ≃ (N ⟶ (res φ).obj P) where
  toFun f := unit φ N ≫ (res φ).map f
  invFun := extend φ
  left_inv := extend_unit φ
  right_inv := unit_extend φ


-- @@ L105-108 verbatim
lemma unit_naturality {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    f ≫ unit φ N' = unit φ N ≫ (res φ).map ((functor φ).map f) := by
  ext n
  rfl


-- @@ L110-111 verbatim
instance (N : ModuleCat.{0} R) [Module.Finite R N] [Module.Projective R N] :
    Module.Projective S ((functor φ).obj N) := BalancedTensor.map_projective


-- @@ L113-122 verbatim
def underlyingEquiv (N : ModuleCat.{0} R) :
    ((functor φ).obj N) ≃ₗ[k]
      BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul S c
    (show BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) from x)


-- @@ L124-125 verbatim
instance [FiniteDimensional k S] (N : ModuleCat.{0} R) [FiniteDimensional k N] :
    FiniteDimensional k ((functor φ).obj N) := Module.Finite.equiv (underlyingEquiv φ N).symm


-- @@ L127-127 verbatim
end Tachikawa.AlgebraInduction




-- @@ L131-131 verbatim
namespace Tachikawa.Enveloping

-- @@ L132-132 verbatim
open CategoryTheory

-- @@ L133-133 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L134-134 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]


-- @@ L136-136 verbatim
def regular : ModuleCat (Alg k R R) := ofBimodule (k := k) (R := R) (S := R) R


-- @@ L138-147 verbatim
def regularUnderlyingEquiv : regular (k := k) (R := R) ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (action (k := k) (R := R) (S := R) R (algebraMap k (Alg k R R) c)) (show R from x) = c • (show R from x)
    rw [AlgHom.commutes]
    rfl


-- @@ L149-157 verbatim
def regularLeftEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * 1) = r * (show R from x)
    rw [mul_one]


-- @@ L159-167 verbatim
def regularRightEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change 1 * ((show R from x) * r.unop) = (show R from x) * r.unop
    rw [one_mul]


-- @@ L169-170 verbatim
instance [FiniteDimensional k R] : FiniteDimensional k (regular (k := k) (R := R)) :=
  Module.Finite.equiv regularUnderlyingEquiv.symm


-- @@ L172-172 verbatim
variable [FiniteDimensional k R]


-- @@ L174-175 verbatim
def regularFinite : FiniteModule k (Alg k R R) :=
  ⟨regular, Module.Finite.of_restrictScalars_finite k (Alg k R R) _⟩


-- @@ L177-178 verbatim
def regularResolution : ProjectiveResolution (regular (k := k) (R := R)) :=
  (regularFinite (k := k) (R := R)).projectiveResolution


-- @@ L180-183 verbatim
instance (n : ℕ) : Module.Finite (Alg k R R)
    ((regularResolution (k := k) (R := R)).complex.X n) := by
  change Module.Finite (Alg k R R) ((regularFinite (k := k) (R := R)).posTerm n)
  infer_instance


-- @@ L185-187 verbatim
instance (n : ℕ) : Module.Projective R
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_left _


-- @@ L189-191 verbatim
instance (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_right _


-- @@ L193-193 verbatim
end Tachikawa.Enveloping




-- @@ L197-197 verbatim
namespace Tachikawa.Enveloping

-- @@ L198-198 verbatim
open CategoryTheory

-- @@ L199-199 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L200-200 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)


-- @@ L202-203 verbatim
def twistedRegular : ModuleCat (Alg k R R) :=
  ofBimodule (k := k) (R := R) (S := R) (AlgebraInduction.Bimod σ.toAlgHom)


-- @@ L205-215 verbatim
def twistedUnderlying : twistedRegular σ ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change action (k := k) (R := R) (S := R)
      (AlgebraInduction.Bimod σ.toAlgHom) (algebraMap k (Alg k R R) c) x = c • (show R from x)
    rw [AlgHom.commutes]
    rfl


-- @@ L217-225 verbatim
def twistedLeftEquiv : Obj (twistedRegular σ) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * σ 1) = r * (show R from x)
    rw [map_one,mul_one]


-- @@ L227-235 verbatim
def twistedRightEquiv : Obj (twistedRegular σ) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := fun x => σ.symm (show R from x)
  invFun := fun x => σ x
  left_inv x := σ.apply_symm_apply x
  right_inv x := σ.symm_apply_apply x
  map_add' x y := map_add σ.symm x y
  map_smul' r x := by
    change σ.symm (1 * ((show R from x) * σ r.unop)) = σ.symm (show R from x) * r.unop
    rw [one_mul,map_mul,AlgEquiv.symm_apply_apply]


-- @@ L237-238 verbatim
instance [FiniteDimensional k R] : FiniteDimensional k (twistedRegular σ) :=
  Module.Finite.equiv (twistedUnderlying σ).symm


-- @@ L240-241 verbatim
instance : Module.Projective R (Obj (twistedRegular σ)) :=
  Module.Projective.of_equiv (twistedLeftEquiv σ).symm

-- @@ L242-245 verbatim
instance : Module.Projective Rᵐᵒᵖ (Obj (twistedRegular σ)) := by
  let : Module.Projective Rᵐᵒᵖ R :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (twistedRightEquiv σ).symm


-- @@ L247-250 verbatim
lemma twisted_left_smul (a : R) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = a * (show R from x) := by
  change a * ((show R from x) * σ 1) = _
  rw [map_one,mul_one]

-- @@ L251-254 verbatim
lemma twisted_right_smul (a : Rᵐᵒᵖ) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = (show R from x) * σ a.unop := by
  change 1 * ((show R from x) * σ a.unop) = _
  rw [one_mul]


-- @@ L256-256 verbatim
end Tachikawa.Enveloping




-- @@ L260-260 verbatim
namespace Tachikawa.Enveloping

-- @@ L261-261 verbatim
open CategoryTheory

-- @@ L262-262 verbatim
open scoped ModuleCat.Algebra

-- @@ L263-264 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R) (X : ModuleCat R)


-- @@ L266-275 verbatim
def twistedEvalBilinear : Obj (twistedRegular σ) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => (twistedLeftEquiv σ m) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (twistedLeftEquiv σ (r • m)) • x = r • ((twistedLeftEquiv σ m) • x)
    rw [map_smul,smul_eq_mul,mul_smul]


-- @@ L277-277 verbatim
variable (hσ : ∀ r : R, ∀ x : X, σ r • x = r • x)

-- @@ L278-278 verbatim
include hσ


-- @@ L280-286 verbatim
def twistedEval : evalObj X (twistedRegular σ) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (twistedEvalBilinear σ X) (by
    intro r m x
    change (twistedLeftEquiv σ (MulOpposite.op r • m)) • x =
      twistedLeftEquiv σ m • (r • x)
    change (1 * ((show R from m) * σ r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul,hσ]))


-- @@ L288-305 verbatim
lemma twistedTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  have hh : σ.symm r • x = r • x := by
    have := hσ (σ.symm r) x
    rw [σ.apply_symm_apply] at this
    exact this.symm
  rw [hh] at hb
  exact hb


-- @@ L307-321 verbatim
def twistedEvalInv : X ⟶ evalObj X (twistedRegular σ) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
        rw [← twistedTensor_move σ X hσ r x]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }


-- @@ L323-337 verbatim
def twistedEvalIso : evalObj X (twistedRegular σ) ≅ X where
  hom := twistedEval σ X hσ
  inv := twistedEvalInv σ X hσ
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move σ X hσ (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x


-- @@ L339-339 verbatim
end Tachikawa.Enveloping




-- @@ L343-343 verbatim
namespace Tachikawa

-- @@ L344-344 verbatim
open CategoryTheory

-- @@ L345-345 verbatim
open scoped ModuleCat.Algebra

-- @@ L346-346 verbatim
namespace SymmetrizingForm

-- @@ L347-349 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R)


-- @@ L351-351 verbatim
abbrev twistFunctor := AlgebraInduction.res σ.symm.toAlgHom


-- @@ L353-387 verbatim
def freeTwistIso (ι : Type) :
    (twistFunctor σ).obj (ModuleCat.of R (ι → R)) ≅ ModuleCat.of R (ι → R) where
  hom := ModuleCat.ofHom (X := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    (Y := ModuleCat.of R (ι → R))
    { toFun x i := σ (x i)
      map_add' x y := by ext i; exact map_add σ _ _
      map_smul' r x := by
        ext i
        change σ (σ.symm r * x i) = r * σ (x i)
        rw [map_mul,AlgEquiv.apply_symm_apply] }
  inv := ModuleCat.ofHom (X := ModuleCat.of R (ι → R))
    (Y := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    { toFun x i := σ.symm (x i)
      map_add' x y := by
        change (fun i => σ.symm (x i+y i)) = fun i => σ.symm (x i)+σ.symm (y i)
        funext i
        exact map_add σ.symm _ _
      map_smul' r x := by
        change (fun i => σ.symm (r * x i)) = fun i => σ.symm r * σ.symm (x i)
        funext i
        rw [map_mul] }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ.symm (σ (x i))) = x
    funext i
    exact AlgEquiv.symm_apply_apply σ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ (σ.symm (x i))) = x
    funext i
    exact AlgEquiv.apply_symm_apply σ _


-- @@ L389-389 verbatim
variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)


-- @@ L391-393 verbatim
def twistToFree (g : N →ₗ[R] (ι → R)) :
    (twistFunctor σ).obj N →ₗ[R] (ι → R) :=
  ((twistFunctor σ).map (ModuleCat.ofHom g) ≫ (freeTwistIso σ ι).hom).hom


-- @@ L395-397 verbatim
def twistFromFree (f : (ι → R) →ₗ[R] N) :
    (ι → R) →ₗ[R] (twistFunctor σ).obj N :=
  ((freeTwistIso σ ι).inv ≫ (twistFunctor σ).map (ModuleCat.ofHom f)).hom


-- @@ L399-407 verbatim
omit [FiniteDimensional k R] [Fintype ι] in
lemma twistFromFree_single (f : (ι → R) →ₗ[R] N) (i : ι) :
    twistFromFree σ ι N f (Pi.single i 1) = f (Pi.single i 1) := by
  change f (fun j => σ.symm ((Pi.single i (1:R) : ι → R) j)) = _
  congr 1
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]


-- @@ L409-415 verbatim
lemma freeHomDual_twist (c : k) (hc : ∀ r, t.linear (σ r) = c * t.linear r)
    (g : N →ₗ[R] (ι → R)) (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι (twistToFree σ ι N g) (twistFromFree σ ι N f) =
      c * t.freeHomDual ι g f := by
  simp only [freeHomDual_apply,twistFromFree_single]
  change (∑ i, t.linear (σ (g (f (Pi.single i 1)) i))) = _
  simp only [hc,Finset.mul_sum]


-- @@ L417-417 verbatim
end SymmetrizingForm

-- @@ L418-418 verbatim
end Tachikawa




-- @@ L422-422 verbatim
namespace Tachikawa.Enveloping

-- @@ L423-423 verbatim
open CategoryTheory

-- @@ L424-424 verbatim
open scoped ModuleCat.Algebra

-- @@ L425-426 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R)


-- @@ L428-429 verbatim
abbrev twistedTensorFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} R :=
  BalancedTensor.functor (k := k) (R := R) (S := R) (M := Obj (twistedRegular σ))


-- @@ L431-443 verbatim
lemma twistedTensor_move_general (X : ModuleCat R) (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  exact hb


-- @@ L445-469 verbatim
def twistedTensorMap (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ⟶ (SymmetrizingForm.twistFunctor σ).obj X :=
  ModuleCat.ofHom (Y := (SymmetrizingForm.twistFunctor σ).obj X)
    (BalancedTensor.lift (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X)
      (P := (SymmetrizingForm.twistFunctor σ).obj X)
      { toFun := fun m =>
          { toFun := fun x => σ.symm (show R from m) • x
            map_add' := fun x y => smul_add _ x y
            map_smul' := fun c x => by
              change σ.symm (show R from m) • ((algebraMap k R c) • x) =
                σ.symm (algebraMap k R c) • (σ.symm (show R from m) • x)
              rw [σ.symm.commutes,IsScalarTower.algebraMap_smul R,
                IsScalarTower.algebraMap_smul R]
              exact smul_comm _ _ _ }
        map_add' := fun m n => by ext x; exact (congrArg (fun r => r • x) (map_add σ.symm _ _)).trans (add_smul _ _ _)
        map_smul' := fun r m => by
          ext x
          change σ.symm (show R from r • m) • x = σ.symm r • (σ.symm (show R from m) • x)
          rw [twisted_left_smul,map_mul,mul_smul] }
      (by
        intro r m x
        change σ.symm (show R from MulOpposite.op r • m) • x = σ.symm (show R from m) • (r • x)
        rw [twisted_right_smul,map_mul,σ.symm_apply_apply,mul_smul]
        rfl))


-- @@ L471-486 verbatim
def twistedTensorInv (X : ModuleCat R) :
    (SymmetrizingForm.twistFunctor σ).obj X ⟶ (twistedTensorFunctor σ).obj X :=
  ModuleCat.ofHom (X := (SymmetrizingForm.twistFunctor σ).obj X)
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • (show X from x)) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
        rw [← twistedTensor_move_general]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }


-- @@ L488-505 verbatim
def twistedTensorIso (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ≅ (SymmetrizingForm.twistFunctor σ).obj X where
  hom := twistedTensorMap σ X
  inv := twistedTensorInv σ X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext (k := k) (R := R) (S := R)
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := R) (N := X)
      (show Obj (twistedRegular σ) from (1:R))
      (σ.symm (show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move_general σ X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change σ.symm (1:R) • (show X from x) = x
    rw [map_one,one_smul]


-- @@ L507-514 verbatim
def twistedTensorNatIso : twistedTensorFunctor σ ≅ SymmetrizingForm.twistFunctor σ :=
  NatIso.ofComponents (twistedTensorIso σ) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change σ.symm (show R from m) • f x = f (σ.symm (show R from m) • x)
    exact (f.hom.map_smul _ _).symm)


-- @@ L516-516 verbatim
end Tachikawa.Enveloping


-- @@ L518-518 verbatim
end


-- @@ L520-520 verbatim
end OAI
