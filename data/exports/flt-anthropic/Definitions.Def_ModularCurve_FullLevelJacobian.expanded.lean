import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_HeckeGalois_EichlerShimura


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup


-- @@ L11-11 verbatim
open scoped MatrixGroups ModularForm


-- @@ L13-13 verbatim
namespace ModularCurve.FullLevel


-- @@ L15-15 verbatim
section Level


-- @@ L17-17 verbatim
variable (q M' : ℕ)


-- @@ L19-20 verbatim
theorem dvd_sq_mul : q ∣ q ^ 2 * M' :=
  Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'


-- @@ L22-23 verbatim
def levelH : Subgroup (ZMod (q ^ 2 * M'))ˣ :=
  (ZMod.unitsMap (dvd_sq_mul q M')).ker


-- @@ L25-27 verbatim
theorem mem_levelH_iff (u : (ZMod (q ^ 2 * M'))ˣ) :
    u ∈ levelH q M' ↔ ZMod.unitsMap (dvd_sq_mul q M') u = 1 :=
  MonoidHom.mem_ker


-- @@ L29-30 verbatim
abbrev fieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  xHFunctionFieldBar (q ^ 2 * M') (levelH q M')


-- @@ L32-32 verbatim
abbrev jacComp : Type := JH (q ^ 2 * M') (levelH q M')


-- @@ L34-34 verbatim
end Level


-- @@ L36-36 verbatim
section Idx


-- @@ L38-38 verbatim
variable (q : ℕ)


-- @@ L40-40 verbatim
def Idx : Type := ↥(primitiveRoots q (AlgebraicClosure ℚ))


-- @@ L42-42 verbatim
instance : Fintype (Idx q) := inferInstanceAs (Fintype ↥(primitiveRoots q (AlgebraicClosure ℚ)))


-- @@ L44-44 verbatim
instance : DecidableEq (Idx q) := Classical.decEq _


-- @@ L46-46 verbatim
variable {q}


-- @@ L48-48 verbatim
def Idx.val (ζ : Idx q) : AlgebraicClosure ℚ := (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).1


-- @@ L50-51 verbatim
theorem Idx.ext {ζ ζ' : Idx q} (h : ζ.val = ζ'.val) : ζ = ζ' :=
  Subtype.ext h


-- @@ L53-53 verbatim
variable [Fact q.Prime]


-- @@ L55-56 verbatim
theorem Idx.isPrimitiveRoot (ζ : Idx q) : IsPrimitiveRoot ζ.val q :=
  (mem_primitiveRoots (Fact.out : q.Prime).pos).1 (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2


-- @@ L58-59 verbatim
def Idx.mk (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z q) : Idx q :=
  ⟨z, (mem_primitiveRoots (Fact.out : q.Prime).pos).2 hz⟩


-- @@ L61-62 verbatim
@[simp] theorem Idx.val_mk (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z q) : (Idx.mk z hz).val = z :=
  rfl


-- @@ L64-67 verbatim
instance : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Idx q) where
  smul σ ζ := Idx.mk (σ ζ.val) (ζ.isPrimitiveRoot.map_of_injective σ.injective)
  one_smul _ := Idx.ext rfl
  mul_smul _ _ _ := Idx.ext rfl


-- @@ L69-71 verbatim
@[simp] theorem Idx.val_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : Idx q) :
    (σ • ζ).val = σ ζ.val :=
  rfl


-- @@ L73-74 verbatim
def Idx.pow (d : (ZMod q)ˣ) (ζ : Idx q) : Idx q :=
  Idx.mk (ζ.val ^ (d : ZMod q).val) (ζ.isPrimitiveRoot.pow_of_coprime _ (ZMod.val_coe_unit_coprime d))


-- @@ L76-77 verbatim
@[simp] theorem Idx.val_pow (d : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow d).val = ζ.val ^ (d : ZMod q).val :=
  rfl


-- @@ L79-79 verbatim
end Idx


-- @@ L81-81 verbatim
section Carrier


-- @@ L83-83 verbatim
variable (q : ℕ) (M' : ℕ)


-- @@ L85-85 verbatim
def Jac : Type := Idx q → jacComp q M'


-- @@ L87-87 verbatim
instance : AddCommGroup (Jac q M') := inferInstanceAs (AddCommGroup (Idx q → jacComp q M'))


-- @@ L89-89 verbatim
variable {q M'}


-- @@ L91-91 verbatim
def Jac.eval (x : Jac q M') (ζ : Idx q) : jacComp q M' := (id x : Idx q → jacComp q M') ζ


-- @@ L93-93 verbatim
def Jac.mk (f : Idx q → jacComp q M') : Jac q M' := (id f : Jac q M')


-- @@ L95-95 verbatim
@[simp] theorem Jac.eval_mk (f : Idx q → jacComp q M') (ζ : Idx q) : (Jac.mk f).eval ζ = f ζ := rfl


-- @@ L97-97 verbatim
theorem Jac.ext {x y : Jac q M'} (h : ∀ ζ, x.eval ζ = y.eval ζ) : x = y := funext h


-- @@ L99-99 verbatim
@[simp] theorem Jac.eval_add (x y : Jac q M') (ζ : Idx q) : (x + y).eval ζ = x.eval ζ + y.eval ζ := rfl

-- @@ L100-100 verbatim
@[simp] theorem Jac.eval_zero (ζ : Idx q) : (0 : Jac q M').eval ζ = 0 := rfl

-- @@ L101-101 verbatim
@[simp] theorem Jac.eval_neg (x : Jac q M') (ζ : Idx q) : (-x).eval ζ = -x.eval ζ := rfl

-- @@ L102-102 verbatim
@[simp] theorem Jac.eval_sub (x y : Jac q M') (ζ : Idx q) : (x - y).eval ζ = x.eval ζ - y.eval ζ := rfl

-- @@ L103-103 verbatim
@[simp] theorem Jac.eval_zsmul (n : ℤ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl

-- @@ L104-104 verbatim
@[simp] theorem Jac.eval_nsmul (n : ℕ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl


-- @@ L106-109 verbatim
def Jac.mapIdx (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q) : Jac q M' →+ Jac q M' where
  toFun x := Jac.mk fun ζ => T ζ (x.eval (s ζ))
  map_zero' := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_zero, map_zero]
  map_add' x y := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_add, map_add]


-- @@ L111-112 verbatim
@[simp] theorem Jac.mapIdx_eval (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q)
    (x : Jac q M') (ζ : Idx q) : (Jac.mapIdx T s x).eval ζ = T ζ (x.eval (s ζ)) := rfl


-- @@ L114-114 verbatim
end Carrier


-- @@ L116-116 verbatim
section Galois


-- @@ L118-118 verbatim
variable (q : ℕ) [Fact q.Prime] (M' : ℕ)


-- @@ L120-120 verbatim
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L122-138 verbatim
def galJac : Gal →* AddMonoid.End (Jac q M') where
  toFun σ :=
    { toFun := fun x => Jac.mk fun ζ => σ • x.eval (σ⁻¹ • ζ)
      map_zero' := Jac.ext fun ζ => by
        simp only [Jac.eval_mk, Jac.eval_zero]
        exact smul_zero (A := jacComp q M') σ
      map_add' := fun x y => Jac.ext fun ζ => by
        simp only [Jac.eval_mk, Jac.eval_add]
        exact smul_add (A := jacComp q M') σ _ _ }
  map_one' := by
    refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
    show (1 : Gal) • x.eval ((1 : Gal)⁻¹ • ζ) = x.eval ζ
    rw [inv_one, one_smul, one_smul]
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
    show (σ * τ) • x.eval ((σ * τ)⁻¹ • ζ) = σ • (τ • x.eval (τ⁻¹ • (σ⁻¹ • ζ)))
    rw [mul_smul, mul_inv_rev, mul_smul]


-- @@ L140-142 verbatim
theorem galJac_eval (σ : Gal) (x : Jac q M') (ζ : Idx q) :
    (galJac q M' σ x).eval ζ = σ • x.eval (σ⁻¹ • ζ) :=
  rfl


-- @@ L144-144 verbatim
end Galois


-- @@ L146-146 verbatim
section LevelAut


-- @@ L148-148 verbatim
variable (q : ℕ) [Fact q.Prime] (M' : ℕ)


-- @@ L150-164 verbatim
def conjElem (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]
    (by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
      have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at h
        exact_mod_cast h
      rw [Matrix.det_fin_two_of]
      have : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) / q * ((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
          ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
        field_simp
      rw [this, hdet]
      exact one_ne_zero)


-- @@ L166-178 verbatim
def IsLevelAutBar (ζ : Idx q) (γ : SL(2, ℤ))
    (τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (ι : AlgebraicClosure ℚ →+* ℂ),
    ι ζ.val = Complex.exp (2 * Real.pi * Complex.I / q) →
      coeffMap ι
          ((τ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : fieldBar q M') :
            LaurentSeries (AlgebraicClosure ℚ)) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] conjElem q γ)) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] conjElem q γ))


-- @@ L180-185 verbatim
def levelAutBar (ζ : Idx q) (γ : SL(2, ℤ)) :
    fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M' :=
  haveI := Classical.dec (∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M',
    IsLevelAutBar q M' ζ γ τ)
  if h : ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ
  then h.choose else AlgEquiv.refl


-- @@ L187-187 verbatim
variable {q M'}


-- @@ L189-193 verbatim
theorem isLevelAutBar_levelAutBar {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    IsLevelAutBar q M' ζ γ (levelAutBar q M' ζ γ) := by
  rw [levelAutBar, dif_pos h]
  exact h.choose_spec


-- @@ L195-198 verbatim
theorem levelAutBar_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    levelAutBar q M' ζ γ = AlgEquiv.refl := by
  rw [levelAutBar, dif_neg h]


-- @@ L200-200 verbatim
variable (q M')


-- @@ L202-203 verbatim
def levelOp (ζ : Idx q) (γ : SL(2, ℤ)) : jacComp q M' →+ jacComp q M' :=
  DistribSMul.toAddMonoidHom (jacComp q M') (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ))


-- @@ L205-207 verbatim
theorem levelOp_apply (ζ : Idx q) (γ : SL(2, ℤ)) (x : jacComp q M') :
    levelOp q M' ζ γ x = SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) • x :=
  rfl


-- @@ L209-218 verbatim
variable {q M'} in

theorem levelOp_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ)
    (x : jacComp q M') : levelOp q M' ζ γ x = x := by
  rw [levelOp_apply, levelAutBar_of_not h]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') = 1 :=
    map_one _
  rw [this, one_smul]


-- @@ L220-222 verbatim
def LevelAutInputs : Prop :=
  ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
    ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ


-- @@ L224-224 verbatim
end LevelAut


-- @@ L226-226 verbatim
section Operators


-- @@ L228-228 verbatim
variable (q : ℕ) [Fact q.Prime] (M' : ℕ)


-- @@ L230-231 verbatim
def redQ : SL(2, ℤ) →* CuspidalType.GL2 q :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))))


-- @@ L233-235 verbatim
def diagOneElem (d : (ZMod q)ˣ) : CuspidalType.GL2 q :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (d : ZMod q)]
    (by rw [Matrix.det_fin_two_of]; simp [d.ne_zero])


-- @@ L237-239 verbatim
@[simp] theorem coe_diagOneElem (d : (ZMod q)ˣ) :
    ((diagOneElem q d : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, 0; 0, (d : ZMod q)] :=
  rfl


-- @@ L241-242 verbatim
def slJac (γ : SL(2, ℤ)) : Jac q M' →+ Jac q M' :=
  Jac.mapIdx (fun ζ => levelOp q M' ζ γ⁻¹) id


-- @@ L244-246 verbatim
@[simp] theorem slJac_eval (γ : SL(2, ℤ)) (x : Jac q M') (ζ : Idx q) :
    (slJac q M' γ x).eval ζ = levelOp q M' ζ γ⁻¹ (x.eval ζ) :=
  rfl


-- @@ L248-249 verbatim
def diagJac (d : (ZMod q)ˣ) : Jac q M' →+ Jac q M' :=
  Jac.mapIdx (fun _ => AddMonoidHom.id _) (Idx.pow d⁻¹)


-- @@ L251-253 verbatim
@[simp] theorem diagJac_eval (d : (ZMod q)ˣ) (x : Jac q M') (ζ : Idx q) :
    (diagJac q M' d x).eval ζ = x.eval (ζ.pow d⁻¹) :=
  rfl


-- @@ L255-258 verbatim
def GL2Laws : Prop :=
  ∃ G : CuspidalType.GL2 q →* AddMonoid.End (Jac q M'),
    (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → G (redQ q γ) = slJac q M' γ) ∧
      ∀ d : (ZMod q)ˣ, G (diagOneElem q d) = diagJac q M' d


-- @@ L260-262 verbatim
def gl2Jac : CuspidalType.GL2 q →* AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (GL2Laws q M')
  if h : GL2Laws q M' then h.choose else 1


-- @@ L264-264 verbatim
variable {q M'}


-- @@ L266-269 verbatim
theorem gl2Jac_redQ (h : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    gl2Jac q M' (redQ q γ) = slJac q M' γ := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.1 γ hγ


-- @@ L271-274 verbatim
theorem gl2Jac_diagOneElem (h : GL2Laws q M') (d : (ZMod q)ˣ) :
    gl2Jac q M' (diagOneElem q d) = diagJac q M' d := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.2 d


-- @@ L276-277 verbatim
theorem gl2Jac_of_not (h : ¬ GL2Laws q M') : gl2Jac q M' = 1 := by
  rw [gl2Jac, dif_neg h]


-- @@ L279-279 verbatim
variable (q M')


-- @@ L281-293 verbatim
def heckeGenJac (ℓ : ℕ) : AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (ℓ.Prime ∧ ¬ ℓ ∣ q * M')
  if h : ℓ.Prime ∧ ¬ ℓ ∣ q * M' then
    haveI : NeZero ℓ := ⟨h.1.ne_zero⟩
    have hq : ℓ.Coprime q := (Nat.Prime.coprime_iff_not_dvd h.1).2 fun hd => h.2 (hd.mul_right M')
    have hqM : ℓ.Coprime (q ^ 2 * M') := by
      refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hq) ?_
      exact (Nat.Prime.coprime_iff_not_dvd h.1).2 fun hd => h.2 (hd.mul_left q)
    (Jac.mapIdx
      (fun _ => (diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹).comp
        (heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ))
      (Idx.pow (ZMod.unitOfCoprime ℓ hq)⁻¹) : Jac q M' →+ Jac q M')
  else 0


-- @@ L295-295 verbatim
variable {q M'}


-- @@ L297-298 verbatim
theorem heckeGenJac_of_dvd {ℓ : ℕ} (h : ℓ ∣ q * M') : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h'.2 h)]


-- @@ L300-301 verbatim
theorem heckeGenJac_of_not_prime {ℓ : ℕ} (h : ¬ ℓ.Prime) : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h h'.1)]


-- @@ L303-311 verbatim
theorem heckeGenJac_eval {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓqM : ¬ ℓ ∣ q * M') (hq : ℓ.Coprime q)
    (hqM : ℓ.Coprime (q ^ 2 * M')) (x : Jac q M') (ζ : Idx q) :
    (heckeGenJac q M' ℓ x).eval ζ =
      diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ
            (x.eval (ζ.pow (ZMod.unitOfCoprime ℓ hq)⁻¹))) := by
  rw [heckeGenJac, dif_pos ⟨hℓ, hℓqM⟩]
  rfl


-- @@ L313-313 verbatim
variable (q M')


-- @@ L315-317 verbatim
def HeckeGenCommute : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeGenJac q M' ℓ * heckeGenJac q M' ℓ' = heckeGenJac q M' ℓ' * heckeGenJac q M' ℓ


-- @@ L319-319 verbatim
variable {q M'}


-- @@ L321-325 verbatim
theorem isMulCommutative_adjoin_heckeGenJac (h : HeckeGenCommute q M') :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')


-- @@ L327-335 verbatim
open scoped IsMulCommutative in

def heckeJacAux (h : HeckeGenCommute q M') :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ) :
      Subalgebra ℤ (AddMonoid.End (Jac q M'))) :=
  haveI := isMulCommutative_adjoin_heckeGenJac h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeGenJac q M' ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ))


-- @@ L337-341 verbatim
open scoped IsMulCommutative in
theorem heckeJacAux_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    (heckeJacAux h (heckeGen ℓ) : AddMonoid.End (Jac q M')) = heckeGenJac q M' ℓ := by
  haveI := isMulCommutative_adjoin_heckeGenJac h
  rw [heckeJacAux, heckeGen, MvPolynomial.aeval_X]


-- @@ L343-343 verbatim
variable (q M')


-- @@ L345-350 verbatim
def heckeJac : HeckeAlg →+* AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (HeckeGenCommute q M')
  if h : HeckeGenCommute q M' then
    ((Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ)).val.comp (heckeJacAux h)).toRingHom
  else (Int.castRingHom (AddMonoid.End (Jac q M'))).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))


-- @@ L352-352 verbatim
variable {q M'}


-- @@ L354-357 verbatim
theorem heckeJac_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = heckeGenJac q M' ℓ := by
  rw [heckeJac, dif_pos h]
  exact heckeJacAux_heckeGen h ℓ


-- @@ L359-362 verbatim
theorem heckeJac_heckeGen_of_not (h : ¬ HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  rw [heckeJac, dif_neg h, heckeGen, RingHom.comp_apply, MvPolynomial.eval₂Hom_zero_apply,
    MvPolynomial.constantCoeff_X, map_zero, map_zero]


-- @@ L364-368 verbatim
theorem heckeJac_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  by_cases h : HeckeGenCommute q M'
  · rw [heckeJac_heckeGen h, heckeGenJac_of_dvd hℓ]
  · exact heckeJac_heckeGen_of_not h ℓ


-- @@ L370-370 verbatim
end Operators


-- @@ L372-372 verbatim
section Tate


-- @@ L374-374 verbatim
variable (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]


-- @@ L376-376 verbatim
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L378-378 verbatim
example : DistribMulAction (AddMonoid.End (Jac q M')) (Jac q M') := inferInstance


-- @@ L380-385 verbatim
def tateEnd : AddMonoid.End (Jac q M') →+* Module.End ℤ_[lam] (TateModule lam (Jac q M')) where
  toFun := TateModule.rep lam (Jac q M') (AddMonoid.End (Jac q M'))
  map_one' := map_one _
  map_mul' f g := map_mul _ f g
  map_zero' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)


-- @@ L387-390 verbatim
omit [Fact q.Prime] in
theorem tateEnd_apply_coe (f : AddMonoid.End (Jac q M')) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateEnd q M' lam f x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = f ((x : ℕ → Jac q M') n) :=
  rfl


-- @@ L392-393 verbatim
def tateGal : Gal →* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).toMonoidHom.comp (galJac q M')


-- @@ L395-396 verbatim
def tateHecke : HeckeAlg →+* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).comp (heckeJac q M')


-- @@ L398-399 verbatim
def tateGL2 : CuspidalType.GL2 q →* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).toMonoidHom.comp (gl2Jac q M')


-- @@ L401-403 verbatim
theorem tateGal_apply_coe (σ : Gal) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGal q M' lam σ x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = galJac q M' σ ((x : ℕ → Jac q M') n) :=
  rfl


-- @@ L405-407 verbatim
theorem tateHecke_apply_coe (t : HeckeAlg) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateHecke q M' lam t x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = heckeJac q M' t ((x : ℕ → Jac q M') n) :=
  rfl


-- @@ L409-411 verbatim
theorem tateGL2_apply_coe (g : CuspidalType.GL2 q) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGL2 q M' lam g x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = gl2Jac q M' g ((x : ℕ → Jac q M') n) :=
  rfl


-- @@ L413-415 verbatim
theorem tateHecke_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    tateHecke q M' lam (heckeGen ℓ) = 0 := by
  rw [tateHecke, RingHom.comp_apply, heckeJac_heckeGen_of_dvd ℓ hℓ, map_zero]


-- @@ L417-417 verbatim
end Tate


-- @@ L419-419 verbatim
end ModularCurve.FullLevel


-- @@ L421-421 verbatim
end
