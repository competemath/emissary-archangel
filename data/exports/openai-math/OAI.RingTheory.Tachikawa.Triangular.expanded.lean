import OAI.RingTheory.Tachikawa.Delta


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa.Triangular

-- @@ L8-8 verbatim
open CategoryTheory

-- @@ L9-9 verbatim
open scoped ModuleCat.Algebra

-- @@ L10-10 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]


-- @@ L12-12 verbatim
def Off (F : ModuleCat (Enveloping.Alg k R R)) : Type := Enveloping.Obj F

-- @@ L13-14 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : AddCommGroup (Off F) :=
  inferInstanceAs (AddCommGroup (Enveloping.Obj F))

-- @@ L15-16 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : Module k (Off F) :=
  inferInstanceAs (Module k (Enveloping.Obj F))

-- @@ L17-18 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : Module (R × R) (Off F) :=
  Module.compHom (Enveloping.Obj F) (RingHom.snd R R)

-- @@ L19-20 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : Module (R × R)ᵐᵒᵖ (Off F) :=
  Module.compHom (Enveloping.Obj F) (RingHom.op (RingHom.fst R R))

-- @@ L21-22 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass (R × R) (R × R)ᵐᵒᵖ (Off F) where
  smul_comm a b x := smul_comm a.2 (MulOpposite.op b.unop.1) (show Enveloping.Obj F from x)

-- @@ L23-24 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : IsScalarTower k (R × R) (Off F) where
  smul_assoc c a x := smul_assoc c a.2 (show Enveloping.Obj F from x)

-- @@ L25-26 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : IsScalarTower k (R × R)ᵐᵒᵖ (Off F) where
  smul_assoc c a x := smul_assoc c (MulOpposite.op a.unop.1) (show Enveloping.Obj F from x)

-- @@ L27-28 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass k (R × R) (Off F) where
  smul_comm c a x := smul_comm c a.2 (show Enveloping.Obj F from x)

-- @@ L29-30 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass k (R × R)ᵐᵒᵖ (Off F) where
  smul_comm c a x := smul_comm c (MulOpposite.op a.unop.1) (show Enveloping.Obj F from x)


-- @@ L32-32 verbatim
abbrev Alg (F : ModuleCat (Enveloping.Alg k R R)) := TrivSqZeroExt (R × R) (Off F)

-- @@ L33-36 verbatim
instance (F : ModuleCat (Enveloping.Alg k R R)) [FiniteDimensional k R]
    [FiniteDimensional k F] : FiniteDimensional k (Alg F) := by
  let : FiniteDimensional k (Off F) := inferInstanceAs (FiniteDimensional k F)
  exact inferInstanceAs (FiniteDimensional k ((R × R) × Off F))


-- @@ L38-38 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R))

-- @@ L39-39 verbatim
def upper : Alg F →ₐ[k] R := (AlgHom.fst k R R).comp (TrivSqZeroExt.fstHom k (R × R) (Off F))

-- @@ L40-40 verbatim
def lower : Alg F →ₐ[k] R := (AlgHom.snd k R R).comp (TrivSqZeroExt.fstHom k (R × R) (Off F))


-- @@ L42-45 verbatim
def off : Alg F →ₗ[k] Enveloping.Obj F where
  toFun a := a.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L47-47 verbatim
@[simp] lemma upper_apply (a : Alg F) : upper F a = a.fst.1 := rfl

-- @@ L48-48 verbatim
@[simp] lemma lower_apply (a : Alg F) : lower F a = a.fst.2 := rfl

-- @@ L49-49 verbatim
@[simp] lemma off_apply (a : Alg F) : off F a = a.snd := rfl

-- @@ L50-51 verbatim
lemma off_mul (a b : Alg F) :
    off F (a*b) = lower F a • off F b + MulOpposite.op (upper F b) • off F a := rfl


-- @@ L53-53 verbatim
def e₀ : Alg F := TrivSqZeroExt.inl (1,0)

-- @@ L54-54 verbatim
def e₁ : Alg F := TrivSqZeroExt.inl (0,1)

-- @@ L55-58 verbatim
lemma idempotent_e₀ : IsIdempotentElem (e₀ F) := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp [e₀]
  · simp [e₀]

-- @@ L59-62 verbatim
lemma idempotent_e₁ : IsIdempotentElem (e₁ F) := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp [e₁]
  · simp [e₁]

-- @@ L63-66 verbatim
lemma e₀_add_e₁ : e₀ F + e₁ F = 1 := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp [e₀,e₁]
  · simp [e₀,e₁]


-- @@ L68-68 verbatim
end Tachikawa.Triangular




-- @@ L72-72 verbatim
namespace Tachikawa.BalancedTensor

-- @@ L73-75 verbatim
variable {k R S M N : Type*} [Field k] [Ring R] [Ring S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [AddCommGroup N] [Module k N] [Module R N]


-- @@ L77-80 verbatim
@[simp] lemma mk_zero_left (n : N) :
    mk (k := k) (R := R) (S := S) (0 : M) n = 0 :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_zero (mk (k := k) (R := R) (S := S)))

-- @@ L81-84 verbatim
@[simp] lemma mk_add_left (a b : M) (n : N) :
    mk (k := k) (R := R) (S := S) (a+b) n = mk a n + mk b n :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_add (mk (k := k) (R := R) (S := S)) a b)

-- @@ L85-88 verbatim
@[simp] lemma mk_smul_left (s : S) (a : M) (n : N) :
    mk (k := k) (R := R) (S := S) (s • a) n = s • mk a n :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_smul (mk (k := k) (R := R) (S := S)) s a)


-- @@ L90-90 verbatim
end Tachikawa.BalancedTensor




-- @@ L94-94 verbatim
namespace Tachikawa.Triangular

-- @@ L95-95 verbatim
open CategoryTheory

-- @@ L96-96 verbatim
open scoped ModuleCat.Algebra

-- @@ L97-97 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L98-99 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R)) (L N : ModuleCat R)
  (α : Enveloping.evalType L F →ₗ[R] N)


-- @@ L101-102 verbatim
def Triple (F : ModuleCat (Enveloping.Alg k R R)) (L N : ModuleCat R)
    (_α : Enveloping.evalType L F →ₗ[R] N) : Type := L × N

-- @@ L103-103 verbatim
instance : AddCommGroup (Triple F L N α) := inferInstanceAs (AddCommGroup (L × N))

-- @@ L104-104 verbatim
instance : Module k (Triple F L N α) := inferInstanceAs (Module k (L × N))

-- @@ L105-152 verbatim
instance : Module (Alg F) (Triple F L N α) where
  smul a x := (upper F a • x.1, α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2)
  one_smul x := by
    change L × N at x
    apply Prod.ext
    · exact one_smul R x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (1:R) • x.2 = x.2
      simp
  mul_smul a b x := by
    change L × N at x
    apply Prod.ext
    · exact mul_smul (upper F a) (upper F b) x.1
    · change α (BalancedTensor.mk (off F (a*b)) x.1) + lower F (a*b) • x.2 =
        α (BalancedTensor.mk (off F a) (upper F b • x.1)) +
          lower F a • (α (BalancedTensor.mk (off F b) x.1) + lower F b • x.2)
      rw [off_mul, map_mul, BalancedTensor.mk_add_left,
        BalancedTensor.mk_smul_left, BalancedTensor.balance, α.map_add,
        α.map_smul, smul_add, mul_smul]
      abel
  smul_zero a := by
    apply Prod.ext
    · exact smul_zero (upper F a)
    · change α (BalancedTensor.mk (off F a) (0 : L)) + lower F a • (0 : N) = 0
      simp
  smul_add a x y := by
    change L × N at x y
    apply Prod.ext
    · exact smul_add (upper F a) x.1 y.1
    · change α (BalancedTensor.mk (off F a) (x.1+y.1)) + lower F a • (x.2+y.2) = _
      rw [(BalancedTensor.mk (off F a)).map_add, α.map_add, smul_add]
      change _ = (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) +
        (α (BalancedTensor.mk (off F a) y.1) + lower F a • y.2)
      abel
  add_smul a b x := by
    change L × N at x
    apply Prod.ext
    · exact add_smul (upper F a) (upper F b) x.1
    · change α (BalancedTensor.mk (off F (a+b)) x.1) + lower F (a+b) • x.2 = _
      rw [(off F).map_add, map_add (lower F), BalancedTensor.mk_add_left, α.map_add, add_smul]
      change _ = (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) +
        (α (BalancedTensor.mk (off F b) x.1) + lower F b • x.2)
      abel
  zero_smul x := by
    change L × N at x
    apply Prod.ext
    · exact zero_smul R x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (0:R) • x.2 = 0
      simp


-- @@ L154-160 verbatim
instance : IsScalarTower k (Alg F) (Triple F L N α) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    apply Prod.ext
    · exact IsScalarTower.algebraMap_smul R c x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) +
        algebraMap k R c • x.2 = c • x.2
      simp


-- @@ L162-162 verbatim
def tripleObj : ModuleCat (Alg F) := ModuleCat.of (Alg F) (Triple F L N α)


-- @@ L164-165 verbatim
@[simp] lemma triple_smul_fst (a : Alg F) (x : Triple F L N α) :
    (a • x).1 = upper F a • x.1 := rfl

-- @@ L166-167 verbatim
@[simp] lemma triple_smul_snd (a : Alg F) (x : Triple F L N α) :
    (a • x).2 = α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2 := rfl


-- @@ L169-170 verbatim
instance [FiniteDimensional k L] [FiniteDimensional k N] :
    FiniteDimensional k (Triple F L N α) := inferInstanceAs (FiniteDimensional k (L × N))


-- @@ L172-172 verbatim
end Tachikawa.Triangular




-- @@ L176-176 verbatim
namespace Tachikawa.Triangular

-- @@ L177-177 verbatim
open CategoryTheory

-- @@ L178-178 verbatim
open scoped ModuleCat.Algebra

-- @@ L179-179 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L180-181 verbatim
variable {F : ModuleCat (Enveloping.Alg k R R)} {L N L' N' : ModuleCat R}
  {α : Enveloping.evalType L F →ₗ[R] N} {β : Enveloping.evalType L' F →ₗ[R] N'}


-- @@ L183-188 verbatim
lemma e₀_smul_triple (x : Triple F L N α) : e₀ F • x = (x.1,0) := by
  apply Prod.ext
  · change (1:R) • x.1 = x.1
    exact one_smul R x.1
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (0:R) • x.2 = 0
    simp

-- @@ L189-194 verbatim
lemma e₁_smul_triple (x : Triple F L N α) : e₁ F • x = (0,x.2) := by
  apply Prod.ext
  · change (0:R) • x.1 = 0
    exact zero_smul R x.1
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (1:R) • x.2 = x.2
    simp

-- @@ L195-200 verbatim
lemma diagonal_smul_triple (r : R) (x : Triple F L N α) :
    (TrivSqZeroExt.inl (r,r) : Alg F) • x = (r • x.1,r • x.2) := by
  apply Prod.ext
  · rfl
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + r • x.2 = r • x.2
    simp


-- @@ L202-214 verbatim
def tripleMap (g : L →ₗ[R] L') (h : N →ₗ[R] N')
    (hc : h.comp α = β.comp (BalancedTensor.mapRight (M := Enveloping.Obj F) g)) :
    Triple F L N α →ₗ[Alg F] Triple F L' N' β where
  toFun x := (g x.1,h x.2)
  map_add' x y := Prod.ext (g.map_add _ _) (h.map_add _ _)
  map_smul' a x := by
    apply Prod.ext
    · exact g.map_smul _ _
    · change h (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) =
        β (BalancedTensor.mk (off F a) (g x.1)) + lower F a • h x.2
      rw [h.map_add,h.map_smul]
      have he := LinearMap.congr_fun hc (BalancedTensor.mk (off F a) x.1)
      exact congrArg (· + lower F a • h x.2) he


-- @@ L216-216 verbatim
variable (f : Triple F L N α →ₗ[Alg F] Triple F L' N' β)


-- @@ L218-221 verbatim
lemma hom_fst_e₁ (y : N) : (f (0,y)).1 = 0 := by
  have h := congrArg Prod.fst (f.map_smul (e₁ F) (show Triple F L N α from (0,y)))
  rw [e₁_smul_triple,e₁_smul_triple] at h
  exact h

-- @@ L222-225 verbatim
lemma hom_snd_e₀ (x : L) : (f (x,0)).2 = 0 := by
  have h := congrArg Prod.snd (f.map_smul (e₀ F) (show Triple F L N α from (x,0)))
  rw [e₀_smul_triple,e₀_smul_triple] at h
  exact h


-- @@ L227-238 verbatim
def homUpper : L →ₗ[R] L' where
  toFun x := (f (x,0)).1
  map_add' x y := by
    have he := congrArg Prod.fst
      (f.map_add (show Triple F L N α from (x,0)) (show Triple F L N α from (y,0)))
    change (f (x+y,(0:N)+0)).1 = (f (x,0)).1 + (f (y,0)).1 at he
    simpa only [add_zero] using he
  map_smul' r x := by
    have h := congrArg Prod.fst (f.map_smul (TrivSqZeroExt.inl (r,r))
      (show Triple F L N α from (x,0)))
    rw [diagonal_smul_triple,diagonal_smul_triple,smul_zero] at h
    exact h


-- @@ L240-251 verbatim
def homLower : N →ₗ[R] N' where
  toFun y := (f (0,y)).2
  map_add' x y := by
    have he := congrArg Prod.snd
      (f.map_add (show Triple F L N α from (0,x)) (show Triple F L N α from (0,y)))
    change (f ((0:L)+0,x+y)).2 = (f (0,x)).2 + (f (0,y)).2 at he
    simpa only [zero_add] using he
  map_smul' r y := by
    have h := congrArg Prod.snd (f.map_smul (TrivSqZeroExt.inl (r,r))
      (show Triple F L N α from (0,y)))
    rw [diagonal_smul_triple,diagonal_smul_triple,smul_zero] at h
    exact h


-- @@ L253-262 verbatim
lemma hom_pair (x : L) (y : N) : f (x,y) = (homUpper f x,homLower f y) := by
  have h := f.map_add (show Triple F L N α from (x,0)) (show Triple F L N α from (0,y))
  change f (x+0,0+y) = f (x,0)+f (0,y) at h
  rw [add_zero,zero_add] at h
  rw [h]
  apply Prod.ext
  · change (f (x,0)).1 + (f (0,y)).1 = (f (x,0)).1
    rw [hom_fst_e₁,add_zero]
  · change (f (x,0)).2 + (f (0,y)).2 = (f (0,y)).2
    rw [hom_snd_e₀,zero_add]


-- @@ L264-274 verbatim
lemma hom_compatible : (homLower f).comp α =
    β.comp (BalancedTensor.mapRight (M := Enveloping.Obj F) (homUpper f)) := by
  apply BalancedTensor.hom_ext
  intro m x
  have h := congrArg Prod.snd (f.map_smul (TrivSqZeroExt.inr (show Off F from m))
    (show Triple F L N α from (x,0)))
  change (f (0 • x, α (BalancedTensor.mk m x) + 0 • (0:N))).2 =
    β (BalancedTensor.mk m (f (x,0)).1) + 0 • (f (x,0)).2 at h
  change (f (0,α (BalancedTensor.mk m x))).2 =
    β (BalancedTensor.mk m (f (x,0)).1)
  simpa only [zero_smul,add_zero] using h


-- @@ L276-279 verbatim
lemma tripleMap_hom : tripleMap (homUpper f) (homLower f) (hom_compatible f) = f := by
  apply LinearMap.ext
  intro x
  exact (hom_pair f x.1 x.2).symm


-- @@ L281-286 verbatim
@[ext] lemma triple_hom_ext {f g : Triple F L N α →ₗ[Alg F] Triple F L' N' β}
    (h₀ : homUpper f = homUpper g) (h₁ : homLower f = homLower g) : f = g := by
  apply LinearMap.ext
  intro x
  change f (x.1,x.2) = g (x.1,x.2)
  rw [hom_pair f x.1 x.2,hom_pair g x.1 x.2,h₀,h₁]


-- @@ L288-288 verbatim
end Tachikawa.Triangular




-- @@ L292-292 verbatim
namespace Tachikawa.Triangular

-- @@ L293-293 verbatim
open CategoryTheory

-- @@ L294-294 verbatim
open scoped ModuleCat.Algebra

-- @@ L295-295 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L296-296 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R))


-- @@ L298-298 verbatim
abbrev tensorObj (L : ModuleCat R) := ModuleCat.of R (Enveloping.evalType L F)

-- @@ L299-300 verbatim
abbrev tensorMap {L L' : ModuleCat R} (f : L ⟶ L') : tensorObj F L ⟶ tensorObj F L' :=
  ModuleCat.ofHom (BalancedTensor.mapRight (M := Enveloping.Obj F) f.hom)

-- @@ L301-301 verbatim
abbrev zeroObj : ModuleCat R := ModuleCat.of R PUnit


-- @@ L303-304 verbatim
def D₀Obj (L : ModuleCat R) : ModuleCat (Alg F) :=
  tripleObj F L (tensorObj F L) LinearMap.id

-- @@ L305-306 verbatim
def D₁Obj (L : ModuleCat R) : ModuleCat (Alg F) :=
  tripleObj F (zeroObj (R := R)) L 0


-- @@ L308-309 verbatim
def D₀Map {L L' : ModuleCat R} (f : L ⟶ L') : D₀Obj F L ⟶ D₀Obj F L' :=
  ModuleCat.ofHom (tripleMap f.hom (tensorMap F f).hom (by simp))

-- @@ L310-311 verbatim
def D₁Map {L L' : ModuleCat R} (f : L ⟶ L') : D₁Obj F L ⟶ D₁Obj F L' :=
  ModuleCat.ofHom (tripleMap 0 f.hom (by simp))


-- @@ L313-330 verbatim
def D₀ : ModuleCat R ⥤ ModuleCat (Alg F) where
  obj := D₀Obj F
  map := D₀Map F
  map_id L := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_id (k := k) (R := R) (S := R)
        (M := Enveloping.Obj F) (N := L)) x.2
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_comp f.hom g.hom) x.2


-- @@ L332-348 verbatim
def D₁ : ModuleCat R ⥤ ModuleCat (Alg F) where
  obj := D₁Obj F
  map := D₁Map F
  map_id L := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · rfl


-- @@ L350-357 verbatim
instance : (D₀ F).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_add f.hom g.hom) x.2

-- @@ L358-365 verbatim
instance : (D₁ F).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl


-- @@ L367-367 verbatim
variable {F} {L L' : ModuleCat R}


-- @@ L369-388 verbatim
def diagonal₀ : (D₀Obj F L ⟶ D₀Obj F L') ≃ₗ[k] (L ⟶ L') where
  toFun f := ModuleCat.ofHom (homUpper f.hom)
  invFun := D₀Map F
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · rfl
    · have hc := hom_compatible f.hom
      apply LinearMap.ext
      intro x
      have he := LinearMap.congr_fun hc x
      exact he.symm
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (x,0)).1 = c • (f.hom (x,0)).1
    exact congrArg Prod.fst (IsScalarTower.algebraMap_smul (Alg F) c (f.hom (x,0)))


-- @@ L390-408 verbatim
def diagonal₁ : (D₁Obj F L ⟶ D₁Obj F L') ≃ₗ[k] (L ⟶ L') where
  toFun f := ModuleCat.ofHom (homLower f.hom)
  invFun := D₁Map F
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (0,x)).2 = c • (f.hom (0,x)).2
    change ((TrivSqZeroExt.inl (algebraMap k R c,algebraMap k R c)) •
      f.hom (0,x)).2 = c • (f.hom (0,x)).2
    erw [diagonal_smul_triple]
    exact IsScalarTower.algebraMap_smul R c (f.hom (0,x)).2


-- @@ L410-418 verbatim
lemma cross₀₁_zero (f : D₀Obj F L ⟶ D₁Obj F L') : f = 0 := by
  apply ModuleCat.hom_ext
  apply triple_hom_ext
  · exact Subsingleton.elim _ _
  · have hc := hom_compatible f.hom
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun hc x
    exact he


-- @@ L420-439 verbatim
def cross₁₀ : (D₁Obj F L ⟶ D₀Obj F L') ≃ₗ[k] (L ⟶ tensorObj F L') where
  toFun f := ModuleCat.ofHom (homLower f.hom)
  invFun h := ModuleCat.ofHom (tripleMap 0 h.hom (by
    rw [LinearMap.comp_zero,BalancedTensor.mapRight_zero,LinearMap.comp_zero]))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · apply Subsingleton.elim
    · rfl
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (0,x)).2 = c • (f.hom (0,x)).2
    change ((TrivSqZeroExt.inl (algebraMap k R c,algebraMap k R c)) •
      f.hom (0,x)).2 = c • (f.hom (0,x)).2
    erw [diagonal_smul_triple]
    exact IsScalarTower.algebraMap_smul R c (f.hom (0,x)).2


-- @@ L441-441 verbatim
end Tachikawa.Triangular




-- @@ L445-445 verbatim
namespace Tachikawa.Triangular

-- @@ L446-446 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L447-447 verbatim
open scoped ModuleCat.Algebra

-- @@ L448-448 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L449-450 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R))
  [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)]


-- @@ L452-466 verbatim
lemma D₀Map_exact {L N P : ModuleCat R} (f : L ⟶ N) (g : N ⟶ P)
    (he : Function.Exact f g) : Function.Exact (D₀Map F f) (D₀Map F g) := by
  have ht := BalancedTensor.mapRight_exact (k := k) (R := R) (S := R) (M := Enveloping.Obj F) f.hom g.hom he
  intro x
  constructor
  · intro hx
    have h₀ : g x.1 = 0 := congrArg Prod.fst hx
    have h₁ : BalancedTensor.mapRight (M := Enveloping.Obj F) g.hom x.2 = 0 := congrArg Prod.snd hx
    obtain ⟨y,hy⟩ := (he x.1).mp h₀
    obtain ⟨z,hz⟩ := (ht x.2).mp h₁
    exact ⟨(y,z),Prod.ext hy hz⟩
  · rintro ⟨y,rfl⟩
    apply Prod.ext
    · exact (he _).mpr ⟨y.1,rfl⟩
    · exact (ht _).mpr ⟨y.2,rfl⟩


-- @@ L468-480 verbatim
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁Map_exact {L N P : ModuleCat R} (f : L ⟶ N) (g : N ⟶ P)
    (he : Function.Exact f g) : Function.Exact (D₁Map F f) (D₁Map F g) := by
  intro x
  constructor
  · intro hx
    have h₁ : g x.2 = 0 := congrArg Prod.snd hx
    obtain ⟨z,hz⟩ := (he x.2).mp h₁
    exact ⟨(0,z),Prod.ext (Subsingleton.elim _ _) hz⟩
  · rintro ⟨y,rfl⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact (he _).mpr ⟨y.2,rfl⟩


-- @@ L482-485 verbatim
lemma D₀_exact (S : ShortComplex (ModuleCat R)) (hS : S.Exact) :
    (S.map (D₀ F)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact D₀Map_exact F S.f S.g hS


-- @@ L487-491 verbatim
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
lemma D₁_exact (S : ShortComplex (ModuleCat R)) (hS : S.Exact) :
    (S.map (D₁ F)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact D₁Map_exact F S.f S.g hS


-- @@ L493-495 verbatim
instance : PreservesFiniteLimits (D₀ F) := by
  have h := ((Functor.exact_tfae (D₀ F)).out 2 4).mp (D₀_exact F)
  exact h.1

-- @@ L496-498 verbatim
instance : PreservesFiniteColimits (D₀ F) := by
  have h := ((Functor.exact_tfae (D₀ F)).out 2 4).mp (D₀_exact F)
  exact h.2


-- @@ L500-503 verbatim
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
instance : PreservesFiniteLimits (D₁ F) := by
  have h := ((Functor.exact_tfae (D₁ F)).out 2 4).mp (D₁_exact F)
  exact h.1

-- @@ L504-507 verbatim
omit [Module.Finite Rᵐᵒᵖ (Enveloping.Obj F)] [Module.Projective Rᵐᵒᵖ (Enveloping.Obj F)] in
instance : PreservesFiniteColimits (D₁ F) := by
  have h := ((Functor.exact_tfae (D₁ F)).out 2 4).mp (D₁_exact F)
  exact h.2


-- @@ L509-509 verbatim
end Tachikawa.Triangular




-- @@ L513-513 verbatim
namespace Tachikawa.Triangular

-- @@ L514-514 verbatim
open CategoryTheory

-- @@ L515-515 verbatim
open scoped ModuleCat.Algebra

-- @@ L516-516 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L517-517 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R)) (ι : Type) [Fintype ι]


-- @@ L519-519 verbatim
def freeObj := ModuleCat.of R (ι → R)

-- @@ L520-520 verbatim
def freeUnderlying : freeObj (R := R) ι ≃ₗ[R] (ι → R) := LinearEquiv.refl R _


-- @@ L522-524 verbatim
def freeTensorEval : Enveloping.evalType (freeObj (R := R) ι) F →ₗ[R] (ι → Enveloping.Obj F) :=
  (BalancedTensor.rightFreeEval (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι).comp
    (BalancedTensor.mapRight (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).toLinearMap)


-- @@ L526-528 verbatim
def freeTensorInv : (ι → Enveloping.Obj F) →ₗ[R] Enveloping.evalType (freeObj (R := R) ι) F :=
  (BalancedTensor.mapRight (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).symm.toLinearMap).comp
    (BalancedTensor.rightFreeInv (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι)


-- @@ L530-532 verbatim
omit [Fintype ι] in
lemma freeTensorEval_mk (m : Enveloping.Obj F) (x : freeObj (R := R) ι) (i : ι) :
    freeTensorEval F ι (BalancedTensor.mk m x) i = MulOpposite.op (x i) • m := rfl


-- @@ L534-542 verbatim
lemma freeTensorEval_inv (x : ι → Enveloping.Obj F) : freeTensorEval F ι (freeTensorInv F ι x) = x := by
  dsimp only [freeTensorEval,freeTensorInv,LinearMap.comp_apply]
  have h := LinearMap.congr_fun (BalancedTensor.mapRight_split (k := k) (S := R)
    (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).symm.toLinearMap
      (freeUnderlying (R := R) ι).toLinearMap (by rfl))
      (BalancedTensor.rightFreeInv (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι x)
  dsimp only [LinearMap.comp_apply,LinearMap.id_apply] at h
  rw [h]
  exact BalancedTensor.rightFreeEval_inv ι x


-- @@ L544-548 verbatim
lemma freeTensorInv_eval (x : Enveloping.evalType (freeObj (R := R) ι) F) :
    freeTensorInv F ι (freeTensorEval F ι x) = x := by
  dsimp only [freeTensorEval,freeTensorInv,LinearMap.comp_apply]
  rw [BalancedTensor.rightFreeInv_eval]
  exact LinearMap.congr_fun (BalancedTensor.mapRight_split _ _ (by rfl)) x


-- @@ L550-554 verbatim
def freeTensorEquiv : Enveloping.evalType (freeObj (R := R) ι) F ≃ₗ[R] (ι → Enveloping.Obj F) :=
  { freeTensorEval F ι with
    invFun := freeTensorInv F ι
    left_inv := freeTensorInv_eval F ι
    right_inv := freeTensorEval_inv F ι }





-- @@ L559-582 verbatim
def D₀FreeInclusion : D₀Obj F (freeObj (R := R) ι) →ₗ[Alg F] (ι → Alg F) where
  toFun x i := ⟨(x.1 i,0), show Off F from freeTensorEval F ι x.2 i⟩
  map_add' x y := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_add (0 : R)).symm
    · exact congrFun ((freeTensorEval F ι).map_add x.2 y.2) i
  map_smul' a x := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · change (0:R) = lower F a * 0
        simp
    · change freeTensorEval F ι
        (BalancedTensor.mk (k := k) (R := R) (S := R) (M := Enveloping.Obj F)
          (N := freeObj (R := R) ι) (off F a) x.1 + lower F a •
          (show Enveloping.evalType (freeObj (R := R) ι) F from x.2)) i =
        lower F a • freeTensorEval F ι x.2 i +
          MulOpposite.op (x.1 i) • off F a
      rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, freeTensorEval_mk]
      exact add_comm _ _


-- @@ L584-604 verbatim
def D₀FreeProjection : (ι → Alg F) →ₗ[Alg F] D₀Obj F (freeObj (R := R) ι) where
  toFun a := (fun i => upper F (a i), freeTensorInv F ι (fun i => off F (a i)))
  map_add' a b := by
    apply Prod.ext
    · funext i
      exact map_add (upper F) (a i) (b i)
    · exact (freeTensorInv F ι).map_add _ _
  map_smul' a z := by
    apply Prod.ext
    · funext i
      exact map_mul (upper F) a (z i)
    · apply (freeTensorEquiv F ι).injective
      change freeTensorEval F ι
        (freeTensorInv F ι (fun i => off F (a * z i))) =
        freeTensorEval F ι
          (BalancedTensor.mk (k := k) (R := R) (S := R) (M := Enveloping.Obj F)
            (N := freeObj (R := R) ι) (off F a) (fun i => upper F (z i)) +
            lower F a • freeTensorInv F ι (fun i => off F (z i)))
      rw [freeTensorEval_inv,map_add,map_smul,freeTensorEval_inv]
      funext i
      exact (off_mul F a (z i)).trans (add_comm _ _)


-- @@ L606-611 verbatim
lemma D₀Free_retract : (D₀FreeProjection F ι).comp (D₀FreeInclusion F ι) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact freeTensorInv_eval F ι x.2


-- @@ L613-632 verbatim
def D₁FreeInclusion : D₁Obj F (freeObj (R := R) ι) →ₗ[Alg F] (ι → Alg F) where
  toFun x i := TrivSqZeroExt.inl (0,x.2 i)
  map_add' x y := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · simp
      · rfl
    · exact (zero_add (0 : Enveloping.Obj F)).symm
  map_smul' a x := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · change (0:R) = upper F a * 0
        simp
      · change ((0 : freeObj (R := R) ι) + lower F a • x.2) i = lower F a * x.2 i
        rw [zero_add]
        rfl
    · change (0 : Enveloping.Obj F) = lower F a • 0 + (0 : Rᵐᵒᵖ) • off F a
      rw [smul_zero, zero_smul, add_zero]


-- @@ L634-648 verbatim
def D₁FreeProjection : (ι → Alg F) →ₗ[Alg F] D₁Obj F (freeObj (R := R) ι) where
  toFun a := (0,fun i => lower F (a i))
  map_add' a b := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      exact map_add (lower F) (a i) (b i)
  map_smul' a z := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      change lower F (a*z i) = ((0 : freeObj (R := R) ι) + lower F a •
        (show freeObj (R := R) ι from fun i => lower F (z i))) i
      rw [zero_add]
      exact map_mul (lower F) a (z i)


-- @@ L650-656 verbatim
omit [Fintype ι] in
lemma D₁Free_retract : (D₁FreeProjection F ι).comp (D₁FreeInclusion F ι) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl


-- @@ L658-659 verbatim
lemma D₀Free_projective : Module.Projective (Alg F) (D₀Obj F (freeObj (R := R) ι)) :=
  Module.Projective.of_split (D₀FreeInclusion F ι) (D₀FreeProjection F ι) (D₀Free_retract F ι)

-- @@ L660-661 verbatim
lemma D₁Free_projective : Module.Projective (Alg F) (D₁Obj F (freeObj (R := R) ι)) :=
  Module.Projective.of_split (D₁FreeInclusion F ι) (D₁FreeProjection F ι) (D₁Free_retract F ι)


-- @@ L663-663 verbatim
end Tachikawa.Triangular




-- @@ L667-667 verbatim
namespace Tachikawa.Triangular

-- @@ L668-668 verbatim
open CategoryTheory

-- @@ L669-669 verbatim
open scoped ModuleCat.Algebra

-- @@ L670-670 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L671-671 verbatim
variable (F : ModuleCat (Enveloping.Alg k R R)) (L : ModuleCat R)


-- @@ L673-685 verbatim
lemma D₀_projective [Module.Finite R L] [Module.Projective R L] :
    Module.Projective (Alg F) (D₀Obj F L) := by
  let c := finiteFreeCover (R := R) (M := L)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective (Alg F) (D₀Obj F (freeObj (R := R) (Fin c.rank))) :=
    D₀Free_projective F (Fin c.rank)
  let inclusion : L ⟶ freeObj (R := R) (Fin c.rank) := ModuleCat.ofHom i
  let projection : freeObj (R := R) (Fin c.rank) ⟶ L := ModuleCat.ofHom c.map
  refine Module.Projective.of_split (D₀Map F inclusion).hom (D₀Map F projection).hom ?_
  have h : inclusion ≫ projection = 𝟙 L := ModuleCat.hom_ext hi
  have he := (D₀ F).map_comp inclusion projection
  rw [h,(D₀ F).map_id] at he
  exact (congrArg ModuleCat.Hom.hom he).symm


-- @@ L687-699 verbatim
lemma D₁_projective [Module.Finite R L] [Module.Projective R L] :
    Module.Projective (Alg F) (D₁Obj F L) := by
  let c := finiteFreeCover (R := R) (M := L)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective (Alg F) (D₁Obj F (freeObj (R := R) (Fin c.rank))) :=
    D₁Free_projective F (Fin c.rank)
  let inclusion : L ⟶ freeObj (R := R) (Fin c.rank) := ModuleCat.ofHom i
  let projection : freeObj (R := R) (Fin c.rank) ⟶ L := ModuleCat.ofHom c.map
  refine Module.Projective.of_split (D₁Map F inclusion).hom (D₁Map F projection).hom ?_
  have h : inclusion ≫ projection = 𝟙 L := ModuleCat.hom_ext hi
  have he := (D₁ F).map_comp inclusion projection
  rw [h,(D₁ F).map_id] at he
  exact (congrArg ModuleCat.Hom.hom he).symm


-- @@ L701-707 verbatim
instance [FiniteDimensional k F] [FiniteDimensional k L] :
    FiniteDimensional k (D₀Obj F L) := by
  let : FiniteDimensional k (Enveloping.Obj F) := inferInstanceAs (FiniteDimensional k F)
  let : FiniteDimensional k (tensorObj F L) := moduleCatFinite _
  let : FiniteDimensional k (Triple F L (tensorObj F L) LinearMap.id) :=
    inferInstanceAs (FiniteDimensional k (L × (tensorObj F L)))
  exact moduleCatFinite (Triple F L (tensorObj F L) LinearMap.id)


-- @@ L709-710 verbatim
instance [FiniteDimensional k L] : FiniteDimensional k (D₁Obj F L) := by
  exact moduleCatFinite _


-- @@ L712-712 verbatim
end Tachikawa.Triangular




-- @@ L716-716 verbatim
namespace Tachikawa.Triangular

-- @@ L717-717 verbatim
open CategoryTheory

-- @@ L718-718 verbatim
open scoped ModuleCat.Algebra

-- @@ L719-719 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L720-720 verbatim
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))

-- @@ L721-722 verbatim
abbrev D₀Complex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((D₀ F).mapHomologicalComplex (.down ℤ)).obj P

-- @@ L723-724 verbatim
abbrev D₁Complex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((D₁ F).mapHomologicalComplex (.down ℤ)).obj P


-- @@ L726-734 verbatim
lemma diagonal₀_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₀Obj F M ⟶ D₀Obj F N) :
    diagonal₀ (D₀Map F d ≫ f) = d ≫ diagonal₀ f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.hom (d x, BalancedTensor.mapRight d.hom 0)).1 = _
  rw [map_zero]
  rfl

-- @@ L735-737 verbatim
lemma diagonal₁_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₁Obj F M ⟶ D₁Obj F N) :
    diagonal₁ (D₁Map F d ≫ f) = d ≫ diagonal₁ f := rfl

-- @@ L738-740 verbatim
lemma cross₁₀_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₁Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (D₁Map F d ≫ f) = d ≫ cross₁₀ f := rfl

-- @@ L741-743 verbatim
lemma cross₁₀_post {L M N : ModuleCat.{0} R} (d : M ⟶ N)
    (f : D₁Obj F L ⟶ D₀Obj F M) :
    cross₁₀ (f ≫ D₀Map F d) = cross₁₀ f ≫ (Enveloping.tensorFunctor F).map d := rfl


-- @@ L745-746 verbatim
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  (N : ModuleCat.{0} R)

-- @@ L747-747 verbatim
include hP

-- @@ L748-758 verbatim
lemma D₀_boundaries [Module.Finite R N] [Module.Projective R N]
    (j : ℤ) (f : D₀Obj F (P.X j) ⟶ D₀Obj F N)
    (hf : D₀Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₀Obj F (P.X (j-1)) ⟶ D₀Obj F N, D₀Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (diagonal₀ (F := F)) hf
  rw [diagonal₀_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (diagonal₀ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨diagonal₀.symm (ModuleCat.ofHom g),?_⟩
  apply diagonal₀.injective
  rw [diagonal₀_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg

-- @@ L759-769 verbatim
lemma D₁_boundaries [Module.Finite R N] [Module.Projective R N]
    (j : ℤ) (f : D₁Obj F (P.X j) ⟶ D₁Obj F N)
    (hf : D₁Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₁Obj F (P.X (j-1)) ⟶ D₁Obj F N, D₁Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (diagonal₁ (F := F)) hf
  rw [diagonal₁_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (diagonal₁ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨diagonal₁.symm (ModuleCat.ofHom g),?_⟩
  apply diagonal₁.injective
  rw [diagonal₁_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg

-- @@ L770-780 verbatim
lemma cross_boundaries [Module.Finite R (tensorObj F N)] [Module.Projective R (tensorObj F N)]
    (j : ℤ) (f : D₁Obj F (P.X j) ⟶ D₀Obj F N)
    (hf : D₁Map F (P.d (j+1) j) ≫ f = 0) :
    ∃ g : D₁Obj F (P.X (j-1)) ⟶ D₀Obj F N, D₁Map F (P.d j (j-1)) ≫ g = f := by
  have h := congrArg (cross₁₀ (F := F)) hf
  rw [cross₁₀_pre,map_zero] at h
  obtain ⟨g,hg⟩ := hP.projective_boundaries j (cross₁₀ f).hom (ModuleCat.hom_ext_iff.mp h)
  refine ⟨cross₁₀.symm (ModuleCat.ofHom g),?_⟩
  apply cross₁₀.injective
  rw [cross₁₀_pre,LinearEquiv.apply_symm_apply]
  exact ModuleCat.hom_ext hg


-- @@ L782-782 verbatim
variable {P}

-- @@ L783-792 verbatim
def crossMap {Q : ChainComplex (ModuleCat.{0} R) ℤ}
    (u : P ⟶ Enveloping.tensorComplex F Q) : D₁Complex F P ⟶ D₀Complex F Q where
  f j := cross₁₀.symm (u.f j)
  comm' i j hij := by
    apply cross₁₀.injective
    change cross₁₀ (cross₁₀.symm (u.f i) ≫ D₀Map F (Q.d i j)) =
      cross₁₀ (D₁Map F (P.d i j) ≫ cross₁₀.symm (u.f j))
    rw [cross₁₀_pre,cross₁₀_post]
    erw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact u.comm i j


-- @@ L794-794 verbatim
end Tachikawa.Triangular


-- @@ L796-796 verbatim
end


-- @@ L798-798 verbatim
end OAI
