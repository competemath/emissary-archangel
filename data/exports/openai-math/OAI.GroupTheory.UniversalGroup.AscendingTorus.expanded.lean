import OAI.GroupTheory.UniversalGroup.GraphActions


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Metric Topology BigOperators

-- @@ L6-6 verbatim
open Set Metric Topology

-- @@ L7-7 verbatim
open Set Topology

-- @@ L8-8 verbatim
open Set Metric Topology

-- @@ L9-9 verbatim
open scoped NNReal

-- @@ L10-10 verbatim
open Set Metric Topology

-- @@ L11-11 verbatim
open scoped NNReal ENNReal

-- @@ L12-12 verbatim
open Set Metric Topology

-- @@ L13-13 verbatim
open scoped TensorProduct


-- @@ L15-15 verbatim
namespace UniversalFInfinity.AscendingTorus


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
open Monoid Coprod Multiplicative

-- @@ L20-20 verbatim
universe u v w

-- @@ L21-21 verbatim
variable {U : Type u} [Group U]


-- @@ L23-23 verbatim
abbrev Free (U : Type u) [Group U] := U ∗ Multiplicative ℤ


-- @@ L25-25 verbatim
def letter : Free U := inr (ofAdd 1)


-- @@ L27-28 verbatim
def relation (f : Monoid.End U) (x : U) : Free U :=
  (inl x * letter) * (letter * inl (f x))⁻¹


-- @@ L30-31 verbatim
def relations (f : Monoid.End U) : Subgroup (Free U) :=
  Subgroup.normalClosure (Set.range (relation f))


-- @@ L33-34 verbatim
instance (f : Monoid.End U) : (relations f).Normal := inferInstanceAs
  (Subgroup.normalClosure (Set.range (relation f))).Normal


-- @@ L36-36 verbatim
def Torus (f : Monoid.End U) := Free U ⧸ relations f


-- @@ L38-40 verbatim
instance (f : Monoid.End U) : Group (Torus f) := by
  delta Torus
  infer_instance


-- @@ L42-42 verbatim
instance groupOfHom (f : U →* U) : Group (Torus f) := instGroupTorus f


-- @@ L44-45 verbatim
def of (f : Monoid.End U) : U →* Torus f :=
  (QuotientGroup.mk' (relations f)).comp inl


-- @@ L47-48 verbatim
def stable (f : Monoid.End U) : Torus f :=
  QuotientGroup.mk' (relations f) letter


-- @@ L50-54 verbatim
lemma of_mul_stable (f : Monoid.End U) (x : U) :
    of f x * stable f = stable f * of f (f x) := by
  apply mul_inv_eq_one.mp
  change QuotientGroup.mk' (relations f) (relation f x) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x,rfl⟩)


-- @@ L56-58 verbatim
lemma stable_conjugate (f : Monoid.End U) (x : U) :
    stable f * of f (f x) * (stable f)⁻¹ = of f x := by
  rw [← of_mul_stable, mul_inv_cancel_right]


-- @@ L60-62 verbatim
lemma inverse_conjugate (f : Monoid.End U) (x : U) :
    (stable f)⁻¹ * of f x * stable f = of f (f x) := by
  rw [mul_assoc, of_mul_stable, inv_mul_cancel_left]


-- @@ L64-64 verbatim
variable {V : Type v} [Group V]


-- @@ L66-74 verbatim
def lift (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) : Torus f →* V :=
  QuotientGroup.lift (relations f) (Coprod.lift φ (zpowersHom V t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x,rfl⟩
    change Coprod.lift φ (zpowersHom V t) (relation f x) = 1
    simp only [relation, letter, map_mul, map_inv, Coprod.lift_apply_inl, Coprod.lift_apply_inr,
      zpowersHom_apply, toAdd_ofAdd, zpow_one]
    rw [h x, mul_inv_cancel])


-- @@ L76-80 verbatim
@[simp] lemma lift_of (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) (x : U) :
    lift f φ t h (of f x) = φ x := by
  change Coprod.lift φ (zpowersHom V t) (inl x) = _
  simp


-- @@ L82-86 verbatim
@[simp] lemma lift_stable (f : Monoid.End U) (φ : U →* V) (t : V)
    (h : ∀ x, φ x * t = t * φ (f x)) :
    lift f φ t h (stable f) = t := by
  change Coprod.lift φ (zpowersHom V t) (inr (ofAdd 1)) = _
  simp


-- @@ L88-93 verbatim
@[ext] lemma hom_ext {f : Monoid.End U} {φ ψ : Torus f →* V}
    (ho : φ.comp (of f) = ψ.comp (of f)) (ht : φ (stable f) = ψ (stable f)) :
    φ = ψ := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f))).mp
  apply Coprod.hom_ext ho
  exact MonoidHom.ext_mint ht


-- @@ L95-108 verbatim
theorem of_injective (f : Monoid.End U) (hf : Function.Injective f) :
    Function.Injective (of f) := by
  let e : (⊤ : Subgroup U) ≃* f.range :=
    (Subgroup.topEquiv).trans (MonoidHom.ofInjective hf)
  let H := HNNExtension U ⊤ f.range e
  let j : U →* H := HNNExtension.of
  let s : H := HNNExtension.t
  have hs (x : U) : j x * s⁻¹ = s⁻¹ * j (f x) := by
    exact HNNExtension.of_mul_inv_t (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup U))
  let Φ : Torus f →* H := lift f j s⁻¹ hs
  intro x y hxy
  apply HNNExtension.of_injective (A := ⊤) (B := f.range) (φ := e)
  exact (lift_of f j s⁻¹ hs x).symm.trans
    ((congrArg Φ hxy).trans (lift_of f j s⁻¹ hs y))


-- @@ L110-110 verbatim
section Factorization

-- @@ L111-111 verbatim
variable {P : Type v} [Group P] (a : U →* P) (b : P →* U)


-- @@ L113-115 verbatim
def forward : Torus (b.comp a) →* Torus (a.comp b) :=
  lift (b.comp a) ((of (a.comp b)).comp a) (stable (a.comp b))
    (fun x => of_mul_stable (a.comp b) (a x))


-- @@ L117-126 verbatim
def backward : Torus (a.comp b) →* Torus (b.comp a) :=
  lift (a.comp b)
    ((MulAut.conj (stable (b.comp a))).toMonoidHom.comp ((of (b.comp a)).comp b))
    (stable (b.comp a)) (by
      intro p
      change (stable (b.comp a) * of (b.comp a) (b p) * (stable (b.comp a))⁻¹) *
        stable (b.comp a) = stable (b.comp a) *
          (stable (b.comp a) * of (b.comp a) ((b.comp a) (b p)) * (stable (b.comp a))⁻¹)
      exact (inv_mul_cancel_right _ _).trans
        (congrArg (stable (b.comp a) * ·) (stable_conjugate (b.comp a) (b p)).symm))


-- @@ L128-130 verbatim
@[simp] lemma forward_of (x : U) :
    forward a b (of (b.comp a) x) = of (a.comp b) (a x) :=
  lift_of _ _ _ _ x


-- @@ L132-133 verbatim
@[simp] lemma forward_stable :
    forward a b (stable (b.comp a)) = stable (a.comp b) := lift_stable _ _ _ _


-- @@ L135-138 verbatim
@[simp] lemma backward_of (p : P) :
    backward a b (of (a.comp b) p) =
      stable (b.comp a) * of (b.comp a) (b p) * (stable (b.comp a))⁻¹ :=
  lift_of _ _ _ _ p


-- @@ L140-141 verbatim
@[simp] lemma backward_stable :
    backward a b (stable (a.comp b)) = stable (b.comp a) := lift_stable _ _ _ _


-- @@ L143-148 verbatim
lemma backward_forward : (backward a b).comp (forward a b) = MonoidHom.id _ := by
  apply hom_ext
  · ext x
    simp only [MonoidHom.comp_apply, forward_of, backward_of, MonoidHom.id_apply]
    exact stable_conjugate (b.comp a) x
  · simp


-- @@ L150-156 verbatim
lemma forward_backward : (forward a b).comp (backward a b) = MonoidHom.id _ := by
  apply hom_ext
  · ext p
    simp only [MonoidHom.comp_apply, backward_of, map_mul, map_inv, forward_stable,
      forward_of, MonoidHom.id_apply]
    exact stable_conjugate (a.comp b) p
  · simp


-- @@ L158-162 verbatim
def cyclicFactorization : Torus (b.comp a) ≃* Torus (a.comp b) :=
  { forward a b with
    invFun := backward a b
    left_inv := fun x => DFunLike.congr_fun (backward_forward a b) x
    right_inv := fun x => DFunLike.congr_fun (forward_backward a b) x }


-- @@ L164-164 verbatim
end Factorization


-- @@ L166-210 verbatim
lemma relations_finitelyNormallyGenerated [Group.FG U] (f : Monoid.End U) :
    (relations f).IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup U).FG)
  let N : Subgroup (Free U) := Subgroup.normalClosure (relation f '' (S : Set U))
  let Q := Free U ⧸ N
  let q : Free U →* Q := QuotientGroup.mk' N
  let t : Q := q letter
  let i : U →* Q := q.comp inl
  let j : U →* Q := (MulAut.conj t).toMonoidHom.comp (i.comp f)
  let E : Subgroup U :=
    { carrier := {x | i x = j x}
      one_mem' := by simp only [Set.mem_ofPred_eq,map_one]
      mul_mem' := by
        intro x y hx hy
        change i (x*y) = j (x*y)
        rw [map_mul,map_mul,hx,hy]
      inv_mem' := by
        intro x hx
        change i x⁻¹ = j x⁻¹
        rw [map_inv,map_inv,hx] }
  have hSsub : (S : Set U) ⊆ E := by
    intro x hx
    have hw : q (relation f x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x,hx,rfl⟩)
    have he : i x * t = t * i (f x) := by
      apply mul_inv_eq_one.mp
      exact hw
    change i x = t * i (f x) * t⁻¹
    rw [← he,mul_inv_cancel_right]
  have htop : (⊤ : Subgroup U) ≤ E := by
    rw [← hS]
    exact (Subgroup.closure_le _).mpr hSsub
  have he (x : U) : i x = t * i (f x) * t⁻¹ := htop (Subgroup.mem_top x)
  refine ⟨relation f '' (S : Set U), S.finite_toSet.image _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨x,_,rfl⟩
    exact ⟨x,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change (i x * t) * (t * i (f x))⁻¹ = 1
    rw [mul_inv_eq_one]
    rw [he x,inv_mul_cancel_right]


-- @@ L212-216 verbatim
instance finitelyPresented [Group.IsFinitelyPresented U] (f : Monoid.End U) :
    Group.IsFinitelyPresented (Torus f) := by
  obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented U).out
  let : Group.FG U := Group.fg_of_surjective hφ
  exact Group.IsFinitelyPresented.quotient (relations f) (relations_finitelyNormallyGenerated f)


-- @@ L218-222 verbatim
theorem finitelyPresented_of_factorization {P : Type v} [Group P]
    [Group.IsFinitelyPresented P] (a : U →* P) (b : P →* U) :
    Group.IsFinitelyPresented (Torus (b.comp a)) := by
  let : Group.IsFinitelyPresented (Torus (a.comp b)) := finitelyPresented (a.comp b)
  exact Group.IsFinitelyPresented.equiv (cyclicFactorization a b).symm


-- @@ L224-224 verbatim
end


-- @@ L226-226 verbatim
section

-- @@ L227-227 verbatim
open Monoid Coprod Multiplicative

-- @@ L228-228 verbatim
universe u

-- @@ L229-229 verbatim
variable {U : Type u} [Group U]


-- @@ L231-238 verbatim
lemma of_mul_stable_pow (f : Monoid.End U) (u : U) (n : ℕ) :
    of f u * stable f ^ n = stable f ^ n * of f ((f ^ n) u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, of_mul_stable, ← mul_assoc, ← pow_succ]
    rw [pow_succ' f n]
    rfl


-- @@ L240-244 verbatim
lemma inv_stable_pow_mul_of (f : Monoid.End U) (u : U) (n : ℕ) :
    (stable f ^ n)⁻¹ * of f u = of f ((f ^ n) u) * (stable f ^ n)⁻¹ := by
  apply mul_right_cancel (b := stable f ^ n)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [of_mul_stable_pow, inv_mul_cancel_left]


-- @@ L246-269 verbatim
def normalForms (f : Monoid.End U) : Subgroup (Torus f) where
  carrier := {x | ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹}
  one_mem' := ⟨0,0,1,by simp⟩
  inv_mem' := by
    rintro x ⟨p,q,u,rfl⟩
    exact ⟨q,p,u⁻¹,by simp only [mul_inv_rev, inv_inv, map_inv, mul_assoc]⟩
  mul_mem' := by
    rintro x y ⟨p,q,u,rfl⟩ ⟨r,s,v,rfl⟩
    refine ⟨p+r,q+s,(f^r) u * (f^q) v,?_⟩
    have ht : (stable f ^ q)⁻¹ * stable f ^ r =
        stable f ^ r * (stable f ^ q)⁻¹ := (Commute.pow_pow (Commute.refl (stable f)) q r).inv_left.eq
    calc
      _ = stable f ^ p * (of f u * stable f ^ r) *
          ((stable f ^ q)⁻¹ * of f v) * (stable f ^ s)⁻¹ := by
            simp only [mul_assoc]
            rw [← mul_assoc ((stable f ^ q)⁻¹),ht]
            simp only [mul_assoc]
      _ = _ := by
        rw [of_mul_stable_pow,inv_stable_pow_mul_of,map_mul,pow_add,pow_add,mul_inv_rev]
        have ht' : (stable f ^ s)⁻¹ * (stable f ^ q)⁻¹ =
            (stable f ^ q)⁻¹ * (stable f ^ s)⁻¹ :=
          (Commute.pow_pow (Commute.refl (stable f)) s q).inv_left.inv_right.eq
        rw [ht']
        simp only [mul_assoc]


-- @@ L271-272 verbatim
lemma of_mem_normalForms (f : Monoid.End U) (u : U) : of f u ∈ normalForms f :=
  ⟨0,0,u,by simp⟩


-- @@ L274-275 verbatim
lemma stable_mem_normalForms (f : Monoid.End U) : stable f ∈ normalForms f :=
  ⟨1,0,1,by simp⟩


-- @@ L277-293 verbatim
theorem normal_form (f : Monoid.End U) (x : Torus f) :
    ∃ (p q : ℕ) (u : U), x = stable f ^ p * of f u * (stable f ^ q)⁻¹ := by
  change x ∈ normalForms f
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (relations f) x
  induction w using Coprod.induction_on with
  | inl u => exact of_mem_normalForms f u
  | inr z =>
    have hz : inr z = (letter (U := U)) ^ toAdd z := by
      rw [letter,← map_zpow]
      congr 1
      change z = ofAdd ((toAdd z) • (1 : ℤ))
      simp
    rw [hz,map_zpow]
    exact (normalForms f).zpow_mem (stable_mem_normalForms f) _
  | mul x y hx hy =>
    rw [map_mul]
    exact (normalForms f).mul_mem hx hy


-- @@ L295-296 verbatim
def height (f : Monoid.End U) : Torus f →* Multiplicative ℤ :=
  lift f 1 (ofAdd 1) (by intro u; simp)


-- @@ L298-299 verbatim
@[simp] lemma height_of (f : Monoid.End U) (u : U) : height f (of f u) = 1 :=
  lift_of f 1 (ofAdd 1) _ u


-- @@ L301-302 verbatim
@[simp] lemma height_stable (f : Monoid.End U) : height f (stable f) = ofAdd 1 :=
  lift_stable f 1 (ofAdd 1) _


-- @@ L304-304 verbatim
end


-- @@ L306-306 verbatim
section

-- @@ L307-307 verbatim
open Monoid Multiplicative

-- @@ L308-308 verbatim
universe u

-- @@ L309-309 verbatim
variable {U : Type u} [Group U]


-- @@ L311-311 verbatim
abbrev Coset (f : Monoid.End U) := Torus f ⧸ (of f).range


-- @@ L313-313 verbatim
def coset (f : Monoid.End U) (x : Torus f) : Coset f := QuotientGroup.mk x


-- @@ L315-317 verbatim
lemma coset_mul_of (f : Monoid.End U) (x : Torus f) (u : U) :
    coset f (x * of f u) = coset f x :=
  QuotientGroup.mk_mul_of_mem x ⟨u,rfl⟩


-- @@ L319-326 verbatim
def next (f : Monoid.End U) : Coset f → Coset f :=
  Quotient.map' (fun x => x * stable f) (by
    intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    obtain ⟨u,hu⟩ := h
    refine ⟨f u,?_⟩
    rw [mul_inv_rev,mul_assoc,← mul_assoc x⁻¹,← hu]
    exact (inverse_conjugate f u).symm)


-- @@ L328-329 verbatim
@[simp] lemma next_coset (f : Monoid.End U) (x : Torus f) :
    next f (coset f x) = coset f (x * stable f) := rfl


-- @@ L331-336 verbatim
lemma next_iterate_coset (f : Monoid.End U) (k : ℕ) (x : Torus f) :
    (next f)^[k] (coset f x) = coset f (x * stable f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,next_coset,pow_succ,mul_assoc]


-- @@ L338-345 verbatim
lemma reaches_base_ray (f : Monoid.End U) (c : Coset f) :
    ∃ (p q : ℕ), (next f)^[q] c = (next f)^[p] (coset f 1) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨p,q,u,hx⟩ := normal_form f x
  refine ⟨p,q,?_⟩
  change (next f)^[q] (coset f x) = _
  rw [next_iterate_coset,next_iterate_coset,hx,mul_assoc,
    inv_mul_cancel,mul_one,one_mul,coset_mul_of]


-- @@ L347-353 verbatim
lemma common_descendant (f : Monoid.End U) (c d : Coset f) :
    ∃ (p q : ℕ), (next f)^[p] c = (next f)^[q] d := by
  obtain ⟨p,q,hc⟩ := reaches_base_ray f c
  obtain ⟨r,s,hd⟩ := reaches_base_ray f d
  refine ⟨r+q,p+s,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hc,hd,
    ← Function.iterate_add_apply,← Function.iterate_add_apply,Nat.add_comm r p]


-- @@ L355-361 verbatim
def cosetHeight (f : Monoid.End U) : Coset f → ℤ :=
  Quotient.lift (fun x => toAdd (height f x)) (by
    intro x y h
    have h' : x⁻¹ * y ∈ (of f).range := QuotientGroup.leftRel_apply.mp h
    obtain ⟨u,hu⟩ := h'
    have hy : y = x * of f u := by rw [hu,mul_inv_cancel_left]
    rw [hy,map_mul,height_of,mul_one])


-- @@ L363-364 verbatim
@[simp] lemma cosetHeight_coset (f : Monoid.End U) (x : Torus f) :
    cosetHeight f (coset f x) = toAdd (height f x) := rfl


-- @@ L366-372 verbatim
lemma height_next (f : Monoid.End U) (c : Coset f) :
    cosetHeight f (next f c) = cosetHeight f c + 1 := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    change cosetHeight f (next f (coset f x)) = cosetHeight f (coset f x) + 1
    rw [next_coset,cosetHeight_coset,cosetHeight_coset,map_mul,height_stable]
    rfl


-- @@ L374-374 verbatim
noncomputable def origin (f : Monoid.End U) (c : Coset f) : Torus f := c.out


-- @@ L376-377 verbatim
@[simp] lemma coset_origin (f : Monoid.End U) (c : Coset f) :
    coset f (origin f c) = c := Quotient.out_eq' c


-- @@ L379-383 verbatim
lemma origin_next_mem (f : Monoid.End U) (c : Coset f) :
    (origin f (next f c))⁻¹ * (origin f c * stable f) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (next f c)) = coset f (origin f c * stable f)
  rw [coset_origin,← next_coset,coset_origin]


-- @@ L385-386 verbatim
noncomputable def cosetOffset (f : Monoid.End U) (c : Coset f) : U :=
  Classical.choose (origin_next_mem f c)


-- @@ L388-391 verbatim
lemma origin_next (f : Monoid.End U) (c : Coset f) :
    origin f (next f c) * of f (cosetOffset f c) = origin f c * stable f := by
  change origin f (next f c) * of f (Classical.choose (origin_next_mem f c)) = _
  rw [Classical.choose_spec (origin_next_mem f c),mul_inv_cancel_left]


-- @@ L393-393 verbatim
end


-- @@ L395-395 verbatim
open Monoid Multiplicative

-- @@ L396-396 verbatim
noncomputable section

-- @@ L397-397 verbatim
universe u

-- @@ L398-398 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)


-- @@ L400-400 verbatim
lemma smul_coset (g x : Torus f) : g • coset f x = coset f (g*x) := rfl

-- @@ L401-403 verbatim
lemma next_smul (g : Torus f) (c : Coset f) : next f (g • c) = g • next f c := by
  induction c using QuotientGroup.induction_on with
  | H x => change coset f ((g*x)*stable f) = coset f (g*(x*stable f)); rw [mul_assoc]


-- @@ L405-409 verbatim
lemma origin_action_mem (g : Torus f) (c : Coset f) :
    (origin f (g • c))⁻¹ * (g * origin f c) ∈ (of f).range := by
  apply QuotientGroup.eq.mp
  change coset f (origin f (g • c)) = coset f (g * origin f c)
  rw [coset_origin,← smul_coset,coset_origin]


-- @@ L411-412 verbatim
def actionOffset (g : Torus f) (c : Coset f) : U :=
  Classical.choose (origin_action_mem f g c)

-- @@ L413-415 verbatim
lemma origin_action (g : Torus f) (c : Coset f) :
    origin f (g • c) * of f (actionOffset f g c) = g * origin f c := by
  rw [actionOffset,Classical.choose_spec (origin_action_mem f g c),mul_inv_cancel_left]


-- @@ L417-417 verbatim
variable (hf : Function.Injective f)

-- @@ L418-418 verbatim
include hf

-- @@ L419-423 verbatim
lemma actionOffset_one (c : Coset f) : actionOffset f 1 c = 1 := by
  apply of_injective f hf
  have h := origin_action f 1 c
  rw [one_smul,one_mul] at h
  exact (mul_left_cancel (h.trans (mul_one _).symm)).trans (map_one _).symm

-- @@ L424-429 verbatim
lemma actionOffset_mul (g h : Torus f) (c : Coset f) :
    actionOffset f (g*h) c = actionOffset f g (h • c) * actionOffset f h c := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f ((g*h) • c))
  rw [map_mul,origin_action,mul_smul,←mul_assoc,origin_action]
  rw [mul_assoc,mul_assoc,origin_action]

-- @@ L430-443 verbatim
lemma actionOffset_next (g : Torus f) (c : Coset f) :
    actionOffset f g (next f c) * cosetOffset f c =
      cosetOffset f (g • c) * f (actionOffset f g c) := by
  apply of_injective f hf
  apply mul_left_cancel (a := origin f (next f (g • c)))
  calc
    origin f (next f (g • c)) * of f (actionOffset f g (next f c) * cosetOffset f c) =
        (origin f (g • next f c) * of f (actionOffset f g (next f c))) * of f (cosetOffset f c) := by rw [map_mul,←mul_assoc,next_smul]
    _ = g * (origin f (next f c) * of f (cosetOffset f c)) := by rw [origin_action,mul_assoc]
    _ = g * (origin f c * stable f) := by rw [origin_next]
    _ = (origin f (g • c) * of f (actionOffset f g c)) * stable f := by rw [origin_action,mul_assoc]
    _ = (origin f (g • c) * stable f) * of f (f (actionOffset f g c)) := by rw [mul_assoc,of_mul_stable,←mul_assoc]
    _ = (origin f (next f (g • c)) * of f (cosetOffset f (g • c))) * of f (f (actionOffset f g c)) := by rw [origin_next]
    _ = origin f (next f (g • c)) * of f (cosetOffset f (g • c) * f (actionOffset f g c)) := by rw [map_mul,mul_assoc]


-- @@ L445-445 verbatim
end

-- @@ L446-446 verbatim
end UniversalFInfinity.AscendingTorus


-- @@ L448-448 verbatim
end OAI
