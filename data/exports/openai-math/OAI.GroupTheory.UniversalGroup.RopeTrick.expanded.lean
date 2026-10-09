import OAI.GroupTheory.UniversalGroup.CentralHNN


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w x


-- @@ L7-7 verbatim
namespace Higman

-- @@ L8-8 verbatim
open Monoid Coprod


-- @@ L10-31 verbatim
lemma commute_of_free_generators {ι : Type u} {κ : Type v}
    {G : Type w} {H : Type x} {K : Type*} [Group G] [Group H] [Group K]
    (p : FreeGroup ι →* G) (hp : Function.Surjective p)
    (q : FreeGroup κ →* H) (hq : Function.Surjective q)
    (f : G →* K) (g : H →* K)
    (hc : ∀ i j, Commute (f (p (FreeGroup.of i))) (g (q (FreeGroup.of j)))) :
    ∀ a b, Commute (f a) (g b) := by
  intro a b
  obtain ⟨a,rfl⟩ := hp a
  obtain ⟨b,rfl⟩ := hq b
  have hgen (i : ι) (b : FreeGroup κ) :
      Commute (f (p (FreeGroup.of i))) (g (q b)) := by
    induction b using FreeGroup.induction_on with
    | one => simp
    | of j => exact hc i j
    | inv_of b hb => simpa only [map_inv] using hb.inv_right
    | mul b c hb hc => simpa only [map_mul] using hb.mul_right hc
  induction a using FreeGroup.induction_on with
  | one => simp
  | of i => exact hgen i b
  | inv_of a ha => simpa only [map_inv] using ha.inv_left
  | mul a c ha hc => simpa only [map_mul] using ha.mul_left hc


-- @@ L33-72 verbatim
theorem finitelyPresented_prod {G : Type u} {H : Type v} [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  classical
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := G)
  obtain ⟨m,q,hq,_⟩ := Group.IsFinitelyPresented.out (G := H)
  let relation : Fin n × Fin m → G ∗ H := fun ij ↦
    (inl (p (FreeGroup.of ij.1)) * inr (q (FreeGroup.of ij.2))) *
      (inr (q (FreeGroup.of ij.2)) * inl (p (FreeGroup.of ij.1)))⁻¹
  let N := Subgroup.normalClosure (Set.range relation)
  let Q := (G ∗ H) ⧸ N
  let proj : G ∗ H →* Q := QuotientGroup.mk' N
  let f : G →* Q := proj.comp inl
  let g : H →* Q := proj.comp inr
  have hcomm : ∀ a b, Commute (f a) (g b) := by
    apply commute_of_free_generators p hp q hq
    intro i j
    have h : proj (relation (i,j)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨(i,j),rfl⟩)
    exact mul_inv_eq_one.mp (by simpa only [f,g,MonoidHom.comp_apply,relation,map_mul,map_inv] using h)
  let π : G ∗ H →* G × H := Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  let s : G × H →* Q := MonoidHom.noncommCoprod f g hcomm
  have hs : s.comp π = proj := by
    apply Coprod.hom_ext <;> ext z <;> simp [s,π,f,g]
  have hker : π.ker = N := by
    apply le_antisymm
    · intro z hz
      apply (QuotientGroup.eq_one_iff _).mp
      change proj z = 1
      rw [← hs]
      change s (π z) = 1
      rw [show π z = 1 from hz,map_one]
    · apply Subgroup.normalClosure_le_normal
      rintro z ⟨⟨i,j⟩,rfl⟩
      change π (relation (i,j)) = 1
      simp [π,relation]
  apply Group.IsFinitelyPresented.of_surjective π
  · rintro ⟨a,b⟩
    exact ⟨inl a * inr b,by simp [π]⟩
  · exact ⟨Set.range relation,Set.finite_range _,hker.symm⟩


-- @@ L74-74 verbatim
end Higman


-- @@ L76-76 verbatim
namespace Higman.RopeTrick


-- @@ L78-78 verbatim
section

-- @@ L79-79 verbatim
open Monoid Coprod Multiplicative


-- @@ L81-81 verbatim
section Container

-- @@ L82-82 verbatim
variable {ι : Type u} {K : Type v} [Group K]


-- @@ L84-84 verbatim
abbrev Raw := (K × FreeGroup ι) ∗ Multiplicative ℤ


-- @@ L86-86 verbatim
def rawK : K →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inl K (FreeGroup ι))

-- @@ L87-87 verbatim
def rawF : FreeGroup ι →* Raw (ι := ι) (K := K) := Coprod.inl.comp (MonoidHom.inr K (FreeGroup ι))

-- @@ L88-88 verbatim
def rawT : Raw (ι := ι) (K := K) := Coprod.inr (ofAdd 1)


-- @@ L90-94 verbatim
def relation (α β : FreeGroup ι →* K) : ι ⊕ ι → Raw (ι := ι) (K := K)
  | .inl j => (rawT * rawK (α (FreeGroup.of j))) *
      (rawK (α (FreeGroup.of j)) * rawT)⁻¹
  | .inr j => (rawT * rawK (β (FreeGroup.of j))) *
      (rawK (β (FreeGroup.of j)) * rawF (FreeGroup.of j) * rawT)⁻¹


-- @@ L96-96 verbatim
abbrev relations (α β : FreeGroup ι →* K) := Subgroup.normalClosure (Set.range (relation α β))

-- @@ L97-97 verbatim
abbrev Container (α β : FreeGroup ι →* K) := Raw (ι := ι) (K := K) ⧸ relations α β


-- @@ L99-100 verbatim
def proj (α β : FreeGroup ι →* K) : Raw (ι := ι) (K := K) →* Container α β :=
  QuotientGroup.mk' (relations α β)

-- @@ L101-101 verbatim
def kMap (α β : FreeGroup ι →* K) : K →* Container α β := (proj α β).comp rawK

-- @@ L102-102 verbatim
def fMap (α β : FreeGroup ι →* K) : FreeGroup ι →* Container α β := (proj α β).comp rawF

-- @@ L103-103 verbatim
def stable (α β : FreeGroup ι →* K) : Container α β := proj α β rawT


-- @@ L105-108 verbatim
theorem finitelyPresented [Finite ι] [Group.IsFinitelyPresented K]
    (α β : FreeGroup ι →* K) : Group.IsFinitelyPresented (Container α β) := by
  let := Higman.finitelyPresented_prod (G := K) (H := FreeGroup ι)
  exact Group.IsFinitelyPresented.quotient _ ⟨Set.range (relation α β),Set.finite_range _,rfl⟩


-- @@ L110-112 verbatim
lemma relation_zero (α β : FreeGroup ι →* K) (j : ι ⊕ ι) :
    proj α β (relation α β j) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩)


-- @@ L114-119 verbatim
lemma generator_zero (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (α (FreeGroup.of j)) =
      kMap α β (α (FreeGroup.of j)) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inl j)


-- @@ L121-126 verbatim
lemma generator_one (α β : FreeGroup ι →* K) (j : ι) :
    stable α β * kMap α β (β (FreeGroup.of j)) =
      kMap α β (β (FreeGroup.of j)) * fMap α β (FreeGroup.of j) * stable α β := by
  apply mul_inv_eq_one.mp
  simpa only [proj,relation,map_mul,map_inv,kMap,fMap,stable,MonoidHom.comp_apply] using
    relation_zero α β (.inr j)


-- @@ L128-137 verbatim
lemma conjugate_zero (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (α w) * (stable α β)⁻¹ = kMap α β (α w) := by
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp α) =
      (kMap α β).comp α := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (α (FreeGroup.of j)) * (stable α β)⁻¹ = _
    rw [generator_zero,mul_inv_cancel_right]
    rfl
  exact DFunLike.congr_fun hh w


-- @@ L139-144 verbatim
lemma pair_eq (α β : FreeGroup ι →* K) (k : K) (w : FreeGroup ι) :
    proj α β (Coprod.inl (k,w)) = kMap α β k * fMap α β w := by
  change proj α β (Coprod.inl (k,w)) =
    proj α β (Coprod.inl (k,1)) * proj α β (Coprod.inl (1,w))
  rw [← map_mul,← map_mul]
  simp


-- @@ L146-160 verbatim
lemma conjugate_one (α β : FreeGroup ι →* K) (w : FreeGroup ι) :
    stable α β * kMap α β (β w) * (stable α β)⁻¹ =
      kMap α β (β w) * fMap α β w := by
  let p : FreeGroup ι →* Container α β :=
    ((proj α β).comp Coprod.inl).comp (β.prod (MonoidHom.id _))
  have hh : (MulAut.conj (stable α β)).toMonoidHom.comp ((kMap α β).comp β) = p := by
    apply FreeGroup.ext_hom
    intro j
    change stable α β * kMap α β (β (FreeGroup.of j)) * (stable α β)⁻¹ =
      proj α β (Coprod.inl (β (FreeGroup.of j),FreeGroup.of j))
    rw [generator_one,mul_inv_cancel_right,pair_eq]
  have h := DFunLike.congr_fun hh w
  change stable α β * kMap α β (β w) * (stable α β)⁻¹ =
    proj α β (Coprod.inl (β w,w)) at h
  rwa [pair_eq] at h


-- @@ L162-166 verbatim
lemma kills_relation (α β : FreeGroup ι →* K) (w : FreeGroup ι) (hw : α w = β w) :
    fMap α β w = 1 := by
  have h0 := conjugate_zero α β w
  rw [hw,conjugate_one] at h0
  exact mul_left_cancel (h0.trans (mul_one _).symm)


-- @@ L168-168 verbatim
end Container


-- @@ L170-170 verbatim
variable {A : Type u} {K : Type v} {G : Type w} [Group A] [Group K] [Group G]

-- @@ L171-171 verbatim
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)


-- @@ L173-173 verbatim
def left : A →* K × G := i.prod 1

-- @@ L174-174 verbatim
def right : A →* K × G := i.prod r


-- @@ L176-179 verbatim
include hi in
lemma left_injective : Function.Injective (left i (G := G)) := by
  intro a b h
  exact hi (congrArg Prod.fst h)

-- @@ L180-183 verbatim
include hi in
lemma right_injective : Function.Injective (right i r) := by
  intro a b h
  exact hi (congrArg Prod.fst h)


-- @@ L185-187 verbatim
noncomputable def associated : (left i (G := G)).range ≃* (right i r).range :=
  (MonoidHom.ofInjective (left_injective i hi)).symm.trans
    (MonoidHom.ofInjective (right_injective i hi r))


-- @@ L189-189 verbatim
abbrev Model := HNNExtension (K × G) (left i (G := G)).range (right i r).range (associated i hi r)


-- @@ L191-197 verbatim
lemma associated_left (a : A) : associated i hi r ⟨left i a,⟨a,rfl⟩⟩ =
    ⟨right i r a,⟨a,rfl⟩⟩ := by
  change (MonoidHom.ofInjective (right_injective i hi r))
    ((MonoidHom.ofInjective (left_injective i hi)).symm
      ((MonoidHom.ofInjective (left_injective i hi)) a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl


-- @@ L199-204 verbatim
lemma model_relation (a : A) :
    (HNNExtension.t : Model i hi r) * HNNExtension.of (i a,1) =
      HNNExtension.of (i a,r a) * HNNExtension.t := by
  have h := HNNExtension.t_mul_of (φ := associated i hi r) ⟨left i a,⟨a,rfl⟩⟩
  rw [associated_left] at h
  exact h


-- @@ L206-206 verbatim
end


-- @@ L208-208 verbatim
open Monoid Coprod Multiplicative

-- @@ L209-209 verbatim
noncomputable section

-- @@ L210-210 verbatim
variable {ι : Type u} {A : Type v} {K : Type w} {G : Type x}

-- @@ L211-211 verbatim
variable [Group A] [Group K] [Group G]

-- @@ L212-212 verbatim
variable (i : A →* K) (hi : Function.Injective i) (r : A →* G)

-- @@ L213-213 verbatim
variable (q : FreeGroup ι →* G)


-- @@ L215-217 verbatim
def evaluate : Raw (ι := ι) (K := K) →* Model i hi r :=
  Coprod.lift (HNNExtension.of.comp ((MonoidHom.id K).prodMap q))
    (zpowersHom _ HNNExtension.t)


-- @@ L219-221 verbatim
@[simp] lemma evaluate_rawK (k : K) :
    evaluate i hi r q (rawK k) = HNNExtension.of (k,1) := by
  simp [evaluate,rawK]

-- @@ L222-224 verbatim
@[simp] lemma evaluate_rawF (w : FreeGroup ι) :
    evaluate i hi r q (rawF w) = HNNExtension.of (1,q w) := by
  simp [evaluate,rawF]

-- @@ L225-227 verbatim
@[simp] lemma evaluate_rawT :
    evaluate i hi r q rawT = HNNExtension.t := by
  simp [evaluate,rawT]


-- @@ L229-229 verbatim
variable (p₀ p₁ : FreeGroup ι →* A)

-- @@ L230-230 verbatim
variable (h₀ : ∀ w, r (p₀ w) = 1) (h₁ : ∀ w, r (p₁ w) = q w)


-- @@ L232-245 verbatim
include h₀ h₁ in
lemma evaluate_relation (j : ι ⊕ ι) :
    evaluate i hi r q (relation (i.comp p₀) (i.comp p₁) j) = 1 := by
  cases j with
  | inl j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    simpa only [MonoidHom.comp_apply,h₀] using model_relation i hi r (p₀ (FreeGroup.of j))
  | inr j =>
    simp only [relation,map_mul,map_inv,evaluate_rawK,evaluate_rawF,evaluate_rawT]
    apply mul_inv_eq_one.mpr
    rw [← map_mul]
    simpa only [MonoidHom.comp_apply,Prod.mk_mul_mk,mul_one,one_mul,h₁] using
      model_relation i hi r (p₁ (FreeGroup.of j))


-- @@ L247-251 verbatim
def detect : Container (i.comp p₀) (i.comp p₁) →* Model i hi r :=
  QuotientGroup.lift _ (evaluate i hi r q) (by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨j,rfl⟩
    exact evaluate_relation i hi r q p₀ p₁ h₀ h₁ j)


-- @@ L253-257 verbatim
@[simp] lemma detect_fMap (w : FreeGroup ι) :
    detect i hi r q p₀ p₁ h₀ h₁ (fMap (i.comp p₀) (i.comp p₁) w) =
      HNNExtension.of (1,q w) := by
  change evaluate i hi r q (rawF w) = _
  exact evaluate_rawF i hi r q w


-- @@ L259-283 verbatim
include hi h₀ h₁ in

theorem embeds_quotient [Finite ι] [Group.IsFinitelyPresented K]
    (hq : Function.Surjective q)
    (hident : ∀ w ∈ q.ker, i (p₀ w) = i (p₁ w)) :
    ∃ (Q : Type (max u w)) (_ : Group Q) (_ : Group.IsFinitelyPresented Q),
      ∃ j : G →* Q, Function.Injective j := by
  let α := i.comp p₀
  let β := i.comp p₁
  have hk : q.ker ≤ (fMap α β).ker := by
    intro w hw
    exact kills_relation α β w (hident w hw)
  let j : G →* Container α β := q.liftOfSurjective hq ⟨fMap α β,hk⟩
  have hj (w : FreeGroup ι) : j (q w) = fMap α β w := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let d := detect i hi r q p₀ p₁ h₀ h₁
  have hd (g : G) : d (j g) = HNNExtension.of (1,g) := by
    obtain ⟨w,rfl⟩ := hq g
    rw [hj]
    exact detect_fMap i hi r q p₀ p₁ h₀ h₁ w
  refine ⟨Container α β,inferInstance,finitelyPresented α β,j,?_⟩
  intro g h he
  have hh := congrArg d he
  rw [hd,hd] at hh
  exact congrArg Prod.snd (HNNExtension.of_injective (φ := associated i hi r) hh)


-- @@ L285-285 verbatim
end

-- @@ L286-286 verbatim
end Higman.RopeTrick


-- @@ L288-288 verbatim
namespace Higman

-- @@ L289-289 verbatim
variable {G : Type u} [Group G]


-- @@ L291-294 verbatim
def IsBenign (A : Subgroup G) : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
    (i : G →* K), Function.Injective i ∧
    ∃ B : Subgroup K, B.FG ∧ B.comap i = A


-- @@ L296-296 verbatim
namespace Double

-- @@ L297-300 verbatim
lemma firstIn_eq_secondIn {A : Subgroup G} {g : G} (hg : g ∈ A) :
    firstIn A g = secondIn A g := by
  apply Subtype.ext
  exact HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g,hg⟩

-- @@ L301-301 verbatim
end Double


-- @@ L303-321 verbatim
theorem embeds_of_benign_kernel {ι : Type u} [Finite ι]
    {D : Type v} [Group D] (q : FreeGroup ι →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  obtain ⟨K,_,_,i,hi,B,hB,hBi⟩ := hben
  let E := CentralExtension K B
  have : Group.IsFinitelyPresented E := CentralExtension.finitelyPresented hB
  let j := CentralExtension.map i (le_of_eq hBi.symm)
  have hj : Function.Injective j := CentralExtension.map_injective i hi hBi
  let A := Double.subgroup q.ker
  let jA : A →* E := j.comp A.subtype
  have hjA : Function.Injective jA := hj.comp Subtype.val_injective
  let r := Double.read q (le_refl q.ker)
  exact RopeTrick.embeds_quotient jA hjA r q
    (Double.firstIn q.ker) (Double.secondIn q.ker)
    (Double.read_first q (le_refl q.ker))
    (Double.read_second q (le_refl q.ker)) hq
    (fun w hw ↦ congrArg jA (Double.firstIn_eq_secondIn hw))


-- @@ L323-323 verbatim
namespace IsBenign

-- @@ L324-324 verbatim
variable {A B : Subgroup G}


-- @@ L326-328 verbatim
theorem of_fg [Group.IsFinitelyPresented G] (hA : A.FG) : IsBenign A := by
  refine ⟨G,inferInstance,inferInstance,MonoidHom.id G,Function.injective_id,A,hA,?_⟩
  rfl


-- @@ L330-340 verbatim
theorem inf (hA : IsBenign A) (hB : IsBenign B) : IsBenign (A ⊓ B) := by
  obtain ⟨K,_,_,i,hi,L,hL,hLi⟩ := hA
  obtain ⟨K',_,_,j,_,L',hL',hLj⟩ := hB
  refine ⟨K × K',inferInstance,finitelyPresented_prod,i.prod j,?_,L.prod L',
    hL.prod hL',?_⟩
  · intro x y h
    exact hi (congrArg Prod.fst h)
  · ext x
    change i x ∈ L ∧ j x ∈ L' ↔ x ∈ A ∧ x ∈ B
    change x ∈ L.comap i ∧ x ∈ L'.comap j ↔ _
    rw [hLi,hLj]


-- @@ L342-355 verbatim
theorem comap {D : Type u} [Group D] [Group.IsFinitelyPresented D]
    (hA : IsBenign A) (f : D →* G) : IsBenign (A.comap f) := by
  obtain ⟨n,p,hp,_⟩ := Group.IsFinitelyPresented.out (G := D)
  have : Group.FG D := Group.fg_of_surjective hp
  obtain ⟨K,_,_,i,_,L,hL,hLi⟩ := hA
  refine ⟨D × K,inferInstance,finitelyPresented_prod,
    (MonoidHom.id D).prod (i.comp f),?_,(⊤ : Subgroup D).prod L,
    Group.FG.out.prod hL,?_⟩
  · intro x y h
    exact congrArg Prod.fst h
  · ext x
    change (x ∈ (⊤ : Subgroup D) ∧ i (f x) ∈ L) ↔ f x ∈ A
    simpa only [Subgroup.mem_top,true_and,Subgroup.mem_comap] using
      (show f x ∈ L.comap i ↔ f x ∈ A by rw [hLi])


-- @@ L357-357 verbatim
end IsBenign


-- @@ L359-359 verbatim
end Higman


-- @@ L361-361 verbatim
end OAI
