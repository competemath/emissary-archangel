import OAI.GroupTheory.UniversalGroup.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section UniversalFinitelyPresentedProof

-- @@ L6-6 verbatim
universe u v w x


-- @@ L8-8 verbatim
namespace Higman

-- @@ L9-9 verbatim
open HNNExtension


-- @@ L11-12 verbatim
abbrev CentralExtension (G : Type u) [Group G] (A : Subgroup G) :=
  HNNExtension G A A (MulEquiv.refl A)


-- @@ L14-14 verbatim
namespace CentralExtension

-- @@ L15-15 verbatim
variable {G : Type u} [Group G] {K : Type v} [Group K]

-- @@ L16-16 verbatim
variable {A : Subgroup G} {B : Subgroup K}


-- @@ L18-22 verbatim
def map (i : G →* K) (hi : A ≤ B.comap i) :
    CentralExtension G A →* CentralExtension K B :=
  HNNExtension.lift (HNNExtension.of.comp i) HNNExtension.t (by
    intro a
    exact HNNExtension.t_mul_of (φ := MulEquiv.refl B) ⟨i a, hi a.2⟩)


-- @@ L24-26 verbatim
@[simp] theorem map_of (i : G →* K) (hi : A ≤ B.comap i) (g : G) :
    map i hi (HNNExtension.of g) = HNNExtension.of (i g) := by
  exact HNNExtension.lift_of _ _ _ g


-- @@ L28-30 verbatim
@[simp] theorem map_t (i : G →* K) (hi : A ≤ B.comap i) :
    map i hi HNNExtension.t = HNNExtension.t := by
  exact HNNExtension.lift_t _ _ _


-- @@ L32-44 verbatim
def mapWord (i : G →* K) (hi : B.comap i = A)
    (r : NormalWord.ReducedWord G A A) : NormalWord.ReducedWord K B B where
  head := i r.head
  toList := r.toList.map (fun p ↦ (p.1, i p.2))
  chain := by
    apply (List.isChain_map _).mpr
    apply r.chain.imp
    intro a b hab hmem
    apply hab
    have hm : i a.2 ∈ B := by
      simpa [HNNExtension.toSubgroup] using hmem
    have : a.2 ∈ B.comap i := hm
    simpa [hi, HNNExtension.toSubgroup] using this


-- @@ L46-50 verbatim
@[simp] theorem mapWord_prod (i : G →* K) (hi : B.comap i = A)
    (r : NormalWord.ReducedWord G A A) :
    (mapWord i hi r).prod (MulEquiv.refl B) =
      map i (le_of_eq hi.symm) (r.prod (MulEquiv.refl A)) := by
  simp [NormalWord.ReducedWord.prod, mapWord, map_list_prod, List.map_map, Function.comp_def]


-- @@ L52-75 verbatim
theorem map_injective (i : G →* K) (hinj : Function.Injective i)
    (hi : B.comap i = A) : Function.Injective (map i (le_of_eq hi.symm)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A A
  let r := (NormalWord.equiv (MulEquiv.refl A) d g)
  have hr : r.prod (MulEquiv.refl A) = g :=
    (NormalWord.equiv (MulEquiv.refl A) d).symm_apply_apply g
  have hm : (mapWord i hi r.toReducedWord).prod (MulEquiv.refl B) = 1 := by
    rw [mapWord_prod]
    change map i (le_of_eq hi.symm) (r.prod (MulEquiv.refl A)) = 1
    rw [hr]
    exact hg
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl B) (mapWord i hi r.toReducedWord)
    (by rw [hm]; exact Subgroup.one_mem _)
  have hnil : r.toList = [] := by simpa [mapWord] using hn
  have hhead : i r.head = 1 := by
    apply HNNExtension.of_injective (φ := MulEquiv.refl B)
    simpa [mapWord, NormalWord.ReducedWord.prod, hnil] using hm
  have hhead' : r.head = 1 := hinj (by simpa using hhead)
  rw [Subgroup.mem_bot, ← hr]
  simp [NormalWord.ReducedWord.prod, hnil, hhead']


-- @@ L77-77 verbatim
open Monoid Coprod Multiplicative


-- @@ L79-80 verbatim
def relation (g : G) : G ∗ Multiplicative ℤ :=
  (inr (ofAdd 1) * inl g) * (inl g * inr (ofAdd 1))⁻¹


-- @@ L82-129 verbatim
theorem con_finitelyNormallyGenerated (hA : A.FG) :
    (HNNExtension.con G A A (MulEquiv.refl A)).subgroup.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S, hS⟩ := hA
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  let N : Subgroup (G ∗ Multiplicative ℤ) :=
    Subgroup.normalClosure (relation '' (S : Set G))
  let Q := (G ∗ Multiplicative ℤ) ⧸ N
  let q : G ∗ Multiplicative ℤ →* Q := QuotientGroup.mk' N
  let f : G →* Q := q.comp inl
  let t : Q := q (inr (ofAdd 1))
  let e : G →* Q := (MulAut.conj t).toMonoidHom.comp f
  have hgen : (S : Set G) ⊆ f.eqLocus e := by
    intro g hg
    have hh : q (relation g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨g, hg, rfl⟩)
    have he : t * f g = f g * t := by
      apply mul_inv_eq_one.mp
      exact hh
    change f g = t * f g * t⁻¹
    rw [he, mul_inv_cancel_right]
  have hAeq : A ≤ f.eqLocus e := by
    rw [← hS]
    exact (Subgroup.closure_le _).mpr hgen
  have hC : C ≤ Con.ker q := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨a, rfl, rfl⟩
    change t * f a = f a * t
    have ha : f a = t * f a * t⁻¹ := hAeq a.2
    nth_rw 2 [ha]
    simp only [inv_mul_cancel_right]
  refine ⟨relation '' (S : Set G), S.finite_toSet.image _, ?_⟩
  change N = C.subgroup
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨g, hg, rfl⟩
    have hgA : g ∈ A := by rw [← hS]; exact Subgroup.subset_closure hg
    have hr : C (inr (ofAdd 1) * inl g) (inl g * inr (ofAdd 1)) :=
      ConGen.Rel.of _ _ ⟨⟨g, hgA⟩, rfl, rfl⟩
    change C (relation g) 1
    have hh := C.mul hr (C.refl (inl g * inr (ofAdd 1))⁻¹)
    have hcancel : (inl g * inr (ofAdd 1) : G ∗ Multiplicative ℤ) *
        (inl g * inr (ofAdd 1))⁻¹ = 1 := mul_inv_cancel _
    rw [hcancel] at hh
    exact hh
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact (hC hx).trans (map_one q)


-- @@ L131-138 verbatim
theorem finitelyPresented [Group.IsFinitelyPresented G] (hA : A.FG) :
    Group.IsFinitelyPresented (CentralExtension G A) := by
  let C := HNNExtension.con G A A (MulEquiv.refl A)
  have hC := con_finitelyNormallyGenerated hA
  have hfp := Group.IsFinitelyPresented.quotient C.subgroup hC
  change Group.IsFinitelyPresented C.Quotient
  rw [← QuotientGroup.con_subgroup C]
  exact hfp


-- @@ L140-140 verbatim
end CentralExtension

-- @@ L141-141 verbatim
end Higman


-- @@ L143-143 verbatim
namespace Higman.Double

-- @@ L144-144 verbatim
open HNNExtension Multiplicative

-- @@ L145-145 verbatim
variable {G : Type u} [Group G] {D : Type v} [Group D]

-- @@ L146-146 verbatim
variable (A : Subgroup G)


-- @@ L148-148 verbatim
abbrev Extension := HNNExtension G A A (MulEquiv.refl A)


-- @@ L150-150 verbatim
def first : G →* Extension A := HNNExtension.of


-- @@ L152-153 verbatim
def second : G →* Extension A :=
  (MulAut.conj HNNExtension.t).toMonoidHom.comp (first A)


-- @@ L155-155 verbatim
def subgroup : Subgroup (Extension A) := (first A).range ⊔ (second A).range


-- @@ L157-158 verbatim
def firstIn : G →* subgroup A :=
  (first A).codRestrict (subgroup A) (fun g ↦ (le_sup_left : (first A).range ≤ subgroup A) ⟨g,rfl⟩)


-- @@ L160-161 verbatim
def secondIn : G →* subgroup A :=
  (second A).codRestrict (subgroup A) (fun g ↦ (le_sup_right : (second A).range ≤ subgroup A) ⟨g,rfl⟩)


-- @@ L163-163 verbatim
variable {A}


-- @@ L165-171 verbatim
def lamp : D →* D ≀ᵣ Multiplicative ℤ where
  toFun d := ⟨fun n ↦ if n = 1 then d else 1, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext n
    · by_cases hn : n = 1 <;> simp [hn]
    · simp


-- @@ L173-174 verbatim
@[simp] theorem lamp_left (d : D) (n : Multiplicative ℤ) :
    (lamp d).left n = if n = 1 then d else 1 := rfl


-- @@ L176-176 verbatim
@[simp] theorem lamp_right (d : D) : (lamp d).right = 1 := rfl


-- @@ L178-184 verbatim
def coordinate (n : Multiplicative ℤ) :
    (RegularWreathProduct.rightHom : D ≀ᵣ Multiplicative ℤ →* Multiplicative ℤ).ker →* D where
  toFun x := x.1.left n
  map_one' := rfl
  map_mul' x y := by
    have hx : x.1.right = 1 := x.2
    simp [RegularWreathProduct.mul_left, hx]


-- @@ L186-191 verbatim
def wreathMap (q : G →* D) (hq : A ≤ q.ker) :
    Extension A →* D ≀ᵣ Multiplicative ℤ :=
  HNNExtension.lift (lamp.comp q) (RegularWreathProduct.inl (ofAdd 1)) (by
    intro a
    have ha : q a = 1 := hq a.2
    simp [ha])


-- @@ L193-195 verbatim
@[simp] theorem wreathMap_first (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    wreathMap q hq (first A g) = lamp (q g) := by
  simp [wreathMap, first]


-- @@ L197-201 verbatim
@[simp] theorem wreathMap_second (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    wreathMap q hq (second A g) =
      RegularWreathProduct.inl (ofAdd 1) * lamp (q g) *
        (RegularWreathProduct.inl (ofAdd 1))⁻¹ := by
  simp [second, MulAut.conj_apply, wreathMap, first]


-- @@ L203-211 verbatim
theorem subgroup_le_coordKer (q : G →* D) (hq : A ≤ q.ker) :
    subgroup A ≤ (RegularWreathProduct.rightHom.comp (wreathMap q hq)).ker := by
  apply sup_le
  · rintro _ ⟨g,rfl⟩
    change (wreathMap q hq (first A g)).right = 1
    simp
  · rintro _ ⟨g,rfl⟩
    change (wreathMap q hq (second A g)).right = 1
    simp


-- @@ L213-216 verbatim
def read (q : G →* D) (hq : A ≤ q.ker) : subgroup A →* D :=
  (coordinate (ofAdd 1)).comp
    (((wreathMap q hq).comp (subgroup A).subtype).codRestrict _
      (fun x ↦ subgroup_le_coordKer q hq x.2))


-- @@ L218-222 verbatim
@[simp] theorem read_first (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    read q hq (firstIn A g) = 1 := by
  change (wreathMap q hq (first A g)).left (ofAdd 1) = 1
  rw [wreathMap_first, lamp_left]
  simp


-- @@ L224-228 verbatim
@[simp] theorem read_second (q : G →* D) (hq : A ≤ q.ker) (g : G) :
    read q hq (secondIn A g) = q g := by
  change (wreathMap q hq (second A g)).left (ofAdd 1) = q g
  rw [wreathMap_second]
  simp


-- @@ L230-230 verbatim
end Higman.Double


-- @@ L232-232 verbatim
end UniversalFinitelyPresentedProof


-- @@ L234-234 verbatim
end OAI
