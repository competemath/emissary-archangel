import DG.Homotopy.SemiFree


-- @@ L3-43 verbatim
/-!
# The lifting property against surjective quasi-isomorphisms

Let `A` be a dg ring. A dg module `P` has the lifting property against surjective
quasi-isomorphisms (it is cofibrant in the projective model structure) if every morphism
`P → N` lifts along every surjective quasi-isomorphism `M → N`. This file shows that this
property is equivalent to `P` being K-projective *and* graded-projective, and that semi-free and
finite-cell dg modules have it.

## Main definitions

* `DG.IsGradedProjective A P`: graded `A`-linear maps of degree `0` out of `P` lift along
  surjective morphisms of dg modules.
* `DG.HasLiftingProperty A P`: morphisms out of `P` lift along surjective quasi-isomorphisms.
* `DG.Cochain.codRestrict`: a cochain with values in a dg submodule, as a cochain to it.

## Main results

* `DG.hasLiftingProperty_iff`: `HasLiftingProperty A P ↔ IsKProjective A P ∧
  IsGradedProjective A P`, with the two halves `DG.HasLiftingProperty.isKProjective`,
  `DG.HasLiftingProperty.isGradedProjective` and `DG.IsKProjective.hasLiftingProperty`.
* `DG.DGModuleHom.isAcyclic_ker`: the kernel of a surjective quasi-isomorphism is acyclic.
* `DG.SemiFreeFiltration.isGradedProjective`, `DG.SemiFreeFiltration.hasLiftingProperty`,
  `DG.FiniteCellFiltration.isGradedProjective`, `DG.FiniteCellFiltration.hasLiftingProperty`.

## K-projective versus the lifting property

The lifting property implies K-projectivity, but not conversely: K-projectivity is invariant
under homotopy equivalence, whereas the lifting property forces graded projectivity. For
instance, for `A = ℤ` concentrated in degree `0`, the cone of the identity of `ℚ` (the complex
`ℚ → ℚ` in degrees `-1, 0`) is contractible, hence K-projective, but `ℚ` is not a projective
`ℤ`-module, so by `DG.hasLiftingProperty_iff` it does not have the lifting property. The correct
statement is the equivalence `DG.hasLiftingProperty_iff`; the cofibrant dg modules are the
K-projective dg modules which are projective as graded modules (and they are the retracts of
semi-free modules, once semi-free resolutions are available).

## Universes

As for `DG.IsKProjective`, the modules `M`, `N` in the definitions range over a universe `w`
which is a parameter of the definitions.
-/


-- @@ L45-45 verbatim
universe w w'


-- @@ L47-47 verbatim
namespace DG


-- @@ L49-49 verbatim
/-! ### Graded projectivity and the lifting property -/


-- @@ L51-51 verbatim
section Defs


-- @@ L53-54 verbatim
variable (A : Type*) [Ring A] [DGAddCommGroup A]
  (P : Type*) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]


-- @@ L56-68 expanded
/-- A dg module `P` is graded-projective if graded `A`-linear maps of degree `0` out of `P` lift
along surjective morphisms of dg modules: for every surjection `p : M → N` of dg modules
(`M N : Type w`) and every graded `A`-linear map `f : P → N` of degree `0` (not necessarily
compatible with the differentials) there is a graded `A`-linear `g : P → M` of degree `0` with
`p ∘ g = f`. This is implied by projectivity of `P` as a graded module over the underlying
graded ring of `A`, and (since every dg module is a quotient of a direct sum of cones of
identities of shifts of `A`, which is free as a graded module) equivalent to it. -/
@[pp_with_univ]
def IsGradedProjective : Prop :=
  ∀ (M N : Type w) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] (p : DGModuleHom A M N),
    Function.Surjective p →
      ∀ f : Cochain A P N 0, ∃ g : Cochain A P M 0, (Cochain.ofHom p).comp g (zero_add 0) = f


-- @@ L70-78 expanded
/-- A dg module `P` has the (left) lifting property with respect to surjective
quasi-isomorphisms if for every surjective quasi-isomorphism `p : M → N` (`M N : Type w`) every
morphism `f : P → N` lifts to a morphism `g : P → M`, `p ∘ g = f`. These are the cofibrant
objects of the projective model structure on dg modules. -/
@[pp_with_univ]
def HasLiftingProperty : Prop :=
  ∀ (M N : Type w) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] (p : DGModuleHom A M N),
    Function.Surjective p →
      p.IsQuasiIso → ∀ f : DGModuleHom A P N, ∃ g : DGModuleHom A P M, p.comp g = f


-- @@ L80-80 verbatim
end Defs


-- @@ L82-82 verbatim
/-! ### Cochains into dg submodules and kernels of surjective quasi-isomorphisms -/


-- @@ L84-84 verbatim
section Kernel


-- @@ L86-89 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]


-- @@ L91-98 verbatim
/-- A cochain with values in a dg submodule `S`, as a cochain to `S`. -/
def Cochain.codRestrict {n : ℤ} (c : Cochain A P M n) (S : DGSubmodule A M)
    (h : ∀ x, c x ∈ S) : Cochain A P S n where
  toFun x := ⟨c x, h x⟩
  map_zero' := Subtype.ext (map_zero c)
  map_add' x y := Subtype.ext (map_add c x y)
  map_mem' _ _ hx := c.map_mem hx
  map_smul' ha x := Subtype.ext (c.map_smul ha x)


-- @@ L100-103 verbatim
omit [DGModule A P] [DGModule A M] in
@[simp]
theorem Cochain.coe_codRestrict_apply {n : ℤ} (c : Cochain A P M n) (S : DGSubmodule A M)
    (h : ∀ x, c x ∈ S) (x : P) : (c.codRestrict S h x : M) = c x := rfl


-- @@ L105-111 verbatim
theorem Cochain.coe_δ_codRestrict {n : ℤ} (m : ℤ) (c : Cochain A P M n) (S : DGSubmodule A M)
    (h : ∀ x, c x ∈ S) (x : P) : (δ n m (c.codRestrict S h) x : M) = δ n m c x := by
  by_cases hnm : n + 1 = m
  · rw [δ_apply _ _ hnm, δ_apply _ _ hnm]
    rfl
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    rfl


-- @@ L113-134 expanded
omit [DGModule A M] [DGModule A N] in
/-- The kernel of a surjective quasi-isomorphism is acyclic. -/
theorem DGModuleHom.isAcyclic_ker (p : DGModuleHom A M N) (hp : Function.Surjective p)
    (hq : p.IsQuasiIso) : IsAcyclic p.ker :=
  by
  refine isAcyclic_iff.mpr fun n z hz hdz => ?_
  have hz' : (z : M) ∈ grading n := hz
  have hdz' : d (z : M) = 0 := congrArg Subtype.val hdz
  have hpz : p z = 0 := z.2
  obtain ⟨m, hm, hdm⟩ :=
    (cohomology.map_injective_iff p n).mp (hq n).1 _ hz' hdz' ⟨0, zero_mem _, by rw [d_zero, hpz]⟩
  have hdpm : d (p m) = 0 := by rw [← p.map_d, hdm, hpz]
  obtain ⟨m', hm', hdm', y, hy, hdy⟩ :=
    (cohomology.map_surjective_iff p (n - 1)).mp (hq (n - 1)).2 (p m) (p.map_mem hm) hdpm
  obtain ⟨y', hy', rfl⟩ := p.exists_mem_grading_of_surjective hp hy
  refine ⟨⟨m - m' + d y', ?_⟩, ?_, Subtype.ext ?_⟩
  · change p (m - m' + d y') = 0
    rw [map_add, map_sub, p.map_d, hdy]
    abel
  · change m - m' + d y' ∈ grading (n - 1)
    exact add_mem (sub_mem hm hm') (by simpa using d_mem hy')
  · change d (m - m' + d y') = z
    rw [d_add, d_sub, hdm, hdm', d_d, sub_zero, add_zero]


-- @@ L136-136 verbatim
end Kernel


-- @@ L138-138 verbatim
/-! ### The lifting property -/


-- @@ L140-140 verbatim
section Lifting


-- @@ L142-143 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]


-- @@ L145-148 expanded
/-- The shift `(N⟦-1⟧)⟦1⟧` is `N` (`DG.Shift.addEquiv` followed by `DG.Shift.zeroEquiv`). -/
def Shift.shiftNegOneEquiv (N : Type*) [AddCommGroup N] [DGAddCommGroup N] [Module A N] :
    DGModuleEquiv A (Shift 1 (Shift (-1) N)) N :=
  (Shift.addEquiv (A := A) (M := N) 1 (-1)).trans Shift.zeroEquiv


-- @@ L150-169 expanded
/-- A dg module with the lifting property against surjective quasi-isomorphisms is K-projective:
for acyclic `N`, the projection `Cone (id_{N⟦-1⟧}) → (N⟦-1⟧)⟦1⟧ = N` is a surjective
quasi-isomorphism from a contractible module. -/
theorem HasLiftingProperty.isKProjective (h : HasLiftingProperty.{w} A P) : IsKProjective.{w} A P :=
  by
  intro N _ _ _ _ hN f
  let C := Cone (DGModuleHom.id : DGModuleHom A (Shift (-1) N) (Shift (-1) N))
  let p : DGModuleHom A C N :=
    (Shift.shiftNegOneEquiv N).toDGModuleHom.comp (Cone.fstHom DGModuleHom.id)
  have hC : IsContractible A C := Cone.isContractible_id _
  have hp : Function.Surjective p := by
    intro y
    refine ⟨Cone.inlLinear _ ((Shift.shiftNegOneEquiv (A := A) N).symm y), ?_⟩
    simp only [p, DGModuleHom.comp_apply, DGModuleEquiv.coe_toDGModuleHom]
    rw [Cone.fstHom_inlLinear, DGModuleEquiv.apply_symm_apply]
  have hq : p.IsQuasiIso := DGModuleHom.isQuasiIso_of_isAcyclic (A := A) hC.isAcyclic hN p
  obtain ⟨g, hg⟩ := h C N p hp hq f
  rw [← hg]
  exact
    ((hC.homotopic_zero_of_right g).comp_right p).trans (Homotopic.of_eq (DGModuleHom.comp_zero p))


-- @@ L171-196 expanded
set_option backward.isDefEq.respectTransparency false in
/-- A dg module with the lifting property against surjective quasi-isomorphisms is
graded-projective: a graded map `f : P → N` of degree `0` is the second component of the
morphism `P → Cone (id_N)` with components `(-δ f, f)`, and `Cone (id_M) → Cone (id_N)` is a
surjective quasi-isomorphism for a surjection `M → N`. -/
theorem HasLiftingProperty.isGradedProjective (h : HasLiftingProperty.{w} A P) :
    IsGradedProjective.{w} A P :=
  by
  intro M N _ _ _ _ _ _ _ _ p hp f
  let q :
    DGModuleHom A (Cone (DGModuleHom.id : DGModuleHom A M M))
      (Cone (DGModuleHom.id : DGModuleHom A N N)) :=
    Cone.map p p rfl
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := hp ((Cone.fst _).1 y)
    obtain ⟨b, hb⟩ := hp (Cone.snd _ y)
    refine ⟨Cone.inl _ a + Cone.inr _ b, Cone.ext_to ?_ ?_⟩
    · simp [q, ha]
    · simp [q, hb]
  have hqq : q.IsQuasiIso :=
    DGModuleHom.isQuasiIso_of_isAcyclic (Cone.isContractible_id M).isAcyclic
      (Cone.isContractible_id N).isAcyclic q
  let α : Cocycle A P N 1 := Cocycle.mk (-δ 0 1 f) 2 (by norm_num) (by rw [δ_neg, δ_δ, neg_zero])
  obtain ⟨G, hG⟩ :=
    h _ _ q hq hqq
      (Cone.lift DGModuleHom.id α f
        (by
          ext x
          simp [α]))
  refine ⟨(Cone.snd _).comp (Cochain.ofHom G) (zero_add 0), Cochain.ext fun x => ?_⟩
  have h1 := congrArg (fun φ => Cone.snd _ (φ x)) hG
  simpa [q] using h1


-- @@ L198-218 verbatim
/-- A K-projective and graded-projective dg module has the lifting property against surjective
quasi-isomorphisms: a graded lift `g₀` of `f` differs from a morphism by the cocycle `δ g₀` with
values in the (acyclic) kernel of the surjection, which is a coboundary. -/
theorem IsKProjective.hasLiftingProperty (hK : IsKProjective.{w} A P)
    (hG : IsGradedProjective.{w} A P) : HasLiftingProperty.{w} A P := by
  intro M N _ _ _ _ _ _ _ _ p hp hq f
  obtain ⟨g₀, hg₀⟩ := hG M N p hp (Cochain.ofHom f)
  have hpg : ∀ x, p (g₀ x) = f x := fun x => congrArg (fun c : Cochain A P N 0 => c x) hg₀
  have hmem : ∀ x, δ 0 1 g₀ x ∈ p.ker := fun x => by
    change p (δ 0 1 g₀ x) = 0
    rw [δ_zero_cochain_apply, map_sub, p.map_d, hpg, hpg, f.map_d, sub_self]
  have hc₁ : δ 1 2 (Cochain.codRestrict (δ 0 1 g₀) p.ker hmem) = 0 := Cochain.ext fun x =>
    Subtype.ext (by rw [Cochain.coe_δ_codRestrict, δ_δ]; rfl)
  obtain ⟨c₀, hc₀⟩ := (hK.isAcyclic_hom (p.isAcyclic_ker hp hq)).exists_δ_eq (zero_add 1) _ hc₁
  have hg : δ 0 1 (g₀ - (Cochain.ofHom p.ker.subtype).comp c₀ (zero_add 0)) = 0 := by
    ext x
    rw [δ_sub, δ_comp_ofHom, hc₀]
    simp
  refine ⟨Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hg), DGModuleHom.ext fun x => ?_⟩
  change p (g₀ x - (c₀ x : M)) = f x
  rw [map_sub, hpg, show p (c₀ x : M) = 0 from (c₀ x).2, sub_zero]


-- @@ L220-227 verbatim
/-- The lifting property against surjective quasi-isomorphisms is equivalent to being both
K-projective and graded-projective. In particular it implies K-projectivity, but not
conversely: a contractible dg module is K-projective, but it has the lifting property only if it
is graded-projective (e.g. over `A = ℤ` in degree `0`, the cone of the identity of `ℚ` is
contractible but does not have the lifting property, `ℚ` not being a projective `ℤ`-module). -/
theorem hasLiftingProperty_iff :
    HasLiftingProperty.{w} A P ↔ IsKProjective.{w} A P ∧ IsGradedProjective.{w} A P :=
  ⟨fun h => ⟨h.isKProjective, h.isGradedProjective⟩, fun h => h.1.hasLiftingProperty h.2⟩


-- @@ L229-229 verbatim
end Lifting


-- @@ L231-231 verbatim
/-! ### Graded projectivity of semi-free and finite-cell modules -/


-- @@ L233-233 verbatim
section GradedProjective


-- @@ L235-237 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]


-- @@ L239-248 expanded
omit [DGModule A P] [DGModule A Q] in
/-- A retract of a graded-projective dg module is graded-projective. -/
theorem IsGradedProjective.of_retract (hP : IsGradedProjective.{w} A P) (i : DGModuleHom A Q P)
    (r : DGModuleHom A P Q) (hri : r.comp i = DGModuleHom.id) : IsGradedProjective.{w} A Q :=
  by
  intro M N _ _ _ _ _ _ _ _ p hp f
  obtain ⟨g, hg⟩ := hP M N p hp (f.comp (Cochain.ofHom r) (zero_add 0))
  refine ⟨g.comp (Cochain.ofHom i) (zero_add 0), Cochain.ext fun x => ?_⟩
  have h := congrArg (fun c : Cochain A P N 0 => c (i x)) hg
  simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h ⊢
  rw [h, ← DGModuleHom.comp_apply, hri, DGModuleHom.id_apply]


-- @@ L250-267 expanded
omit [DGModule A Q] in
/-- An extension of graded-projective dg modules, split as graded modules, is
graded-projective. -/
theorem IsGradedProjective.of_gradedSplitting {F G : Type*} [AddCommGroup F] [DGAddCommGroup F]
    [Module A F] [DGModule A F] [AddCommGroup G] [DGAddCommGroup G] [Module A G] [DGModule A G]
    {i : DGModuleHom A F G} {p : DGModuleHom A G Q} (σ : GradedSplitting i p)
    (hF : IsGradedProjective.{w} A F) (hQ : IsGradedProjective.{w} A Q) :
    IsGradedProjective.{w} A G :=
  by
  intro M N _ _ _ _ _ _ _ _ q hq f
  obtain ⟨gF, hgF⟩ := hF M N q hq (f.comp (Cochain.ofHom i) (zero_add 0))
  obtain ⟨gQ, hgQ⟩ := hQ M N q hq (f.comp σ.s (zero_add 0))
  refine
    ⟨gF.comp σ.r (zero_add 0) + gQ.comp (Cochain.ofHom p) (zero_add 0), Cochain.ext fun x => ?_⟩
  have h1 := congrArg (fun c : Cochain A F N 0 => c (σ.r x)) hgF
  have h2 := congrArg (fun c : Cochain A Q N 0 => c (p x)) hgQ
  simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h1 h2
  simp only [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.add_apply, map_add, h1, h2]
  rw [← map_add, σ.i_r_add_s_p]


-- @@ L269-269 verbatim
variable [DGRing A]


-- @@ L271-271 verbatim
namespace SemiFreeFiltration


-- @@ L273-273 verbatim
variable (S : SemiFreeFiltration.{w'} A P)


-- @@ L275-301 verbatim
include S in
/-- Semi-free dg modules are graded-projective. -/
theorem isGradedProjective : IsGradedProjective.{w} A P := by
  intro M N _ _ _ _ _ _ _ _ p hp f
  obtain ⟨g, hg⟩ := Cochain.exists_of_filtration S.mono S.exists_mem
    (fun i => {g : Cochain A (S.F i) M 0 | (Cochain.ofHom p).comp g (zero_add 0) =
      f.comp (Cochain.ofHom (S.F i).subtype) (zero_add 0)})
    ⟨0, Cochain.ext fun x => by simp [S.eq_zero_of_mem_zero x x.2]⟩
    (fun i g hg => by
      obtain ⟨gQ, hgQ⟩ := Cochain.exists_lift_directSum_shift (S.deg i) p hp
        ((f.comp (Cochain.ofHom (S.F (i + 1)).subtype) (zero_add 0)).comp
          (S.gradedSplitting i).s (zero_add 0))
      refine ⟨g.comp (S.gradedSplitting i).r (zero_add 0) +
        gQ.comp (Cochain.ofHom (S.π i)) (zero_add 0), Cochain.ext fun x => ?_, fun x => ?_⟩
      · have h1 := congrArg (fun c : Cochain A (S.F i) N 0 => c ((S.gradedSplitting i).r x)) hg
        have h2 := congrArg (fun c : Cochain A _ N 0 => c (S.π i x)) hgQ
        have h3 := congrArg (fun y : S.F (i + 1) => (y : P))
          ((S.gradedSplitting i).i_r_add_s_p x)
        simp only [Cochain.comp_apply, Cochain.ofHom_apply, DGSubmodule.subtype_apply] at h1 h2
        simp only [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.add_apply, map_add, h1, h2,
          DGSubmodule.subtype_apply]
        simp only [DGSubmodule.coe_add, DGSubmodule.coe_inclusion_apply] at h3
        rw [← map_add, h3]
      · simp [(S.gradedSplitting i).r_i, (S.gradedSplitting i).p_i])
  refine ⟨g, Cochain.ext fun x => ?_⟩
  obtain ⟨i, hi⟩ := S.exists_mem x
  exact congrArg (fun c : Cochain A (S.F i) N 0 => c ⟨x, hi⟩) (hg i)


-- @@ L303-306 verbatim
include S in
/-- Semi-free dg modules have the lifting property against surjective quasi-isomorphisms. -/
theorem hasLiftingProperty : HasLiftingProperty.{w} A P :=
  S.isKProjective.hasLiftingProperty S.isGradedProjective


-- @@ L308-308 verbatim
end SemiFreeFiltration


-- @@ L310-310 verbatim
namespace FiniteCellFiltration


-- @@ L312-312 verbatim
variable (C : FiniteCellFiltration A P)


-- @@ L314-323 verbatim
theorem isGradedProjective_F {i : ℕ} (hi : i ≤ C.length) : IsGradedProjective.{w} A (C.F i) := by
  induction i with
  | zero =>
    intro M N _ _ _ _ _ _ _ _ p hp f
    refine ⟨0, Cochain.ext fun x => ?_⟩
    rw [show x = 0 from Subtype.ext (C.eq_zero_of_mem_zero x x.2), map_zero, map_zero]
  | succ i ih =>
    refine IsGradedProjective.of_gradedSplitting (C.gradedSplitting ⟨i, hi⟩) (ih (by omega)) ?_
    intro M N _ _ _ _ _ _ _ _ p hp f
    exact Cochain.exists_lift_shift_leftCorner _ p hp _ f


-- @@ L325-329 verbatim
include C in
/-- Finite-cell dg modules are graded-projective. -/
theorem isGradedProjective : IsGradedProjective.{w} A P :=
  (C.isGradedProjective_F le_rfl).of_retract (DGSubmodule.codRestrict DGModuleHom.id C.mem_length)
    (C.F C.length).subtype (DGSubmodule.subtype_comp_codRestrict _ _)


-- @@ L331-334 verbatim
include C in
/-- Finite-cell dg modules have the lifting property against surjective quasi-isomorphisms. -/
theorem hasLiftingProperty : HasLiftingProperty.{w} A P :=
  C.isKProjective.hasLiftingProperty C.isGradedProjective


-- @@ L336-336 verbatim
end FiniteCellFiltration


-- @@ L338-338 verbatim
end GradedProjective


-- @@ L340-340 verbatim
end DG
