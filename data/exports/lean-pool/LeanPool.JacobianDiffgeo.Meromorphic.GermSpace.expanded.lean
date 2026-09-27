/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import LeanPool.JacobianDiffgeo.Meromorphic.Predicates
import LeanPool.JacobianDiffgeo.Meromorphic.CodiscreteBridge
import LeanPool.JacobianDiffgeo.Surface.Identity
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L15-30 verbatim
/-!
# The germ space `MeroGermOn X U` and `ℳ X` (CC3, D1/D6)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.3, D1, D6).

* `Algebra ℂ (Filter.Germ l ℂ)` (Compat, upstreamable): built from the existing `Module ℂ`
  instance via `Algebra.ofModule`, no diamond.
* `meroGermSubalgebra X U : Subalgebra ℂ (Filter.Germ (codiscreteWithin U) ℂ)`: germs admitting a
  meromorphic representative on `U`. `MeroGermOn X U := meroGermSubalgebra X U` (as a type, via
  the `Subalgebra` coercion to `Type`); `ℳ X := MeroGermOn X Set.univ` (CC3's `ℳ(X)`, an
  `abbrev`, so all `MeroGermOn` API applies verbatim).
* `MeroGermOn.mk`, `mk_eq_mk`, `exists_rep`, `ind`; `mk_add/mk_mul/mk_neg/mk_smul/mk_zero/mk_one`,
  `algebraMap_mk`.
* `MeroGermOn.restrict (h : V ⊆ U) : MeroGermOn X U →ₐ[ℂ] MeroGermOn X V` (Čech's structure
  maps), with `restrict_mk`, `restrict_restrict`, `restrict_id`.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
open scoped ContDiff Manifold

-- @@ L35-35 verbatim
open Set Filter Topology


-- @@ L37-37 verbatim
namespace RS


-- @@ L39-39 verbatim
/-! ### Compat: `Algebra ℂ (Germ l ℂ)` -/


-- @@ L41-48 verbatim
noncomputable instance instAlgebraGerm {α : Type*} {l : Filter α} : Algebra ℂ (Filter.Germ l ℂ) :=
  Algebra.ofModule
    (fun r x y => Filter.Germ.inductionOn₂ x y fun f g => by
      rw [← Filter.Germ.coe_smul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul,
        ← Filter.Germ.coe_smul, smul_mul_assoc])
    (fun r x y => Filter.Germ.inductionOn₂ x y fun f g => by
      rw [← Filter.Germ.coe_smul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul,
        ← Filter.Germ.coe_smul, mul_smul_comm])


-- @@ L50-56 verbatim
@[simp] theorem Filter.Germ.algebraMap_apply {α : Type*} {l : Filter α} (c : ℂ) :
    algebraMap ℂ (Filter.Germ l ℂ) c = ((fun _ => c : α → ℂ) : Filter.Germ l ℂ) := by
  change c • (1 : Filter.Germ l ℂ) = _
  rw [← Filter.Germ.coe_one, ← Filter.Germ.coe_smul]
  congr 1
  funext a
  simp


-- @@ L58-58 verbatim
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

-- @@ L59-59 verbatim
variable {U V : Set X} {f g : X → ℂ}


-- @@ L61-61 verbatim
/-! ### The subalgebra and the type `MeroGermOn` -/


-- @@ L63-74 verbatim
variable (X) in
/-- Germs over `codiscreteWithin U` admitting a meromorphic representative. -/
noncomputable def meroGermSubalgebra (U : Set X) :
    Subalgebra ℂ (Filter.Germ (Filter.codiscreteWithin U) ℂ) where
  carrier := {γ | ∃ f, MeromorphicOnX f U ∧ γ = (f : Filter.Germ (codiscreteWithin U) ℂ)}
  mul_mem' := by
    rintro γ₁ γ₂ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, (Filter.Germ.coe_mul f g).symm⟩
  add_mem' := by
    rintro γ₁ γ₂ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, (Filter.Germ.coe_add f g).symm⟩
  algebraMap_mem' c := ⟨fun _ => c, meromorphicOnX_const c U, by simp⟩


-- @@ L76-78 verbatim
variable (X) in
/-- The space of meromorphic germ classes on `U` (CC3 relativized; junk-free). -/
def MeroGermOn (U : Set X) : Type _ := meroGermSubalgebra X U


-- @@ L80-82 verbatim
variable (X) in
/-- CC3 (frozen): the field of meromorphic functions, `ℳ X`. -/
abbrev Mero : Type _ := MeroGermOn X (Set.univ : Set X)


-- @@ L84-84 verbatim
@[inherit_doc] scoped notation "ℳ" => RS.Mero


-- @@ L86-87 verbatim
noncomputable instance : CommRing (MeroGermOn X U) :=
  inferInstanceAs (CommRing (meroGermSubalgebra X U))


-- @@ L89-90 verbatim
noncomputable instance : Algebra ℂ (MeroGermOn X U) :=
  inferInstanceAs (Algebra ℂ (meroGermSubalgebra X U))


-- @@ L92-93 verbatim
noncomputable instance : Module ℂ (MeroGermOn X U) :=
  inferInstanceAs (Module ℂ (meroGermSubalgebra X U))


-- @@ L95-98 verbatim
instance instNontrivialMero [Nonempty X] : Nontrivial (ℳ X) := by
  have _hnb : (codiscrete X).NeBot := instNeBotCodiscrete
  exact ⟨0, 1, fun h => (zero_ne_one (α := Filter.Germ (codiscrete X) ℂ))
    (congrArg Subtype.val h)⟩


-- @@ L100-100 verbatim
namespace MeroGermOn


-- @@ L102-104 verbatim
/-- Constructor: the class of a meromorphic function. -/
noncomputable def mk (f : X → ℂ) (hf : MeromorphicOnX f U) : MeroGermOn X U :=
  ⟨(f : Filter.Germ (codiscreteWithin U) ℂ), f, hf, rfl⟩


-- @@ L106-112 verbatim
theorem mk_eq_mk {f g : X → ℂ} {hf : MeromorphicOnX f U} {hg : MeromorphicOnX g U} :
    mk f hf = mk g hg ↔ f =ᶠ[codiscreteWithin U] g := by
  constructor
  · intro h
    exact Filter.Germ.coe_eq.1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Filter.Germ.coe_eq.2 h)


-- @@ L114-116 verbatim
theorem exists_rep (φ : MeroGermOn X U) : ∃ f, ∃ hf : MeromorphicOnX f U, mk f hf = φ := by
  obtain ⟨f, hf, hfeq⟩ := φ.2
  exact ⟨f, hf, Subtype.ext hfeq.symm⟩


-- @@ L118-122 verbatim
@[elab_as_elim]
theorem ind {motive : MeroGermOn X U → Prop} (h : ∀ f (hf : MeromorphicOnX f U), motive (mk f hf))
    (φ : MeroGermOn X U) : motive φ := by
  obtain ⟨f, hf, hfeq⟩ := exists_rep φ
  exact hfeq ▸ h f hf


-- @@ L124-126 verbatim
@[simp] theorem mk_add {f g : X → ℂ} {hf : MeromorphicOnX f U} {hg : MeromorphicOnX g U} :
    mk f hf + mk g hg = mk (f + g) (hf.add hg) :=
  Subtype.ext (Filter.Germ.coe_add f g).symm


-- @@ L128-130 verbatim
@[simp] theorem mk_mul {f g : X → ℂ} {hf : MeromorphicOnX f U} {hg : MeromorphicOnX g U} :
    mk f hf * mk g hg = mk (f * g) (hf.mul hg) :=
  Subtype.ext (Filter.Germ.coe_mul f g).symm


-- @@ L132-134 verbatim
@[simp] theorem mk_neg {f : X → ℂ} {hf : MeromorphicOnX f U} :
    -mk f hf = mk (-f) hf.neg :=
  Subtype.ext (Filter.Germ.coe_neg f).symm


-- @@ L136-140 verbatim
/-- `mk` turns subtraction into subtraction. Stated directly (rather than via `mk_neg`/`mk_add`)
because a rewrite chain through those cannot instantiate the proof-valued arguments. -/
@[simp] theorem mk_sub {f g : X → ℂ} {hf : MeromorphicOnX f U} {hg : MeromorphicOnX g U} :
    mk f hf - mk g hg = mk (f - g) (hf.sub hg) :=
  Subtype.ext (Filter.Germ.coe_sub f g).symm


-- @@ L142-144 verbatim
@[simp] theorem mk_smul (c : ℂ) {f : X → ℂ} {hf : MeromorphicOnX f U} :
    c • mk f hf = mk (c • f) (hf.smul c) :=
  Subtype.ext (Filter.Germ.coe_smul c f).symm


-- @@ L146-150 verbatim
@[simp] theorem mk_zero :
    (mk (fun _ : X => (0 : ℂ)) (meromorphicOnX_const 0 U) : MeroGermOn X U) = 0 := by
  apply Subtype.ext
  change ((fun _ : X => (0 : ℂ)) : Filter.Germ (codiscreteWithin U) ℂ) = 0
  exact Filter.Germ.coe_zero


-- @@ L152-156 verbatim
@[simp] theorem mk_one :
    (mk (fun _ : X => (1 : ℂ)) (meromorphicOnX_const 1 U) : MeroGermOn X U) = 1 := by
  apply Subtype.ext
  change ((fun _ : X => (1 : ℂ)) : Filter.Germ (codiscreteWithin U) ℂ) = 1
  exact Filter.Germ.coe_one


-- @@ L158-161 verbatim
theorem algebraMap_mk (c : ℂ) :
    algebraMap ℂ (MeroGermOn X U) c = mk (fun _ => c) (meromorphicOnX_const c U) := by
  apply Subtype.ext
  exact Filter.Germ.algebraMap_apply c


-- @@ L163-163 verbatim
end MeroGermOn


-- @@ L165-165 verbatim
/-! ### Restriction (Čech's structure maps) -/


-- @@ L167-172 verbatim
/-- The germ-level restriction map: pulling back a `codiscreteWithin U`-germ to a
`codiscreteWithin V`-germ, for `V ⊆ U`. Meromorphy-free. -/
noncomputable def restrictGerm (h : V ⊆ U) (γ : Filter.Germ (codiscreteWithin U) ℂ) :
    Filter.Germ (codiscreteWithin V) ℂ :=
  γ.liftOn (fun f => (f : Filter.Germ (codiscreteWithin V) ℂ))
    (fun _f _g hfg => Filter.Germ.coe_eq.2 (hfg.filter_mono (codiscreteWithin_mono h)))


-- @@ L174-177 verbatim
omit [ChartedSpace ℂ X] in
@[simp] theorem restrictGerm_coe (h : V ⊆ U) (f : X → ℂ) :
    restrictGerm h (f : Filter.Germ (codiscreteWithin U) ℂ) =
      (f : Filter.Germ (codiscreteWithin V) ℂ) := rfl


-- @@ L179-183 verbatim
omit [ChartedSpace ℂ X] in
theorem restrictGerm_add (h : V ⊆ U) (γ₁ γ₂ : Filter.Germ (codiscreteWithin U) ℂ) :
    restrictGerm h (γ₁ + γ₂) = restrictGerm h γ₁ + restrictGerm h γ₂ :=
  Filter.Germ.inductionOn₂ γ₁ γ₂ fun f g => by
    simp only [← Filter.Germ.coe_add, restrictGerm_coe]


-- @@ L185-189 verbatim
omit [ChartedSpace ℂ X] in
theorem restrictGerm_mul (h : V ⊆ U) (γ₁ γ₂ : Filter.Germ (codiscreteWithin U) ℂ) :
    restrictGerm h (γ₁ * γ₂) = restrictGerm h γ₁ * restrictGerm h γ₂ :=
  Filter.Germ.inductionOn₂ γ₁ γ₂ fun f g => by
    simp only [← Filter.Germ.coe_mul, restrictGerm_coe]


-- @@ L191-196 verbatim
omit [ChartedSpace ℂ X] in
theorem restrictGerm_one (h : V ⊆ U) :
    restrictGerm h (1 : Filter.Germ (codiscreteWithin U) ℂ) = 1 := by
  change restrictGerm h ((fun _ : X => (1 : ℂ)) : Filter.Germ (codiscreteWithin U) ℂ) = _
  rw [restrictGerm_coe]
  exact Filter.Germ.coe_one


-- @@ L198-203 verbatim
omit [ChartedSpace ℂ X] in
theorem restrictGerm_zero (h : V ⊆ U) :
    restrictGerm h (0 : Filter.Germ (codiscreteWithin U) ℂ) = 0 := by
  change restrictGerm h ((fun _ : X => (0 : ℂ)) : Filter.Germ (codiscreteWithin U) ℂ) = _
  rw [restrictGerm_coe]
  exact Filter.Germ.coe_zero


-- @@ L205-208 verbatim
theorem restrictGerm_mem (h : V ⊆ U) {γ : Filter.Germ (codiscreteWithin U) ℂ}
    (hγ : γ ∈ meroGermSubalgebra X U) : restrictGerm h γ ∈ meroGermSubalgebra X V := by
  obtain ⟨f, hf, rfl⟩ := hγ
  exact ⟨f, fun x hx => hf x (h hx), (restrictGerm_coe h f)⟩


-- @@ L210-210 verbatim
namespace MeroGermOn


-- @@ L212-223 verbatim
/-- Restriction to a smaller open set (Čech's structure maps). -/
noncomputable def restrict (h : V ⊆ U) : MeroGermOn X U →ₐ[ℂ] MeroGermOn X V where
  toFun φ := ⟨restrictGerm h φ.1, restrictGerm_mem h φ.2⟩
  map_one' := Subtype.ext (restrictGerm_one h)
  map_mul' φ ψ := Subtype.ext (restrictGerm_mul h φ.1 ψ.1)
  map_zero' := Subtype.ext (restrictGerm_zero h)
  map_add' φ ψ := Subtype.ext (restrictGerm_add h φ.1 ψ.1)
  commutes' c := by
    apply Subtype.ext
    change restrictGerm h (algebraMap ℂ (MeroGermOn X U) c).1 = (algebraMap ℂ (MeroGermOn X V) c).1
    rw [MeroGermOn.algebraMap_mk, MeroGermOn.algebraMap_mk]
    exact restrictGerm_coe h (fun _ => c)


-- @@ L225-227 verbatim
@[simp] theorem restrict_mk (h : V ⊆ U) {f : X → ℂ} {hf : MeromorphicOnX f U} :
    restrict h (mk f hf) = mk f (fun x hx => hf x (h hx)) :=
  Subtype.ext (restrictGerm_coe h f)


-- @@ L229-232 verbatim
theorem restrict_restrict {W : Set X} (h₁ : V ⊆ U) (h₂ : W ⊆ V) (φ : MeroGermOn X U) :
    restrict h₂ (restrict h₁ φ) = restrict (h₂.trans h₁) φ := by
  induction φ using ind with
  | h f hf => exact Subtype.ext (by simp only [restrict_mk]; rfl)


-- @@ L234-236 verbatim
theorem restrict_id (φ : MeroGermOn X U) : restrict (subset_refl U) φ = φ := by
  induction φ using ind with
  | h f hf => simp


-- @@ L238-238 verbatim
end MeroGermOn


-- @@ L240-248 verbatim
theorem algebraMap_injective [Nonempty X] : Function.Injective (algebraMap ℂ (ℳ X)) := by
  intro c d hcd
  have hcd' : (MeroGermOn.mk (fun _ : X => c) (meromorphicOnX_const c univ) :
      MeroGermOn X univ) = MeroGermOn.mk (fun _ : X => d) (meromorphicOnX_const d univ) := by
    rw [← MeroGermOn.algebraMap_mk, ← MeroGermOn.algebraMap_mk]; exact hcd
  have heq := MeroGermOn.mk_eq_mk.1 hcd'
  have heq2 := eventuallyEq_codiscrete_iff.mp heq (Classical.arbitrary X)
  obtain ⟨_, hcd2⟩ := heq2.exists
  exact hcd2


-- @@ L250-250 verbatim
end RS
