/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.Auxiliary.Adapted


-- @@ L10-55 verbatim
/-!

# Indistinguishable processes

We build a space of equivalence classes of processes, where two processes are treated as identical
if they are `Indistinguishable`. We form the set of equivalence classes under the relation of
being indistinguishable.
We consider equivalence classes of strongly adapted processes
(or, equivalently, of almost everywhere strongly adapted processes.)

## Notation

* `α →ₚ[μ, 𝓕] β`

## Main statements

* The linear structure of `L⁰` :
  Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
  `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₚ β` inherits the linear structure
  of `β`. For example, if `β` is a module, then `α →ₚ β` is a module over the same ring.

  See `mk_add_mk`, `neg_mk`, `mk_sub`, `smul_mk`,
  `coeFn_add`, `coeFn_neg`, `coeFn_sub`, `coeFn_smul`

* The order structure of `L⁰` :
  `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
  And `α →ₚ β` inherits the preorder and partial order of `β`.

  TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
  linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.cast`:      To find a representative of `f : α →ₚ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `AEEqProcess.mk`:  To construct an `L⁰` function `α →ₚ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`:        Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₚ γ` when `g` is
                 continuous. Use `compMeasurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`:       Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`

-/


-- @@ L57-57 verbatim
@[expose] public section


-- @@ L59-59 verbatim
noncomputable section


-- @@ L61-61 verbatim
open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function


-- @@ L63-64 verbatim
variable {ι α β γ δ : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  [Preorder ι] {𝓕 : Filtration ι mα}


-- @@ L66-66 verbatim
namespace MeasureTheory


-- @@ L68-68 verbatim
section MeasurableSpace


-- @@ L70-70 verbatim
variable [TopologicalSpace β]

-- @@ L71-71 verbatim
variable (𝓕 β)


-- @@ L73-79 expanded
/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[implicit_reducible]
def Measure.aeEqSetoid' (μ : Measure α) : Setoid { X : ι → α → β // AEStronglyAdapted X 𝓕 μ } :=
  ⟨fun f g => Indistinguishable μ f.1 g, fun {_} => .rfl, fun {_ _} => .symm, fun {_ _ _} => .trans⟩


-- @@ L81-81 verbatim
variable (α)


-- @@ L83-87 verbatim
/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
they differ on a set of measure `0`. -/
def AEEqProcess (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid' β 𝓕)


-- @@ L89-89 verbatim
variable {α β}


-- @@ L91-92 verbatim
@[inherit_doc MeasureTheory.AEEqProcess]
notation:25 α " →ₚ[" μ ", " 𝓕 "] " β => AEEqProcess α β 𝓕 μ


-- @@ L94-94 verbatim
end MeasurableSpace


-- @@ L96-96 verbatim
variable [TopologicalSpace δ]


-- @@ L98-98 verbatim
namespace AEEqProcess


-- @@ L100-100 verbatim
section

-- @@ L101-101 verbatim
variable [TopologicalSpace β]


-- @@ L103-107 expanded
/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [TopologicalSpace β] (f : ι → α → β) (hf : AEStronglyAdapted f 𝓕 μ) :
    AEEqProcess α β 𝓕 μ :=
  Quotient.mk'' ⟨f, hf⟩


-- @@ L109-117 expanded
open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
def cast (X : AEEqProcess α β 𝓕 μ) : ι → α → β :=
  if h : ∃ (c : β), X = mk (fun _ _ ↦ c) .const then fun _ _ ↦ h.choose
  else AEStronglyAdapted.mk _ (Quotient.out X : { f : ι → α → β // AEStronglyAdapted f 𝓕 μ }).2


-- @@ L119-120 expanded
/-- A measurable representative of an `AEEqProcess` [f] -/
instance instCoeFun : CoeFun (AEEqProcess α β 𝓕 μ) fun _ => ι → α → β :=
  ⟨cast⟩


-- @@ L122-126 expanded
protected lemma stronglyAdapted (f : AEEqProcess α β 𝓕 μ) : StronglyAdapted 𝓕 f :=
  by
  simp only [cast]
  split_ifs with h
  · exact stronglyAdapted_const 𝓕 _
  · apply AEStronglyAdapted.stronglyAdapted_mk


-- @@ L128-129 expanded
protected lemma aestronglyAdapted (f : AEEqProcess α β 𝓕 μ) : AEStronglyAdapted f 𝓕 μ :=
  f.stronglyAdapted.aestronglyAdapted


-- @@ L131-133 expanded
protected lemma adapted [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : AEEqProcess α β 𝓕 μ) : Adapted 𝓕 f :=
  f.stronglyAdapted.adapted


-- @@ L135-138 expanded
@[simp]
lemma quot_mk_eq_mk (f : ι → α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid' β 𝓕) ⟨f, hf⟩ : AEEqProcess α β 𝓕 μ) = mk f hf :=
  rfl


-- @@ L140-142 expanded
@[simp]
lemma mk_eq_mk {f g : ι → α → β} {hf hg} :
    (mk f hf : AEEqProcess α β 𝓕 μ) = mk g hg ↔ Indistinguishable μ f g :=
  Quotient.eq''


-- @@ L144-151 expanded
@[simp]
lemma mk_coeFn (f : AEEqProcess α β 𝓕 μ) : mk f f.aestronglyAdapted = f :=
  by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEStronglyAdapted.indist_mk _).symm


-- @@ L153-155 expanded
@[ext]
lemma ext {f g : AEEqProcess α β 𝓕 μ} (h : Indistinguishable μ f g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]


-- @@ L157-158 expanded
lemma coeFn_mk (f : ι → α → β) (hf) : Indistinguishable μ (mk f hf : AEEqProcess α β 𝓕 μ) f := by
  rw [← mk_eq_mk (hf := AEEqProcess.aestronglyAdapted ..) (hg := hf), mk_coeFn]


-- @@ L160-163 expanded
@[elab_as_elim]
lemma induction_on (f : AEEqProcess α β 𝓕 μ) {p : (AEEqProcess α β 𝓕 μ) → Prop}
    (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H


-- @@ L165-170 expanded
@[elab_as_elim]
lemma induction_on₂ {α' β' ι' : Type*} {mα' : MeasurableSpace α'} [TopologicalSpace β']
    {μ' : Measure α'} [Preorder ι'] {𝓕' : Filtration ι' mα'} (f : AEEqProcess α β 𝓕 μ)
    (f' : AEEqProcess α' β' 𝓕' μ') {p : (AEEqProcess α β 𝓕 μ) → (AEEqProcess α' β' 𝓕' μ') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf


-- @@ L172-180 expanded
@[elab_as_elim]
lemma induction_on₃ {α' β' ι' : Type*} {mα' : MeasurableSpace α'} [TopologicalSpace β']
    {μ' : Measure α'} [Preorder ι'] {𝓕' : Filtration ι' mα'} {α'' β'' ι'' : Type*}
    {mα'' : MeasurableSpace α''} [TopologicalSpace β''] {μ'' : Measure α''} [Preorder ι'']
    {𝓕'' : Filtration ι'' mα''} (f : AEEqProcess α β 𝓕 μ) (f' : AEEqProcess α' β' 𝓕' μ')
    (f'' : AEEqProcess α'' β'' 𝓕'' μ'')
    {p : (AEEqProcess α β 𝓕 μ) → (AEEqProcess α' β' 𝓕' μ') → (AEEqProcess α'' β'' 𝓕'' μ'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf


-- @@ L182-182 verbatim
end


-- @@ L184-184 verbatim
variable [TopologicalSpace β] [TopologicalSpace γ]


-- @@ L186-191 expanded
/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₚ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₚ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : AEEqProcess α β 𝓕 μ) : AEEqProcess α γ 𝓕 μ :=
  Quotient.liftOn' f (fun f => mk (fun t ↦ g ∘ (f.1 t)) (hg.comp_aestronglyAdapted f.2))
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g


-- @@ L193-196 expanded
@[simp]
lemma comp_mk (g : β → γ) (hg : Continuous g) (f : ι → α → β) (hf) :
    comp g hg (mk f hf : AEEqProcess α β 𝓕 μ) =
      mk (fun t ↦ g ∘ (f t)) (hg.comp_aestronglyAdapted hf) :=
  rfl


-- @@ L198-200 expanded
@[simp]
lemma comp_id (f : AEEqProcess α β 𝓕 μ) : comp id (continuous_id) f = f := by rcases f; rfl


-- @@ L202-205 expanded
@[simp]
lemma comp_comp (g : γ → δ) (g' : β → γ) (hg : Continuous g) (hg' : Continuous g')
    (f : AEEqProcess α β 𝓕 μ) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  rcases f; rfl


-- @@ L207-209 expanded
lemma comp_eq_mk (g : β → γ) (hg : Continuous g) (f : AEEqProcess α β 𝓕 μ) :
    comp g hg f = mk (fun t ↦ g ∘ (f t)) (hg.comp_aestronglyAdapted f.aestronglyAdapted) := by
  rw [← comp_mk g hg f f.aestronglyAdapted, mk_coeFn]


-- @@ L211-214 expanded
lemma coeFn_comp (g : β → γ) (hg : Continuous g) (f : AEEqProcess α β 𝓕 μ) :
    Indistinguishable μ (comp g hg f) (fun t ↦ g ∘ (f t)) :=
  by
  rw [comp_eq_mk]
  apply coeFn_mk


-- @@ L216-219 expanded
/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : AEEqProcess α β 𝓕 μ) (g : AEEqProcess α γ 𝓕 μ) : AEEqProcess α (β × γ) 𝓕 μ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun t ω => (f.1 t ω, g.1 t ω)) (f.2.prodMk g.2))
    fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 <| Hf.prodMk Hg


-- @@ L221-224 expanded
@[simp]
lemma pair_mk_mk (f : ι → α → β) (hf) (g : ι → α → γ) (hg) :
    (mk f hf : AEEqProcess α β 𝓕 μ).pair (mk g hg) =
      mk (fun t ω => (f t ω, g t ω)) (hf.prodMk hg) :=
  rfl


-- @@ L226-229 expanded
lemma pair_eq_mk (f : AEEqProcess α β 𝓕 μ) (g : AEEqProcess α γ 𝓕 μ) :
    f.pair g = mk (fun t ω => (f t ω, g t ω)) (f.aestronglyAdapted.prodMk g.aestronglyAdapted) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyAdapted, g.aestronglyAdapted]


-- @@ L231-234 expanded
lemma coeFn_pair (f : AEEqProcess α β 𝓕 μ) (g : AEEqProcess α γ 𝓕 μ) :
    Indistinguishable μ (f.pair g) fun t ω => (f t ω, g t ω) :=
  by
  rw [pair_eq_mk]
  apply coeFn_mk


-- @@ L236-242 expanded
/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₚ β` and `[f₂] : α →ₚ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₚ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : AEEqProcess α β 𝓕 μ)
    (f₂ : AEEqProcess α γ 𝓕 μ) : AEEqProcess α δ 𝓕 μ :=
  comp _ hg (f₁.pair f₂)


-- @@ L244-249 expanded
@[simp]
lemma comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : ι → α → β) (f₂ : ι → α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : AEEqProcess α β 𝓕 μ) (mk f₂ hf₂) =
      mk (fun t ω => g (f₁ t ω) (f₂ t ω)) (hg.comp_aestronglyAdapted (hf₁.prodMk hf₂)) :=
  rfl


-- @@ L251-253 expanded
lemma comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : AEEqProcess α β 𝓕 μ)
    (f₂ : AEEqProcess α γ 𝓕 μ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl


-- @@ L255-258 expanded
lemma comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : AEEqProcess α β 𝓕 μ)
    (f₂ : AEEqProcess α γ 𝓕 μ) :
    comp₂ g hg f₁ f₂ =
      mk (fun t ω => g (f₁ t ω) (f₂ t ω))
        (hg.comp_aestronglyAdapted (f₁.aestronglyAdapted.prodMk f₂.aestronglyAdapted)) :=
  by rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; rfl


-- @@ L260-263 expanded
lemma coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : AEEqProcess α β 𝓕 μ)
    (f₂ : AEEqProcess α γ 𝓕 μ) :
    Indistinguishable μ (comp₂ g hg f₁ f₂) fun t ω => g (f₁ t ω) (f₂ t ω) :=
  by
  rw [comp₂_eq_mk]
  apply coeFn_mk


-- @@ L265-269 expanded
/-- Interpret `f : α →ₚ[μ, 𝓕] β` as a germ at `ae μ` forgetting that `f` is almost everywhere
strongly measurable. -/
def toGerm (f : AEEqProcess α β 𝓕 μ) : Germ (ae μ) (ι → β) :=
  Quotient.liftOn' f (fun f => (fun ω t ↦ f.1 t ω : Germ (ae μ) (ι → β))) fun _ _ H =>
    Germ.coe_eq.2 H.ae_eq


-- @@ L271-273 expanded
@[simp]
lemma mk_toGerm (f : ι → α → β) (hf) : (mk f hf : AEEqProcess α β 𝓕 μ).toGerm = (fun ω t ↦ f t ω) :=
  rfl


-- @@ L275-276 expanded
lemma toGerm_eq (f : AEEqProcess α β 𝓕 μ) : f.toGerm = (fun ω t ↦ f t ω) := by
  rw [← mk_toGerm f f.aestronglyAdapted, mk_coeFn]


-- @@ L278-279 expanded
lemma toGerm_injective : Injective (toGerm : (AEEqProcess α β 𝓕 μ) → Germ (ae μ) (ι → β)) :=
  fun f g H => ext <| EventuallyEq.indist <| Germ.coe_eq.1 <| by rwa [← toGerm_eq, ← toGerm_eq]


-- @@ L281-285 expanded
lemma comp_toGerm (g : β → γ) (hg : Continuous g) (f : AEEqProcess α β 𝓕 μ) :
    (comp g hg f).toGerm = f.toGerm.map (fun f t ↦ g (f t)) :=
  induction_on f fun f _ =>
    by
    simp only [comp_mk, mk_toGerm, comp_apply, Germ.map_coe, Germ.coe_eq]
    exact ae_of_all _ (by simp)


-- @@ L287-290 expanded
lemma comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : AEEqProcess α β 𝓕 μ)
    (f₂ : AEEqProcess α γ 𝓕 μ) :
    (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ (fun f h t ↦ g (f t) (h t)) f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp; rfl


-- @@ L292-295 expanded
/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
for almost all `a` -/
def LiftPred (p : (ι → β) → Prop) (f : AEEqProcess α β 𝓕 μ) : Prop :=
  f.toGerm.LiftPred p


-- @@ L297-300 expanded
/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
`(f a, g a)` for almost all `a` -/
def LiftRel (r : (ι → β) → (ι → γ) → Prop) (f : AEEqProcess α β 𝓕 μ) (g : AEEqProcess α γ 𝓕 μ) :
    Prop :=
  f.toGerm.LiftRel r g.toGerm


-- @@ L302-304 expanded
lemma liftRel_mk_mk {r : (ι → β) → (ι → γ) → Prop} {f : ι → α → β} {g : ι → α → γ} {hf hg} :
    LiftRel r (mk f hf : AEEqProcess α β 𝓕 μ) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f · a) (g · a) :=
  Iff.rfl


-- @@ L306-309 expanded
lemma liftRel_iff_coeFn {r : (ι → β) → (ι → γ) → Prop} {f : AEEqProcess α β 𝓕 μ}
    {g : AEEqProcess α γ 𝓕 μ} : LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f · a) (g · a) := by
  rw [← liftRel_mk_mk (hf := f.aestronglyAdapted) (hg := g.aestronglyAdapted), mk_coeFn, mk_coeFn]


-- @@ L311-311 verbatim
variable (α)


-- @@ L313-316 expanded
/-- The equivalence class of a constant function: `[fun _ : α => b]`, based on the equivalence
relation of being almost everywhere equal -/
def const (b : β) : AEEqProcess α β 𝓕 μ :=
  mk (fun _ _ ↦ b) .const


-- @@ L318-319 expanded
lemma coeFn_const (b : β) : Indistinguishable μ (const α b : AEEqProcess α β 𝓕 μ) (fun _ _ ↦ b) :=
  coeFn_mk _ _


-- @@ L321-331 expanded
/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
@[simp]
lemma coeFn_const_eq [NeZero μ] (b : β) (t : ι) (x : α) :
    (const α b : AEEqProcess α β 𝓕 μ) t x = b :=
  by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := h.choose_spec
  set b := h.choose with hb
  simp_rw [const, mk_eq_mk, ProbabilityTheory.Indistinguishable] at this
  have ⟨_, h1⟩ := Eventually.exists this
  rw [h1 t]


-- @@ L333-337 expanded
lemma coeFn_const_eq' (b : β) :
    ∃ b', ((const α b : AEEqProcess α β 𝓕 μ) : ι → α → β) = fun _ ↦ b' :=
  by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨fun _ ↦ h.choose, by ext; simp⟩


-- @@ L339-339 verbatim
variable {α}


-- @@ L341-342 expanded
instance instInhabited [Inhabited β] : Inhabited (AEEqProcess α β 𝓕 μ) :=
  ⟨const α default⟩


-- @@ L344-346 expanded
@[to_additive]
instance instOne [One β] : One (AEEqProcess α β 𝓕 μ) :=
  ⟨const α 1⟩


-- @@ L348-350 expanded
@[to_additive]
lemma one_def [One β] : (1 : AEEqProcess α β 𝓕 μ) = mk (fun _ _ => 1) .const :=
  rfl


-- @@ L352-354 expanded
@[to_additive]
lemma coeFn_one [One β] : Indistinguishable μ (⇑(1 : AEEqProcess α β 𝓕 μ)) 1 :=
  coeFn_const ..


-- @@ L356-358 expanded
@[to_additive (attr := simp)]
lemma coeFn_one_eq [NeZero μ] [One β] {t : ι} {x : α} : (1 : AEEqProcess α β 𝓕 μ) t x = 1 :=
  coeFn_const_eq ..


-- @@ L360-365 expanded
@[to_additive (attr := simp)]
lemma one_toGerm [One β] : (1 : AEEqProcess α β 𝓕 μ).toGerm = 1 :=
  rfl


-- @@ L366-366 verbatim
section SMul


-- @@ L368-368 verbatim
variable {𝕜 𝕜' : Type*}

-- @@ L369-369 verbatim
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]

-- @@ L370-370 verbatim
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]


-- @@ L372-373 expanded
instance instSMul : SMul 𝕜 (AEEqProcess α γ 𝓕 μ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩


-- @@ L375-378 expanded
@[simp]
lemma smul_mk (c : 𝕜) (f : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) :
    c • (mk f hf : AEEqProcess α γ 𝓕 μ) = mk (c • f) hf.const_smul :=
  rfl


-- @@ L380-381 expanded
lemma coeFn_smul (c : 𝕜) (f : AEEqProcess α γ 𝓕 μ) : Indistinguishable μ (⇑(c • f)) (c • ⇑f) :=
  coeFn_comp _ _ _


-- @@ L383-384 expanded
lemma smul_toGerm (c : 𝕜) (f : AEEqProcess α γ 𝓕 μ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _


-- @@ L386-387 expanded
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (AEEqProcess α γ 𝓕 μ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩


-- @@ L389-390 expanded
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] :
    IsScalarTower 𝕜 𝕜' (AEEqProcess α γ 𝓕 μ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩


-- @@ L392-394 expanded
instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] :
    IsCentralScalar 𝕜 (AEEqProcess α γ 𝓕 μ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩


-- @@ L396-396 verbatim
end SMul


-- @@ L398-398 verbatim
section Mul


-- @@ L400-400 verbatim
variable [Mul γ] [ContinuousMul γ]


-- @@ L402-404 expanded
@[to_additive]
instance instMul : Mul (AEEqProcess α γ 𝓕 μ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩


-- @@ L406-409 expanded
@[to_additive (attr := simp)]
lemma mk_mul_mk (f g : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) (hg : AEStronglyAdapted g 𝓕 μ) :
    (mk f hf : AEEqProcess α γ 𝓕 μ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl


-- @@ L411-413 expanded
@[to_additive]
lemma coeFn_mul (f g : AEEqProcess α γ 𝓕 μ) : Indistinguishable μ (⇑(f * g)) (f * g) :=
  coeFn_comp₂ _ _ _ _


-- @@ L415-417 expanded
@[to_additive (attr := simp)]
lemma mul_toGerm (f g : AEEqProcess α γ 𝓕 μ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _


-- @@ L419-419 verbatim
end Mul


-- @@ L421-422 expanded
instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _


-- @@ L424-425 expanded
instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] :
    AddCommMonoid (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _


-- @@ L427-427 verbatim
section Monoid


-- @@ L429-429 verbatim
variable [Monoid γ] [ContinuousMul γ]


-- @@ L431-432 expanded
instance instPowNat : Pow (AEEqProcess α γ 𝓕 μ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩


-- @@ L434-438 expanded
@[simp]
lemma mk_pow (f : ι → α → γ) (hf) (n : ℕ) :
    (mk f hf : AEEqProcess α γ 𝓕 μ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyAdapted hf) :=
  rfl


-- @@ L440-441 expanded
lemma coeFn_pow (f : AEEqProcess α γ 𝓕 μ) (n : ℕ) : Indistinguishable μ (⇑(f ^ n)) ((⇑f) ^ n) :=
  coeFn_comp _ _ _


-- @@ L443-445 expanded
@[simp]
lemma pow_toGerm (f : AEEqProcess α γ 𝓕 μ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _


-- @@ L447-449 expanded
@[to_additive existing]
instance instMonoid : Monoid (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm


-- @@ L451-456 expanded
/-- `AEEqProcess.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `AEEqProcess.toGerm` as an `AddMonoidHom`. -/
    ]
def toGermMonoidHom : (AEEqProcess α γ 𝓕 μ) →* (ae μ).Germ (ι → γ)
    where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm


-- @@ L458-458 verbatim
end Monoid


-- @@ L460-462 expanded
@[to_additive existing]
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm


-- @@ L464-473 expanded
@[to_additive]
lemma coeFn_finsetProd [CommMonoid γ] [ContinuousMul γ] {η : Type*} (s : Finset η)
    (f : η → AEEqProcess α γ 𝓕 μ) : Indistinguishable μ (⇑(∏ i ∈ s, f i)) (∏ i ∈ s, ⇑(f i)) := by
  classical
    induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]


-- @@ L475-480 expanded
@[to_additive]
lemma coeFn_fun_finsetProd [CommMonoid γ] [ContinuousMul γ] {ι : Type*} (s : Finset ι)
    (f : ι → AEEqProcess α γ 𝓕 μ) : Indistinguishable μ ⇑(∏ i ∈ s, f i) fun x ↦ ∏ i ∈ s, f i x :=
  by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp


-- @@ L482-482 verbatim
section Group


-- @@ L484-484 verbatim
variable [Group γ] [IsTopologicalGroup γ]


-- @@ L486-486 verbatim
section Inv


-- @@ L488-490 expanded
@[to_additive]
instance instInv : Inv (AEEqProcess α γ 𝓕 μ) :=
  ⟨comp Inv.inv continuous_inv⟩


-- @@ L492-494 expanded
@[to_additive (attr := simp)]
lemma inv_mk (f : ι → α → γ) (hf) : (mk f hf : AEEqProcess α γ 𝓕 μ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl


-- @@ L496-498 expanded
@[to_additive]
lemma coeFn_inv (f : AEEqProcess α γ 𝓕 μ) : Indistinguishable μ (⇑f⁻¹) f⁻¹ :=
  coeFn_comp _ _ _


-- @@ L500-502 expanded
@[to_additive]
lemma inv_toGerm (f : AEEqProcess α γ 𝓕 μ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _


-- @@ L504-504 verbatim
end Inv


-- @@ L506-506 verbatim
section Div


-- @@ L508-510 expanded
@[to_additive]
instance instDiv : Div (AEEqProcess α γ 𝓕 μ) :=
  ⟨comp₂ Div.div continuous_div'⟩


-- @@ L512-515 expanded
@[to_additive (attr := simp)]
lemma mk_div (f g : ι → α → γ) (hf : AEStronglyAdapted f 𝓕 μ) (hg : AEStronglyAdapted g 𝓕 μ) :
    mk (f / g) (hf.div' hg) = (mk f hf : AEEqProcess α γ 𝓕 μ) / mk g hg :=
  rfl


-- @@ L517-519 expanded
@[to_additive]
lemma coeFn_div (f g : AEEqProcess α γ 𝓕 μ) : Indistinguishable μ (⇑(f / g)) (f / g) :=
  coeFn_comp₂ _ _ _ _


-- @@ L521-523 expanded
@[to_additive]
lemma div_toGerm (f g : AEEqProcess α γ 𝓕 μ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _


-- @@ L525-525 verbatim
end Div


-- @@ L527-527 verbatim
section ZPow


-- @@ L529-530 expanded
instance instPowInt : Pow (AEEqProcess α γ 𝓕 μ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩


-- @@ L532-535 expanded
@[simp]
lemma mk_zpow (f : ι → α → γ) (hf) (n : ℤ) :
    (mk f hf : AEEqProcess α γ 𝓕 μ) ^ n =
      mk (f ^ n) ((continuous_zpow n).comp_aestronglyAdapted hf) :=
  rfl


-- @@ L537-538 expanded
lemma coeFn_zpow (f : AEEqProcess α γ 𝓕 μ) (n : ℤ) : Indistinguishable μ (⇑(f ^ n)) ((⇑f) ^ n) :=
  coeFn_comp _ _ _


-- @@ L540-542 expanded
@[simp]
lemma zpow_toGerm (f : AEEqProcess α γ 𝓕 μ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _


-- @@ L544-544 verbatim
end ZPow


-- @@ L546-546 verbatim
end Group


-- @@ L548-550 expanded
instance instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _


-- @@ L552-554 expanded
instance instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] :
    AddCommGroup (AEEqProcess α γ 𝓕 μ) :=
  { add_comm := add_comm }


-- @@ L556-558 expanded
@[to_additive existing]
instance instGroup [Group γ] [IsTopologicalGroup γ] : Group (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm


-- @@ L560-562 expanded
@[to_additive existing]
instance instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (AEEqProcess α γ 𝓕 μ) :=
  { mul_comm := mul_comm }


-- @@ L564-564 verbatim
section Module


-- @@ L566-566 verbatim
variable {𝕜 : Type*}


-- @@ L568-570 expanded
instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.mulAction toGerm smul_toGerm


-- @@ L572-575 expanded
instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (AEEqProcess α γ 𝓕 μ) →+ _) fun c : 𝕜 =>
    smul_toGerm c


-- @@ L577-579 expanded
instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (AEEqProcess α γ 𝓕 μ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (AEEqProcess α γ 𝓕 μ) →+ _) smul_toGerm


-- @@ L581-581 verbatim
end Module


-- @@ L583-583 verbatim
open ENNReal


-- @@ L585-585 verbatim
section Star


-- @@ L587-587 verbatim
variable {R : Type*} [TopologicalSpace R]


-- @@ L589-590 expanded
instance [Star R] [ContinuousStar R] : Star (AEEqProcess α R 𝓕 μ) where
  star f := (AEEqProcess.comp _ continuous_star f)


-- @@ L592-594 expanded
lemma coeFn_star [Star R] [ContinuousStar R] (f : AEEqProcess α R 𝓕 μ) :
    Indistinguishable μ ↑(star f) (star f : ι → α → R) :=
  coeFn_comp _ (continuous_star) f


-- @@ L596-597 expanded
instance [InvolutiveStar R] [ContinuousStar R] : InvolutiveStar (AEEqProcess α R 𝓕 μ) where
  star_involutive f := comp_comp _ _ _ _ f |>.trans <| by simp [star_involutive.comp_self]


-- @@ L599-600 expanded
instance [Star R] [TrivialStar R] [ContinuousStar R] : TrivialStar (AEEqProcess α R 𝓕 μ) where
  star_trivial f := show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]


-- @@ L602-602 verbatim
end Star


-- @@ L604-604 verbatim
end AEEqProcess


-- @@ L606-606 verbatim
end MeasureTheory
