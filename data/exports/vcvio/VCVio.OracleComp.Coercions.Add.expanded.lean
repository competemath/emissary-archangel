/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.ProbComp


-- @@ L11-21 verbatim
/-!
# Coercing Computations to Larger Oracle Sets

This file defines `SubSpec` instances for oracle specs constructed with
either `OracleSpec.add` or `OracleSpec.sigma`. Each instance spells out the
`monadLift` action explicitly (rather than letting it default from
`onQuery` / `onResponse`) so that the lifted query reduces fully under
`isDefEq`. This is load-bearing for `rw` / `simp` lemmas like
`probEvent_liftComp` to find their pattern through the synthesized
`MonadLiftT` instance chain.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-28 verbatim
open OracleSpec

/- Lean 4.33 checks the `PFunctor.Obj`/dependent-pair conversion at implicit transparency
while normalizing nested lifted queries. -/

-- @@ L29-29 verbatim
attribute [local implicit_reducible] PFunctor.Obj


-- @@ L31-31 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L33-33 verbatim
namespace OracleQuery


-- @@ L35-35 verbatim
universe u v w


-- @@ L37-39 verbatim
variable {ι₁} {ι₂} {ι₃} {ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {α β γ : Type u}


-- @@ L41-41 verbatim
section instances


-- @@ L43-49 expanded
/-- We need `Inhabited` to prevent infinite type-class searching. -/
instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    SubSpec OracleSpec.emptySpec.{u, v} spec
    where
  monadLift q := PEmpty.elim q.input
  onQuery t := t.elim
  onResponse t := t.elim
  liftM_eq_lift q := PEmpty.elim q.input


-- @@ L51-53 expanded
instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    LawfulSubSpec OracleSpec.emptySpec spec where onResponse_bijective t := PEmpty.elim t


-- @@ L55-55 verbatim
section add_left


-- @@ L57-61 expanded
/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_add_left : SubSpec spec₁ (spec₁ + spec₂)
    where
  monadLift q := ⟨.inl q.input, q.cont⟩
  onQuery := Sum.inl
  onResponse _ := id


-- @@ L63-64 verbatim
@[simp] lemma liftM_add_left_def (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inl q.input) q.cont := rfl


-- @@ L66-67 expanded
@[simp high]
lemma liftM_add_left_query (t : spec₁.Domain) :
    (liftM (OracleSpec.query t) : OracleQuery (spec₁ + spec₂) (spec₁.Range t)) =
      OracleSpec.query (Sum.inl t) :=
  rfl


-- @@ L69-70 expanded
instance lawfulSubSpec_add_left : LawfulSubSpec spec₁ (spec₁ + spec₂) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L72-72 verbatim
end add_left


-- @@ L74-74 verbatim
section add_right


-- @@ L76-80 expanded
/-- Add additional oracles to the left side of the exiting ones. -/
instance subSpec_add_right : SubSpec spec₂ (spec₁ + spec₂)
    where
  monadLift q := ⟨.inr q.input, q.cont⟩
  onQuery := Sum.inr
  onResponse _ := id


-- @@ L82-83 verbatim
@[simp] lemma liftM_add_right_def (q : OracleQuery spec₂ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inr q.input) q.cont := rfl


-- @@ L85-86 expanded
@[simp high]
lemma liftM_add_right_query (t : spec₂.Domain) :
    (liftM (OracleSpec.query t) : OracleQuery (spec₁ + spec₂) (spec₂.Range t)) =
      OracleSpec.query (Sum.inr t) :=
  rfl


-- @@ L88-89 expanded
instance lawfulSubSpec_add_right : LawfulSubSpec spec₂ (spec₁ + spec₂) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L91-93 verbatim
instance disjointSubSpec_add_left_right :
    OracleSpec.DisjointSubSpec spec₁ spec₂ (spec₁ + spec₂) where
  disjoint_onQuery _ _ := by rintro ⟨⟩


-- @@ L95-97 verbatim
instance disjointSubSpec_add_right_left :
    OracleSpec.DisjointSubSpec spec₂ spec₁ (spec₁ + spec₂) where
  disjoint_onQuery _ _ := by rintro ⟨⟩


-- @@ L99-99 verbatim
end add_right


-- @@ L101-101 verbatim
section left_add_left_add


-- @@ L103-122 expanded
/-- Congruence on the left summand: an inclusion `spec₁ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₃ + spec₂`.

Low priority so that searches whose source spec is a metavariable (notably the
`MonadLiftT (OracleComp spec) (OracleComp superSpec)` chain behind whole-computation
coercions) prefer the direct embeddings `subSpec_add_left` / `subSpec_add_right`. This keeps
such coercions a single `liftComp`, definitionally, instead of a stack of lifts through an
intermediate spec. -/
instance (priority := low) subSpec_left_add_left_add_of_subSpec [h : SubSpec spec₁ spec₃] :
    SubSpec (spec₁ + spec₂) (spec₃ + spec₂)
    where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (h.onQuery t), f ∘ h.onResponse t⟩
    | ⟨.inr t, f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (h.onQuery t)
    | .inr t => .inr t
  onResponse
    | .inl t => h.onResponse t
    | .inr _ => id
  liftM_eq_lift q := by rcases q with ⟨_ | _, _⟩ <;> rfl


-- @@ L124-134 expanded
@[simp]
lemma liftM_left_add_left_add_def [h : SubSpec spec₁ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₃ + spec₂) α) =
      match q with
      | .mk (.inl q) f => liftM ((liftM (OracleQuery.mk q f) : OracleQuery spec₃ _))
      | .mk (.inr q) f => .mk (.inr q) f :=
  by
  rcases q with ⟨t | t, f⟩
  · change _ = liftM (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _)
    rw [show (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _) = ⟨h.onQuery t, f ∘ h.onResponse t⟩
        from h.liftM_eq_lift _]
    rfl
  · rfl


-- @@ L136-143 expanded
@[simp high]
lemma liftM_left_add_left_add_query [h : SubSpec spec₁ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (OracleSpec.query t) : OracleQuery (spec₃ + spec₂) ((spec₁ + spec₂).Range t)) =
      match t with
      | .inl t => liftM (liftM (OracleSpec.query t) : OracleQuery spec₃ _)
      | .inr t => OracleSpec.query (Sum.inr t) :=
  by
  rw [liftM_left_add_left_add_def]
  rcases t with t | t <;> rfl


-- @@ L145-152 expanded
instance lawfulSubSpec_left_add_left_add [SubSpec spec₁ spec₃] [LawfulSubSpec spec₁ spec₃] :
    LawfulSubSpec (spec₁ + spec₂) (spec₃ + spec₂) where
  onResponse_bijective
    t := by
    match t with
    | .inl t =>
      exact OracleSpec.LawfulSubSpec.onResponse_bijective (spec := spec₁) (superSpec := spec₃) t
    | .inr _ => exact Function.bijective_id


-- @@ L154-154 verbatim
end left_add_left_add


-- @@ L156-156 verbatim
section right_add_right_add


-- @@ L158-175 expanded
/-- Congruence on the right summand: an inclusion `spec₂ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₁ + spec₃`.

Low priority for the same reason as `subSpec_left_add_left_add_of_subSpec`: the direct
embeddings must win metavariable-headed searches so that whole-computation coercions stay a
single `liftComp`. -/
instance (priority := low) subSpec_right_add_right_add_of_subSpec [h : SubSpec spec₂ spec₃] :
    SubSpec (spec₁ + spec₂) (spec₁ + spec₃)
    where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl t, f⟩
    | ⟨.inr t, f⟩ => ⟨.inr (h.onQuery t), f ∘ h.onResponse t⟩
  onQuery
    | .inl t => .inl t
    | .inr t => .inr (h.onQuery t)
  onResponse
    | .inl _ => id
    | .inr t => h.onResponse t
  liftM_eq_lift q := by rcases q with ⟨_ | _, _⟩ <;> rfl


-- @@ L177-187 expanded
@[simp]
lemma liftM_right_add_right_add_def [h : SubSpec spec₂ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₁ + spec₃) α) =
      match q with
      | .mk (.inl q) f => .mk (.inl q) f
      | .mk (.inr q) f => (liftM (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) :=
  by
  rcases q with ⟨t | t, f⟩
  · rfl
  · change _ = liftM (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _)
    rw [show (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _) = ⟨h.onQuery t, f ∘ h.onResponse t⟩
        from h.liftM_eq_lift _]
    rfl


-- @@ L189-196 expanded
@[simp high]
lemma liftM_right_add_right_add_query [h : SubSpec spec₂ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (OracleSpec.query t) : OracleQuery (spec₁ + spec₃) ((spec₁ + spec₂).Range t)) =
      match t with
      | .inl t => OracleSpec.query (Sum.inl t)
      | .inr t => liftM (liftM (OracleSpec.query t) : OracleQuery spec₃ _) :=
  by
  rw [liftM_right_add_right_add_def]
  rcases t with t | t <;> rfl


-- @@ L198-205 expanded
instance lawfulSubSpec_right_add_right_add [SubSpec spec₂ spec₃] [LawfulSubSpec spec₂ spec₃] :
    LawfulSubSpec (spec₁ + spec₂) (spec₁ + spec₃) where
  onResponse_bijective
    t := by
    match t with
    | .inl _ => exact Function.bijective_id
    | .inr t =>
      exact OracleSpec.LawfulSubSpec.onResponse_bijective (spec := spec₂) (superSpec := spec₃) t


-- @@ L207-207 verbatim
end right_add_right_add


-- @@ L209-209 verbatim
section add_assoc


-- @@ L211-224 expanded
instance subSpec_add_assoc : SubSpec (spec₁ + (spec₂ + spec₃)) (spec₁ + spec₂ + spec₃)
    where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (.inl t)
    | .inr (.inl t) => .inl (.inr t)
    | .inr (.inr t) => .inr t
  onResponse
    | .inl _ => id
    | .inr (.inl _) => id
    | .inr (.inr _) => id
  liftM_eq_lift q := by rcases q with ⟨_ | _ | _, _⟩ <;> rfl


-- @@ L226-232 verbatim
@[simp] lemma liftM_add_assoc_def (q : OracleQuery (spec₁ + (spec₂ + spec₃)) α) :
    (liftM q : OracleQuery (spec₁ + spec₂ + spec₃) α) =
    match q with
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩ := by
  rcases q with ⟨t | t | t, f⟩ <;> rfl


-- @@ L234-240 expanded
lemma liftM_add_assoc_query (t : (spec₁ + (spec₂ + spec₃)).Domain) :
    (liftM (OracleSpec.query t) :
        OracleQuery (spec₁ + spec₂ + spec₃) ((spec₁ + (spec₂ + spec₃)).Range t)) =
      match t with
      | .inl t => OracleSpec.query (Sum.inl (Sum.inl t))
      | .inr (.inl t) => OracleSpec.query (Sum.inl (Sum.inr t))
      | .inr (.inr t) => OracleSpec.query (Sum.inr t) :=
  by rcases t with t | t | t <;> rfl


-- @@ L242-245 expanded
instance lawfulSubSpec_add_assoc : LawfulSubSpec (spec₁ + (spec₂ + spec₃)) (spec₁ + spec₂ + spec₃)
    where onResponse_bijective t := by rcases t with t | t | t <;> exact Function.bijective_id


-- @@ L247-247 verbatim
end add_assoc


-- @@ L249-249 verbatim
section sigma


-- @@ L251-253 verbatim
variable {σ ι} (specs : σ → OracleSpec ι)

-- dtumad: we could expand this more to lifting a finite sum to the sigma type


-- @@ L255-259 expanded
instance subSpec_sigma {σ ι} (specs : σ → OracleSpec ι) (j : σ) :
    SubSpec (specs j) (OracleSpec.sigma specs)
    where
  monadLift q := ⟨⟨j, q.input⟩, q.cont⟩
  onQuery t := ⟨j, t⟩
  onResponse _ := id


-- @@ L261-262 verbatim
@[simp low] lemma liftM_sigma_def (j : σ) (q : OracleQuery (specs j) α) :
    (liftM q : OracleQuery (OracleSpec.sigma specs) _) = .mk ⟨j, q.input⟩ q.cont := rfl


-- @@ L264-266 expanded
@[simp]
lemma liftM_sigma_query (j : σ) (t : (specs j).Domain) :
    (liftM (OracleSpec.query t) : OracleQuery (OracleSpec.sigma specs) ((specs j).Range t)) =
      (OracleSpec.sigma specs).query ⟨j, t⟩ :=
  rfl


-- @@ L268-270 expanded
instance lawfulSubSpec_sigma (j : σ) : LawfulSubSpec (specs j) (OracleSpec.sigma specs) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L272-272 verbatim
end sigma


-- @@ L274-274 verbatim
end instances


-- @@ L276-280 expanded
@[simp low] -- dtumad: the `simp` tag could be dangerous even at low I think
  
lemma liftM_eq_liftM_liftM [SubSpec spec₁ spec₂] [MonadLift (OracleQuery spec₂) (OracleQuery spec₃)]
    (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery spec₃ α) =
      (liftM (liftM q : OracleQuery spec₂ α) : OracleQuery spec₃ α) :=
  rfl


-- @@ L282-282 verbatim
end OracleQuery


-- @@ L284-286 verbatim
section tests

-- This set of examples serves as sort of a "unit test" for the coercions above

-- @@ L287-294 expanded
variable (α : Type) {ι₁ ι₂ ι₃ ι₄ ι ι'} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} (coeSpec : OracleSpec ι)
  (coeSuperSpec : OracleSpec ι')
  [_hSub : SubSpec coeSpec coeSuperSpec]
    -- coerce a single oracle and then add extra oracles


-- @@ L295-296 verbatim
example (oa : OracleComp spec₁ α) :
  OracleComp ((spec₁ + spec₂) + spec₃) α := oa

-- @@ L297-298 verbatim
example (oa : OracleComp spec₂ α) :
  OracleComp ((spec₁ + spec₂) + spec₂) α := oa

-- @@ L299-300 verbatim
example (oa : OracleComp spec₃ α) :
  OracleComp ((spec₁ + spec₂) + spec₃) α := oa

-- @@ L301-302 verbatim
example (oa : OracleComp spec₁ α) :
  OracleComp (spec₁ + (spec₂ + spec₃)) α := oa

-- @@ L303-304 verbatim
example (oa : OracleComp spec₂ α) :
  OracleComp (spec₁ + (spec₂ + spec₂)) α := oa

-- @@ L305-308 verbatim
example (oa : OracleComp spec₃ α) :
  OracleComp (spec₁ + (spec₂ + spec₃)) α := oa

-- coerce a single oracle and then add extra oracles

-- @@ L309-310 verbatim
example (oa : OracleComp coeSpec α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃) α := oa

-- @@ L311-312 verbatim
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa

-- @@ L313-316 verbatim
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa

-- coerce left side of add and then add on additional oracles

-- @@ L317-318 verbatim
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa

-- @@ L319-320 verbatim
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₁) α := oa

-- @@ L321-324 verbatim
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (spec₂ + coeSuperSpec + spec₁) α := oa

-- coerce right side of add and then add on additional oracles

-- @@ L325-326 verbatim
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa

-- @@ L327-328 verbatim
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa

-- @@ L329-332 verbatim
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₂ + spec₁ + coeSuperSpec) α := oa

-- coerce an inside part while also applying associativity

-- @@ L333-334 verbatim
example (oa : OracleComp (spec₁ + (spec₂ + coeSpec)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa

-- @@ L335-336 verbatim
example (oa : OracleComp (spec₁ + (coeSpec + spec₂)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa

-- @@ L337-340 verbatim
example (oa : OracleComp (coeSpec + (spec₁ + spec₂)) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa

-- coerce two oracles up to four oracles

-- @@ L341-342 verbatim
example (oa : OracleComp (spec₁ + spec₂) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L343-344 verbatim
example (oa : OracleComp (spec₁ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L345-346 verbatim
example (oa : OracleComp (spec₁ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L347-348 verbatim
example (oa : OracleComp (spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L349-350 verbatim
example (oa : OracleComp (spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L351-354 verbatim
example (oa : OracleComp (spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- coerce threee oracles up to four oracles

-- @@ L355-356 verbatim
example (oa : OracleComp (spec₁ + spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L357-358 verbatim
example (oa : OracleComp (spec₁ + spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L359-360 verbatim
example (oa : OracleComp (spec₁ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- @@ L361-364 verbatim
example (oa : OracleComp (spec₂ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- four oracles with associativity and internal coercion

-- @@ L365-366 verbatim
example (oa : OracleComp ((coeSpec + spec₂) + (spec₃ + spec₄)) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃ + spec₄) α := oa

-- @@ L367-368 verbatim
example (oa : OracleComp ((spec₁ + spec₂) + (coeSpec + spec₄)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec + spec₄) α := oa

-- @@ L369-370 verbatim
example (oa : OracleComp ((spec₁ + coeSpec) + (spec₃ + spec₄)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₃ + spec₄) α := oa

-- @@ L371-372 verbatim
example (oa : OracleComp ((spec₁ + spec₂) + (spec₃ + coeSuperSpec)) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + coeSuperSpec) α := oa


-- @@ L374-379 expanded
/-- coercion makes it possible to mix computations on individual oracles -/
example : OracleComp (unifSpec + spec₁) Bool := do
  let n : Fin 315 ← uniformFin 314;
  let m : Fin 315 ← uniformFin 314
  if n = m then 
    return true
  else
    uniformSelect!
        #v[true, false]
          -- Testing that simp pathways work well different lifting orders


-- @@ L380-384 verbatim
example (q : OracleQuery spec₁ α) :
    (liftM (liftM q : OracleQuery (spec₁ + spec₂) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) =
    (liftM (liftM q : OracleQuery (spec₁ + spec₃) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) := by simp

-- @@ L385-393 verbatim
example (q : OracleQuery spec₁ α) :
    (liftM (liftM q : OracleQuery (spec₁ + (spec₂ + spec₃)) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) =
    (liftM (liftM q : OracleQuery (spec₁ + spec₃) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) := by simp

-- Whole-computation coercions into a sum spec are *definitionally* a single `liftComp`,
-- with no intermediate hop through another spec. In particular lifting out of `ProbComp`
-- (e.g. into a random-oracle spec `unifSpec + (T →ₒ U)`) is `liftComp` by `rfl`.

-- @@ L394-395 verbatim
example (oa : OracleComp spec₁ α) :
    (oa : OracleComp (spec₁ + spec₂) α) = OracleComp.liftComp oa (spec₁ + spec₂) := rfl

-- @@ L396-397 verbatim
example (oa : OracleComp spec₂ α) :
    (oa : OracleComp (spec₁ + spec₂) α) = OracleComp.liftComp oa (spec₁ + spec₂) := rfl

-- @@ L398-399 verbatim
example (px : ProbComp α) :
    (px : OracleComp (unifSpec + spec₁) α) = OracleComp.liftComp px (unifSpec + spec₁) := rfl


-- @@ L401-401 verbatim
end tests
