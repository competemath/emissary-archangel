/-
A self-contained classical reasoning layer.

Rebuilds the pieces of Lean's `Classical` namespace that this project uses,
starting from our own `choice` axiom. This is strictly a pedagogical mirror:
`propext` and `funext` still come from Lean core (they are not derivable from
choice alone), but no piece of the Classical API itself is reused.
-/


-- @@ L10-10 verbatim
universe u v


-- @@ L12-12 verbatim
namespace MyClassical


-- @@ L14-18 verbatim
/-- Axiom of choice: from a proof that `α` is inhabited, pick an element. -/
axiom choice
    {α : Sort u}
    (h : Nonempty α) :
    α


-- @@ L20-26 verbatim
/-- Given `∃ x, p x`, produce a subtype witness. -/
noncomputable def indefiniteDescription
    {α : Sort u}
    (p : α → Prop)
    (h : ∃ x, p x) :
    {x // p x} :=
  choice (let ⟨x, px⟩ := h; Nonempty.intro (Subtype.mk x px))


-- @@ L28-34 verbatim
/-- Given `∃ x, p x`, pick such an `x`. -/
noncomputable def choose
    {α : Sort u}
    (p : α → Prop)
    (h : ∃ x, p x) :
    α :=
  Subtype.val (indefiniteDescription p h)


-- @@ L36-42 verbatim
/-- The chosen element satisfies the predicate. -/
theorem choose_spec
    {α : Sort u}
    (p : α → Prop)
    (h : ∃ x, p x) :
    p (choose p h) :=
  Subtype.property (indefiniteDescription p h)


-- @@ L44-96 verbatim
/--
Excluded middle, via Diaconescu's theorem.

Uses `choice` together with `propext` and `funext` from Lean core.
-/
theorem em
    (p : Prop) :
    p ∨ ¬p :=
  let U (x : Prop) : Prop :=
    x = True ∨ p
  let V (x : Prop) : Prop :=
    x = False ∨ p
  have exU : ∃ x, U x :=
    Exists.intro True (Or.inl rfl)
  have exV : ∃ x, V x :=
    Exists.intro False (Or.inl rfl)
  let u : Prop :=
    choose U exU
  let v : Prop :=
    choose V exV
  have u_def : U u :=
    choose_spec U exU
  have v_def : V v :=
    choose_spec V exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by
        intro huv
        rw [hut] at huv
        rw [hvf] at huv
        exact Eq.mp huv True.intro
      Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        (propext (Iff.intro hl hr) : (x = True ∨ p) = (x = False ∨ p))
    have h₀ : ∀ (exU' : ∃ x, U x) (exV' : ∃ x, V x),
        choose U exU' = choose V exV' := by
      rw [hpred]
      intro exU' exV'
      rfl
    (h₀ exU exV : u = v)
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h


-- @@ L98-102 verbatim
theorem byContradiction
    (p : Prop)
    (h : ¬p → False) :
    p :=
  Or.elim (em p) id (fun hnp => False.elim (h hnp))


-- @@ L104-104 verbatim
end MyClassical
