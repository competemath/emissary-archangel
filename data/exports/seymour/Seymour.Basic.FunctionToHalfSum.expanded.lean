import Seymour.Basic.Basic


-- @@ L3-7 verbatim
/-!
# Functions to "half" Sum

Here we study functions of type `α → β₁ ⊕ β₂` that happen to contain image in only one of the half of its codomain.
-/


-- @@ L9-9 verbatim
variable {β₁ β₂ : Type*}


-- @@ L11-12 expanded
lemma sum_ne_inl {x : β₁ ⊕ β₂} (hx₁ : ∀ b₁ : β₁, x ≠ Sum.inl b₁) : ∃ b₂ : β₂, x = Sum.inr b₂ := by
  aesop


-- @@ L14-15 expanded
lemma sum_ne_inr {x : β₁ ⊕ β₂} (hx₂ : ∀ b₂ : β₂, x ≠ Sum.inr b₂) : ∃ b₁ : β₁, x = Sum.inl b₁ := by
  aesop


-- @@ L17-17 verbatim
variable {α : Type*}


-- @@ L19-20 expanded
lemma fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ Sum.inl b₁) :
    ∀ a : α, ∃ b₂ : β₂, f a = Sum.inr b₂ :=
  (sum_ne_inl <| hf ·)


-- @@ L22-23 expanded
lemma fn_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ Sum.inr b₂) :
    ∀ a : α, ∃ b₁ : β₁, f a = Sum.inl b₁ :=
  (sum_ne_inr <| hf ·)


-- @@ L25-27 expanded
/-- Assume `f : α → β₁ ⊕ β₂` never reaches `β₁` values. We convert `f` to `α → β₂` function. -/
noncomputable def fn_of_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ Sum.inl b₁) :
    α → β₂ :=
  (fn_sum_ne_inl hf · |>.choose)


-- @@ L29-31 expanded
/-- Assume `f : α → β₁ ⊕ β₂` never reaches `β₂` values. We convert `f` to `α → β₁` function. -/
noncomputable def fn_of_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ Sum.inr b₂) :
    α → β₁ :=
  (fn_sum_ne_inr hf · |>.choose)


-- @@ L33-35 expanded
lemma eq_of_fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ Sum.inl b₁) (i : α) :
    f i = Sum.inr (fn_of_sum_ne_inl hf i) :=
  (fn_sum_ne_inl hf i).choose_spec


-- @@ L37-39 expanded
lemma eq_of_fn_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ Sum.inr b₂) (i : α) :
    f i = Sum.inl (fn_of_sum_ne_inr hf i) :=
  (fn_sum_ne_inr hf i).choose_spec

