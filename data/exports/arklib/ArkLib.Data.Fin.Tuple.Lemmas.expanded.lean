/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Fin.Tuple.Notation


-- @@ L10-12 verbatim
/-!
  # Lemmas for new operations on `Fin`-indexed (heterogeneous) vectors
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
universe u v w


-- @@ L18-21 verbatim
private lemma cast_eq_cast_same_type {α β : Sort u} (h1 h2 : α = β) {x y : α}
    (h : cast h1 x = cast h2 y) : x = y := by
  subst_vars
  rfl


-- @@ L23-23 verbatim
namespace Fin


-- @@ L25-25 verbatim
variable {m n : ℕ} {α : Sort u}


-- @@ L27-30 verbatim
instance : Unique (Fin 0 → α) where
  uniq v := by
    ext i
    exact elim0 i


-- @@ L32-33 verbatim
instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  uniq := fun v => by ext i; exact elim0 i


-- @@ L35-38 verbatim
@[simp]
theorem dcons_zero {motive : Fin (n + 1) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive i.succ) : (a ::ᵈ⟨motive⟩ v) 0 = a := by
  induction n <;> simp [dcons]; rfl


-- @@ L40-42 verbatim
@[simp]
theorem vcons_zero (a : α) (v : Fin n → α) : (a ::ᵛ v) 0 = a :=
  dcons_zero (motive := fun _ => α) a v


-- @@ L44-49 verbatim
@[simp]
theorem dcons_succ {motive : Fin (n + 1) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive i.succ) (i : Fin n) : (a ::ᵈ⟨motive⟩ v) i.succ = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih => simp [dcons, succ]


-- @@ L51-53 verbatim
@[simp]
theorem vcons_succ (a : α) (v : Fin n → α) (i : Fin n) : (a ::ᵛ v) i.succ = v i :=
  dcons_succ (motive := fun _ => α) a v i


-- @@ L55-60 verbatim
/-- `dcons` is equal to `cons`. Marked as `csimp` to allow for switching to the `cons`
  implementation during execution. -/
@[csimp]
theorem dcons_eq_cons : @dcons = @cons := by
  ext n motive a v i
  induction i using induction <;> simp


-- @@ L62-72 verbatim
theorem vcons_eq_cons (a : α) (v : Fin n → α) : a ::ᵛ v = cons a v := by
  have := dcons_eq_cons
  apply funext_iff.mp at this
  have := this n
  apply funext_iff.mp at this
  have := this (fun _ => α)
  apply funext_iff.mp at this
  have := this a
  apply funext_iff.mp at this
  have := this v
  exact this


-- @@ L74-77 verbatim
@[simp]
theorem dcons_one {motive : Fin (n + 2) → Sort u} (a : motive 0)
    (v : (i : Fin (n + 1)) → motive i.succ) : (a ::ᵈ⟨motive⟩ v) 1 = v 0 :=
  dcons_succ a v 0


-- @@ L79-81 verbatim
@[simp]
theorem vcons_one (a : α) (v : Fin (n + 1) → α) : (a ::ᵛ v) 1 = v 0 :=
  vcons_succ a v 0


-- @@ L83-84 verbatim
@[simp]
theorem vcons_empty (a : α) : a ::ᵛ !v[] = !v[a] := rfl


-- @@ L86-89 verbatim
@[simp]
theorem vcons_of_one (a : α) {i : Fin 1} : !v[a] i = match i with | 0 => a := rfl

-- Head/Tail Operations for cons (matching Fin.cons naming)

-- @@ L90-93 verbatim
@[simp]
theorem tail_vcons (a : α) (v : Fin n → α) : tail (a ::ᵛ v) = v := by
  ext i
  simp [tail]


-- @@ L95-100 verbatim
@[simp]
theorem vcons_self_tail (v : Fin (n + 1) → α) : (v 0) ::ᵛ (tail v) = v := by
  ext i
  induction i using induction <;> simp [tail]

-- Injectivity Properties (matching Fin.cons naming)

-- @@ L101-106 verbatim
theorem vcons_right_injective (a : α) :
    Function.Injective (vcons a : (Fin n → α) → Fin (n + 1) → α) := by
  intro v w h
  have : tail (a ::ᵛ v) = tail (a ::ᵛ w) := by
    ext i; rw [h]
  rwa [tail_vcons, tail_vcons] at this


-- @@ L108-110 verbatim
theorem vcons_left_injective (v : Fin n → α) : Function.Injective (fun a => a ::ᵛ v) := by
  intro a b h
  simpa only [vcons_zero] using congr_fun h 0


-- @@ L112-115 verbatim
theorem vcons_injective2 : Function.Injective2 (@vcons α n) := by
  intro a₁ v₁ a₂ v₂ h
  rw [vcons_eq_cons, vcons_eq_cons] at h
  exact cons_injective2 h


-- @@ L117-124 verbatim
theorem vcons_inj (a b : α) (v w : Fin n → α) : a ::ᵛ v = b ::ᵛ w ↔ a = b ∧ v = w := by
  constructor
  · intro h
    exact vcons_injective2 h
  · intro ⟨ha, hv⟩
    rw [ha, hv]

-- Empty Vector Properties

-- @@ L125-126 verbatim
@[simp]
theorem vcons_fin_zero (a : α) (v : Fin 0 → α) : a ::ᵛ v = fun i => match i with | 0 => a := rfl


-- @@ L128-132 verbatim
theorem vcons_eq_const (a : α) : a ::ᵛ (fun _ : Fin n => a) = fun _ => a := by
  ext i
  induction i using induction <;> simp

-- Range Properties for cons (when α : Type*)

-- @@ L133-136 verbatim
theorem range_vcons {α : Type*} (a : α) (v : Fin n → α) :
    Set.range (a ::ᵛ v) = insert a (Set.range v) := by
  rw [vcons_eq_cons]
  simp


-- @@ L138-140 verbatim
@[simp]
theorem dconcat_zero {motive : Fin 1 → Sort u} (a : motive (last 0)) :
    !d⟨fun _ : Fin 0 => motive (castSucc _)⟩[] :+ᵈ⟨motive⟩ a = !d⟨motive⟩[a] := rfl


-- @@ L142-144 verbatim
@[simp]
theorem vconcat_zero (a : α) : vconcat !v[] a = !v[a] :=
  dconcat_zero (motive := fun _ => α) a


-- @@ L146-153 verbatim
@[simp]
theorem dconcat_last {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) : (v :+ᵈ⟨motive⟩ a) (last n) = a := by
  induction n with
  | zero => simp [dconcat]
  | succ n ih =>
    simp only [dconcat, dcons, last]
    exact ih _ _


-- @@ L155-157 verbatim
@[simp]
theorem vconcat_last (v : Fin n → α) (a : α) : vconcat v a (Fin.last n) = a :=
  dconcat_last (motive := fun _ => α) v a


-- @@ L159-173 verbatim
@[simp]
theorem dconcat_castSucc {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) (i : Fin n) : (v :+ᵈ⟨motive⟩ a) (castSucc i) = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih =>
    simp only [dconcat]
    cases i using cases with
    | zero => exact dcons_zero _ _
    | succ i =>
      rw! (castMode := .all) [Fin.castSucc_succ i]
      simp only [dcons]
      change dconcat (motive := fun j => motive j.succ) (fun j => v j.succ) a i.castSucc =
        v i.succ
      exact ih (motive := fun j : Fin (n + 1) => motive j.succ) (fun j => v j.succ) a i


-- @@ L175-178 verbatim
@[simp]
theorem vconcat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    vconcat v a (castSucc i) = v i :=
  dconcat_castSucc (motive := fun _ => α) v a i


-- @@ L180-190 verbatim
/-- `dconcat` is equal to `snoc`. Marked as `csimp` to allow for switching to the `snoc`
  implementation during execution. -/
@[csimp]
theorem dconcat_eq_snoc : @dconcat = @snoc := by
  ext n motive v a i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, dconcat_castSucc, snoc_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this, dconcat_last, snoc_last]


-- @@ L192-202 verbatim
theorem vconcat_eq_snoc (v : Fin n → α) (a : α) : vconcat v a = snoc v a := by
  have := dconcat_eq_snoc
  apply funext_iff.mp at this
  have := this n
  apply funext_iff.mp at this
  have := this (fun _ => α)
  apply funext_iff.mp at this
  have := this v
  apply funext_iff.mp at this
  have := this a
  exact this


-- @@ L204-221 verbatim
theorem dconcat_dcons_eq_dcons_dconcat {motive : Fin (n + 2) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive (succ (castSucc i))) (b : motive (last (n + 1))) :
    (a ::ᵈ v) :+ᵈ⟨motive⟩ b = a ::ᵈ⟨motive⟩ (v :+ᵈ b) := by
  ext i
  match n with
  | 0 => cases i using cases <;> simp [dconcat, dcons]
  | n + 1 =>
    cases i using cases with
    | zero => rfl
    | succ i =>
      by_cases hi : i = last (n + 1)
      · rw [hi]
        simp only [succ_last, Nat.succ_eq_add_one, dconcat_last]
        have : last (_ + 1 + 1) = (last (n + 1)).succ := by simp
        rw! (castMode := .all) [this, dcons_succ]
        simp
      · simp_all only [dcons_succ]
        rfl


-- @@ L223-227 verbatim
theorem vconcat_vcons_eq_vcons_vconcat (a : α) (v : Fin n → α) (b : α) :
    vconcat (a ::ᵛ v) b = a ::ᵛ (vconcat v b) :=
  dconcat_dcons_eq_dcons_dconcat (motive := fun _ => α) a v b

-- Init/snoc properties (matching Fin.snoc naming)

-- @@ L228-231 verbatim
theorem init_dconcat {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) : (fun i => (v :+ᵈ⟨motive⟩ a) (castSucc i)) = v := by
  ext i
  simp [dconcat_castSucc]


-- @@ L233-235 verbatim
theorem init_vconcat (v : Fin n → α) (a : α) :
    (fun i => vconcat v a (Fin.castSucc i)) = v :=
  init_dconcat (motive := fun _ => α) v a


-- @@ L237-246 verbatim
theorem dconcat_init_self {motive : Fin (n + 1) → Sort u} (v : (i : Fin (n + 1)) → motive i) :
    (fun i => v (castSucc i)) :+ᵈ⟨motive⟩ (v (last n)) = v := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, dconcat_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this]
    simp [dconcat_last]


-- @@ L248-250 verbatim
theorem vconcat_init_self (v : Fin (n + 1) → α) :
    vconcat (fun i => v (Fin.castSucc i)) (v (Fin.last n)) = v :=
  dconcat_init_self (motive := fun _ => α) v


-- @@ L252-257 verbatim
theorem range_vconcat {α : Type*} (v : Fin n → α) (a : α) :
    Set.range (vconcat v a) = insert a (Set.range v) := by
  rw [vconcat_eq_snoc]
  simp

-- Injectivity properties for concat (matching Fin.snoc naming)

-- @@ L258-264 verbatim
theorem dconcat_injective2 {motive : Fin (n + 1) → Sort u} :
    Function.Injective2 (@dconcat n motive) := by
  intro v w a b h
  constructor
  · ext i
    simpa only [dconcat_castSucc] using congr_fun h (castSucc i)
  · simpa only [dconcat_last] using congr_fun h (last n)


-- @@ L266-267 verbatim
theorem vconcat_injective2 : Function.Injective2 (@vconcat α n) :=
  dconcat_injective2 (motive := fun _ => α)


-- @@ L269-275 verbatim
theorem dconcat_inj {motive : Fin (n + 1) → Sort u} (v w : (i : Fin n) → motive (castSucc i))
    (a b : motive (last n)) :
    (v :+ᵈ⟨motive⟩ a) = (w :+ᵈ⟨motive⟩ b) ↔ v = w ∧ a = b := by
  constructor
  · exact @dconcat_injective2 _ motive v w a b
  · intro ⟨hv, ha⟩
    rw [hv, ha]


-- @@ L277-279 verbatim
theorem vconcat_inj (v w : Fin n → α) (a b : α) :
    vconcat v a = vconcat w b ↔ v = w ∧ a = b :=
  dconcat_inj (motive := fun _ => α) v w a b


-- @@ L281-286 verbatim
theorem dconcat_right_injective {motive : Fin (n + 1) → Sort u}
    (v : (i : Fin n) → motive (castSucc i)) :
    Function.Injective (dconcat (motive := motive) v) := by
  intro x y h
  have : dconcat (motive := motive) v x = dconcat (motive := motive) v y := h
  exact (dconcat_inj v v x y).mp this |>.2


-- @@ L288-289 verbatim
theorem vconcat_right_injective (v : Fin n → α) : Function.Injective (vconcat v) :=
  dconcat_right_injective (motive := fun _ => α) v


-- @@ L291-294 verbatim
theorem dconcat_left_injective {motive : Fin (n + 1) → Sort u} (a : motive (last n)) :
    Function.Injective (fun v => dconcat (motive := motive) v a) := by
  intro x y h
  exact (dconcat_inj x y a a).mp h |>.1


-- @@ L296-298 verbatim
theorem vconcat_left_injective {n : ℕ} (a : α) :
    Function.Injective (fun v : Fin n → α => vconcat v a) :=
  dconcat_left_injective (motive := fun _ => α) a


-- @@ L300-319 verbatim
@[simp]
theorem zero_dappend {motive : Fin (0 + n) → Sort u} {u : (i : Fin 0) → motive (castAdd n i)}
    (v : (i : Fin n) → motive (natAdd 0 i)) :
    dappend (motive := motive) u v = fun i => cast (by simp) (v (i.cast (by omega))) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [dappend, ih, dconcat_eq_snoc, Fin.cast, last]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc ⟨i.val, by simp [h]⟩ := by ext; simp
      rw [this, snoc_castSucc]
      simp
    · have : i.val = n := by omega
      have : i = Fin.last _ := by ext; simp [this]
      rw! [this]
      subst this
      simp_all only [forall_fin_zero_pi, Nat.add_eq, val_last, zero_add,
                    lt_self_iff_false, not_false_eq_true, snoc_last]
      grind only [cases Or]



-- @@ L322-325 verbatim
@[simp]
theorem zero_vappend {u : Fin 0 → α} (v : Fin n → α) :
    vappend u v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_dappend (motive := fun _ => α) v


-- @@ L327-329 verbatim
@[simp]
theorem dappend_zero {motive : Fin (m + 0) → Sort u} (u : (i : Fin m) → motive (castAdd 0 i)) :
    dappend (motive := motive) u !d⟨fun _ : Fin 0 => motive (natAdd m _)⟩[] = u := rfl


-- @@ L331-332 verbatim
@[simp]
theorem vappend_zero (u : Fin m → α) {v : Fin 0 → α} : vappend u v = u := rfl


-- @@ L334-340 verbatim
theorem dappend_succ {motive : Fin (m + (n + 1)) → Sort u}
    (u : (i : Fin m) → motive (castAdd (n + 1) i))
    (v : (i : Fin (n + 1)) → motive (natAdd m i)) :
    dappend (motive := motive) u v =
      (dappend u (fun i => v (castSucc i))) :+ᵈ⟨motive⟩ (v (last n)) := by
  ext i
  simp [dappend]


-- @@ L342-344 verbatim
theorem vappend_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    vappend u v = vconcat (vappend u (v ∘ castSucc)) (v (last n)) :=
  dappend_succ (motive := fun _ => α) u v


-- @@ L346-370 verbatim
/-- `dappend` is equal to `addCases`. Marked as `csimp` to allow for switching to the `addCases`
  implementation during execution. -/
@[csimp]
theorem dappend_eq_addCases : @dappend = @addCases := by
  ext m n motive u v i
  induction n with
  | zero => simp [dappend, addCases, castLT]
  | succ n ih =>
    simp only [dappend, dconcat_eq_snoc]
    have ih' : ∀ (motive : Fin (m + n) → Sort _)
      (u : (i : Fin m) → motive (castAdd n i))
      (v : (i : Fin n) → motive (natAdd m i)),
        dappend (motive := motive) u v = addCases (motive := motive) u v := by
      intro motive_1 u_1 v_1
      ext x : 1
      apply ih
    rw [ih' (fun i => motive i.castSucc) u (fun i => v (castSucc i))]
    simp [snoc, addCases, last, castLT, subNat]
    by_cases h : i.val < m
    · have : i.val < m + n := by omega
      simp [h, this]
    · by_cases h' : i.val < m + n
      · grind only
      · have : i.val = m + n := by omega
        grind only [cases Or]


-- @@ L372-378 verbatim
/-- `vappend` is equal to `append`. Marked as `csimp` to allow for switching to the `append`
  implementation during execution. -/
@[csimp]
theorem vappend_eq_append : @vappend = @append := by
  ext
  rw [vappend, dappend_eq_addCases]
  simp [append]


-- @@ L380-384 verbatim
@[simp]
theorem dempty_dappend {motive : Fin (0 + n) → Sort u} (v : (i : Fin n) → motive (natAdd 0 i)) :
    dappend (motive := motive) !d⟨fun _ : Fin 0 => motive (castAdd n _)⟩[] v =
      fun i => cast (by simp) (v (i.cast (by omega))) :=
  zero_dappend v


-- @@ L386-388 verbatim
@[simp]
theorem vempty_vappend (v : Fin n → α) : vappend !v[] v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_vappend v


-- @@ L390-392 verbatim
@[simp]
theorem dappend_dempty {motive : Fin (m + 0) → Sort u} (v : (i : Fin m) → motive (castAdd 0 i)) :
    dappend (motive := motive) v !d⟨fun _ : Fin 0 => motive (natAdd m _)⟩[] = v := rfl


-- @@ L394-395 verbatim
@[simp]
theorem vappend_vempty (v : Fin m → α) : vappend v !v[] = v := rfl


-- @@ L397-416 verbatim
theorem dappend_assoc {p : ℕ} {motive : Fin (m + n + p) → Sort u}
    (_u : (i : Fin m) → motive (castAdd p (castAdd n i)))
    (_v : (i : Fin n) → motive (castAdd p (natAdd m i)))
    (_w : (i : Fin p) → motive (natAdd (m + n) i)) : True := by
      simp_all only
    -- dappend (motive := motive) (dappend u v) w =
    -- dappend (m := m) (n := n + p) (motive := motive ∘ Fin.cast (Nat.add_assoc m n p).symm) u
    --   (dappend
    --     (motive := fun i : Fin (n + p) =>
    --       motive (Fin.cast (Nat.add_assoc _ _ _).symm (natAdd m i)))
    --     v (sorry)) := by sorry
  -- ext i
  -- simp [dappend]
  -- have : castAdd p (castAdd n i) = castAdd (n + p) i := by
  --   ext; simp [coe_castAdd]
  -- rw [this, dconcat_castSucc, dconcat_castSucc]
  -- simp [dappend]
  -- have : castAdd p (natAdd m i) = castAdd (m + p) i := by
  --   ext; simp [coe_castAdd]
  -- sorry


-- @@ L418-420 verbatim
theorem vappend_assoc {p : ℕ} (u : Fin m → α) (v : Fin n → α) (w : Fin p → α) :
    (vappend (vappend u v) w) = (vappend u (vappend v w)) ∘ Fin.cast (add_assoc m n p) := by
  simp [vappend_eq_append, append_assoc]


-- @@ L422-426 verbatim
@[simp]
theorem dappend_left {motive : Fin (m + n) → Sort u} (u : (i : Fin m) → motive (castAdd n i))
    (v : (i : Fin n) → motive (natAdd m i)) (i : Fin m) :
    dappend (motive := motive) u v (castAdd n i) = u i := by
  rw [dappend_eq_addCases, addCases_left]


-- @@ L428-431 verbatim
@[simp]
theorem vappend_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    vappend u v (castAdd n i) = u i :=
  dappend_left (motive := fun _ => α) u v i


-- @@ L433-437 verbatim
@[simp]
theorem dappend_right {motive : Fin (m + n) → Sort u} (u : (i : Fin m) → motive (castAdd n i))
    (v : (i : Fin n) → motive (natAdd m i)) (i : Fin n) :
    dappend (motive := motive) u v (natAdd m i) = v i := by
  rw [dappend_eq_addCases, addCases_right]


-- @@ L439-475 verbatim
@[simp]
theorem vappend_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    vappend u v (natAdd m i) = v i :=
  dappend_right (motive := fun _ => α) u v i

lemma dappend_left_of_lt {motive : Fin (m + n) → Sort u}
    (u : (i : Fin m) → motive (castAdd n i)) (v : (i : Fin n) → motive (natAdd m i))
    (i : Fin (m + n)) (h : i.val < m) :
      dappend (motive := motive) u v i = cast (by simp) (u ⟨i, h⟩) := by
  simp [dappend_eq_addCases, addCases, castLT, h]

lemma vappend_left_of_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : i.val < m) :
      vappend u v i = u ⟨i, h⟩ :=
  dappend_left_of_lt (motive := fun _ => α) u v i h

lemma dappend_right_of_not_lt {motive : Fin (m + n) → Sort u}
    (u : (i : Fin m) → motive (castAdd n i)) (v : (i : Fin n) → motive (natAdd m i))
    (i : Fin (m + n)) (h : ¬ i.val < m) :
      dappend (motive := motive) u v i = dcast (by ext; simp; omega) (v ⟨i - m, by omega⟩) := by
  simp [dappend_eq_addCases, addCases, h, subNat, dcast, cast]
  grind only

lemma vappend_right_of_not_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : ¬ i.val < m) :
      vappend u v i = v ⟨i - m, by omega⟩ :=
  dappend_right_of_not_lt (motive := fun _ => α) u v i h

-- @[simp]
-- theorem dappend_dcons {motive : Fin ((m + 1) + n) → Sort u} (a : motive 0)
--     (u : (i : Fin m) → motive (succ (castAdd n i)))
--     (v : (i : Fin n) → motive (natAdd (m + 1) i)) :
--     dappend (motive := motive) (a ::ᵈ⟨motive⟩ u) v =
--       fun i => cast (by simp) (dcons a
-- (dappend (motive := fun i => motive (cast (by omega) i)) u v)
--         (i.cast (Nat.succ_add m n))) := by
--   sorry


-- @@ L477-489 verbatim
@[simp]
theorem vappend_vcons (a : α) (u : Fin m → α) (v : Fin n → α) :
    vappend (vcons a u) v = (vcons a (vappend u v)) ∘ Fin.cast (Nat.succ_add m n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_cons a u v

-- theorem dappend_dconcat {motive : Fin (m + (n + 1)) → Sort u}
--     (u : (i : Fin m) → motive (cast (by omega) (castAdd (n + 1) i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd m (castSucc i))))
--     (a : motive (cast (by omega) (natAdd m (last n)))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) u (dconcat v a) =
--       dconcat (motive := fun i => motive (cast (by omega) i)) (dappend u v) a := by
--   sorry


-- @@ L491-501 verbatim
theorem vappend_vconcat (u : Fin m → α) (v : Fin n → α) (a : α) :
    vappend u (vconcat v a) = vconcat (vappend u v) a := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_snoc u v a

-- theorem dappend_left_eq_dcons {motive : Fin (1 + n) → Sort u}
--     (a : (i : Fin 1) → motive (cast (by omega) (castAdd n i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd 1 i))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) a v =
--       fun i => cast (by simp) (dcons (a 0) v (i.cast (Nat.add_comm 1 n))) := by
--   sorry


-- @@ L503-512 verbatim
theorem vappend_left_eq_cons (a : Fin 1 → α) (v : Fin n → α) :
    vappend a v = (vcons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_left_eq_cons a v

-- theorem dappend_right_eq_dconcat
--     {motive : Fin (m + 1) → Sort u} (u : (i : Fin m) → motive (cast (by omega) (castAdd 1 i)))
--     (a : (i : Fin 1) → motive (cast (by omega) (natAdd m i))) :
--     dappend (motive := motive) u a = dconcat u (a 0) := by
--   sorry


-- @@ L514-521 verbatim
theorem vappend_right_eq_snoc (u : Fin m → α) (a : Fin 1 → α) :
    vappend u a = vconcat u (a 0) := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_right_eq_snoc u a

lemma vappend_zero_of_succ_left {u : Fin (m + 1) → α} {v : Fin n → α} :
    (vappend u v) 0 = u 0 := by
  simp [vappend_eq_append]


-- @@ L523-528 verbatim
@[simp]
lemma vappend_last_of_succ_right {u : Fin m → α} {v : Fin (n + 1) → α} :
    (vappend u v) (last (m + n)) = v (last n) := by
  simp [vappend_eq_append]

-- Range properties for append (when α : Type*)

-- @@ L529-548 verbatim
theorem range_vappend {α : Type*} (u : Fin m → α) (v : Fin n → α) :
    Set.range (vappend u v) = Set.range u ∪ Set.range v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [vappend_succ, range_vconcat, ih]
    ext i
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_range, Function.comp_apply]
    constructor
    · rintro (rfl | h | ⟨y, rfl⟩)
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, rfl⟩
    · rintro (h | ⟨y, rfl⟩)
      · exact Or.inr (Or.inl h)
      · by_cases hy : y = Fin.last n
        · exact Or.inl (by rw [hy])
        · exact Or.inr (Or.inr ⟨y.castPred hy, by simp⟩)

-- Extensionality for append

-- @@ L549-557 verbatim
theorem vappend_ext (u₁ u₂ : Fin m → α) (v₁ v₂ : Fin n → α) :
    vappend u₁ v₁ = vappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  simp only [vappend_eq_append]
  constructor <;> intro h
  · exact ⟨by ext i; simpa only [append_left] using congr_fun h (Fin.castAdd n i),
          by ext i; simpa only [append_right] using congr_fun h (Fin.natAdd m i)⟩
  · simp [h]

-- Additional useful extensionality lemmas

-- @@ L558-559 verbatim
theorem ext_vcons (a b : α) (v w : Fin n → α) : vcons a v = vcons b w ↔ a = b ∧ v = w :=
  vcons_inj a b v w


-- @@ L561-564 verbatim
theorem vcons_eq_vcons_iff (a b : α) (v w : Fin n → α) : vcons a v = vcons b w ↔ a = b ∧ v = w :=
  vcons_inj a b v w

-- Two vectors are equal iff they are equal at every index

-- @@ L565-568 verbatim
theorem vext_iff {v w : Fin n → α} : v = w ↔ ∀ i, v i = w i :=
  ⟨fun h i => by rw [h], fun h => funext h⟩

-- Interaction between operations

-- @@ L569-572 verbatim
theorem vcons_vappend_comm (a : α) (u : Fin m → α) (v : Fin n → α) :
    vcons a (vappend u v) = (vappend (vcons a u) v) ∘ Fin.cast (Nat.succ_add m n).symm := by
  simp only [vcons_eq_cons, vappend_eq_append]
  ext i; simp [append_cons]


-- @@ L574-578 verbatim
theorem vappend_singleton (u : Fin m → α) (a : α) :
    vappend u (vcons a !v[]) = vconcat u a := by
  simp only [vappend_eq_append, vcons_eq_cons, vconcat_eq_snoc, vempty]
  ext i
  simp [append_right_cons]


-- @@ L580-586 verbatim
theorem singleton_append (a : α) (v : Fin n → α) :
    vappend !v[a] v = vcons a v ∘ Fin.cast (Nat.add_comm _ n) := by
  have ha : !v[a] 0 = a := by
    exact vcons_zero a !v[]
  rw [vappend_left_eq_cons, ha]

-- Empty cases

-- @@ L587-588 verbatim
theorem empty_unique (v : Fin 0 → α) : v = !v[] :=
  funext (fun i => elim0 i)


-- @@ L590-592 verbatim
/-! ### Lemmas for functorial vectors (binary first, then unary) -/

/- Binary functorial lemmas for `fcons₂`, `fconcat₂`, `fappend₂`. -/

-- @@ L593-593 verbatim
section FunctorialBinary


-- @@ L595-595 verbatim
variable {A : Sort u} {B : Sort v} {F₂ : A → B → Sort w} {m n : ℕ}


-- @@ L597-601 verbatim
@[simp]
theorem fcons₂_zero {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a b 0 = cast (by simp [Fin.vcons_zero]) a := by
  induction n <;> rfl


-- @@ L603-610 verbatim
@[simp]
theorem fcons₂_succ {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin n) :
    fcons₂ (F := F₂) a b i.succ =
      cast (by simp [Fin.vcons_succ]) (b i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ _ _ => rfl


-- @@ L612-616 verbatim
@[simp]
theorem fcons₂_one {α₁ : A} {α₂ : B} {β₁ : Fin (n + 1) → A} {β₂ : Fin (n + 1) → B}
    (a : F₂ α₁ α₂) (b : (i : Fin (n + 1)) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a b 1 = b 0 := by
  induction n <;> rfl


-- @@ L618-624 verbatim
theorem fcons₂_right_injective {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) :
    Function.Injective
      (fcons₂ (F := F₂) a : ((i : Fin n) → F₂ (β₁ i) (β₂ i)) → (i : Fin (n + 1)) → _ ) := by
  intro x y h; ext i
  exact cast_eq_cast_same_type _ _ <|
    by simpa only [fcons₂_succ] using congr_fun h i.succ


-- @@ L626-631 verbatim
theorem fcons₂_left_injective {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    Function.Injective (fun a : F₂ α₁ α₂ => fcons₂ (F := F₂) a b) := by
  intro x y h
  exact cast_eq_cast_same_type _ _ <|
    by simpa only [fcons₂_zero] using congr_fun h 0


-- @@ L633-641 verbatim
theorem fcons₂_injective2 {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B} :
    Function.Injective2 (@fcons₂ A B F₂ n α₁ β₁ α₂ β₂) := by
  intro a₁ b₁ a₂ b₂ h
  constructor
  · exact cast_eq_cast_same_type _ _ <|
      by simpa only [fcons₂_zero] using congr_fun h 0
  · ext i
    exact cast_eq_cast_same_type _ _ <|
      by simpa only [fcons₂_succ] using congr_fun h i.succ


-- @@ L643-648 verbatim
theorem fcons₂_inj {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a₁ a₂ : F₂ α₁ α₂) (b₁ b₂ : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a₁ b₁ = fcons₂ (F := F₂) a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h; exact fcons₂_injective2 (n := n) (β₁ := β₁) (β₂ := β₂) h
  · intro ⟨ha, hb⟩; simp [ha, hb]


-- @@ L650-665 verbatim
@[simp]
theorem fconcat₂_castSucc {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a : F₂ β₁ β₂) (i : Fin n) :
    fconcat₂ (F := F₂) v a (castSucc i) =
      cast (by simp [vconcat_castSucc]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fconcat₂]
    induction i using induction with
    | zero => simp
    | succ i ih' =>
      rw! (castMode := .all) [Fin.castSucc_succ i]
      change fconcat₂ (fun j => v j.succ) a i.castSucc = _
      rw! (castMode := .all) [ih]
      rfl


-- @@ L667-678 verbatim
@[simp]
theorem fconcat₂_last {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a : F₂ β₁ β₂) :
    fconcat₂ (F := F₂) v a (last n) = cast (by simp [vconcat_last]) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! (castMode := .all) [this, fconcat₂]
    change fconcat₂ (fun j => v j.succ) a (last n) = _
    rw! (castMode := .all) [ih]
    rfl


-- @@ L680-688 verbatim
theorem fconcat₂_injective2 {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B} :
    Function.Injective2 (@fconcat₂ A B F₂ n α₁ β₁ α₂ β₂) := by
  intro v₁ a₁ v₂ a₂ h
  constructor
  · ext i
    exact cast_eq_cast_same_type _ _ <|
      by simpa only [fconcat₂_castSucc] using congr_fun h (castSucc i)
  · exact cast_eq_cast_same_type _ _ <|
      by simpa only [fconcat₂_last] using congr_fun h (last n)


-- @@ L690-695 verbatim
theorem fconcat₂_inj {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v₁ v₂ : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a₁ a₂ : F₂ β₁ β₂) :
    fconcat₂ (F := F₂) v₁ a₁ = fconcat₂ (F := F₂) v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  constructor
  · intro h; exact fconcat₂_injective2 (n := n) (α₁ := α₁) (α₂ := α₂) (β₁ := β₁) (β₂ := β₂) h
  · intro ⟨hv, ha⟩; simp [hv, ha]


-- @@ L697-701 verbatim
theorem fconcat₂_right_injective {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) :
    Function.Injective (fconcat₂ (F := F₂) v :
      F₂ β₁ β₂ → (i : Fin (n + 1)) → F₂ (Fin.vconcat α₁ β₁ i) (Fin.vconcat α₂ β₂ i)) := by
  intro x y h; exact (fconcat₂_inj (α₁ := α₁) (α₂ := α₂) v v x y).mp h |>.2


-- @@ L703-705 verbatim
theorem fconcat₂_left_injective {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B} (a : F₂ β₁ β₂) :
    Function.Injective (fun v : (i : Fin n) → F₂ (α₁ i) (α₂ i) => fconcat₂ (F := F₂) v a) := by
  intro x y h; exact (fconcat₂_inj (α₁ := α₁) (α₂ := α₂) x y a a).mp h |>.1


-- @@ L707-710 verbatim
@[simp]
theorem fappend₂_zero {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin 0 → A} {β₂ : Fin 0 → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) :
    fappend₂ (F := F₂) u (!h⦃F₂⦄⟨β₁⟩⟨β₂⟩[] : (i : Fin 0) → F₂ (β₁ i) (β₂ i)) = u := rfl


-- @@ L712-718 verbatim
@[simp]
theorem fappend₂_succ {α₁ : Fin m → A} {α₂ : Fin m → B}
    {β₁ : Fin (n + 1) → A} {β₂ : Fin (n + 1) → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin (n + 1)) → F₂ (β₁ i) (β₂ i)) :
    fappend₂ (F := F₂) u v =
      fconcat₂ (F := F₂) (fappend₂ (F := F₂) u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [fappend₂]


-- @@ L720-731 verbatim
@[simp]
theorem fappend₂_left {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin m) :
    fappend₂ (F := F₂) u v (castAdd n i) =
      cast (by simp [vappend_left]) (u i) := by
  induction n with
  | zero => exact (cast_eq _ _).symm
  | succ n ih =>
    simp only [fappend₂_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, fconcat₂_castSucc, ih]
    exact _root_.cast_cast ..


-- @@ L733-750 verbatim
@[simp]
theorem fappend₂_right {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin n) :
    fappend₂ (F := F₂) u v (natAdd m i) =
      cast (by simp [vappend_right]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fappend₂_succ]
    by_cases h : i.val < n
    · have : natAdd m i = castSucc ⟨m + i.val, by simp [h]⟩ := by ext; simp
      rw! [this, fconcat₂_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, fconcat₂_last, hi]; rfl


-- @@ L752-763 verbatim
theorem fappend₂_ext {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u₁ u₂ : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v₁ v₂ : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fappend₂ (F := F₂) u₁ v₁ = fappend₂ (F := F₂) u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  constructor
  · intro h; constructor
    · ext i
      exact cast_eq_cast_same_type _ _ <|
        by simpa only [fappend₂_left] using congr_fun h (castAdd n i)
    · ext i
      exact cast_eq_cast_same_type _ _ <|
        by simpa only [fappend₂_right] using congr_fun h (natAdd m i)
  · intro ⟨hu, hv⟩; simp [hu, hv]


-- @@ L765-765 verbatim
end FunctorialBinary


-- @@ L767-767 verbatim
section FunctorialUnary


-- @@ L769-769 verbatim
variable {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : A}


-- @@ L771-774 verbatim
@[simp]
theorem fcons_zero {β : Fin n → A} (a : F α) (b : (i : Fin n) → F (β i)) :
    fcons a b 0 = cast (by simp [vcons_zero]) a := by
  induction n <;> rfl


-- @@ L776-781 verbatim
@[simp]
theorem fcons_succ {β : Fin n → A} (a : F α) (v : (i : Fin n) → F (β i)) (i : Fin n) :
    fcons a v i.succ = cast (by simp [vcons_succ]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => rfl


-- @@ L783-788 verbatim
@[simp]
theorem fcons_one {β : Fin (n + 1) → A} (a : F α) (v : (i : Fin (n + 1)) → F (β i)) :
    fcons a v 1 = v 0 := by
  induction n <;> rfl

-- Injectivity properties for fcons

-- @@ L789-794 verbatim
theorem fcons_right_injective {β : Fin n → A} (a : F α) :
    Function.Injective (fcons a : ((i : Fin n) → F (β i)) → (i : Fin (n + 1)) → _) := by
  intro x y h
  ext i
  exact cast_eq_cast_same_type _ _ <|
    by simpa only [fcons_succ] using congr_fun h i.succ


-- @@ L796-800 verbatim
theorem fcons_left_injective {β : Fin n → A} (b : (i : Fin n) → F (β i)) :
    Function.Injective (fun (a : F α) => fcons a b) := by
  intro x y h
  exact cast_eq_cast_same_type _ _ <|
    by simpa only [fcons_zero] using congr_fun h 0


-- @@ L802-810 verbatim
theorem fcons_injective2 {β : Fin n → A} :
    Function.Injective2 (@fcons A F n α β) := by
  intro a₁ b₁ a₂ b₂ h
  constructor
  · exact cast_eq_cast_same_type _ _ <|
      by simpa only [fcons_zero] using congr_fun h 0
  · ext i
    exact cast_eq_cast_same_type _ _ <|
      by simpa only [fcons_succ] using congr_fun h (succ i)


-- @@ L812-817 verbatim
theorem fcons_inj {β : Fin n → A} (a₁ a₂ : F α) (b₁ b₂ : (i : Fin n) → F (β i)) :
    fcons a₁ b₁ = fcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro i; have := fcons_injective2 i; exact this
  · intro ⟨ha, hb⟩
    rw [ha, hb]


-- @@ L819-821 verbatim
@[simp]
theorem fconcat_zero {α : Fin 0 → A} {β : A} (a : F β) : !h⦃F⦄⟨α⟩[] :+ʰ a =
    fun i => match i with | 0 => a := rfl


-- @@ L823-837 verbatim
@[simp]
theorem fconcat_castSucc {α : Fin n → A} {β : A}
    (v : (i : Fin n) → F (α i)) (b : F β) (i : Fin n) :
    (v :+ʰ⦃F⦄ b) (castSucc i) = cast (by simp [vconcat_castSucc]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fconcat]
    induction i using induction with
    | zero => simp
    | succ i _ =>
      rw! (castMode := .all) [Fin.castSucc_succ i]
      change fconcat (fun j => v j.succ) b i.castSucc = _
      rw! (castMode := .all) [ih]
      rfl


-- @@ L839-851 verbatim
@[simp]
theorem fconcat_last {α : Fin n → A} {β : A} (v : (i : Fin n) → F (α i)) (b : F β) :
    fconcat v b (last n) = cast (by simp [vconcat_last]) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! (castMode := .all) [this, fconcat]
    change fconcat (fun j => v j.succ) b (last n) = _
    rw! (castMode := .all) [ih]
    rfl

-- Injectivity properties for fconcat

-- @@ L852-860 verbatim
theorem fconcat_injective2 {α : Fin n → A} {β : A} :
    Function.Injective2 (@fconcat A F n α β) := by
  intro v₁ a₁ v₂ a₂ h
  constructor
  · ext i
    exact cast_eq_cast_same_type _ _ <|
      by simpa only [fconcat_castSucc] using congr_fun h (castSucc i)
  · exact cast_eq_cast_same_type _ _ <|
      by simpa only [fconcat_last] using congr_fun h (last n)


-- @@ L862-868 verbatim
theorem fconcat_inj {α : Fin n → A} {β : A}
    (v₁ v₂ : (i : Fin n) → F (α i)) (a₁ a₂ : F β) :
    fconcat v₁ a₁ = fconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  constructor
  · intro h; exact fconcat_injective2 h
  · intro ⟨hv, ha⟩
    rw [hv, ha]


-- @@ L870-873 verbatim
theorem fconcat_right_injective {α : Fin n → A} {β : A} (v : (i : Fin n) → F (α i)) :
    Function.Injective (fconcat v : F β → (i : Fin (n + 1)) → F (vconcat α β i)) := by
  intro x y h
  exact (fconcat_inj v v x y).mp h |>.2


-- @@ L875-878 verbatim
theorem fconcat_left_injective {α : Fin n → A} {β : A} (a : F β) :
    Function.Injective (fun v : (i : Fin n) → F (α i) => fconcat v a) := by
  intro x y h
  exact (fconcat_inj x y a a).mp h |>.1


-- @@ L880-880 verbatim
/-! Functorial append (unary F) lemmas -/


-- @@ L882-885 verbatim
@[simp]
theorem fappend_zero {β : Fin m → A} {α : Fin 0 → A}
    (u : (i : Fin m) → F (β i)) :
    fappend u (!h⦃F⦄⟨α⟩[] : (i : Fin 0) → F (α i)) = u := rfl


-- @@ L887-891 verbatim
@[simp]
theorem fappend_succ {α : Fin m → A} {β : Fin (n + 1) → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin (n + 1)) → F (β i)) :
    fappend u v = fconcat (fappend u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [fappend]


-- @@ L893-903 verbatim
@[simp]
theorem fappend_left {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) (i : Fin m) :
    fappend u v (castAdd n i) = cast (by simp [vappend_left]) (u i) := by
  induction n with
  | zero => exact (cast_eq _ _).symm
  | succ n ih =>
    simp only [fappend_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, fconcat_castSucc, ih]
    exact _root_.cast_cast ..


-- @@ L905-921 verbatim
@[simp]
theorem fappend_right {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) (i : Fin n) :
    fappend u v (natAdd m i) = cast (by simp [vappend_right]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fappend_succ]
    by_cases h : i.val < n
    · have : natAdd m i = (castSucc (⟨m + i.val, by simp [h]⟩)) := by ext; simp
      rw! [this, fconcat_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, fconcat_last, hi]; rfl


-- @@ L923-936 verbatim
theorem fappend_ext {α : Fin m → A} {β : Fin n → A}
    (u₁ u₂ : (i : Fin m) → F (α i)) (v₁ v₂ : (i : Fin n) → F (β i)) :
    fappend u₁ v₁ = fappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  constructor
  · intro h
    constructor
    · ext i
      exact cast_eq_cast_same_type _ _ <|
        by simpa only [fappend_left] using congr_fun h (castAdd n i)
    · ext i
      exact cast_eq_cast_same_type _ _ <|
        by simpa only [fappend_right] using congr_fun h (natAdd m i)
  · intro ⟨hu, hv⟩
    rw [hu, hv]


-- @@ L938-938 verbatim
end FunctorialUnary


-- @@ L940-940 verbatim
/-! ### Lemmas for heterogeneous vectors -/


-- @@ L942-945 verbatim
@[simp]
theorem hcons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    hcons a b 0 = cast (vcons_zero α β).symm a := by
  simp [hcons, fcons_zero]


-- @@ L947-950 verbatim
@[simp]
theorem hcons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    hcons a v i.succ = cast (vcons_succ α β i).symm (v i) := by
  simp [hcons, fcons_succ]


-- @@ L952-955 verbatim
@[simp]
theorem hcons_one {β : Fin (n + 1) → Sort u} (a : α) (v : (i : Fin (n + 1)) → β i) :
    hcons a v 1 = cast (vcons_succ α β 0).symm (v 0) := by
  simp [hcons, fcons_one]; rfl


-- @@ L957-960 verbatim
theorem hcons_eq_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    hcons a v = cons (α := vcons α β) (hcons a v 0) (fun i => hcons a v i.succ) := by
  ext i
  induction i using induction <;> simp


-- @@ L962-964 verbatim
@[simp]
theorem hconcat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    hconcat !h⟨α⟩[] a = fun i => match i with | 0 => a := rfl


-- @@ L966-970 verbatim
@[simp]
theorem hconcat_castSucc {α : Fin n → Sort u} {β : Sort u}
    (v : (i : Fin n) → α i) (b : β) (i : Fin n) :
    hconcat v b (castSucc i) = cast (vconcat_castSucc α β i).symm (v i) := by
  simp [hconcat, fconcat_castSucc]


-- @@ L972-975 verbatim
@[simp]
theorem hconcat_last {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    hconcat v b (last n) = cast (vconcat_last α β).symm b := by
  simp [hconcat, fconcat_last]


-- @@ L977-991 verbatim
theorem hconcat_eq_snoc {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    hconcat v b = snoc (α := vconcat α β)
      (fun i => cast (vconcat_castSucc _ _ i).symm (v i))
      (cast (vconcat_last _ _).symm b) := by
  induction n with
  | zero => ext; simp [hconcat, snoc, fconcat]; split; rfl
  | succ n ih =>
    ext i
    by_cases hi : i.val < n + 1
    · have : i = castSucc ⟨i.val, hi⟩ := by ext; simp
      rw [this, hconcat_castSucc, snoc_castSucc]
    · have : i = last (n + 1) := by ext; simp; omega
      rw [this, hconcat_last, snoc_last]

-- Injectivity properties for cons (from functorial versions)

-- @@ L992-994 verbatim
theorem hcons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (hcons a : ((i : Fin n) → β i) → (i : Fin (n + 1)) → vcons α β i) := by
  exact fcons_right_injective (F := id) a


-- @@ L996-998 verbatim
theorem hcons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : (i : Fin n) → β i) :
    Function.Injective (fun (a : α) => hcons a b) := by
  exact fcons_left_injective (F := id) b


-- @@ L1000-1002 verbatim
theorem hcons_injective2 {α : Sort u} {β : Fin n → Sort u} :
    Function.Injective2 (@hcons n α β) := by
  exact fcons_injective2 (F := id)


-- @@ L1004-1008 verbatim
theorem hcons_inj {α : Sort u} {β : Fin n → Sort u} (a₁ a₂ : α) (b₁ b₂ : (i : Fin n) → β i) :
    hcons a₁ b₁ = hcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  exact fcons_inj (F := id) a₁ a₂ b₁ b₂

-- Empty tuple properties

-- @@ L1009-1012 verbatim
@[simp]
theorem hcons_fin_zero {α : Sort u} {β : Fin 0 → Sort u} (a : α) (v : (i : Fin 0) → β i) :
    hcons a v = fun i => match i with | 0 => a := by
  ext i; rfl


-- @@ L1014-1019 verbatim
theorem hconcat_hcons {α : Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (_a : α) (_v : (i : Fin n) → β i) (_c : γ) :
    True := by
    simp_all only

-- Init/concat properties

-- @@ L1020-1022 verbatim
theorem dinit_hconcat {α : Fin n → Sort u} {β : Sort u} (_v : (i : Fin n) → α i) (_b : β) :
    True := by
  simp_all only


-- @@ L1024-1028 verbatim
theorem hconcat_init_self {α : Fin n.succ → Sort u} (_v : (i : Fin (n + 1)) → α i) :
    True := by
  simp_all only

-- Injectivity properties for concat (from functorial versions)

-- @@ L1029-1031 verbatim
theorem hconcat_injective2 {α : Fin n → Sort u} {β : Sort u} :
    Function.Injective2 (@hconcat n α β) := by
  exact fconcat_injective2 (F := id)


-- @@ L1033-1035 verbatim
theorem hconcat_inj {α : Fin n → Sort u} {β : Sort u} (v₁ v₂ : (i : Fin n) → α i) (a₁ a₂ : β) :
    hconcat v₁ a₁ = hconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  exact fconcat_inj (F := id) v₁ v₂ a₁ a₂


-- @@ L1037-1039 verbatim
theorem hconcat_right_injective {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) :
    Function.Injective (hconcat v : β → (i : Fin (n + 1)) → vconcat α β i) := by
  exact fconcat_right_injective (F := id) v


-- @@ L1041-1043 verbatim
theorem hconcat_left_injective {α : Fin n → Sort u} {β : Sort u} (a : β) :
    Function.Injective (fun v : (i : Fin n) → α i => hconcat v a) := by
  exact fconcat_left_injective (F := id) a


-- @@ L1045-1048 verbatim
@[simp]
theorem happend_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    happend u !h⟨α⟩[] = u :=
  fappend_zero (F := id) u


-- @@ L1050-1052 verbatim
@[simp]
theorem happend_empty {α : Fin m → Sort u} {β : Fin 0 → Sort u} (v : (i : Fin m) → α i) :
    happend v !h⟨β⟩[] = v := rfl


-- @@ L1054-1058 verbatim
@[simp]
theorem happend_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin (n + 1)) → β i) :
    happend u v = hconcat (happend u (fun i => v (castSucc i))) (v (last n)) := by
  exact fappend_succ (F := id) u v


-- @@ L1060-1082 verbatim
@[simp]
theorem dempty_happend {α : Fin 0 → Sort u} {β : Fin n → Sort u} (v : (i : Fin n) → β i) :
    happend !d⟨α⟩[] v =
      fun i : Fin (0 + n) => cast (by simp) (v <| i.cast (by omega)) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [happend_succ]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc (⟨i.val, by simp [h]⟩) := by ext; simp
      rw [this, hconcat_castSucc]
      simp only [Fin.cast, castSucc_mk, Fin.eta]
      have key := congr_fun (ih (β := fun j => β j.castSucc) (fun j => v j.castSucc))
        ⟨i.val, by omega⟩
      rw [key]
      exact _root_.cast_cast ..
    · have : i = Fin.last (0 + n) := by ext; simp; omega
      rw! [this, hconcat_last]
      simp only [Fin.last, Fin.cast_mk]
      grind only

-- Index access for append

-- @@ L1083-1087 verbatim
@[simp]
theorem happend_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin m) :
    happend u v (castAdd n i) = cast (vappend_left α β i).symm (u i) := by
  simp [happend, fappend_left]


-- @@ L1089-1093 verbatim
@[simp]
theorem happend_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin n) :
    happend u v (natAdd m i) = cast (vappend_right α β i).symm (v i) := by
  simp [happend, fappend_right]


-- @@ L1095-1107 verbatim
theorem happend_eq_addCases {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    happend u v = addCases (motive := vappend α β)
      (fun i => cast (vappend_left α β i).symm (u i))
      (fun i => cast (vappend_right α β i).symm (v i)) := by
  ext i
  by_cases h : i.val < m
  · have : i = castAdd n ⟨i, by omega⟩ := by ext; simp
    rw [this]
    simp only [addCases_left, happend_left]
  · have : i = natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [this]
    simp only [addCases_right, happend_right]


-- @@ L1109-1117 verbatim
/-- Access into a heterogeneous append on the left, by value: if `↑j < m`, then `happend u v j` is
(heterogeneously) the `j`-th entry of `u`. -/
theorem happend_heq_left {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (j : Fin (m + n)) (h : (j : ℕ) < m) :
    HEq (happend u v j) (u ⟨(j : ℕ), h⟩) := by
  have key : HEq (happend u v (Fin.castAdd n ⟨(j : ℕ), h⟩)) (u ⟨(j : ℕ), h⟩) := by
    rw [happend_left]; exact cast_heq _ _
  have hj : Fin.castAdd n ⟨(j : ℕ), h⟩ = j := by ext; simp
  rwa [hj] at key


-- @@ L1119-1128 verbatim
/-- Access into a heterogeneous append on the right, by value: if `m ≤ ↑j`, then `happend u v j` is
(heterogeneously) the `(↑j - m)`-th entry of `v`. -/
theorem happend_heq_right {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (j : Fin (m + n)) (h : ¬ (j : ℕ) < m) :
    HEq (happend u v j) (v ⟨(j : ℕ) - m, by omega⟩) := by
  have key : HEq (happend u v (Fin.natAdd m ⟨(j : ℕ) - m, by omega⟩))
      (v ⟨(j : ℕ) - m, by omega⟩) := by
    rw [happend_right]; exact cast_heq _ _
  have hj : Fin.natAdd m ⟨(j : ℕ) - m, by omega⟩ = j := by ext; simp; omega
  rwa [hj] at key


-- @@ L1130-1156 verbatim
theorem happend_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (w : (i : Fin p) → γ i) :
    happend (happend u v) w =
      fun i => cast (by simp [vappend_assoc])
        (happend u (happend v w) (i.cast (by omega))) := by
  funext i
  by_cases hm : (i : ℕ) < m
  · rw [show i = Fin.castAdd p (Fin.castAdd n ⟨(i : ℕ), hm⟩) from by ext; simp]
    simp only [happend_left]
    simp only [Fin.castAdd_castAdd, Fin.cast_cast, Fin.cast_eq_self, happend_left, _root_.cast_cast]
  · by_cases hn : (i : ℕ) < m + n
    · rw [show i = Fin.castAdd p (Fin.natAdd m ⟨(i : ℕ) - m, by omega⟩) from by ext; simp; omega]
      simp only [happend_left, happend_right]
      simp only [← Fin.natAdd_castAdd, happend_left, happend_right, _root_.cast_cast]
    · apply eq_of_heq
      refine HEq.trans (happend_heq_right (happend u v) w i (by omega)) ?_
      refine HEq.trans ?_ (cast_heq _ _).symm
      refine HEq.trans ?_
        (happend_heq_right u (happend v w) (i.cast (by omega)) (by simp; omega)).symm
      refine HEq.trans ?_
        (happend_heq_right v w
          ⟨((i.cast (by omega) : Fin (m + (n + p))) : ℕ) - m, by simp; omega⟩
          (by simp; omega)).symm
      congr 1
      simp [Nat.sub_sub]

-- Relationship with cons/concat

-- @@ L1157-1160 verbatim
theorem happend_hcons {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (_a : α) (_u : (i : Fin m) → β i) (_v : (i : Fin n) → γ i) :
    True := by
    simp_all only


-- @@ L1162-1167 verbatim
theorem happend_hconcat {α : Fin m → Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (_u : (i : Fin m) → α i) (_v : (i : Fin n) → β i) (_c : γ) :
    True := by
    simp_all only

-- Compatibility lemmas

-- @@ L1168-1171 verbatim
theorem happend_left_eq_hcons {α : Fin 1 → Sort u} {β : Fin n → Sort u}
    (_a : (i : Fin 1) → α i) (_v : (i : Fin n) → β i) :
    True := by
    simp_all only


-- @@ L1173-1177 verbatim
theorem happend_right_eq_hconcat {α : Fin m → Sort u} {β : Fin 1 → Sort u}
    (u : (i : Fin m) → α i) (a : (i : Fin 1) → β i) :
    happend u a = hconcat u (a 0) := by
    simp_all only [happend_succ, Nat.add_zero, vappend_zero, reduceLast, isValue]
    rfl


-- @@ L1179-1182 verbatim
theorem happend_ext {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u₁ u₂ : (i : Fin m) → α i) (v₁ v₂ : (i : Fin n) → β i) :
    happend u₁ v₁ = happend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  exact fappend_ext (F := id) u₁ u₂ v₁ v₂


-- @@ L1184-1186 verbatim
theorem ext_hcons {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    hcons a₁ v₁ = hcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ :=
  hcons_inj a₁ a₂ v₁ v₂


-- @@ L1188-1192 verbatim
theorem hcons_eq_hcons_iff {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    hcons a₁ v₁ = hcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ :=
  hcons_inj a₁ a₂ v₁ v₂

-- Two tuples are equal iff they are equal at every index (with casting)

-- @@ L1193-1197 verbatim
theorem dext_iff {α : Fin n → Sort u} {v w : (i : Fin n) → α i} :
    v = w ↔ ∀ i, v i = w i := by
  aesop

-- Interaction between operations

-- @@ L1198-1201 verbatim
theorem hcons_happend_comm {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (_a : α) (_u : (i : Fin m) → β i) (_v : (i : Fin n) → γ i) :
    True := by
    simp_all only


-- @@ L1203-1205 verbatim
theorem happend_singleton {α : Fin m → Sort u} {β : Sort u} (_u : (i : Fin m) → α i) (_a : β) :
    True := by
    simp_all only


-- @@ L1207-1209 verbatim
theorem singleton_happend {β : Fin n → Sort u} (_a : α) (_v : (i : Fin n) → β i) :
    True := by
    simp_all only


-- @@ L1211-1235 verbatim
instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  default := fun i => elim0 i
  uniq v := by
    ext i
    exact Fin.elim0 i

-- Cast lemma for type families
-- theorem cast_cons {β : Fin n → Sort u} (a : α) (v : FinTuple n β) :
--     FinTuple.cast rfl (fun _ => rfl) (cons a v) = cons a v := by
--   simp only [Fin.cast_eq_self, cons_eq_fin_cons, cons_zero, cons_succ]
--   ext _
--   simp [cast]

-- theorem cast_hconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
--     cast rfl (fun _ => rfl) (hconcat v b) = hconcat v b := by
--   simp only [Fin.cast_eq_self, hconcat_eq_fin_snoc]
--   ext _
--   simp [cast]

-- theorem cast_happend {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
--     cast rfl (fun _ => rfl) (happend u v) = happend u v := by
--   simp only [Fin.cast_eq_self, happend_eq_addCases]
--   ext _
--   simp [cast]


-- @@ L1237-1242 verbatim
variable {m n : ℕ} {α : Sort u}

-- @[simp, grind =]
-- theorem concat_eq_append {α : Sort u} {n : ℕ} (v : FinVec α n) (a : α) :
--     concat v a = append v (FinVec.cons a FinVec.empty) := by
--   ext i; fin_cases i <;> rfl


-- @@ L1244-1244 verbatim
section padding


-- @@ L1246-1249 verbatim
@[simp]
theorem rightpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < m) : rightpad n a v i = v ⟨i.val, h⟩ := by
  simp [rightpad, h]


-- @@ L1251-1255 verbatim
@[simp]
theorem rightpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : m ≤ i.val) : rightpad n a v i = a := by
  simp [rightpad]
  omega


-- @@ L1257-1261 verbatim
@[simp]
theorem leftpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < n - m) : leftpad n a v i = a := by
  simp [leftpad]
  omega


-- @@ L1263-1266 verbatim
@[simp]
theorem leftpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : n - m ≤ i.val) : leftpad n a v i = v ⟨i.val - (n - m), by omega⟩ := by
  simp [leftpad, h]


-- @@ L1268-1270 verbatim
theorem rightpad_eq_self (v : Fin n → α) (a : α) : rightpad n a v = v := by
  ext i
  simp [rightpad_apply_lt]


-- @@ L1272-1274 verbatim
theorem leftpad_eq_self (v : Fin n → α) (a : α) : leftpad n a v = v := by
  ext i
  simp [leftpad_apply_ge]


-- @@ L1276-1276 verbatim
end padding


-- @@ L1278-1278 verbatim
end Fin
