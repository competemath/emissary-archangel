module
public import Mathlib.Data.Fin.VecNotation
public import Foundation.Vorspiel.Nat.Basic
public import Foundation.Vorspiel.Fin.Basic


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace Matrix


-- @@ L10-10 verbatim
open _root_.Fin


-- @@ L12-12 verbatim
section

-- @@ L13-13 verbatim
variable {n : ℕ} {α : Type u}


-- @@ L15-15 verbatim
infixr:70 " :> " => vecCons


-- @@ L17-18 verbatim
@[simp] lemma vecCons_zero :
    (a :> s) 0 = a := by simp


-- @@ L20-21 verbatim
@[simp] lemma vecCons_succ (i : Fin n) :
    (a :> s) (Fin.succ i) = s i := by simp


-- @@ L23-24 verbatim
@[simp] lemma vecCons_last (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := vecCons_succ (Fin.last n)


-- @@ L26-27 verbatim
def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t


-- @@ L29-29 verbatim
@[simp] lemma cons_app_one {n : ℕ} (a : α) (s : Fin n.succ → α) : (a :> s) 1 = s 0 := rfl


-- @@ L31-31 verbatim
@[simp] lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (a :> s) 2 = s 1 := rfl


-- @@ L33-33 verbatim
@[simp] lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (a :> s) 3 = s 2 := rfl


-- @@ L35-35 verbatim
@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl


-- @@ L37-37 verbatim
@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) : (a :> s) 5 = s 4 := rfl


-- @@ L39-39 verbatim
@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) : (a :> s) 6 = s 5 := rfl


-- @@ L41-41 verbatim
@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 7 = s 6 := rfl


-- @@ L43-43 verbatim
@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 8 = s 7 := rfl


-- @@ L45-45 verbatim
section delab

-- @@ L46-46 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L48-50 verbatim
@[app_unexpander Matrix.vecEmpty]
meta def unexpandVecEmpty : Unexpander
  | `($(_)) => `(![])


-- @@ L52-56 verbatim
@[app_unexpander Matrix.vecCons]
meta def unexpandVecCons : Unexpander
  | `($(_) $a ![])      => `(![$a])
  | `($(_) $a ![$as,*]) => `(![$a, $as,*])
  | _                   => throw ()


-- @@ L58-58 verbatim
end delab


-- @@ L60-60 verbatim
infixl:70 " <: " => vecConsLast


-- @@ L62-63 verbatim
@[simp] lemma rightConcat_last :
    (s <: a) (Fin.last n) = a := by simp [vecConsLast]


-- @@ L65-66 verbatim
@[simp] lemma rightConcat_castSucc (i : Fin n) :
    (s <: a) (Fin.castSucc i) = s i := by simp [vecConsLast]


-- @@ L68-69 verbatim
@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc 0


-- @@ L71-72 verbatim
@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> Fin.succ = id :=
  funext $ Fin.cases (by simp) (by simp)


-- @@ L74-81 verbatim
@[simp] lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) : (f 0 :> (f ·.succ) : Fin (n + 1) → α) = f := by
    funext x; cases x using Fin.cases <;> simp

lemma eq_vecCons (s : Fin (n + 1) → C) : s 0 :> s ∘ Fin.succ = s :=
   funext $ Fin.cases (by simp) (by simp)

lemma eq_vecCons' (s : Fin (n + 1) → C) : s 0 :> (s ·.succ) = s :=
   funext $ Fin.cases (by simp) (by simp)


-- @@ L83-98 verbatim
@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp [h]⟩

lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    a :> (s <: b) = (a :> s) <: b := by
  funext x; cases' x using Fin.cases with x
  · simp
  · cases x using Fin.lastCases
    · simp
    case cast i =>
      simp; simp only [rightConcat_castSucc, Fin.succ_castSucc i, cons_val_succ]


-- @@ L100-121 verbatim
def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simpa [Matrix.empty_eq] using isTrue trivial
  | n + 1, v, w, d => by
      rw [←eq_vecCons v, ←eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simpa using d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> f ∘ s :=
  funext (fun i => Fin.cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ f <| (a :> s) x) = f a :> fun i ↦ f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

lemma comp_vecCons₂' (g : β → γ) (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ g <| f <| (a :> s) x) = (g (f a) :> fun i ↦ g <| f <| s i) := by
  funext x
  cases x using Fin.cases <;> simp


-- @@ L123-123 verbatim
@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp [Matrix.empty_eq]


-- @@ L125-125 verbatim
@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp [comp_vecCons'']


-- @@ L127-127 verbatim
@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp [comp_vecCons'']


-- @@ L129-129 verbatim
@[simp] lemma comp₃ (a₁ a₂ a₃ : α) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by simp [comp_vecCons'']


-- @@ L131-134 verbatim
@[simp] lemma comp₄ (a₁ a₂ a₃ a₄ : α) : f ∘ ![a₁, a₂, a₃, a₄] = ![f a₁, f a₂, f a₃, f a₄] := by simp [comp_vecCons'']

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => Fin.lastCases (by simp) (by simp) i)


-- @@ L136-137 verbatim
@[simp] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) : vecHead (f ∘ v) = f (vecHead v) :=
  by simp [vecHead]


-- @@ L139-177 verbatim
@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i
    · rw [this, rightConcat_last, cons_val_fin_one]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ ↦ a) = ![a] := by funext x; simp

lemma fun_eq_vec_one (v : Fin 1 → α) : v = ![v 0] := by funext x; simp

lemma constant_eq_vec₂ {a : α} : (fun _ ↦ a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp

lemma fun_eq_vec_two (v : Fin 2 → α) : v = ![v 0, v 1] := by
  funext x;
  cases x using Fin.cases <;> simp

lemma fun_eq_vec_three (v : Fin 3 → α) : v = ![v 0, v 1, v 2] := by
  funext x
  repeat cases' x using Fin.cases with x <;> simp

lemma fun_eq_vec_four (v : Fin 4 → α) : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  repeat cases' x using Fin.cases with x <;> simp

lemma fun_eq_vec_four' (f : α → β) (v : Fin 4 → α) : f ∘ v = ![f (v 0), f (v 1), f (v 2), f (v 3)] := by
  rw [fun_eq_vec_four v]; simp

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) : Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases
  · simp
  · simp [*]
  · simp [*]
  · simpa using @h _ _


-- @@ L179-182 verbatim
@[simp] lemma vecCons_empty_eq_singleton (v : Fin 0 → α) (x : α) : x :> v = ![x] := by
  ext i
  rcases Fin.fin_one_eq_zero i
  simp


-- @@ L184-188 verbatim
@[simp] lemma vecConsLast_empty_eq_singleton (v : Fin 0 → α) (x : α) : v <: x = ![x] := by
  ext i
  rcases Fin.fin_one_eq_zero i
  simp [vecConsLast]
  rfl


-- @@ L190-190 verbatim
end


-- @@ L192-192 verbatim
variable {α : Type _}


-- @@ L194-196 verbatim
def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)


-- @@ L198-198 verbatim
@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl


-- @@ L200-200 verbatim
@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl


-- @@ L202-203 verbatim
@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp [*]


-- @@ L205-211 verbatim
@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a := by
  induction n
  · simp [*]
  · suffices (a = v 0 ∨ ∃ i : Fin _, v i.succ = a) ↔ ∃ i, v i = a by simp [*]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp


-- @@ L213-213 verbatim
variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}


-- @@ L215-224 verbatim
def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction' n with n ih
  · unfold getM; congr; funext x; exact x.elim0
  · simp only [getM, map_pure, ih, seq_pure]
    exact congr_arg _ (funext <| Fin.cases rfl fun i ↦ rfl)


-- @@ L226-227 verbatim
@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v


-- @@ L229-229 verbatim
def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α := Matrix.vecAppend (add_comm m n) v w


-- @@ L231-231 verbatim
@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]


-- @@ L233-246 verbatim
@[simp] lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) : appendr (x :> v) w = x :> appendr v w := by funext i; simp [appendr]

-- Renamed from `Matrix.forall_iff` to `Matrix.vecForall_iff` to avoid clashing with
-- Mathlib's `Matrix.forall_iff` (Mathlib.Data.Matrix.Reflection), which otherwise makes
-- Foundation unimportable alongside that module.
lemma vecForall_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∀ v, φ v) ↔ (∀ a, ∀ v, φ (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

-- Renamed from `Matrix.exists_iff` to `Matrix.vecExists_iff`; see `vecForall_iff` above.
lemma vecExists_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∃ v, φ v) ↔ (∃ a, ∃ v, φ (a :> v)) :=
  ⟨by rintro ⟨v, hv⟩; exact ⟨v 0, v ∘ Fin.succ, by simpa [eq_vecCons] using hv⟩,
   by rintro ⟨a, v, hv⟩; exact ⟨_, hv⟩⟩


-- @@ L248-254 verbatim
def foldr (f : α → β → β) (init : β) : {k : ℕ} → (Fin k → α) → β
  |     0, _ => init
  | _ + 1, v => f (vecHead v) (Matrix.foldr f init (vecTail v))

-- Renamed from `Matrix.map` to `Matrix.vecMap` to avoid clashing with Mathlib's
-- `Matrix.map`: both auto-generate `Matrix.map.eq_1`, which makes Foundation
-- unimportable alongside Mathlib matrix/analysis theory (e.g. Bochner integration).

-- @@ L255-255 verbatim
def vecMap (f : α → β) : (Fin k → α) → (Fin k → β) := fun v ↦ f ∘ v


-- @@ L257-257 verbatim
section vecMap


-- @@ L259-259 verbatim
postfix:max "⨟" => vecMap


-- @@ L261-261 verbatim
variable (f : α → β)


-- @@ L263-263 verbatim
@[simp] lemma vecMap_nil (v : Fin 0 → α) : f⨟ v = ![] := empty_eq (f⨟ v)


-- @@ L265-267 verbatim
@[simp] lemma vecMap_cons (a : α) (v : Fin k → α) : f⨟ (a :> v) = f a :> f⨟ v := by
  ext i
  cases i using Fin.cases <;> simp [vecMap]


-- @@ L269-271 verbatim
@[simp] lemma vecMap_cons' (v : Fin (k + 1) → α) : f⨟ v = f (vecHead v) :> f⨟ (vecTail v) := by
  ext i
  cases i using Fin.cases <;> { simp [vecMap]; rfl }


-- @@ L273-279 verbatim
@[simp] lemma vecMap_app (v : Fin k → α) (i : Fin k) : (f⨟ v) i = f (v i) := rfl

lemma vecMap_vecMap_comp (g : β → γ) (f : α → β) (v : Fin k → α) :
    g⨟ (f⨟ v) = (g ∘ f)⨟ v := by ext x; simp

lemma vecMap_vecMap_comp' (g : β → γ) (f : α → β) (v : Fin k → α) :
    g⨟ (f⨟ v) = (fun x ↦ g (f x))⨟ v := by ext x; simp


-- @@ L281-281 verbatim
end vecMap

-- @@ L282-282 verbatim
section foldr


-- @@ L284-284 verbatim
variable (f : α → β → β) (init : β)


-- @@ L286-286 verbatim
@[simp] lemma foldr_zero (v : Fin 0 → α) : foldr f init v = init := rfl


-- @@ L288-288 verbatim
@[simp] lemma foldr_succ (v : Fin (k + 1) → α) : foldr f init v = f (vecHead v) (foldr f init (vecTail v)) := rfl


-- @@ L290-290 verbatim
end foldr


-- @@ L292-294 verbatim
def foldl (f : α → β → α) : (init : α) → {k : ℕ} → (Fin k → β) → α
  | a,     0, _ => a
  | a, _ + 1, v => Matrix.foldl f (f a (vecHead v)) (vecTail v)


-- @@ L296-296 verbatim
section foldl


-- @@ L298-298 verbatim
variable (f : α → β → α) (init : α)


-- @@ L300-300 verbatim
@[simp] lemma foldl_zero (v : Fin 0 → β) : foldl f init v = init := rfl


-- @@ L302-302 verbatim
@[simp] lemma foldl_succ (v : Fin (k + 1) → β) : foldl f init v = foldl f (f init (vecHead v)) (vecTail v) := rfl


-- @@ L304-313 verbatim
end foldl

lemma eq_iff_eq_vecHead_of_eq_vecTail {v₁ v₂ : Fin (n + 1) → α} :
    Matrix.vecHead v₁ = Matrix.vecHead v₂ ∧ Matrix.vecTail v₁ = Matrix.vecTail v₂ ↔ v₁ = v₂ := by
  constructor
  · rintro ⟨h, t⟩
    ext i; cases i using Fin.cases
    · exact h
    · exact congr_fun t _
  · rintro rfl; simp


-- @@ L315-315 verbatim
section vecToNat


-- @@ L317-317 verbatim
def vecToNat (v : Fin n → ℕ) : ℕ := foldr (fun x ih ↦ Nat.pair x ih + 1) 0 v


-- @@ L319-319 verbatim
@[simp] lemma vecToNat_empty (v : Fin 0 → ℕ) : vecToNat v = 0 := by rfl


-- @@ L321-322 verbatim
@[simp] lemma encode_succ {n} (x : ℕ) (v : Fin n → ℕ) : vecToNat (x :> v) = Nat.pair x (vecToNat v) + 1 := by
  simp [vecToNat]


-- @@ L324-324 verbatim
end vecToNat



-- @@ L327-327 verbatim
section


-- @@ L329-329 verbatim
variable {m : ℕ}


-- @@ L331-332 verbatim
@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]


-- @@ L334-335 verbatim
@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]


-- @@ L337-337 verbatim
end


-- @@ L339-339 verbatim
end Matrix


-- @@ L341-341 verbatim
end
