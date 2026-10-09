import OAI.Combinatorics.MatrixRemoval.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-9 verbatim
/-!
The raw finite host; row and column orders are supplied separately.
The second coordinate in a variable class is uniform on `Fin (2^h)`;
its quotient by the block size is the node index.
-/

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace Problem348.Construction


-- @@ L13-13 verbatim
abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)

-- @@ L14-14 verbatim
abbrev AnchorPosition (h : ℕ) := Fin (6 * h) × Fin 64 × Fin (2 ^ h)

-- @@ L15-15 verbatim
abbrev Position (h : ℕ) := AnchorPosition h ⊕ (VariablePosition h ⊕ Fin (2 ^ h))

-- @@ L16-16 verbatim
abbrev Mode (h : ℕ) := Fin (6 * h)


-- @@ L18-18 verbatim
def depth {h : ℕ} (x : VariablePosition h) : ℕ := x.1.val / 2

-- @@ L19-19 verbatim
def node {h : ℕ} (x : VariablePosition h) : ℕ := x.2.val / 2 ^ (h - depth x)

-- @@ L20-20 verbatim
def plus {h : ℕ} (x : VariablePosition h) : Bool := decide (x.1.val % 2 = 0)

-- @@ L21-21 verbatim
def level {h : ℕ} (t : Mode h) : ℕ := t.val / 6 + 1

-- @@ L22-22 verbatim
def kind {h : ℕ} (t : Mode h) : ℕ := t.val % 6


-- @@ L24-25 verbatim
def AtLevel {h : ℕ} (i : ℕ) (s : Bool) (x : VariablePosition h) : Prop :=
  depth x = i ∧ (i = h ∨ plus x = s)


-- @@ L27-38 verbatim
def rowRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => 2 ≤ kind t ∧ j.val = 1
  | Sum.inr (Sum.inl v) =>
    if kind t = 0 then
      AtLevel (if j.val = 0 then level t else level t - 1) true v
    else if kind t = 1 then
      AtLevel (if j.val = 0 then level t - 1 else level t) false v
    else
      j.val = 0 ∧ AtLevel (level t) (decide (kind t < 4)) v ∧
        node v % 2 = (kind t % 2)


-- @@ L40-52 verbatim
def colRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => kind t < 2 ∧ j.val = 0
  | Sum.inr (Sum.inl v) =>
    if kind t < 2 then
      j.val = 1 ∧ AtLevel (level t - 1) (decide (kind t = 0)) v
    else if kind t < 4 then
      if j.val = 0 then AtLevel (level t - 1) true v
      else AtLevel (level t) true v ∧ node v % 2 = kind t % 2
    else
      if j.val = 0 then AtLevel (level t) false v ∧ node v % 2 = kind t % 2
      else AtLevel (level t - 1) false v


-- @@ L54-55 verbatim
instance {h : ℕ} (i : ℕ) (s : Bool) (v : VariablePosition h) :
    Decidable (AtLevel i s v) := inferInstanceAs (Decidable (_ ∧ _))

-- @@ L56-57 verbatim
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (rowRole t j x) := by unfold rowRole; split <;> infer_instance

-- @@ L58-59 verbatim
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (colRole t j x) := by unfold colRole; split <;> infer_instance


-- @@ L61-70 verbatim
def variableEntry {h : ℕ} (r c : VariablePosition h) : Bool :=
  if depth r = depth c then
    if depth r = h then decide (node r ≤ node c)
    else if plus r = plus c then
      if plus r then decide (node r ≤ node c) else decide (node r < node c)
    else false
  else if depth r = depth c + 1 ∧ depth c < h ∧
      (depth r = h ∨ plus r = plus c) then
    if plus c then decide (node r / 2 ≤ node c) else decide (node r / 2 < node c)
  else false


-- @@ L72-81 verbatim
def host {h : ℕ} (r c : Position h) : Bool :=
  match r, c with
  | Sum.inl (t, u, _), Sum.inl (t', v, _) =>
      if t = t' then Problem348.anchor64 u v else false
  | Sum.inl (t, u, _), Sum.inr _ =>
      decide ((u.val = 0 ∧ colRole t 0 c) ∨ (u.val = 1 ∧ colRole t 1 c))
  | Sum.inr _, Sum.inl (t, v, _) =>
      decide ((v.val = 0 ∧ rowRole t 0 r) ∨ (v.val = 1 ∧ rowRole t 1 r))
  | Sum.inr (Sum.inl v), Sum.inr (Sum.inl w) => variableEntry v w
  | Sum.inr _, Sum.inr _ => true


-- @@ L83-86 verbatim
theorem depth_le {h : ℕ} (x : VariablePosition h) : depth x ≤ h := by
  have hx := x.1.isLt
  unfold depth
  omega


-- @@ L88-90 verbatim
theorem level_pos {h : ℕ} (t : Mode h) : 1 ≤ level t := by
  unfold level
  omega


-- @@ L92-95 verbatim
theorem level_le {h : ℕ} (t : Mode h) : level t ≤ h := by
  have ht := t.isLt
  unfold level
  omega


-- @@ L97-98 verbatim
theorem kind_lt {h : ℕ} (t : Mode h) : kind t < 6 := by
  exact Nat.mod_lt _ (by decide)


-- @@ L100-102 verbatim
theorem card_variablePosition (h : ℕ) :
    Fintype.card (VariablePosition h) = (2 * h + 1) * 2 ^ h := by
  simp [VariablePosition]


-- @@ L104-108 verbatim
theorem card_position (h : ℕ) :
    Fintype.card (Position h) = (386 * h + 2) * 2 ^ h := by
  simp only [Position, AnchorPosition, VariablePosition, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  ring


-- @@ L110-113 verbatim
@[simp] theorem host_anchor_same {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t, v, y)) = anchor64 u v := by
  simp [host]


-- @@ L115-118 verbatim
@[simp] theorem host_anchor_different {h : ℕ} (t t' : Mode h) (ht : t ≠ t')
    (u v : Fin 64) (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t', v, y)) = false := by
  simp [host, ht]


-- @@ L120-121 verbatim
@[simp] theorem host_variable_variable {h : ℕ} (v w : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inl w)) = variableEntry v w := rfl


-- @@ L123-125 verbatim
@[simp] theorem host_dummy_variable {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inl v)) = true := rfl


-- @@ L127-129 verbatim
@[simp] theorem host_variable_dummy {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr x)) = true := rfl


-- @@ L131-139 verbatim
theorem rowRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (rowRole t 0 x ∧ rowRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [rowRole]
  · interval_cases e : kind t <;>
      simp [rowRole, e, AtLevel] <;> omega
  · simp [rowRole]


-- @@ L141-149 verbatim
theorem colRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (colRole t 0 x ∧ colRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [colRole]
  · interval_cases e : kind t <;>
      simp [colRole, e, AtLevel] <;> omega
  · simp [colRole]


-- @@ L151-151 verbatim
end Problem348.Construction


-- @@ L153-153 verbatim
end


-- @@ L155-155 verbatim
end OAI
