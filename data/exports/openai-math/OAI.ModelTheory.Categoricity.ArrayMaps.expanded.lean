import OAI.ModelTheory.Categoricity.Arrays


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace CHObstruction


-- @@ L11-11 verbatim
open Cardinal Ordinal Order


-- @@ L13-13 verbatim
namespace Arrays


-- @@ L15-15 verbatim
section


-- @@ L17-17 verbatim
open Tuples

-- @@ L18-18 verbatim
open scoped symmDiff


-- @@ L20-20 verbatim
variable {M N : Data.{u}} (f : Map M N)

-- @@ L21-21 verbatim
local instance : DecidableEq M.B := Classical.decEq M.B

-- @@ L22-22 verbatim
local instance : DecidableEq N.B := Classical.decEq N.B


-- @@ L24-36 verbatim
private theorem row_action_iff (t t' : Tuple M.I) (n n' : ℕ) (s u s' : Finset M.B) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ n' = n ∧
      f.rowShift t' n' ∆ s'.map f.base.toEmbedding =
        (f.rowShift t n ∆ s.map f.base.toEmbedding) ∆ u.map f.base.toEmbedding) ↔
      (t' = t ∧ n' = n ∧ s' = s ∆ u) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    refine ⟨rfl, rfl, ?_⟩
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj] at h
    exact Finset.map_injective _ h
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by rw [FiniteSupports.map_symmDiff, symmDiff_assoc]⟩


-- @@ L38-47 verbatim
private theorem col_action_iff (t t' : Tuple M.I) (b b' : M.B) (v u v' : Finset ℕ) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ f.base b' = f.base b ∧
      f.colShift t' b' ∆ v' = (f.colShift t b ∆ v) ∆ u) ↔
      (t' = t ∧ b' = b ∧ v' = v ∆ u) := by
  rw [Tuples.map_eq_iff, f.base.injective.eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, by simpa only [symmDiff_assoc, symmDiff_right_inj] using h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (symmDiff_assoc _ _ _).symm⟩


-- @@ L49-60 verbatim
private theorem bit_relation_iff (t t' : Tuple M.I) (n : ℕ) (b : M.B)
    (s : Finset M.B) (v : Finset ℕ) :
    (Tuples.map f.index t = Tuples.map f.index t' ∧
      Matrix.bit (N.bits (Tuples.map f.index t)) n
        (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t' b ∆ v) = true) ↔
      (t = t' ∧ Matrix.bit (M.bits t) n s b v = true) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩


-- @@ L62-66 verbatim
private theorem group_add_iff (s t w : Finset M.B) :
    w.map f.base.toEmbedding = s.map f.base.toEmbedding ∆ t.map f.base.toEmbedding ↔
      w = s ∆ t := by
  rw [← FiniteSupports.map_symmDiff]
  exact (Finset.map_injective _).eq_iff


-- @@ L68-69 verbatim
attribute [local simp] Data.rawRel Map.onPoint group_add_iff row_action_iff
  col_action_iff bit_relation_iff


-- @@ L71-77 verbatim
private theorem raw_map_index (xs : List M.Carrier) :
    N.rawRel (.index) (xs.map f.onPoint) ↔ M.rawRel (.index) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L79-85 verbatim
private theorem raw_map_base (xs : List M.Carrier) :
    N.rawRel (.base) (xs.map f.onPoint) ↔ M.rawRel (.base) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L87-93 verbatim
private theorem raw_map_group (xs : List M.Carrier) :
    N.rawRel (.group) (xs.map f.onPoint) ↔ M.rawRel (.group) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L95-101 verbatim
private theorem raw_map_star (xs : List M.Carrier) :
    N.rawRel (.star) (xs.map f.onPoint) ↔ M.rawRel (.star) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L103-109 verbatim
private theorem raw_map_row (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.row k n) (xs.map f.onPoint) ↔ M.rawRel (.row k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L111-117 verbatim
private theorem raw_map_col (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.col k) (xs.map f.onPoint) ↔ M.rawRel (.col k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L119-125 verbatim
private theorem raw_map_label (s : Finset ℕ) (xs : List M.Carrier) :
    N.rawRel (.label s) (xs.map f.onPoint) ↔ M.rawRel (.label s) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp


-- @@ L127-135 verbatim
private theorem raw_map_order (xs : List M.Carrier) :
    N.rawRel (.order) (xs.map f.onPoint) ↔ M.rawRel (.order) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp


-- @@ L137-145 verbatim
private theorem raw_map_incidence (xs : List M.Carrier) :
    N.rawRel (.incidence) (xs.map f.onPoint) ↔ M.rawRel (.incidence) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp


-- @@ L147-157 verbatim
private theorem raw_map_bit (xs : List M.Carrier) :
    N.rawRel (.bit) (xs.map f.onPoint) ↔ M.rawRel (.bit) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
    rintro rfl
    exact f.bit_all _ _ _ _ _
  · cases x <;> cases y <;> simp


-- @@ L159-169 verbatim
private theorem raw_map_groupAdd (xs : List M.Carrier) :
    N.rawRel (.groupAdd) (xs.map f.onPoint) ↔ M.rawRel (.groupAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp


-- @@ L171-181 verbatim
private theorem raw_map_starAdd (xs : List M.Carrier) :
    N.rawRel (.starAdd) (xs.map f.onPoint) ↔ M.rawRel (.starAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp


-- @@ L183-196 verbatim
private theorem raw_map_rowAct (xs : List M.Carrier) :
    N.rawRel (.rowAct) (xs.map f.onPoint) ↔ M.rawRel (.rowAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj]
    exact (Finset.map_injective _).eq_iff
  · cases x <;> cases y <;> cases z <;> simp


-- @@ L198-210 verbatim
private theorem raw_map_colAct (xs : List M.Carrier) :
    N.rawRel (.colAct) (xs.map f.onPoint) ↔ M.rawRel (.colAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, symmDiff_right_inj]
  · cases x <;> cases y <;> cases z <;> simp


-- @@ L212-220 verbatim
private theorem tuple_list_eq_iff (t : Tuple M.I) (xs : List M.Carrier) :
    xs.map f.onPoint = List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) ↔
      xs = List.ofFn (fun i => Point.index (t.2 i)) := by
  have he : List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) =
      (List.ofFn (fun i => Point.index (t.2 i))).map f.onPoint := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  exact f.injective.list_map.eq_iff


-- @@ L222-225 verbatim
private theorem base_point_eq_iff (x : M.Carrier) (b : M.B) :
    f.onPoint x = Point.base (f.base b) ↔ x = Point.base b := by
  change f.onPoint x = f.onPoint (.base b) ↔ _
  exact f.injective.eq_iff


-- @@ L227-233 verbatim
private theorem raw_map_rowProjection (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.rowProjection k n) (xs.map f.onPoint) ↔ M.rawRel (.rowProjection k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  cases x <;> simp
  intro _ _
  simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ xs


-- @@ L235-244 verbatim
private theorem raw_map_colProjection (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.colProjection k) (xs.map f.onPoint) ↔ M.rawRel (.colProjection k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, ys⟩
  · cases x <;> simp
  cases x <;> simp
  intro _
  exact and_congr (base_point_eq_iff f y _) (by
    simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ ys)


-- @@ L246-264 verbatim
theorem Map.rawRel (s : Symbol) (xs : List M.Carrier) :
    N.rawRel s (xs.map f.onPoint) ↔ M.rawRel s xs := by
  cases s with
  | index => exact raw_map_index f xs
  | base => exact raw_map_base f xs
  | group => exact raw_map_group f xs
  | star => exact raw_map_star f xs
  | row k n => exact raw_map_row f k n xs
  | col k => exact raw_map_col f k xs
  | label v => exact raw_map_label f v xs
  | rowProjection k n => exact raw_map_rowProjection f k n xs
  | colProjection k => exact raw_map_colProjection f k xs
  | order => exact raw_map_order f xs
  | incidence => exact raw_map_incidence f xs
  | bit => exact raw_map_bit f xs
  | groupAdd => exact raw_map_groupAdd f xs
  | starAdd => exact raw_map_starAdd f xs
  | rowAct => exact raw_map_rowAct f xs
  | colAct => exact raw_map_colAct f xs


-- @@ L266-268 verbatim
theorem Map.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) :
    N.rel n s (f.onPoint ∘ a) ↔ M.rel n s a := by
  simpa only [Data.rel, List.map_ofFn] using f.rawRel s.val (List.ofFn a)


-- @@ L270-270 verbatim
end


-- @@ L272-272 verbatim
open Tuples

-- @@ L273-273 verbatim
open scoped symmDiff


-- @@ L275-275 verbatim
variable {M N P : Data.{u}}

-- @@ L276-276 verbatim
local instance : DecidableEq M.B := Classical.decEq M.B

-- @@ L277-277 verbatim
local instance : DecidableEq N.B := Classical.decEq N.B

-- @@ L278-278 verbatim
local instance : DecidableEq P.B := Classical.decEq P.B


-- @@ L280-285 verbatim
def Map.id (M : Data.{u}) : Map M M where
  index := Function.Embedding.refl _
  base := (OrderIso.refl _).toOrderEmbedding
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees t n b := by simp [Matrix.bit]


-- @@ L287-295 verbatim
def Map.comp (g : Map N P) (f : Map M N) : Map M P where
  index := f.index.trans g.index
  base := f.base.trans g.base
  rowShift t n := g.rowShift (Tuples.map f.index t) n ∆
    (f.rowShift t n).map g.base.toEmbedding
  colShift t b := g.colShift (Tuples.map f.index t) (f.base b) ∆ f.colShift t b
  bit_agrees t n b := by
    exact (g.bit_all (Tuples.map f.index t) n (f.rowShift t n) (f.base b)
      (f.colShift t b)).trans (f.bit_agrees t n b)


-- @@ L297-299 verbatim
@[simp] theorem Map.id_onPoint (M : Data.{u}) (x : M.Carrier) : (Map.id M).onPoint x = x := by
  have he : (OrderIso.refl M.B).toOrderEmbedding.toEmbedding = Function.Embedding.refl M.B := rfl
  cases x <;> simp [Map.id, Map.onPoint, he]


-- @@ L301-304 verbatim
@[simp] theorem Map.comp_onPoint (g : Map N P) (f : Map M N) (x : M.Carrier) :
    (g.comp f).onPoint x = g.onPoint (f.onPoint x) := by
  have he : (f.base.trans g.base).toEmbedding = f.base.toEmbedding.trans g.base.toEmbedding := rfl
  cases x <;> simp [Map.comp, Map.onPoint, Finset.map_map, symmDiff_assoc, he]


-- @@ L306-327 verbatim
theorem Map.ext_onPoint {f g : Map M N} (h : ∀ x, f.onPoint x = g.onPoint x) : f = g := by
  have hi : f.index = g.index := by
    ext i
    exact Point.index.inj (h (.index i))
  have hb : f.base = g.base := by
    ext b
    exact Point.base.inj (h (.base b))
  have hr : f.rowShift = g.rowShift := by
    funext t n
    have he := (Point.row.inj (h (.row t n ∅))).2.2
    simpa using he
  have hc : f.colShift = g.colShift := by
    funext t b
    have he := (Point.col.inj (h (.col t b ∅))).2.2
    simpa using he
  cases f
  cases g
  cases hi
  cases hb
  cases hr
  cases hc
  rfl


-- @@ L329-330 verbatim
@[simp] theorem Map.comp_id (f : Map M N) : f.comp (Map.id M) = f :=
  Map.ext_onPoint (fun x => by simp)


-- @@ L332-333 verbatim
@[simp] theorem Map.id_comp (f : Map M N) : (Map.id N).comp f = f :=
  Map.ext_onPoint (fun x => by simp)


-- @@ L335-335 verbatim
end Arrays


-- @@ L337-337 verbatim
end CHObstruction


-- @@ L339-339 verbatim
end


-- @@ L341-341 verbatim
end OAI
