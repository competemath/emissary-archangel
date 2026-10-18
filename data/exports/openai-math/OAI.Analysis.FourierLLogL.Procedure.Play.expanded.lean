import OAI.Analysis.FourierLLogL.Procedure.Capital


-- @@ L3-3 verbatim
/-! # The finite spatial and spectral play -/


-- @@ L5-5 verbatim
open Function Set Filter

-- @@ L6-6 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace OAI


-- @@ L11-11 verbatim
namespace FourierLLogL.Dyadic.Procedure

-- @@ L12-12 verbatim
open Law Node Real Period Compress.Params Thermal Fund

-- @@ L13-13 verbatim
open scoped Classical

-- @@ L14-14 verbatim
variable {M J j : ℕ}


-- @@ L16-21 verbatim
structure Scene (M : ℕ) where
  here : Node
  wage : Grid M → ℝ
  fund : Fund M
  live : Bool
  norm : ℝ


-- @@ L23-23 verbatim
def cutoff (j : ℕ) : ℝ := ((j:ℝ)+1)^3


-- @@ L25-25 verbatim
namespace Scene

-- @@ L26-26 verbatim
def mass (s : Scene M) := s.here.avg s.wage

-- @@ L27-29 verbatim
def actor (s : Scene M) : Law (Grid M) :=
    if h : ∃ P : Law (Grid M), PieceLaw s.here s.wage P then Classical.choose h
    else uniform _

-- @@ L30-31 verbatim
def openHere (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) :=
    s.here.lev < J ∧ s.here.avg f ≤ cutoff j ∧ 0 < s.mass

-- @@ L32-33 verbatim
def retire (s : Scene M) (j : ℕ) :=
    s.live=true ∧ (s.fund.breached j ∨ s.mass < exp (-height j))

-- @@ L34-34 verbatim
def enter (s : Scene M) := 2*s.norm < s.mass

-- @@ L35-36 verbatim
def work (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) :=
    s.openHere j J f ∧ ¬ s.retire j ∧ ¬ s.enter

-- @@ L37-39 verbatim
def settled (s : Scene M) (j : ℕ) :=
    s.live=true → ∀ i, i ≤ testIx j →
      ¬ request s.fund.mood j s.here s.wage s.norm (side i) (kappa j (codeWeight capA) i)


-- @@ L41-41 verbatim
def reset (s : Scene M) := {s with norm := s.mass}

-- @@ L42-42 verbatim
def out (s : Scene M) := {s with norm := 0, live := false}

-- @@ L43-43 verbatim
def smaller (s : Scene M) (b : Bool) := {s with here := s.here.child b}

-- @@ L44-47 verbatim
def win (s : Scene M) (u : Update j M s.here) : Scene M :=
    {s with wage := (Set.ofPred (u.take s.fund.mood)).indicator s.wage
            norm := 0
            fund := s.fund.advance s.here u}

-- @@ L48-49 verbatim
def lose (s : Scene M) (u : Update j M s.here) : Scene M :=
    {s with wage := (Set.ofPred fun x => ¬ u.take s.fund.mood x).indicator s.wage}




-- @@ L53-58 verbatim
def beginPlay (f : Grid M → ℝ) (b : Bool) : Scene M :=
    { here:=root
      wage:=f
      fund:=initial M
      live:=b
      norm:=0 }


-- @@ L60-67 verbatim
structure Safe (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) : Prop where
  within : s.here.ok M
  depth_ok : s.here.lev ≤ J
  capital : s.fund.Ok s.here j
  norm_ok : 0 ≤ s.norm
  positive : 0 ≤ s.wage
  sub : s.wage ≤ f
  cut : s.here.avg f ≤ 2*cutoff j


-- @@ L69-69 verbatim
variable {f : Grid M → ℝ} {s : Scene M}


-- @@ L71-76 verbatim
lemma actor_def (hp : s.here.ok M) (hv : 0 ≤ s.wage) (he : 0 < s.mass) :
    PieceLaw s.here s.wage s.actor := by
  unfold actor; split
  · exact Classical.choose_spec _
  · rename_i hh
    exact (hh (make_piece _ hp hv he)).elim


-- @@ L78-79 verbatim
lemma Safe.mass_lower (hh : s.Safe j J f) : 0 ≤ s.mass :=
  avg_nonneg _ (fun x _ => hh.positive x)

-- @@ L80-82 verbatim
lemma Safe.mass_upper (hh : s.Safe j J f) :
    s.mass ≤ s.here.avg f := by
  unfold mass; rw [avg_ex hh.within,avg_ex hh.within]; exact Ex_mono _ hh.sub

-- @@ L83-84 verbatim
lemma Safe.budget (hh : s.Safe j J f) : s.mass ≤ 2*cutoff j :=
    hh.mass_upper.trans hh.cut


-- @@ L86-86 verbatim
end Scene


-- @@ L88-88 verbatim
open Scene


-- @@ L90-97 verbatim
inductive Play (j M : ℕ) : Scene M → Type
| rest (s : Scene M) : Play j M s
| freeze (s : Scene M) (t : Play j M s.out) : Play j M s
| ticket (s : Scene M) (t : Play j M s.reset) : Play j M s
| jump (s : Scene M)
    (l : Play j M (s.smaller false)) (r : Play j M (s.smaller true)) : Play j M s
| attempt (s : Scene M) (u : Update j M s.here)
    (l : Play j M (s.lose u)) (r : Play j M (s.win u)) : Play j M s


-- @@ L99-99 verbatim
namespace Play

-- @@ L100-100 verbatim
variable {s : Scene M}


-- @@ L102-110 verbatim
def Follows (J : ℕ) (f : Grid M → ℝ) : {s : Scene M} → Play j M s → Prop
  | _, .rest s => s.Safe j J f ∧ ¬s.openHere j J f
  | _, .ticket s t => s.Safe j J f ∧ s.openHere j J f ∧ ¬s.retire j ∧
      s.enter ∧ Follows J f t
  | _, .freeze s t => s.Safe j J f ∧ s.openHere j J f ∧ s.retire j ∧ Follows J f t
  | _, .jump s l r => s.Safe j J f ∧ s.work j J f ∧ s.settled j ∧
      Follows J f l ∧ Follows J f r
  | _, .attempt s u l r => s.Safe j J f ∧ s.work j J f ∧ s.live=true ∧
      u.Good capA s.fund.mood s.actor ∧ Follows J f l ∧ Follows J f r


-- @@ L112-112 verbatim
variable {t : Play j M s} {f : Grid M → ℝ}

-- @@ L113-114 verbatim
lemma first (h : t.Follows J f) : s.Safe j J f := by
  cases t <;> exact h.1


-- @@ L116-116 verbatim
end Play

-- @@ L117-117 verbatim
end FourierLLogL.Dyadic.Procedure


-- @@ L119-119 verbatim
end OAI
