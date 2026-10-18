import OAI.Analysis.FourierLLogL.Plateau.Output
import OAI.Analysis.FourierLLogL.Finite.Tail


-- @@ L4-4 verbatim
/-! # Finite joint observation moments -/

-- @@ L5-5 verbatim
open Function Set Filter

-- @@ L6-6 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
namespace FourierLLogL.Dyadic.Procedure

-- @@ L11-11 verbatim
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread

-- @@ L12-12 verbatim
variable {M J j : ℕ} {s q : Scene M} {α β : Type} [Fintype α] [Fintype β]

-- @@ L13-13 verbatim
open scoped Classical


-- @@ L15-15 verbatim
def share (s : Scene M) := s.mass/s.norm

-- @@ L16-16 verbatim
def ante (s : Scene M) (x : Grid M) := wt s.here s.wage s.norm x


-- @@ L18-19 verbatim
lemma ante_nonneg (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (x : Grid M) : 0 ≤ ante s x :=
    wt_nonneg _ hs hp _

-- @@ L20-20 verbatim
lemma ante_total (s : Scene M) (hp : s.here.ok M) : ∑ x, ante s x = share s := wt_total _ hp _ _


-- @@ L22-36 verbatim
lemma ante_split (s : Scene M) (hp : s.here.valid) (hM : s.here.lev < M) (x : Grid M) :
    ante (s.smaller false) x + ante (s.smaller true) x=2*ante s x := by
  unfold ante
  simp only [smaller, wt_half hp hM]
  by_cases hh : x∈s.here.block M
  · have h₁ := Set.disjoint_left.mp (s.here.block_separate M)
    rw [block_union] at hh
    rcases hh with hh|hh
    · simp [child,hh,h₁ hh]
    · have h2 : x∉s.here.L.block M := fun he => h₁ he hh
      simp [child,hh,h2]
  · have h (b : Bool) : ¬ x∈(s.here.child b).block M := fun h => hh
      (block_of_below (child_below _ _) _ h)
    simp_rw [ite_eq_right (h _),wt,dice_apply ⟨hp,hM.le⟩,ite_eq_right hh,zero_mul,zero_div]
    ring


-- @@ L38-41 verbatim
lemma share_split (s : Scene M) :
    share (s.smaller false)+share (s.smaller true)=2*share s := by
  unfold share mass; rw [show s.here.avg s.wage = _ from s.here.avg_split_real s.wage]
  dsimp only [smaller,child]; ring


-- @@ L43-43 verbatim
def Packet (M : ℕ) (α : Type) := Grid M → α → ℝ


-- @@ L45-46 verbatim
def addMass (s : Scene M) (k : Grid M → Law α) (x : Grid M) (i : α) :=
    ante s x*k x i


-- @@ L48-49 verbatim
def rung (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℝ) :=
    ∑ x, ∑ i, addMass s k x i * f x i


-- @@ L51-52 verbatim
def rungC (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℂ) :=
    ∑ x, ∑ i, (addMass s k x i:ℂ) * f x i


-- @@ L54-56 verbatim
lemma nonnegative_hist (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (k : Grid M → Law α)
    (z : α) : 0 ≤ hist s k z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ante_nonneg s hs hp _) ((k i).nonneg _)


-- @@ L58-63 verbatim
lemma total_hist (s : Scene M) (hp : s.here.ok M) (k : Grid M → Law α) :
    ∑ z, hist s k z=share s := by
  unfold hist
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Law.total,mul_one]
  exact ante_total s hp


-- @@ L65-69 verbatim
lemma rung_mono (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (k : Grid M → Law α)
    (f g : Grid M → α → ℝ) (h : ∀ i j, f i j ≤ g i j) :
    rung s k f ≤ rung s k g :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _ _)
    (mul_nonneg (ante_nonneg _ hs hp _) ((k _).nonneg _))


-- @@ L71-76 verbatim
lemma rung_const (s : Scene M) (hp : s.here.ok M) (k : Grid M → Law α) (c : ℝ) :
    rung s k (fun _ _ => c) = share s*c := by
  unfold rung; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [← total_hist s hp k]
  rfl


-- @@ L78-80 verbatim
lemma rung_add (s : Scene M) (k : Grid M → Law α) (f g : Grid M → α → ℝ) :
    rung s k (fun i j => f i j + g i j)=rung s k f+rung s k g := by
  unfold rung; simp_rw [mul_add,Finset.sum_add_distrib]


-- @@ L82-85 verbatim
lemma rung_lmul (s : Scene M) (k : Grid M → Law α) (f : Grid M → α → ℝ) (c : ℝ) :
    rung s k (fun i j => c*f i j)=c*rung s k f := by
  unfold rung
  simp_rw [Finset.mul_sum,mul_left_comm c]


-- @@ L87-97 verbatim
lemma rung_error (s : Scene M) (hs : 0 ≤ s.wage) (hp : 0 ≤ s.norm) (hv : s.here.ok M)
    (k : Grid M → Law α) {f g : Grid M → α → ℝ} {r : ℝ}
    (hh : ∀ i j, |f i j-g i j| ≤ r) :
    |rung s k f-rung s k g| ≤ share s*r := by
  have he {f g : Grid M → α → ℝ} (h : ∀ i j, f i j ≤ r+g i j) :
      rung s k f ≤ share s*r+rung s k g := by
    apply le_trans (rung_mono s hs hp _ _ _ h)
    rw [rung_add (f:=fun _ _ => r),rung_const _ hv]
  have h1 := he (f:=f) (g:=g) fun i j => by linarith [(abs_le.mp (hh i j)).2]
  have h2 := he (f:=g) (g:=f) fun i j => by linarith [(abs_le.mp (hh i j)).1]
  rw [abs_le]; constructor <;> linarith


-- @@ L99-102 verbatim
lemma rung_hist (s : Scene M) (k : Grid M → Law α) (f : α→ℝ) :
    ∑ i, hist s k i*f i = rung s k (fun _ i => f i) := by
  unfold rung; rw [Finset.sum_comm]; simp_rw [hist,Finset.sum_mul]
  rfl


-- @@ L104-111 verbatim
lemma rung_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (k : Grid M → Law α) (f : Grid M → α → ℝ) :
    rung (s.smaller false) k f+rung (s.smaller true) k f= 2*rung s k f := by
  unfold rung
  rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; refine Finset.sum_congr rfl fun j _ => ?_
  rw [addMass,addMass,← add_mul,← add_mul,ante_split s hp hh]
  unfold addMass; ring


-- @@ L113-120 verbatim
lemma hist_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (k : Grid M → Law α) (z : α) :
    hist (s.smaller false) k z + hist (s.smaller true) k z = 2*hist s k z := by
  unfold hist; rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have H := ante_split s hp hh i
  unfold ante at H
  rw [← add_mul,H,mul_assoc]


-- @@ L122-128 verbatim
lemma hist_le {s q : Scene M} (h : Less s q) (hs : ReadyAt s) (hh : 0 ≤ s.norm)
    (k : Grid M → Law α) (z : α) :
    hist q k z ≤ hist s k z := by
  unfold hist wt; rw [h.here,h.flat]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ ((k _).nonneg _)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h.antitone hs.2 i)
    ((s.here.dice M).nonneg i)) hh


-- @@ L130-143 verbatim
lemma fisher_range (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (hs : 0 ≤ s.wage) (he : 0 ≤ s.norm) (k : Grid M → Law α) : 0 ≤ fisher s k ∧ fisher s k ≤ share s := by
  have hM := nonnegative_hist s hs he k
  constructor
  exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hM i)
  rw [← total_hist s ⟨hp,hh.le⟩ k]
  apply Finset.sum_le_sum; intro i _
  have h1 (b : Bool) := nonnegative_hist (s.smaller b) hs he k i
  have h2 := hist_split _ hp hh k i
  unfold diff
  rcases eq_or_lt_of_le (hM i) with hm|hm
  · rw [← hm,div_zero]
  apply (div_le_iff₀ hm).mpr
  nlinarith [h1 true,h1 false,mul_nonneg (h1 true) (h1 false)]


-- @@ L145-155 verbatim
lemma fz_split (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (A : Form M) (i z : Grid M) :
    fz s.here.L s.wage s.norm A i z + fz s.here.R s.wage s.norm A i z =
      2*fz s.here s.wage s.norm A i z := by
  unfold fz omegaObs
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have H := ante_split s hp hh x
  simp_rw [ante,smaller,child] at H
  rw [← add_mul,← Complex.ofReal_add,← add_mul,H]
  push_cast; ring


-- @@ L157-157 verbatim
end FourierLLogL.Dyadic.Procedure


-- @@ L159-159 verbatim
end OAI
