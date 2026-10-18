import OAI.Analysis.FourierLLogL.Dyadic.Discrete


-- @@ L3-3 verbatim
/-! # Signed combination spans and Fourier support -/

-- @@ L4-4 verbatim
open Function Set Filter

-- @@ L5-5 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
namespace FourierLLogL.Dyadic

-- @@ L10-10 verbatim
open Law Period Real

-- @@ L11-11 verbatim
variable {M : ℕ}


-- @@ L13-14 verbatim
def enclosed (s : Finset (Grid M)) (n : ℕ) (x : Grid M) : Prop :=
    ∃ f : Grid M → ℤ, (∀ i∈s, |f i| ≤ n) ∧ ∑ i∈s, f i • i = x


-- @@ L16-17 verbatim
lemma enclosed_zero (s : Finset (Grid M)) (n : ℕ) : enclosed s n 0 :=
  ⟨fun _ => 0,by simp,by simp⟩


-- @@ L19-22 verbatim
lemma enclosed_mem (s : Finset (Grid M)) {x : Grid M} (hx : x∈s) : enclosed s 1 x := by
  refine ⟨fun i => if i=x then 1 else 0,fun i hi => ?_,?_⟩
  · dsimp only; split_ifs <;> norm_num
  simp [ite_smul,hx]


-- @@ L24-29 verbatim
lemma enclosed_neg {s : Finset (Grid M)} {n : ℕ} {x : Grid M} (h : enclosed s n x) :
    enclosed s n (-x) := by
  obtain ⟨f,hf,rfl⟩ := h
  refine ⟨fun i => -f i,fun i hi => ?_,?_⟩
  · simpa only [abs_neg] using hf i hi
  simp


-- @@ L31-38 verbatim
lemma enclosed_add {s : Finset (Grid M)} {n m : ℕ} {x y : Grid M} (h : enclosed s n x)
    (h' : enclosed s m y) : enclosed s (n+m) (x+y) := by
  obtain ⟨f,hf,rfl⟩ := h
  obtain ⟨g,hg,rfl⟩ := h'
  refine ⟨fun i => f i + g i,fun i hi => ?_,?_⟩
  · rw [Nat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (hf _ hi) (hg _ hi))
  simp [add_smul,Finset.sum_add_distrib]


-- @@ L40-52 verbatim
lemma enclosed_insert {s : Finset (Grid M)} {i x : Grid M} (hi : i ∉ s)
    {n : ℕ} (h : enclosed s n x) (j : ℤ) (hj : |j| ≤ n) :
    enclosed (insert i s) n (x+j•i) := by
  obtain ⟨f,hf,rfl⟩ := h
  refine ⟨fun k => if k=i then j else f k,?_,?_⟩
  · intro k hk
    dsimp only
    split_ifs with h
    · exact hj
    · exact hf _ ((Finset.mem_insert.mp hk).resolve_left h)
  · rw [Finset.sum_insert hi]; dsimp only; rw [ite_eq_left rfl,add_comm _ (j • i)]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [ite_eq_right (by intro he; exact hi (he ▸ hk))]


-- @@ L54-63 verbatim
lemma enclosed_sum {α : Type*} [Fintype α] (s : Finset (Grid M)) (X : α → Grid M)
    (h : ∀ x, enclosed s 1 (X x)) :
    enclosed s (Fintype.card α) (∑ i, X i) := by
  classical
  suffices HH : ∀ t : Finset α, enclosed s t.card (∑ i∈t, X i) from HH _
  intro t; induction t using Finset.induction_on with
  | empty => simp [enclosed_zero]
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,add_comm t.card]
    exact enclosed_add (h _) ih


-- @@ L65-65 verbatim
open scoped Classical


-- @@ L67-67 verbatim
def palace (s : Finset (Grid M)) (n : ℕ) := Finset.univ.filter (enclosed s n)


-- @@ L69-83 verbatim
lemma palace_size (s : Finset (Grid M)) (n : ℕ) : (palace s n).card ≤ (2*n+1)^s.card := by
  classical
  let t : Finset ℤ := Finset.Icc (-(n:ℤ)) n
  let f (w : s → (t:Type)) := ∑ i : s, (w i).val • (i:Grid M)
  have hs : palace s n ⊆ Finset.univ.image f := by
    intro i hi
    obtain ⟨g,hg,he⟩ := (Finset.mem_filter.mp hi).2
    let w (i : s) : t := ⟨g i, Finset.mem_Icc.mpr (abs_le.mp (hg _ i.property))⟩
    refine Finset.mem_image.mpr ⟨w,Finset.mem_univ _,?_⟩
    rw [← he,← Finset.sum_attach s]
    simp only [f,w]; rfl
  apply le_trans ((Finset.card_le_card hs).trans Finset.card_image_le)
  simp only [Finset.card_univ, Fintype.card_fun,Fintype.card_coe]
  have He : t.card = 2*n+1 := by simp [t]; omega
  rw [He]


-- @@ L85-88 verbatim
/-- The Fourier coefficients are supported within a bandwidth of the signed span. This
form (arbitrary thickening of our unthickened case) will also be used for broad capture. -/
def spanned (s : Finset (Grid M)) (f : Grid M → ℂ) : Prop :=
    ∀ i, ¬enclosed s 1 i → fc f i=0


-- @@ L90-94 verbatim
lemma spanned_one (s : Finset (Grid M)) : spanned s 1 := by
  intro i hi
  have hn : i≠0 := fun he => hi (he ▸ enclosed_zero s 1)
  change fc (fun x => 1) i = 0
  rw [← funext chi_zero_left,fc_chi,ite_eq_right hn.symm]


-- @@ L96-105 verbatim
private lemma fc_real_step (f : Grid M → ℂ) (c : ℂ) (s i : Grid M) :
    fc (fun x => f x * (↑((c*chi s x).re):ℂ)) i =
      2⁻¹*(c*fc f (i-s)+conj c*fc f (i+s)) := by
  have he (x : Grid M) :
    f x * (↑((c*chi s x).re):ℂ) = 2⁻¹ *
      (c*(f x*chi s x) + (conj c)*(f x * chi (-s) x)) := by
    rw [Complex.re_eq_add_conj,map_mul,chi_neg']
    ring
  simp_rw [he]; rw [fc_lmul,fc_add, fc_lmul,fc_lmul, fc_mul_chi,fc_mul_chi]
  rw [sub_neg_eq_add]


-- @@ L107-111 verbatim
lemma expand_one_step (f : Grid M → ℂ) (c : ℂ) (s i : Grid M) :
    fc (fun x => f x * (1 + (↑((c*chi s x).re):ℂ))) i =
      fc f i + 2⁻¹*(c*fc f (i-s)+conj c*fc f (i+s)) := by
  simp_rw [mul_add,mul_one,fc_add,fc_real_step]
  ring


-- @@ L113-133 verbatim
lemma span_augment {f : Grid M → ℂ} {u : Finset (Grid M)} (h : spanned u f)
    (c : ℂ) (s : Grid M) (hs : ¬ enclosed u 1 s) :
    let g := fun x : Grid M => f x * (1+(↑((c*chi s x).re):ℂ))
    spanned (insert s u) g ∧ fc g 0 = fc f 0 := by
  have hx : s ∉ u := fun h => hs (enclosed_mem _ h)
  intro g
  have ha (i : Grid M) := expand_one_step f c s i
  constructor
  · intro i hi
    have hA : ¬ enclosed u 1 i := by
      intro he
      apply hi; simpa using enclosed_insert hx he 0 (by norm_num)
    have hB : ¬ enclosed u 1 (i-s) := by
      intro he
      apply hi; simpa using enclosed_insert hx he 1 (by norm_num)
    have hC : ¬ enclosed u 1 (i+s) := by
      intro he
      apply hi; simpa using enclosed_insert hx he (-1) (by norm_num)
    rw [ha i,h _ hA,h _ hB,h _ hC]; ring
  · have hs' : ¬ enclosed u 1 (-s) := fun he => hs (by simpa using enclosed_neg he)
    rw [ha 0, zero_add, zero_sub,h _ hs,h _ hs']; ring


-- @@ L135-135 verbatim
end FourierLLogL.Dyadic


-- @@ L137-137 verbatim
end OAI
