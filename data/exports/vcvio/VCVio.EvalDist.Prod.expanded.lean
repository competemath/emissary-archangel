/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Seq
public import ToMathlib.Data.ENNReal.SumSquares


-- @@ L11-15 verbatim
/-!
# Evaluation Distributions of Computations with `Prod`

Lemmas about `evalSPMF` and `support` involving `Prod`, ported to generic `[MonadLiftT m SPMF]`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open ENNReal Prod


-- @@ L21-21 verbatim
universe u v


-- @@ L23-24 verbatim
variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m SPMF]
  [LawfulMonadLiftT m SPMF] {α β γ δ : Type u}


-- @@ L26-29 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
omit [LawfulMonad m] in
lemma probOutput_prod_mk_eq_probEvent (mx : m (α × β)) (x : α) (y : β) :
    probOutput mx (x, y) = probEvent mx fun z => z.1 = x ∧ z.2 = y := by grind


-- @@ L31-36 expanded
@[grind =]
lemma probOutput_fst_map_eq_tsum (mx : m (α × β)) (x : α) :
    probOutput (Prod.fst <$> mx) x = ∑' y, probOutput mx (x, y) := by
  classical
  simp only [probOutput_map_eq_tsum_ite, ENNReal.tsum_prod']
  refine (tsum_eq_single x fun a ha => by simp [Ne.symm ha]).trans (by simp)


-- @@ L38-41 expanded
@[grind =]
lemma probOutput_fst_map_eq_sum [Fintype β] (mx : m (α × β)) (x : α) :
    probOutput (Prod.fst <$> mx) x = ∑ y, probOutput mx (x, y) := by
  rw [probOutput_fst_map_eq_tsum, tsum_fintype]


-- @@ L43-48 expanded
@[grind =]
lemma probOutput_snd_map_eq_tsum (mx : m (α × β)) (y : β) :
    probOutput (Prod.snd <$> mx) y = ∑' x, probOutput mx (x, y) := by
  classical
  simp only [probOutput_map_eq_tsum_ite, ENNReal.tsum_prod']
  refine tsum_congr fun _ => (tsum_eq_single y fun b hb => by simp [Ne.symm hb]).trans (by simp)


-- @@ L50-53 expanded
@[grind =]
lemma probOutput_snd_map_eq_sum [Fintype α] (mx : m (α × β)) (y : β) :
    probOutput (Prod.snd <$> mx) y = ∑ x, probOutput mx (x, y) := by
  rw [probOutput_snd_map_eq_tsum, tsum_fintype]


-- @@ L55-57 expanded
@[grind =]
lemma probOutput_fst_map_eq_probEvent (mx : m (α × β)) (x : α) :
    probOutput (Prod.fst <$> mx) x = probEvent mx fun z => z.1 = x := by grind


-- @@ L59-62 expanded
/-- Unlike `probEvent_map` this unfolds the function composition automatically. -/
@[simp high, grind =]
lemma probEvent_fst_map (mx : m (α × β)) (p : α → Prop) :
    probEvent (Prod.fst <$> mx) p = probEvent mx fun x => p x.1 := by grind


-- @@ L64-66 expanded
@[grind =]
lemma probOutput_snd_map_eq_probEvent (mx : m (α × β)) (y : β) :
    probOutput (Prod.snd <$> mx) y = probEvent mx fun z => z.2 = y := by grind


-- @@ L68-71 expanded
/-- Unlike `probEvent_map` this unfolds the function composition automatically. -/
@[simp high, grind =]
lemma probEvent_snd_map (mx : m (α × β)) (p : β → Prop) :
    probEvent (Prod.snd <$> mx) p = probEvent mx fun y => p y.2 := by grind


-- @@ L73-80 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
omit [LawfulMonad m] in
@[simp, grind =]
lemma probEvent_fst_eq_snd (mx : m (α × α)) :
    (probEvent mx fun z => z.1 = z.2) = ∑' x : α, probOutput mx (x, x) := by
  classical
  rw [probEvent_eq_tsum_ite, ENNReal.tsum_prod']
  simp


-- @@ L82-82 verbatim
section prod_mk


-- @@ L84-89 verbatim
variable (mx : m α) (my : m β) (f : α → γ) (g : β → δ)

/- `@[grind norm]` (not `@[grind =]`): `Seq.seq`'s thunk argument makes the LHS an invalid
E-matching pattern, but `grind`'s simp-based normalization phase needs no pattern indexing. This
lets bare `grind` factor an independent applicative product (and e.g. close equiprobability of a
uniform product), which E-matching alone cannot. -/

-- @@ L90-93 expanded
@[simp high, grind norm]
lemma probOutput_seq_map_prod_mk_eq_mul (z : α × β) :
    probOutput (Prod.mk <$> mx <*> my) z = probOutput mx z.1 * probOutput my z.2 :=
  probOutput_seq_map_eq_mul_of_injective2 mx my Prod.mk Prod.mk.injective2 z.1 z.2


-- @@ L95-99 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[simp high]
lemma support_seq_map_prod_mk [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    support (Prod.mk <$> mx <*> my) = support mx ×ˢ support my := by
  simp [Set.ext_iff]


-- @@ L101-105 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
lemma finSupport_seq_map_prod_mk [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [HasEvalFinset m] [DecidableEq α] [DecidableEq β] :
    finSupport (Prod.mk <$> mx <*> my) = Finset.product (finSupport mx) (finSupport my) := by
  simp


-- @@ L107-112 expanded
@[simp]
lemma probOutput_seq_map_prod_mk_map_eq_mul (z : γ × δ) :
    probOutput ((f ·, g ·) <$> mx <*> my) z =
      probOutput (f <$> mx) z.1 * probOutput (g <$> my) z.2 :=
  by
  have hseq : (f ·, g ·) <$> mx <*> my = Prod.mk <$> (f <$> mx) <*> (g <$> my) := by
    simp [seq_eq_bind_map, Functor.map_map]
  rw [hseq, probOutput_seq_map_prod_mk_eq_mul]


-- @@ L114-119 expanded
@[simp]
lemma probOutput_seq_map_prod_mk_map_eq_mul' (z : γ × δ) :
    probOutput ((fun y x => (f x, g y)) <$> my <*> mx) z =
      probOutput (f <$> mx) z.1 * probOutput (g <$> my) z.2 :=
  by
  rw [← probOutput_seq_map_swap]
  simp


-- @@ L121-124 expanded
@[simp]
lemma probOutput_bind_map_prod_mk_eq_mul (z : γ × δ) :
    probOutput
        (do
          let x ← mx;
          (f x, g ·) <$> my)
        z =
      probOutput (f <$> mx) z.1 * probOutput (g <$> my) z.2 :=
  by simpa [monad_norm] using probOutput_seq_map_prod_mk_map_eq_mul mx my f g z


-- @@ L126-130 expanded
@[simp]
lemma probOutput_bind_map_prod_mk_eq_mul' (mx : m α) (my : m β) (f : α → γ) (g : β → δ)
    (z : γ × δ) :
    probOutput
        (do
          let y ← my;
          (f ·, g y) <$> mx)
        z =
      probOutput (f <$> mx) z.1 * probOutput (g <$> my) z.2 :=
  by simpa [monad_norm] using probOutput_seq_map_prod_mk_map_eq_mul' mx my f g z


-- @@ L132-136 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[simp high]
lemma support_seq_map_prod_mk_eq_sprod [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    support ((f ·, g ·) <$> mx <*> my) = (f '' support mx) ×ˢ (g '' support my) := by
  simp [Set.ext_iff]; grind


-- @@ L138-143 verbatim
omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
lemma finSupport_seq_map_prod_mk_eq_product [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] : finSupport ((f ·, g ·) <$> mx <*> my) =
      ((finSupport mx).image f).product ((finSupport my).image g) := by
  simp [Finset.ext_iff]; grind


-- @@ L145-148 expanded
lemma probOutput_bind_bind_prod_mk_eq_mul (mx : m α) (my : m β) (f : α → γ) (g : β → δ)
    (z : γ × δ) :
    probOutput
        (do
          let x ← mx;
          let y ← my;
          return (f x, g y))
        z =
      probOutput (f <$> mx) z.1 * probOutput (g <$> my) z.2 :=
  by simp


-- @@ L150-153 expanded
lemma probOutput_bind_bind_prod_mk_eq_mul' (mx : m α) (my : m β) (f : α → γ) (g : β → δ) (x : γ)
    (y : δ) :
    probOutput
        (do
          let a ← mx;
          let b ← my;
          return (f a, g b))
        (x, y) =
      probOutput (f <$> mx) x * probOutput (g <$> my) y :=
  by simp


-- @@ L155-181 expanded
/-- Two conditionally independent executions dominate the square of the
corresponding single-execution output probability. -/
lemma sq_probOutput_bind_le_probOutput_bind_prod (source : m α) (kernel : α → m β) (y : β) :
    probOutput (source >>= kernel) y ^ 2 ≤
      probOutput
        (source >>= fun x => do
          let a ← kernel x
          let b ← kernel x
          pure (a, b))
        (y, y) :=
  by
  have hfactor (x : α) :
    probOutput
        (do
          let a ← kernel x
          let b ← kernel x
          pure (a, b))
        (y, y) =
      probOutput (kernel x) y * probOutput (kernel x) y :=
    by
    rw [probOutput_bind_bind_prod_mk_eq_mul']
    simp only [show (fun a : β ↦ a) = id from rfl, id_map]
  rw [probOutput_bind_eq_tsum source kernel y,
    probOutput_bind_eq_tsum source
      (fun x ↦ do
        let a ← kernel x
        let b ← kernel x
        pure (a, b))
      (y, y)]
  refine
    (ENNReal.sq_tsum_le_tsum_sq (fun x ↦ probOutput source x) (fun x ↦ probOutput (kernel x) y)
          (tsum_probOutput_le_one (mx := source))).trans_eq
      ?_
  refine tsum_congr fun x ↦ ?_
  rw [hfactor]
  simp [sq]


-- @@ L183-189 expanded
@[simp]
lemma probOutput_prod_mk_fst_map [DecidableEq β] (mx : m α) (y : β) (z : α × β) :
    probOutput ((·, y) <$> mx) z = if z.2 = y then probOutput mx z.1 else 0 :=
  calc
    probOutput ((·, y) <$> mx) z
    _ = probOutput (Prod.mk <$> mx <*> pure y) z := by simp; rfl
    _ = if z.2 = y then probOutput mx z.1 else 0 := by
      simp only [probOutput_seq_map_prod_mk_eq_mul, probOutput_pure, mul_ite, mul_one, mul_zero]


-- @@ L191-197 expanded
@[simp]
lemma probOutput_prod_mk_snd_map [DecidableEq α] (my : m β) (x : α) (z : α × β) :
    probOutput ((x, ·) <$> my) z = if z.1 = x then probOutput my z.2 else 0 :=
  calc
    probOutput ((x, ·) <$> my) z
    _ = probOutput (Prod.mk <$> pure x <*> my) z := by simp [seq_eq_bind_map]; rfl
    _ = if z.1 = x then probOutput my z.2 else 0 := by
      simp only [probOutput_seq_map_prod_mk_eq_mul, probOutput_pure, ite_mul, one_mul, zero_mul]


-- @@ L199-199 verbatim
end prod_mk
