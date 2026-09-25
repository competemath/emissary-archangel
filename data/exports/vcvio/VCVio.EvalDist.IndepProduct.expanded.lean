/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Expectation


-- @@ L10-23 verbatim
/-!
# Independent products of computations

`Fin.mOfFn n g` runs `g 0, …, g (n - 1)` in order and collects the results as a function
`Fin n → α`; `Fintype.mPi f` is the same product over an arbitrary finite index type, transported
along `Fintype.equivFin`. No factor sees another's result, so the joint output distribution is the
product of the factor distributions: `probOutput_mOfFn` and `probOutput_mPi`.

Two consequences are what callers want. The support is coordinatewise (`mem_support_mOfFn`), and a
single coordinate marginalizes back to its own factor (`probEvent_coord_mOfFn`,
`probEvent_coord_mPi`). The marginal is an *equality* only when the remaining factors carry full
mass, since a factor that can fail removes mass from every coordinate at once; without that
hypothesis only `probEvent_coord_mOfFn_le` holds.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open scoped ENNReal


-- @@ L29-29 verbatim
universe u v w


-- @@ L31-31 verbatim
variable {α : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]


-- @@ L33-33 verbatim
/-! ## Support -/


-- @@ L35-35 verbatim
section support


-- @@ L37-37 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L39-55 verbatim
omit [LawfulMonad m] in
/-- Every coordinate of an output of an independent product lies in the support of its factor. -/
lemma mem_support_mOfFn (n : ℕ) (g : Fin n → m α) (v : Fin n → α)
    (hv : v ∈ support (Fin.mOfFn n g)) (i : Fin n) : v i ∈ support (g i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [Fin.mOfFn, mem_support_bind_iff] at hv
      obtain ⟨a, ha, hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨rest, hrest, hv⟩ := hv
      simp only [support_pure, Set.mem_singleton_iff] at hv
      subst hv
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · rw [Fin.cons_succ]
        exact ih (fun j => g j.succ) rest hrest j


-- @@ L57-57 verbatim
end support


-- @@ L59-59 verbatim
/-! ## Output probabilities -/


-- @@ L61-61 verbatim
section probOutput


-- @@ L63-63 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L65-111 expanded
omit [LawfulMonad m] in
/-- The output distribution of an independent product is the product of the factor
distributions. -/
lemma probOutput_mOfFn (n : ℕ) (g : Fin n → m α) (v : Fin n → α) :
    probOutput (Fin.mOfFn n g) v = ∏ i, probOutput (g i) (v i) := by
  classical
    induction n with
  | zero =>
    have hv : v = Fin.elim0 := funext fun i => i.elim0
    subst hv
    simp [Fin.mOfFn]
  | succ n
    ih =>
    have hcons :
      ∀ (a : α) (rest : Fin n → α), (v = Fin.cons a rest) ↔ (a = v 0 ∧ rest = Fin.tail v) :=
      by
      intro a rest
      constructor
      · intro hEq
        refine ⟨by rw [hEq, Fin.cons_zero], funext fun k => ?_⟩
        have hk := congrFun hEq k.succ
        rw [Fin.cons_succ] at hk
        exact hk.symm
      · rintro ⟨rfl, rfl⟩
        exact (Fin.cons_self_tail v).symm
    have hinner :
      ∀ a : α,
        probOutput
            ((Fin.mOfFn n fun i => g i.succ) >>= fun rest =>
              (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
            v =
          if a = v 0 then probOutput (Fin.mOfFn n fun i => g i.succ) (Fin.tail v) else 0 :=
      by
      intro a
      rw [probOutput_bind_eq_tsum]
      by_cases ha : a = v 0
      · rw [if_pos ha]
        refine (tsum_eq_single (Fin.tail v) fun rest hrest => ?_).trans ?_
        · rw [probOutput_pure, if_neg (fun h => hrest ((hcons a rest).mp h).2), mul_zero]
        · rw [probOutput_pure, if_pos ((hcons a (Fin.tail v)).mpr ⟨ha, rfl⟩), mul_one]
      · rw [if_neg ha]
        have hzero :
          ∀ rest : Fin n → α,
            probOutput (Fin.mOfFn n fun i => g i.succ) rest *
                probOutput (pure (Fin.cons a rest) : m (Fin (n + 1) → α)) v =
              0 :=
          by
          intro rest
          rw [probOutput_pure, if_neg (fun h => ha ((hcons a rest).mp h).1), mul_zero]
        simp only [hzero, tsum_zero]
    simp only [Fin.mOfFn]
    rw [probOutput_bind_eq_tsum]
    simp only [hinner, mul_ite, mul_zero]
    rw [tsum_eq_single (v 0) (fun a ha => if_neg ha), if_pos rfl,
      ih (fun i => g i.succ) (Fin.tail v), Fin.prod_univ_succ]
    rfl


-- @@ L113-154 expanded
omit [LawfulMonad m] in
/-- A coordinatewise conjunction of events factors as a product over the coordinates. This is the
form the joint law is usually consumed in: `probOutput_mOfFn` is the case where each coordinate is
pinned to a value, and `probEvent_coord_mOfFn` the case where all but one are trivial. No
full-mass hypothesis is needed, since a factor that fails simply contributes its own deficient
mass to the product. -/
lemma probEvent_forall_coord_mOfFn (n : ℕ) (g : Fin n → m α) (p : (i : Fin n) → α → Prop) :
    (probEvent (Fin.mOfFn n g) fun v => ∀ i, p i (v i)) = ∏ i, probEvent (g i) (p i) := by
  classical
    induction n with
  | zero => simp [Fin.mOfFn]
  | succ n
    ih =>
    have hinner :
      ∀ a : α,
        (probEvent
            ((Fin.mOfFn n fun i => g i.succ) >>= fun rest =>
              (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
            fun v => ∀ i, p i (v i)) =
          if p 0 a then
            probEvent (Fin.mOfFn n fun i => g i.succ) fun rest : Fin n → α => ∀ j, p j.succ (rest j)
          else 0 :=
      by
      intro a
      rw [probEvent_bind_eq_tsum]
      by_cases ha : p 0 a
      · rw [if_pos ha, probEvent_eq_tsum_ite]
        refine tsum_congr fun rest => ?_
        simp only [probEvent_pure, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ha, true_and]
        split <;> simp
      · rw [if_neg ha]
        have hzero :
          ∀ rest : Fin n → α,
            (probOutput (Fin.mOfFn n fun i => g i.succ) rest *
                probEvent (pure (Fin.cons a rest) : m (Fin (n + 1) → α)) fun v => ∀ i, p i (v i)) =
              0 :=
          by
          intro rest
          simp only [probEvent_pure, Fin.forall_fin_succ, Fin.cons_zero, ha, false_and, if_false,
            mul_zero]
        simp only [hzero, tsum_zero]
    simp only [Fin.mOfFn]
    rw [probEvent_bind_eq_tsum]
    simp only [hinner]
    rw [Fin.prod_univ_succ, ← ih (fun i => g i.succ) (fun j => p j.succ),
      probEvent_eq_tsum_ite (g 0) (p 0), ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    split <;> simp


-- @@ L156-165 expanded
/-- An independent product never fails when none of its factors can. -/
lemma probFailure_mOfFn (n : ℕ) (g : Fin n → m α) (hg : ∀ i, probFailure (g i) = 0) :
    probFailure (Fin.mOfFn n g) = 0 := by
  induction n with
  | zero => simp [Fin.mOfFn]
  | succ n
    ih =>
    have htail : probFailure (Fin.mOfFn n fun i => g i.succ) = 0 := ih _ (fun i => hg i.succ)
    simp only [Fin.mOfFn]
    rw [probFailure_bind_of_probFailure_eq_zero (hg 0)]
    simp [htail]


-- @@ L167-167 verbatim
end probOutput


-- @@ L169-169 verbatim
/-! ## Marginals -/


-- @@ L171-171 verbatim
section marginal


-- @@ L173-173 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L175-213 expanded
/-- Marginalizing one coordinate out of an independent product recovers that factor exactly,
provided the other factors carry full mass. -/
lemma probEvent_coord_mOfFn (n : ℕ) (g : Fin n → m α) (hg : ∀ j, probFailure (g j) = 0) (i : Fin n)
    (p : α → Prop) : (probEvent (Fin.mOfFn n g) fun v => p (v i)) = probEvent (g i) p := by
  classical
    induction n with
  | zero => exact i.elim0
  | succ n
    ih =>
    have htail : probFailure (Fin.mOfFn n fun j => g j.succ) = 0 :=
      probFailure_mOfFn n _ (fun j => hg j.succ)
    refine Fin.cases ?_ (fun j => ?_) i
    · have hinner :
        ∀ a : α,
          (probEvent
              ((Fin.mOfFn n fun j => g j.succ) >>= fun rest =>
                (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
              fun v => p (v 0)) =
            if p a then 1 else 0 :=
        by
        intro a
        rw [probEvent_bind_eq_tsum]
        simp only [probEvent_pure, Fin.cons_zero]
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' htail, one_mul]
      simp only [Fin.mOfFn]
      rw [probEvent_bind_eq_tsum]
      simp only [hinner]
      rw [probEvent_eq_tsum_ite]
      refine tsum_congr fun a => ?_
      split <;> simp
    · have hj :
        (probEvent (Fin.mOfFn n fun l => g l.succ) fun rest : Fin n → α => p (rest j)) =
          probEvent (g j.succ) p :=
        ih (fun l => g l.succ) (fun l => hg l.succ) j
      have hinner :
        ∀ a : α,
          (probEvent
              ((Fin.mOfFn n fun l => g l.succ) >>= fun rest =>
                (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
              fun v => p (v j.succ)) =
            probEvent (g j.succ) p :=
        by
        intro a
        rw [probEvent_bind_eq_tsum, ← hj, probEvent_eq_tsum_ite]
        refine tsum_congr fun rest => ?_
        simp only [probEvent_pure, Fin.cons_succ]
        split <;> simp
      simp only [Fin.mOfFn]
      rw [probEvent_bind_eq_tsum]
      simp only [hinner]
      rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (hg 0), one_mul]


-- @@ L215-252 expanded
omit [LawfulMonad m] in
/-- Without a full-mass hypothesis on the other factors the marginal is only a bound: a factor
that fails removes mass from every coordinate at once. -/
lemma probEvent_coord_mOfFn_le [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (n : ℕ) (g : Fin n → m α) (i : Fin n) (p : α → Prop) :
    (probEvent (Fin.mOfFn n g) fun v => p (v i)) ≤ probEvent (g i) p := by
  classical
    induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.mOfFn]
      rw [probEvent_bind_eq_tsum]
      calc
        (∑' a,
              probOutput (g 0) a *
                probEvent
                  ((Fin.mOfFn n fun j => g j.succ) >>= fun rest =>
                    (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
                  fun v => p (v 0)) ≤
            ∑' a, probOutput (g 0) a * (if p a then (1 : ℝ≥0∞) else 0) :=
          by
          gcongr with a
          refine probEvent_bind_le_of_forall_le fun rest _ => ?_
          exact le_of_eq (by simp [probEvent_pure])
        _ = probEvent (g 0) p := by
          rw [probEvent_eq_tsum_ite]
          refine tsum_congr fun a => ?_
          split <;> simp
    · simp only [Fin.mOfFn]
      rw [probEvent_bind_eq_tsum]
      calc
        (∑' a,
              probOutput (g 0) a *
                probEvent
                  ((Fin.mOfFn n fun l => g l.succ) >>= fun rest =>
                    (pure (Fin.cons a rest) : m (Fin (n + 1) → α)))
                  fun v => p (v j.succ)) ≤
            ∑' a, probOutput (g 0) a * probEvent (g j.succ) p :=
          by
          gcongr with a
          refine le_trans (le_of_eq ?_) (ih (fun l => g l.succ) j)
          rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
          refine tsum_congr fun rest => ?_
          simp only [probEvent_pure, Fin.cons_succ]
          split <;> simp
        _ ≤ probEvent (g j.succ) p := by exact tsum_probOutput_mul_le_of_le _ fun _ => le_rfl


-- @@ L254-254 verbatim
end marginal


-- @@ L256-256 verbatim
/-! ## Products over an arbitrary finite index -/


-- @@ L258-258 verbatim
section mPi


-- @@ L260-260 verbatim
universe v'


-- @@ L262-262 verbatim
variable {α : Type} {m : Type → Type v'} [Monad m] [LawfulMonad m] {ι : Type} [Fintype ι]


-- @@ L264-268 verbatim
/-- The independent product of a family of computations indexed by a finite type, obtained by
transporting `Fin.mOfFn` along `Fintype.equivFin`. -/
noncomputable def Fintype.mPi (f : ι → m α) : m (ι → α) :=
  (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl α)) <$>
    Fin.mOfFn (Fintype.card ι) fun k => f ((Fintype.equivFin ι).symm k)


-- @@ L270-270 verbatim
section support


-- @@ L272-272 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L274-278 verbatim
lemma mem_support_mPi (f : ι → m α) (v : ι → α) (hv : v ∈ support (Fintype.mPi f)) (i : ι) :
    v i ∈ support (f i) := by
  rw [Fintype.mPi, support_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  simpa using mem_support_mOfFn _ _ w hw (Fintype.equivFin ι i)


-- @@ L280-280 verbatim
end support


-- @@ L282-282 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L284-289 expanded
/-- The output distribution of a finite independent product is the product of the factors. -/
lemma probOutput_mPi [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (f : ι → m α) (v : ι → α) : probOutput (Fintype.mPi f) v = ∏ i, probOutput (f i) (v i) :=
  by
  rw [Fintype.mPi, probOutput_map_equiv, probOutput_mOfFn]
  exact Equiv.prod_comp (Fintype.equivFin ι).symm fun i => probOutput (f i) (v i)


-- @@ L291-293 expanded
lemma probFailure_mPi (f : ι → m α) (hf : ∀ i, probFailure (f i) = 0) :
    probFailure (Fintype.mPi f) = 0 :=
  by
  rw [Fintype.mPi, probFailure_map]
  exact probFailure_mOfFn _ _ fun k => hf _


-- @@ L295-309 expanded
/-- A coordinatewise conjunction of events over a finite index factors as a product. -/
lemma probEvent_forall_coord_mPi (f : ι → m α) (p : (i : ι) → α → Prop) :
    (probEvent (Fintype.mPi f) fun v => ∀ i, p i (v i)) = ∏ i, probEvent (f i) (p i) :=
  by
  rw [Fintype.mPi, probEvent_map]
  have h :=
    probEvent_forall_coord_mOfFn (Fintype.card ι) (fun k => f ((Fintype.equivFin ι).symm k))
      (fun k => p ((Fintype.equivFin ι).symm k))
  rw [show
      ((fun v => ∀ i, p i (v i)) ∘ ⇑((Fintype.equivFin ι).symm.arrowCongr (Equiv.refl α))) =
        fun w => ∀ k, p ((Fintype.equivFin ι).symm k) (w k)
      from ?_,
    h]
  · exact Equiv.prod_comp (Fintype.equivFin ι).symm fun i => probEvent (f i) (p i)
  · funext w
    simp only [Function.comp_def, Equiv.arrowCongr, Equiv.coe_fn_mk, Equiv.coe_refl, id_eq,
      Equiv.symm_symm, eq_iff_iff]
    exact
      ⟨fun hw k => by simpa using hw ((Fintype.equivFin ι).symm k), fun hw i => by
        simpa using hw ((Fintype.equivFin ι) i)⟩


-- @@ L311-317 expanded
/-- Marginalizing one coordinate out of a finite independent product recovers that factor. -/
lemma probEvent_coord_mPi (f : ι → m α) (hf : ∀ i, probFailure (f i) = 0) (i : ι) (p : α → Prop) :
    (probEvent (Fintype.mPi f) fun v => p (v i)) = probEvent (f i) p :=
  by
  rw [Fintype.mPi, probEvent_map]
  have h :=
    probEvent_coord_mOfFn (Fintype.card ι) (fun k => f ((Fintype.equivFin ι).symm k))
      (fun k => hf _) (Fintype.equivFin ι i) p
  simpa [Function.comp_def, Equiv.arrowCongr] using h


-- @@ L319-324 expanded
/-- Reading off one coordinate of a finite independent product recovers that factor's output
distribution. -/
lemma probOutput_coord_mPi (f : ι → m α) (hf : ∀ i, probFailure (f i) = 0) (i : ι) (x : α) :
    probOutput ((fun v => v i) <$> Fintype.mPi f) x = probOutput (f i) x :=
  by
  rw [probOutput_map]
  exact (probEvent_coord_mPi f hf i (· = x)).trans (probEvent_eq_eq_probOutput _ x)


-- @@ L326-333 expanded
/-- Expectations of a functional of one coordinate are computed in that factor alone. This is
what makes the total cost of an independent family split as a sum over the family. -/
lemma expectedValue_coord_mPi (f : ι → m α) (hf : ∀ i, probFailure (f i) = 0) (i : ι)
    (g : α → ℝ≥0∞) :
    OracleComp.EvalDist.expectedValue (Fintype.mPi f) (fun v => g (v i)) =
      OracleComp.EvalDist.expectedValue (f i) g :=
  by
  rw [← OracleComp.EvalDist.expectedValue_map (Fintype.mPi f) (fun v => v i) g]
  exact OracleComp.EvalDist.expectedValue_congr (probOutput_coord_mPi f hf i) g


-- @@ L335-335 verbatim
end mPi
