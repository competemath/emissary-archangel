import OAI.Combinatorics.TreewidthL1.Particles


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe treewidthLevel1 treewidthLevel2 treewidthLevel3 treewidthLevel4


-- @@ L7-8 verbatim
/-! Deterministic causal recursion on a rooted finite tree. The depth certificate
is constructed from graph distance below; it is not an embedding hypothesis. -/

-- @@ L9-9 verbatim
namespace BoundedTreewidthL1


-- @@ L11-14 verbatim
structure RootedForest (I : Type*) where
  parent : I → Option I
  depth : I → ℕ
  decreases : ∀ i p, parent i = some p → depth p < depth i


-- @@ L16-16 verbatim
namespace RootedForest

-- @@ L17-17 verbatim
variable {I A : Type*}


-- @@ L19-26 verbatim
noncomputable def run (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) : A :=
  step i (match h : R.parent i with
    | none => seed
    | some p =>
      have : R.depth p < R.depth i := R.decreases i p h
      R.run seed step p)
termination_by R.depth i
decreasing_by assumption


-- @@ L28-31 verbatim
lemma run_eq (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) :
    R.run seed step i = step i ((R.parent i).elim seed (R.run seed step)) := by
  rw [run]
  split <;> simp_all


-- @@ L33-44 verbatim
lemma run_invariant (R : RootedForest I) (seed : A) (step : I → A → A)
    (Q : A → Prop) (hseed : Q seed) (hstep : ∀ i a, Q a → Q (step i a)) :
    ∀ i, Q (R.run seed step i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [run_eq]
    apply hstep
    cases hp : R.parent i with
    | none => exact hseed
    | some p =>
      apply ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl


-- @@ L46-59 verbatim
lemma run_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (R : RootedForest I) (seed : Ω → A) (step : I → Ω → A → A)
    (hseed : Measurable seed)
    (hstep : ∀ i f, Measurable f → Measurable (fun ω => step i ω (f ω))) :
    ∀ i, Measurable (fun ω => R.run (seed ω) (fun j => step j ω) i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    simp_rw [run_eq]
    cases hp : R.parent i with
    | none => simpa only [hp, Option.elim_none] using hstep i seed hseed
    | some p =>
      simpa only [hp, Option.elim_some] using hstep i _
        (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl)

-- @@ L60-60 verbatim
end RootedForest

-- @@ L61-61 verbatim
end BoundedTreewidthL1


-- @@ L63-63 verbatim
namespace BoundedTreewidthL1.TreeParticles

-- @@ L64-64 verbatim
open MeasureTheory ParticleSchedule ParticleBatch

-- @@ L65-66 verbatim
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]


-- @@ L68-69 verbatim
noncomputable def interface (R : RootedForest I) (bag : I → Finset V) (i : I) : Finset V :=
  (R.parent i).elim ∅ bag

-- @@ L70-71 verbatim
noncomputable def retained (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  (R.parent i).elim ∅ (fun p => A i ∩ A p)

-- @@ L72-73 verbatim
noncomputable def fresh (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  A i \ retained R A i

-- @@ L74-75 verbatim
noncomputable def seed : (ι → V → ℝ) × (J → ι × ι) :=
  (fun _ _ => 0, fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))

-- @@ L76-78 verbatim
noncomputable def step (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (S : (ι → V → ℝ) × (J → ι × ι)) :=
  launchBatch (interface R bag i) (fresh R A i).toList (retained R A i) S.1 S.2 (g i)

-- @@ L79-81 verbatim
noncomputable def state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) : (ι → V → ℝ) × (J → ι × ι) :=
  R.run seed (step R bag A g) i


-- @@ L83-88 verbatim
lemma retained_subset (R : RootedForest I) (A : I → Finset J) (i : I) :
    retained R A i ⊆ A i := by
  unfold retained
  cases R.parent i with
  | none => exact Finset.empty_subset _
  | some p => exact Finset.inter_subset_left


-- @@ L90-100 verbatim
lemma batch_data (R : RootedForest I) (A : I → Finset J) (i : I)
    {q : ℕ} (hA : (A i).card ≤ q) :
    (fresh R A i).toList.Nodup ∧
    (∀ a ∈ (fresh R A i).toList, a ∉ retained R A i) ∧
    (retained R A i ∪ (fresh R A i).toList.toFinset).card ≤ q := by
  classical
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  · simpa only [Finset.toList_toFinset, fresh,
      Finset.union_sdiff_of_subset (retained_subset R A i)] using hA


-- @@ L102-109 verbatim
lemma interface_card
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype V]
    (R : RootedForest I) (bag : I → Finset V) {k : ℕ}
    (hbag : ∀ i, (bag i).card ≤ k) (i : I) : (interface R bag i).card ≤ k := by
  unfold interface
  cases R.parent i with
  | none => exact Nat.zero_le _
  | some p => exact hbag p


-- @@ L111-117 verbatim
lemma state_eq
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {J : Type treewidthLevel4} [Fintype V] [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq J]
    (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) :
    state (ι := ι) R bag A g i = step R bag A g i
      ((R.parent i).elim seed (state R bag A g)) := RootedForest.run_eq _ _ _ _

-- @@ L118-193 verbatim
/-- Actual branching preparation for active-scale keys. Children use their own
copies of the parent's list; no consistency assumption on sampled bag laws. -/
theorem forest_particle_realization (R : RootedForest I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ interface R bag i, g i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let S := state (ι := ι) R bag A g
    (∀ i, FunctionParticleReachable d L H (S i).1) ∧
    (∀ i p, R.parent i = some p →
      particleTrace M (S i).1 (bag p) = particleTrace M (S p).1 (bag p)) ∧
    (∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) ∧
    (∀ i a, a ∈ fresh R A i →
      ((S i).2 a).1 ≠ ((S i).2 a).2 ∧
      ∀ v, (S i).1 ((S i).2 a).1 v - (S i).1 ((S i).2 a).2 v = 2*g i a v) := by
  classical
  dsimp only
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  let S := state (ι := ι) R bag A g
  have hstep (i : I) (F : ι → V → ℝ) (p : J → ι × ι)
      (hF : FunctionParticleReachable d L H F) :=
    launchBatch_correct k q hN (interface R bag i) (interface_card R bag hbag i)
      (fresh R A i).toList (retained R A i)
      (batch_data R A i (hA i)).1 (batch_data R A i (hA i)).2.1
      (batch_data R A i (hA i)).2.2 d L H Δ hH hΔ F p hF (g i)
      (fun a _ => hLip i a) (fun a _ => hHeight i a) (fun a _ => hzero i a)
  have hreach : ∀ i, FunctionParticleReachable d L H (S i).1 := by
    apply R.run_invariant seed (step R bag A g) (fun S => FunctionParticleReachable d L H S.1)
    · exact FunctionParticleReachable.zero
    · intro i F hF
      exact (hstep i F.1 F.2 hF).1
  have hinput (i : I) : FunctionParticleReachable d L H
      ((R.parent i).elim seed S).1 := by
    cases hp : R.parent i with
    | none => exact FunctionParticleReachable.zero
    | some p => exact hreach p
  have hstate (i : I) :
      launchBatch (interface R bag i) (fresh R A i).toList (retained R A i)
        ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 (g i) = S i :=
    (state_eq R bag A g i).symm
  refine ⟨hreach, ?_, ?_, ?_⟩
  · intro i p hp
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.1
    rw [hstate] at hj
    unfold interface at hj
    rw [hp] at hj
    exact hj
  · intro i p hp a ha
    have hj := hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)
    dsimp only at hj
    rw [hstate] at hj
    have hm : a ∈ retained R A i := by simpa only [retained, hp, Option.elim_some] using ha
    have he := hj.2.2.1 a hm
    have hleft := hj.2.2.2.1 _ (first_mem_used hm ((R.parent i).elim seed S).2)
    have hright := hj.2.2.2.1 _ (second_mem_used hm ((R.parent i).elim seed S).2)
    have he' : (S i).2 a = (S p).2 a := by
      simpa only [hp, Option.elim_some] using he
    refine ⟨he', ?_, ?_⟩
    · rw [he']
      simpa only [hp, Option.elim_some] using hleft
    · rw [he']
      simpa only [hp, Option.elim_some] using hright
  · intro i a ha
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.2.2.2 a (Finset.mem_toList.mpr ha)
    rw [hstate] at hj
    exact hj

-- @@ L194-194 verbatim
end BoundedTreewidthL1.TreeParticles


-- @@ L196-196 verbatim
namespace BoundedTreewidthL1.TreeParticles

-- @@ L197-197 verbatim
open MeasureTheory ParticleSchedule ParticleBatch

-- @@ L198-200 verbatim
variable {I V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]


-- @@ L202-214 verbatim
/-- Measurability of the actual branching preparation, with all randomness
sampled beforehand. No measurable-choice assumption about the particle lists. -/
theorem measurable_state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : Ω → I → J → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (i : I) :
    Measurable (fun ω => state (ι := ι) R bag A (g ω) i) := by
  apply R.run_measurable (fun _ => seed) (fun j ω S => step R bag A (g ω) j S)
    measurable_const
  intro j f hf
  exact measurable_launchBatch (interface R bag j) (fresh R A j).toList (retained R A j)
    (fun ω => (f ω).1) (fun ω => (f ω).2) (fun ω => g ω j)
    (fun a v => (measurable_pi_apply v).comp ((measurable_pi_apply a).comp hf.fst))
    (fun a => (measurable_pi_apply a).comp hf.snd) (hg j)


-- @@ L216-216 verbatim
end BoundedTreewidthL1.TreeParticles


-- @@ L218-218 verbatim
end OAI
