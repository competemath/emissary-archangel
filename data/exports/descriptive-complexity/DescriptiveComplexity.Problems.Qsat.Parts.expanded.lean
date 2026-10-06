/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Matrix


-- @@ L8-29 verbatim
/-!
# The blocks of the prefix, and what the matrix says

The five kinds of block the prefix of the constructed instance splits into –
the endpoints, then a midpoint, a universal bit and a pair per level, then the
auxiliary variables (`DescriptiveComplexity.tEnds`, `DescriptiveComplexity.tZ`,
`DescriptiveComplexity.tB`, `DescriptiveComplexity.tUV`,
`DescriptiveComplexity.tAux`) – together with the reading of the matrix they make
possible.

Grouping the clause tags by what they talk about turns the matrix into four
conditions (`DescriptiveComplexity.qsatMatrix_iff_parts`): the source valuation
witnesses `DescriptiveComplexity.IsStart` for the first endpoint
(`DescriptiveComplexity.SrcPart`), the target valuation witnesses
`DescriptiveComplexity.IsGoal` for the second (`DescriptiveComplexity.TgtPart`),
the transition valuation and the bit `sE` witness one move of the walk at the
bottom level (`DescriptiveComplexity.StepPart`), and every level relates its own
pair to the pair it receives from above (`DescriptiveComplexity.LevPart`).

Each group is the conjunction of two clauses of opposite signs, which is why the
conditions come out as equivalences rather than implications.
-/


-- @@ L31-31 verbatim
namespace DescriptiveComplexity


-- @@ L33-33 verbatim
open FirstOrder


-- @@ L35-35 verbatim
open Language Structure


-- @@ L37-37 verbatim
/-! ### The block coordinates -/


-- @@ L39-39 verbatim
section Triples


-- @@ L41-41 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L43-44 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sS (p q : A) : keyTriple .sS p q = (0, q, 0) := rfl

-- @@ L45-46 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sT (p q : A) : keyTriple .sT p q = (0, q, 0) := rfl

-- @@ L47-48 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sZ (p q : A) : keyTriple .sZ p q = (1, p, 0) := rfl

-- @@ L49-50 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sB (p q : A) : keyTriple .sB p q = (1, p, 1) := rfl

-- @@ L51-52 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sU (p q : A) : keyTriple .sU p q = (1, p, 2) := rfl

-- @@ L53-54 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sV (p q : A) : keyTriple .sV p q = (1, p, 2) := rfl

-- @@ L55-56 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aS (p q : A) : keyTriple .aS p q = (2, q, 0) := rfl

-- @@ L57-58 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aT (p q : A) : keyTriple .aT p q = (2, q, 0) := rfl

-- @@ L59-60 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_aP (p q : A) : keyTriple .aP p q = (2, q, 0) := rfl

-- @@ L61-62 verbatim
omit [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
@[simp] theorem keyTriple_sE (p q : A) : keyTriple .sE p q = (2, q, 0) := rfl


-- @@ L64-66 verbatim
variable (A) in
/-- The block coordinates of the two endpoints of the walk: the first block. -/
noncomputable def tEnds : ℕ × A × ℕ := (0, qBot A, 0)


-- @@ L68-69 verbatim
/-- The block coordinates of the midpoint guessed at level `ℓ`. -/
def tZ (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 0)


-- @@ L71-72 verbatim
/-- The block coordinates of the universal bit of level `ℓ`. -/
def tB (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 1)


-- @@ L74-75 verbatim
/-- The block coordinates of the pair passed below level `ℓ`. -/
def tUV (ℓ : A) : ℕ × A × ℕ := (1, ℓ, 2)


-- @@ L77-79 verbatim
variable (A) in
/-- The block coordinates of the auxiliary variables: the last block. -/
noncomputable def tAux : ℕ × A × ℕ := (2, qBot A, 0)


-- @@ L81-81 verbatim
end Triples


-- @@ L83-83 verbatim
/-! ### Overriding a block -/


-- @@ L85-85 verbatim
section Over


-- @@ L87-87 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L88-88 verbatim
variable {B : QM A → Prop} (τ ν : QM A → Prop)


-- @@ L90-93 verbatim
omit [Finite A] [Nonempty A] in
theorem qOver_out {v : QVarTag} {p q : A} (h : ¬B (qVar v p q)) :
    qOver B τ ν (qVar v p q) ↔ τ (qVar v p q) :=
  ⟨fun hx => (hx.resolve_left fun hh => h hh.1).2, fun hx => Or.inr ⟨h, hx⟩⟩


-- @@ L95-98 verbatim
omit [Finite A] [Nonempty A] in
theorem qOver_in {v : QVarTag} {p q : A} (h : B (qVar v p q)) :
    qOver B τ ν (qVar v p q) ↔ ν (qVar v p q) :=
  ⟨fun hx => (hx.resolve_right fun hh => hh.1 h).2, fun hx => Or.inl ⟨h, hx⟩⟩


-- @@ L100-100 verbatim
end Over


-- @@ L102-102 verbatim
/-! ### Two clauses of opposite signs make an equivalence -/


-- @@ L104-104 verbatim
section Pairs


-- @@ L106-107 verbatim
theorem iff_of_or_not {P Q : Prop} (h0 : ¬P ∨ Q) (h1 : P ∨ ¬Q) : P ↔ Q :=
  ⟨fun hp => h0.resolve_left (not_not_intro hp), fun hq => h1.resolve_right (not_not_intro hq)⟩


-- @@ L109-114 verbatim
theorem or_forall_of_forall_or {ι : Sort*} {R : Prop} {P : ι → Prop} (h : ∀ i, R ∨ P i) :
    R ∨ ∀ i, P i := by
  classical
  by_cases hR : R
  · exact Or.inl hR
  · exact Or.inr fun i => (h i).resolve_left hR


-- @@ L116-116 verbatim
end Pairs


-- @@ L118-118 verbatim
/-! ### What the matrix says -/


-- @@ L120-120 verbatim
section Parts


-- @@ L122-122 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L123-123 verbatim
variable (σ : QM A → Prop)


-- @@ L125-128 verbatim
/-- The source valuation satisfies the source clauses and reads the source
endpoint of the walk. -/
def SrcPart : Prop :=
  ClausesHold A (valS σ) tsSrcCl ∧ ReadsCur A (valS σ) (stS σ)


-- @@ L130-133 verbatim
/-- The target valuation satisfies the target clauses and reads the target
endpoint of the walk. -/
def TgtPart : Prop :=
  ClausesHold A (valT σ) tsTgtCl ∧ ReadsCur A (valT σ) (stT σ)


-- @@ L135-142 verbatim
/-- The base case of the recursion: either the equality branch, or the
transition valuation satisfying the transition clauses while reading the first
component of the bottom pair and writing the second. -/
def StepPart : Prop :=
  (bitE σ ∨ ClausesHold A (valP σ) tsStepCl) ∧
    (∀ m : A, IsMaxSV m → (bitE σ ∨ ReadsCur A (valP σ) (stU σ m))) ∧
    (∀ m : A, IsMaxSV m → (bitE σ ∨ WritesNext A (valP σ) (stV σ m))) ∧
    ∀ m : A, IsMaxSV m → (¬bitE σ ∨ ∀ x : A, IsSV x → (stU σ m x ↔ stV σ m x))


-- @@ L144-146 verbatim
/-- Every level relates its pair to the pair it receives from above. -/
def LevPart : Prop :=
  ∀ (b w s : Bool) (ℓ x : A), IsSV ℓ → IsSV x → LevSat σ b w s ℓ x


-- @@ L148-151 verbatim
theorem matrix_cSrc_iff :
    (∀ p q : A, QClOn .cSrc p q → ClSat σ .cSrc p q) ↔ ClausesHold A (valS σ) tsSrcCl :=
  ⟨fun h c hc => (clSat_cSrc σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩),
    fun h p q hg => (clSat_cSrc σ p q).mpr (h p hg.1)⟩


-- @@ L153-156 verbatim
theorem matrix_cTgt_iff :
    (∀ p q : A, QClOn .cTgt p q → ClSat σ .cTgt p q) ↔ ClausesHold A (valT σ) tsTgtCl :=
  ⟨fun h c hc => (clSat_cTgt σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩),
    fun h p q hg => (clSat_cTgt σ p q).mpr (h p hg.1)⟩


-- @@ L158-167 verbatim
theorem matrix_cStep_iff :
    (∀ p q : A, QClOn .cStep p q → ClSat σ .cStep p q) ↔
      (bitE σ ∨ ClausesHold A (valP σ) tsStepCl) := by
  constructor
  · intro h
    refine or_forall_of_forall_or fun c => or_forall_of_forall_or fun hc => ?_
    exact (clSat_cStep σ c (qBot A)).mp (h c (qBot A) ⟨hc, isBot_qBot A⟩)
  · rintro (hb | h) p q hg
    · exact (clSat_cStep σ p q).mpr (Or.inl hb)
    · exact (clSat_cStep σ p q).mpr (Or.inr (h p hg.1))


-- @@ L169-188 verbatim
theorem matrix_lS_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lS s) p q → ClSat σ (.lS s) p q) ↔
      ReadsCur A (valS σ) (stS σ) := by
  classical
  constructor
  · intro h x hx
    have h0 := (clSat_lS σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lS σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    exact iff_of_or_not h0 h1
  · intro h s p q hg
    rw [clSat_lS σ s hg]
    have hp := h p hg.1
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valS σ p
      · exact Or.inr (hp.mp hv)
      · exact Or.inl hv
    · by_cases hv : valS σ p
      · exact Or.inl hv
      · exact Or.inr fun hs => hv (hp.mpr hs)


-- @@ L190-209 verbatim
theorem matrix_lT_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lT s) p q → ClSat σ (.lT s) p q) ↔
      ReadsCur A (valT σ) (stT σ) := by
  classical
  constructor
  · intro h x hx
    have h0 := (clSat_lT σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lT σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    exact iff_of_or_not h0 h1
  · intro h s p q hg
    rw [clSat_lT σ s hg]
    have hp := h p hg.1
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valT σ p
      · exact Or.inr (hp.mp hv)
      · exact Or.inl hv
    · by_cases hv : valT σ p
      · exact Or.inl hv
      · exact Or.inr fun hs => hv (hp.mpr hs)


-- @@ L211-245 verbatim
theorem matrix_lU_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lU s) p q → ClSat σ (.lU s) p q) ↔
      ∀ m : A, IsMaxSV m → (bitE σ ∨ ReadsCur A (valP σ) (stU σ m)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun hx => ?_
    have h0 := (clSat_lU σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_lU σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with hn | ⟨m', hm', hu⟩
      · exact Or.inl hn
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
    · rcases h1 with hv | ⟨m', hm', hu⟩
      · exact Or.inl hv
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
  · intro h s p q hg
    rw [clSat_lU σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hr
    · exact Or.inl hb
    have hp := hr p hg.1
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valP σ p
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl hv
    · by_cases hv : valP σ p
      · exact Or.inl hv
      · exact Or.inr ⟨m, hm, fun hu => hv (hp.mpr hu)⟩


-- @@ L247-282 verbatim
theorem matrix_lV_iff :
    (∀ (s : Bool) (p q : A), QClOn (.lV s) p q → ClSat σ (.lV s) p q) ↔
      ∀ m : A, IsMaxSV m → (bitE σ ∨ WritesNext A (valP σ) (stV σ m)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun y =>
      or_forall_of_forall_or fun hx => or_forall_of_forall_or fun hxy => ?_
    have h0 := (clSat_lV σ false ⟨hx, hxy⟩).mp (h false x y ⟨hx, hxy⟩)
    have h1 := (clSat_lV σ true ⟨hx, hxy⟩).mp (h true x y ⟨hx, hxy⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with hn | ⟨m', hm', hu⟩
      · exact Or.inl hn
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
    · rcases h1 with hv | ⟨m', hm', hu⟩
      · exact Or.inl hv
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hu)
  · intro h s p q hg
    rw [clSat_lV σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hw
    · exact Or.inl hb
    have hp := hw p q hg.1 hg.2
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : valP σ q
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl hv
    · by_cases hv : valP σ q
      · exact Or.inl hv
      · exact Or.inr ⟨m, hm, fun hu => hv (hp.mpr hu)⟩


-- @@ L284-318 verbatim
theorem matrix_bE_iff :
    (∀ (s : Bool) (p q : A), QClOn (.bE s) p q → ClSat σ (.bE s) p q) ↔
      ∀ m : A, IsMaxSV m → (¬bitE σ ∨ ∀ x : A, IsSV x → (stU σ m x ↔ stV σ m x)) := by
  classical
  constructor
  · intro h m hm
    refine or_forall_of_forall_or fun x => or_forall_of_forall_or fun hx => ?_
    have h0 := (clSat_bE σ false ⟨hx, isBot_qBot A⟩).mp (h false x (qBot A) ⟨hx, isBot_qBot A⟩)
    have h1 := (clSat_bE σ true ⟨hx, isBot_qBot A⟩).mp (h true x (qBot A) ⟨hx, isBot_qBot A⟩)
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false] at h0 h1
    rcases h0 with hb | h0
    · exact Or.inl hb
    rcases h1 with hb | h1
    · exact Or.inl hb
    refine Or.inr (iff_of_or_not ?_ ?_)
    · rcases h0 with ⟨m', hm', hu⟩ | ⟨m', hm', hv⟩
      · exact Or.inl (isMaxSV_unique hm' hm ▸ hu)
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hv)
    · rcases h1 with ⟨m', hm', hu⟩ | ⟨m', hm', hv⟩
      · exact Or.inl (isMaxSV_unique hm' hm ▸ hu)
      · exact Or.inr (isMaxSV_unique hm' hm ▸ hv)
  · intro h s p q hg
    rw [clSat_bE σ s hg]
    obtain ⟨m, hm⟩ := exists_isMaxSV hg.1
    rcases h m hm with hb | hu
    · exact Or.inl hb
    have hp := hu p hg.1
    refine Or.inr ?_
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, iff_true, iff_false]
    · by_cases hv : stU σ m p
      · exact Or.inr ⟨m, hm, hp.mp hv⟩
      · exact Or.inl ⟨m, hm, hv⟩
    · by_cases hv : stU σ m p
      · exact Or.inl ⟨m, hm, hv⟩
      · exact Or.inr ⟨m, hm, fun hw => hv (hp.mpr hw)⟩


-- @@ L320-324 verbatim
theorem matrix_lev_iff :
    (∀ (b w s : Bool) (ℓ x : A), QClOn (.lev b w s) ℓ x → ClSat σ (.lev b w s) ℓ x) ↔
      LevPart σ :=
  ⟨fun h b w s ℓ x hl hx => (clSat_lev σ b w s ⟨hl, hx⟩).mp (h b w s ℓ x ⟨hl, hx⟩),
    fun h b w s ℓ x hg => (clSat_lev σ b w s hg).mpr (h b w s ℓ x hg.1 hg.2)⟩


-- @@ L326-351 verbatim
/-- **The matrix, read semantically.** -/
theorem qsatMatrix_iff_parts :
    QsatMatrix σ ↔ SrcPart σ ∧ TgtPart σ ∧ StepPart σ ∧ LevPart σ := by
  rw [qsatMatrix_iff]
  constructor
  · intro h
    exact ⟨⟨(matrix_cSrc_iff σ).mp fun p q => h .cSrc p q,
        (matrix_lS_iff σ).mp fun s p q => h (.lS s) p q⟩,
      ⟨(matrix_cTgt_iff σ).mp fun p q => h .cTgt p q,
        (matrix_lT_iff σ).mp fun s p q => h (.lT s) p q⟩,
      ⟨(matrix_cStep_iff σ).mp fun p q => h .cStep p q,
        (matrix_lU_iff σ).mp fun s p q => h (.lU s) p q,
        (matrix_lV_iff σ).mp fun s p q => h (.lV s) p q,
        (matrix_bE_iff σ).mp fun s p q => h (.bE s) p q⟩,
      (matrix_lev_iff σ).mp fun b w s ℓ x => h (.lev b w s) ℓ x⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6, h7, h8⟩, h9⟩ c p q
    cases c with
    | cSrc => exact (matrix_cSrc_iff σ).mpr h1 p q
    | cTgt => exact (matrix_cTgt_iff σ).mpr h3 p q
    | cStep => exact (matrix_cStep_iff σ).mpr h5 p q
    | lS s => exact (matrix_lS_iff σ).mpr h2 s p q
    | lT s => exact (matrix_lT_iff σ).mpr h4 s p q
    | lU s => exact (matrix_lU_iff σ).mpr h6 s p q
    | lV s => exact (matrix_lV_iff σ).mpr h7 s p q
    | bE s => exact (matrix_bE_iff σ).mpr h8 s p q
    | lev b w s => exact (matrix_lev_iff σ).mpr h9 b w s p q


-- @@ L353-353 verbatim
end Parts


-- @@ L355-355 verbatim
end DescriptiveComplexity
