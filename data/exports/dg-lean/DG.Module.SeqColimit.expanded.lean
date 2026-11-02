import DG.Module.DirectSum
import DG.Module.Equiv
import DG.Module.SubQuotient


-- @@ L5-27 verbatim
/-!
# Sequential colimits of dg modules

Let `S 0 → S 1 → S 2 → ⋯` be a sequence of morphisms `ι n : S n → S (n + 1)` of dg `A`-modules.
Its colimit is the quotient of the direct sum `⨁ n, S n` by the image of the morphism
`x ↦ x - ι n x` (for `x ∈ S n`); it is again a dg module, and it comes with morphisms
`DG.SeqColimit.of S ι n : S n → SeqColimit S ι` compatible with the `ι n`.

## Main definitions

* `DG.SeqColimit S ι`: the colimit of the sequence.
* `DG.SeqColimit.of S ι n`: the canonical morphisms `S n → SeqColimit S ι`.
* `DG.SeqColimit.desc`: the morphism out of the colimit determined by a compatible family of
  morphisms `S n → N`.

## Main results

* `DG.SeqColimit.of_comp_ι`: `of (n + 1) ∘ ι n = of n`.
* `DG.SeqColimit.of_injective`: if all `ι n` are injective, so are the `of n`; the images
  `DG.SeqColimit.filtration S ι n` of the `of n` then form an increasing exhaustive filtration
  of the colimit (`DG.SeqColimit.filtration_mono`, `DG.SeqColimit.exists_mem_filtration`)
  by dg submodules isomorphic to the `S n`.
-/


-- @@ L29-29 verbatim
open DirectSum


-- @@ L31-31 verbatim
namespace DG


-- @@ L33-35 expanded
variable {A : Type*} [Ring A] [DGAddCommGroup A] (S : ℕ → Type*) [∀ n, AddCommGroup (S n)]
  [∀ n, DGAddCommGroup (S n)] [∀ n, Module A (S n)] (ι : ∀ n, DGModuleHom A (S n) (S (n + 1)))


-- @@ L37-37 verbatim
namespace SeqColimit


-- @@ L39-43 expanded
/-- The morphism `⨁ n, S n → ⨁ n, S n` given on `S n` by `x ↦ x - ι n x`; the colimit of the
sequence is its cokernel. -/
noncomputable def relHom : DGModuleHom A (⨁ n, S n) (⨁ n, S n) :=
  DGModuleHom.toModule fun n => DGModuleHom.lof A S n - (DGModuleHom.lof A S (n + 1)).comp (ι n)


-- @@ L45-45 verbatim
variable {S}


-- @@ L47-49 verbatim
theorem relHom_of (n : ℕ) (x : S n) :
    relHom S ι (DirectSum.of S n x) = DirectSum.of S n x - DirectSum.of S (n + 1) (ι n x) := by
  simp [relHom]


-- @@ L51-56 verbatim
theorem relHom_apply_zero (y : ⨁ n, S n) : relHom S ι y 0 = y 0 := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n x =>
    rw [relHom_of, DirectSum.sub_apply, of_eq_of_ne _ _ _ (Nat.succ_ne_zero n).symm, sub_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy]


-- @@ L58-71 verbatim
theorem relHom_apply_succ (y : ⨁ n, S n) (k : ℕ) :
    relHom S ι y (k + 1) = y (k + 1) - ι k (y k) := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero, sub_zero]
  | of n x =>
    rw [relHom_of, DirectSum.sub_apply]
    congr 1
    by_cases h : n = k
    · subst h
      rw [of_eq_same, of_eq_same]
    · rw [of_eq_of_ne _ _ _ (by omega), of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy =>
    rw [map_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply, DirectSum.add_apply, map_add]
    abel


-- @@ L73-73 verbatim
end SeqColimit


-- @@ L75-78 verbatim
/-- The colimit of a sequence `S 0 → S 1 → ⋯` of morphisms of dg modules: the quotient of
`⨁ n, S n` by the image of `x ↦ x - ι n x`. -/
abbrev SeqColimit : Type _ :=
  (⨁ n, S n) ⧸ (SeqColimit.relHom S ι).range.toSubmodule


-- @@ L80-80 verbatim
namespace SeqColimit


-- @@ L82-84 expanded
/-- The canonical morphism `S n → SeqColimit S ι`. -/
noncomputable def of (n : ℕ) : DGModuleHom A (S n) (SeqColimit S ι) :=
  (relHom S ι).range.mkQ.comp (DGModuleHom.lof A S n)


-- @@ L86-86 verbatim
variable {S ι}


-- @@ L88-89 verbatim
theorem of_apply (n : ℕ) (x : S n) :
    of S ι n x = (relHom S ι).range.mkQ (DirectSum.of S n x) := rfl


-- @@ L91-94 verbatim
theorem of_succ_ι (n : ℕ) (x : S n) : of S ι (n + 1) (ι n x) = of S ι n x := by
  rw [of_apply, of_apply, eq_comm, ← sub_eq_zero, ← map_sub, DGSubmodule.mkQ_eq_zero_iff,
    ← relHom_of]
  exact DGModuleHom.apply_mem_range _ _


-- @@ L96-98 verbatim
@[simp]
theorem of_comp_ι (n : ℕ) : (of S ι (n + 1)).comp (ι n) = of S ι n :=
  DGModuleHom.ext (of_succ_ι n)


-- @@ L100-143 verbatim
/-- If the transition maps are injective, so are the canonical maps into the colimit. -/
theorem of_injective (hι : ∀ n, Function.Injective (ι n)) (n : ℕ) :
    Function.Injective (of S ι n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [of_apply, DGSubmodule.mkQ_eq_zero_iff, DGModuleHom.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  have h0 : ∀ k, k < n → y k = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h := relHom_apply_zero ι y
      rw [hy, of_eq_of_ne _ _ _ (by omega)] at h
      exact h.symm
    | succ k ih =>
      intro hk
      have h := relHom_apply_succ ι y k
      rw [hy, of_eq_of_ne _ _ _ (by omega), ih (by omega), map_zero, sub_zero] at h
      exact h.symm
  have hn : y n = x := by
    cases n with
    | zero =>
      have h := relHom_apply_zero ι y
      rw [hy, of_eq_same] at h
      exact h.symm
    | succ k =>
      have h := relHom_apply_succ ι y k
      rw [hy, of_eq_same, h0 k (by omega), map_zero, sub_zero] at h
      exact h.symm
  by_contra hx0
  have hne : ∀ j, y (n + j) ≠ 0 := by
    intro j
    induction j with
    | zero => exact hn ▸ hx0
    | succ j ih =>
      intro hj
      have h := relHom_apply_succ ι y (n + j)
      change y (n + j + 1) = 0 at hj
      rw [hy, of_eq_of_ne _ _ _ (by omega), hj, zero_sub, eq_comm, neg_eq_zero,
        map_eq_zero_iff _ (hι _)] at h
      exact ih h
  exact Set.infinite_of_injective_forall_mem (add_right_injective n) hne
    (DFinsupp.finite_support y)


-- @@ L145-147 verbatim
/-- The filtration of the colimit by the images of the `S n`. -/
noncomputable def filtration (n : ℕ) : DGSubmodule A (SeqColimit S ι) :=
  (of S ι n).range


-- @@ L149-151 verbatim
theorem mem_filtration_iff {n : ℕ} {x : SeqColimit S ι} :
    x ∈ filtration n ↔ ∃ y, of S ι n y = x :=
  Iff.rfl


-- @@ L153-154 verbatim
theorem of_mem_filtration (n : ℕ) (x : S n) : of S ι n x ∈ filtration n :=
  ⟨x, rfl⟩


-- @@ L156-159 verbatim
theorem filtration_mono : Monotone (filtration (S := S) (ι := ι)) := by
  refine monotone_nat_of_le_succ fun n x hx => ?_
  obtain ⟨y, rfl⟩ := hx
  exact ⟨ι n y, of_succ_ι n y⟩


-- @@ L161-172 verbatim
/-- The filtration by the images of the `S n` is exhaustive. -/
theorem exists_mem_filtration (x : SeqColimit S ι) : ∃ n, x ∈ filtration n := by
  obtain ⟨y, rfl⟩ := (relHom S ι).range.mkQ_surjective x
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; exact zero_mem _⟩
  | of n x => exact ⟨n, x, rfl⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    rw [map_add]
    exact ⟨max i j, add_mem (filtration_mono (le_max_left i j) hi)
      (filtration_mono (le_max_right i j) hj)⟩


-- @@ L174-176 verbatim
/-- Every element of the colimit comes from some `S n`. -/
theorem exists_of_eq (x : SeqColimit S ι) : ∃ n y, of S ι n y = x :=
  (exists_mem_filtration x).imp fun _ h => h


-- @@ L178-178 verbatim
section Desc


-- @@ L180-181 expanded
variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  (g : ∀ n, DGModuleHom A (S n) N) (hg : ∀ n, (g (n + 1)).comp (ι n) = g n)


-- @@ L183-190 verbatim
include hg in
theorem toModule_relHom (y : ⨁ n, S n) : DGModuleHom.toModule g (relHom S ι y) = 0 := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n x =>
    rw [relHom_of, map_sub, DGModuleHom.toModule_lof, DGModuleHom.toModule_lof,
      ← DGModuleHom.comp_apply, hg, sub_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]


-- @@ L192-197 expanded
/-- The morphism out of the colimit determined by a compatible family of morphisms
`g n : S n → N`. -/
noncomputable def desc : DGModuleHom A (SeqColimit S ι) N :=
  DGSubmodule.liftQ (DGModuleHom.toModule g) fun x hx =>
    by
    obtain ⟨y, rfl⟩ := hx
    exact toModule_relHom g hg y


-- @@ L199-201 verbatim
@[simp]
theorem desc_of (n : ℕ) (x : S n) : desc g hg (of S ι n x) = g n x :=
  DGModuleHom.toModule_lof g n x


-- @@ L203-205 verbatim
@[simp]
theorem desc_comp_of (n : ℕ) : (desc g hg).comp (of S ι n) = g n :=
  DGModuleHom.ext (desc_of g hg n)


-- @@ L207-207 verbatim
end Desc


-- @@ L209-209 verbatim
end SeqColimit


-- @@ L211-211 verbatim
end DG
