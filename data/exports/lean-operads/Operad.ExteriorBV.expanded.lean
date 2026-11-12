/-
# The Chevalley–Eilenberg BV algebra of a Lie algebra

For a Lie algebra `L`, the exterior algebra `Λ L` carries the **Chevalley–Eilenberg operator**
`Δ (m₁ ∧ ⋯ ∧ m_k) = ∑_{i < j} ± [m_i, m_j] ∧ m₁ ∧ ⋯ m̂_i ⋯ m̂_j ⋯ ∧ m_k`, defined by the recursion
`Δ (m ∧ x) = -D_m x - m ∧ Δ x` (`ExtBV.Δ_ι_mul`), where `D_m` is the even derivation extending
`ad m` (`ExtBV.D`). It makes `Λ L` a **BV algebra**:
* `Δ² = 0` (`ExtBV.Δ_Δ`), using `[D_m, D_n] = D_[m, n]` (`ExtBV.Dm_comm`) and `[Δ, D_m] = 0`
  (`ExtBV.Δ_Dm`);
* `Δ` is **of order at most two** (`ExtBV.dv_mul_even`, `ExtBV.dv_mul_odd`): its deviation
  `⟨x, y⟩ = Δ (x y) - (Δ x) y - x̂ (Δ y)` (`ExtBV.dv`, with `x̂` the grade involution) is a graded
  derivation in `y`. It is computed by `⟨m ∧ x, y⟩ = -x D_m y - m ∧ ⟨x, y⟩` (`ExtBV.dv_ι_mul`).

The parity of `Λ L` is its `ℤ/2`-grading (`ExtBV.prZ`), making it a super module
(`ExtBV.instSuperMod`); the exterior algebra is graded commutative (`ExtBV.mul_comm_even`,
`ExtBV.mul_comm_odd`). Everything is characteristic free.

Hence `Λ L` is a **Gerstenhaber algebra** under the wedge product and the deviation of `Δ`, the
Schouten bracket up to sign (`ExtBV.isGer`), an algebra over the Gerstenhaber operad
(`ExtBV.gerAlg`). On vectors the deviation is the bracket of `L` up to sign:
`⟨m, n⟩ = -[m, n]` (`ExtBV.dv_ι_ι`).
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing
import Operad.GerOperad
import Operad.BinaryKoszul


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
namespace Operad


-- @@ L35-35 verbatim
namespace ExtBV


-- @@ L37-37 verbatim
open ExteriorAlgebra GrEnd

-- @@ L38-38 verbatim
open Sym (EndOp)

-- @@ L39-40 verbatim
open CliffordAlgebra (evenOdd foldr' foldr'_ι_mul foldr'_algebraMap involute involute_ι
  involute_involutive ι_mem_evenOdd_one)


-- @@ L42-42 verbatim
variable {R : Type u} [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]


-- @@ L44-45 verbatim
/-- The exterior algebra, as a Clifford algebra. -/
local notation "E" => ExteriorAlgebra R L


-- @@ L47-48 verbatim
/-- The quadratic form of the exterior algebra. -/
local notation "Q₀" => (0 : QuadraticForm R L)


-- @@ L50-57 verbatim
/-- **Induction on the exterior algebra**, by left multiplication by vectors. -/
@[elab_as_elim]
theorem induction {P : E → Prop} (alg : ∀ r, P (algebraMap R E r))
    (add : ∀ x y, P x → P y → P (x + y)) (ι_mul : ∀ m x, P x → P (ι R m * x)) (x : E) : P x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => exact alg r
  | add x y hx hy => exact add x y hx hy
  | ι_mul x m hx => exact ι_mul m x hx


-- @@ L59-59 verbatim
/-! ## Parity -/


-- @@ L61-62 verbatim
/-- **The parity components** of the exterior algebra, `0` even and `1` odd. -/
noncomputable def prZ (i : ZMod 2) : E →ₗ[R] E := GradedAlgebra.proj (evenOdd Q₀) i


-- @@ L64-64 verbatim
lemma prZ_apply (i : ZMod 2) (x : E) : prZ i x = DirectSum.decompose (evenOdd Q₀) x i := rfl


-- @@ L66-67 verbatim
lemma prZ_mem (i : ZMod 2) (x : E) : prZ i x ∈ evenOdd Q₀ i := by
  exact (DirectSum.decompose (evenOdd Q₀) x i).2


-- @@ L69-70 verbatim
lemma prZ_of_mem {i : ZMod 2} {x : E} (h : x ∈ evenOdd Q₀ i) : prZ i x = x :=
  DirectSum.decompose_of_mem_same _ h


-- @@ L72-73 verbatim
lemma prZ_of_mem_ne {i j : ZMod 2} {x : E} (h : x ∈ evenOdd Q₀ i) (hij : i ≠ j) : prZ j x = 0 :=
  DirectSum.decompose_of_mem_ne _ h hij


-- @@ L75-75 verbatim
lemma ι_mem (m : L) : ι R m ∈ evenOdd Q₀ 1 := ι_mem_evenOdd_one Q₀ m


-- @@ L77-78 verbatim
lemma prZ_ι_mul (i : ZMod 2) (m : L) (x : E) : prZ (1 + i) (ι R m * x) = ι R m * prZ i x :=
  DirectSum.coe_decompose_mul_add_of_left_mem (evenOdd Q₀) (ι_mem (R := R) m)


-- @@ L80-82 verbatim
lemma prZ_zero_ι_mul (m : L) (x : E) : prZ 0 (ι R m * x) = ι R m * prZ 1 x := by
  rw [← prZ_ι_mul]
  rfl


-- @@ L84-86 verbatim
lemma prZ_one_ι_mul (m : L) (x : E) : prZ 1 (ι R m * x) = ι R m * prZ 0 x := by
  rw [← prZ_ι_mul]
  rfl


-- @@ L88-89 verbatim
lemma algebraMap_mem (r : R) : algebraMap R E r ∈ evenOdd Q₀ 0 :=
  SetLike.algebraMap_mem_graded _ _


-- @@ L91-107 verbatim
/-- **Induction on parity components**: properties `Pe` of the even and `Po` of the odd elements,
transported by the left multiplications by vectors. -/
theorem parity_induction {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) (x : E) :
    Pe (prZ 0 x) ∧ Po (prZ 1 x) := by
  induction x using induction with
  | alg r =>
    rw [prZ_of_mem (algebraMap_mem r), prZ_of_mem_ne (algebraMap_mem r) (by decide)]
    exact ⟨alg r, zero⟩
  | add x y hx hy =>
    rw [map_add, map_add]
    exact ⟨adde _ _ hx.1 hy.1, addo _ _ hx.2 hy.2⟩
  | ι_mul m x hx =>
    rw [prZ_zero_ι_mul, prZ_one_ι_mul]
    exact ⟨ιe m _ (prZ_mem 1 x) hx.2, ιo m _ (prZ_mem 0 x) hx.1⟩


-- @@ L109-115 verbatim
lemma even_induction' {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) {x : E} (hx : x ∈ evenOdd Q₀ 0) :
    Pe x := by
  have h := (parity_induction alg zero adde addo ιe ιo x).1
  rwa [prZ_of_mem hx] at h


-- @@ L117-123 verbatim
lemma odd_induction' {Pe Po : E → Prop} (alg : ∀ r, Pe (algebraMap R E r)) (zero : Po 0)
    (adde : ∀ x y, Pe x → Pe y → Pe (x + y)) (addo : ∀ x y, Po x → Po y → Po (x + y))
    (ιe : ∀ m x, x ∈ evenOdd Q₀ 1 → Po x → Pe (ι R m * x))
    (ιo : ∀ m x, x ∈ evenOdd Q₀ 0 → Pe x → Po (ι R m * x)) {x : E} (hx : x ∈ evenOdd Q₀ 1) :
    Po x := by
  have h := (parity_induction alg zero adde addo ιe ιo x).2
  rwa [prZ_of_mem hx] at h


-- @@ L125-132 verbatim
lemma prZ_add (x : E) : prZ 0 x + prZ 1 x = x := by
  induction x using induction with
  | alg r =>
    rw [prZ_of_mem (algebraMap_mem r), prZ_of_mem_ne (algebraMap_mem r) (by decide), add_zero]
  | add x y hx hy =>
    rw [map_add, map_add, add_add_add_comm, hx, hy]
  | ι_mul m x hx =>
    rw [prZ_zero_ι_mul, prZ_one_ι_mul, ← mul_add, add_comm, hx]


-- @@ L134-134 verbatim
/-! ## Graded commutativity -/


-- @@ L136-139 verbatim
/-- Two anticommuting vectors. -/
lemma ι_anti (a b : L) (x : E) : ι R a * (ι R b * x) = -(ι R b * (ι R a * x)) := by
  rw [← mul_assoc, ← mul_assoc, eq_neg_of_add_eq_zero_left (ι_add_mul_swap (R := R) a b),
    neg_mul]


-- @@ L141-142 verbatim
lemma ι_ι (a : L) (x : E) : ι R a * (ι R a * x) = 0 := by
  rw [← mul_assoc, ι_sq_zero, zero_mul]


-- @@ L144-151 verbatim
/-- **A vector twist-commutes** with everything: `m x = x̂ m`. -/
lemma ι_mul_comm (m : L) (x : E) : ι R m * x = involute x * ι R m := by
  induction x using induction with
  | alg r => rw [AlgHom.commutes, Algebra.commutes]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]
  | ι_mul n x hx =>
    rw [ι_anti, hx, map_mul, involute_ι]
    noncomm_ring


-- @@ L153-154 verbatim
lemma ι_mul_involute (m : L) (x : E) : ι R m * involute x = x * ι R m := by
  rw [ι_mul_comm, involute_involutive]


-- @@ L156-165 verbatim
/-- **Graded commutativity**: even elements are central and odd elements twist-commute. -/
theorem mul_comm_parity (x : E) :
    (∀ y, prZ 0 x * y = y * prZ 0 x) ∧ (∀ y, prZ 1 x * y = involute y * prZ 1 x) := by
  refine parity_induction (Pe := fun x => ∀ y, x * y = y * x)
    (Po := fun x => ∀ y, x * y = involute y * x) (fun r y => Algebra.commutes r y)
    (fun y => by rw [zero_mul, mul_zero]) (fun x x' hx hx' y => by rw [add_mul, mul_add, hx, hx'])
    (fun x x' hx hx' y => by rw [add_mul, mul_add, hx, hx']) (fun m x _ hx y => ?_)
    (fun m x _ hx y => ?_) x
  · rw [mul_assoc, hx, ← mul_assoc, ι_mul_involute, mul_assoc]
  · rw [mul_assoc, hx, ← mul_assoc, ι_mul_comm, mul_assoc]


-- @@ L167-169 verbatim
lemma mul_comm_even {x : E} (hx : x ∈ evenOdd Q₀ 0) (y : E) : x * y = y * x := by
  have h := (mul_comm_parity x).1 y
  rwa [prZ_of_mem hx] at h


-- @@ L171-173 verbatim
lemma mul_comm_odd {x : E} (hx : x ∈ evenOdd Q₀ 1) (y : E) : x * y = involute y * x := by
  have h := (mul_comm_parity x).2 y
  rwa [prZ_of_mem hx] at h


-- @@ L175-175 verbatim
/-! ## The even derivations `D_f` -/


-- @@ L177-183 verbatim
/-- The step of the even derivation extending an endomorphism `f`. -/
noncomputable def dStep (f : L →ₗ[R] L) : L →ₗ[R] E × E →ₗ[R] E :=
  LinearMap.mk₂ R (fun m p => ι R (f m) * p.1 + ι R m * p.2)
    (fun m m' p => by simp only [map_add, add_mul]; abel)
    (fun c m p => by simp only [map_smul, smul_mul_assoc, smul_add])
    (fun m p q => by simp only [Prod.fst_add, Prod.snd_add, mul_add]; abel)
    (fun c m p => by simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_add])


-- @@ L185-186 verbatim
lemma dStep_apply (f : L →ₗ[R] L) (m : L) (p : E × E) :
    dStep f m p = ι R (f m) * p.1 + ι R m * p.2 := rfl


-- @@ L188-192 verbatim
/-- **The even derivation extending `f`**: `D_f (m ∧ x) = f m ∧ x + m ∧ D_f x`. -/
noncomputable def D (f : L →ₗ[R] L) : E →ₗ[R] E :=
  foldr' Q₀ (dStep f) (fun m x fx => by
    rw [dStep_apply, dStep_apply, QuadraticMap.zero_apply, zero_smul, mul_add, ι_anti, ι_ι,
      add_zero, neg_add_cancel]) 0


-- @@ L194-196 verbatim
lemma D_ι_mul (f : L →ₗ[R] L) (m : L) (x : E) :
    D f (ι R m * x) = ι R (f m) * x + ι R m * D f x :=
  foldr'_ι_mul _ _ _ _ _ _


-- @@ L198-199 verbatim
lemma D_algebraMap (f : L →ₗ[R] L) (r : R) : D f (algebraMap R E r) = 0 := by
  rw [D, foldr'_algebraMap, smul_zero]


-- @@ L201-202 verbatim
lemma D_one (f : L →ₗ[R] L) : D f 1 = 0 := by
  rw [← map_one (algebraMap R E), D_algebraMap]


-- @@ L204-205 verbatim
lemma D_ι (f : L →ₗ[R] L) (m : L) : D f (ι R m) = ι R (f m) := by
  rw [← mul_one (ι R m), D_ι_mul, D_one, mul_zero, add_zero, mul_one]


-- @@ L207-215 verbatim
/-- **`D_f` is a derivation.** -/
theorem D_mul (f : L →ₗ[R] L) (x y : E) : D f (x * y) = D f x * y + x * D f y := by
  induction x using induction with
  | alg r =>
    rw [D_algebraMap, zero_mul, zero_add, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul, add_mul]; abel
  | ι_mul m x hx =>
    rw [mul_assoc, D_ι_mul, hx, D_ι_mul]
    noncomm_ring


-- @@ L217-222 verbatim
lemma D_add (f g : L →ₗ[R] L) (x : E) : D (f + g) x = D f x + D g x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, D_algebraMap, add_zero]
  | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx']; abel
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, D_ι_mul, hx, LinearMap.add_apply, map_add, add_mul, mul_add]; abel


-- @@ L224-230 verbatim
lemma D_smul (c : R) (f : L →ₗ[R] L) (x : E) : D (c • f) x = c • D f x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, smul_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', smul_add]
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, hx, LinearMap.smul_apply, map_smul, smul_mul_assoc, mul_smul_comm,
      smul_add]


-- @@ L232-243 verbatim
/-- **The commutator of the derivations**: `[D_f, D_g] = D_[f, g]`. -/
theorem D_comm (f g : L →ₗ[R] L) (x : E) :
    D f (D g x) - D g (D f x) = D (f ∘ₗ g - g ∘ₗ f) x := by
  induction x using induction with
  | alg r => rw [D_algebraMap, D_algebraMap, map_zero, map_zero, sub_zero, D_algebraMap]
  | add x x' hx hx' =>
    rw [map_add, map_add, map_add, map_add, map_add, ← hx, ← hx']; abel
  | ι_mul m x hx =>
    rw [D_ι_mul, D_ι_mul, map_add, map_add, D_ι_mul, D_ι_mul, D_ι_mul, D_ι_mul, D_ι_mul,
      ← hx, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub, sub_mul,
      mul_sub]
    abel


-- @@ L245-245 verbatim
/-! ## The derivations `D_m` of the adjoint action -/


-- @@ L247-252 verbatim
variable (R L) in
/-- **The derivation `D_m` extending `ad m`**, linear in `m`. -/
noncomputable def Dm : L →ₗ[R] E →ₗ[R] E where
  toFun m := D (LieAlgebra.ad R L m)
  map_add' m n := LinearMap.ext fun x => by rw [map_add, D_add]; rfl
  map_smul' c m := LinearMap.ext fun x => by rw [map_smul, D_smul]; rfl


-- @@ L254-254 verbatim
lemma Dm_apply (m : L) (x : E) : Dm R L m x = D (LieAlgebra.ad R L m) x := rfl


-- @@ L256-257 verbatim
lemma Dm_ι_mul (m n : L) (x : E) : Dm R L m (ι R n * x) = ι R ⁅m, n⁆ * x + ι R n * Dm R L m x :=
  D_ι_mul _ _ _


-- @@ L259-259 verbatim
lemma Dm_algebraMap (m : L) (r : R) : Dm R L m (algebraMap R E r) = 0 := D_algebraMap _ _


-- @@ L261-261 verbatim
lemma Dm_one (m : L) : Dm R L m 1 = 0 := D_one _


-- @@ L263-263 verbatim
lemma Dm_ι (m n : L) : Dm R L m (ι R n) = ι R ⁅m, n⁆ := D_ι _ _


-- @@ L265-266 verbatim
lemma Dm_mul (m : L) (x y : E) : Dm R L m (x * y) = Dm R L m x * y + x * Dm R L m y :=
  D_mul _ _ _


-- @@ L268-269 verbatim
lemma Dm_self (m : L) (x : E) : Dm R L m (ι R m * x) = ι R m * Dm R L m x := by
  rw [Dm_ι_mul, lie_self, map_zero, zero_mul, zero_add]


-- @@ L271-277 verbatim
/-- **`m ↦ D_m` is a Lie morphism**: `[D_m, D_n] = D_[m, n]`. -/
theorem Dm_comm (m n : L) (x : E) :
    Dm R L m (Dm R L n x) - Dm R L n (Dm R L m x) = Dm R L ⁅m, n⁆ x := by
  rw [Dm_apply, Dm_apply, Dm_apply, Dm_apply, D_comm, Dm_apply]
  congr 2
  ext k
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LieAlgebra.ad_apply, lie_lie]


-- @@ L279-279 verbatim
/-! ## The Chevalley–Eilenberg operator -/


-- @@ L281-289 verbatim
/-- The step of the Chevalley–Eilenberg operator. -/
noncomputable def δStep : L →ₗ[R] E × E →ₗ[R] E :=
  LinearMap.mk₂ R (fun m p => -Dm R L m p.1 - ι R m * p.2)
    (fun m m' p => by simp only [map_add, LinearMap.add_apply, add_mul]; abel)
    (fun c m p => by simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, smul_sub,
      smul_neg])
    (fun m p q => by simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]; abel)
    (fun c m p => by simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, map_smul, smul_sub,
      smul_neg])


-- @@ L291-291 verbatim
lemma δStep_apply (m : L) (p : E × E) : δStep (R := R) m p = -Dm R L m p.1 - ι R m * p.2 := rfl


-- @@ L293-299 verbatim
variable (R L) in
/-- **The Chevalley–Eilenberg operator** `Δ (m ∧ x) = -D_m x - m ∧ Δ x`. -/
noncomputable def Δ : E →ₗ[R] E :=
  foldr' Q₀ δStep (fun m x fx => by
    rw [δStep_apply, δStep_apply, QuadraticMap.zero_apply, zero_smul, Dm_self, mul_sub, mul_neg,
      ι_ι]
    simp) 0


-- @@ L301-302 verbatim
lemma Δ_ι_mul (m : L) (x : E) : Δ R L (ι R m * x) = -Dm R L m x - ι R m * Δ R L x :=
  foldr'_ι_mul _ _ _ _ _ _


-- @@ L304-305 verbatim
lemma Δ_algebraMap (r : R) : Δ R L (algebraMap R E r) = 0 := by
  rw [Δ, foldr'_algebraMap, smul_zero]


-- @@ L307-308 verbatim
lemma Δ_one : Δ R L (1 : E) = 0 := by
  rw [← map_one (algebraMap R E), Δ_algebraMap]


-- @@ L310-311 verbatim
lemma Δ_ι (m : L) : Δ R L (ι R m) = 0 := by
  rw [← mul_one (ι R m), Δ_ι_mul, Δ_one, Dm_one, mul_zero, neg_zero, sub_zero]


-- @@ L313-322 verbatim
/-- **`Δ` commutes with the derivations `D_m`.** -/
theorem Δ_Dm (m : L) (x : E) : Δ R L (Dm R L m x) = Dm R L m (Δ R L x) := by
  induction x using induction with
  | alg r => rw [Dm_algebraMap, Δ_algebraMap, map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | ι_mul n x hx =>
    have h := Dm_comm (R := R) m n x
    rw [Dm_ι_mul, map_add, Δ_ι_mul, Δ_ι_mul, Δ_ι_mul, hx, map_sub, map_neg, Dm_ι_mul]
    rw [← h]
    abel


-- @@ L324-331 verbatim
/-- **`Δ² = 0`.** -/
theorem Δ_Δ (x : E) : Δ R L (Δ R L x) = 0 := by
  induction x using induction with
  | alg r => rw [Δ_algebraMap, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]
  | ι_mul n x hx =>
    rw [Δ_ι_mul, map_sub, map_neg, Δ_Dm, Δ_ι_mul, hx, mul_zero, sub_zero]
    abel


-- @@ L333-333 verbatim
/-! ## The deviation -/


-- @@ L335-343 verbatim
variable (R L) in
/-- **The deviation of `Δ`** from being a derivation:
`⟨x, y⟩ = Δ (x y) - (Δ x) y - x̂ (Δ y)`. -/
noncomputable def dv : E →ₗ[R] E →ₗ[R] E :=
  LinearMap.mk₂ R (fun x y => Δ R L (x * y) - Δ R L x * y - involute x * Δ R L y)
    (fun x x' y => by simp only [add_mul, map_add]; abel)
    (fun c x y => by simp only [smul_mul_assoc, map_smul, smul_sub])
    (fun x y y' => by simp only [mul_add, map_add]; abel)
    (fun c x y => by simp only [mul_smul_comm, map_smul, smul_sub])


-- @@ L345-346 verbatim
lemma dv_apply (x y : E) :
    dv R L x y = Δ R L (x * y) - Δ R L x * y - involute x * Δ R L y := rfl


-- @@ L348-350 verbatim
lemma dv_algebraMap (r : R) (y : E) : dv R L (algebraMap R E r) y = 0 := by
  rw [dv_apply, Δ_algebraMap, zero_mul, sub_zero, AlgHom.commutes, ← Algebra.smul_def,
    ← Algebra.smul_def, map_smul, sub_self]


-- @@ L352-357 verbatim
/-- **The recursion of the deviation**: `⟨m ∧ x, y⟩ = -x D_m y - m ∧ ⟨x, y⟩`. -/
theorem dv_ι_mul (m : L) (x y : E) :
    dv R L (ι R m * x) y = -(x * Dm R L m y) - ι R m * dv R L x y := by
  rw [dv_apply, dv_apply, mul_assoc, Δ_ι_mul, Δ_ι_mul, Dm_mul, map_mul involute (ι R m) x,
    involute_ι]
  noncomm_ring


-- @@ L359-361 verbatim
lemma dv_ι (m : L) (y : E) : dv R L (ι R m) y = -Dm R L m y := by
  rw [← mul_one (ι R m), dv_ι_mul, ← map_one (algebraMap R E), dv_algebraMap, map_one, one_mul,
    mul_zero, sub_zero]


-- @@ L363-365 verbatim
/-- **On vectors, the deviation is the opposite of the bracket.** -/
lemma dv_ι_ι (m n : L) : dv R L (ι R m) (ι R n) = -ι R ⁅m, n⁆ := by
  rw [dv_ι, Dm_ι]


-- @@ L367-389 verbatim
/-- **`Δ` is of order at most two**: the deviation is a graded derivation in its second argument,
`⟨x, y z⟩ = ⟨x, y⟩ z + ŷ ⟨x, z⟩` for `x` even and `⟨x, y⟩ z + y ⟨x, z⟩` for `x` odd. -/
theorem dv_mul_parity (x : E) :
    (∀ y z, dv R L (prZ 0 x) (y * z)
      = dv R L (prZ 0 x) y * z + involute y * dv R L (prZ 0 x) z) ∧
    (∀ y z, dv R L (prZ 1 x) (y * z) = dv R L (prZ 1 x) y * z + y * dv R L (prZ 1 x) z) := by
  refine parity_induction
    (Pe := fun x => ∀ y z, dv R L x (y * z) = dv R L x y * z + involute y * dv R L x z)
    (Po := fun x => ∀ y z, dv R L x (y * z) = dv R L x y * z + y * dv R L x z)
    (fun r y z => by rw [dv_algebraMap, dv_algebraMap, dv_algebraMap, zero_mul, mul_zero,
      add_zero])
    (fun y z => by simp only [map_zero, LinearMap.zero_apply, zero_mul, mul_zero, add_zero])
    (fun x x' hx hx' y z => by
      simp only [map_add, LinearMap.add_apply, add_mul, mul_add, hx y z, hx' y z]; abel)
    (fun x x' hx hx' y z => by
      simp only [map_add, LinearMap.add_apply, add_mul, mul_add, hx y z, hx' y z]; abel)
    (fun m x hxo hx y z => ?_) (fun m x hxe hx y z => ?_) x
  · rw [dv_ι_mul, dv_ι_mul, dv_ι_mul, hx, Dm_mul, mul_add, mul_add, ← mul_assoc x y,
      mul_comm_odd hxo y, ← mul_assoc (ι R m) y, ι_mul_comm m y]
    noncomm_ring
  · rw [dv_ι_mul, dv_ι_mul, dv_ι_mul, hx, Dm_mul, mul_add, mul_add, ← mul_assoc x y,
      mul_comm_even hxe y, ← mul_assoc (ι R m) (involute y), ι_mul_involute m y]
    noncomm_ring


-- @@ L391-394 verbatim
lemma dv_mul_even {x : E} (hx : x ∈ evenOdd Q₀ 0) (y z : E) :
    dv R L x (y * z) = dv R L x y * z + involute y * dv R L x z := by
  have h := (dv_mul_parity x).1 y z
  rwa [prZ_of_mem hx] at h


-- @@ L396-399 verbatim
lemma dv_mul_odd {x : E} (hx : x ∈ evenOdd Q₀ 1) (y z : E) :
    dv R L x (y * z) = dv R L x y * z + y * dv R L x z := by
  have h := (dv_mul_parity x).2 y z
  rwa [prZ_of_mem hx] at h


-- @@ L401-401 verbatim
/-! ## Parities of the operations -/


-- @@ L403-405 verbatim
lemma mul_mem' {i j k : ZMod 2} (h : i + j = k) {x y : E} (hx : x ∈ evenOdd Q₀ i)
    (hy : y ∈ evenOdd Q₀ j) : x * y ∈ evenOdd Q₀ k :=
  h ▸ SetLike.mul_mem_graded hx hy


-- @@ L407-410 verbatim
lemma zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl


-- @@ L412-417 verbatim
lemma involute_mem {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) : involute x ∈ evenOdd Q₀ i := by
  obtain rfl | rfl := zmod2_cases i
  · rw [CliffordAlgebra.involute_eq_of_mem_even hx]
    exact hx
  · rw [CliffordAlgebra.involute_eq_of_mem_odd hx]
    exact Submodule.neg_mem _ hx


-- @@ L419-425 verbatim
lemma mem_of_parity {P : ZMod 2 → E → Prop} (h : ∀ x, P 0 (prZ 0 x) ∧ P 1 (prZ 1 x)) {i : ZMod 2}
    {x : E} (hx : x ∈ evenOdd Q₀ i) : P i x := by
  obtain rfl | rfl := zmod2_cases i
  · have := (h x).1
    rwa [prZ_of_mem hx] at this
  · have := (h x).2
    rwa [prZ_of_mem hx] at this


-- @@ L427-442 verbatim
/-- **`D_f` is even.** -/
lemma D_mem (f : L →ₗ[R] L) {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) :
    D f x ∈ evenOdd Q₀ i := by
  refine mem_of_parity (P := fun i x => D f x ∈ evenOdd Q₀ i) (fun x => parity_induction
    (Pe := fun x => D f x ∈ evenOdd Q₀ 0) (Po := fun x => D f x ∈ evenOdd Q₀ 1)
    (fun r => by beta_reduce; rw [D_algebraMap]; exact Submodule.zero_mem _)
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun m x hx h => ?_) (fun m x hx h => ?_) x) hx
  · beta_reduce
    rw [D_ι_mul]
    exact Submodule.add_mem _ (mul_mem' (by decide) (ι_mem _) hx) (mul_mem' (by decide) (ι_mem _) h)
  · beta_reduce
    rw [D_ι_mul]
    exact Submodule.add_mem _ (mul_mem' (by decide) (ι_mem _) hx) (mul_mem' (by decide) (ι_mem _) h)


-- @@ L444-460 verbatim
/-- **`Δ` is odd.** -/
lemma Δ_mem {i : ZMod 2} {x : E} (hx : x ∈ evenOdd Q₀ i) : Δ R L x ∈ evenOdd Q₀ (i + 1) := by
  refine mem_of_parity (P := fun i x => Δ R L x ∈ evenOdd Q₀ (i + 1)) (fun x => parity_induction
    (Pe := fun x => Δ R L x ∈ evenOdd Q₀ (0 + 1)) (Po := fun x => Δ R L x ∈ evenOdd Q₀ (1 + 1))
    (fun r => by beta_reduce; rw [Δ_algebraMap]; exact Submodule.zero_mem _)
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun x y hx hy => by beta_reduce; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun m x hx h => ?_) (fun m x hx h => ?_) x) hx
  · beta_reduce
    rw [Δ_ι_mul]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (D_mem _ hx))
      (mul_mem' (by decide) (ι_mem _) h)
  · beta_reduce
    rw [Δ_ι_mul]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (D_mem _ hx))
      (mul_mem' (by decide) (ι_mem _) h)


-- @@ L462-467 verbatim
/-- **The deviation is odd.** -/
lemma dv_mem {i j : ZMod 2} {x y : E} (hx : x ∈ evenOdd Q₀ i) (hy : y ∈ evenOdd Q₀ j) :
    dv R L x y ∈ evenOdd Q₀ (i + j + 1) := by
  rw [dv_apply]
  refine Submodule.sub_mem _ (Submodule.sub_mem _ (Δ_mem (mul_mem' rfl hx hy))
    (mul_mem' (by ring) (Δ_mem hx) hy)) (mul_mem' (by ring) (involute_mem hx) (Δ_mem hy))


-- @@ L469-469 verbatim
/-! ## The super module -/


-- @@ L471-472 verbatim
/-- The parity of a Boolean. -/
def bz (b : Bool) : ZMod 2 := cond b 1 0


-- @@ L474-475 verbatim
lemma bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by
  cases a <;> cases b <;> decide


-- @@ L477-478 verbatim
lemma bz_not (a : Bool) : bz (!a) = bz a + 1 := by
  cases a <;> decide


-- @@ L480-482 verbatim
lemma bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)


-- @@ L484-492 verbatim
/-- **The exterior algebra is a super module**, by its parity components. -/
noncomputable instance instSuperMod : SuperMod R E where
  pr b := prZ (bz b)
  pr_add x := prZ_add x
  pr_pr b b' x := by
    split_ifs with h
    · subst h
      exact prZ_of_mem (prZ_mem _ _)
    · exact prZ_of_mem_ne (prZ_mem _ _) fun h' => h (bz_injective h').symm


-- @@ L494-495 verbatim
lemma isP_iff (p : Bool) (x : E) : EndGr.IsP (R := R) p x ↔ x ∈ evenOdd Q₀ (bz p) :=
  ⟨fun h => h ▸ prZ_mem _ _, fun h => prZ_of_mem h⟩


-- @@ L497-501 verbatim
lemma involute_eq_σ {p : Bool} {x : E} (hx : x ∈ evenOdd Q₀ (bz p)) :
    involute x = GerBV.σ R p • x := by
  cases p
  · rw [CliffordAlgebra.involute_eq_of_mem_even hx, GerBV.σ_false, one_smul]
  · rw [CliffordAlgebra.involute_eq_of_mem_odd hx, GerBV.σ_true, neg_one_smul]


-- @@ L503-508 verbatim
/-- **Graded commutativity**: `x y = σ(|x| |y|) y x`. -/
lemma mul_comm_σ {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) : x * y = GerBV.σ R (p && q) • (y * x) := by
  cases p
  · rw [mul_comm_even hx, Bool.false_and, GerBV.σ_false, one_smul]
  · rw [mul_comm_odd hx, involute_eq_σ hy, Bool.true_and, smul_mul_assoc]


-- @@ L510-522 verbatim
/-- **The deviation is graded symmetric**: `⟨x, y⟩ = σ(|x| |y|) ⟨y, x⟩`. -/
lemma dv_comm {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) : dv R L x y = GerBV.σ R (p && q) • dv R L y x := by
  have c1 := congrArg (Δ R L) (mul_comm_σ hx hy)
  have c2 := mul_comm_σ (R := R) (L := L) (p := !p) (q := q) (by rw [bz_not]; exact Δ_mem hx) hy
  have c3 := mul_comm_σ (R := R) (L := L) (p := p) (q := !q) hx (by rw [bz_not]; exact Δ_mem hy)
  rw [map_smul] at c1
  rw [dv_apply, dv_apply, involute_eq_σ hx, involute_eq_σ hy]
  cases p <;> cases q <;> simp at c1 c2 c3 ⊢
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; abel
  · rw [c1, c2, c3]; module


-- @@ L524-524 verbatim
/-! ## The Gerstenhaber algebra -/


-- @@ L526-529 verbatim
lemma dev_eq {p : Bool} {x : E} (hx : x ∈ evenOdd Q₀ (bz p)) (y : E) :
    GerBV.dev (LinearMap.mul R E) (Δ R L) p x y = dv R L x y := by
  rw [dv_apply, involute_eq_σ hx, smul_mul_assoc]
  rfl


-- @@ L531-538 verbatim
/-- **The Leibniz rule**: `⟨x, y z⟩ = ⟨x, y⟩ z + σ((|x| + 1) |y|) y ⟨x, z⟩`. -/
lemma dv_mul_σ {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p)) (hy : y ∈ evenOdd Q₀ (bz q))
    (z : E) :
    dv R L x (y * z) = dv R L x y * z + GerBV.σ R ((!p) && q) • (y * dv R L x z) := by
  cases p
  · rw [dv_mul_even hx, involute_eq_σ hy, smul_mul_assoc]
    rfl
  · rw [dv_mul_odd hx, Bool.not_true, Bool.false_and, GerBV.σ_false, one_smul]


-- @@ L540-559 verbatim
/-- **The Jacobi identity** of the deviation. -/
lemma dv_jacobi {p q : Bool} {x y : E} (hx : x ∈ evenOdd Q₀ (bz p))
    (hy : y ∈ evenOdd Q₀ (bz q)) (z : E) :
    dv R L (dv R L x y) z + GerBV.σ R p • dv R L x (dv R L y z)
      + GerBV.σ R ((!p) && q) • dv R L y (dv R L x z) = 0 := by
  have J := GerBV.dev_jacobi (μ := LinearMap.mul R E) (Δ := Δ R L)
    (H := fun p x => x ∈ evenOdd Q₀ (bz p)) Δ_Δ
    (fun p q x y z hx hy => by
      simp only [dev_eq hx, LinearMap.mul_apply']
      exact dv_mul_σ hx hy z)
    (fun p x hx => by beta_reduce at hx ⊢; rw [bz_not]; exact Δ_mem hx) z hx hy
  have hxy : dv R L x y ∈ evenOdd Q₀ (bz (!(xor p q))) := by
    rw [bz_not, bz_xor]
    exact dv_mem hx hy
  rw [dev_eq hy, dev_eq hx, dev_eq hx, dev_eq hxy, dev_eq hx, dev_eq hy] at J
  cases p <;> cases q <;> simp at J ⊢
  · rw [J]; abel
  · rw [J]; abel
  · rw [J]; module
  · rw [J]; module


-- @@ L561-563 verbatim
variable (R L) in
/-- The wedge product, as a binary operation. -/
noncomputable def mulOp : EndOp R E (Fin 2) := FreeBin.bilinOp (LinearMap.mul R E)


-- @@ L565-567 verbatim
variable (R L) in
/-- The deviation of `Δ`, as a binary operation. -/
noncomputable def dvOp : EndOp R E (Fin 2) := FreeBin.bilinOp (dv R L)


-- @@ L569-569 verbatim
lemma mulOp_apply (x y : E) : mulOp R L ![x, y] = x * y := rfl


-- @@ L571-571 verbatim
lemma dvOp_apply (x y : E) : dvOp R L ![x, y] = dv R L x y := rfl


-- @@ L573-583 verbatim
/-- A binary operation sending inputs of parities `p, q` to the parity `b + p + q` is of parity
`b`. -/
lemma parML_two {b : Bool} {f : EndOp R E (Fin 2)}
    (h : ∀ p q x y, x ∈ evenOdd Q₀ (bz p) → y ∈ evenOdd Q₀ (bz q) →
      f ![x, y] ∈ evenOdd Q₀ (bz b + bz p + bz q)) :
    parML R E b f = f := by
  refine ext_hom fun c v hv => ?_
  rw [parML_apply_hom hv, EndGr.vec_two v, EndGr.vec_two c, Ger.tot_two]
  refine prZ_of_mem ?_
  rw [bz_xor, bz_xor, ← add_assoc]
  exact h _ _ _ _ ((isP_iff _ _).1 (hv 0)) ((isP_iff _ _).1 (hv 1))


-- @@ L585-598 verbatim
/-- **The exterior algebra of a Lie algebra is a Gerstenhaber algebra** under the wedge product
and the deviation of the Chevalley–Eilenberg operator. -/
theorem isGer : Ger.IsGer (mulOp R L) (dvOp R L) where
  par_m := parML_two fun p q x y hx hy => mul_mem' (by simp [bz]) hx hy
  par_l := parML_two fun p q x y hx hy => by
    rw [dvOp_apply]
    convert dv_mem hx hy using 1
    simp only [bz, cond_true]
    ring_nf
  comm p q x y hx hy := mul_comm_σ ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy)
  symm p q x y hx hy := dv_comm ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy)
  assoc p q r x y z _ _ _ := mul_assoc x y z
  leibniz p q r x y z hx hy _ := dv_mul_σ ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy) z
  jacobi p q r x y z hx hy _ := dv_jacobi ((isP_iff _ _).1 hx) ((isP_iff _ _).1 hy) z


-- @@ L600-603 verbatim
variable (R L) in
/-- **The exterior algebra of a Lie algebra is an algebra over the Gerstenhaber operad.** -/
noncomputable def gerAlg : GrAlgebra R E (GerOp R) :=
  Ger.algebraEquiv.symm ⟨(mulOp R L, dvOp R L), isGer⟩


-- @@ L605-609 verbatim
lemma sv_gerAlg_mul :
    EndGr.sv ((gerAlg R L).app _ (FreeGr.presGen (Ger.rel R) GerGen.mul)) = mulOp R L :=
  congrArg (fun z => z.1.1) (Ger.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, dvOp R L), isGer⟩ : {ml : EndOp R E (Fin 2) × EndOp R E (Fin 2) //
      Ger.IsGer ml.1 ml.2}))


-- @@ L611-615 verbatim
lemma sv_gerAlg_br :
    EndGr.sv ((gerAlg R L).app _ (FreeGr.presGen (Ger.rel R) GerGen.br)) = dvOp R L :=
  congrArg (fun z => z.1.2) (Ger.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, dvOp R L), isGer⟩ : {ml : EndOp R E (Fin 2) × EndOp R E (Fin 2) //
      Ger.IsGer ml.1 ml.2}))


-- @@ L617-617 verbatim
/-! ## The BV algebra -/


-- @@ L619-621 verbatim
variable (R L) in
/-- The Chevalley–Eilenberg operator, as a unary operation. -/
noncomputable def ΔOp : EndOp R E (Fin 1) := MultilinearMap.ofSubsingleton R E E 0 (Δ R L)


-- @@ L623-623 verbatim
lemma ΔOp_apply (x : E) : ΔOp R L ![x] = Δ R L x := rfl


-- @@ L625-628 verbatim
lemma BV_dv_eq {p : Bool} {x : E} (hx : x ∈ evenOdd Q₀ (bz p)) (y : E) :
    BV.dv (mulOp R L) (ΔOp R L) p x y = dv R L x y := by
  rw [BV.dv, dv_apply, involute_eq_σ hx, smul_mul_assoc]
  rfl


-- @@ L630-653 verbatim
/-- **The exterior algebra of a Lie algebra is a BV algebra** under the wedge product and the
Chevalley–Eilenberg operator. -/
theorem isBV : BV.IsBV (mulOp R L) (ΔOp R L) where
  par_m := isGer.par_m
  par_d := by
    refine ext_hom fun c v hv => ?_
    rw [parML_apply_hom hv]
    refine prZ_of_mem ?_
    have h0 : v = ![v 0] := funext fun i => by fin_cases i; rfl
    have hc : tot c = c 0 := by
      have : c = ![c 0] := funext fun i => by fin_cases i; rfl
      rw [this]
      cases c 0 <;> rfl
    rw [h0, ΔOp_apply, hc, Bool.true_xor, bz_not]
    exact Δ_mem ((isP_iff _ _).1 (hv 0))
  comm := isGer.comm
  assoc := isGer.assoc
  sq p x _ := by
    rw [ΔOp_apply, ΔOp_apply, Δ_Δ]
  order p q r x y z hx hy _ := by
    have hx' := (isP_iff _ _).1 hx
    have hy' := (isP_iff _ _).1 hy
    rw [BV_dv_eq hx', BV_dv_eq hx', BV_dv_eq hx']
    exact dv_mul_σ hx' hy' z


-- @@ L655-658 verbatim
variable (R L) in
/-- **The exterior algebra of a Lie algebra is an algebra over the BV operad.** -/
noncomputable def bvAlg : GrAlgebra R E (BVOp R) :=
  BV.algebraEquiv.symm ⟨(mulOp R L, ΔOp R L), isBV⟩


-- @@ L660-664 verbatim
lemma sv_bvAlg_mul :
    EndGr.sv ((bvAlg R L).app _ (FreeGr.presGen (BV.rel R) BVGen.mul)) = mulOp R L :=
  congrArg (fun z => z.1.1) (BV.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, ΔOp R L), isBV⟩ : {md : EndOp R E (Fin 2) × EndOp R E (Fin 1) //
      BV.IsBV md.1 md.2}))


-- @@ L666-670 verbatim
lemma sv_bvAlg_op :
    EndGr.sv ((bvAlg R L).app _ (FreeGr.presGen (BV.rel R) BVGen.op)) = ΔOp R L :=
  congrArg (fun z => z.1.2) (BV.algebraEquiv.apply_symm_apply
    (⟨(mulOp R L, ΔOp R L), isBV⟩ : {md : EndOp R E (Fin 2) × EndOp R E (Fin 1) //
      BV.IsBV md.1 md.2}))


-- @@ L672-672 verbatim
end ExtBV


-- @@ L674-674 verbatim
end Operad
