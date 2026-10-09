import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.CentralSequences


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology



-- @@ L29-29 verbatim
open scoped TensorProduct CStarAlgebra


-- @@ L31-31 verbatim
namespace KirchbergRordam

-- @@ L32-32 verbatim
namespace StarCompletion


-- @@ L34-34 verbatim
open UniformSpace

-- @@ L35-35 verbatim
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]



-- @@ L38-40 verbatim
@[simp]
lemma star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe star_isometry.uniformContinuous x



-- @@ L43-47 verbatim
instance completionNormedStarGroup : NormedStarGroup (Completion R) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simp only [star_coe, Completion.norm_coe, norm_star, le_refl]


-- @@ L49-49 verbatim
variable [NormedAlgebra ℂ R] [StarModule ℂ R]



-- @@ L52-52 verbatim
end StarCompletion


-- @@ L54-54 verbatim
end KirchbergRordam



-- @@ L57-57 verbatim
namespace KirchbergRordam.CStarInductiveLimit

-- @@ L58-58 verbatim
section

-- @@ L59-59 verbatim
universe u



-- @@ L62-62 verbatim
attribute [instance] System.cstar



-- @@ L65-66 verbatim
@[simp] lemma rawOf_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    rawOf S j (S.map i j h x) = rawOf S i x := DirectLimit.mk_apply _ _ _ _



-- @@ L69-70 verbatim
@[simp] lemma normLift_mk (S : System) (n : ℕ) (x : S.obj n) :
    normLift S (rawOf S n x) = ‖x‖ := rfl



-- @@ L73-74 verbatim
@[simp] theorem norm_rawOf (S : System) (n : ℕ) (x : S.obj n) :
    ‖rawOf S n x‖ = ‖x‖ := rfl



-- @@ L77-80 verbatim
def rawInclusion (S : System) : Raw S →⋆ₐ[ℂ] Algebra S where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' _ := (StarCompletion.star_coe _ _).symm


-- @@ L82-83 verbatim
def of (S : System) (n : ℕ) : S.obj n →⋆ₐ[ℂ] Algebra S :=
  (rawInclusion S).comp (rawOf S n)


-- @@ L85-89 verbatim
@[simp] theorem of_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    of S j (S.map i j h x) = of S i x := by
  change rawInclusion S (rawOf S j (S.map i j h x)) = _
  rw [rawOf_map]
  rfl


-- @@ L91-92 verbatim
@[simp] theorem norm_of (S : System) (n : ℕ) (x : S.obj n) : ‖of S n x‖ = ‖x‖ :=
  (UniformSpace.Completion.norm_coe _).trans (norm_rawOf S n x)


-- @@ L94-96 verbatim
theorem of_isometry (S : System) (n : ℕ) : Isometry (of S n) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_of S n


-- @@ L98-99 verbatim
instance (S : System) [Nontrivial (S.obj 0)] : Nontrivial (Algebra S) :=
  (of_isometry S 0).injective.nontrivial



-- @@ L102-102 verbatim
variable {C : Type*} [CStarAlgebra C]


-- @@ L104-111 verbatim
def rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Raw S →⋆ₐ[ℂ] C where
  __ := DirectLimit.Algebra.lift S.obj S.map C (fun n => (f n).toAlgHom) hf
  map_star' x := by
    refine DirectLimit.induction S.map ?_ x
    intro n x
    exact map_star (f n) x


-- @@ L113-115 verbatim
@[simp] theorem rawLift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : rawLift S f hf (rawOf S n x) = f n x := rfl


-- @@ L117-122 verbatim
theorem norm_rawLift_le (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (x : Raw S) : ‖rawLift S f hf x‖ ≤ ‖x‖ := by
  refine DirectLimit.induction S.map ?_ x
  intro n x
  exact NonUnitalStarAlgHom.norm_apply_le (f n) x


-- @@ L124-130 verbatim
theorem continuous_rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Continuous (rawLift S f hf) := by
  exact ((rawLift S f hf).toLinearMap.mkContinuous 1
    (fun x => by
      change ‖rawLift S f hf x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_rawLift_le S f hf x)).continuous



-- @@ L133-155 verbatim
def lift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Algebra S →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
      (continuous_rawLift S f hf) (algebraMap ℂ (Raw S) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (rawLift S f hf).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
        (continuous_rawLift S f hf) (star (x : Algebra S)) =
        star (UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
          (continuous_rawLift S f hf) (x : Algebra S))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (rawLift S f hf) x


-- @@ L157-161 verbatim
@[simp] theorem lift_rawInclusion (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) (x : Raw S) :
    lift S f hf (rawInclusion S x) = rawLift S f hf x :=
  UniformSpace.Completion.extensionHom_coe (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf) x


-- @@ L163-167 verbatim
@[simp] theorem lift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : lift S f hf (of S n x) = f n x := by
  change lift S f hf (rawInclusion S (rawOf S n x)) = _
  rw [lift_rawInclusion, rawLift_of]



-- @@ L170-176 verbatim
theorem induction_on (S : System) {P : Algebra S → Prop} (x : Algebra S)
    (hclosed : IsClosed {x | P x}) (hof : ∀ n x, P (of S n x)) : P x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    refine DirectLimit.induction S.map ?_ x
    exact hof



-- @@ L179-182 verbatim
theorem hom_ext (S : System) (f g : Algebra S →⋆ₐ[ℂ] C)
    (h : ∀ n x, f (of S n x) = g (of S n x)) : f = g := by
  ext x
  exact induction_on S x (isClosed_eq (map_continuous f) (map_continuous g)) h


-- @@ L184-188 verbatim
theorem denseRange_of (S : System) :
    DenseRange (fun p : Σ n, S.obj n => of S p.1 p.2) := by
  intro x
  exact induction_on S x isClosed_closure
    (fun n x => subset_closure ⟨⟨n,x⟩,rfl⟩)



-- @@ L191-193 verbatim
instance (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Algebra S) :=
  (denseRange_of S).separableSpace (continuous_sigma fun n => map_continuous (of S n))


-- @@ L195-195 verbatim
end


-- @@ L197-197 verbatim
universe u



-- @@ L200-200 verbatim
attribute [instance] Chain.cstar



-- @@ L203-204 verbatim
@[simp] lemma Chain.map_self (S : Chain) (i : ℕ) :
    S.map i i le_rfl = StarAlgHom.id ℂ _ := by simp [Chain.map, Nat.leRecOn_self]


-- @@ L206-209 verbatim
@[simp] lemma Chain.map_succ (S : Chain) (i j : ℕ) (h : i ≤ j) :
    S.map i (j+1) (h.trans (Nat.le_succ j)) = (S.step j).comp (S.map i j h) := by
  exact Nat.leRecOn_succ (C := fun n => S.obj i →⋆ₐ[ℂ] S.obj n)
    (next := fun {n} φ => (S.step n).comp φ) h (StarAlgHom.id ℂ (S.obj i))


-- @@ L211-217 verbatim
lemma Chain.map_map (S : Chain) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (x : S.obj i) : S.map j k hjk (S.map i j hij x) = S.map i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    rw [S.map_succ j k hjk, S.map_succ i k (hij.trans hjk)]
    exact congrArg (S.step k) ih


-- @@ L219-225 verbatim
lemma Chain.norm_map (S : Chain) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    ‖S.map i j h x‖ = ‖x‖ := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j h ih =>
    rw [S.map_succ i j h]
    exact (S.norm_step j (S.map i j h x)).trans ih



-- @@ L228-228 verbatim
end KirchbergRordam.CStarInductiveLimit



-- @@ L231-231 verbatim
end


-- @@ L233-233 verbatim
end OAI
