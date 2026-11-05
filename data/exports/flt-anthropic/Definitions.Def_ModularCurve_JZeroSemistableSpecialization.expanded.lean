import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_ComponentGroup


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace ModularCurve


-- @@ L12-12 verbatim
open AlgebraicCurve IsLocalRing


-- @@ L14-14 verbatim
local notation "Qbar" => AlgebraicClosure ℚ


-- @@ L16-16 verbatim
section Generic


-- @@ L18-19 verbatim
def PrimeToTorsion (q : ℕ) {M : Type*} [AddMonoid M] (x : M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ¬ q ∣ n ∧ n • x = 0


-- @@ L21-21 verbatim
namespace PrimeToTorsion


-- @@ L23-23 verbatim
variable {q : ℕ} {M M' : Type*}


-- @@ L25-26 verbatim
theorem zero [AddMonoid M] (hq : q ≠ 1) : PrimeToTorsion q (0 : M) :=
  ⟨1, Nat.one_pos, fun h => hq (Nat.dvd_one.mp h), nsmul_zero _⟩


-- @@ L28-33 verbatim
theorem add [AddCommMonoid M] (hq : q.Prime) {x y : M} (hx : PrimeToTorsion q x)
    (hy : PrimeToTorsion q y) : PrimeToTorsion q (x + y) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  obtain ⟨m, hm, hqm, hmy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, fun h => (hq.dvd_mul.mp h).elim hqn hqm, ?_⟩
  rw [nsmul_add, mul_nsmul, hnx, nsmul_zero, zero_add, mul_comm n m, mul_nsmul, hmy, nsmul_zero]


-- @@ L35-37 verbatim
theorem neg [AddCommGroup M] {x : M} (hx : PrimeToTorsion q x) : PrimeToTorsion q (-x) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  exact ⟨n, hn, hqn, by rw [neg_nsmul, hnx, neg_zero]⟩


-- @@ L39-42 verbatim
theorem map [AddMonoid M] [AddMonoid M'] {F : Type*} [FunLike F M M'] [AddMonoidHomClass F M M']
    (f : F) {x : M} (hx : PrimeToTorsion q x) : PrimeToTorsion q (f x) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  exact ⟨n, hn, hqn, by rw [← map_nsmul, hnx, map_zero]⟩


-- @@ L44-44 verbatim
end PrimeToTorsion


-- @@ L46-51 verbatim
def smulInvariants {G : Type*} [Group G] (I : Subgroup G) (M : Type*) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup M where
  carrier := {x | ∀ σ ∈ I, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := fun {x y} hx hy σ hσ => by rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := fun {x} hx σ hσ => by rw [smul_neg, hx σ hσ]


-- @@ L53-55 verbatim
theorem mem_smulInvariants {G : Type*} [Group G] {I : Subgroup G} {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] {x : M} : x ∈ smulInvariants I M ↔ ∀ σ ∈ I, σ • x = x :=
  Iff.rfl


-- @@ L57-57 verbatim
end Generic


-- @@ L59-59 verbatim
section Inertia


-- @@ L61-61 verbatim
variable (A : ValuationSubring Qbar) (M : ℕ)


-- @@ L63-64 verbatim
def inertiaInvariants : AddSubgroup (JZero M) :=
  smulInvariants (A.inertiaSubgroupIn ℚ) (JZero M)


-- @@ L66-66 verbatim
variable {A M}


-- @@ L68-70 verbatim
theorem mem_inertiaInvariants {x : JZero M} :
    x ∈ inertiaInvariants A M ↔ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  Iff.rfl


-- @@ L72-72 verbatim
end Inertia


-- @@ L74-74 verbatim
section Semistable


-- @@ L76-76 verbatim
variable (A : ValuationSubring Qbar) (N q : ℕ) (hq : q.Prime) [NeZero N]


-- @@ L78-80 verbatim
noncomputable local instance instDecidableEqResidueFieldSemistable :
    DecidableEq (ResidueField A) :=
  Classical.decEq _


-- @@ L82-86 verbatim
set_option synthInstance.maxHeartbeats 80000 in

noncomputable local instance instAlgebraResidueFieldModularFunctionFieldCSemistable :
    Algebra (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  inferInstance


-- @@ L88-89 verbatim
variable [Module HeckeAlg (JZero (N * q))] [Module HeckeAlg (JZero N)]
  [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]


-- @@ L91-170 verbatim
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

structure JZeroSemistableSpecialization where

  nodes : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
    Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))

  nodes_rational : ∀ s ∈ nodes,
    Function.Surjective (algebraMap (ResidueField A) s.1.ResidueField) ∧
      Function.Surjective (algebraMap (ResidueField A) s.2.ResidueField)

  frob : SemilinearAut (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  frob_nodeStable : SemilinearAut.IsNodeStable nodes frob

  baseAut_frob : ∀ a : ResidueField A, SemilinearAut.baseAut frob a = a ^ q

  nodePerm_nodePerm : ∀ s : ↥nodes, SemilinearAut.nodePerm nodes frob frob_nodeStable
    (SemilinearAut.nodePerm nodes frob frob_nodeStable s) = s

  width : ↥nodes → ℕ

  comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup width

  comp_heckeGen : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ = (((ℓ : ℕ) : ℤ) + 1) • comp x

  comp_hecke_of_comp_eq_zero : ∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
      (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨T • (x : JZero (N * q)), hx⟩ = 0

  comp_frob_of_comp_eq_zero : ∀ φ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt φ q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨φ • (x : JZero (N * q)), hx⟩ = 0

  sp : ↥(inertiaInvariants A (N * q)) →+
    GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N) nodes

  toPic0Pair_sp_heckeGen : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → GluedPic0.toPic0Pair nodes (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) =
        heckeGen ℓ • GluedPic0.toPic0Pair nodes (sp x)

  toPic0Pair_sp_eq_zero : ∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
      (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → GluedPic0.toPic0Pair nodes (sp x) = 0 →
        GluedPic0.toPic0Pair nodes (sp ⟨T • (x : JZero (N * q)), hx⟩) = 0

  sp_frob : ∀ φ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt φ q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → sp ⟨φ • (x : JZero (N * q)), hx⟩ =
        GluedPic0.glueMap nodes frob frob_nodeStable (sp x)

  sp_heckeGen_self : ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ⟨q, hq⟩ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → ∀ w : ↥nodes → Additive (ResidueField A)ˣ,
        sp x = GluedPic0.nodeUnit nodes w →
          sp ⟨heckeGen ⟨q, hq⟩ • (x : JZero (N * q)), hx⟩ = GluedPic0.nodeUnit nodes
            (fun t => w ((SemilinearAut.nodePerm nodes frob frob_nodeStable).symm t))

  sp_injective : ∀ x : ↥(inertiaInvariants A (N * q)),
    PrimeToTorsion q (x : JZero (N * q)) → comp x = 0 → sp x = 0 → x = 0

  exists_prime_torsion : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion (JZero (N * q)) 𝔪, ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p • x = 0

  spN : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  spN_hecke : ∀ (T : HeckeAlg) (y : JZero N), spN (T • y) = T • spN y

  spN_injective : ∀ y : JZero N, PrimeToTorsion q y → spN y = 0 → y = 0

  spN_surjective : ∀ c : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
    PrimeToTorsion q c → ∃ y : JZero N, PrimeToTorsion q y ∧ spN y = c


-- @@ L172-172 verbatim
end Semistable


-- @@ L174-174 verbatim
end ModularCurve


-- @@ L176-176 verbatim
end
