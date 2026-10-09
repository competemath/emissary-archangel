import OAI.Geometry.LatticeCovering.Chains


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
section

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Real

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open scoped BigOperators

-- @@ L15-15 verbatim
open MeasureTheory Set

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
open Module Submodule MeasureTheory

-- @@ L18-18 verbatim
open scoped BigOperators

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open Real Filter Topology

-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open scoped BigOperators

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open Filter Topology Asymptotics

-- @@ L25-25 verbatim
noncomputable section

-- @@ L26-26 verbatim
open scoped BigOperators

-- @@ L27-27 verbatim
open Classical

-- @@ L28-28 verbatim
noncomputable section

-- @@ L29-29 verbatim
open scoped BigOperators

-- @@ L30-30 verbatim
open Classical

-- @@ L31-31 verbatim
noncomputable section

-- @@ L32-32 verbatim
open scoped BigOperators

-- @@ L33-33 verbatim
open Classical

-- @@ L34-34 verbatim
noncomputable section

-- @@ L35-35 verbatim
open scoped BigOperators

-- @@ L36-36 verbatim
noncomputable section

-- @@ L37-37 verbatim
open Module MeasureTheory


-- @@ L39-39 verbatim
namespace SingleLatticeCovering.LatticeGeometry



-- @@ L42-51 verbatim
def appendEquiv (m n : ℕ) : ((Fin m → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin (m+n) → ℝ) :=
  { Fin.appendEquiv m n with
    map_add' := by
      intro x y
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Fin.appendEquiv]
    map_smul' := by
      intro a x
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Fin.appendEquiv] }


-- @@ L53-54 verbatim
@[simp] lemma appendEquiv_apply (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    appendEquiv m n x = Fin.append x.1 x.2 := rfl

-- @@ L55-57 verbatim
@[simp] lemma appendEquiv_symm_apply (m n : ℕ) (y : Fin (m+n) → ℝ) :
    (appendEquiv m n).symm y =
      (fun j => y (Fin.castAdd n j),fun j => y (Fin.natAdd m j)) := rfl


-- @@ L59-60 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L62-64 verbatim
instance prod_discrete (L : Submodule ℤ E) (N : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology N] : DiscreteTopology (L.prod N) :=
  (Homeomorph.Set.prod (L : Set E) (N : Set F)).symm.discreteTopology


-- @@ L66-73 verbatim
instance prod_full (L : Submodule ℤ E) (N : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology N] [IsZLattice ℝ L] [IsZLattice ℝ N] :
    IsZLattice ℝ (L.prod N) := by
  constructor
  change Submodule.span ℝ ((L : Set E) ×ˢ (N : Set F)) = ⊤
  rw [Submodule.span_prod_eq ℝ L.zero_mem N.zero_mem, IsZLattice.span_top, IsZLattice.span_top]
  ext x
  simp


-- @@ L75-82 verbatim
def prodSubtypeEquiv (L : Submodule ℤ E) (N : Submodule ℤ F) :
    (L.prod N) ≃ₗ[ℤ] (L × N) where
  toFun x := (⟨x.1.1,x.2.1⟩,⟨x.1.2,x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1),x.1.2,x.2.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl


-- @@ L84-86 verbatim
abbrev finProduct {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) : Submodule ℤ (Fin (m+n) → ℝ) :=
  ZLattice.comap ℝ (L.prod N) (appendEquiv m n).symm.toLinearMap


-- @@ L88-91 verbatim
@[simp] lemma mem_finProduct {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) (x : Fin (m+n) → ℝ) :
    x ∈ finProduct L N ↔
      (fun j => x (Fin.castAdd n j)) ∈ L ∧ (fun j => x (Fin.natAdd m j)) ∈ N := Iff.rfl


-- @@ L93-98 verbatim
instance finProduct_discrete {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N] :
    DiscreteTopology (finProduct L N) := by
  change DiscreteTopology (ZLattice.comap ℝ (L.prod N)
    (appendEquiv m n).symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L100-105 verbatim
instance finProduct_full {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N] : IsZLattice ℝ (finProduct L N) := by
  change IsZLattice ℝ (ZLattice.comap ℝ (L.prod N)
    (appendEquiv m n).symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L107-111 verbatim
def finProductBasis {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) (b : Basis (Fin m) ℤ L) (c : Basis (Fin n) ℤ N) :
    Basis (Fin (m+n)) ℤ (finProduct L N) :=
  (((b.prod c).map (prodSubtypeEquiv L N).symm).ofZLatticeComap ℝ (L.prod N)
    (appendEquiv m n).symm).reindex finSumFinEquiv


-- @@ L113-132 verbatim
lemma finProduct_covolume {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N] :
    ZLattice.covolume (finProduct L N) = ZLattice.covolume L * ZLattice.covolume N := by
  let b := IsZLattice.basis L
  let c := IsZLattice.basis N
  rw [ZLattice.covolume_eq_det _ (finProductBasis L N b c),
    ZLattice.covolume_eq_det _ b, ZLattice.covolume_eq_det _ c]
  have he : Matrix.of (Subtype.val ∘ finProductBasis L N b c) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Matrix.of (Subtype.val ∘ b)) 0 0 (Matrix.of (Subtype.val ∘ c))) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply]
    rw [finProductBasis, Basis.reindex_apply, Basis.ofZLatticeComap_apply]
    simp only [LinearEquiv.symm_symm, Basis.map_apply]
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;>
      simp [Basis.prod_apply, prodSubtypeEquiv, Fin.appendEquiv, appendEquiv, Matrix.reindex_apply]
  rw [he, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, abs_mul]



-- @@ L135-135 verbatim
end SingleLatticeCovering.LatticeGeometry


-- @@ L137-137 verbatim
namespace SingleLatticeCovering.LatticeGeometry

-- @@ L138-138 verbatim
open Module MeasureTheory

-- @@ L139-139 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



-- @@ L142-143 verbatim
abbrev image (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : Submodule ℤ (ι → ℝ) :=
  ZLattice.comap ℝ L e.symm.toLinearMap


-- @@ L145-148 verbatim
instance image_discrete (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] : DiscreteTopology (image L e) := by
  change DiscreteTopology (ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L150-153 verbatim
instance image_full (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] : IsZLattice ℝ (image L e) := by
  change IsZLattice ℝ (ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance


-- @@ L155-160 verbatim
lemma mem_image {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    x ∈ image L e ↔ ∃ l ∈ L, e l=x := by
  change e.symm x ∈ L ↔ _
  constructor
  · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  · rintro ⟨l,hl,rfl⟩; simpa using hl


-- @@ L162-172 verbatim
lemma image_covolume (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (image L e) = |LinearMap.det e.toLinearMap| * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let b' : Basis ι ℤ (image L e) := b.ofZLatticeComap ℝ L e.symm
  rw [ZLattice.covolume_eq_det _ b',ZLattice.covolume_eq_det _ b,
    ←Pi.basisFun_det_apply, ←Pi.basisFun_det_apply]
  have he : Subtype.val ∘ b' = e.toLinearMap ∘ (Subtype.val ∘ b) := by
    ext j k
    simp [b', Basis.ofZLatticeComap_apply]
  rw [he, Basis.det_comp, abs_mul]



-- @@ L175-175 verbatim
end SingleLatticeCovering.LatticeGeometry


-- @@ L177-177 verbatim
namespace SingleLatticeCovering.LatticeGeometry

-- @@ L178-178 verbatim
open Module MeasureTheory




-- @@ L182-223 verbatim
def triangular {m n : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin (m+n) → ℝ) ≃ₗ[ℝ] (Fin (m+n) → ℝ) where
  toFun x := Fin.append (e (fun j => x (Fin.castAdd n j)) + S (fun j => x (Fin.natAdd m j)))
    (f (fun j => x (Fin.natAdd m j)))
  invFun y := Fin.append
    (e.symm ((fun j => y (Fin.castAdd n j))-S (f.symm (fun j => y (Fin.natAdd m j)))))
    (f.symm (fun j => y (Fin.natAdd m j)))
  left_inv := by
    intro x
    simp only [Fin.append_left, Fin.append_right, LinearEquiv.symm_apply_apply,
      add_sub_cancel_right]
    exact (Fin.appendEquiv m n).apply_symm_apply x
  right_inv := by
    intro y
    simp only [Fin.append_left, Fin.append_right, LinearEquiv.apply_symm_apply,
      sub_add_cancel]
    exact (Fin.appendEquiv m n).apply_symm_apply y
  map_add' := by
    intro x y
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simp only [Fin.append_left, Pi.add_apply]
      change e ((fun j => x (Fin.castAdd n j)) + (fun j => y (Fin.castAdd n j))) k +
        S ((fun j => x (Fin.natAdd m j)) + (fun j => y (Fin.natAdd m j))) k = _
      simp only [map_add, Pi.add_apply]
      ring
    · simp only [Fin.append_right, Pi.add_apply]
      change f ((fun j => x (Fin.natAdd m j)) + (fun j => y (Fin.natAdd m j))) k = _
      simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro a x
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simp only [Fin.append_left, Pi.add_apply, Pi.smul_apply, RingHom.id_apply]
      change e (a • (fun j => x (Fin.castAdd n j))) k +
        S (a • (fun j => x (Fin.natAdd m j))) k = _
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]
      change f (a • (fun j => x (Fin.natAdd m j))) k = _
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]


-- @@ L225-230 verbatim
@[simp] lemma triangular_append {m n : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    triangular e f S (Fin.append x y) = Fin.append (e x+S y) (f y) := by
  simp [triangular]


-- @@ L232-237 verbatim
lemma single_left {m n : ℕ} (i : Fin m) :
    (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m+n) → ℝ) =
      Fin.append (Pi.single i 1) 0 := by
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Pi.single_apply]
  all_goals intro h; have hv := congrArg Fin.val h; simp at hv; omega


-- @@ L239-244 verbatim
lemma single_right {m n : ℕ} (i : Fin n) :
    (Pi.single (Fin.natAdd m i) (1 : ℝ) : Fin (m+n) → ℝ) =
      Fin.append 0 (Pi.single i 1) := by
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Pi.single_apply]
  all_goals intro h; have hv := congrArg Fin.val h; simp at hv; omega


-- @@ L246-262 verbatim
lemma triangular_det {m n : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    LinearMap.det (triangular e f S).toLinearMap =
      LinearMap.det e.toLinearMap * LinearMap.det f.toLinearMap := by
  rw [←LinearMap.det_toMatrix', ←LinearMap.det_toMatrix' e.toLinearMap,
    ←LinearMap.det_toMatrix' f.toLinearMap]
  have he : LinearMap.toMatrix' (triangular e f S).toLinearMap =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (LinearMap.toMatrix' e.toLinearMap) (LinearMap.toMatrix' S) 0
          (LinearMap.toMatrix' f.toLinearMap)) := by
    ext i j
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix'_apply, single_left, single_right, Matrix.reindex_apply]
  rw [he, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]




-- @@ L266-275 verbatim
theorem triangular_lattice_covolume {m n : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) (N : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [DiscreteTopology N] [IsZLattice ℝ L] [IsZLattice ℝ N]
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ZLattice.covolume (image (finProduct L N) (triangular e f S)) =
      |LinearMap.det e.toLinearMap| * ZLattice.covolume L *
        (|LinearMap.det f.toLinearMap| * ZLattice.covolume N) := by
  rw [image_covolume,triangular_det,finProduct_covolume,abs_mul]
  ring



-- @@ L278-278 verbatim
end SingleLatticeCovering.LatticeGeometry


-- @@ L280-280 verbatim
namespace SingleLatticeCovering.Vertical

-- @@ L281-281 verbatim
open Folded ConstructionA Blocks LatticeGeometry

-- @@ L282-282 verbatim
open scoped BigOperators


-- @@ L284-284 verbatim
namespace Block

-- @@ L285-286 verbatim
instance lattice_discrete (B : Block) : DiscreteTopology B.lattice :=
  Classical.choose (line_lattice B.p B.direction B.direction_ne)

-- @@ L287-288 verbatim
instance lattice_full (B : Block) : IsZLattice ℝ B.lattice :=
  (Classical.choose_spec (line_lattice B.p B.direction B.direction_ne)).1

-- @@ L289-290 verbatim
lemma lattice_covolume (B : Block) : ZLattice.covolume B.lattice = (B.p : ℝ)⁻¹ :=
  (Classical.choose_spec (line_lattice B.p B.direction B.direction_ne)).2


-- @@ L292-293 verbatim
def linear (B : Block) : B.Vec ≃ₗ[ℝ] B.Vec :=
  LinearEquiv.smulOfNeZero ℝ B.Vec B.h B.h_pos.ne'

-- @@ L294-294 verbatim
@[simp] lemma linear_apply (B : Block) (l : B.Vec) : B.linear l = B.h • l := rfl

-- @@ L295-298 verbatim
lemma linear_det (B : Block) : LinearMap.det B.linear.toLinearMap = B.h^B.b := by
  change LinearMap.det (B.h • (LinearMap.id : B.Vec →ₗ[ℝ] B.Vec)) = _
  rw [LinearMap.det_smul]
  simp

-- @@ L299-302 verbatim
lemma physical_covolume (B : Block) :
    ZLattice.covolume (image B.lattice B.linear) = B.det := by
  rw [image_covolume, linear_det, abs_of_pos (pow_pos B.h_pos _), lattice_covolume]
  simp only [det,div_eq_mul_inv]


-- @@ L304-305 verbatim
def shiftMap (A B : Block) (w : Fin B.b → A.Group) : B.Vec →ₗ[ℝ] A.Vec :=
  Matrix.mulVecLin (fun j k => A.h/(A.p : ℝ)*((w k j).val : ℝ))

-- @@ L306-314 verbatim
@[simp] lemma shiftMap_apply (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) :
    A.shiftMap B w l = A.shift B w l := by
  ext j
  change (∑ k, (A.h/(A.p : ℝ)*((w k j).val : ℝ))*l k) =
    A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

-- @@ L315-315 verbatim
end Block


-- @@ L317-317 verbatim
namespace Chain

-- @@ L318-318 verbatim
variable {A B : Block}


-- @@ L320-322 verbatim
def injectLast : {B : Block} → (c : Chain B) → B.Vec →ₗ[ℝ] c.Vec
  | _, .base _ => LinearMap.id
  | _, .append c B _ => (appendEquiv c.dim B.b).toLinearMap.comp (LinearMap.inr ℝ c.Vec B.Vec)


-- @@ L324-330 verbatim
lemma subLast_eq_sub (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.subLast y t = y-c.injectLast t := by
  cases c with
  | base B => rfl
  | append c B w =>
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [subLast,injectLast,appendEquiv]


-- @@ L332-334 verbatim
abbrev rawLattice : {B : Block} → (c : Chain B) → Submodule ℤ c.Vec
  | _, .base B => B.lattice
  | _, .append c B _ => finProduct c.rawLattice B.lattice

-- @@ L335-338 verbatim
instance raw_discrete (c : Chain B) : DiscreteTopology c.rawLattice := by
  induction c with
  | base B => exact B.lattice_discrete
  | append c B w ih => let := ih; exact finProduct_discrete _ _

-- @@ L339-342 verbatim
instance raw_full (c : Chain B) : IsZLattice ℝ c.rawLattice := by
  induction c with
  | base B => exact B.lattice_full
  | append c B w ih => let := ih; exact finProduct_full _ _

-- @@ L343-346 verbatim
lemma mem_raw (c : Chain B) (l : c.Vec) : l ∈ c.rawLattice ↔ c.RawMem l := by
  induction c with
  | base B => rfl
  | append c B w ih => exact and_congr (ih _) Iff.rfl


-- @@ L348-351 verbatim
def linear : {B : Block} → (c : Chain B) → c.Vec ≃ₗ[ℝ] c.Vec
  | _, .base B => B.linear
  | _, .append (A := A) c B w =>
    triangular c.linear B.linear (c.injectLast.comp (A.shiftMap B w))

-- @@ L352-354 verbatim
def det : {B : Block} → Chain B → ℝ
  | _, .base B => B.det
  | _, .append c B _ => c.det*B.det

-- @@ L355-355 verbatim
abbrev physicalLattice (c : Chain B) : Submodule ℤ c.Vec := image c.rawLattice c.linear


-- @@ L357-364 verbatim
lemma physical_covolume (c : Chain B) : ZLattice.covolume c.physicalLattice = c.det := by
  induction c with
  | base B => exact B.physical_covolume
  | append c B w ih =>
    change ZLattice.covolume (image (finProduct c.rawLattice B.lattice)
      (triangular c.linear B.linear _)) = c.det*B.det
    rw [triangular_lattice_covolume, ←image_covolume, ←image_covolume]
    exact congrArg₂ (fun x y : ℝ => x*y) ih B.physical_covolume


-- @@ L366-377 verbatim
lemma residual_append (c : Chain A) (B : Block) (w : Fin B.b → A.Group)
    (y l : (Chain.append c B w).Vec) :
    y-(Chain.append c B w).linear l =
      Fin.append
        (c.subLast (fun j => y (Fin.castAdd B.b j))
          (A.shift B w (fun j => l (Fin.natAdd c.dim j))) -
          c.linear (fun j => l (Fin.castAdd B.b j)))
        (fun j => y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [linear,triangular,sub_eq_add_neg,add_comm,add_assoc]


-- @@ L379-381 verbatim
lemma gamma_append {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    gamma (Fin.append x y) = gamma x*gamma y := by
  simp only [gamma,Fin.prod_univ_add,Fin.append_left,Fin.append_right]




-- @@ L385-392 verbatim
lemma weight_eq (c : Chain B) (y l : c.Vec) :
    c.weight y l = c.det*gamma (y-c.linear l) := by
  induction c with
  | base B => rfl
  | @append A c B w ih =>
    rw [weight, ih, residual_append, gamma_append]
    simp only [Block.weight,det,Block.det]
    ring




-- @@ L396-396 verbatim
end Chain

-- @@ L397-397 verbatim
end SingleLatticeCovering.Vertical


-- @@ L399-399 verbatim
namespace SingleLatticeCovering.Vertical

-- @@ L400-400 verbatim
open scoped BigOperators



-- @@ L403-419 verbatim
lemma binaryExpansion (k n : ℕ) (hn : n < 2^k) :
    ∃ e : Fin k → Bool, (∑ j, if e j then 2^(j : ℕ) else 0) = n := by
  induction k generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    exact ⟨Fin.elim0,by simp [hn0]⟩
  | succ k ih =>
    by_cases hh : n < 2^k
    · obtain ⟨e,he⟩ := ih n hh
      refine ⟨Fin.snoc e false,?_⟩
      rw [Fin.sum_univ_castSucc]
      simpa using he
    · have hn' : n-2^k < 2^k := by rw [pow_succ] at hn; omega
      obtain ⟨e,he⟩ := ih (n-2^k) hn'
      refine ⟨Fin.snoc e true,?_⟩
      rw [Fin.sum_univ_castSucc]
      simp [he,Nat.sub_add_cancel (by omega : 2^k ≤ n)]


-- @@ L421-423 verbatim
def terminalColumns (b p : ℕ) : Fin (b*Nat.clog 2 p) → Fin b → ZMod p :=
  fun i => Pi.single (finProdFinEquiv.symm i).1
    ((2 : ZMod p)^((finProdFinEquiv.symm i).2 : ℕ))



-- @@ L426-452 verbatim
theorem terminal_exhaustion (b p : ℕ) [NeZero p] :
    Function.Surjective (fun e : Fin (b*Nat.clog 2 p) → Bool =>
      ∑ i, if e i then terminalColumns b p i else 0) := by
  classical
  intro z
  have hb (j : Fin b) : (z j).val < 2^(Nat.clog 2 p) :=
    (ZMod.val_lt (z j)).trans_le (Nat.le_pow_clog (by norm_num) p)
  choose e he using fun j => binaryExpansion (Nat.clog 2 p) (z j).val (hb j)
  refine ⟨fun i => e (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2,?_⟩
  ext j
  change (∑ i, if e (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 then terminalColumns b p i else 0) j = z j
  simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
  rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply,terminalColumns,     Fintype.sum_prod_type]
  have hdiag : (∑ a : Fin b, ∑ k : Fin (Nat.clog 2 p),
      (if e a k then Pi.single a ((2 : ZMod p)^(k : ℕ)) j else 0)) =
      ∑ k : Fin (Nat.clog 2 p), if e j k then (2 : ZMod p)^(k : ℕ) else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ haj
      apply Finset.sum_eq_zero
      intro k _
      simp [Pi.single_eq_of_ne (Ne.symm haj)]
    · simp
  rw [hdiag]
  have he' := congrArg (fun n : ℕ => (n : ZMod p)) (he j)
  simpa using he'



-- @@ L455-455 verbatim
end SingleLatticeCovering.Vertical


-- @@ L457-457 verbatim
namespace SingleLatticeCovering.Vertical

-- @@ L458-458 verbatim
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory

-- @@ L459-459 verbatim
open scoped BigOperators


-- @@ L461-462 verbatim
abbrev integerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

-- @@ L463-470 verbatim
lemma integerLattice_covolume (n : ℕ) : ZLattice.covolume (integerLattice n) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume),
    ZSpan.volume_real_fundamentalDomain]
  have hm : Matrix.of (Pi.basisFun ℝ (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hm,Matrix.det_one,abs_one]

-- @@ L471-474 verbatim
lemma integer_mem (n : ℕ) (k : Fin n → ℤ) : (fun j => (k j : ℝ)) ∈ integerLattice n := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨k j,by simp⟩


-- @@ L476-476 verbatim
namespace Block

-- @@ L477-477 verbatim
abbrev terminalDim (B : Block) : ℕ := B.b*Nat.clog 2 B.p


-- @@ L479-480 verbatim
def shiftDim (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) : B.Vec :=
  fun j => B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k


-- @@ L482-483 verbatim
def shiftDimMap (B : Block) (d : ℕ) (w : Fin d → B.Group) : (Fin d → ℝ) →ₗ[ℝ] B.Vec :=
  Matrix.mulVecLin (fun j k => B.h/(B.p : ℝ)*((w k j).val : ℝ))

-- @@ L484-492 verbatim
@[simp] lemma shiftDimMap_apply (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) :
    B.shiftDimMap d w l = B.shiftDim d w l := by
  ext j
  change (∑ k, (B.h/(B.p : ℝ)*((w k j).val : ℝ))*l k) =
    B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring


-- @@ L494-523 verbatim
lemma shiftDim_grid_bits (B : Block) (d : ℕ) (w : Fin d → B.Group) (y : B.Vec)
    (lam : Fin d → ℝ) (e : Fin d → Bool) :
    B.grid (y-B.shiftDim d w (bits d lam e)) =
      B.grid (y-B.shiftDim d w lam)-Bits.groupShift w e := by
  ext j
  have hp : (B.p : ℝ) ≠ 0 := by exact_mod_cast B.prime.pos.ne'
  have hh : B.h ≠ 0 := B.h_pos.ne'
  have hs : (B.p : ℝ)*((y-B.shiftDim d w (bits d lam e)) j/B.h) =
      (B.p : ℝ)*((y-B.shiftDim d w lam) j/B.h)-
        (((∑ k, if e k then ((w k j).val : ℤ) else 0) : ℤ) : ℝ) := by
    simp only [Pi.sub_apply, shiftDim, bits]
    rw [Int.cast_sum]
    simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero]
    have hs' : (∑ k, ((w k j).val : ℝ)*(lam k+if e k then 1 else 0)) =
        (∑ k, ((w k j).val : ℝ)*lam k) + (∑ k, if e k then ((w k j).val : ℝ) else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      cases he : e k <;> simp [mul_add]
    rw [hs']
    field_simp
    ring
  simp only [Pi.sub_apply] at hs
  simp only [grid,residue,floorVector,Pi.sub_apply]
  rw [hs,Int.floor_sub_intCast,Int.cast_sub,Int.cast_sum]
  congr 1
  simp only [Bits.groupShift,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases he : e k <;> simp


-- @@ L525-526 verbatim
abbrev terminalShift (B : Block) : (Fin B.terminalDim → ℝ) →ₗ[ℝ] B.Vec :=
  B.shiftDimMap B.terminalDim (terminalColumns B.b B.p)




-- @@ L530-553 verbatim
lemma terminal_index (B : Block) (y : B.Vec) (t : Fin B.terminalDim → ℝ) (z : B.Group) :
    ∃ l ∈ integerLattice B.terminalDim,
      (∀ j, |t j-l j| ≤ 1) ∧ B.grid (y-B.terminalShift l)=z := by
  classical
  let lam : Fin B.terminalDim → ℝ := fun j => (⌊t j⌋ : ℤ)
  obtain ⟨e,he⟩ := terminal_exhaustion B.b B.p
    (B.grid (y-B.terminalShift lam)-z)
  refine ⟨bits B.terminalDim lam e,?_,?_,?_⟩
  · convert integer_mem B.terminalDim (fun j => ⌊t j⌋+if e j then 1 else 0) using 1
    ext j
    cases he : e j <;> simp [bits,lam,he]
  · intro j
    have hfl := Int.floor_le (t j)
    have hfu := Int.lt_floor_add_one (t j)
    rw [abs_le]
    cases he : e j <;>
      simp only [bits,lam,he,Bool.false_eq_true,↓reduceIte,add_zero] <;> constructor <;> linarith
  · simp only [terminalShift,shiftDimMap_apply]
    rw [shiftDim_grid_bits]
    have he' : Bits.groupShift (terminalColumns B.b B.p) e =
        B.grid (y-B.shiftDim B.terminalDim (terminalColumns B.b B.p) lam)-z := by
      simpa only [Bits.groupShift,terminalShift,shiftDimMap_apply] using he
    rw [he']
    abel

-- @@ L554-554 verbatim
end Block


-- @@ L556-556 verbatim
namespace Chain

-- @@ L557-557 verbatim
variable {B : Block}

-- @@ L558-558 verbatim
abbrev fullDim (c : Chain B) : ℕ := c.dim+B.terminalDim

-- @@ L559-559 verbatim
abbrev FullVec (c : Chain B) := Fin c.fullDim → ℝ

-- @@ L560-560 verbatim
abbrev fullRaw (c : Chain B) : Submodule ℤ c.FullVec := finProduct c.rawLattice (integerLattice B.terminalDim)

-- @@ L561-562 verbatim
def fullLinear (c : Chain B) : c.FullVec ≃ₗ[ℝ] c.FullVec :=
  triangular c.linear (LinearEquiv.refl ℝ _) (c.injectLast.comp B.terminalShift)

-- @@ L563-563 verbatim
abbrev fullLattice (c : Chain B) : Submodule ℤ c.FullVec := image c.fullRaw c.fullLinear


-- @@ L565-571 verbatim
lemma full_covolume (c : Chain B) : ZLattice.covolume c.fullLattice = c.det := by
  rw [show c.fullLattice = image (finProduct c.rawLattice (integerLattice B.terminalDim))
    (triangular c.linear (LinearEquiv.refl ℝ _) (c.injectLast.comp B.terminalShift)) from rfl,
    triangular_lattice_covolume,←image_covolume]
  have hc := c.physical_covolume
  have ht := integerLattice_covolume B.terminalDim
  simpa using congrArg₂ (fun x y : ℝ => x*y) hc ht


-- @@ L573-580 verbatim
lemma full_residual (c : Chain B) (y : c.FullVec) (v : c.Vec) (t : Fin B.terminalDim → ℝ) :
    y-c.fullLinear (Fin.append v t) = Fin.append
      (c.subLast (fun j => y (Fin.castAdd B.terminalDim j)) (B.terminalShift t)-c.linear v)
      (fun j => y (Fin.natAdd c.dim j)-t j) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [fullLinear,triangular_append,sub_eq_add_neg,add_comm,add_assoc]


-- @@ L582-587 verbatim
lemma full_weight (c : Chain B) (y : c.FullVec) (v : c.Vec) (t : Fin B.terminalDim → ℝ) :
    c.det*gamma (y-c.fullLinear (Fin.append v t)) =
      c.weight (c.subLast (fun j => y (Fin.castAdd B.terminalDim j)) (B.terminalShift t)) v *
        gamma (fun j => y (Fin.natAdd c.dim j)-t j) := by
  rw [full_residual,gamma_append,weight_eq]
  ring




-- @@ L591-591 verbatim
end Chain

-- @@ L592-592 verbatim
end SingleLatticeCovering.Vertical


-- @@ L594-594 verbatim
namespace SingleLatticeCovering.Vertical

-- @@ L595-595 verbatim
open Folded ConstructionA Blocks

-- @@ L596-596 verbatim
open scoped BigOperators


-- @@ L598-598 verbatim
namespace Block


-- @@ L600-603 verbatim
def Selected (B : Block) (y l : B.Vec) : Prop :=
  ∃ z ∈ B.usable, ∃ lam : B.Vec,
    ((fun j => y j/B.h)-lam) ∈ gridCell B.p z ∧
    ∃ e : Fin B.b → Bool, l=bits B.b lam e


-- @@ L605-629 verbatim
lemma cell_selected (B : Block) (y : B.Vec) (hg : 0 < B.g (B.grid y)) :
    ∃ z ∈ B.usable, ∃ lam : B.Vec,
      lam ∈ B.lattice ∧
      B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) ∧
      (∀ e : Fin B.b → Bool, bits B.b lam e ∈ B.lattice ∧
        (∀ j, |y j-B.h*bits B.b lam e j| ≤ B.h) ∧
        (Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
          (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) ≤ B.weight y (bits B.b lam e)) ∧
        B.Selected y (bits B.b lam e)) := by
  obtain ⟨z,hz,lam,hlam,ht,hg',he⟩ := gaussian_cell B.h_pos B.usable B.direction
    (fun j => y j/B.h) hg
  change B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) at hg'
  refine ⟨z,hz,lam,hlam,hg',?_⟩
  intro e
  obtain ⟨hm,hr,hw⟩ := he e
  refine ⟨hm,?_,?_,⟨z,hz,lam,ht,e,rfl⟩⟩
  · intro j
    convert hr j using 1
    congr 1
    dsimp only [bits]
    simp only [bitValue]
    field_simp [B.h_pos.ne']
    ring
  · rw [weight_bits, hg']
    simpa only [Fintype.card_fin] using hw


-- @@ L631-636 verbatim
lemma selected_weight_le (B : Block) (y l : B.Vec) (hl : B.Selected y l)
    (q : ℝ) (hq : ∀ z ∈ B.usable, ∀ t : B.Vec, t ∈ gridCell B.p z →
      ∀ e : Fin B.b → Bool, atom B.h t e/(B.p : ℝ) ≤ q) : B.weight y l ≤ q := by
  obtain ⟨z,hz,lam,ht,e,rfl⟩ := hl
  rw [weight_bits]
  exact hq z hz _ ht e

-- @@ L637-637 verbatim
end Block


-- @@ L639-639 verbatim
namespace Chain

-- @@ L640-640 verbatim
variable {A B : Block}


-- @@ L642-648 verbatim
def Selected : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => B.Selected y l
  | _, .append (A := A) c B w, y, l =>
      c.Selected (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      B.Selected (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))


-- @@ L650-678 verbatim
lemma base_pattern_selected (B : Block) (y : B.Vec) :
    ∃ P : Finset B.Vec, SuffixBinary P ∧
      (∀ l ∈ P, l ∈ B.lattice ∧ (∀ j, |y j-B.h*l j| ≤ B.h) ∧ B.Selected y l) ∧
      Real.exp (-((B.b : ℝ)*B.h^2/B.p))*B.g (B.grid y) ≤ ∑ l ∈ P, B.weight y l := by
  classical
  by_cases hg : 0 < B.g (B.grid y)
  · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell_selected y hg
    let P : Finset B.Vec := Finset.univ.image (bits B.b lam)
    refine ⟨P,?_,?_,?_⟩
    · intro j t
      refine ⟨lam j,?_⟩
      intro l hl hlt
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact bits_scalar B.b lam e j
    · intro l hl
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(he e).1,(he e).2.1,(he e).2.2.2⟩
    · change _ ≤ ∑ l ∈ Finset.univ.image (bits B.b lam), _
      rw [Finset.sum_image (fun e he e' he' h => bits_injective B.b lam h)]
      calc
        _ = ∑ e, Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
            (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) := by
          rw [←Finset.mul_sum, ←Finset.mul_sum, wordMass_sum B.h_pos, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun e _ => (he e).2.2.1)
  · have heq : B.g (B.grid y)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
    refine ⟨∅,?_,by simp,?_⟩
    · intro j t
      exact ⟨0,by simp⟩
    · simp [heq]





-- @@ L683-734 verbatim
theorem truncated_patterns_selected (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss)
    (y : c.Vec) :
    ∃ P : Finset c.Vec, SuffixBinary P ∧
      (∀ l ∈ P, c.RawMem l ∧ c.Residual y l ∧ c.Selected y l) ∧
      c.coefficient loss*B.g (B.grid (c.last y)) ≤ ∑ l ∈ P, c.weight y l := by
  classical
  induction c with
  | base B => exact base_pattern_selected B y
  | @append A c B w ih =>
    let yl : c.Vec := fun j => y (Fin.castAdd B.b j)
    let yr : B.Vec := fun j => y (Fin.natAdd c.dim j)
    by_cases hg : 0 < B.g (B.grid yr)
    · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell_selected yr hg
      have hcp := fun e : Fin B.b → Bool => ih hc.1 (c.subLast yl (A.shift B w (bits B.b lam e)))
      choose P hPb hPm hPw using hcp
      refine ⟨concat P lam,suffixBinary_concat P lam hPb,?_,?_⟩
      · intro l hl
        obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam l).mp hl
        have hv' := hPm e v hv
        exact ⟨by simpa [RawMem] using And.intro hv'.1 (he e).1,
          by simpa [Residual] using And.intro hv'.2.1 (he e).2.1,
          by simpa [Selected] using And.intro hv'.2.2 (he e).2.2.2⟩
      · let x := A.grid (c.last yl-A.shift B w lam)
        have hgrid (e : Fin B.b → Bool) :
            A.grid (c.last (c.subLast yl (A.shift B w (bits B.b lam e)))) =
              x-Bits.groupShift w e := by
          rw [last_subLast, Block.shift_grid_bits]
        have hs : (1-loss B)*(1-loss A) ≤
            ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e) :=
          (mul_le_mul_of_nonneg_left hc.2.2.2.1 hc.2.1).trans (hc.2.2.2.2 z hz x)
        have hw := weighted_join P (bits B.b lam) (bits_injective B.b lam)
          (fun e l => c.weight (c.subLast yl (A.shift B w (bits B.b lam e))) l)
          (fun e => B.weight yr (bits B.b lam e))
          (fun l => (Chain.append c B w).weight y (Fin.append l.1 l.2))
          (wordMass B.h (anchor B.p z)) (fun e => A.g (x-Bits.groupShift w e))
          (c.coefficient loss) (B.g (B.grid yr)) (Real.exp (-((B.b : ℝ)*B.h^2/B.p)))
          ((1-loss B)*(1-loss A)) (coefficient_nonneg c loss hc.1) (B.g_nonneg _)
          (Real.exp_pos _).le
          (fun e => Finset.prod_nonneg (fun j _ => (probability_pos B.h_pos _ _).le))
          (fun e => A.g_nonneg _)
          (fun e => by convert (he e).2.2.1 using 1 ; ring)
          (fun e => by rw [←hgrid e]; exact hPw e)
          (fun e l hl => by simp [weight,yl,yr]) hs
        change _ ≤ ∑ l ∈ (join P (bits B.b lam)).image (fun x => Fin.append x.1 x.2), _
        rw [Finset.sum_image (fun x hx y hy h => append_injective h)]
        convert hw using 1 ; dsimp [coefficient, last,yr] ; ring
    · have heq : B.g (B.grid yr)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
      refine ⟨∅,?_,by simp,?_⟩
      · intro j t
        exact ⟨0,by simp⟩
      · change _*B.g (B.grid yr) ≤ _
        simp [heq]



-- @@ L737-737 verbatim
end Chain

-- @@ L738-738 verbatim
end SingleLatticeCovering.Vertical



-- @@ L741-741 verbatim
end

-- @@ L742-742 verbatim
end

-- @@ L743-743 verbatim
end

-- @@ L744-744 verbatim
end

-- @@ L745-745 verbatim
end

-- @@ L746-746 verbatim
end

-- @@ L747-747 verbatim
end

-- @@ L748-748 verbatim
end

-- @@ L749-749 verbatim
end

-- @@ L750-750 verbatim
end

-- @@ L751-751 verbatim
end

-- @@ L752-752 verbatim
end

-- @@ L753-753 verbatim
end

-- @@ L754-754 verbatim
end


-- @@ L756-756 verbatim
end OAI
