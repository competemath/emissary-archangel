import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.QuotientGrading

-- @@ L8-8 verbatim
open DirectSum

-- @@ L9-12 verbatim
variable {k R Q ι : Type*} [CommRing k] [CommRing R] [CommRing Q]
  [Algebra k R] [Algebra k Q] [AddCommMonoid ι] [DecidableEq ι]
  (G : ι → Submodule k R) [GradedAlgebra G]
  (q : R →ₐ[k] Q)


-- @@ L14-14 verbatim
def pieces (i : ι) : Submodule k Q := (G i).map q.toLinearMap


-- @@ L16-17 verbatim
def componentMap (i : ι) : G i →ₗ[k] pieces G q i :=
  (q.toLinearMap.comp (G i).subtype).codRestrict _ (fun r => ⟨r, r.2, rfl⟩)


-- @@ L19-20 verbatim
def sourceDecompose : R →ₗ[k] ⨁ i, pieces G q i :=
  (DirectSum.lmap (componentMap G q)).comp (decomposeLinearEquiv G).toLinearMap


-- @@ L22-23 verbatim
lemma sourceDecompose_apply (r : R) (i : ι) :
    ((sourceDecompose G q r i : pieces G q i) : Q) = q (decompose G r i) := rfl


-- @@ L25-29 verbatim
lemma sourceDecompose_zero (hK : (RingHom.ker q).IsHomogeneous G) {r : R}
    (hr : q r = 0) : sourceDecompose G q r = 0 := by
  ext i
  change q (decompose G r i) = 0
  exact (hK.mem_iff.mp hr) i


-- @@ L31-39 verbatim
lemma sourceDecompose_eq (hK : (RingHom.ker q).IsHomogeneous G)
    {a b : R} (hab : q a = q b) : sourceDecompose G q a = sourceDecompose G q b := by
  ext i
  have hz : q (a-b) = 0 := by rw [map_sub, hab, sub_self]
  have hh := (hK.mem_iff.mp hz) i
  change q (decompose G (a-b) i) = 0 at hh
  rw [decompose_sub] at hh
  change q (decompose G a i) = q (decompose G b i)
  simpa only [DirectSum.sub_apply, Submodule.coe_sub, map_sub, sub_eq_zero] using hh


-- @@ L41-53 verbatim
def decomposeMap (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : Q →ₗ[k] ⨁ i, pieces G q i where
  toFun r := sourceDecompose G q (Classical.choose (hq r))
  map_add' r s := by
    rw [← map_add]
    apply sourceDecompose_eq G q hK
    simp only [map_add, Classical.choose_spec (hq _)]
  map_smul' a r := by
    change sourceDecompose G q (Classical.choose (hq (a • r))) =
      a • sourceDecompose G q (Classical.choose (hq r))
    rw [← map_smul]
    apply sourceDecompose_eq G q hK
    simp only [map_smul, Classical.choose_spec (hq _)]


-- @@ L55-58 verbatim
@[simp] lemma decomposeMap_q (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) (r : R) :
    decomposeMap G q hq hK (q r) = sourceDecompose G q r :=
  sourceDecompose_eq G q hK (Classical.choose_spec (hq (q r)))


-- @@ L60-72 verbatim
lemma coe_sourceDecompose (r : R) :
    coeLinearMap (pieces G q) (sourceDecompose G q r) = q r := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp
  | @homogeneous i r =>
    change coeLinearMap (pieces G q) (DirectSum.lmap (componentMap G q)
      (decompose G (r : R))) = _
    rw [decompose_coe, DirectSum.lmap_of]
    change coeLinearMap (pieces G q)
      (DirectSum.lof k ι (fun i => pieces G q i) i (componentMap G q i r)) = _
    rw [coeLinearMap_lof]
    rfl
  | add r s hr hs => simp [hr, hs]


-- @@ L74-83 verbatim
lemma decomposeMap_homogeneous (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) (i : ι) (r : pieces G q i) :
    decomposeMap G q hq hK r = DirectSum.lof k ι (fun i => pieces G q i) i r := by
  obtain ⟨s, hs, hsr⟩ := r.2
  have he : (r : Q) = q s := hsr.symm
  rw [he, decomposeMap_q]
  change DirectSum.lmap (componentMap G q) (decompose G s) = _
  rw [decompose_of_mem G hs, DirectSum.lmap_of]
  apply congrArg (DirectSum.of (fun i => pieces G q i) i)
  exact Subtype.ext hsr


-- @@ L85-101 verbatim
@[instance_reducible] def decomposition (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : Decomposition (pieces G q) :=
  Decomposition.ofLinearMap (pieces G q) (decomposeMap G q hq hK)
    (by
      ext r
      obtain ⟨s, rfl⟩ := hq r
      exact (congrArg (coeLinearMap (pieces G q)) (decomposeMap_q G q hq hK s)).trans
        (coe_sourceDecompose G q s))
    (by
      apply DirectSum.linearMap_ext k
      intro i
      apply LinearMap.ext
      intro r
      change decomposeMap G q hq hK
        (coeLinearMap (pieces G q) (DirectSum.lof k ι (fun i => pieces G q i) i r)) = _
      rw [coeLinearMap_lof]
      exact decomposeMap_homogeneous G q hq hK i r)


-- @@ L103-111 verbatim
@[instance_reducible] def grading (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) : GradedAlgebra (pieces G q) where
  toDecomposition := decomposition G q hq hK
  one_mem := ⟨1, SetLike.one_mem_graded G, map_one q⟩
  mul_mem := by
    intro i j r s hr hs
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨b, hb, rfl⟩ := hs
    exact ⟨a*b, SetLike.mul_mem_graded ha hb, map_mul q a b⟩


-- @@ L113-120 verbatim
lemma projection_q (hq : Function.Surjective q)
    (hK : (RingHom.ker q).IsHomogeneous G) (r : R) (i : ι) :
    letI : GradedAlgebra (pieces G q) := grading G q hq hK
    GradedAlgebra.proj (pieces G q) i (q r) = q (GradedAlgebra.proj G i r) := by
  let : GradedAlgebra (pieces G q) := grading G q hq hK
  change ((decomposeMap G q hq hK (q r) i : pieces G q i) : Q) = _
  rw [decomposeMap_q]
  rfl


-- @@ L122-122 verbatim
end ComplexCancellation.QuotientGrading


-- @@ L124-124 verbatim
end


-- @@ L126-126 verbatim
end OAI
