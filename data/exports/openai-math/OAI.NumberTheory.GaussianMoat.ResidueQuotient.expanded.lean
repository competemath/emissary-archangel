import OAI.NumberTheory.GaussianMoat.FiniteEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace GaussianMoat


-- @@ L7-8 verbatim
noncomputable def multiples (π : GaussianInt) : Submodule ℤ GaussianInt :=
  (twoVectorMap π (π * ⟨0,1⟩)).range


-- @@ L10-13 verbatim
lemma twoVectorMap_mul_i (π z : GaussianInt) :
    twoVectorMap π (π * ⟨0,1⟩) z = π*z := by
  rw [twoVectorMap_apply]
  ext <;> simp [zsmul_eq_mul,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring


-- @@ L15-17 verbatim
lemma mem_multiples (π z : GaussianInt) : z ∈ multiples π ↔ π ∣ z := by
  simp only [multiples, LinearMap.mem_range, twoVectorMap_mul_i]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,ha.symm⟩,fun ⟨a,ha⟩ => ⟨a,ha.symm⟩⟩


-- @@ L19-25 verbatim
lemma multiples_index {π : GaussianInt} (hπ : π ≠ 0) :
    Nat.card (GaussianInt ⧸ multiples π) = π.norm.natAbs := by
  have he : π.re*(π*⟨0,1⟩).im-π.im*(π*⟨0,1⟩).re = π.norm := by
    simp [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.norm]
  have hn : π.norm ≠ 0 := (GaussianInt.norm_pos.mpr hπ).ne'
  have h := twoVectorMap_quotient_card (a := π) (b := π*⟨0,1⟩) (he.trans_ne hn)
  simpa only [multiples,he] using h


-- @@ L27-28 verbatim
noncomputable def gaussianResidue (π z : GaussianInt) : GaussianInt ⧸ multiples π :=
  Submodule.Quotient.mk z


-- @@ L30-32 verbatim
lemma gaussianResidue_eq (π z w : GaussianInt) :
    gaussianResidue π z = gaussianResidue π w ↔ π ∣ z-w := by
  rw [gaussianResidue,gaussianResidue,Submodule.Quotient.eq,mem_multiples]


-- @@ L34-34 verbatim
instance : Countable GaussianInt := latticeCoords.injective.countable


-- @@ L36-37 verbatim
instance (π : GaussianInt) : Countable (GaussianInt ⧸ multiples π) :=
  (Submodule.Quotient.mk_surjective (p := multiples π)).countable


-- @@ L39-41 verbatim
noncomputable def residueCode (π z : GaussianInt) : ℕ := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  exact Encodable.encode (gaussianResidue π z)


-- @@ L43-47 verbatim
lemma residueCode_eq (π z w : GaussianInt) :
    residueCode π z = residueCode π w ↔ π ∣ z-w := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  change Encodable.encode (gaussianResidue π z) = Encodable.encode (gaussianResidue π w) ↔ _
  rw [Encodable.encode_inj,gaussianResidue_eq]


-- @@ L49-53 verbatim
lemma residueCode_sub {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x-y) = residueCode π (x'-y') := by
  rw [residueCode_eq] at *
  convert dvd_sub hx hy using 1; ring


-- @@ L55-59 verbatim
lemma residueCode_add {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x+y) = residueCode π (x'+y') := by
  rw [residueCode_eq] at *
  convert dvd_add hx hy using 1; ring


-- @@ L61-65 verbatim
lemma finite_gaussianResidue {π : GaussianInt} (hπ : π ≠ 0) :
    Finite (GaussianInt ⧸ multiples π) := by
  apply Nat.finite_of_card_ne_zero
  rw [multiples_index hπ]
  simpa only [Int.natAbs_ne_zero] using (GaussianInt.norm_pos.mpr hπ).ne'


-- @@ L67-78 verbatim
lemma residueCode_range_card {π : GaussianInt} (hπ : π ≠ 0) :
    (Set.range (residueCode π)).Finite ∧ (Set.range (residueCode π)).ncard = π.norm.natAbs := by
  let := finite_gaussianResidue hπ
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  have hs : Function.Surjective (gaussianResidue π) := Submodule.Quotient.mk_surjective _
  have hr : Set.range (residueCode π) = Set.range
      (Encodable.encode : (GaussianInt ⧸ multiples π) → ℕ) := by
    change Set.range (Encodable.encode ∘ gaussianResidue π) = _
    rw [Set.range_comp,hs.range_eq,Set.image_univ]
  rw [hr]
  refine ⟨Set.finite_range _,?_⟩
  rw [Set.ncard_range_of_injective Encodable.encode_injective,multiples_index hπ]


-- @@ L80-80 verbatim
end GaussianMoat


-- @@ L82-82 verbatim
end OAI
