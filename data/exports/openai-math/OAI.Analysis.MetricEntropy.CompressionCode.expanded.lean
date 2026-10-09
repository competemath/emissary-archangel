import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
universe uE


-- @@ L8-15 verbatim
/-!
# Finite codes for uniform compression

A code records one common index, one label code for each level and pivot slot,
and one weight code for each level, pivot slot, and subset of the index set.
The decoded family is the actual image of this finite type under a fixed
decoder. Its cardinality does not depend on the decoder's target type.
-/


-- @@ L17-17 verbatim
namespace MetricEntropyDuality


-- @@ L19-22 verbatim
/-- The actual finite data retained by the compression construction. -/
abbrev CompressionCode (u q h s N : ℕ) :=
  Fin u × (Fin h → Fin s → Fin q) ×
    (Fin h → Fin s → Finset (Fin u) → Fin N)


-- @@ L24-31 verbatim
/-- Count the common index, label slots, and subset-weight slots exactly. -/
theorem card_compressionCode (u q h s N : ℕ) :
    Fintype.card (CompressionCode u q h s N) =
      u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := by
  classical
  simp only [CompressionCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_finset, Fintype.card_fin]
  simp only [← pow_mul, Nat.mul_assoc, Nat.mul_comm]


-- @@ L33-33 verbatim
section Decode


-- @@ L35-35 verbatim
variable {u q h s N : ℕ} {E : Type uE}


-- @@ L37-40 verbatim
/-- Enumerate the actual image of the finite code space under a fixed decoder. -/
noncomputable def compressionImage (decode : CompressionCode u q h s N → E) : Finset E := by
  classical
  exact Finset.univ.image decode


-- @@ L42-45 verbatim
theorem mem_compressionImage (decode : CompressionCode u q h s N → E) (a : E) :
    a ∈ compressionImage decode ↔ ∃ c, decode c = a := by
  classical
  simp [compressionImage]


-- @@ L47-49 verbatim
theorem decode_mem_compressionImage (decode : CompressionCode u q h s N → E)
    (c : CompressionCode u q h s N) : decode c ∈ compressionImage decode :=
  (mem_compressionImage decode (decode c)).2 ⟨c, rfl⟩


-- @@ L51-57 verbatim
/-- Collisions under decoding can only reduce the number of approximants. -/
theorem card_compressionImage_le_code (decode : CompressionCode u q h s N → E) :
    (compressionImage decode).card ≤ Fintype.card (CompressionCode u q h s N) := by
  classical
  simpa only [compressionImage, Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset (CompressionCode u q h s N)))
      (f := decode))


-- @@ L59-64 verbatim
theorem card_compressionImage_le (decode : CompressionCode u q h s N → E) :
    (compressionImage decode).card ≤ u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := by
  calc
    (compressionImage decode).card ≤ Fintype.card (CompressionCode u q h s N) :=
      card_compressionImage_le_code decode
    _ = u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := card_compressionCode u q h s N


-- @@ L66-71 verbatim
/-- Constant zero labels and weight codes work even if there are no levels or slots. -/
theorem compressionCode_nonempty (hu : 0 < u) (hq : 0 < q) (hN : 0 < N) :
    Nonempty (CompressionCode u q h s N) := by
  refine ⟨⟨⟨0, hu⟩, ?_, ?_⟩⟩
  · exact fun _ _ => ⟨0, hq⟩
  · exact fun _ _ _ => ⟨0, hN⟩


-- @@ L73-77 verbatim
/-- Decode an actual code to witness that the approximant family is nonempty. -/
theorem compressionImage_nonempty (decode : CompressionCode u q h s N → E)
    (hu : 0 < u) (hq : 0 < q) (hN : 0 < N) : (compressionImage decode).Nonempty := by
  obtain ⟨c⟩ := compressionCode_nonempty (h := h) (s := s) hu hq hN
  exact ⟨decode c, decode_mem_compressionImage decode c⟩


-- @@ L79-79 verbatim
end Decode


-- @@ L81-81 verbatim
end MetricEntropyDuality


-- @@ L83-83 verbatim
end OAI
