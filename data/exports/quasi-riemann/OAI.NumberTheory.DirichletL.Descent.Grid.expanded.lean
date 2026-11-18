import OAI.NumberTheory.DirichletL.Descent.Dyadic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
open CanonicalQuadraticSieve CompletedGauss

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-11 verbatim
section FiniteGrid

-- @@ L12-12 verbatim
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]


-- @@ L14-15 verbatim
def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd


-- @@ L17-43 verbatim
theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]


-- @@ L45-45 verbatim
end FiniteGrid


-- @@ L47-48 verbatim
def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)


-- @@ L50-63 verbatim
theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl


-- @@ L65-66 verbatim
def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex


-- @@ L68-81 verbatim
theorem hybrid_grid_reindex (D : Finset HybridColumnData) (t : Ideal Eis)
    (hD : ∀ d ∈ D, d.square = t) (f : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ p ∈ (hybridGridSupport D).image Prod.fst,
        ∑ c ∈ gridCommonSupport (hybridGridSupport D) p.1,
          if (p, c) ∈ hybridGridSupport D then f c p.1 p.2 else 0 := by
  have he : (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ u ∈ hybridGridSupport D, f u.2 u.1.1 u.1.2 := by
    symm
    apply Finset.sum_image
    intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg
  rw [he]
  exact finite_triple_support_reindex (hybridGridSupport D) _


-- @@ L83-89 verbatim
theorem gridCommonSupport_origin (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (hybridGridSupport D) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = c := by
  obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
  obtain ⟨huT, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨d, hd, hum, huc⟩


-- @@ L91-91 verbatim
end

-- @@ L92-92 verbatim
end SevenEighths.InverseMoment


-- @@ L94-94 verbatim
end OAI
