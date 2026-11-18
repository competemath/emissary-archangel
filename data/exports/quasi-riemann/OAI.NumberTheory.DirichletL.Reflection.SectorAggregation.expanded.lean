import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
import OAI.NumberTheory.DirichletL.Reflection.FixedLevel


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L12-13 verbatim
def fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) : Finset (Ideal Eis) :=
  rows.filter (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r)


-- @@ L15-17 verbatim
lemma mem_fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) (K : Ideal Eis) :
    K∈fullRaySector N rows r ↔ K∈rows ∧ Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r :=
  Finset.mem_filter


-- @@ L19-22 verbatim
lemma sum_fullRaySectors {M : Type*} [AddCommMonoid M] (N : Eis)
    [Fintype (Eis⧸Ideal.span {N^2})] (rows : Finset (Ideal Eis)) (f : Ideal Eis→M) :
    (∑ r : Eis⧸Ideal.span {N^2}, ∑ K∈fullRaySector N rows r,f K)=∑ K∈rows,f K :=
  Finset.sum_fiberwise rows (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)) f


-- @@ L24-45 verbatim
theorem full_ray_sector_energy (N : Eis) [Fintype (Eis⧸Ideal.span {N^2})]
    (rows Pset : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) (E : ℝ)
    (hE : ∀ r p : Eis⧸Ideal.span {N^2},
      (∑ K∈fullRaySector N rows r, ‖∑ P∈fullRaySector N Pset p,f K P‖^2)≤E) :
    (∑ K∈rows,‖∑ P∈Pset,f K P‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*E := by
  rw [←sum_fullRaySectors N rows (fun K => ‖∑ P∈Pset,f K P‖^2)]
  calc
    _ ≤ ∑ r : Eis⧸Ideal.span {N^2}, (Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^2*E := by
      apply Finset.sum_le_sum
      intro r hr
      have hh := weighted_finite_row_energy_uniform (Finset.univ : Finset (Eis⧸Ideal.span {N^2}))
        (fullRaySector N rows r) (fun _ => (1:ℂ))
        (fun p K => ∑ P∈fullRaySector N Pset p,f K P) E (fun p _ => hE r p)
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      have he : (∑ K∈fullRaySector N rows r, ‖∑ P∈Pset,f K P‖^2)=
          ∑ K∈fullRaySector N rows r, ‖∑ p : Eis⧸Ideal.span {N^2},∑ P∈fullRaySector N Pset p,f K P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [sum_fullRaySectors]
      rw [he]
      exact hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

-- @@ L46-46 verbatim
end

-- @@ L47-47 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L49-49 verbatim
end OAI
