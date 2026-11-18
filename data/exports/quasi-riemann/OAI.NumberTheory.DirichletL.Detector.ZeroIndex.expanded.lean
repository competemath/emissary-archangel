import OAI.NumberTheory.DirichletL.Detector.PrincipalEulerIdentity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeEuler

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-11 verbatim
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]


-- @@ L13-14 verbatim
def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m


-- @@ L16-20 verbatim
omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV


-- @@ L22-36 verbatim
include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [ite_eq_right hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]


-- @@ L38-39 verbatim
def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m


-- @@ L41-55 verbatim
include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq


-- @@ L57-57 verbatim
end SevenEighths.ProbeEuler

-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
