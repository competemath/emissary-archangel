/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoG2Relations
import LieLean.Algebra.QuantumGroup.PBW.RankTwoB2BraidSpan
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeRelation


-- @@ L10-39 verbatim
/-!
# Ordered spans of the actual six-letter G₂ PBW words

Let `i, j` be nodes of an arbitrary Cartan datum with `aᵢⱼ = -3`, `aⱼᵢ = -1` (`i` short),
`q = vᵢ`. Along the two reduced words `i j i j i j` and `j i j i j i` of the longest element of the
rank-two parabolic subgroup, the root vectors are, up to nonzero scalars,
`Eᵢ, x₃, x₂, z, x₁, Eⱼ` and `Eⱼ, y₁, y₃, y₂, w, Eᵢ` (`G2PBW.x1`, …, `G2PBW.w`;
`QuantumGroup.altVec_g2`, `QuantumGroup.altVec_g2_rev`). The relations `G2PBW.baseRel_fwd`,
`G2PBW.baseRel_rev` between the first letter and the later root vectors, transported along the
words by the braid automorphisms (`OrderedSpan.isLS_altVec`), give commutation relations of
Levendorskii–Soibelman type between all pairs of root vectors, hence ordered spanning
(`OrderedSpan.span_mono_eq_adjoin`).

## Main results

* `QuantumGroup.span_pbwMonomial_g2`, `QuantumGroup.span_pbwMonomial_g2_rev`: both actual
  six-letter words span the two-generator subalgebra, in arbitrary ambient Cartan data.
* `QuantumGroup.span_pbwMonomial_g2_braid`: the two words have equal ordered spans.
* `QuantumGroup.span_pbwMonomial_g2_context`,
  `QuantumGroup.span_pbwMonomial_g2_context_of_not_root`: equality in arbitrary prefix/suffix
  word context, given the six-term braid relation (supplied by the constructed automorphisms at
  a non-root-of-unity parameter).

The local results assume `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `[3]ᵢ! ≠ 0`.

## References

Our own reconstruction of the rank-two case of [Jan] J. C. Jantzen, *Lectures on quantum
groups*, GSM 6, Prop. 8.22 b) (the input of the reduced-word independence of PBW spans).
-/


-- @@ L41-41 verbatim
open LieLean


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
namespace LieLean.QuantumGroup


-- @@ L47-47 verbatim
namespace OrderedSpan


-- @@ L49-49 verbatim
variable {k B I : Type*} [Field k] [Ring B] [Algebra k B] (T : I → B ≃ₐ[k] B) (E : I → B)


-- @@ L51-55 verbatim
/-- The root vectors `E_a, T_a(E_b), T_aT_b(E_a), …` along the alternating word `a b a b ⋯` of
length `m`. -/
def altVec : I → I → (m : ℕ) → Fin m → B
  | _, _, 0 => Fin.elim0
  | a, b, m + 1 => Fin.cons (E a) fun i ↦ T a (altVec b a m i)


-- @@ L57-67 verbatim
lemma altVec_castSucc : ∀ (a b : I) (m : ℕ),
    (fun i : Fin m ↦ altVec T E a b (m + 1) i.castSucc) = altVec T E a b m
  | _, _, 0 => funext fun i ↦ i.elim0
  | a, b, m + 1 => by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change altVec T E a b (m + 2) i.succ.castSucc = altVec T E a b (m + 1) i.succ
      rw [← Fin.succ_castSucc]
      exact congrArg (T a) (congrFun (altVec_castSucc b a m) i)


-- @@ L69-76 verbatim
lemma baseRel_altVec_le {a b : I} : ∀ d m : ℕ,
    BaseRel k (altVec T E a b (m + d + 1)) → BaseRel k (altVec T E a b (m + 1))
  | 0, _, h => h
  | d + 1, m, h => by
    have h' : BaseRel k (fun i : Fin (m + d + 1) ↦ altVec T E a b (m + d + 1 + 1) i.castSucc) :=
      h.castSucc
    rw [altVec_castSucc] at h'
    exact baseRel_altVec_le d m h'


-- @@ L78-94 verbatim
/-- If the relations between the first letter and the later root vectors hold along both
alternating words of length `N + 1`, then all commutation relations of Levendorskii–Soibelman
type hold along both words (and their initial segments). -/
theorem isLS_altVec {N : ℕ} {a b : I} (hab : BaseRel k (altVec T E a b (N + 1)))
    (hba : BaseRel k (altVec T E b a (N + 1))) :
    ∀ m, m ≤ N + 1 → IsLS k (altVec T E a b m) ∧ IsLS k (altVec T E b a m)
  | 0, _ => ⟨fun x ↦ x.elim0, fun x ↦ x.elim0⟩
  | m + 1, hm => by
    obtain ⟨h1, h2⟩ := isLS_altVec hab hba m (by omega)
    have hN : m + (N - m) = N := by omega
    refine ⟨isLS_cons (T a).toAlgHom h2 ?_, isLS_cons (T b).toAlgHom h1 ?_⟩
    · refine baseRel_altVec_le T E (N - m) m ?_
      rw [hN]
      exact hab
    · refine baseRel_altVec_le T E (N - m) m ?_
      rw [hN]
      exact hba


-- @@ L96-97 verbatim
lemma mono_altVec_zero (a b : I) (c : Fin 0 → ℕ) : mono (altVec T E a b 0) c = 1 := by
  simp [mono]


-- @@ L99-104 verbatim
lemma mono_altVec_succ (a b : I) (m : ℕ) (c : Fin (m + 1) → ℕ) :
    mono (altVec T E a b (m + 1)) c =
      E a ^ c 0 * T a (mono (altVec T E b a m) fun i ↦ c i.succ) := by
  simp only [mono, List.ofFn_succ, List.prod_cons, map_list_prod, List.map_ofFn,
    Function.comp_def, map_pow]
  rfl


-- @@ L106-112 verbatim
/-- The actual recursive PBW monomial of `a b a b a b` is the ordered monomial in the root
vectors `altVec`. -/
theorem pbwMonomial_eq_mono_altVec_six (a b : I) (c : Fin 6 → ℕ) :
    CoxeterSystem.pbwMonomial T E [a, b, a, b, a, b] c = mono (altVec T E a b 6) c := by
  simp only [mono_altVec_succ, mono_altVec_zero, CoxeterSystem.pbwMonomial_cons,
    CoxeterSystem.pbwMonomial_nil]
  rfl


-- @@ L114-114 verbatim
end OrderedSpan


-- @@ L116-116 verbatim
open OrderedSpan BraidDiagonal LusztigF


-- @@ L118-119 verbatim
/-- The scalar of `TᵢTⱼ(Eᵢ) = c₃ x₂` in type `G₂`. -/
abbrev g2c3 {k : Type*} [Field k] (q : k) : k := (qFactorial q 3)⁻¹ * cc q (q ^ 3) 3


-- @@ L121-123 verbatim
/-- The scalar of `TᵢTⱼ(x₂) = c₂ x₁` in type `G₂`. -/
abbrev g2c2 {k : Type*} [Field k] (q : k) : k :=
  (qFactorial q 3)⁻¹ * cc q (q ^ 3) 3 * cc q (q ^ 3) 2


-- @@ L125-131 verbatim
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
  {i j : I} (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
  (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)


-- @@ L133-133 verbatim
section Values


-- @@ L135-135 verbatim
local notation "q" => v ^ D.d i

-- @@ L136-136 verbatim
local notation "Xg" n:max => X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) n


-- @@ L138-141 verbatim
omit [NeZero v] in
lemma g2_X_one : Xg 1 = G2PBW.x1 q (E R v i) (E R v j) := by
  rw [X_succ, tripleSix_shift_zero]
  rfl


-- @@ L143-146 verbatim
omit [NeZero v] in
lemma g2_X_two (hq0 : v ^ D.d i ≠ 0) : Xg 2 = G2PBW.x2 q (E R v i) (E R v j) := by
  rw [X_succ, tripleSix_shift_one hq0, g2_X_one]
  rfl


-- @@ L148-151 verbatim
omit [NeZero v] in
lemma g2_X_three (hq0 : v ^ D.d i ≠ 0) : Xg 3 = G2PBW.x3 q (E R v i) (E R v j) := by
  rw [X_succ, tripleSix_shift_two hq0, g2_X_two R v hq0]
  rfl


-- @@ L153-159 verbatim
include Hj hij h h' in
omit [NeZero v] in
lemma g2_Tj_Ei : (T j) (E R v i) = G2PBW.y1 q (E R v i) (E R v j) := by
  have e := tripleSix_T_Ei Hj hij
  change (T j) (E R v i) = _ at e
  rw [e, braidEj_eq_of_cartanMatrix_eq_neg_one h', parameter_eq_cube_of_triple_edge h h']
  rfl


-- @@ L161-165 verbatim
include Hi hij h in
lemma g2_Ti_Ej : (T i) (E R v j) = (qFactorial q 3)⁻¹ • G2PBW.x3 q (E R v i) (E R v j) := by
  have e := tripleSix_S_Ej Hi hij h
  change (T i) (E R v j) = _ at e
  rw [e, g2_X_three R v (pow_ne_zero _ (NeZero.ne v))]


-- @@ L167-173 verbatim
include Hi Hj hij h h' hq in
lemma g2_TiTj_Ei : (T i) ((T j) (E R v i)) = g2c3 q • G2PBW.x2 q (E R v i) (E R v j) := by
  have e1 := tripleSix_T_Ei Hj hij
  change (T j) (E R v i) = _ at e1
  have e2 := tripleSix_S_Yv Hi hij h h' hq
  change (T i) _ = _ at e2
  rw [e1, e2, g2_X_two R v (pow_ne_zero _ (NeZero.ne v))]


-- @@ L175-179 verbatim
include Hj hij h h' hq h3 in
lemma g2_Tj_X1 : (T j) (G2PBW.x1 q (E R v i) (E R v j)) = E R v i := by
  have e := tripleSix_T_X_one Hj hij h h' hq h3
  change (T j) _ = _ at e
  rwa [g2_X_one] at e


-- @@ L181-185 verbatim
include Hj hij h h' hq h3 in
lemma g2_Tj_X2 : (T j) (G2PBW.x2 q (E R v i) (E R v j)) = G2PBW.y2 q (E R v i) (E R v j) := by
  rw [G2PBW.x2, map_sub, map_mul, map_smul, map_mul, g2_Tj_X1 R v T Hj hij h h' hq h3,
    g2_Tj_Ei R v T Hj hij h h']
  rfl


-- @@ L187-191 verbatim
include Hj hij h h' hq h3 in
lemma g2_Tj_X3 : (T j) (G2PBW.x3 q (E R v i) (E R v j)) = G2PBW.y3 q (E R v i) (E R v j) := by
  rw [G2PBW.x3, map_sub, map_mul, map_smul, map_mul, g2_Tj_X2 R v T Hj hij h h' hq h3,
    g2_Tj_Ei R v T Hj hij h h']
  rfl


-- @@ L193-199 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TiTj_X2 :
    (T i) ((T j) (G2PBW.x2 q (E R v i) (E R v j))) = g2c2 q • G2PBW.x1 q (E R v i) (E R v j) := by
  have e := tripleSix_S_TX2 Hi Hj hij h h' hq h3
  change (T i) ((T j) _) = _ at e
  rw [g2_X_two R v (pow_ne_zero _ (NeZero.ne v)), g2_X_one] at e
  exact e


-- @@ L201-211 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TiTjTi_Ej : (T i) ((T j) ((T i) (E R v j))) =
    ((qFactorial q 3)⁻¹ * g2c3 q * g2c2 q) • G2PBW.z q (E R v i) (E R v j) := by
  rw [g2_Ti_Ej R v T Hi hij h, map_smul, map_smul, G2PBW.x3, map_sub, map_mul, map_smul,
    map_mul, g2_Tj_Ei R v T Hj hij h h', map_sub, map_mul, map_smul, map_mul,
    g2_TiTj_X2 R v T Hi Hj hij h h' hq h3]
  have e : (T i) (G2PBW.y1 q (E R v i) (E R v j)) = g2c3 q • G2PBW.x2 q (E R v i) (E R v j) := by
    rw [← g2_Tj_Ei R v T Hj hij h h', g2_TiTj_Ei R v T Hi Hj hij h h' hq]
  rw [e, G2PBW.z]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  module


-- @@ L213-217 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TiTjTiTj_Ei : (T i) ((T j) ((T i) ((T j) (E R v i)))) =
    (g2c3 q * g2c2 q) • G2PBW.x1 q (E R v i) (E R v j) := by
  rw [g2_TiTj_Ei R v T Hi Hj hij h h' hq, map_smul, map_smul,
    g2_TiTj_X2 R v T Hi Hj hij h h' hq h3, smul_smul]


-- @@ L219-222 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TjTi_Ej : (T j) ((T i) (E R v j)) =
    (qFactorial q 3)⁻¹ • G2PBW.y3 q (E R v i) (E R v j) := by
  rw [g2_Ti_Ej R v T Hi hij h, map_smul, g2_Tj_X3 R v T Hj hij h h' hq h3]


-- @@ L224-227 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TjTiTj_Ei : (T j) ((T i) ((T j) (E R v i))) =
    g2c3 q • G2PBW.y2 q (E R v i) (E R v j) := by
  rw [g2_TiTj_Ei R v T Hi Hj hij h h' hq, map_smul, g2_Tj_X2 R v T Hj hij h h' hq h3]


-- @@ L229-234 verbatim
include Hi Hj hij h h' hq h3 in
lemma g2_TjTiTjTi_Ej : (T j) ((T i) ((T j) ((T i) (E R v j)))) =
    ((qFactorial q 3)⁻¹ * g2c3 q * g2c2 q) • G2PBW.w q (E R v i) (E R v j) := by
  rw [g2_TiTjTi_Ej R v T Hi Hj hij h h' hq h3, map_smul, G2PBW.z, map_sub, map_mul, map_smul,
    map_mul, g2_Tj_X2 R v T Hj hij h h' hq h3, g2_Tj_X1 R v T Hj hij h h' hq h3]
  rfl


-- @@ L236-251 verbatim
include Hi Hj hij h h' hq h3 in
/-- The root vectors along `i j i j i j`. -/
theorem altVec_g2 : altVec T (E R v) i j 6 =
    ![E R v i, (qFactorial q 3)⁻¹ • G2PBW.x3 q (E R v i) (E R v j),
      g2c3 q • G2PBW.x2 q (E R v i) (E R v j),
      ((qFactorial q 3)⁻¹ * g2c3 q * g2c2 q) • G2PBW.z q (E R v i) (E R v j),
      (g2c3 q * g2c2 q) • G2PBW.x1 q (E R v i) (E R v j), E R v j] := by
  funext l
  fin_cases l
  · rfl
  · exact g2_Ti_Ej R v T Hi hij h
  · exact g2_TiTj_Ei R v T Hi Hj hij h h' hq
  · exact g2_TiTjTi_Ej R v T Hi Hj hij h h' hq h3
  · exact g2_TiTjTiTj_Ei R v T Hi Hj hij h h' hq h3
  · have e := tripleSix_Ej Hi Hj hij h h' hq h3
    exact e


-- @@ L253-268 verbatim
include Hi Hj hij h h' hq h3 in
/-- The root vectors along `j i j i j i`. -/
theorem altVec_g2_rev : altVec T (E R v) j i 6 =
    ![E R v j, G2PBW.y1 q (E R v i) (E R v j),
      (qFactorial q 3)⁻¹ • G2PBW.y3 q (E R v i) (E R v j),
      g2c3 q • G2PBW.y2 q (E R v i) (E R v j),
      ((qFactorial q 3)⁻¹ * g2c3 q * g2c2 q) • G2PBW.w q (E R v i) (E R v j), E R v i] := by
  funext l
  fin_cases l
  · rfl
  · exact g2_Tj_Ei R v T Hj hij h h'
  · exact g2_TjTi_Ej R v T Hi Hj hij h h' hq h3
  · exact g2_TjTiTj_Ei R v T Hi Hj hij h h' hq h3
  · exact g2_TjTiTjTi_Ej R v T Hi Hj hij h h' hq h3
  · have e := tripleSix_Ei Hi Hj hij h h' hq h3
    exact e


-- @@ L270-270 verbatim
end Values


-- @@ L272-272 verbatim
include Hi Hj hij h h' hq h3


-- @@ L274-299 verbatim
/-- All commutation relations of Levendorskii–Soibelman type hold along both six-letter words. -/
theorem isLS_altVec_g2 :
    IsLS k (altVec T (E R v) i j 6) ∧ IsLS k (altVec T (E R v) j i 6) := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  obtain ⟨h2', h3'⟩ := tripleSix_qInt_ne h3 hv
  have hq2 : (v ^ D.d i) ^ 2 + 1 ≠ 0 := by
    have e : (v ^ D.d i) ^ 2 + 1 = v ^ D.d i * (v ^ D.d i + (v ^ D.d i)⁻¹) := by field_simp
    rw [e]
    exact mul_ne_zero hq0 h2'
  have hS4 := serre_E R v hij
  rw [h, show (1 - (-3 : ℤ)).toNat = 4 by rfl] at hS4
  have hS2 := serre_E R v hij.symm
  rw [h', show (1 - (-1 : ℤ)).toNat = 2 by rfl, parameter_eq_cube_of_triple_edge h h'] at hS2
  have hs2 : (qFactorial (v ^ D.d i) 3)⁻¹ ≠ 0 := inv_ne_zero h3
  have hc3 : g2c3 (v ^ D.d i) ≠ 0 := by
    rw [g2c3, tripleSix_cc_three hq0 hq]
    exact mul_ne_zero hs2 h3'
  have hc2 : g2c2 (v ^ D.d i) ≠ 0 := by
    rw [g2c2, tripleSix_cc_three hq0 hq, tripleSix_cc_two hq0 hq]
    exact mul_ne_zero (mul_ne_zero hs2 h3') (pow_ne_zero _ h2')
  refine isLS_altVec T (E R v) (N := 5) ?_ ?_ 6 le_rfl
  · rw [altVec_g2 R v T Hi Hj hij h h' hq h3]
    exact G2PBW.baseRel_fwd hq0 hS4 hS2 hq2 hs2 hc3 (mul_ne_zero hc3 hc2)
  · rw [altVec_g2_rev R v T Hi Hj hij h h' hq h3]
    exact G2PBW.baseRel_rev hq0 hS2 hs2 hc3


-- @@ L301-334 verbatim
/-- The root vectors along either word generate the two-generator subalgebra. -/
lemma adjoin_range_altVec_g2 (a b : I) (hab : (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    Algebra.adjoin k (Set.range (altVec T (E R v) a b 6)) =
      Algebra.adjoin k {E R v i, E R v j} := by
  have hi : E R v i ∈ Algebra.adjoin k {E R v i, E R v j} := Algebra.subset_adjoin (by simp)
  have hj : E R v j ∈ Algebra.adjoin k {E R v i, E R v j} := Algebra.subset_adjoin (by simp)
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [altVec_g2 R v T Hi Hj hij h h' hq h3]
      fin_cases l
      · exact hi
      · exact Subalgebra.smul_mem _ (G2PBW.x3_mem _ _ _) _
      · exact Subalgebra.smul_mem _ (G2PBW.x2_mem _ _ _) _
      · exact Subalgebra.smul_mem _ (G2PBW.z_mem _ _ _) _
      · exact Subalgebra.smul_mem _ (G2PBW.x1_mem _ _ _) _
      · exact hj
    · rw [altVec_g2_rev R v T Hi Hj hij h h' hq h3]
      fin_cases l
      · exact hj
      · exact G2PBW.y1_mem _ _ _
      · exact Subalgebra.smul_mem _ (G2PBW.y3_mem _ _ _) _
      · exact Subalgebra.smul_mem _ (G2PBW.y2_mem _ _ _) _
      · exact Subalgebra.smul_mem _ (G2PBW.w_mem _ _ _) _
      · exact hi
  · rw [Algebra.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Algebra.subset_adjoin ⟨0, rfl⟩
      · exact Algebra.subset_adjoin ⟨5, by rw [altVec_g2_rev R v T Hi Hj hij h h' hq h3]; rfl⟩
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Algebra.subset_adjoin ⟨5, by rw [altVec_g2 R v T Hi Hj hij h h' hq h3]; rfl⟩
      · exact Algebra.subset_adjoin ⟨0, rfl⟩


-- @@ L336-344 verbatim
/-- The actual PBW word `i j i j i j` spans the two-generator subalgebra. -/
theorem span_pbwMonomial_g2 :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i, j, i, j])) =
      (Algebra.adjoin k {E R v i, E R v j}).toSubmodule := by
  have hr : Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i, j, i, j]) =
      Set.range (mono (altVec T (E R v) i j 6)) :=
    congrArg Set.range (funext (pbwMonomial_eq_mono_altVec_six T (E R v) i j))
  rw [hr, span_mono_eq_adjoin _ (isLS_altVec_g2 R v T Hi Hj hij h h' hq h3).1,
    adjoin_range_altVec_g2 R v T Hi Hj hij h h' hq h3 i j (Or.inl ⟨rfl, rfl⟩)]


-- @@ L346-354 verbatim
/-- The actual PBW word `j i j i j i` spans the two-generator subalgebra. -/
theorem span_pbwMonomial_g2_rev :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [j, i, j, i, j, i])) =
      (Algebra.adjoin k {E R v i, E R v j}).toSubmodule := by
  have hr : Set.range (CoxeterSystem.pbwMonomial T (E R v) [j, i, j, i, j, i]) =
      Set.range (mono (altVec T (E R v) j i 6)) :=
    congrArg Set.range (funext (pbwMonomial_eq_mono_altVec_six T (E R v) j i))
  rw [hr, span_mono_eq_adjoin _ (isLS_altVec_g2 R v T Hi Hj hij h h' hq h3).2,
    adjoin_range_altVec_g2 R v T Hi Hj hij h h' hq h3 j i (Or.inr ⟨rfl, rfl⟩)]


-- @@ L356-361 verbatim
/-- The two actual six-letter G₂ words have equal ordered PBW spans. -/
theorem span_pbwMonomial_g2_braid :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i, j, i, j])) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [j, i, j, i, j, i])) := by
  rw [span_pbwMonomial_g2 R v T Hi Hj hij h h' hq h3,
    span_pbwMonomial_g2_rev R v T Hi Hj hij h h' hq h3]


-- @@ L363-375 verbatim
/-- **G₂ span invariance in context.** An actual G₂ braid move preserves the ordered PBW span
in arbitrary prefix/suffix context, given the full six-term braid relation. -/
theorem span_pbwMonomial_g2_context
    (hT : T i * T j * T i * T j * T i * T j = T j * T i * T j * T i * T j * T i)
    (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
      (p ++ [i, j, i, j, i, j] ++ s))) =
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
      (p ++ [j, i, j, i, j, i] ++ s))) := by
  apply CoxeterSystem.span_pbwMonomial_context
    T (E R v) (span_pbwMonomial_g2_braid R v T Hi Hj hij h h' hq h3)
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, ← mul_assoc] using hT


-- @@ L377-401 verbatim
omit hq h3 Hi Hj in
/-- At a non-root-of-unity parameter the constructed braid automorphisms satisfy the six-term
braid relation (`isBraidLiftable_braidEquivOfNotRoot`), so G₂ braid moves preserve ordered
PBW spans in arbitrary word context. -/
theorem span_pbwMonomial_g2_context_of_not_root
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) (p ++ [i, j, i, j, i, j] ++ s))) =
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) (p ++ [j, i, j, i, j, i] ++ s))) := by
  apply span_pbwMonomial_g2_context R v (braidEquivOfNotRoot R hv')
    (braidEquivOfNotRoot_images hv' i) (braidEquivOfNotRoot_images hv' j) hij h h'
    (shortNode_braidGeneric_of_not_root hv' i).sub_ne
    (qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i 3)
  have hLift : D.cartanMatrix.coxeterMatrix.IsBraidLiftable (braidEquivOfNotRoot R hv') :=
    isBraidLiftable_braidEquivOfNotRoot R hv'
  have hm : D.cartanMatrix.coxeterMatrix i j = 6 := by
    rw [Matrix.coxeterMatrix_apply_of_ne _ hij, h, h']
    rfl
  have hm' : D.cartanMatrix.coxeterMatrix j i = 6 := by
    rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, h, h']
    rfl
  have e := hLift i j hij (by omega)
  simpa [CoxeterSystem.braidWord, hm, hm', CoxeterSystem.alternatingWord,
    ← mul_assoc] using e


-- @@ L403-403 verbatim
end LieLean.QuantumGroup
