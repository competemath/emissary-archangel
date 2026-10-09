import OAI.Geometry.LatticeCovering.CircuitLattices


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open MeasureTheory Filter Set

-- @@ L10-10 verbatim
open scoped Topology

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory Filter Set

-- @@ L13-13 verbatim
open scoped Topology ENNReal

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
noncomputable section

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace SingleLatticeCovering.CircuitGridSum

-- @@ L23-23 verbatim
open CircuitVolume SimplexYoung GridGeometry FiniteKernel CircuitGrid

-- @@ L24-24 verbatim
open MeasureTheory Measure Filter

-- @@ L25-25 verbatim
open scoped Topology Pointwise BigOperators





-- @@ L30-81 verbatim
theorem eventually_sum_normalized_circuits_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)}
    (hJc : IsCompact J) (hJv : Convex ℝ J) (h0 : 0 ∈ J)
    (X : ℝ → PrimitiveAffineCoefficients r → Finset (Fin (r+1) → Fin d → ℤ))
    {B : ℝ} (hB : 1 ≤ B)
    (hX : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ i j, |(x i j:ℝ)| ≤ B*t)
    (hJ : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ i, (fun j => t⁻¹*(x i j:ℝ)) ∈ J)
    (hrel : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ j, ∑ i, a.val i*x i j = 0)
    (hind : ∀ t, 1 ≤ t → ∀ a x, x ∈ X t a → ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      (∑' a : PrimitiveAffineCoefficients r, ((X t a).card:ℝ)/t^(r*d)) <
        (affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  let w : PrimitiveAffineCoefficients r → ℝ :=
    fun a => ∏ i, |(a.val i:ℝ)|^(-((d:ℝ)/(r+1:ℕ)))
  have hw : Summable w :=
    (CircuitWeight.summable_circuit_weight hd).comp_injective Subtype.val_injective
  let b : PrimitiveAffineCoefficients r → ℝ := fun a => (2*(r+1)*B)^(r*d)*w a
  have hb : Summable b := hw.mul_left _
  have hb0 (a) : 0 ≤ b a := by dsimp [b,w]; positivity
  let G : PrimitiveAffineCoefficients r → ℝ := fun a => (rationalCircuitVolume J a.val).toReal
  have hG : Summable G :=
    (summable_rationalCircuitVolume_toReal hr hd hJc).comp_injective Subtype.val_injective
  let g : ℝ → PrimitiveAffineCoefficients r → ℝ := fun t a => max 0
    ((Nat.card ↥(weightedGridConfiguration J (fun i => -(a.val i.succ:ℝ)/(a.val 0:ℝ)) ∩
        t⁻¹ • (kernelLattice (gridRelationForm (d:=d) (a.val 0).natAbs (fun i => a.val i.succ)) :
          Set (Fin r × Fin d → ℝ))) : ℝ) / t^(r*d))
  have hlim (a) : Tendsto (fun t => g t a) atTop (𝓝 (G a)) := by
    have hh := GridLimit.primitive_configuration_limit a.val (a.property.1 0)
      a.property.2.1 hJc hJv h0
    rw [←rationalCircuitVolume_toReal hJc a.val a.property.1] at hh
    change Tendsto (fun t => max (0:ℝ) _) atTop (𝓝 _)
    simpa only [max_eq_right ENNReal.toReal_nonneg] using
      (tendsto_const_nhds (x:=(0:ℝ))).max hh
  have hf : ∀ᶠ t : ℝ in atTop, ∀ a : PrimitiveAffineCoefficients r,
      0 ≤ ((X t a).card:ℝ)/t^(r*d) ∧ ((X t a).card:ℝ)/t^(r*d) ≤ g t a ∧
        ((X t a).card:ℝ)/t^(r*d) ≤ b a := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    intro a
    refine ⟨by positivity, ?_, ?_⟩
    · exact (GridLimit.circuit_count_le_primitive_grid a.val (a.property.1 0) J hJc
        (X t a) ht0 (hJ t ht a) (hrel t ht a)).trans (le_max_right _ _)
    · exact normalized_circuit_grid_domination a.val a.property.1 a.property.2.1 a.property.2.2
        (X t a) hB ht (hX t ht a) (hrel t ht a) (hind t ht a)
  have hh := CircuitLimit.eventually_tsum_le_of_dominated_comparison
    (fun t a => ((X t a).card:ℝ)/t^(r*d)) g G b hb hb0 (fun _ _ => le_max_left _ _) hG hlim hf hε
  filter_upwards [hh] with t ht
  apply ht.trans_le
  change (∑' a : PrimitiveAffineCoefficients r, (rationalCircuitVolume J a.val).toReal)+ε ≤ _
  linarith [primitive_volume_sum_le hr hd hJc]



-- @@ L84-84 verbatim
end SingleLatticeCovering.CircuitGridSum





-- @@ L89-89 verbatim
noncomputable section

-- @@ L90-90 verbatim
namespace SingleLatticeCovering.PrimitiveCircuit

-- @@ L91-91 verbatim
open Module Matrix

-- @@ L92-92 verbatim
open scoped BigOperators


-- @@ L94-117 verbatim
lemma integer_relation_of_rat_dependence {s d : ℕ} (v : Fin s → Fin d → ℤ)
    (hdep : ¬LinearIndependent ℚ (fun i => fun j => (v i j : ℚ))) :
    ∃ z : Fin s → ℤ, (∃ i, z i ≠ 0) ∧ ∀ j, ∑ i, z i*v i j = 0 := by
  classical
  obtain ⟨g,hg,i,hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨q,hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) g
  choose z hz using hq
  have hq0 : (q : ℤ) ≠ 0 := nonZeroDivisors.ne_zero q.property
  have hzcast (i) : (z i : ℚ) = (q:ℤ)*g i := by
    simpa only [Algebra.smul_def, eq_intCast, Int.cast_id] using hz i
  refine ⟨z, ⟨i, ?_⟩, ?_⟩
  · intro hzi
    have h := hzcast i
    rw [hzi, Int.cast_zero] at h
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hq0) hi) h.symm
  · intro j
    have hj := congrFun hg j
    have hs : (∑ i, (z i:ℚ)*(v i j:ℚ)) = 0 := by
      simp_rw [hzcast, mul_assoc, ←Finset.mul_sum]
      have he : (∑ i, g i*(v i j:ℚ)) = 0 := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj
      rw [he, mul_zero]
    exact_mod_cast hs


-- @@ L119-142 verbatim
lemma primitive_normalize {s d : ℕ} (v : Fin s → Fin d → ℤ) (z : Fin s → ℤ)
    (hne : ∃ i, z i ≠ 0) (hrel : ∀ j, ∑ i, z i*v i j = 0) :
    ∃ a : Fin s → ℤ, Finset.univ.gcd a = 1 ∧ (∃ i, a i ≠ 0) ∧
      ∀ j, ∑ i, a i*v i j = 0 := by
  classical
  obtain ⟨i,hi⟩ := hne
  let q := Finset.univ.gcd z
  let a := fun i => z i/q
  have hdiv (j) : q ∣ z j := Finset.gcd_dvd (Finset.mem_univ j)
  have hza (j) : q*a j = z j := by
    dsimp [a]
    exact Int.mul_ediv_cancel' (hdiv j)
  have hq : q ≠ 0 := by
    intro hq
    apply hi
    rw [←hza i,hq,zero_mul]
  refine ⟨a, Finset.gcd_div_eq_one (Finset.mem_univ i) hi, ⟨i, ?_⟩, ?_⟩
  · intro hai
    apply hi
    rw [←hza i,hai,mul_zero]
  · intro j
    apply mul_left_cancel₀ hq
    rw [mul_zero, Finset.mul_sum]
    simpa only [←mul_assoc, hza] using hrel j


-- @@ L144-165 verbatim
lemma coefficients_nonzero_of_delete_independent {r d : ℕ}
    (v : Fin (r+1) → Fin d → ℤ) (a : Fin (r+1) → ℤ)
    (hne : ∃ i, a i ≠ 0) (hrel : ∀ j, ∑ i, a i*v i j = 0)
    (hind : ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ (fun i : Fin r => fun j => (v (e i.succ) j : ℚ))) :
    ∀ i, a i ≠ 0 := by
  classical
  intro k hk
  let e := Equiv.swap (0 : Fin (r+1)) k
  have h0 : a (e 0) = 0 := by simpa [e] using hk
  have hz : (∑ i : Fin r, (a (e i.succ):ℚ) • (fun j => (v (e i.succ) j:ℚ))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hperm := (Equiv.sum_comp e (fun i => a i*v i j)).trans (hrel j)
    rw [Fin.sum_univ_succ, h0, zero_mul, zero_add] at hperm
    exact_mod_cast hperm
  have hc := Fintype.linearIndependent_iff.mp (hind e) _ hz
  obtain ⟨i,hi⟩ := hne
  obtain ⟨j,rfl⟩ := e.surjective i
  apply hi
  refine Fin.cases h0 (fun j => ?_) j
  exact Int.cast_eq_zero.mp (hc j)




-- @@ L169-177 verbatim
theorem exists_primitive_circuit_relation {r d : ℕ} (v : Fin (r+1) → Fin d → ℤ)
    (hdep : ¬LinearIndependent ℚ (fun i => fun j => (v i j : ℚ)))
    (hind : ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ (fun i : Fin r => fun j => (v (e i.succ) j : ℚ))) :
    ∃ a : Fin (r+1) → ℤ, Finset.univ.gcd a = 1 ∧ (∀ i, a i ≠ 0) ∧
      ∀ j, ∑ i, a i*v i j = 0 := by
  obtain ⟨z,hzne,hzrel⟩ := integer_relation_of_rat_dependence v hdep
  obtain ⟨a,hprim,hane,harel⟩ := primitive_normalize v z hzne hzrel
  exact ⟨a,hprim,coefficients_nonzero_of_delete_independent v a hane harel hind,harel⟩



-- @@ L180-180 verbatim
end SingleLatticeCovering.PrimitiveCircuit


-- @@ L182-182 verbatim
noncomputable section

-- @@ L183-183 verbatim
namespace SingleLatticeCovering.RogersPreparation

-- @@ L184-184 verbatim
open Matrix


-- @@ L186-189 verbatim
lemma int_det_abs_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) {B : ℕ}
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) : |A.det| ≤ (k.factorial * B^k : ℕ) := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hB
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow] using h


-- @@ L191-198 verbatim
lemma intCast_eq_zero_small (p : ℕ) {z : ℤ} (hz : z.natAbs < p) :
    (z : ZMod p)=0 ↔ z=0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hz)
  · rintro rfl
    exact dvd_zero _


-- @@ L200-207 verbatim
lemma det_mod_eq_zero_small {k : ℕ} (p : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) {B : ℕ}
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) (hp : k.factorial*B^k<p) :
    (A.map (fun z => (z : ZMod p))).det=0 ↔ A.det=0 := by
  rw [←Int.cast_det]
  apply intCast_eq_zero_small
  have h := int_det_abs_le A hB
  have hlt : |A.det| < (p : ℤ) := lt_of_le_of_lt h (by exact_mod_cast hp)
  exact_mod_cast (show (A.det.natAbs : ℤ)<p by rwa [Int.natCast_natAbs])


-- @@ L209-212 verbatim
lemma det_mod_ne_zero_small {k : ℕ} (p : ℕ) (A : Matrix (Fin k) (Fin k) ℤ) {B : ℕ}
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) (hp : k.factorial*B^k<p) (hdet : A.det≠0) :
    (A.map (fun z => (z : ZMod p))).det≠0 :=
  mt (det_mod_eq_zero_small p A hB hp).mp hdet



-- @@ L215-215 verbatim
end SingleLatticeCovering.RogersPreparation



-- @@ L218-218 verbatim
noncomputable section

-- @@ L219-219 verbatim
namespace SingleLatticeCovering.RogersPreparation

-- @@ L220-220 verbatim
open Matrix Module Submodule CircuitGrid




-- @@ L224-241 verbatim
lemma exists_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) (hW : LinearIndependent F W.row) :
    ∃ c : Fin k ↪ Fin n, (W.submatrix id c).det≠0 := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' F W.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have htop : Submodule.span F (Set.range (W.col ∘ a))=⊤ := by
    rw [hspan,←Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (mulVec_surjective_of_rowIndependent W hW)
  let b : Basis κ F (Fin k → F) := Basis.mk hli (by rw [htop])
  have hcard : Fintype.card κ=k := by
    rw [←Module.finrank_eq_card_basis b,Module.finrank_pi,Fintype.card_fin]
  let e : Fin k ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let c : Fin k ↪ Fin n := ⟨a ∘ e,ha.comp e.injective⟩
  refine ⟨c,Matrix.nonsingular_iff_det_ne_zero.mp ?_⟩
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact hli.comp e e.injective



-- @@ L244-248 verbatim
lemma rowIndependent_of_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) (c : Fin k → Fin n)
    (hc : (W.submatrix id c).det≠0) : LinearIndependent F W.row := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hc
  exact h.of_comp (LinearMap.funLeft F F c)


-- @@ L250-253 verbatim
lemma rowIndependent_iff_column_minor {F : Type*} [Field F] {k n : ℕ}
    (W : Matrix (Fin k) (Fin n) F) :
    LinearIndependent F W.row ↔ ∃ c : Fin k ↪ Fin n, (W.submatrix id c).det≠0 :=
  ⟨exists_column_minor W,fun ⟨c,hc⟩ => rowIndependent_of_column_minor W c hc⟩




-- @@ L257-269 verbatim
lemma rowIndependent_mod_iff_rat {k n : ℕ} (p : ℕ) [Fact p.Prime]
    (W : Matrix (Fin k) (Fin n) ℤ) {B : ℕ}
    (hB : ∀ i j, |W i j| ≤ (B : ℤ)) (hp : k.factorial*B^k<p) :
    LinearIndependent (ZMod p) (W.map (fun z => (z : ZMod p))).row ↔
      LinearIndependent ℚ (W.map (fun z => (z : ℚ))).row := by
  rw [rowIndependent_iff_column_minor,rowIndependent_iff_column_minor]
  apply exists_congr
  intro c
  have h : ((W.submatrix id c).map (fun z => (z : ZMod p))).det=0 ↔
      (W.submatrix id c).det=0 := det_mod_eq_zero_small p _ (fun i j => hB i (c j)) hp
  have hq : ((W.submatrix id c).map (fun z => (z : ℚ))).det=0 ↔
      (W.submatrix id c).det=0 := by rw [←Int.cast_det,Int.cast_eq_zero]
  exact not_congr (h.trans hq.symm)



-- @@ L272-272 verbatim
end SingleLatticeCovering.RogersPreparation


-- @@ L274-274 verbatim
namespace SingleLatticeCovering.AffineCircuit

-- @@ L275-275 verbatim
open Matrix CircuitVolume CircuitGrid RogersPreparation

-- @@ L276-276 verbatim
open scoped BigOperators



-- @@ L279-280 verbatim
def integerRows {s d : ℕ} (x : Fin s → Fin d → ℤ) : Matrix (Fin s) (Fin (d+1)) ℤ :=
  fun i => Fin.cons 1 (x i)



-- @@ L283-286 verbatim
def IsCircuit {r d : ℕ} (x : Fin (r+1) → Fin d → ℤ) : Prop :=
  ¬LinearIndependent ℚ ((integerRows x).map (fun z => (z:ℚ))).row ∧
    ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ ((integerRows (fun i => x (e i.succ))).map (fun z => (z:ℚ))).row


-- @@ L288-295 verbatim
lemma rowIndependent_real_iff_rat {k n : ℕ} (W : Matrix (Fin k) (Fin n) ℤ) :
    LinearIndependent ℝ (W.map (fun z => (z:ℝ))).row ↔ LinearIndependent ℚ (W.map (fun z => (z:ℚ))).row := by
  rw [rowIndependent_iff_column_minor,rowIndependent_iff_column_minor]
  apply exists_congr
  intro c
  change ((W.submatrix id c).map (Int.cast:ℤ → ℝ)).det ≠ 0 ↔
    ((W.submatrix id c).map (Int.cast:ℤ → ℚ)).det ≠ 0
  simp only [←Int.cast_det,Int.cast_ne_zero]


-- @@ L297-303 verbatim
lemma IsCircuit.real_delete {r d : ℕ} {x : Fin (r+1) → Fin d → ℤ}
    (hx : IsCircuit x) (e : Equiv.Perm (Fin (r+1))) :
    LinearIndependent ℝ (affineRows (fun i => x (e i.succ))).row := by
  have h := (rowIndependent_real_iff_rat (integerRows (fun i => x (e i.succ)))).mpr (hx.2 e)
  convert h using 1
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [affineRows,integerRows]


-- @@ L305-313 verbatim
lemma IsCircuit.primitive_relation {r d : ℕ} {x : Fin (r+1) → Fin d → ℤ}
    (hx : IsCircuit x) : ∃ a : PrimitiveAffineCoefficients r,
      ∀ j, ∑ i, a.val i*x i j = 0 := by
  obtain ⟨a,hg,ha,hrel⟩ := PrimitiveCircuit.exists_primitive_circuit_relation
    (integerRows x) hx.1 hx.2
  have hs : ∑ i, a i = 0 := by simpa [integerRows] using hrel 0
  refine ⟨⟨a,ha,hg,hs⟩,?_⟩
  intro j
  simpa [integerRows] using hrel j.succ



-- @@ L316-318 verbatim
def circuits {d : ℕ} (S : Finset (Fin d → ℤ)) (r : ℕ) : Finset (Fin (r+1) → Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin (r+1) => S)).filter IsCircuit


-- @@ L320-323 verbatim
lemma mem_circuits {r d : ℕ} {S : Finset (Fin d → ℤ)} {x : Fin (r+1) → Fin d → ℤ} :
    x ∈ circuits S r ↔ (∀ i, x i ∈ S) ∧ IsCircuit x := by
  classical
  simp only [circuits,Finset.mem_filter,Fintype.mem_piFinset]


-- @@ L325-328 verbatim
def coefficientCircuits {r d : ℕ} (S : Finset (Fin d → ℤ)) (a : PrimitiveAffineCoefficients r) :
    Finset (Fin (r+1) → Fin d → ℤ) := by
  classical
  exact (circuits S r).filter (fun x => ∀ j, ∑ i, a.val i*x i j = 0)


-- @@ L330-335 verbatim
lemma mem_coefficientCircuits {r d : ℕ} {S : Finset (Fin d → ℤ)}
    {a : PrimitiveAffineCoefficients r} {x : Fin (r+1) → Fin d → ℤ} :
    x ∈ coefficientCircuits S a ↔ ((∀ i, x i ∈ S) ∧ IsCircuit x) ∧
      ∀ j, ∑ i, a.val i*x i j = 0 := by
  classical
  simp only [coefficientCircuits,Finset.mem_filter,mem_circuits]


-- @@ L337-341 verbatim
lemma circuits_covered {r d : ℕ} {S : Finset (Fin d → ℤ)}
    {x : Fin (r+1) → Fin d → ℤ} (hx : x ∈ circuits S r) :
    ∃ a : PrimitiveAffineCoefficients r, x ∈ coefficientCircuits S a := by
  obtain ⟨a,ha⟩ := (mem_circuits.mp hx).2.primitive_relation
  exact ⟨a,mem_coefficientCircuits.mpr ⟨mem_circuits.mp hx,ha⟩⟩




-- @@ L345-345 verbatim
end SingleLatticeCovering.AffineCircuit




-- @@ L349-349 verbatim
noncomputable section

-- @@ L350-350 verbatim
namespace SingleLatticeCovering.CircuitEnumeration

-- @@ L351-351 verbatim
open scoped BigOperators


-- @@ L353-353 verbatim
variable {ι : Type*} [DecidableEq ι]




-- @@ L357-358 verbatim
def Enumerations (B : Finset (Finset ι)) (r : ℕ) :=
  (T : B) × (Fin r ≃ T.val)


-- @@ L360-362 verbatim
instance (B : Finset (Finset ι)) (r : ℕ) : Fintype (Enumerations B r) := by
  unfold Enumerations
  infer_instance


-- @@ L364-374 verbatim
lemma card_enumerations (B : Finset (Finset ι)) (r : ℕ)
    (hr : ∀ T ∈ B, T.card = r) :
    Fintype.card (Enumerations B r) = B.card*r.factorial := by
  classical
  unfold Enumerations
  rw [Fintype.card_sigma]
  have he (T : B) : Fintype.card (Fin r ≃ T.val) = r.factorial := by
    have hc : Fintype.card (Fin r) = Fintype.card T.val := by
      simp only [Fintype.card_fin,Fintype.card_coe,hr T.val T.property]
    simpa using Fintype.card_equiv (Fintype.equivOfCardEq hc)
  simp [he]


-- @@ L376-378 verbatim
def orderedCircuit {r : ℕ} {B : Finset (Finset ι)} (e : B → ι)
    (x : Enumerations B r) : Fin (r+1) → ι :=
  Fin.cons (e x.1) (fun i => (x.2 i).val)


-- @@ L380-405 verbatim
lemma orderedCircuit_injective {ι : Type*} [DecidableEq ι] {r : ℕ} {B : Finset (Finset ι)} (e : B → ι) :
    Function.Injective (orderedCircuit (r:=r) e) := by
  classical
  rintro ⟨T,x⟩ ⟨U,y⟩ h
  have htail (i : Fin r) : (x i).val = (y i).val := by
    exact congrFun h i.succ
  have hTU : T = U := by
    apply Subtype.ext
    apply Finset.coe_injective
    have hx : Set.range (fun i => (x i).val) = (T.val : Set ι) := by
      change Set.range (Subtype.val ∘ x) = _
      rw [x.surjective.range_comp]
      exact Subtype.range_val
    have hy : Set.range (fun i => (y i).val) = (U.val : Set ι) := by
      change Set.range (Subtype.val ∘ y) = _
      rw [y.surjective.range_comp]
      exact Subtype.range_val
    rw [←hx,←hy]
    congr 1
    funext i
    exact htail i
  subst U
  congr 1
  apply Equiv.ext
  intro i
  exact Subtype.ext (htail i)




-- @@ L409-418 verbatim
theorem factorial_count_le {r : ℕ} {B : Finset (Finset ι)}
    (hr : ∀ T ∈ B, T.card = r) (e : B → ι)
    (C : Finset (Fin (r+1) → ι))
    (hC : ∀ x : Enumerations B r, orderedCircuit e x ∈ C) :
    B.card*r.factorial ≤ C.card := by
  let f : Enumerations B r → C := fun x => ⟨orderedCircuit e x,hC x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact orderedCircuit_injective e (congrArg Subtype.val hxy)
  simpa only [card_enumerations B r hr,Fintype.card_coe] using Fintype.card_le_of_injective f hf




-- @@ L422-440 verbatim
theorem card_mul_le_tsum_cover {α β : Type*} [DecidableEq β]
    (C : Finset β) (X : α → Finset β)
    (hC : ∀ x ∈ C, ∃ a, x ∈ X a) {u : ℝ} (hu : 0 ≤ u)
    (hs : Summable (fun a => ((X a).card:ℝ)*u)) :
    (C.card:ℝ)*u ≤ ∑' a, ((X a).card:ℝ)*u := by
  classical
  choose a ha using fun x : C => hC x.val x.property
  let A : Finset α := Finset.univ.image a
  have hsub : C ⊆ A.biUnion X := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨a ⟨x,hx⟩,Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_univ _,rfl⟩,ha ⟨x,hx⟩⟩
  have hc : C.card ≤ ∑ a ∈ A, (X a).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcr : (C.card:ℝ) ≤ ∑ a ∈ A, ((X a).card:ℝ) := by exact_mod_cast hc
  calc
    (C.card:ℝ)*u ≤ (∑ a ∈ A, ((X a).card:ℝ))*u := mul_le_mul_of_nonneg_right hcr hu
    _ = ∑ a ∈ A, ((X a).card:ℝ)*u := by rw [Finset.sum_mul]
    _ ≤ ∑' a, ((X a).card:ℝ)*u := hs.sum_le_tsum A (fun _ _ => by positivity)



-- @@ L443-456 verbatim
theorem factorial_weight_le_tsum {α : Type*} {r : ℕ} {B : Finset (Finset ι)}
    (hr : ∀ T ∈ B, T.card = r) (e : B → ι)
    (C : Finset (Fin (r+1) → ι))
    (hC : ∀ x : Enumerations B r, orderedCircuit e x ∈ C)
    (X : α → Finset (Fin (r+1) → ι))
    (hX : ∀ x ∈ C, ∃ a, x ∈ X a) {u : ℝ} (hu : 0 ≤ u)
    (hs : Summable (fun a => ((X a).card:ℝ)*u)) :
    (B.card:ℝ)*u ≤ (∑' a, ((X a).card:ℝ)*u)/(r.factorial:ℝ) := by
  have hc : (B.card:ℝ)*(r.factorial:ℝ) ≤ (C.card:ℝ) := by
    exact_mod_cast factorial_count_le hr e C hC
  have hsum := card_mul_le_tsum_cover C X hX hu hs
  have hfact : (0:ℝ) < (r.factorial:ℝ) := by exact_mod_cast r.factorial_pos
  apply (le_div_iff₀ hfact).mpr
  nlinarith [mul_le_mul_of_nonneg_right hc hu]




-- @@ L460-460 verbatim
end SingleLatticeCovering.CircuitEnumeration


-- @@ L462-462 verbatim
namespace SingleLatticeCovering.AffineCircuit

-- @@ L463-463 verbatim
open CircuitVolume CircuitGrid MeasureTheory Measure Filter

-- @@ L464-464 verbatim
open scoped BigOperators Topology


-- @@ L466-482 verbatim
lemma coefficient_counts_summable {r d : ℕ} (hd : 2*(r+1) ≤ d)
    (S : Finset (Fin d → ℤ)) {B t : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hS : ∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ B*t) :
    Summable (fun a : PrimitiveAffineCoefficients r =>
      ((coefficientCircuits S a).card:ℝ)/t^(r*d)) := by
  have hw := (CircuitWeight.summable_circuit_weight hd).comp_injective
    (Subtype.val_injective (p:=fun a : Fin (r+1) → ℤ =>
      (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0))
  apply (hw.mul_left ((2*(r+1)*B)^(r*d))).of_nonneg_of_le
  · intro a
    positivity
  · intro a
    exact normalized_circuit_grid_domination a.val a.property.1 a.property.2.1 a.property.2.2
      (coefficientCircuits S a) hB ht
      (fun x hx i j => hS (x i) ((mem_coefficientCircuits.mp hx).1.1 i) j)
      (fun x hx => (mem_coefficientCircuits.mp hx).2)
      (fun x hx => (mem_coefficientCircuits.mp hx).1.2.real_delete)





-- @@ L487-508 verbatim
theorem eventually_circuit_count_le {r d : ℕ} (hr : 0 < r)
    (hd : 2*(r+1) ≤ d) {J : Set (Fin d → ℝ)} (hJc : IsCompact J)
    (hJv : Convex ℝ J) (h0 : 0 ∈ J) (S : ℝ → Finset (Fin d → ℤ))
    {B : ℝ} (hB : 1 ≤ B)
    (hS : ∀ t, 1 ≤ t → ∀ z ∈ S t, ∀ j, |(z j:ℝ)| ≤ B*t)
    (hSJ : ∀ t, 1 ≤ t → ∀ z ∈ S t, (fun j => t⁻¹*(z j:ℝ)) ∈ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ((circuits (S t) r).card:ℝ)/t^(r*d) <
      (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal+ε := by
  have hh := CircuitGridSum.eventually_sum_normalized_circuits_le hr hd hJc hJv h0
    (fun t a => coefficientCircuits (S t) a) hB
    (fun t ht a x hx i j => hS t ht (x i) ((mem_coefficientCircuits.mp hx).1.1 i) j)
    (fun t ht a x hx i => hSJ t ht (x i) ((mem_coefficientCircuits.mp hx).1.1 i))
    (fun t ht a x hx => (mem_coefficientCircuits.mp hx).2)
    (fun t ht a x hx => (mem_coefficientCircuits.mp hx).1.2.real_delete) hε
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with t hlim ht
  apply lt_of_le_of_lt ?_ hlim
  have hs := coefficient_counts_summable hd (S t) hB ht (hS t ht)
  have hp := CircuitEnumeration.card_mul_le_tsum_cover (circuits (S t) r)
    (coefficientCircuits (S t)) (fun x hx => circuits_covered hx)
    (u:=(t^(r*d))⁻¹) (by positivity) (by simpa only [div_eq_mul_inv] using hs)
  simpa only [div_eq_mul_inv] using hp



-- @@ L511-511 verbatim
end SingleLatticeCovering.AffineCircuit


-- @@ L513-513 verbatim
namespace SingleLatticeCovering.CircuitEnumeration

-- @@ L514-514 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L515-526 verbatim
theorem factorial_count_le_map {κ : Type*} {r : ℕ} {B : Finset (Finset ι)}
    (hr : ∀ T ∈ B, T.card = r) (e : B → ι) (f : ι → κ) (hf : Function.Injective f)
    (C : Finset (Fin (r+1) → κ))
    (hC : ∀ x : Enumerations B r, (fun i => f (orderedCircuit e x i)) ∈ C) :
    B.card*r.factorial ≤ C.card := by
  let g : Enumerations B r → C := fun x => ⟨fun i => f (orderedCircuit e x i),hC x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply orderedCircuit_injective e
    funext i
    exact hf (congrFun (congrArg Subtype.val hxy) i)
  simpa only [card_enumerations B r hr,Fintype.card_coe] using Fintype.card_le_of_injective g hg



-- @@ L529-529 verbatim
end SingleLatticeCovering.CircuitEnumeration




-- @@ L533-533 verbatim
noncomputable section

-- @@ L534-534 verbatim
namespace SingleLatticeCovering.BrokenCircuit

-- @@ L535-535 verbatim
open scoped BigOperators

-- @@ L536-536 verbatim
open Submodule


-- @@ L538-538 verbatim
variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]




-- @@ L542-543 verbatim
def Active (v : ι → V) (S : Finset ι) (e : ι) : Prop :=
  v e ∈ Submodule.span K (v '' (↑(S.filter (fun j => e < j)) : Set ι))


-- @@ L545-546 verbatim
def NoBrokenCircuit (v : ι → V) (S : Finset ι) : Prop :=
  ∀ e, ¬Active (K := K) v S e


-- @@ L548-554 verbatim
lemma active_mono {v : ι → V} {S T : Finset ι} (hST : S ⊆ T) {e : ι}
    (h : Active (K := K) v S e) : Active (K := K) v T e := by
  apply Submodule.span_mono _ h
  exact Set.image_mono (by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨hST (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩)


-- @@ L556-560 verbatim
lemma NoBrokenCircuit.mono {v : ι → V} {S T : Finset ι}
    (hT : NoBrokenCircuit (K := K) v T) (hST : S ⊆ T) :
    NoBrokenCircuit (K := K) v S := by
  intro e he
  exact hT e (active_mono hST he)


-- @@ L562-579 verbatim
lemma NoBrokenCircuit.linearIndepOn {v : ι → V} {S : Finset ι}
    (h : NoBrokenCircuit (K := K) v S) : LinearIndepOn K v (S : Set ι) := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert a S ha ih =>
    have hS := h.mono (Finset.subset_insert a S)
    have hn : v a ∉ Submodule.span K (v '' (S : Set ι)) := by
      have he : (insert a S).filter (fun j => a < j) = S := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hj, haj⟩
          · exact (lt_irrefl _ haj).elim
          · exact hj
        · intro hj
          exact ⟨Or.inr hj, ha j hj⟩
      simpa only [Active, he] using h a
    simpa only [Finset.coe_insert] using (ih hS).insert hn


-- @@ L581-586 verbatim
lemma active_zero {v : ι → V} {S : Finset ι} {e : ι} (L : V →ₗ[K] K)
    (hS : ∀ j ∈ S, L (v j) = 0) (he : Active (K := K) v S e) : L (v e) = 0 := by
  change v e ∈ L.ker
  apply (Submodule.span_le.mpr _) he
  rintro _ ⟨j,hj,rfl⟩
  exact hS j (Finset.mem_filter.mp hj).1





-- @@ L591-613 verbatim
lemma nbc_insert_least_zero {v : ι → V} {S : Finset ι} {a : ι}
    (L : V →ₗ[K] K) (hS : ∀ j ∈ S, L (v j) = 0) (ha : L (v a) = 0)
    (hmin : ∀ j, L (v j) = 0 → a ≤ j) :
    NoBrokenCircuit (K := K) v (insert a S) ↔ NoBrokenCircuit (K := K) v S := by
  constructor
  · exact fun h => h.mono (Finset.subset_insert _ _)
  · intro h e he
    have hz : L (v e) = 0 := active_zero L (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ha
      · exact hS j hj) he
    have hae : a ≤ e := hmin e hz
    have hfilter : (insert a S).filter (fun j => e < j) = S.filter (fun j => e < j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hel⟩
        · exact (not_lt_of_ge hae hel).elim
        · exact ⟨hj,hel⟩
      · intro hj
        exact ⟨Or.inr hj.1,hj.2⟩
    exact h e (by simpa only [Active,hfilter] using he)


-- @@ L615-615 verbatim
section Cone

-- @@ L616-616 verbatim
variable {α : Type*} [DecidableEq α]




-- @@ L620-665 verbatim
theorem cone_partial_sum (F : Finset (Finset α)) (a : α)
    (hins : ∀ S ∈ F, insert a S ∈ F) (herase : ∀ S ∈ F, S.erase a ∈ F) (k : ℕ) :
    (∑ S ∈ F, if S.card ≤ k then (-1:ℝ)^S.card else 0) =
      (-1:ℝ)^k * ((F.filter (fun S => a ∉ S ∧ S.card = k)).card:ℝ) := by
  let F₀ := F.filter (fun S => a ∉ S)
  have hsplit : F = F₀ ∪ F₀.image (insert a) := by
    ext S
    constructor
    · intro hS
      by_cases ha : a ∈ S
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨S.erase a, Finset.mem_filter.mpr ⟨herase S hS, Finset.notMem_erase _ _⟩,
          Finset.insert_erase ha⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,ha⟩)
    · intro hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact (Finset.mem_filter.mp hS).1
      · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
        exact hins T (Finset.mem_filter.mp hT).1
  have hd : Disjoint F₀ (F₀.image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hS'
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS'
    exact (Finset.mem_filter.mp hS).2 (Finset.mem_insert_self _ _)
  have hi : Set.InjOn (insert a) (↑F₀ : Set (Finset α)) := by
    intro S hS T hT h
    have hS' := (Finset.mem_filter.mp hS).2
    have hT' := (Finset.mem_filter.mp hT).2
    simpa only [Finset.erase_insert hS', Finset.erase_insert hT'] using congrArg (Finset.erase · a) h
  conv_lhs => rw [hsplit, Finset.sum_union hd, Finset.sum_image hi, ←Finset.sum_add_distrib]
  have hterm (S : Finset α) (hS : S ∈ F₀) :
      (if S.card ≤ k then (-1:ℝ)^S.card else 0) +
      (if (insert a S).card ≤ k then (-1:ℝ)^(insert a S).card else 0) =
        if S.card = k then (-1:ℝ)^k else 0 := by
    rw [Finset.card_insert_of_notMem (Finset.mem_filter.mp hS).2]
    rcases lt_trichotomy S.card k with h | h | h
    · rw [ite_eq_left h.le, ite_eq_left (by omega), ite_eq_right (by omega), pow_succ]
      ring
    · simp [h]
    · simp [show ¬S.card≤k by omega, show ¬S.card+1≤k by omega, show S.card≠k by omega]
  rw [Finset.sum_congr rfl hterm]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm]
  simp only [F₀, Finset.filter_filter]





-- @@ L670-670 verbatim
end Cone


-- @@ L672-672 verbatim
section Pointwise

-- @@ L673-673 verbatim
variable [Fintype ι]


-- @@ L675-677 verbatim
def zeroFamily (v : ι → V) (L : V →ₗ[K] K) : Finset ι := by
  classical
  exact Finset.univ.filter (fun e => L (v e) = 0)


-- @@ L679-681 verbatim
def nbcFaces (v : ι → V) (Z : Finset ι) : Finset (Finset ι) := by
  classical
  exact Z.powerset.filter (NoBrokenCircuit (K := K) v)


-- @@ L683-684 verbatim
def nbcValue (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) : ℝ :=
  ∑ S ∈ nbcFaces (K := K) v (zeroFamily v L), if S.card ≤ k then (-1:ℝ)^S.card else 0


-- @@ L686-688 verbatim
def avoidanceIndicator (v : ι → V) (L : V →ₗ[K] K) : ℝ := by
  classical
  exact if ∀ e, L (v e) ≠ 0 then 1 else 0


-- @@ L690-693 verbatim
lemma mem_zeroFamily {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype ι] {v : ι → V} {L : V →ₗ[K] K} {e : ι} :
    e ∈ zeroFamily v L ↔ L (v e) = 0 := by
  classical
  simp [zeroFamily]


-- @@ L695-698 verbatim
lemma mem_nbcFaces {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype ι] {v : ι → V} {Z : Finset ι} {S : Finset ι} :
    S ∈ nbcFaces (K := K) v Z ↔ S ⊆ Z ∧ NoBrokenCircuit (K := K) v S := by
  classical
  simp [nbcFaces]




-- @@ L702-752 verbatim
theorem nbc_alternating_bound (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) :
    0 ≤ (-1:ℝ)^k * (nbcValue v L k - avoidanceIndicator v L) := by
  classical
  by_cases hz : ∀ e, L (v e) ≠ 0
  · have he : zeroFamily v L = ∅ := by
      ext e
      simp [mem_zeroFamily, hz e]
    have hnbc : NoBrokenCircuit (K := K) v ∅ := by
      intro e he
      exact hz e (active_zero L (by simp) he)
    have hn : nbcFaces (K := K) v ∅ = {∅} := by
      ext S
      simp only [mem_nbcFaces, Finset.subset_empty, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro hS
        subst S
        exact ⟨rfl, hnbc⟩
    simp [nbcValue, he, hn, avoidanceIndicator, hz]
  · have hZ : (zeroFamily v L).Nonempty := by
      push Not at hz
      obtain ⟨e,he⟩ := hz
      exact ⟨e,mem_zeroFamily.mpr he⟩
    let a := (zeroFamily v L).min' hZ
    have ha : a ∈ zeroFamily v L := Finset.min'_mem _ _
    have hmin : ∀ j, L (v j) = 0 → a ≤ j := by
      intro j hj
      exact Finset.min'_le _ _ (mem_zeroFamily.mpr hj)
    have hins : ∀ S ∈ nbcFaces (K := K) v (zeroFamily v L),
        insert a S ∈ nbcFaces (K := K) v (zeroFamily v L) := by
      intro S hS
      obtain ⟨hSZ,hN⟩ := mem_nbcFaces.mp hS
      apply mem_nbcFaces.mpr
      refine ⟨Finset.insert_subset ha hSZ, ?_⟩
      exact (nbc_insert_least_zero L (fun j hj => mem_zeroFamily.mp (hSZ hj))
        (mem_zeroFamily.mp ha) hmin).mpr hN
    have herase : ∀ S ∈ nbcFaces (K := K) v (zeroFamily v L),
        S.erase a ∈ nbcFaces (K := K) v (zeroFamily v L) := by
      intro S hS
      obtain ⟨hSZ,hN⟩ := mem_nbcFaces.mp hS
      exact mem_nbcFaces.mpr ⟨(Finset.erase_subset _ _).trans hSZ,
        hN.mono (Finset.erase_subset _ _)⟩
    have hc := cone_partial_sum (nbcFaces (K := K) v (zeroFamily v L)) a hins herase k
    change nbcValue v L k = _ at hc
    have hs : ((-1:ℝ)^k)^2 = 1 := by
      rw [←pow_mul, mul_comm k 2, pow_mul]
      norm_num
    rw [hc, avoidanceIndicator, ite_eq_right hz, sub_zero]
    have hn : (0:ℝ) ≤ ((nbcFaces (K := K) v (zeroFamily v L)).filter
        (fun S => a ∉ S ∧ S.card = k)).card := Nat.cast_nonneg _
    nlinarith only [hs, hn]


-- @@ L754-758 verbatim
lemma nbc_even_bound (v : ι → V) (L : V →ₗ[K] K) (q : ℕ) :
    avoidanceIndicator v L ≤ nbcValue v L (2*q) := by
  have h := nbc_alternating_bound v L (2*q)
  norm_num [pow_mul] at h
  exact h


-- @@ L760-764 verbatim
lemma nbc_odd_bound (v : ι → V) (L : V →ₗ[K] K) (q : ℕ) :
    nbcValue v L (2*q+1) ≤ avoidanceIndicator v L := by
  have h := nbc_alternating_bound v L (2*q+1)
  norm_num [pow_succ, pow_mul] at h
  linarith





-- @@ L769-769 verbatim
end Pointwise



-- @@ L772-772 verbatim
section FiniteField

-- @@ L773-773 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L774-774 verbatim
variable {τ κ : Type*} [Fintype τ] [Fintype κ]

-- @@ L775-795 verbatim
lemma mulVec_surjective_of_rowIndependent (W : Matrix κ τ K)
    (hW : LinearIndependent K W.row) : Function.Surjective W.mulVec := by
  classical
  have hf : Function.Injective W.vecMulLinear := Matrix.vecMul_injective_iff.mpr hW
  intro b
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective hf
    ((dotProductBilin K K) b)
  refine ⟨fun j => g (Pi.single j 1), ?_⟩
  ext i
  have hi := DFunLike.congr_fun hg (Pi.single i 1)
  have hrow : W.vecMulLinear (Pi.single i 1) = W i := by
    ext j
    simp [Matrix.vecMulLinear, Matrix.vecMul, dotProduct, Pi.single_apply]
  change g (W.vecMulLinear (Pi.single i 1)) = _ at hi
  rw [hrow] at hi
  have hsingle (x : τ) : (fun j => if x=j then (1 : K) else 0) = Pi.single x 1 := by
    funext j
    simp [Pi.single_apply,eq_comm]
  have hgi := LinearMap.pi_apply_eq_sum_univ g (W i)
  simp_rw [hsingle] at hgi
  simpa [Matrix.mulVec, dotProduct, dotProductBilin, Pi.single_apply, mul_comm, eq_comm] using hgi.symm.trans hi


-- @@ L797-807 verbatim
lemma card_fiber_mul_card_of_surjective
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] [Fintype V] [Fintype U]
    (f : V →ₗ[K] U) (hf : Function.Surjective f) (b : U) :
    Fintype.card {x // f x = b} * Fintype.card U = Fintype.card V := by
  classical
  have hc (u : U) : Fintype.card {x // f x = u} = Fintype.card f.ker := by
    exact Fintype.card_congr (f.toAddMonoidHom.fiberEquivKerOfSurjective hf u)
  have hs := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hs
  simpa only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hs


-- @@ L809-822 verbatim
lemma fiber_ratio_of_surjective
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] [Fintype V] [Fintype U]
    (f : V →ₗ[K] U) (hf : Function.Surjective f) (b : U) :
    (Nat.card {x // f x = b} : ℝ) / Fintype.card V =
      (Fintype.card U : ℝ)⁻¹ := by
  rw [Nat.card_eq_fintype_card]
  have hc := card_fiber_mul_card_of_surjective f hf b
  have hU : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : (Fintype.card {x // f x = b} : ℝ) * Fintype.card U = Fintype.card V := by
    exact_mod_cast hc
  field_simp
  nlinarith



-- @@ L825-825 verbatim
variable [Fintype K] [Fintype ι]



-- @@ L828-829 verbatim
def vectorAverage (f : (τ → K) → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card (τ → K)


-- @@ L831-855 verbatim
lemma independent_joint_probability (v : ι → τ → K) (S : Finset ι)
    (h : LinearIndepOn K v (S : Set ι)) :
    vectorAverage (fun a : τ → K => if ∀ i ∈ S,
      (dotProductBilin K K a) (v i) = 0 then 1 else 0) =
        ((Fintype.card K : ℝ)^S.card)⁻¹ := by
  classical
  let W : Matrix S τ K := fun i => v i
  have hi : LinearIndependent K W.row := h
  have hf := fiber_ratio_of_surjective W.mulVecLin
    (mulVec_surjective_of_rowIndependent W hi) 0
  have he (a : τ → K) : W.mulVecLin a = 0 ↔
      ∀ i ∈ S, (dotProductBilin K K a) (v i) = 0 := by
    constructor
    · intro ha i hi
      change dotProduct a (v i) = 0
      rw [dotProduct_comm]
      exact congrFun ha ⟨i,hi⟩
    · intro ha
      ext i
      change dotProduct (v i) a = 0
      rw [dotProduct_comm]
      exact ha i i.property
  simp_rw [he] at hf
  rw [Nat.card_eq_fintype_card] at hf
  simpa [vectorAverage, Fintype.card_subtype, Finset.sum_ite] using hf




-- @@ L859-863 verbatim
lemma vectorAverage_mono {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] {f g : (τ → K) → ℝ} (h : ∀ a, f a ≤ g a) :
    vectorAverage f ≤ vectorAverage g := by
  unfold vectorAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a))
    (Nat.cast_nonneg _)


-- @@ L865-868 verbatim
lemma vectorAverage_sum {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] {Ω : Type*} (s : Finset Ω) (f : Ω → (τ → K) → ℝ) :
    vectorAverage (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, vectorAverage (f i) := by
  unfold vectorAverage
  rw [Finset.sum_comm, Finset.sum_div]


-- @@ L870-874 verbatim
lemma vectorAverage_const_mul {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] (c : ℝ) (f : (τ → K) → ℝ) :
    vectorAverage (fun a => c * f a) = c * vectorAverage f := by
  unfold vectorAverage
  rw [←Finset.mul_sum]
  ring


-- @@ L876-877 verbatim
lemma vectorAverage_zero {K : Type*} [Field K] {τ : Type*} [Fintype τ] [Fintype K] : vectorAverage (fun _ : τ → K => (0:ℝ)) = 0 := by
  simp [vectorAverage]


-- @@ L879-889 verbatim
lemma nbcFaces_zero_eq {ι : Type*} {K : Type*} {V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Fintype ι] (v : ι → V) (L : V →ₗ[K] K) :
    nbcFaces (K := K) v (zeroFamily v L) =
      (nbcFaces (K := K) v Finset.univ).filter (fun S => ∀ i ∈ S, L (v i) = 0) := by
  classical
  ext S
  simp only [mem_nbcFaces, Finset.mem_filter, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hS,hN⟩
    exact ⟨hN,fun i hi => mem_zeroFamily.mp (hS hi)⟩
  · rintro ⟨hN,hS⟩
    exact ⟨fun i hi => mem_zeroFamily.mpr (hS i hi),hN⟩


-- @@ L891-895 verbatim
lemma nbcValue_eq (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) :
    nbcValue v L k = ∑ S ∈ nbcFaces (K := K) v Finset.univ,
      if ∀ i ∈ S, L (v i) = 0 then
        (if S.card ≤ k then (-1:ℝ)^S.card else 0) else 0 := by
  rw [nbcValue, nbcFaces_zero_eq, Finset.sum_filter]


-- @@ L897-899 verbatim
def nbcPolynomial (v : ι → V) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ nbcFaces (K := K) v Finset.univ,
    if S.card ≤ k then (-1:ℝ)^S.card * t^S.card else 0




-- @@ L903-922 verbatim
lemma average_nbcValue (v : ι → τ → K) (k : ℕ) :
    vectorAverage (fun a : τ → K => nbcValue v (dotProductBilin K K a) k) =
      nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) k := by
  simp_rw [nbcValue_eq]
  rw [vectorAverage_sum]
  unfold nbcPolynomial
  apply Finset.sum_congr rfl
  intro S hS
  have hN := (mem_nbcFaces.mp hS).2
  by_cases hc : S.card ≤ k
  · simp only [ite_eq_left hc]
    have he : (fun a : τ → K => if ∀ i ∈ S,
        (dotProductBilin K K a) (v i) = 0 then (-1:ℝ)^S.card else 0) =
        (fun a : τ → K => (-1:ℝ)^S.card *
          (if ∀ i ∈ S, (dotProductBilin K K a) (v i) = 0 then 1 else 0)) := by
      funext a
      split_ifs <;> simp
    rw [he, vectorAverage_const_mul,
      independent_joint_probability v S hN.linearIndepOn, inv_pow]
  · simp only [ite_eq_right hc, ite_self, vectorAverage_zero]




-- @@ L926-930 verbatim
theorem average_avoidance_even_le (v : ι → τ → K) (q : ℕ) :
    vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) ≤
      nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) (2*q) := by
  rw [←average_nbcValue]
  exact vectorAverage_mono (fun a => nbc_even_bound v (dotProductBilin K K a) q)


-- @@ L932-936 verbatim
theorem average_avoidance_odd_ge (v : ι → τ → K) (q : ℕ) :
    nbcPolynomial (K := K) v ((Fintype.card K : ℝ)⁻¹) (2*q+1) ≤
      vectorAverage (fun a : τ → K => avoidanceIndicator v (dotProductBilin K K a)) := by
  rw [←average_nbcValue]
  exact vectorAverage_mono (fun a => nbc_odd_bound v (dotProductBilin K K a) q)






-- @@ L942-942 verbatim
end FiniteField

-- @@ L943-943 verbatim
end SingleLatticeCovering.BrokenCircuit



-- @@ L946-946 verbatim
noncomputable section


-- @@ L948-948 verbatim
end

-- @@ L949-949 verbatim
end

-- @@ L950-950 verbatim
end

-- @@ L951-951 verbatim
end

-- @@ L952-952 verbatim
end

-- @@ L953-953 verbatim
end

-- @@ L954-954 verbatim
end

-- @@ L955-955 verbatim
end

-- @@ L956-956 verbatim
end

-- @@ L957-957 verbatim
end

-- @@ L958-958 verbatim
end

-- @@ L959-959 verbatim
end

-- @@ L960-960 verbatim
end

-- @@ L961-961 verbatim
end

-- @@ L962-962 verbatim
end

-- @@ L963-963 verbatim
end

-- @@ L964-964 verbatim
end

-- @@ L965-965 verbatim
end


-- @@ L967-967 verbatim
end OAI
