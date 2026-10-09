import Mathlib
import OAI.Analysis.Matrix.TensorMoment


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

-- @@ L8-8 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

-- @@ L11-11 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L13-13 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L14-16 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Occupancies of single alphabet symbols in an ordinary tensor word. -/

-- @@ L17-19 verbatim
def count (w : I → A) (a : A) : ℕ := Fintype.card {i : I // w i = a}

/- Ordinary tensor permutation, with the manuscript's product convention. -/

-- @@ L20-24 verbatim
def permute (σ : Equiv.Perm I) : Equiv.Perm (I → A) where
  toFun w i := w (σ⁻¹ i)
  invFun w i := w (σ i)
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp


-- @@ L26-29 verbatim
omit [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] in
lemma permute_mul (σ τ : Equiv.Perm I) :
    permute (A := A) (σ*τ) = permute σ * permute τ := by
  ext w i; simp [permute]


-- @@ L31-32 verbatim
omit [Fintype A] [DecidableEq I] in
lemma count_le (w : I → A) (a : A) : count w a ≤ Fintype.card I := Fintype.card_subtype_le _


-- @@ L34-37 verbatim
omit [DecidableEq I] in
lemma sum_count (w : I → A) : ∑ a, count w a = Fintype.card I := by
  classical
  simpa only [count, Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)


-- @@ L39-52 verbatim
omit [Fintype A] [DecidableEq I] in
lemma counts_eq_exists_perm {u w : I → A} (h : count u = count w) :
    ∃ σ : Equiv.Perm I, permute σ u = w := by
  let e (a : A) : {i : I // u i = a} ≃ {i : I // w i = a} :=
    Fintype.equivOfCardEq (congrFun h a)
  let σ : Equiv.Perm I := Equiv.ofFiberEquiv e
  refine ⟨σ, ?_⟩
  ext i
  have hi : w (σ (σ⁻¹ i)) = u (σ⁻¹ i) := Equiv.ofFiberEquiv_map e (σ⁻¹ i)
  change u (σ⁻¹ i) = w i
  simpa using hi.symm

/- Word-preserving permutations and independent permutations of its fibers
are literally equivalent finite sets. This yields the factorial frame moments. -/

-- @@ L53-67 verbatim
def fiberPermEquiv (w : I → A) :
    {σ : Equiv.Perm I // ∀ i, w (σ i) = w i} ≃ (∀ a : A, Equiv.Perm {i : I // w i = a}) where
  toFun σ a := σ.val.subtypePerm (fun i => by rw [σ.property i])
  invFun τ := ⟨Equiv.ofFiberEquiv τ, Equiv.ofFiberEquiv_map τ⟩
  left_inv σ := by
    apply Subtype.ext
    ext i
    rfl
  right_inv τ := by
    funext a
    apply Equiv.ext
    rintro ⟨i,hi⟩
    apply Subtype.ext
    subst a
    rfl


-- @@ L69-75 verbatim
lemma card_wordStabilizer (w : I → A) :
    Fintype.card {σ : Equiv.Perm I // ∀ i, w (σ i) = w i} =
      ∏ a : A, (count w a).factorial := by
  rw [Fintype.card_congr (fiberPermEquiv w), Fintype.card_pi]
  simp only [Fintype.card_perm, count]

/- A transporter fiber is a coset of the literal word stabilizer. -/

-- @@ L76-92 verbatim
def transporterEquiv (u w : I → A) (σ : Equiv.Perm I) (hσ : permute σ u = w) :
    {g : Equiv.Perm I // permute g u = w} ≃
      {g : Equiv.Perm I // ∀ i, u (g i) = u i} where
  toFun g := ⟨σ⁻¹*g.val, by
    intro i
    have hg : u (g.val⁻¹ (g.val i)) = w (g.val i) := congrFun g.property (g.val i)
    have hs : u (σ⁻¹ (g.val i)) = w (g.val i) := congrFun hσ (g.val i)
    simpa using hs.trans hg.symm⟩
  invFun g := ⟨σ*g.val, by
    ext i
    change u (g.val⁻¹ (σ⁻¹ i)) = w i
    have hg := g.property (g.val⁻¹ (σ⁻¹ i))
    have hs : u (σ⁻¹ i) = w i := congrFun hσ i
    have hh : u (g.val⁻¹ (σ⁻¹ i)) = u (σ⁻¹ i) := by simpa using hg.symm
    exact hh.trans hs⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)


-- @@ L94-102 verbatim
omit [Fintype A] [DecidableEq I] in
lemma permute_count (σ : Equiv.Perm I) (w : I → A) : count (permute σ w) = count w := by
  ext a
  apply Fintype.card_congr
  exact
    { toFun := fun i => ⟨σ⁻¹ i.val, i.property⟩
      invFun := fun i => ⟨σ i.val, by simpa [permute] using i.property⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun i => Subtype.ext (by simp) }


-- @@ L104-115 verbatim
lemma card_transporter (u w : I → A) :
    Fintype.card {g : Equiv.Perm I // permute g u = w} =
      if count u = count w then ∏ a, (count u a).factorial else 0 := by
  split_ifs with h
  · obtain ⟨σ,hσ⟩ := counts_eq_exists_perm h
    rw [Fintype.card_congr (transporterEquiv u w σ hσ), card_wordStabilizer]
  · have : IsEmpty {g : Equiv.Perm I // permute g u = w} :=
      ⟨fun g => h (by rw [← g.property, permute_count])⟩
    exact Fintype.card_eq_zero

/- The finite moment matrix which will be realized by actual radial Gamma
variables and root phases rather than an assumed de Finetti density. -/

-- @@ L116-117 verbatim
def momentFrame : Matrix (I → A) (I → A) ℂ := fun u w =>
  if count u = count w then (∏ a, ((count u a).factorial : ℂ)) else 0


-- @@ L119-128 verbatim
lemma momentFrame_eq_perm_sum :
    (momentFrame (I := I) (A := A)) =
      ∑ σ : Equiv.Perm I, (fun u w => if permute σ w = u then (1 : ℂ) else 0 : Matrix _ _ ℂ) := by
  apply Matrix.ext
  intro u w
  simp only [momentFrame, Finset.sum_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype,
    card_transporter]
  split_ifs with h hw <;> simp_all [eq_comm, Nat.cast_prod]

-- @@ L129-129 verbatim
end CoordinateSweeps.OrdinaryTensor


-- @@ L131-134 verbatim
namespace CoordinateSweeps.OrdinaryTensor

/- A factorial ratio is bounded by the largest factor; used to avoid
any assumed entropy/Stirling estimate in the empirical postselection measure. -/

-- @@ L135-147 verbatim
lemma factorial_step_upper (t k : ℕ) : (t+k).factorial ≤ t.factorial * (t+k)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (t+(k+1)).factorial = (t+k+1)*(t+k).factorial := by rw [← Nat.add_assoc, Nat.factorial_succ]
      _ ≤ (t+k+1)*(t.factorial*(t+k)^k) := Nat.mul_le_mul_left _ ih
      _ ≤ (t+k+1)*(t.factorial*(t+k+1)^k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      _ = t.factorial*(t+(k+1))^(k+1) := by rw [pow_succ]; ring

/- For any integral Poisson mean n, n is a mode. This elementary exact
inequality is the only numerical ingredient for the finite tensor mixture. -/

-- @@ L148-159 verbatim
lemma factorial_mode (n t : ℕ) : n^t * n.factorial ≤ n^n * t.factorial := by
  rcases le_total t n with h | h
  · have hu : n.factorial ≤ t.factorial*n^(n-t) := by
      simpa only [Nat.add_sub_of_le h] using factorial_step_upper t (n-t)
    calc
      _ ≤ n^t * (t.factorial*n^(n-t)) := Nat.mul_le_mul_left _ hu
      _ = n^n*t.factorial := by rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le h]; ring
  · have hl := Nat.factorial_mul_pow_sub_le_factorial h
    calc
      n^t*n.factorial = n^n*(n.factorial*n^(t-n)) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le h]; ring
      _ ≤ n^n*t.factorial := Nat.mul_le_mul_left _ hl


-- @@ L161-161 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]


-- @@ L163-169 verbatim
omit [DecidableEq I] in
lemma prod_word_eq_counts {R : Type*} [CommMonoid R] (r : A → R) (w : I → A) :
    (∏ i, r (w i)) = ∏ a, r a ^ count w a := by
  rw [← Finset.prod_fiberwise' Finset.univ w r]
  simp only [Finset.prod_const, ← Fintype.card_subtype, count]

/- Exact sigma decomposition of a word orbit and its transporter fibers. -/

-- @@ L170-180 verbatim
def orbitFiberEquiv (u : I → A) :
    (Σ w : {w : I → A // count w = count u}, {σ : Equiv.Perm I // permute σ u = w.val}) ≃
      Equiv.Perm I where
  toFun x := x.2.val
  invFun σ := ⟨⟨permute σ u, permute_count σ u⟩,⟨σ,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨w,hw⟩,⟨σ,hσ⟩⟩
    change permute σ u = w at hσ
    subst w
    rfl
  right_inv σ := rfl


-- @@ L182-197 verbatim
lemma orbit_card_mul_factorials (u : I → A) :
    Fintype.card {w : I → A // count w = count u} * (∏ a, (count u a).factorial) =
      (Fintype.card I).factorial := by
  have he := Fintype.card_congr (orbitFiberEquiv u)
  rw [Fintype.card_sigma, Fintype.card_perm] at he
  calc
    _ = ∑ _w : {w : I → A // count w = count u}, (∏ a, (count u a).factorial) := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = ∑ w : {w : I → A // count w = count u},
        Fintype.card {σ : Equiv.Perm I // permute σ u = w.val} := by
      apply Finset.sum_congr rfl
      intro w _
      rw [card_transporter, ite_eq_left w.property.symm]
    _ = _ := he

/- Histogram space is an actual finite set of attained occupancies. -/

-- @@ L198-199 verbatim
abbrev Histogram (I A : Type*) [Fintype I] [Fintype A] [DecidableEq A] :=
  Set.range (count (I := I) (A := A))


-- @@ L201-201 verbatim
instance : Finite (Histogram I A) := Finite.Set.finite_range _

-- @@ L202-202 verbatim
noncomputable instance : Fintype (Histogram I A) := Fintype.ofFinite _


-- @@ L204-204 verbatim
def histogram (w : I → A) : Histogram I A := ⟨count w, w, rfl⟩


-- @@ L206-209 verbatim
omit [DecidableEq I] in
lemma histogram_surjective : Function.Surjective (histogram (I := I) (A := A)) := by
  rintro ⟨h,⟨w,hw⟩⟩
  exact ⟨w,Subtype.ext hw⟩


-- @@ L211-222 verbatim
omit [DecidableEq I] in
lemma histogram_card_le : Fintype.card (Histogram I A) ≤ (Fintype.card I+1)^Fintype.card A := by
  let f : Histogram I A → (A → Fin (Fintype.card I+1)) := fun h a =>
    ⟨h.val a, by obtain ⟨w,hw⟩ := h.property; rw [← hw]; exact Nat.lt_succ_of_le (count_le w a)⟩
  have hf : Function.Injective f := by
    intro h k he
    apply Subtype.ext
    funext a
    exact congrArg Fin.val (congrFun he a)
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/- The individual multinomial type of a word, evaluated at any integer weights. -/

-- @@ L223-224 verbatim
def typeWeight (r : A → ℕ) (u : I → A) : ℕ :=
  Fintype.card {w : I → A // count w = count u} * ∏ a, r a ^ count u a


-- @@ L226-231 verbatim
lemma typeWeight_mul_factorials (r : A → ℕ) (u : I → A) :
    typeWeight r u * (∏ a, (count u a).factorial) =
      (Fintype.card I).factorial * (∏ a, r a ^ count u a) := by
  rw [typeWeight, mul_right_comm, orbit_card_mul_factorials]

/- Empirical occupancies maximize their own exact multinomial type weight. -/

-- @@ L232-250 verbatim
lemma typeWeight_empirical_max (u w : I → A) : typeWeight (count u) w ≤ typeWeight (count u) u := by
  have hu : 0 < ∏ a : A, (count u a).factorial :=
    Finset.prod_pos (fun a _ => Nat.factorial_pos _)
  have hw : 0 < ∏ a : A, (count w a).factorial :=
    Finset.prod_pos (fun a _ => Nat.factorial_pos _)
  apply Nat.le_of_mul_le_mul_right (c := ∏ a, (count w a).factorial) _ hw
  apply Nat.le_of_mul_le_mul_right (c := ∏ a, (count u a).factorial) _ hu
  calc
    _ = (Fintype.card I).factorial *
        ((∏ a, count u a ^ count w a) * (∏ a, (count u a).factorial)) := by
      rw [typeWeight_mul_factorials, mul_assoc]
    _ ≤ (Fintype.card I).factorial *
        ((∏ a, count u a ^ count u a) * (∏ a, (count w a).factorial)) := by
      apply Nat.mul_le_mul_left
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun a _ => factorial_mode (count u a) (count w a))
    _ = _ := by rw [mul_right_comm (typeWeight _ _), typeWeight_mul_factorials, mul_assoc]

/- Type weight on the finite, attained histogram space. -/

-- @@ L251-252 verbatim
def histogramWeight (r : A → ℕ) (h : Histogram I A) : ℕ :=
  Fintype.card {w : I → A // histogram w = h} * ∏ a, r a ^ h.val a


-- @@ L254-262 verbatim
lemma histogramWeight_mk (r : A → ℕ) (u : I → A) :
    histogramWeight r (histogram u) = typeWeight r u := by
  unfold histogramWeight typeWeight
  congr 1
  apply Fintype.card_congr
  exact { toFun := fun w => ⟨w.val, congrArg Subtype.val w.property⟩
          invFun := fun w => ⟨w.val, Subtype.ext w.property⟩
          left_inv := fun w => Subtype.ext rfl
          right_inv := fun w => Subtype.ext rfl }


-- @@ L264-280 verbatim
lemma sum_histogramWeight (r : A → ℕ) :
    (∑ h : Histogram I A, histogramWeight r h) = (∑ a, r a)^Fintype.card I := by
  have ht := Finset.sum_prod_piFinset (Finset.univ : Finset A) (fun _i : I => r)
  simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ] at ht
  rw [← ht, ← Fintype.sum_fiberwise (histogram (I := I) (A := A))]
  apply Finset.sum_congr rfl
  intro h _
  change Fintype.card {w : I → A // histogram w = h} * (∏ a, r a^h.val a) =
    ∑ w : {w : I → A // histogram w = h}, ∏ i, r (w.val i)
  have he (w : {w : I → A // histogram w = h}) :
      (∏ i, r (w.val i)) = ∏ a, r a ^ h.val a := by
    rw [prod_word_eq_counts, show count w.val = h.val from congrArg Subtype.val w.property]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/- Exact polynomial empirical multinomial lower bound. It includes zero
occupancies and avoids Stirling errors and asymptotic hypotheses. -/

-- @@ L281-296 verbatim
theorem empirical_type_mass (u : I → A) :
    (Fintype.card I)^Fintype.card I ≤
      (Fintype.card I+1)^Fintype.card A * typeWeight (count u) u := by
  have he := sum_histogramWeight (I := I) (count u)
  rw [sum_count] at he
  calc
    _ = ∑ h : Histogram I A, histogramWeight (count u) h := he.symm
    _ ≤ ∑ _h : Histogram I A, typeWeight (count u) u := by
      apply Finset.sum_le_sum
      intro h _
      obtain ⟨w,rfl⟩ := histogram_surjective h
      rw [histogramWeight_mk]
      exact typeWeight_empirical_max u w
    _ = Fintype.card (Histogram I A) * typeWeight (count u) u := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (histogram_card_le (I := I) (A := A))

-- @@ L297-297 verbatim
end CoordinateSweeps.OrdinaryTensor


-- @@ L299-299 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L300-300 verbatim
open AddChar

-- @@ L301-304 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

/- Finite independent root phases. The modulus is strictly larger than
any occupancy, so it distinguishes every histogram without an analytic limit. -/

-- @@ L305-305 verbatim
abbrev PhaseSpace (I A : Type*) [Fintype I] := A → ZMod (Fintype.card I+1)


-- @@ L307-308 verbatim
def wordPhase (t : PhaseSpace I A) (w : I → A) : ℂ :=
  ∏ a, ZMod.stdAddChar (t a * (count w a : ZMod (Fintype.card I+1)))


-- @@ L310-318 verbatim
omit [DecidableEq I] in
lemma wordPhase_eq_prod (t : PhaseSpace I A) (w : I → A) :
    wordPhase t w = ∏ i, ZMod.stdAddChar (t (w i)) := by
  rw [prod_word_eq_counts (fun a : A => ZMod.stdAddChar (t a)) w]
  unfold wordPhase
  apply Finset.prod_congr rfl
  intro a _
  simpa only [nsmul_eq_mul, mul_comm] using
    (map_nsmul_eq_pow (ZMod.stdAddChar (N := Fintype.card I+1)) (count w a) (t a))


-- @@ L320-345 verbatim
omit [DecidableEq I] in
lemma phase_conjugate_sum (c d : A → ℕ) (hc : ∀ a, c a ≤ Fintype.card I)
    (hd : ∀ a, d a ≤ Fintype.card I) :
    (∑ t : PhaseSpace I A,
      (∏ a, ZMod.stdAddChar (t a * (c a : ZMod (Fintype.card I+1)))) *
        star (∏ a, ZMod.stdAddChar (t a * (d a : ZMod (Fintype.card I+1))))) =
      if c = d then (Fintype.card (PhaseSpace I A) : ℂ) else 0 := by
  simp only [star_prod]
  simp_rw [← Finset.prod_mul_distrib, Complex.star_def, ← AddChar.map_neg_eq_conj,
    ← map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  have hf := Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod (Fintype.card I+1)))
    (fun a x => ZMod.stdAddChar (x * ((c a : ZMod (Fintype.card I+1)) - (d a : ZMod (Fintype.card I+1)))))
  simp only [Fintype.piFinset_univ] at hf
  rw [hf]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _)]
  have he (a : A) : (c a : ZMod (Fintype.card I+1)) - (d a : ZMod (Fintype.card I+1)) = 0 ↔ c a = d a := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hc a)), Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hd a))]
  simp_rw [he]
  by_cases h : c = d
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    obtain ⟨a,ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

/- Exact finite orthogonality of different empirical type phases. -/

-- @@ L346-352 verbatim
omit [DecidableEq I] in
lemma wordPhase_orthogonality (u w : I → A) :
    (∑ t : PhaseSpace I A, wordPhase t u * star (wordPhase t w)) =
      if count u = count w then (Fintype.card (PhaseSpace I A) : ℂ) else 0 :=
  phase_conjugate_sum (count u) (count w) (count_le u) (count_le w)

/- Every root-phase component has unit modulus. -/

-- @@ L353-360 verbatim
omit [DecidableEq I] in
lemma wordPhase_star_mul (t : PhaseSpace I A) (w : I → A) :
    wordPhase t w * star (wordPhase t w) = 1 := by
  simp only [wordPhase, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← map_add_eq_mul]
  simp

-- @@ L361-361 verbatim
end CoordinateSweeps.OrdinaryTensor


-- @@ L363-363 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L364-364 verbatim
open AddChar

-- @@ L365-365 verbatim
open scoped ComplexOrder

-- @@ L366-366 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]


-- @@ L368-368 verbatim
def tensorVector (z : A → ℂ) (w : I → A) : ℂ := ∏ i, z (w i)

-- @@ L369-369 verbatim
def outer {J : Type*} (v : J → ℂ) : Matrix J J ℂ := Matrix.vecMulVec v (star v)


-- @@ L371-372 verbatim
lemma outer_posSemidef {J : Type*} [Finite J] (v : J → ℂ) : (outer v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v


-- @@ L374-377 verbatim
lemma outer_apply {J : Type*} (v : J → ℂ) (i j : J) : outer v i j = v i * star (v j) := rfl

/- Empirical-site amplitudes. Their exact squared norm is one when there is
at least one slot. Zero-count letters are allowed and have zero amplitude. -/

-- @@ L378-379 verbatim
def empiricalVector (h : Histogram I A) (t : PhaseSpace I A) (a : A) : ℂ :=
  (Real.sqrt ((h.val a : ℝ)/Fintype.card I) : ℂ) * ZMod.stdAddChar (t a)


-- @@ L381-382 verbatim
def amplitude (h : Histogram I A) (w : I → A) : ℝ :=
  ∏ i, Real.sqrt ((h.val (w i) : ℝ)/Fintype.card I)


-- @@ L384-388 verbatim
omit [DecidableEq I] in
lemma char_star_mul (t : ZMod (Fintype.card I+1)) :
    ZMod.stdAddChar t * star (ZMod.stdAddChar t) = 1 := by
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← map_add_eq_mul]
  simp


-- @@ L390-401 verbatim
omit [DecidableEq I] in
lemma empiricalVector_square (h : Histogram I A) (t : PhaseSpace I A) (a : A) :
    empiricalVector h t a * star (empiricalVector h t a) =
      (((h.val a : ℝ)/Fintype.card I : ℝ) : ℂ) := by
  unfold empiricalVector
  simp only [star_mul, RCLike.star_def, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt ((h.val a : ℝ)/Fintype.card I) : ℂ)^2 *
        (ZMod.stdAddChar (t a) * star (ZMod.stdAddChar (t a))) := by
      simp only [Complex.star_def]; ring
    _ = _ := by
      rw [char_star_mul, mul_one, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]


-- @@ L403-410 verbatim
omit [DecidableEq I] in
lemma empiricalVector_unit (hn : 0 < Fintype.card I) (h : Histogram I A) (t : PhaseSpace I A) :
    (∑ a, empiricalVector h t a * star (empiricalVector h t a)) = 1 := by
  simp_rw [empiricalVector_square]
  rw [← Complex.ofReal_sum, ← Finset.sum_div]
  obtain ⟨w,hw⟩ := h.property
  rw [← hw, ← Nat.cast_sum, sum_count, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  rfl


-- @@ L412-417 verbatim
omit [DecidableEq I] in
lemma amplitude_eq_counts (h : Histogram I A) (w : I → A) :
    amplitude h w = ∏ a, (Real.sqrt ((h.val a : ℝ)/Fintype.card I)) ^ count w a :=
by
  unfold amplitude
  exact prod_word_eq_counts (fun a => Real.sqrt ((h.val a : ℝ)/Fintype.card I)) w


-- @@ L419-421 verbatim
omit [DecidableEq I] in
lemma amplitude_congr (h : Histogram I A) {u w : I → A} (he : count u = count w) :
    amplitude h u = amplitude h w := by rw [amplitude_eq_counts, amplitude_eq_counts, he]


-- @@ L423-427 verbatim
omit [DecidableEq I] in
lemma tensorVector_empirical (h : Histogram I A) (t : PhaseSpace I A) (w : I → A) :
    tensorVector (empiricalVector h t) w = (amplitude h w : ℂ) * wordPhase t w := by
  rw [wordPhase_eq_prod]
  simp only [tensorVector, empiricalVector, amplitude, Complex.ofReal_prod, Finset.prod_mul_distrib]


-- @@ L429-438 verbatim
omit [DecidableEq I] in
lemma amplitude_square (h : Histogram I A) (w : I → A) :
    amplitude h w ^ 2 = (∏ a, (h.val a : ℝ) ^ count w a) /
      (Fintype.card I : ℝ) ^ Fintype.card I := by
  rw [amplitude_eq_counts, ← Finset.prod_pow]
  simp_rw [← pow_mul, mul_comm _ 2, pow_mul, Real.sq_sqrt (by positivity :
    0 ≤ (h.val _ : ℝ)/Fintype.card I), div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_count]

/- Finite phase average of actual pure product states. -/

-- @@ L439-441 verbatim
def phaseFrame (h : Histogram I A) : Matrix (I → A) (I → A) ℂ :=
  (Fintype.card (PhaseSpace I A) : ℂ)⁻¹ •
    ∑ t : PhaseSpace I A, outer (tensorVector (empiricalVector h t))


-- @@ L443-446 verbatim
omit [DecidableEq I] in
lemma phaseSpace_card_pos : 0 < Fintype.card (PhaseSpace I A) := by
  rw [Fintype.card_fun, ZMod.card]
  positivity


-- @@ L448-452 verbatim
omit [DecidableEq I] in
lemma phaseFrame_posSemidef (h : Histogram I A) : (phaseFrame h).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ (fun t _ => outer_posSemidef _)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)


-- @@ L454-470 verbatim
omit [DecidableEq I] in
lemma phaseFrame_entry (h : Histogram I A) (u w : I → A) :
    phaseFrame h u w = if count u = count w then ((amplitude h u : ℂ)^2) else 0 := by
  simp only [phaseFrame, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, outer_apply,
    tensorVector_empirical, star_mul, RCLike.star_def, Complex.conj_ofReal]
  have he (t : PhaseSpace I A) :
      ((amplitude h u : ℂ)*wordPhase t u) *
        (star (wordPhase t w)*(amplitude h w : ℂ)) =
      ((amplitude h u : ℂ)*(amplitude h w : ℂ)) * (wordPhase t u * star (wordPhase t w)) := by ring
  simp only [← Complex.star_def]
  simp_rw [he]
  rw [← Finset.mul_sum, wordPhase_orthogonality]
  split_ifs with hc
  · rw [amplitude_congr h hc]
    have hn : (Fintype.card (PhaseSpace I A) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt phaseSpace_card_pos)
    field_simp
  · simp

-- @@ L471-471 verbatim
end CoordinateSweeps.OrdinaryTensor


-- @@ L473-473 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L474-474 verbatim
open scoped ComplexOrder

-- @@ L475-475 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]


-- @@ L477-477 verbatim
def orbitSize (h : Histogram I A) : ℕ := Fintype.card {w : I → A // histogram w = h}

-- @@ L478-478 verbatim
def representative (h : Histogram I A) : I → A := Classical.choose h.property


-- @@ L480-482 verbatim
omit [DecidableEq I] in
lemma count_representative (h : Histogram I A) : count (representative h) = h.val :=
  Classical.choose_spec h.property

-- @@ L483-485 verbatim
omit [DecidableEq I] in
lemma histogram_representative (h : Histogram I A) : histogram (representative h) = h :=
  Subtype.ext (count_representative h)


-- @@ L487-489 verbatim
lemma orbitSize_pos (h : Histogram I A) : 0 < orbitSize h := by
  have : Nonempty {w : I → A // histogram w = h} := ⟨⟨representative h, histogram_representative h⟩⟩
  exact Fintype.card_pos


-- @@ L491-494 verbatim
lemma orbitSize_mk (w : I → A) :
    orbitSize (histogram w) = Fintype.card {u : I → A // count u = count w} := by
  have he := histogramWeight_mk (fun _ : A => 1) w
  simpa only [histogramWeight,typeWeight,one_pow,Finset.prod_const_one,mul_one,orbitSize] using he


-- @@ L496-497 verbatim
def block (h : Histogram I A) : Matrix (I → A) (I → A) ℂ :=
  outer (fun w => if histogram w = h then 1 else 0)


-- @@ L499-500 verbatim
omit [DecidableEq I] in
lemma block_posSemidef (h : Histogram I A) : (block h).PosSemidef := outer_posSemidef _


-- @@ L502-509 verbatim
omit [DecidableEq I] in
lemma block_entry (h : Histogram I A) (u w : I → A) :
    block h u w = if histogram u = h ∧ histogram w = h then (1 : ℂ) else 0 := by
  simp only [block,outer_apply]
  split_ifs <;> simp_all

/- Orthogonal projection onto vectors invariant under ordinary slot
permutations, implemented by their exact histogram blocks. -/

-- @@ L510-511 verbatim
def symProjector : Matrix (I → A) (I → A) ℂ :=
  ∑ h : Histogram I A, (orbitSize h : ℂ)⁻¹ • block h


-- @@ L513-516 verbatim
lemma symProjector_posSemidef : (symProjector (I := I) (A := A)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro h _
  exact (block_posSemidef h).smul (inv_nonneg.mpr (Nat.cast_nonneg _))


-- @@ L518-526 verbatim
lemma symProjector_entry (u w : I → A) : symProjector u w =
    if histogram u = histogram w then (orbitSize (histogram u) : ℂ)⁻¹ else 0 := by
  simp only [symProjector, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, block_entry]
  rw [Finset.sum_eq_single (histogram u)]
  · by_cases h : histogram u = histogram w <;> simp [h,eq_comm]
  · intro h _ hne
    have he : histogram u ≠ h := Ne.symm hne
    simp [he]
  · simp


-- @@ L528-547 verbatim
lemma symProjector_mulVec_of_constant (v : (I → A) → ℂ)
    (hv : ∀ u w, count u = count w → v u = v w) :
    (symProjector (I := I) (A := A)).mulVec v = v := by
  ext u
  simp only [Matrix.mulVec, dotProduct, symProjector_entry, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have he (w : I → A) (hw : w ∈ Finset.univ.filter (fun w => histogram u = histogram w)) : v w = v u :=
    (hv u w (congrArg Subtype.val (Finset.mem_filter.mp hw).2)).symm
  rw [Finset.sum_congr rfl (fun w hw => congrArg ((orbitSize (histogram u) : ℂ)⁻¹ * ·) (he w hw))]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  have hc : Fintype.card {w : I → A // histogram u = histogram w} = orbitSize (histogram u) := by
    unfold orbitSize
    apply Fintype.card_congr
    exact { toFun := fun w => ⟨w.val,w.property.symm⟩
            invFun := fun w => ⟨w.val,w.property.symm⟩
            left_inv := fun w => Subtype.ext rfl
            right_inv := fun w => Subtype.ext rfl }
  rw [hc]
  have ho : (orbitSize (histogram u) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (orbitSize_pos _))
  field_simp


-- @@ L549-554 verbatim
lemma symProjector_idempotent : (symProjector (I := I) (A := A)) * symProjector = symProjector := by
  ext u w
  have he := symProjector_mulVec_of_constant (fun v : I → A => symProjector v w) (fun v v' h => by
    have hh : histogram v = histogram v' := Subtype.ext h
    simp only [symProjector_entry, hh])
  exact congrFun he u


-- @@ L556-556 verbatim
def histogramAmplitude (h k : Histogram I A) : ℝ := amplitude h (representative k)


-- @@ L558-562 verbatim
omit [DecidableEq I] in
lemma histogramAmplitude_mk (h : Histogram I A) (w : I → A) :
    histogramAmplitude h (histogram w) = amplitude h w := by
  apply amplitude_congr
  exact count_representative _


-- @@ L564-581 verbatim
omit [DecidableEq I] in
lemma phaseFrame_blocks (h : Histogram I A) :
    phaseFrame h = ∑ k : Histogram I A, ((histogramAmplitude h k : ℂ)^2) • block k := by
  ext u w
  rw [phaseFrame_entry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, block_entry]
  rw [Finset.sum_eq_single (histogram u)]
  · have he : (count u = count w) ↔ histogram w = histogram u :=
      ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩
    rw [histogramAmplitude_mk]
    simp only [true_and, he]
    split_ifs <;> simp
  · intro k _ hk
    have he : histogram u ≠ k := Ne.symm hk
    simp [he]
  · simp

/- Polynomial inverse-orbit bound for the **actual** empirical phase frame. -/

-- @@ L582-598 verbatim
lemma inverse_orbit_le_empirical (hn : 0 < Fintype.card I) (h : Histogram I A) :
    (orbitSize h : ℝ)⁻¹ ≤ ((Fintype.card I+1)^Fintype.card A : ℕ) * histogramAmplitude h h ^ 2 := by
  obtain ⟨u,rfl⟩ := histogram_surjective h
  rw [histogramAmplitude_mk, orbitSize_mk, amplitude_square]
  have ho : (0 : ℝ) < Fintype.card {w : I → A // count w = count u} := by
    simpa only [← orbitSize_mk] using (Nat.cast_pos.mpr (orbitSize_pos (histogram u)) :
      (0 : ℝ) < orbitSize (histogram u))
  have hn' : (0 : ℝ) < (Fintype.card I : ℝ)^Fintype.card I := pow_pos (Nat.cast_pos.mpr hn) _
  have hm := empirical_type_mass u
  have hr : (Fintype.card I : ℝ)^Fintype.card I ≤
      (((Fintype.card I+1)^Fintype.card A : ℕ) : ℝ) *
        ((Fintype.card {w : I → A // count w = count u} : ℝ) * ∏ a, (count u a : ℝ)^count u a) := by
    exact_mod_cast hm
  change _ ≤ (((Fintype.card I+1)^Fintype.card A : ℕ) : ℝ) *
    ((∏ a, (count u a : ℝ)^count u a) / (Fintype.card I : ℝ)^Fintype.card I)
  rw [← mul_div_assoc, le_div_iff₀ hn', inv_mul_eq_div, div_le_iff₀ ho]
  nlinarith [hr]

-- @@ L599-599 verbatim
end CoordinateSweeps.OrdinaryTensor


-- @@ L601-601 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L602-602 verbatim
open scoped ComplexOrder

-- @@ L603-603 verbatim
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]


-- @@ L605-615 verbatim
omit [DecidableEq I] in
lemma phaseFrame_sum_blocks :
    (∑ h : Histogram I A, phaseFrame h) = ∑ k : Histogram I A,
      (∑ h : Histogram I A, (histogramAmplitude h k : ℂ)^2) • block k := by
  simp_rw [phaseFrame_blocks]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_smul.symm

/- Constructive finite postselection before normalizing the histogram sum. -/

-- @@ L616-641 verbatim
theorem phaseFrame_sum_domination (hn : 0 < Fintype.card I) :
    ((((Fintype.card I+1)^Fintype.card A : ℕ) : ℂ) •
      (∑ h : Histogram I A, phaseFrame h) - symProjector).PosSemidef := by
  let P : ℕ := (Fintype.card I+1)^Fintype.card A
  have hc (k : Histogram I A) :
      0 ≤ (P : ℝ) * (∑ h : Histogram I A, histogramAmplitude h k ^ 2) - (orbitSize k : ℝ)⁻¹ := by
    apply sub_nonneg.mpr
    apply (inverse_orbit_le_empirical hn k).trans
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun h _ => sq_nonneg (histogramAmplitude h k)) (Finset.mem_univ k))
      (Nat.cast_nonneg P)
  have he : (P : ℂ) • (∑ h : Histogram I A, phaseFrame h) - symProjector =
      ∑ k : Histogram I A,
        (((P : ℝ) * (∑ h : Histogram I A, histogramAmplitude h k ^ 2) -
          (orbitSize k : ℝ)⁻¹ : ℝ) : ℂ) • block k := by
    rw [phaseFrame_sum_blocks, symProjector, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    rfl
  rw [show (((Fintype.card I+1)^Fintype.card A : ℕ) : ℂ) = (P : ℂ) from rfl, he]
  apply Matrix.posSemidef_sum
  intro k _
  exact (block_posSemidef k).smul (by exact_mod_cast hc k)


-- @@ L643-646 verbatim
instance [Nonempty A] : Nonempty (Histogram I A) := ⟨histogram (fun _ => Classical.arbitrary A)⟩

/- Literal finite average of empirical pure product tensors, grouped first
by histogram and then by independent roots. -/

-- @@ L647-648 verbatim
def finiteMixture : Matrix (I → A) (I → A) ℂ :=
  (Fintype.card (Histogram I A) : ℂ)⁻¹ • ∑ h : Histogram I A, phaseFrame h


-- @@ L650-657 verbatim
omit [DecidableEq I] in
lemma finiteMixture_posSemidef : (finiteMixture (I := I) (A := A)).PosSemidef := by
  exact (Matrix.posSemidef_sum _ (fun h _ => phaseFrame_posSemidef h)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/- Finite, normalized tensor postselection with explicit polynomial overhead.
Every product in finiteMixture comes from squared-norm-one empirical vectors;
there is no de Finetti theorem or independent density assumption. -/

-- @@ L658-681 verbatim
theorem finite_postselection [Nonempty A] (hn : 0 < Fintype.card I) :
    ((((Fintype.card I+1)^(2*Fintype.card A) : ℕ) : ℂ) •
      (finiteMixture (I := I) (A := A)) - symProjector).PosSemidef := by
  let P : ℕ := (Fintype.card I+1)^Fintype.card A
  let H : ℕ := Fintype.card (Histogram I A)
  have hH : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  have h := phaseFrame_sum_domination (I := I) (A := A) hn
  have he : ((P*H : ℕ) : ℂ) • (finiteMixture (I := I) (A := A)) =
      (P : ℂ) • ∑ h : Histogram I A, phaseFrame h := by
    unfold finiteMixture
    rw [smul_smul, Nat.cast_mul]
    congr 1
    change (P : ℂ)*(H : ℂ)*(H : ℂ)⁻¹ = (P : ℂ)
    field_simp
  have hm : (P*H : ℕ) ≤ (Fintype.card I+1)^(2*Fintype.card A) := by
    have hle := Nat.mul_le_mul_left P (histogram_card_le (I := I) (A := A))
    simpa only [P,H,← pow_two,← pow_mul, mul_comm 2] using hle
  have hp : (0 : ℂ) ≤ (((Fintype.card I+1)^(2*Fintype.card A) : ℕ) : ℂ) - ((P*H : ℕ) : ℂ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  have hh := (finiteMixture_posSemidef (I := I) (A := A)).smul hp
  have hf := hh.add h
  rw [← he] at hf
  convert hf using 1
  module


-- @@ L683-692 verbatim
omit [DecidableEq A] in
lemma outer_tensorVector_trace (z : A → ℂ) :
    Matrix.trace (outer (tensorVector (I := I) z)) =
      (∑ a, z a * star (z a))^Fintype.card I := by
  have ht := Finset.sum_prod_piFinset (Finset.univ : Finset A)
    (fun _i : I => fun a : A => z a * star (z a))
  simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ] at ht
  change (∑ w : I → A, tensorVector z w * star (tensorVector z w)) = _
  simp only [tensorVector,star_prod,← Finset.prod_mul_distrib]
  exact ht


-- @@ L694-699 verbatim
lemma phaseFrame_trace [Nonempty A] (hn : 0 < Fintype.card I) (h : Histogram I A) :
    Matrix.trace (phaseFrame h) = 1 := by
  rw [phaseFrame, Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [outer_tensorVector_trace, empiricalVector_unit hn, one_pow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt phaseSpace_card_pos))


-- @@ L701-706 verbatim
lemma finiteMixture_trace [Nonempty A] (hn : 0 < Fintype.card I) :
    Matrix.trace (finiteMixture (I := I) (A := A)) = 1 := by
  rw [finiteMixture, Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [phaseFrame_trace hn]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos))

-- @@ L707-710 verbatim
end CoordinateSweeps.OrdinaryTensor

/- Positive-operator inequalities needed for the actual purification proof
of signed tensor density domination (05:eq13), not standalone main results. -/

-- @@ L711-711 verbatim
noncomputable section

-- @@ L712-712 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L713-713 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L714-714 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L715-715 verbatim
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]


-- @@ L717-722 verbatim
omit [DecidableEq A] in
lemma outer_trace_nonneg (v : (I → A) → ℂ) : 0 ≤ Matrix.trace (outer v) := by
  exact (outer_posSemidef v).trace_nonneg

/- The ordinary finite postselection theorem applied to an actual invariant
purification vector, rather than an assumed projection inequality. -/

-- @@ L723-743 verbatim
theorem invariant_vector_postselection [Nonempty A] (hn : 0 < Fintype.card I)
    (v : (I → A) → ℂ) (hv : ∀ σ : Equiv.Perm I, ∀ w, v (permute σ w) = v w) :
    ((Matrix.trace (outer v) * ((Fintype.card I+1 : ℕ) : ℂ)^(2*Fintype.card A)) •
      finiteMixture - outer v).PosSemidef := by
  have hfix : symProjector.mulVec v = v := by
    apply symProjector_mulVec_of_constant
    intro u w he
    obtain ⟨σ,hσ⟩ := counts_eq_exists_perm he
    rw [← hσ,hv]
  have hPA : symProjector * outer v = outer v := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k, symProjector i k * (v k * star (v j))) = v i * star (v j)
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    exact congrArg (fun z : ℂ => z*star (v j)) (congrFun hfix i)
  have h1 := PositiveTensor.projection_trace_domination (outer v) symProjector
    (outer_posSemidef v) symProjector_posSemidef.isHermitian symProjector_idempotent hPA
  have h2 := (finite_postselection (I := I) (A := A) hn).smul (outer_trace_nonneg v)
  have hh := h2.add h1
  simpa only [smul_sub,smul_smul,sub_add_sub_cancel,Nat.cast_pow] using hh

-- @@ L744-744 verbatim
end CoordinateSweeps.OrdinaryTensor

-- @@ L745-745 verbatim
namespace CoordinateSweeps.OrdinaryTensor

-- @@ L746-746 verbatim
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]


-- @@ L748-749 verbatim
def rawMixture : Matrix (I → A) (I → A) ℂ :=
  ∑ h : Histogram I A, ∑ t : PhaseSpace I A, outer (tensorVector (empiricalVector h t))

-- @@ L750-752 verbatim
omit [DecidableEq I] in
lemma rawMixture_posSemidef : (rawMixture (I := I) (A := A)).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun h _ => Matrix.posSemidef_sum _ (fun t _ => outer_posSemidef _))

-- @@ L753-765 verbatim
omit [DecidableEq I] in
lemma rawMixture_eq : rawMixture (I := I) (A := A) =
    ((Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)) • finiteMixture := by
  have hP : (Fintype.card (PhaseSpace I A) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr phaseSpace_card_pos.ne'
  by_cases hH : (Fintype.card (Histogram I A) : ℂ) = 0
  · have he : IsEmpty (Histogram I A) := Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hH)
    let := he
    simp [rawMixture,finiteMixture]
  · unfold finiteMixture phaseFrame rawMixture
    rw [smul_smul,← Finset.smul_sum,smul_smul]
    have hc : ((Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)) *
        (Fintype.card (Histogram I A) : ℂ)⁻¹ * (Fintype.card (PhaseSpace I A) : ℂ)⁻¹ = 1 := by field_simp
    rw [hc,one_smul]

-- @@ L766-774 verbatim
omit [DecidableEq I] in
lemma rawMixture_domination [Nonempty A] :
    (rawMixture (I := I) (A := A) - finiteMixture).PosSemidef := by
  rw [rawMixture_eq]
  have hH : (1 : ℂ) ≤ (Fintype.card (Histogram I A) : ℂ) := by exact_mod_cast Fintype.card_pos
  have hP : (1 : ℂ) ≤ (Fintype.card (PhaseSpace I A) : ℂ) := by exact_mod_cast phaseSpace_card_pos
  have hp : (0 : ℂ) ≤ (Fintype.card (Histogram I A) : ℂ)*(Fintype.card (PhaseSpace I A) : ℂ)-1 :=
    sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hH hP)
  simpa only [sub_smul,one_smul] using finiteMixture_posSemidef.smul hp

-- @@ L775-775 verbatim
end CoordinateSweeps.OrdinaryTensor

-- @@ L776-776 verbatim
end

-- @@ L777-777 verbatim
end

-- @@ L778-778 verbatim
end

-- @@ L779-779 verbatim
open scoped Matrix.Norms.L2Operator


-- @@ L781-781 verbatim
end OAI
