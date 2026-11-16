import Mathlib
import Submission.Fondamenta
import Submission.Trasferimento
import Submission.TetraedroStadio2


-- @@ L6-14 verbatim
/-!
DODECAEDRO — TESTIMONE (5,3), port a modulo (18 lug 2026, notte).

Sorgente: `teoremi/Platonici_DodecaedroCompleto.lean` (sol, fascicoli 6-8,
CERTIFICATO 177/177). Le definizioni condivise vengono da `Fondamenta`,
i lemmi di trasferimento dal modulo `Trasferimento`, `E3`/`norma_toLp` dal
modulo del tetraedro. Rinomine anti-collisione: suffisso `D` su F₀, c0-c3,
d1, d2, segnoX/Y/Z; `cosferico_extremePoints_dodeca`.
-/


-- @@ L16-16 verbatim
open Set Metric FiniteConvexPolytope

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
set_option linter.unreachableTactic false

-- @@ L22-22 verbatim
set_option linter.unnecessarySeqFocus false

-- @@ L23-23 verbatim
set_option linter.unusedTactic false

-- @@ L24-24 verbatim
set_option linter.unusedSimpArgs false

-- @@ L25-25 verbatim
set_option linter.unusedSectionVars false


-- @@ L27-27 verbatim
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]


-- @@ L29-29 verbatim
/-! ## Aritmetica aurea e coordinate -/



-- @@ L32-32 verbatim
local notation "φ" => Real.goldenRatio


-- @@ L34-36 expanded
theorem golden_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 :=
  by
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]


-- @@ L38-40 expanded
theorem golden_norm_sq : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio ^ 2 = 3 :=
  by
  rw [golden_inv, Real.goldenRatio_sq]
  nlinarith [Real.goldenRatio_sq]


-- @@ L42-47 expanded
theorem golden_norm_sq_nf : (2 / (1 + Real.sqrt 5)) ^ 2 + (Real.goldenRatio + 1) = 3 :=
  by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith


-- @@ L49-54 expanded
theorem golden_inv_nf : 2 / (1 + Real.sqrt 5) = Real.goldenRatio - 1 :=
  by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 5 ≠ 0 := by positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith


-- @@ L56-58 expanded
theorem golden_sqrt_five : Real.sqrt 5 = 2 * Real.goldenRatio - 1 :=
  by
  rw [Real.goldenRatio]
  ring


-- @@ L60-61 verbatim
theorem golden_den_self : (1 + Real.sqrt 5) / (1 + Real.sqrt 5) = 1 := by
  field_simp


-- @@ L63-63 expanded
theorem golden_inv_pos : 0 < Real.goldenRatio⁻¹ :=
  inv_pos.mpr Real.goldenRatio_pos


-- @@ L65-65 verbatim
/-! ## I venti vertici -/


-- @@ L67-67 verbatim
def a0 : E3 := WithLp.toLp 2 ![-1, -1, -1]

-- @@ L68-68 verbatim
def a1 : E3 := WithLp.toLp 2 ![-1, -1,  1]

-- @@ L69-69 verbatim
def a2 : E3 := WithLp.toLp 2 ![-1,  1, -1]

-- @@ L70-70 verbatim
def a3 : E3 := WithLp.toLp 2 ![-1,  1,  1]

-- @@ L71-71 verbatim
def a4 : E3 := WithLp.toLp 2 ![ 1, -1, -1]

-- @@ L72-72 verbatim
def a5 : E3 := WithLp.toLp 2 ![ 1, -1,  1]

-- @@ L73-73 verbatim
def a6 : E3 := WithLp.toLp 2 ![ 1,  1, -1]

-- @@ L74-74 verbatim
def a7 : E3 := WithLp.toLp 2 ![ 1,  1,  1]


-- @@ L76-76 expanded
def b0 : E3 :=
  WithLp.toLp 2 ![0, -Real.goldenRatio⁻¹, -Real.goldenRatio]


-- @@ L77-77 expanded
def b1 : E3 :=
  WithLp.toLp 2 ![0, -Real.goldenRatio⁻¹, Real.goldenRatio]


-- @@ L78-78 expanded
def b2 : E3 :=
  WithLp.toLp 2 ![0, Real.goldenRatio⁻¹, -Real.goldenRatio]


-- @@ L79-79 expanded
def b3 : E3 :=
  WithLp.toLp 2 ![0, Real.goldenRatio⁻¹, Real.goldenRatio]


-- @@ L81-81 expanded
def c0D : E3 :=
  WithLp.toLp 2 ![-Real.goldenRatio, 0, -Real.goldenRatio⁻¹]


-- @@ L82-82 expanded
def c1D : E3 :=
  WithLp.toLp 2 ![-Real.goldenRatio, 0, Real.goldenRatio⁻¹]


-- @@ L83-83 expanded
def c2D : E3 :=
  WithLp.toLp 2 ![Real.goldenRatio, 0, -Real.goldenRatio⁻¹]


-- @@ L84-84 expanded
def c3D : E3 :=
  WithLp.toLp 2 ![Real.goldenRatio, 0, Real.goldenRatio⁻¹]


-- @@ L86-86 expanded
def d0 : E3 :=
  WithLp.toLp 2 ![-Real.goldenRatio⁻¹, -Real.goldenRatio, 0]


-- @@ L87-87 expanded
def d1D : E3 :=
  WithLp.toLp 2 ![-Real.goldenRatio⁻¹, Real.goldenRatio, 0]


-- @@ L88-88 expanded
def d2D : E3 :=
  WithLp.toLp 2 ![Real.goldenRatio⁻¹, -Real.goldenRatio, 0]


-- @@ L89-89 expanded
def d3 : E3 :=
  WithLp.toLp 2 ![Real.goldenRatio⁻¹, Real.goldenRatio, 0]


-- @@ L91-94 verbatim
open Classical in
def verticiDodeca : Finset E3 :=
  {a0, a1, a2, a3, a4, a5, a6, a7,
   b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3}


-- @@ L96-106 verbatim
theorem norm_verticiDodeca : ∀ v ∈ verticiDodeca, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals rw [norma_toLp]
  all_goals congr 1
  all_goals norm_num [golden_inv, Real.goldenRatio_sq] <;>
    nlinarith [golden_norm_sq_nf]


-- @@ L108-108 verbatim
/-! Il lemma cosferico usato anche per il tetraedro. -/


-- @@ L110-122 verbatim
theorem cosferico_extremePoints_dodeca {B : Type*} [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [Nontrivial B]
    (x : B) (r : ℝ) (V : Set B) (hV : V ⊆ sphere x r) :
    (convexHull ℝ V).extremePoints ℝ = V := by
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ V ⊆ closedBall x r :=
    convexHull_min (hV.trans sphere_subset_closedBall) (convex_closedBall x r)
  intro v hv
  have hsfera : v ∈ (closedBall x r).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hV hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ V hv, hsfera⟩


-- @@ L124-132 verbatim
def dodecaedro : FiniteConvexPolytope E3 where
  vertices := verticiDodeca
  nonempty := ⟨a0, by simp [verticiDodeca]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiDodeca : Set E3) ⊆ sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_verticiDodeca v (by exact_mod_cast hv)
    exact (cosferico_extremePoints_dodeca 0 (Real.sqrt 3) _ hV).symm


-- @@ L134-134 verbatim
/-! ## Dimensione affine tre -/


-- @@ L136-136 verbatim
def cubeBasisPoints : Fin 4 → E3 := ![a7, a4, a2, a1]


-- @@ L138-161 verbatim
theorem cubeBasisPoints_affineIndependent :
    AffineIndependent ℝ cubeBasisPoints := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [cubeBasisPoints, a7, a4, a2, a1, Fin.sum_univ_four] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  change u 0 * 1 + u 1 * 1 + u 2 * (-1) + u 3 * (-1) =
    v 0 * 1 + v 1 * 1 + v 2 * (-1) + v 3 * (-1) at h0
  change u 0 * 1 + u 1 * (-1) + u 2 * 1 + u 3 * (-1) =
    v 0 * 1 + v 1 * (-1) + v 2 * 1 + v 3 * (-1) at h1
  change u 0 * 1 + u 1 * (-1) + u 2 * (-1) + u 3 * 1 =
    v 0 * 1 + v 1 * (-1) + v 2 * (-1) + v 3 * 1 at h2
  rw [Fin.sum_univ_four] at hu hv
  have e0 : u 0 = v 0 := by linarith
  have e1 : u 1 = v 1 := by linarith
  have e2 : u 2 = v 2 := by linarith
  have e3 : u 3 = v 3 := by linarith
  fin_cases i <;> assumption


-- @@ L163-166 verbatim
theorem range_cubeBasisPoints_subset :
    Set.range cubeBasisPoints ⊆ (verticiDodeca : Set E3) := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;> simp [cubeBasisPoints, verticiDodeca]


-- @@ L168-178 verbatim
theorem dodecaedro_finrank :
    Module.finrank ℝ (vectorSpan ℝ (dodecaedro.vertices : Set E3)) = 3 := by
  change Module.finrank ℝ (vectorSpan ℝ (verticiDodeca : Set E3)) = 3
  have htop : vectorSpan ℝ (Set.range cubeBasisPoints) = ⊤ :=
    cubeBasisPoints_affineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp)
  have hspan : vectorSpan ℝ (verticiDodeca : Set E3) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact vectorSpan_mono ℝ range_cubeBasisPoints_subset
  rw [hspan]
  simp


-- @@ L180-180 verbatim
/-! ## La faccia scelta e il suo piano di supporto -/


-- @@ L182-182 verbatim
def x0 : E3 := a7

-- @@ L183-183 verbatim
def x1 : E3 := b3

-- @@ L184-184 verbatim
def x2 : E3 := b1

-- @@ L185-185 verbatim
def x3 : E3 := a5

-- @@ L186-186 verbatim
def x4 : E3 := c3D


-- @@ L188-189 verbatim
/-- I vertici sono gia' ordinati nel verso della rotazione costruita sotto. -/
def faceCycle : Fin 5 → E3 := ![x0, x1, x2, x3, x4]


-- @@ L191-191 verbatim
@[simp] theorem faceCycle_zero : faceCycle 0 = x0 := rfl

-- @@ L192-192 verbatim
@[simp] theorem faceCycle_one : faceCycle 1 = x1 := rfl

-- @@ L193-193 verbatim
@[simp] theorem faceCycle_two : faceCycle 2 = x2 := rfl

-- @@ L194-194 verbatim
@[simp] theorem faceCycle_three : faceCycle 3 = x3 := rfl

-- @@ L195-195 verbatim
@[simp] theorem faceCycle_four : faceCycle 4 = x4 := rfl


-- @@ L197-197 verbatim
def F₀D : Set E3 := convexHull ℝ (Set.range faceCycle)


-- @@ L199-200 expanded
/-- La lunghezza del lato nel modello di raggio `sqrt 3`. -/
def ℓ₀ : ℝ :=
  2 * Real.goldenRatio⁻¹


-- @@ L202-204 verbatim
theorem ℓ₀_pos : 0 < ℓ₀ := by
  dsimp [ℓ₀]
  positivity


-- @@ L206-209 expanded
/-- Il normale della faccia e' `(1,0,φ)`; il livello di supporto e' `φ+1`. -/
def supportL : E3 →L[ℝ] ℝ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 0) +
    Real.goldenRatio • (PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) 2)


-- @@ L211-212 expanded
@[simp]
theorem supportL_apply (z : E3) : supportL z = z 0 + Real.goldenRatio * z 2 := by rfl


-- @@ L214-226 expanded
theorem supportL_faceCycle (i : Fin 5) : supportL (faceCycle i) = Real.goldenRatio + 1 :=
  by
  fin_cases i
  · change (1 : ℝ) + Real.goldenRatio * 1 = Real.goldenRatio + 1
    ring
  · change (0 : ℝ) + Real.goldenRatio * Real.goldenRatio = Real.goldenRatio + 1
    nlinarith [golden_inv_nf, Real.goldenRatio_sq]
  · change (0 : ℝ) + Real.goldenRatio * Real.goldenRatio = Real.goldenRatio + 1
    nlinarith [Real.goldenRatio_sq]
  · change (1 : ℝ) + Real.goldenRatio * 1 = Real.goldenRatio + 1
    ring
  · change Real.goldenRatio + Real.goldenRatio * Real.goldenRatio⁻¹ = Real.goldenRatio + 1
    rw [Real.inv_goldenRatio, mul_neg, Real.goldenRatio_mul_goldenConj]
    ring


-- @@ L228-231 verbatim
theorem faceCycle_mem_vertices (i : Fin 5) :
    faceCycle i ∈ (verticiDodeca : Set E3) := by
  fin_cases i <;> simp [faceCycle, x0, x1, x2, x3, x4,
    verticiDodeca]


-- @@ L233-250 expanded
theorem faceCycle_injective : Function.Injective faceCycle :=
  by
  have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hq : 0 < 2 / (1 + Real.sqrt 5) := by positivity
  have hsqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    have h0 := congrArg (fun z : E3 => z 0) hij
    have h1 := congrArg (fun z : E3 => z 1) hij
    have h2 := congrArg (fun z : E3 => z 2) hij
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4, a7, b3, b1, a5, c3D] at h0
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4, a7, b3, b1, a5, c3D] at h1
  all_goals norm_num [faceCycle, x0, x1, x2, x3, x4, a7, b3, b1, a5, c3D] at h2
  all_goals nlinarith


-- @@ L252-264 expanded
theorem supportL_vertices_le (v : E3) (hv : v ∈ verticiDodeca) :
    supportL v ≤ Real.goldenRatio + 1 :=
  by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [supportL, a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D,
      d2D, d3]
  all_goals
    simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals nlinarith [golden_inv_nf, Real.goldenRatio_sq]


-- @@ L266-286 expanded
theorem supportL_eq_imp_faceCycle (v : E3) (hv : v ∈ verticiDodeca)
    (heq : supportL v = Real.goldenRatio + 1) : v ∈ Set.range faceCycle :=
  by
  have hp := Real.goldenRatio_pos
  have hp1 := Real.one_lt_goldenRatio
  have hp2 := Real.goldenRatio_lt_two
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | skip
  all_goals exfalso
  all_goals
    norm_num [supportL, a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D,
      d2D, d3] at heq
  all_goals
    simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ] at heq
  all_goals nlinarith [golden_inv_nf, Real.goldenRatio_sq]


-- @@ L288-289 verbatim
theorem F₀_nonemptyD : F₀D.Nonempty := by
  exact ⟨x0, subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩⟩


-- @@ L291-294 verbatim
theorem F₀_subset_dodecaedro : F₀D ⊆ dodecaedro.toSet := by
  apply convexHull_mono
  rintro z ⟨i, rfl⟩
  exact faceCycle_mem_vertices i


-- @@ L296-302 expanded
theorem supportL_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    supportL z ≤ Real.goldenRatio + 1 :=
  by
  have hc : ConvexOn ℝ Set.univ supportL := supportL.toLinearMap.convexOn convex_univ
  obtain ⟨v, hv, hzv⟩ :=
    hc.exists_ge_of_mem_convexHull (Set.subset_univ (s := (verticiDodeca : Set E3))) hz
  exact hzv.trans (supportL_vertices_le v hv)


-- @@ L304-316 expanded
theorem supportL_eq_on_F₀ (z : E3) (hz : z ∈ F₀D) : supportL z = Real.goldenRatio + 1 :=
  by
  have hc : ConvexOn ℝ Set.univ supportL := supportL.toLinearMap.convexOn convex_univ
  have hcc : ConcaveOn ℝ Set.univ supportL := supportL.toLinearMap.concaveOn convex_univ
  obtain ⟨u, ⟨i, rfl⟩, hzu⟩ :=
    hc.exists_ge_of_mem_convexHull (Set.subset_univ (s := Set.range faceCycle)) hz
  obtain ⟨v, ⟨j, rfl⟩, hvz⟩ :=
    hcc.exists_le_of_mem_convexHull (Set.subset_univ (s := Set.range faceCycle)) hz
  rw [supportL_faceCycle i] at hzu
  rw [supportL_faceCycle j] at hvz
  exact le_antisymm hzu hvz


-- @@ L318-393 expanded
/-- Un punto dell'hull totale sul piano di supporto usa soltanto i cinque
vertici massimizzanti, dunque appartiene alla faccia. -/
theorem mem_F₀_of_mem_polytope_support_eq (z : E3) (hz : z ∈ dodecaedro.toSet)
    (hzeq : supportL z = Real.goldenRatio + 1) : z ∈ F₀D := by
  classical
  change z ∈ convexHull ℝ (Set.range faceCycle)
  change z ∈ convexHull ℝ (verticiDodeca : Set E3) at hz
  obtain ⟨w, hw0, hw1, hsum⟩ := (Finset.mem_convexHull').mp hz
  have hLsum : ∑ y ∈ verticiDodeca, w y * supportL y = supportL z :=
    by
    have h := congrArg supportL hsum
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  have hdef : ∑ y ∈ verticiDodeca, w y * ((Real.goldenRatio + 1) - supportL y) = 0 := by
    calc
      ∑ y ∈ verticiDodeca, w y * ((Real.goldenRatio + 1) - supportL y) =
          ∑ y ∈ verticiDodeca, (w y * (Real.goldenRatio + 1) - w y * supportL y) :=
        by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ =
          (∑ y ∈ verticiDodeca, w y * (Real.goldenRatio + 1)) -
            ∑ y ∈ verticiDodeca, w y * supportL y :=
        by rw [Finset.sum_sub_distrib]
      _ =
          (Real.goldenRatio + 1) * (∑ y ∈ verticiDodeca, w y) -
            ∑ y ∈ verticiDodeca, w y * supportL y :=
        by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (Real.goldenRatio + 1) - supportL z := by rw [hw1, hLsum]; ring
      _ = 0 := by rw [hzeq]; ring
  have hterm (y : E3) (hy : y ∈ verticiDodeca) : w y * ((Real.goldenRatio + 1) - supportL y) = 0 :=
    by
    apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef y hy
    intro u hu
    exact mul_nonneg (hw0 u hu) (sub_nonneg.mpr (supportL_vertices_le u hu))
  have hwzero (y : E3) (hy : y ∈ verticiDodeca) (hyface : y ∉ Set.range faceCycle) : w y = 0 :=
    by
    have hne : (Real.goldenRatio + 1) - supportL y ≠ 0 :=
      by
      intro h
      apply hyface
      apply supportL_eq_imp_faceCycle y hy
      linarith
    exact (mul_eq_zero.mp (hterm y hy)).resolve_right hne
  let I := { y // y ∈ verticiDodeca }
  let z' : I → E3 := fun y => if y.1 ∈ Set.range faceCycle then y.1 else x0
  refine mem_convexHull_of_exists_fintype (fun y : I => w y.1) z' ?_ ?_ ?_ ?_
  · intro y
    exact hw0 y.1 y.2
  · change (∑ y : { y // y ∈ verticiDodeca }, w y.1) = 1
    rw [← Finset.sum_subtype verticiDodeca (by simp) w]
    exact hw1
  · intro y
    dsimp [z']
    split_ifs with h
    · exact h
    · exact ⟨0, rfl⟩
  · have hzterm (y : I) : w y.1 • z' y = w y.1 • y.1 :=
      by
      by_cases hface : y.1 ∈ Set.range faceCycle
      · change w y.1 • (if y.1 ∈ Set.range faceCycle then y.1 else x0) = _
        rw [if_pos hface]
      · change w y.1 • (if y.1 ∈ Set.range faceCycle then y.1 else x0) = _
        rw [if_neg hface, hwzero y.1 y.2 hface]
        simp
    calc
      ∑ y : I, w y.1 • z' y = ∑ y : I, w y.1 • y.1 :=
        by
        apply Fintype.sum_congr
        exact hzterm
      _ = ∑ y ∈ verticiDodeca, w y • y :=
        by
        change (∑ y : { y // y ∈ verticiDodeca }, w y.1 • y.1) = _
        rw [← Finset.sum_subtype verticiDodeca (by simp) (fun y => w y • y)]
      _ = z := hsum


-- @@ L395-411 expanded
theorem F₀_isExposed : IsExposed ℝ dodecaedro.toSet F₀D :=
  by
  intro _hne
  refine ⟨supportL, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨F₀_subset_dodecaedro hz, ?_⟩
    intro y hy
    rw [supportL_eq_on_F₀ z hz]
    exact supportL_polytope_le y hy
  · rintro ⟨hzP, hzmax⟩
    have hx0P : x0 ∈ dodecaedro.toSet :=
      F₀_subset_dodecaedro (subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩)
    have hlo : Real.goldenRatio + 1 ≤ supportL z := by
      simpa [show supportL x0 = Real.goldenRatio + 1 from supportL_faceCycle 0] using hzmax x0 hx0P
    have hhi := supportL_polytope_le z hzP
    exact mem_F₀_of_mem_polytope_support_eq z hzP (le_antisymm hhi hlo)


-- @@ L413-413 verbatim
/-! ## Dimensione due della faccia -/


-- @@ L415-415 verbatim
def baseTriple : Fin 3 → E3 := ![x0, x1, x2]


-- @@ L417-438 verbatim
theorem baseTriple_affineIndependent : AffineIndependent ℝ baseTriple := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  funext i
  have hcoord (j : Fin 3) := congrArg (fun z : E3 => z j) huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hu),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hv)] at hcoord
  simp [baseTriple, x0, x1, x2, a7, b3, b1, Fin.sum_univ_three] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  change u 0 * 1 + u 1 * 0 + u 2 * 0 =
    v 0 * 1 + v 1 * 0 + v 2 * 0 at h0
  change u 0 * 1 + u 1 * (2 / (1 + Real.sqrt 5)) +
      u 2 * (-(2 / (1 + Real.sqrt 5))) =
    v 0 * 1 + v 1 * (2 / (1 + Real.sqrt 5)) +
      v 2 * (-(2 / (1 + Real.sqrt 5))) at h1
  rw [Fin.sum_univ_three] at hu hv
  have hq : 0 < 2 / (1 + Real.sqrt 5) := by positivity
  have e0 : u 0 = v 0 := by linarith
  have e1 : u 1 = v 1 := by nlinarith
  have e2 : u 2 = v 2 := by nlinarith
  fin_cases i <;> assumption


-- @@ L440-440 expanded
def weights3 : Fin 3 → ℝ :=
  ![1, -Real.goldenRatio, Real.goldenRatio]


-- @@ L441-441 expanded
def weights4 : Fin 3 → ℝ :=
  ![Real.goldenRatio, -Real.goldenRatio, 1]


-- @@ L443-444 verbatim
theorem weights3_sum : ∑ i : Fin 3, weights3 i = 1 := by
  simp [weights3, Fin.sum_univ_three]


-- @@ L446-447 verbatim
theorem weights4_sum : ∑ i : Fin 3, weights4 i = 1 := by
  simp [weights4, Fin.sum_univ_three]


-- @@ L449-455 verbatim
theorem E3_ext {u v : E3} (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (h2 : u 2 = v 2) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2


-- @@ L457-468 expanded
theorem combo_x3 : Finset.univ.affineCombination ℝ baseTriple weights3 = x3 :=
  by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using weights3_sum)]
  rw [Fin.sum_univ_three]
  apply E3_ext
  · change (1 : ℝ) * 1 + (-Real.goldenRatio) * 0 + Real.goldenRatio * 0 = 1
    ring
  · change
      (1 : ℝ) * 1 + (-Real.goldenRatio) * Real.goldenRatio⁻¹ +
          Real.goldenRatio * (-Real.goldenRatio⁻¹) =
        -1
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]
  · change
      (1 : ℝ) * 1 + (-Real.goldenRatio) * Real.goldenRatio + Real.goldenRatio * Real.goldenRatio = 1
    ring


-- @@ L470-482 expanded
theorem combo_x4 : Finset.univ.affineCombination ℝ baseTriple weights4 = x4 :=
  by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using weights4_sum)]
  rw [Fin.sum_univ_three]
  apply E3_ext
  · change Real.goldenRatio * 1 + (-Real.goldenRatio) * 0 + (1 : ℝ) * 0 = Real.goldenRatio
    ring
  · change
      Real.goldenRatio * 1 + (-Real.goldenRatio) * Real.goldenRatio⁻¹ +
          (1 : ℝ) * (-Real.goldenRatio⁻¹) =
        0
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]
  · change
      Real.goldenRatio * 1 + (-Real.goldenRatio) * Real.goldenRatio + (1 : ℝ) * Real.goldenRatio =
        Real.goldenRatio⁻¹
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]


-- @@ L484-489 verbatim
theorem x3_mem_affineSpan_base : x3 ∈ affineSpan ℝ (Set.range baseTriple) := by
  have h := affineCombination_mem_affineSpan
    (s := (Finset.univ : Finset (Fin 3))) (w := weights3)
    (by simpa using weights3_sum) baseTriple
  rw [combo_x3] at h
  exact h


-- @@ L491-496 verbatim
theorem x4_mem_affineSpan_base : x4 ∈ affineSpan ℝ (Set.range baseTriple) := by
  have h := affineCombination_mem_affineSpan
    (s := (Finset.univ : Finset (Fin 3))) (w := weights4)
    (by simpa using weights4_sum) baseTriple
  rw [combo_x4] at h
  exact h


-- @@ L498-516 verbatim
theorem range_faceCycle_eq : Set.range faceCycle =
    insert x4 (insert x3 (Set.range baseTriple)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨1, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨2, rfl⟩)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert _ _
  · rw [Set.mem_insert_iff, Set.mem_insert_iff]
    rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨4, rfl⟩
    · exact ⟨3, rfl⟩
    · fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩


-- @@ L518-529 verbatim
theorem faceCycle_coplanar : Coplanar ℝ (Set.range faceCycle) := by
  have hbaseRank :
      Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) = 2 :=
    baseTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
  have hbase : Coplanar ℝ (Set.range baseTriple) := by
    rw [coplanar_iff_finrank_le_two, hbaseRank]
  have h3 : Coplanar ℝ (insert x3 (Set.range baseTriple)) :=
    (coplanar_insert_iff_of_mem_affineSpan x3_mem_affineSpan_base).2 hbase
  have hx4 : x4 ∈ affineSpan ℝ (insert x3 (Set.range baseTriple)) := by
    exact (affineSpan_mono ℝ (Set.subset_insert x3 _)) x4_mem_affineSpan_base
  rw [range_faceCycle_eq]
  exact (coplanar_insert_iff_of_mem_affineSpan hx4).2 h3


-- @@ L531-547 verbatim
theorem F₀_finrank : Module.finrank ℝ (vectorSpan ℝ F₀D) = 2 := by
  have hupper : Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) ≤ 2 :=
    faceCycle_coplanar.finrank_le_two
  have hlower : 2 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) := by
    have hbaseRank :
        Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) = 2 :=
      baseTriple_affineIndependent.finrank_vectorSpan (n := 2) (by simp)
    calc
      2 = Module.finrank ℝ (vectorSpan ℝ (Set.range baseTriple)) := hbaseRank.symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range faceCycle)) := by
        apply Submodule.finrank_mono
        apply vectorSpan_mono ℝ
        intro z hz
        rw [range_faceCycle_eq]
        exact Set.mem_insert_of_mem x4 (Set.mem_insert_of_mem x3 hz)
  rw [F₀D, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  omega


-- @@ L549-550 verbatim
theorem F₀_isFacet : dodecaedro.IsFacet F₀D :=
  ⟨⟨F₀_isExposed, F₀_nonemptyD⟩, F₀_finrank⟩


-- @@ L552-552 verbatim
/-! ## La rotazione aurea di ordine cinque -/


-- @@ L554-559 expanded
/-- La matrice e' `1/2 * [[1,-φ,φ⁻¹],[φ,φ⁻¹,-1],[φ⁻¹,1,φ]]`.
Non e' una permutazione delle coordinate. -/
def rhoFormula (z : E3) : E3 :=
  WithLp.toLp 2
    ![(z 0 - Real.goldenRatio * z 1 + Real.goldenRatio⁻¹ * z 2) / 2,
      (Real.goldenRatio * z 0 + Real.goldenRatio⁻¹ * z 1 - z 2) / 2,
      (Real.goldenRatio⁻¹ * z 0 + z 1 + Real.goldenRatio * z 2) / 2]


-- @@ L561-566 verbatim
def rhoLinearMap : E3 →ₗ[ℝ] E3 where
  toFun := rhoFormula
  map_add' u v := by
    apply E3_ext <;> simp [rhoFormula] <;> ring
  map_smul' c u := by
    apply E3_ext <;> simp [rhoFormula] <;> ring


-- @@ L568-568 verbatim
@[simp] theorem rhoLinearMap_apply (z : E3) : rhoLinearMap z = rhoFormula z := rfl


-- @@ L570-586 expanded
def rhoLinearIsometry : E3 →ₗᵢ[ℝ] E3
    where
  toLinearMap := rhoLinearMap
  norm_map'
    z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    change
      ((z 0 - Real.goldenRatio * z 1 + Real.goldenRatio⁻¹ * z 2) / 2) ^ 2 +
            ((Real.goldenRatio * z 0 + Real.goldenRatio⁻¹ * z 1 - z 2) / 2) ^ 2 +
          ((Real.goldenRatio⁻¹ * z 0 + z 1 + Real.goldenRatio * z 2) / 2) ^ 2 =
        z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2
    rw [golden_inv]
    ring_nf
    have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [hs]
    ring


-- @@ L588-589 verbatim
def rhoLinear : E3 ≃ₗᵢ[ℝ] E3 :=
  rhoLinearIsometry.toLinearIsometryEquiv rfl


-- @@ L591-591 verbatim
def ρ : E3 ≃ᵃⁱ[ℝ] E3 := rhoLinear.toAffineIsometryEquiv


-- @@ L593-594 verbatim
@[simp] theorem rho_apply (z : E3) : ρ z = rhoFormula z := by
  rfl


-- @@ L596-639 verbatim
theorem rho_faceCycle (i : Fin 5) :
    ρ (faceCycle i) = faceCycle (finRotate 5 i) := by
  have h01 : ρ x0 = x1 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x0, x1, a7, b3]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h12 : ρ x1 = x2 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x1, x2, b3, b1]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h23 : ρ x2 = x3 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x2, x3, b1, a5]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  have h34 : ρ x3 = x4 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x3, x4, a5, c3D]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals nlinarith [golden_sqrt_five, Real.goldenRatio_sq]
  have h40 : ρ x4 = x0 := by
    apply E3_ext
    all_goals norm_num [rhoFormula, x4, x0, c3D, a7]
    all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
    all_goals rw [golden_inv_nf] at *
    all_goals try simp only [golden_den_self] at *
    all_goals nlinarith [Real.goldenRatio_sq]
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h40


-- @@ L641-641 verbatim
theorem rho_x0 : ρ x0 = x1 := by simpa using rho_faceCycle 0

-- @@ L642-642 verbatim
theorem rho_x1 : ρ x1 = x2 := by simpa using rho_faceCycle 1

-- @@ L643-643 verbatim
theorem rho_x2 : ρ x2 = x3 := by simpa using rho_faceCycle 2

-- @@ L644-644 verbatim
theorem rho_x3 : ρ x3 = x4 := by simpa using rho_faceCycle 3

-- @@ L645-645 verbatim
theorem rho_x4 : ρ x4 = x0 := by simpa using rho_faceCycle 4


-- @@ L647-659 verbatim
theorem rho_iter_faceCycle (i : Fin 5) :
    (⇑ρ)^[(i : ℕ)] x0 = faceCycle i := by
  fin_cases i
  · change x0 = x0
    rfl
  · change ρ x0 = x1
    exact rho_x0
  · change ρ (ρ x0) = x2
    rw [rho_x0, rho_x1]
  · change ρ (ρ (ρ x0)) = x3
    rw [rho_x0, rho_x1, rho_x2]
  · change ρ (ρ (ρ (ρ x0))) = x4
    rw [rho_x0, rho_x1, rho_x2, rho_x3]


-- @@ L661-663 verbatim
theorem rho_order_five_on_x0 : (⇑ρ)^[5] x0 = x0 := by
  change ρ (ρ (ρ (ρ (ρ x0)))) = x0
  rw [rho_x0, rho_x1, rho_x2, rho_x3, rho_x4]


-- @@ L665-670 verbatim
theorem rho_orbit_injective :
    Function.Injective (fun i : Fin 5 => (⇑ρ)^[(i : ℕ)] x0) := by
  intro i j hij
  change (⇑ρ)^[(i : ℕ)] x0 = (⇑ρ)^[(j : ℕ)] x0 at hij
  rw [rho_iter_faceCycle, rho_iter_faceCycle] at hij
  exact faceCycle_injective hij


-- @@ L672-680 verbatim
theorem range_rho_orbit :
    Set.range (fun i : Fin 5 => (⇑ρ)^[(i : ℕ)] x0) =
      Set.range faceCycle := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (rho_iter_faceCycle i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rho_iter_faceCycle i⟩


-- @@ L682-691 verbatim
theorem rho_image_faceCycle :
    (⇑ρ) '' Set.range faceCycle = Set.range faceCycle := by
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [rho_faceCycle]
    exact Set.mem_range_self _
  · rintro ⟨i, rfl⟩
    refine ⟨faceCycle ((finRotate 5).symm i), Set.mem_range_self _, ?_⟩
    rw [rho_faceCycle, (finRotate 5).apply_symm_apply]


-- @@ L693-702 verbatim
theorem rho_image_F₀ : (⇑ρ) '' F₀D = F₀D := by
  change (⇑ρ) '' convexHull ℝ (Set.range faceCycle) =
    convexHull ℝ (Set.range faceCycle)
  calc
    (⇑ρ) '' convexHull ℝ (Set.range faceCycle) =
        convexHull ℝ ((⇑ρ) '' Set.range faceCycle) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        (ρ.toAffineEquiv.toAffineMap.image_convexHull (Set.range faceCycle))
    _ = convexHull ℝ (Set.range faceCycle) := by rw [rho_image_faceCycle]


-- @@ L704-720 expanded
theorem dist_x0_rho : dist x0 (ρ x0) = ℓ₀ :=
  by
  rw [rho_x0, dist_eq_norm]
  have hsub :
    x0 - x1 = (WithLp.toLp 2 ![(1 : ℝ), 1 - Real.goldenRatio⁻¹, 1 - Real.goldenRatio] : E3) :=
    by
    apply E3_ext
    all_goals norm_num [x0, x1, a7, b3]
    all_goals
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  rw [hsub]
  change
    ‖(WithLp.toLp 2 ![(1 : ℝ), 1 - Real.goldenRatio⁻¹, 1 - Real.goldenRatio] : E3)‖ =
      2 * Real.goldenRatio⁻¹
  rw [norma_toLp]
  have hrad :
    (1 : ℝ) ^ 2 + (1 - Real.goldenRatio⁻¹) ^ 2 + (1 - Real.goldenRatio) ^ 2 =
      (2 * Real.goldenRatio⁻¹) ^ 2 :=
    by
    rw [golden_inv]
    nlinarith [Real.goldenRatio_sq]
  rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos]
  exact mul_pos (by norm_num) golden_inv_pos


-- @@ L722-722 verbatim
/-! ## Assemblaggio dello spike -/


-- @@ L724-729 verbatim
theorem faccia_dodecaedro_regolare :
    dodecaedro.IsRegularFacet F₀D 5 ℓ₀ := by
  refine ⟨F₀_isFacet, ℓ₀_pos, by omega, ρ, x0, ?_, rho_image_F₀,
    rho_orbit_injective, rho_order_five_on_x0, ?_, dist_x0_rho⟩
  · exact subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩
  · rw [F₀D, range_rho_orbit]


-- @@ L731-731 verbatim
/-! ## FASCICOLO 7 — il fan del vertice `a7 = (1,1,1)` -/


-- @@ L733-735 verbatim
/-- Il ciclo delle coordinate `(x,y,z) ↦ (z,x,y)`. -/
def sigmaLinear : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)


-- @@ L737-737 verbatim
def σ : E3 ≃ᵃⁱ[ℝ] E3 := sigmaLinear.toAffineIsometryEquiv


-- @@ L739-740 verbatim
@[simp] theorem sigma_apply_zero (z : E3) : σ z 0 = z 2 := by
  rfl


-- @@ L742-743 verbatim
@[simp] theorem sigma_apply_one (z : E3) : σ z 1 = z 0 := by
  rfl


-- @@ L745-746 verbatim
@[simp] theorem sigma_apply_two (z : E3) : σ z 2 = z 1 := by
  rfl


-- @@ L748-750 verbatim
theorem sigma_formula (z : E3) :
    σ z = WithLp.toLp 2 ![z 2, z 0, z 1] := by
  apply E3_ext <;> rfl


-- @@ L752-753 verbatim
theorem sigma_three (z : E3) : σ (σ (σ z)) = z := by
  apply E3_ext <;> rfl


-- @@ L755-756 verbatim
theorem sigma_a7 : σ a7 = a7 := by
  apply E3_ext <;> rfl


-- @@ L758-764 verbatim
theorem sigma_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    σ v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [sigma_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]


-- @@ L766-773 verbatim
theorem sigma_image_vertices :
    (⇑σ) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact sigma_vertices v hv
  · intro v hv
    refine ⟨σ (σ v), sigma_vertices _ (sigma_vertices _ hv), ?_⟩
    exact sigma_three v


-- @@ L775-787 verbatim
theorem sigma_preserves_polytope :
    (⇑σ) '' dodecaedro.toSet = dodecaedro.toSet := by
  change (⇑σ) '' convexHull ℝ (verticiDodeca : Set E3) =
    convexHull ℝ (verticiDodeca : Set E3)
  calc
    (⇑σ) '' convexHull ℝ (verticiDodeca : Set E3) =
        convexHull ℝ ((⇑σ) '' (verticiDodeca : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        (σ.toAffineEquiv.toAffineMap.image_convexHull
          (verticiDodeca : Set E3))
    _ = convexHull ℝ (verticiDodeca : Set E3) := by
      rw [sigma_image_vertices]


-- @@ L789-802 verbatim
theorem sigma_mem_polytope_iff (z : E3) :
    σ z ∈ dodecaedro.toSet ↔ z ∈ dodecaedro.toSet := by
  constructor
  · intro hz
    have h₁ : σ (σ z) ∈ dodecaedro.toSet := by
      rw [← sigma_preserves_polytope]
      exact ⟨σ z, hz, rfl⟩
    have h₂ : σ (σ (σ z)) ∈ dodecaedro.toSet := by
      rw [← sigma_preserves_polytope]
      exact ⟨σ (σ z), h₁, rfl⟩
    rwa [sigma_three] at h₂
  · intro hz
    rw [← sigma_preserves_polytope]
    exact ⟨z, hz, rfl⟩


-- @@ L804-834 verbatim
theorem sigma_image_isExposed {F : Set E3}
    (hF : IsExposed ℝ dodecaedro.toSet F) :
    IsExposed ℝ dodecaedro.toSet ((⇑σ) '' F) := by
  intro himage
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := himage
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy⟩
  obtain ⟨l, hl⟩ := hF hFne
  let l' : E3 →L[ℝ] ℝ :=
    l.comp sigmaLinear.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨l', ?_⟩
  rw [hl]
  ext x
  constructor
  · rintro ⟨u, ⟨huP, humax⟩, rfl⟩
    refine ⟨(sigma_mem_polytope_iff u).2 huP, ?_⟩
    intro y hyP
    obtain ⟨z, rfl⟩ := σ.surjective y
    have hzP : z ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff z).1 hyP
    simpa [l', σ] using humax z hzP
  · rintro ⟨hxP, hxmax⟩
    obtain ⟨u, rfl⟩ := σ.surjective x
    have huP : u ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff u).1 hxP
    refine ⟨u, ⟨huP, ?_⟩, rfl⟩
    intro z hzP
    have hσzP : σ z ∈ dodecaedro.toSet :=
      (sigma_mem_polytope_iff z).2 hzP
    simpa [l', σ] using hxmax (σ z) hσzP


-- @@ L836-842 verbatim
theorem sigma_image_finrank (F : Set E3) :
    Module.finrank ℝ (vectorSpan ℝ ((⇑σ) '' F)) =
      Module.finrank ℝ (vectorSpan ℝ F) := by
  change Module.finrank ℝ
      (vectorSpan ℝ ((⇑σ.toAffineEquiv.toAffineMap) '' F)) = _
  rw [← σ.toAffineEquiv.toAffineMap.map_vectorSpan]
  exact sigmaLinear.toLinearEquiv.finrank_map_eq (vectorSpan ℝ F)


-- @@ L844-847 verbatim
theorem sigma_image_isFacet {F : Set E3} (hF : dodecaedro.IsFacet F) :
    dodecaedro.IsFacet ((⇑σ) '' F) := by
  refine ⟨⟨sigma_image_isExposed hF.1.1, hF.1.2.image _⟩, ?_⟩
  rw [sigma_image_finrank, hF.2]


-- @@ L849-849 verbatim
def F₁ : Set E3 := (⇑σ) '' F₀D

-- @@ L850-850 verbatim
def F₂ : Set E3 := (⇑σ) '' F₁


-- @@ L852-852 verbatim
def fanFace : Fin 3 → Set E3 := ![F₀D, F₁, F₂]


-- @@ L854-855 verbatim
theorem F₁_isFacet : dodecaedro.IsFacet F₁ :=
  sigma_image_isFacet F₀_isFacet


-- @@ L857-858 verbatim
theorem F₂_isFacet : dodecaedro.IsFacet F₂ :=
  sigma_image_isFacet F₁_isFacet


-- @@ L860-868 verbatim
theorem sigma_image_F₂ : (⇑σ) '' F₂ = F₀D := by
  ext z
  constructor
  · rintro ⟨u, ⟨v, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [sigma_three]
    exact hw
  · intro hz
    refine ⟨σ (σ z), ⟨σ z, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
    exact sigma_three z


-- @@ L870-875 verbatim
theorem sigma_image_fanFace (i : Fin 3) :
    (⇑σ) '' fanFace i = fanFace (finRotate 3 i) := by
  fin_cases i
  · rfl
  · rfl
  · exact sigma_image_F₂


-- @@ L877-879 expanded
theorem mem_F₀_support (z : E3) (hz : z ∈ F₀D) :
    z 0 + Real.goldenRatio * z 2 = Real.goldenRatio + 1 := by exact supportL_eq_on_F₀ z hz


-- @@ L881-887 expanded
theorem mem_F₁_support (z : E3) (hz : z ∈ F₁) :
    Real.goldenRatio * z 0 + z 1 = Real.goldenRatio + 1 :=
  by
  rcases hz with ⟨u, hu, rfl⟩
  have h := supportL_eq_on_F₀ u hu
  change u 0 + Real.goldenRatio * u 2 = Real.goldenRatio + 1 at h
  change Real.goldenRatio * u 2 + u 0 = Real.goldenRatio + 1
  linarith


-- @@ L889-895 expanded
theorem mem_F₂_support (z : E3) (hz : z ∈ F₂) :
    Real.goldenRatio * z 1 + z 2 = Real.goldenRatio + 1 :=
  by
  rcases hz with ⟨u, ⟨v, hv, rfl⟩, rfl⟩
  have h := supportL_eq_on_F₀ v hv
  change v 0 + Real.goldenRatio * v 2 = Real.goldenRatio + 1 at h
  change Real.goldenRatio * v 2 + v 0 = Real.goldenRatio + 1
  linarith


-- @@ L897-898 verbatim
theorem a7_mem_F₀ : a7 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨0, rfl⟩


-- @@ L900-904 verbatim
theorem a7_mem_fanFace (i : Fin 3) : a7 ∈ fanFace i := by
  fin_cases i
  · exact a7_mem_F₀
  · exact ⟨a7, a7_mem_F₀, sigma_a7⟩
  · exact ⟨a7, ⟨a7, a7_mem_F₀, sigma_a7⟩, sigma_a7⟩


-- @@ L906-907 verbatim
theorem b1_mem_F₀ : b1 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨2, rfl⟩


-- @@ L909-911 verbatim
theorem c2_mem_F₁ : c2D ∈ F₁ := by
  refine ⟨b1, b1_mem_F₀, ?_⟩
  apply E3_ext <;> rfl


-- @@ L913-919 expanded
theorem b1_not_mem_F₁ : b1 ∉ F₁ := by
  intro h
  have he := mem_F₁_support b1 h
  change Real.goldenRatio * 0 + (-Real.goldenRatio⁻¹) = Real.goldenRatio + 1 at he
  have hp := Real.goldenRatio_pos
  have hi := golden_inv_pos
  nlinarith


-- @@ L921-926 expanded
theorem b1_not_mem_F₂ : b1 ∉ F₂ := by
  intro h
  have he := mem_F₂_support b1 h
  change Real.goldenRatio * (-Real.goldenRatio⁻¹) + Real.goldenRatio = Real.goldenRatio + 1 at he
  rw [golden_inv] at he
  nlinarith [Real.goldenRatio_sq]


-- @@ L928-934 expanded
theorem c2_not_mem_F₂ : c2D ∉ F₂ := by
  intro h
  have he := mem_F₂_support c2D h
  change Real.goldenRatio * 0 + (-Real.goldenRatio⁻¹) = Real.goldenRatio + 1 at he
  have hp := Real.goldenRatio_pos
  have hi := golden_inv_pos
  nlinarith


-- @@ L936-963 verbatim
theorem fanFace_injective : Function.Injective fanFace := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals exfalso
  · change F₀D = F₁ at hij
    apply b1_not_mem_F₁
    rw [← hij]
    exact b1_mem_F₀
  · change F₀D = F₂ at hij
    apply b1_not_mem_F₂
    rw [← hij]
    exact b1_mem_F₀
  · change F₁ = F₀D at hij
    apply b1_not_mem_F₁
    rw [hij]
    exact b1_mem_F₀
  · change F₁ = F₂ at hij
    apply c2_not_mem_F₂
    rw [← hij]
    exact c2_mem_F₁
  · change F₂ = F₀D at hij
    apply b1_not_mem_F₂
    rw [hij]
    exact b1_mem_F₀
  · change F₂ = F₁ at hij
    apply c2_not_mem_F₂
    rw [hij]
    exact c2_mem_F₁


-- @@ L965-966 verbatim
theorem c3_mem_F₀ : c3D ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨4, rfl⟩


-- @@ L968-969 verbatim
theorem b3_mem_F₀ : b3 ∈ F₀D := by
  exact subset_convexHull ℝ (Set.range faceCycle) ⟨1, rfl⟩


-- @@ L971-973 verbatim
theorem c3_mem_F₁ : c3D ∈ F₁ := by
  refine ⟨b3, b3_mem_F₀, ?_⟩
  apply E3_ext <;> rfl


-- @@ L975-977 verbatim
theorem d3_mem_F₁ : d3 ∈ F₁ := by
  refine ⟨c3D, c3_mem_F₀, ?_⟩
  apply E3_ext <;> rfl


-- @@ L979-980 verbatim
theorem d3_mem_F₂ : d3 ∈ F₂ := by
  exact ⟨c3D, c3_mem_F₁, by apply E3_ext <;> rfl⟩


-- @@ L982-984 verbatim
theorem b3_mem_F₂ : b3 ∈ F₂ := by
  refine ⟨d3, d3_mem_F₁, ?_⟩
  apply E3_ext <;> rfl


-- @@ L986-989 verbatim
theorem c3_ne_a7 : c3D ≠ a7 := by
  intro h
  have h1 := congrArg (fun z : E3 => z 1) h
  norm_num [c3D, a7] at h1


-- @@ L991-995 verbatim
theorem d3_ne_a7 : d3 ≠ a7 := by
  intro h
  have h2 := congrArg (fun z : E3 => z 2) h
  change (0 : ℝ) = 1 at h2
  norm_num at h2


-- @@ L997-1000 verbatim
theorem b3_ne_a7 : b3 ≠ a7 := by
  intro h
  have h0 := congrArg (fun z : E3 => z 0) h
  norm_num [b3, a7] at h0


-- @@ L1002-1007 verbatim
theorem fanFace_spigolo (i : Fin 3) :
    ∃ x, x ≠ a7 ∧ x ∈ fanFace i ∩ fanFace (finRotate 3 i) := by
  fin_cases i
  · exact ⟨c3D, c3_ne_a7, c3_mem_F₀, c3_mem_F₁⟩
  · exact ⟨d3, d3_ne_a7, d3_mem_F₁, d3_mem_F₂⟩
  · exact ⟨b3, b3_ne_a7, b3_mem_F₂, b3_mem_F₀⟩


-- @@ L1009-1031 expanded
theorem three_fan_faces_meet_at_a7 (z : E3) (h0 : z ∈ F₀D) (h1 : z ∈ F₁) (h2 : z ∈ F₂) : z = a7 :=
  by
  have e0 := mem_F₀_support z h0
  have e1 := mem_F₁_support z h1
  have e2 := mem_F₂_support z h2
  have q0 : (z 0 - 1) + Real.goldenRatio * (z 2 - 1) = 0 := by linarith
  have q1 : Real.goldenRatio * (z 0 - 1) + (z 1 - 1) = 0 := by linarith
  have q2 : Real.goldenRatio * (z 1 - 1) + (z 2 - 1) = 0 := by linarith
  have qz : (z 2 - 1) - Real.goldenRatio ^ 2 * (z 0 - 1) = 0 := by
    linear_combination q2 - Real.goldenRatio * q1
  have qx : (1 + Real.goldenRatio ^ 3) * (z 0 - 1) = 0 := by
    linear_combination q0 - Real.goldenRatio * qz
  have hp : 0 < 1 + Real.goldenRatio ^ 3 := by positivity
  have hx : z 0 = 1 := by nlinarith
  have hy : z 1 = 1 := by rw [hx] at q1; linarith
  have hz : z 2 = 1 := by rw [hx] at qz; linarith
  apply E3_ext
  · exact hx
  · exact hy
  · exact hz


-- @@ L1033-1033 verbatim
/-! ## Il muro: classificazione locale delle faccette incidenti -/


-- @@ L1035-1061 verbatim
open Classical in
theorem dodeca_exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : dodecaedro.IsFace F) :
    F = convexHull ℝ
      ((dodecaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact dodecaedro.toSet := by
    exact dodecaedro.vertices.finite_toSet.isCompact_convexHull ℝ
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ dodecaedro.toSet.extremePoints ℝ) ↔
      x ∈ dodecaedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← dodecaedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((dodecaedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl


-- @@ L1063-1063 verbatim
def e₀ : E3 := WithLp.toLp 2 ![1, 0, 0]

-- @@ L1064-1064 verbatim
def e₁ : E3 := WithLp.toLp 2 ![0, 1, 0]

-- @@ L1065-1065 verbatim
def e₂ : E3 := WithLp.toLp 2 ![0, 0, 1]


-- @@ L1067-1069 verbatim
theorem E3_decomp (z : E3) :
    z = z 0 • e₀ + z 1 • e₁ + z 2 • e₂ := by
  apply E3_ext <;> simp [e₀, e₁, e₂]


-- @@ L1071-1074 verbatim
theorem functional_apply_coords (l : E3 →L[ℝ] ℝ) (z : E3) :
    l z = z 0 * l e₀ + z 1 * l e₁ + z 2 * l e₂ := by
  conv_lhs => rw [E3_decomp z]
  simp only [map_add, map_smul, smul_eq_mul]


-- @@ L1076-1079 verbatim
theorem functional_a7 (l : E3 →L[ℝ] ℝ) :
    l a7 = l e₀ + l e₁ + l e₂ := by
  rw [functional_apply_coords]
  simp [a7]


-- @@ L1081-1084 expanded
theorem functional_c3 (l : E3 →L[ℝ] ℝ) :
    l c3D = Real.goldenRatio * l e₀ + Real.goldenRatio⁻¹ * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [c3D]


-- @@ L1086-1089 expanded
theorem functional_b3 (l : E3 →L[ℝ] ℝ) :
    l b3 = Real.goldenRatio⁻¹ * l e₁ + Real.goldenRatio * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [b3]


-- @@ L1091-1094 expanded
theorem functional_d3 (l : E3 →L[ℝ] ℝ) :
    l d3 = Real.goldenRatio⁻¹ * l e₀ + Real.goldenRatio * l e₁ :=
  by
  rw [functional_apply_coords]
  simp [d3]


-- @@ L1096-1100 expanded
theorem functional_b0 (l : E3 →L[ℝ] ℝ) :
    l b0 = -Real.goldenRatio⁻¹ * l e₁ - Real.goldenRatio * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [b0]
  ring


-- @@ L1102-1105 expanded
theorem functional_b1 (l : E3 →L[ℝ] ℝ) :
    l b1 = -Real.goldenRatio⁻¹ * l e₁ + Real.goldenRatio * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [b1]


-- @@ L1107-1111 expanded
theorem functional_b2 (l : E3 →L[ℝ] ℝ) :
    l b2 = Real.goldenRatio⁻¹ * l e₁ - Real.goldenRatio * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [b2]
  ring


-- @@ L1113-1117 expanded
theorem functional_c0 (l : E3 →L[ℝ] ℝ) :
    l c0D = -Real.goldenRatio * l e₀ - Real.goldenRatio⁻¹ * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [c0D]
  ring


-- @@ L1119-1122 expanded
theorem functional_c1 (l : E3 →L[ℝ] ℝ) :
    l c1D = -Real.goldenRatio * l e₀ + Real.goldenRatio⁻¹ * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [c1D]


-- @@ L1124-1128 expanded
theorem functional_c2 (l : E3 →L[ℝ] ℝ) :
    l c2D = Real.goldenRatio * l e₀ - Real.goldenRatio⁻¹ * l e₂ :=
  by
  rw [functional_apply_coords]
  simp [c2D]
  ring


-- @@ L1130-1134 expanded
theorem functional_d0 (l : E3 →L[ℝ] ℝ) :
    l d0 = -Real.goldenRatio⁻¹ * l e₀ - Real.goldenRatio * l e₁ :=
  by
  rw [functional_apply_coords]
  simp [d0]
  ring


-- @@ L1136-1139 expanded
theorem functional_d1 (l : E3 →L[ℝ] ℝ) :
    l d1D = -Real.goldenRatio⁻¹ * l e₀ + Real.goldenRatio * l e₁ :=
  by
  rw [functional_apply_coords]
  simp [d1D]


-- @@ L1141-1145 expanded
theorem functional_d2 (l : E3 →L[ℝ] ℝ) :
    l d2D = Real.goldenRatio⁻¹ * l e₀ - Real.goldenRatio * l e₁ :=
  by
  rw [functional_apply_coords]
  simp [d2D]
  ring


-- @@ L1147-1157 verbatim
theorem weighted_terms_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a * x + b * y + c * z = 0) :
    a * x = 0 ∧ b * y = 0 ∧ c * z = 0 := by
  have hax : 0 ≤ a * x := mul_nonneg ha hx
  have hby : 0 ≤ b * y := mul_nonneg hb hy
  have hcz : 0 ≤ c * z := mul_nonneg hc hz
  constructor
  · nlinarith
  constructor <;> nlinarith


-- @@ L1159-1166 verbatim
theorem weighted_first_two_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hsum : a * x + b * y + c * z = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨hax, hby, _⟩ := weighted_terms_eq_zero hx hy hz
    ha.le hb.le hc hsum
  exact ⟨(mul_eq_zero.mp hax).resolve_left ha.ne',
    (mul_eq_zero.mp hby).resolve_left hb.ne'⟩


-- @@ L1168-1175 verbatim
theorem weighted_first_third_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hsum : a * x + b * y + c * z = 0) : x = 0 ∧ z = 0 := by
  obtain ⟨hax, _, hcz⟩ := weighted_terms_eq_zero hx hy hz
    ha.le hb hc.le hsum
  exact ⟨(mul_eq_zero.mp hax).resolve_left ha.ne',
    (mul_eq_zero.mp hcz).resolve_left hc.ne'⟩


-- @@ L1177-1184 verbatim
theorem weighted_last_two_eq_zero {x y z a b c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * x + b * y + c * z = 0) : y = 0 ∧ z = 0 := by
  obtain ⟨_, hby, hcz⟩ := weighted_terms_eq_zero hx hy hz
    ha hb.le hc.le hsum
  exact ⟨(mul_eq_zero.mp hby).resolve_left hb.ne',
    (mul_eq_zero.mp hcz).resolve_left hc.ne'⟩


-- @@ L1186-1459 expanded
/-- I tre gap locali non negativi controllano tutti i vertici massimizzanti. -/
theorem local_maximizer_dichotomy (l : E3 →L[ℝ] ℝ) (hmax : ∀ v ∈ verticiDodeca, l v ≤ l a7) (v : E3)
    (hv : v ∈ verticiDodeca) (heq : l v = l a7) :
    v = a7 ∨
      (v = c3D ∧ l c3D = l a7) ∨
        (v = b3 ∧ l b3 = l a7) ∨
          (v = d3 ∧ l d3 = l a7) ∨
            (l c3D = l a7 ∧ l b3 = l a7) ∨
              (l c3D = l a7 ∧ l d3 = l a7) ∨ (l b3 = l a7 ∧ l d3 = l a7) :=
  by
  let gc : ℝ := l a7 - l c3D
  let gb : ℝ := l a7 - l b3
  let gd : ℝ := l a7 - l d3
  have hgc : 0 ≤ gc := sub_nonneg.mpr (hmax c3D (by simp [verticiDodeca]))
  have hgb : 0 ≤ gb := sub_nonneg.mpr (hmax b3 (by simp [verticiDodeca]))
  have hgd : 0 ≤ gd := sub_nonneg.mpr (hmax d3 (by simp [verticiDodeca]))
  have hp1 : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hp2 : 0 < 2 - Real.goldenRatio := sub_pos.mpr Real.goldenRatio_lt_two
  have heq_raw := heq
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [gc, gb, gd] at hgc hgb hgd
  · right; right; right; right; left
    have hid : gc + gb + gd = (2 - Real.goldenRatio) * (l a7 - l a0) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a0,
        golden_inv]
      simp [a0]
      ring
    rw [heq] at hid
    have hsum : 1 * gc + 1 * gb + 1 * gd = 0 := by simpa using hid
    obtain ⟨hc0, hb0, _⟩ :=
      weighted_terms_eq_zero hgc hgb hgd (by positivity) (by positivity) (by positivity) hsum
    have hc0' : l a7 - l c3D = 0 := by simpa using hc0
    have hb0' : l a7 - l b3 = 0 := by simpa using hb0
    exact ⟨(sub_eq_zero.mp hc0').symm, (sub_eq_zero.mp hb0').symm⟩
  · right; right; right; right; left
    have hid :
      (Real.goldenRatio - 1) * gc + 1 * gb + (2 - Real.goldenRatio) * gd =
        (2 - Real.goldenRatio) * (l a7 - l a1) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a1,
        golden_inv]
      simp [a1] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (Real.goldenRatio - 1) * gc + 1 * gb + (2 - Real.goldenRatio) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp1 (by norm_num) hp2.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid :
      (2 - Real.goldenRatio) * gc + (Real.goldenRatio - 1) * gb + 1 * gd =
        (2 - Real.goldenRatio) * (l a7 - l a2) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a2,
        golden_inv]
      simp [a2] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - Real.goldenRatio) * gc + (Real.goldenRatio - 1) * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp2 hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; right
    have hid :
      0 * gc + (Real.goldenRatio - 1) * gb + (2 - Real.goldenRatio) * gd =
        (2 - Real.goldenRatio) * (l a7 - l a3) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a3,
        golden_inv]
      simp [a3] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 0 * gc + (Real.goldenRatio - 1) * gb + (2 - Real.goldenRatio) * gd = 0 := by
      simpa using hid
    obtain ⟨hb0, hd0⟩ := weighted_last_two_eq_zero hgc hgb hgd (by norm_num) hp1 hp2 hsum
    change l a7 - l b3 = 0 at hb0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hb0).symm, (sub_eq_zero.mp hd0).symm⟩
  · right; right; right; right; left
    have hid :
      1 * gc + (2 - Real.goldenRatio) * gb + (Real.goldenRatio - 1) * gd =
        (2 - Real.goldenRatio) * (l a7 - l a4) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a4,
        golden_inv]
      simp [a4] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (2 - Real.goldenRatio) * gb + (Real.goldenRatio - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd (by norm_num) hp2 hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid :
      (Real.goldenRatio - 1) * gc + (2 - Real.goldenRatio) * gb + 0 * gd =
        (2 - Real.goldenRatio) * (l a7 - l a5) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a5,
        golden_inv]
      simp [a5] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (Real.goldenRatio - 1) * gc + (2 - Real.goldenRatio) * gb + 0 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp1 hp2 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; left
    have hid :
      (2 - Real.goldenRatio) * gc + 0 * gb + (Real.goldenRatio - 1) * gd =
        (2 - Real.goldenRatio) * (l a7 - l a6) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_apply_coords l a6,
        golden_inv]
      simp [a6] <;> ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - Real.goldenRatio) * gc + 0 * gb + (Real.goldenRatio - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hd0⟩ := weighted_first_third_eq_zero hgc hgb hgd hp2 (by norm_num) hp1 hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hd0).symm⟩
  · exact Or.inl rfl
  · right; right; right; right; left
    have hid :
      1 * gc + (Real.goldenRatio - 1) * gb + 1 * gd = (2 - Real.goldenRatio) * (l a7 - l b0) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_b0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (Real.goldenRatio - 1) * gb + 1 * gd = 0 := by simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd (by norm_num) hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid :
      (2 - Real.goldenRatio) * gc + (Real.goldenRatio - 1) * gb + 0 * gd =
        (2 - Real.goldenRatio) * (l a7 - l b1) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_b1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - Real.goldenRatio) * gc + (Real.goldenRatio - 1) * gb + 0 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp2 hp1 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid :
      (Real.goldenRatio - 1) * gc + (2 - Real.goldenRatio) * gb + 1 * gd =
        (2 - Real.goldenRatio) * (l a7 - l b2) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_b2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (Real.goldenRatio - 1) * gc + (2 - Real.goldenRatio) * gb + 1 * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp1 hp2 (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, heq_raw⟩))
  · right; right; right; right; left
    have hid :
      (Real.goldenRatio - 1) * gc + 1 * gb + 1 * gd = (2 - Real.goldenRatio) * (l a7 - l c0D) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_c0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (Real.goldenRatio - 1) * gc + 1 * gb + 1 * gd = 0 := by simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp1 (by norm_num) (by norm_num) hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; left
    have hid :
      (2 - Real.goldenRatio) * gc + 1 * gb + (Real.goldenRatio - 1) * gd =
        (2 - Real.goldenRatio) * (l a7 - l c1D) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_c1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (2 - Real.goldenRatio) * gc + 1 * gb + (Real.goldenRatio - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd hp2 (by norm_num) hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; left
    have hid :
      (Real.goldenRatio - 1) * gc + 0 * gb + (2 - Real.goldenRatio) * gd =
        (2 - Real.goldenRatio) * (l a7 - l c2D) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_c2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : (Real.goldenRatio - 1) * gc + 0 * gb + (2 - Real.goldenRatio) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hd0⟩ := weighted_first_third_eq_zero hgc hgb hgd hp1 (by norm_num) hp2 hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hd0).symm⟩
  · exact Or.inr (Or.inl ⟨rfl, heq_raw⟩)
  · right; right; right; right; left
    have hid :
      1 * gc + 1 * gb + (Real.goldenRatio - 1) * gd = (2 - Real.goldenRatio) * (l a7 - l d0) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_d0, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + 1 * gb + (Real.goldenRatio - 1) * gd = 0 := by simpa using hid
    obtain ⟨hc0, hb0⟩ :=
      weighted_first_two_eq_zero hgc hgb hgd (by norm_num) (by norm_num) hp1.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · right; right; right; right; right; right
    have hid :
      0 * gc + (2 - Real.goldenRatio) * gb + (Real.goldenRatio - 1) * gd =
        (2 - Real.goldenRatio) * (l a7 - l d1D) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_d1, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 0 * gc + (2 - Real.goldenRatio) * gb + (Real.goldenRatio - 1) * gd = 0 := by
      simpa using hid
    obtain ⟨hb0, hd0⟩ := weighted_last_two_eq_zero hgc hgb hgd (by norm_num) hp2 hp1 hsum
    change l a7 - l b3 = 0 at hb0
    change l a7 - l d3 = 0 at hd0
    exact ⟨(sub_eq_zero.mp hb0).symm, (sub_eq_zero.mp hd0).symm⟩
  · right; right; right; right; left
    have hid :
      1 * gc + (Real.goldenRatio - 1) * gb + (2 - Real.goldenRatio) * gd =
        (2 - Real.goldenRatio) * (l a7 - l d2D) :=
      by
      dsimp [gc, gb, gd]
      rw [functional_a7, functional_c3, functional_b3, functional_d3, functional_d2, golden_inv]
      ring_nf <;> (try rw [Real.sq_sqrt (by norm_num)]) <;> ring
    rw [heq] at hid
    have hsum : 1 * gc + (Real.goldenRatio - 1) * gb + (2 - Real.goldenRatio) * gd = 0 := by
      simpa using hid
    obtain ⟨hc0, hb0⟩ := weighted_first_two_eq_zero hgc hgb hgd (by norm_num) hp1 hp2.le hsum
    change l a7 - l c3D = 0 at hc0
    change l a7 - l b3 = 0 at hb0
    exact ⟨(sub_eq_zero.mp hc0).symm, (sub_eq_zero.mp hb0).symm⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, heq_raw⟩)))


-- @@ L1461-1471 expanded
theorem golden_pair_solve (A B C : ℝ)
    (h₁ : (Real.goldenRatio - 1) * A - B + (Real.goldenRatio - 2) * C = 0)
    (h₂ : -A + (Real.goldenRatio - 2) * B + (Real.goldenRatio - 1) * C = 0) :
    B = 0 ∧ C = Real.goldenRatio * A :=
  by
  have hs : Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 := by nlinarith [Real.goldenRatio_sq]
  constructor
  · linear_combination (-Real.goldenRatio / 2) * h₁ - (1 / 2) * h₂ + ((A + C) / 2) * hs
  · linear_combination (-1 / 2) * h₁ + ((1 + Real.goldenRatio) / 2) * h₂ - ((B + C) / 2) * hs


-- @@ L1473-1485 expanded
theorem functional_shape₀ (l : E3 →L[ℝ] ℝ) (hc : l c3D = l a7) (hb : l b3 = l a7) :
    ∀ z : E3, l z = l e₀ * (z 0 + Real.goldenRatio * z 2) :=
  by
  have ec : (Real.goldenRatio - 1) * l e₀ - l e₁ + (Real.goldenRatio - 2) * l e₂ = 0 :=
    by
    rw [functional_c3, functional_a7, golden_inv] at hc
    linarith
  have eb : -l e₀ + (Real.goldenRatio - 2) * l e₁ + (Real.goldenRatio - 1) * l e₂ = 0 :=
    by
    rw [functional_b3, functional_a7, golden_inv] at hb
    linarith
  obtain ⟨h1, h2⟩ := golden_pair_solve (l e₀) (l e₁) (l e₂) ec eb
  intro z
  rw [functional_apply_coords, h1, h2]
  ring


-- @@ L1487-1500 expanded
theorem functional_shape₁ (l : E3 →L[ℝ] ℝ) (hc : l c3D = l a7) (hd : l d3 = l a7) :
    ∀ z : E3, l z = l e₁ * (Real.goldenRatio * z 0 + z 1) :=
  by
  have ec : (Real.goldenRatio - 1) * l e₀ - l e₁ + (Real.goldenRatio - 2) * l e₂ = 0 :=
    by
    rw [functional_c3, functional_a7, golden_inv] at hc
    linarith
  have ed : (Real.goldenRatio - 2) * l e₀ + (Real.goldenRatio - 1) * l e₁ - l e₂ = 0 :=
    by
    rw [functional_d3, functional_a7, golden_inv] at hd
    linarith
  obtain ⟨h2, h0⟩ := golden_pair_solve (l e₁) (l e₂) (l e₀) (by linarith [ed]) (by linarith [ec])
  intro z
  rw [functional_apply_coords, h2, h0]
  ring


-- @@ L1502-1515 expanded
theorem functional_shape₂ (l : E3 →L[ℝ] ℝ) (hb : l b3 = l a7) (hd : l d3 = l a7) :
    ∀ z : E3, l z = l e₂ * (Real.goldenRatio * z 1 + z 2) :=
  by
  have eb : -l e₀ + (Real.goldenRatio - 2) * l e₁ + (Real.goldenRatio - 1) * l e₂ = 0 :=
    by
    rw [functional_b3, functional_a7, golden_inv] at hb
    linarith
  have ed : (Real.goldenRatio - 2) * l e₀ + (Real.goldenRatio - 1) * l e₁ - l e₂ = 0 :=
    by
    rw [functional_d3, functional_a7, golden_inv] at hd
    linarith
  obtain ⟨h0, h1⟩ := golden_pair_solve (l e₂) (l e₀) (l e₁) (by linarith [eb]) (by linarith [ed])
  intro z
  rw [functional_apply_coords, h0, h1]
  ring


-- @@ L1517-1524 expanded
theorem support₁_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    Real.goldenRatio * z 0 + z 1 ≤ Real.goldenRatio + 1 :=
  by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  have h := supportL_polytope_le u hu
  change u 0 + Real.goldenRatio * u 2 ≤ Real.goldenRatio + 1 at h
  change Real.goldenRatio * u 2 + u 0 ≤ Real.goldenRatio + 1
  linarith


-- @@ L1526-1533 expanded
theorem support₂_polytope_le (z : E3) (hz : z ∈ dodecaedro.toSet) :
    Real.goldenRatio * z 1 + z 2 ≤ Real.goldenRatio + 1 :=
  by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  have h := support₁_polytope_le u hu
  change Real.goldenRatio * u 0 + u 1 ≤ Real.goldenRatio + 1 at h
  change Real.goldenRatio * u 0 + u 1 ≤ Real.goldenRatio + 1
  exact h


-- @@ L1535-1542 expanded
theorem mem_F₁_of_mem_polytope_support₁_eq (z : E3) (hz : z ∈ dodecaedro.toSet)
    (heq : Real.goldenRatio * z 0 + z 1 = Real.goldenRatio + 1) : z ∈ F₁ :=
  by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  refine ⟨u, mem_F₀_of_mem_polytope_support_eq u hu ?_, rfl⟩
  change Real.goldenRatio * u 2 + u 0 = Real.goldenRatio + 1 at heq
  change u 0 + Real.goldenRatio * u 2 = Real.goldenRatio + 1
  linarith


-- @@ L1544-1550 expanded
theorem mem_F₂_of_mem_polytope_support₂_eq (z : E3) (hz : z ∈ dodecaedro.toSet)
    (heq : Real.goldenRatio * z 1 + z 2 = Real.goldenRatio + 1) : z ∈ F₂ :=
  by
  obtain ⟨u, rfl⟩ := σ.surjective z
  have hu : u ∈ dodecaedro.toSet := (sigma_mem_polytope_iff u).1 hz
  refine ⟨u, mem_F₁_of_mem_polytope_support₁_eq u hu ?_, rfl⟩
  change Real.goldenRatio * u 0 + u 1 = Real.goldenRatio + 1 at heq
  exact heq


-- @@ L1552-1556 verbatim
theorem dodecaedro_toSet_finrank :
    Module.finrank ℝ (vectorSpan ℝ dodecaedro.toSet) = 3 := by
  rw [FiniteConvexPolytope.toSet, ← direction_affineSpan,
    affineSpan_convexHull, direction_affineSpan]
  exact dodecaedro_finrank


-- @@ L1558-1797 expanded
theorem incident_facet_classification {F : Set E3} (hF : dodecaedro.IsFacet F) (ha7 : a7 ∈ F) :
    ∃ i : Fin 3, F = fanFace i := by
  classical
  obtain ⟨l, hFl⟩ := hF.1.1 hF.1.2
  have haChar : a7 ∈ {x ∈ dodecaedro.toSet | ∀ y ∈ dodecaedro.toSet, l y ≤ l x} :=
    by
    rw [← hFl]
    exact ha7
  have hmaxP : ∀ y ∈ dodecaedro.toSet, l y ≤ l a7 := haChar.2
  have hmaxV : ∀ y ∈ verticiDodeca, l y ≤ l a7 :=
    by
    intro y hy
    apply hmaxP y
    exact subset_convexHull ℝ (verticiDodeca : Set E3) hy
  have vertex_mem_iff (y : E3) (hy : y ∈ verticiDodeca) : y ∈ F ↔ l y = l a7 :=
    by
    rw [hFl]
    constructor
    · intro h
      apply le_antisymm (hmaxV y hy)
      exact h.2 a7 haChar.1
    · intro heq
      refine ⟨subset_convexHull ℝ (verticiDodeca : Set E3) hy, ?_⟩
      intro z hz
      rw [heq]
      exact hmaxP z hz
  have hlne : l ≠ 0 := by
    intro hl
    have hFP : F = dodecaedro.toSet :=
      by
      apply Set.Subset.antisymm hF.1.1.subset
      intro z hz
      rw [hFl]
      refine ⟨hz, ?_⟩
      intro y hy
      simp [hl]
    have hd := hF.2
    rw [hFP, dodecaedro_toSet_finrank] at hd
    omega
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) := dodeca_exposedFace_eq_convexHull_vertices hF.1
  have hdS : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 :=
    by
    have hd := hF.2
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan] at hd
    exact hd
  have rank_small (u : E3) (hu : ∀ y ∈ verticiDodeca, l y = l a7 → y = a7 ∨ y = u) : False :=
    by
    let pair : Fin 2 → E3 := ![a7, u]
    have hsub : (S : Set E3) ⊆ Set.range pair :=
      by
      intro y hy
      have hy' : y ∈ dodecaedro.vertices ∧ y ∈ F := by exact Finset.mem_filter.mp hy
      rcases hu y hy'.1 ((vertex_mem_iff y hy'.1).1 hy'.2) with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    have hmono :
      Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) ≤
        Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    have hp : Module.finrank ℝ (vectorSpan ℝ (Set.range pair)) ≤ 1 :=
      finrank_vectorSpan_range_le ℝ pair (by simp)
    omega
  let hc : Prop := l c3D = l a7
  let hb : Prop := l b3 = l a7
  let hd : Prop := l d3 = l a7
  by_cases hcb : hc ∧ hb
  · have shape := functional_shape₀ l hcb.1 hcb.2
    have htne : l e₀ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l d3 = 2 * l e₀ :=
      by
      rw [shape a7, shape d3]
      norm_num [a7, d3]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₀ :=
      by
      have := sub_nonneg.mpr (hmaxV d3 (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₀D := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change
          l e₀ * ((1 : ℝ) + Real.goldenRatio * 1) ≤ l e₀ * (z 0 + Real.goldenRatio * z 2) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := supportL_polytope_le z hz'.1
        exact
          mem_F₀_of_mem_polytope_support_eq z hz'.1
            (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₀_subset_dodecaedro hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₀_support z hz]
        exact supportL_polytope_le y hy
    exact ⟨0, hEq⟩
  by_cases hcd : hc ∧ hd
  · have shape := functional_shape₁ l hcd.1 hcd.2
    have htne : l e₁ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l b3 = 2 * l e₁ :=
      by
      rw [shape a7, shape b3]
      norm_num [a7, b3]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₁ :=
      by
      have := sub_nonneg.mpr (hmaxV b3 (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₁ := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change
          l e₁ * (Real.goldenRatio * (1 : ℝ) + 1) ≤ l e₁ * (Real.goldenRatio * z 0 + z 1) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := support₁_polytope_le z hz'.1
        exact
          mem_F₁_of_mem_polytope_support₁_eq z hz'.1
            (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₁_isFacet.1.1.subset hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₁_support z hz]
        exact support₁_polytope_le y hy
    exact ⟨1, hEq⟩
  by_cases hbd : hb ∧ hd
  · have shape := functional_shape₂ l hbd.1 hbd.2
    have htne : l e₂ ≠ 0 := by
      intro ht
      apply hlne
      ext z
      rw [shape z, ht]
      simp
    have hgap : l a7 - l c3D = 2 * l e₂ :=
      by
      rw [shape a7, shape c3D]
      norm_num [a7, c3D]
      simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      rw [golden_inv_nf]
      ring
    have htpos : 0 < l e₂ :=
      by
      have := sub_nonneg.mpr (hmaxV c3D (by simp [verticiDodeca]))
      rw [hgap] at this
      exact lt_of_le_of_ne (by linarith) (Ne.symm htne)
    have hEq : F = F₂ := by
      ext z
      constructor
      · intro hz
        have hz' := hz
        rw [hFl] at hz'
        have hloRaw := hz'.2 a7 haChar.1
        rw [shape a7, shape z] at hloRaw
        change
          l e₂ * (Real.goldenRatio * (1 : ℝ) + 1) ≤ l e₂ * (Real.goldenRatio * z 1 + z 2) at hloRaw
        have hlo := (mul_le_mul_iff_right₀ htpos).mp hloRaw
        have hhi := support₂_polytope_le z hz'.1
        exact
          mem_F₂_of_mem_polytope_support₂_eq z hz'.1
            (le_antisymm hhi (by norm_num at hlo ⊢; linarith))
      · intro hz
        rw [hFl]
        refine ⟨F₂_isFacet.1.1.subset hz, ?_⟩
        intro y hy
        rw [shape y, shape z]
        apply (mul_le_mul_iff_right₀ htpos).2
        rw [mem_F₂_support z hz]
        exact support₂_polytope_le y hy
    exact ⟨2, hEq⟩
  exfalso
  by_cases hc0 : hc
  · apply rank_small c3D
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.1
    · exact (hcb ⟨hc0, h.2⟩).elim
    · exact (hcd ⟨hc0, h.2⟩).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
  by_cases hb0 : hb
  · apply rank_small b3
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact Or.inr h.1
    · exact (hbd ⟨hb0, h.2⟩).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
  by_cases hd0 : hd
  · apply rank_small d3
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact (hb0 h.2).elim
    · exact Or.inr h.1
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim
  · apply rank_small a7
    intro y hy hyeq
    rcases local_maximizer_dichotomy l hmaxV y hy hyeq with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hc0 h.2).elim
    · exact (hb0 h.2).elim
    · exact (hd0 h.2).elim
    · exact (hcb h).elim
    · exact (hcd h).elim
    · exact (hbd h).elim


-- @@ L1798-1810 verbatim
theorem fanFace_spigolo_due (i j : Fin 3) (z : E3)
    (hz : z ∈ fanFace i ∩ fanFace (finRotate 3 i)) (hz_ne : z ≠ a7)
    (hzj : z ∈ fanFace j) : j = i ∨ j = finRotate 3 i := by
  by_cases hji : j = i
  · exact Or.inl hji
  by_cases hjr : j = finRotate 3 i
  · exact Or.inr hjr
  exfalso
  apply hz_ne
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact three_fan_faces_meet_at_a7 z hz.1 hz.2 hzj
  · exact three_fan_faces_meet_at_a7 z hzj hz.1 hz.2
  · exact three_fan_faces_meet_at_a7 z hz.2 hzj hz.1


-- @@ L1812-1829 verbatim
def dodecaCyclicData : dodecaedro.CyclicVertexData a7 3 where
  faccetta := fanFace
  isFacet i := by
    fin_cases i
    · exact F₀_isFacet
    · exact F₁_isFacet
    · exact F₂_isFacet
  mem_v := a7_mem_fanFace
  distinte := fanFace_injective
  complete := by
    intro F hF ha
    exact incident_facet_classification hF ha
  σ := σ
  fissa_v := sigma_a7
  preserva := sigma_preserves_polytope
  ruota := sigma_image_fanFace
  spigolo := fanFace_spigolo
  spigolo_due := fanFace_spigolo_due


-- @@ L1831-1832 verbatim
theorem a7_vertice_ciclico : dodecaedro.IsCyclicVertex a7 3 :=
  ⟨dodecaCyclicData⟩


-- @@ L1834-1834 verbatim
def v₀ : E3 := WithLp.toLp 2 ![1, 1, 1]


-- @@ L1836-1838 verbatim
theorem vertice_ciclico : dodecaedro.IsCyclicVertex v₀ 3 := by
  change dodecaedro.IsCyclicVertex a7 3
  exact a7_vertice_ciclico


-- @@ L1840-1840 verbatim
/-! ## Simmetrie globali e transitività sui venti vertici -/


-- @@ L1842-1846 verbatim
/-- Riflessione nella coordinata `x`. -/
def segnoXD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]


-- @@ L1848-1852 verbatim
/-- Riflessione nella coordinata `y`. -/
def segnoYD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]


-- @@ L1854-1858 verbatim
/-- Riflessione nella coordinata `z`. -/
def segnoZD : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]


-- @@ L1860-1860 verbatim
def τx : E3 ≃ᵃⁱ[ℝ] E3 := segnoXD.toAffineIsometryEquiv

-- @@ L1861-1861 verbatim
def τy : E3 ≃ᵃⁱ[ℝ] E3 := segnoYD.toAffineIsometryEquiv

-- @@ L1862-1862 verbatim
def τz : E3 ≃ᵃⁱ[ℝ] E3 := segnoZD.toAffineIsometryEquiv


-- @@ L1864-1864 verbatim
@[simp] theorem tauX_zero (z : E3) : τx z 0 = -z 0 := rfl

-- @@ L1865-1865 verbatim
@[simp] theorem tauX_one (z : E3) : τx z 1 = z 1 := rfl

-- @@ L1866-1866 verbatim
@[simp] theorem tauX_two (z : E3) : τx z 2 = z 2 := rfl

-- @@ L1867-1867 verbatim
@[simp] theorem tauY_zero (z : E3) : τy z 0 = z 0 := rfl

-- @@ L1868-1868 verbatim
@[simp] theorem tauY_one (z : E3) : τy z 1 = -z 1 := rfl

-- @@ L1869-1869 verbatim
@[simp] theorem tauY_two (z : E3) : τy z 2 = z 2 := rfl

-- @@ L1870-1870 verbatim
@[simp] theorem tauZ_zero (z : E3) : τz z 0 = z 0 := rfl

-- @@ L1871-1871 verbatim
@[simp] theorem tauZ_one (z : E3) : τz z 1 = z 1 := rfl

-- @@ L1872-1872 verbatim
@[simp] theorem tauZ_two (z : E3) : τz z 2 = -z 2 := rfl


-- @@ L1874-1876 verbatim
theorem tauX_formula (z : E3) :
    τx z = WithLp.toLp 2 ![-z 0, z 1, z 2] := by
  apply E3_ext <;> rfl


-- @@ L1878-1880 verbatim
theorem tauY_formula (z : E3) :
    τy z = WithLp.toLp 2 ![z 0, -z 1, z 2] := by
  apply E3_ext <;> rfl


-- @@ L1882-1884 verbatim
theorem tauZ_formula (z : E3) :
    τz z = WithLp.toLp 2 ![z 0, z 1, -z 2] := by
  apply E3_ext <;> rfl


-- @@ L1886-1894 verbatim
/-- Un'iniezione del finito insieme dei vertici in sé è una permutazione. -/
theorem image_verticiDodeca_eq_of_maps (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hmap : ∀ v ∈ verticiDodeca, g v ∈ verticiDodeca) :
    (⇑g) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  · rw [Set.ncard_image_of_injective _ g.injective]
  · exact verticiDodeca.finite_toSet


-- @@ L1896-1905 verbatim
/-- Una simmetria affine che permuta i vertici preserva il dodecaedro. -/
theorem preserves_dodecaedro_of_image_vertices (g : E3 ≃ᵃⁱ[ℝ] E3)
    (hv : (⇑g) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3)) :
    (⇑g) '' dodecaedro.toSet = dodecaedro.toSet := by
  show (⇑g) '' convexHull ℝ (verticiDodeca : Set E3) =
    convexHull ℝ (verticiDodeca : Set E3)
  have haff : (⇑g) '' convexHull ℝ (verticiDodeca : Set E3) =
      convexHull ℝ ((⇑g) '' (verticiDodeca : Set E3)) :=
    AffineMap.image_convexHull g.toAffineIsometry.toAffineMap _
  rw [haff, hv]


-- @@ L1907-1913 verbatim
theorem tauX_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τx v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauX_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]


-- @@ L1915-1921 verbatim
theorem tauY_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τy v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauY_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]


-- @@ L1923-1929 verbatim
theorem tauZ_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    τz v ∈ verticiDodeca := by
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [tauZ_formula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]


-- @@ L1931-1933 verbatim
theorem tauX_image_vertices :
    (⇑τx) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τx tauX_vertices


-- @@ L1935-1937 verbatim
theorem tauY_image_vertices :
    (⇑τy) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τy tauY_vertices


-- @@ L1939-1941 verbatim
theorem tauZ_image_vertices :
    (⇑τz) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps τz tauZ_vertices


-- @@ L1943-1944 verbatim
theorem tauX_preserves_polytope : (⇑τx) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τx tauX_image_vertices


-- @@ L1946-1947 verbatim
theorem tauY_preserves_polytope : (⇑τy) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τy tauY_image_vertices


-- @@ L1949-1950 verbatim
theorem tauZ_preserves_polytope : (⇑τz) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices τz tauZ_image_vertices


-- @@ L1952-1969 verbatim
set_option maxHeartbeats 1000000 in
/-- Tabella completa dell'azione della rotazione aurea sui vertici. -/
theorem rho_vertex_actions :
    ρ a0 = b0 ∧ ρ a1 = d2D ∧ ρ a2 = c0D ∧ ρ a3 = a1 ∧
    ρ a4 = a6 ∧ ρ a5 = c3D ∧ ρ a6 = d1D ∧ ρ a7 = b3 ∧
    ρ b0 = b2 ∧ ρ b1 = a5 ∧ ρ b2 = a2 ∧ ρ b3 = b1 ∧
    ρ c0D = a0 ∧ ρ c1D = d0 ∧ ρ c2D = d3 ∧ ρ c3D = a7 ∧
    ρ d0 = a4 ∧ ρ d1D = c1D ∧ ρ d2D = c2D ∧ ρ d3 = a3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply E3_ext
  all_goals norm_num [rhoFormula, a0, a1, a2, a3, a4, a5, a6, a7,
    b0, b1, b2, b3, c0D, c1D, c2D, c3D, d0, d1D, d2D, d3]
  all_goals simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  all_goals rw [golden_inv_nf] at *
  all_goals try simp only [golden_den_self] at *
  all_goals nlinarith [golden_sqrt_five, Real.goldenRatio_sq]


-- @@ L1971-1980 verbatim
theorem rho_vertices (v : E3) (hv : v ∈ verticiDodeca) :
    ρ v ∈ verticiDodeca := by
  rcases rho_vertex_actions with
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3⟩
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3]


-- @@ L1982-1984 verbatim
theorem rho_image_vertices :
    (⇑ρ) '' (verticiDodeca : Set E3) = (verticiDodeca : Set E3) :=
  image_verticiDodeca_eq_of_maps ρ rho_vertices


-- @@ L1986-1987 verbatim
theorem rho_preserves_polytope : (⇑ρ) '' dodecaedro.toSet = dodecaedro.toSet :=
  preserves_dodecaedro_of_image_vertices ρ rho_image_vertices


-- @@ L1989-1998 verbatim
/-- La preservazione del politopo è stabile per composizione. -/
theorem preserves_trans (f g : E3 ≃ᵃⁱ[ℝ] E3)
    (hf : (⇑f) '' dodecaedro.toSet = dodecaedro.toSet)
    (hg : (⇑g) '' dodecaedro.toSet = dodecaedro.toSet) :
    (⇑(f.trans g)) '' dodecaedro.toSet = dodecaedro.toSet := by
  rw [show (⇑(f.trans g)) '' dodecaedro.toSet =
      (⇑g) '' ((⇑f) '' dodecaedro.toSet) by
        rw [← Set.image_comp]
        rfl,
    hf, hg]


-- @@ L2000-2001 verbatim
theorem rho_a7_eq_b3 : ρ a7 = b3 := by
  simpa [x0, x1] using rho_x0


-- @@ L2003-2090 verbatim
/-- Per ogni vertice, una simmetria globale che vi porta il vertice base. -/
theorem dodecaedro_vertex_transitive (v : E3) (hv : v ∈ dodecaedro.vertices) :
    ∃ g : E3 ≃ᵃⁱ[ℝ] E3,
      (⇑g) '' dodecaedro.toSet = dodecaedro.toSet ∧ g v₀ = v := by
  have hxy := preserves_trans τx τy tauX_preserves_polytope tauY_preserves_polytope
  have hxz := preserves_trans τx τz tauX_preserves_polytope tauZ_preserves_polytope
  have hyz := preserves_trans τy τz tauY_preserves_polytope tauZ_preserves_polytope
  have hxyz := preserves_trans (τx.trans τy) τz hxy tauZ_preserves_polytope
  have hB := rho_preserves_polytope
  have hBy := preserves_trans ρ τy hB tauY_preserves_polytope
  have hBz := preserves_trans ρ τz hB tauZ_preserves_polytope
  have hByz := preserves_trans (ρ.trans τy) τz hBy tauZ_preserves_polytope
  have hC := preserves_trans ρ σ hB sigma_preserves_polytope
  have hCx := preserves_trans (ρ.trans σ) τx hC tauX_preserves_polytope
  have hCz := preserves_trans (ρ.trans σ) τz hC tauZ_preserves_polytope
  have hCxz := preserves_trans ((ρ.trans σ).trans τx) τz hCx tauZ_preserves_polytope
  have hD := preserves_trans (ρ.trans σ) σ hC sigma_preserves_polytope
  have hDx := preserves_trans ((ρ.trans σ).trans σ) τx hD tauX_preserves_polytope
  have hDy := preserves_trans ((ρ.trans σ).trans σ) τy hD tauY_preserves_polytope
  have hDxy := preserves_trans (((ρ.trans σ).trans σ).trans τx) τy hDx
    tauY_preserves_polytope
  have hbaseB : ρ v₀ = b3 := by
    change ρ a7 = b3
    exact rho_a7_eq_b3
  have hbaseC : σ (ρ v₀) = c3D := by
    rw [hbaseB]
    apply E3_ext <;> simp [c3D, b3]
  have hbaseD : σ (σ (ρ v₀)) = d3 := by
    rw [hbaseC]
    apply E3_ext <;> simp [d3, c3D]
  change v ∈ verticiDodeca at hv
  simp only [verticiDodeca, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(τx.trans τy).trans τz, hxyz, by
      apply E3_ext <;> simp [v₀, a0, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx.trans τy, hxy, by
      apply E3_ext <;> simp [v₀, a1, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx.trans τz, hxz, by
      apply E3_ext <;> simp [v₀, a2, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τx, tauX_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a3]⟩
  · exact ⟨τy.trans τz, hyz, by
      apply E3_ext <;> simp [v₀, a4, AffineIsometryEquiv.coe_trans, Function.comp]⟩
  · exact ⟨τy, tauY_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a5]⟩
  · exact ⟨τz, tauZ_preserves_polytope, by
      apply E3_ext <;> simp [v₀, a6]⟩
  · exact ⟨σ, sigma_preserves_polytope, by simpa [v₀, a7] using sigma_a7⟩
  · exact ⟨(ρ.trans τy).trans τz, hByz, by
      show τz (τy (ρ v₀)) = b0
      rw [hbaseB]
      apply E3_ext <;> simp [b0, b3]⟩
  · exact ⟨ρ.trans τy, hBy, by
      show τy (ρ v₀) = b1
      rw [hbaseB]
      apply E3_ext <;> simp [b1, b3]⟩
  · exact ⟨ρ.trans τz, hBz, by
      show τz (ρ v₀) = b2
      rw [hbaseB]
      apply E3_ext <;> simp [b2, b3]⟩
  · exact ⟨ρ, hB, hbaseB⟩
  · exact ⟨((ρ.trans σ).trans τx).trans τz, hCxz, by
      show τz (τx (σ (ρ v₀))) = c0D
      rw [hbaseC]
      apply E3_ext <;> simp [c0D, c3D]⟩
  · exact ⟨(ρ.trans σ).trans τx, hCx, by
      show τx (σ (ρ v₀)) = c1D
      rw [hbaseC]
      apply E3_ext <;> simp [c1D, c3D]⟩
  · exact ⟨(ρ.trans σ).trans τz, hCz, by
      show τz (σ (ρ v₀)) = c2D
      rw [hbaseC]
      apply E3_ext <;> simp [c2D, c3D]⟩
  · exact ⟨ρ.trans σ, hC, hbaseC⟩
  · exact ⟨(((ρ.trans σ).trans σ).trans τx).trans τy, hDxy, by
      show τy (τx (σ (σ (ρ v₀)))) = d0
      rw [hbaseD]
      apply E3_ext <;> simp [d0, d3]⟩
  · exact ⟨((ρ.trans σ).trans σ).trans τx, hDx, by
      show τx (σ (σ (ρ v₀))) = d1D
      rw [hbaseD]
      apply E3_ext <;> simp [d1D, d3]⟩
  · exact ⟨((ρ.trans σ).trans σ).trans τy, hDy, by
      show τy (σ (σ (ρ v₀))) = d2D
      rw [hbaseD]
      apply E3_ext <;> simp [d2D, d3]⟩
  · exact ⟨(ρ.trans σ).trans σ, hD, hbaseD⟩


-- @@ L2092-2092 verbatim
/-! ## Assemblaggio globale -/


-- @@ L2094-2107 verbatim
/-- Le tre faccette del fan base sono pentagoni regolari dello stesso lato. -/
theorem fanFace_regular (i : Fin 3) :
    dodecaedro.IsRegularFacet (fanFace i) 5 ℓ₀ := by
  fin_cases i
  · exact faccia_dodecaedro_regolare
  · simpa [fanFace, F₁] using
      (FiniteConvexPolytope.isRegularFacet_image dodecaedro σ
        sigma_preserves_polytope faccia_dodecaedro_regolare)
  · have hF₁ : dodecaedro.IsRegularFacet F₁ 5 ℓ₀ := by
      exact FiniteConvexPolytope.isRegularFacet_image dodecaedro σ
        sigma_preserves_polytope faccia_dodecaedro_regolare
    simpa [fanFace, F₂] using
      (FiniteConvexPolytope.isRegularFacet_image dodecaedro σ
        sigma_preserves_polytope hF₁)


-- @@ L2109-2126 verbatim
/-- Ogni faccetta non vuota contiene almeno un vertice dichiarato. -/
theorem dodecaedro_facet_contains_vertex {F : Set E3}
    (hF : dodecaedro.IsFacet F) :
    ∃ v, v ∈ dodecaedro.vertices ∧ v ∈ F := by
  classical
  let S : Finset E3 := dodecaedro.vertices.filter (· ∈ F)
  have hS : S.Nonempty := by
    by_contra hne
    have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hEq := dodeca_exposedFace_eq_convexHull_vertices hF.1
    change F = convexHull ℝ (S : Set E3) at hEq
    rw [hS0] at hEq
    simp only [Finset.coe_empty, convexHull_empty] at hEq
    exact hF.1.2.ne_empty hEq
  obtain ⟨v, hv⟩ := hS
  have hv' : v ∈ dodecaedro.vertices ∧ v ∈ F := by
    simpa [S] using hv
  exact ⟨v, hv'⟩


-- @@ L2128-2151 verbatim
/-- Tutte le faccette del dodecaedro sono pentagoni regolari di lato `ℓ₀`. -/
theorem dodecaedro_facets_regular :
    ∀ F, dodecaedro.IsFacet F → dodecaedro.IsRegularFacet F 5 ℓ₀ := by
  intro F hF
  obtain ⟨v, hvV, hvF⟩ := dodecaedro_facet_contains_vertex hF
  obtain ⟨g, hg, hgv⟩ := dodecaedro_vertex_transitive v hvV
  have hgsymm : (⇑g.symm) '' dodecaedro.toSet = dodecaedro.toSet :=
    FiniteConvexPolytope.preserva_symm g hg
  have hF' : dodecaedro.IsFacet ((⇑g.symm) '' F) :=
    FiniteConvexPolytope.isFacet_image dodecaedro g.symm hgsymm hF
  have hv₀F' : v₀ ∈ (⇑g.symm) '' F := by
    refine ⟨v, hvF, ?_⟩
    rw [← hgv, g.symm_apply_apply]
  have ha7F' : a7 ∈ (⇑g.symm) '' F := by
    exact hv₀F'
  obtain ⟨i, hi⟩ := incident_facet_classification hF' ha7F'
  have hreg : dodecaedro.IsRegularFacet ((⇑g.symm) '' F) 5 ℓ₀ := by
    rw [hi]
    exact fanFace_regular i
  have himg := FiniteConvexPolytope.isRegularFacet_image dodecaedro g hg hreg
  have hcancel : (⇑g) '' ((⇑g.symm) '' F) = F := by
    rw [Set.image_image]
    simp
  rwa [hcancel] at himg


-- @@ L2153-2160 verbatim
/-- Tutti i venti vertici sono 3-ciclici. -/
theorem dodecaedro_vertices_cyclic :
    ∀ v ∈ dodecaedro.vertices, dodecaedro.IsCyclicVertex v 3 := by
  intro v hv
  obtain ⟨g, hg, hgv⟩ := dodecaedro_vertex_transitive v hv
  have himg := FiniteConvexPolytope.isCyclicVertex_image dodecaedro g hg
    vertice_ciclico
  rwa [hgv] at himg


-- @@ L2162-2167 verbatim
/-- IL DODECAEDRO È CICLICAMENTE REGOLARE DI TIPO `(5,3)`. -/
theorem dodecaedro_cyclicallyRegular :
    dodecaedro.IsCyclicallyRegularOfType 5 3 := by
  refine ⟨dodecaedro_finrank, by norm_num, by norm_num, ℓ₀, ℓ₀_pos, ?_, ?_⟩
  · exact dodecaedro_facets_regular
  · exact dodecaedro_vertices_cyclic


-- @@ L2169-2178 verbatim
/-! CONSEGNA

Sono certificati la transitività sui venti vertici, il trasferimento del fan
e della regolarità delle faccette, e il teorema conclusivo
`dodecaedro_cyclicallyRegular : dodecaedro.IsCyclicallyRegularOfType 5 3`.

SHA-256 canonico (tutto il contenuto precedente a questo blocco):
`c00556ea4a0b439bc18f0ead95bdccbadd3948603604a5dc3e12a6b18f547be4`
Compilazione: `lake env lean DodecaedroCompleto.lean` — exit 0, zero errori.
-/
