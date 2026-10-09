import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Real Filter Topology MeasureTheory Polynomial

-- @@ L10-10 verbatim
open Matrix MeasureTheory

-- @@ L11-11 verbatim
open MeasureTheory

-- @@ L12-12 verbatim
open Matrix

-- @@ L13-13 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator

-- @@ L14-14 verbatim
open MeasureTheory Matrix

-- @@ L15-15 verbatim
open scoped TensorProduct

-- @@ L16-16 verbatim
open scoped BigOperators Pointwise Topology

-- @@ L17-17 verbatim
open MeasureTheory Filter

-- @@ L18-18 verbatim
open scoped BigOperators Pointwise

-- @@ L19-19 verbatim
open scoped BigOperators Topology

-- @@ L20-20 verbatim
open scoped TensorProduct BigOperators

-- @@ L21-21 verbatim
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

-- @@ L22-22 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open Set


-- @@ L26-26 verbatim
namespace EuclideanRamsey


-- @@ L28-67 verbatim
theorem fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by
  have hreal := fieldCriterion_realCriterion a h
  have hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,
      Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ) := by
    intro n hn
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hs' : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
    let η : ℝ := 1/(4*n)
    let δ : ℝ := 1/(4*n*s)
    have hη : 0<η := by dsimp [η]; positivity
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨ℓ,hℓ,f,g,hf,hg,hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η hη
    have hq : 0<η/(1+η) := div_pos hη (by linarith)
    obtain ⟨w,lmb,μ,hp,hm,hlmb,hμ,hr⟩ :=
      permutation_equal_endpoints a ha f g (η/(1+η)) δ hq hδ hf hg hperm
    refine ⟨w,lmb,μ,hp,hm,hlmb,lt_of_le_of_lt hr ?_⟩
    have hq' : η/(1+η)<η := (div_lt_iff₀ (by linarith : 0<1+η)).mpr (by nlinarith)
    have he : η+(s:ℝ)*δ=1/(2*n) := by
      dsimp [η,δ]
      field_simp
      ring
    have hhalf : (1:ℝ)/(2*n)<1/n := by
      apply one_div_lt_one_div_of_lt hn'
      nlinarith
    rw [← he] at hhalf
    linarith
  intro r hr
  obtain ⟨D,hD,hmono⟩ := finite_coloring_compactness
    (fun i => FiniteEuclidean.embed d (a i)) r
    (fun c => paths_monochromatic _ hpaths c)
  refine ⟨D,hD,?_⟩
  intro c
  obtain ⟨b,hb,k,hk⟩ := hmono c
  refine ⟨b,?_,k,hk⟩
  intro i j
  rw [dist_eq_norm,dist_eq_norm,hb,← map_sub,LinearIsometry.norm_map]


-- @@ L69-73 verbatim
theorem classification {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    Ramsey a ↔ FieldCriterion a :=
  ⟨ramsey_fieldCriterion a (by omega) hspan,fieldCriterion_ramsey a hs hd ha⟩

-- @@ L74-74 verbatim
end EuclideanRamsey


-- @@ L76-76 verbatim
namespace EuclideanRamsey


-- @@ L78-123 verbatim
theorem full_affine_representative {s D : ℕ} (a : Fin s → Space D)
    (hs : 2 ≤ s) (ha : Function.Injective a) :
    ∃ d : ℕ,1 ≤ d ∧ ∃ b : Fin s → Space d,Function.Injective b ∧
      Congruent a b ∧ affineSpan ℝ (Set.range b)=⊤ := by
  classical
  let i₀ : Fin s := ⟨0,by omega⟩
  let i₁ : Fin s := ⟨1,by omega⟩
  let V : Submodule ℝ (Space D) := Submodule.span ℝ (Set.range (fun i => a i-a i₀))
  have hx (i : Fin s) : a i-a i₀∈V := Submodule.subset_span (Set.mem_range_self i)
  let x (i : Fin s) : V := ⟨a i-a i₀,hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V hx).mpr rfl
  have hpos : 0<Module.finrank ℝ V := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨x i₁,?_⟩
    intro he
    have hv := congrArg (fun z : V => (z : Space D)) he
    change a i₁-a i₀=0 at hv
    have hi := ha (sub_eq_zero.mp hv)
    have hi' := congrArg Fin.val hi
    norm_num [i₀,i₁] at hi'
  let E := (stdOrthonormalBasis ℝ V).repr
  let b : Fin s → Space (Module.finrank ℝ V) := fun i => E (x i)
  have hbspan : Submodule.span ℝ (Set.range b)=⊤ := by
    change Submodule.span ℝ (Set.range (E.toLinearEquiv.toLinearMap ∘ x))=⊤
    rw [Set.range_comp,Submodule.span_image,hxspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr E.surjective
  have hb0 : b i₀=0 := by
    change E (x i₀)=0
    have hx0 : x i₀=0 := by apply Subtype.ext; exact sub_self _
    rw [hx0,map_zero]
  refine ⟨Module.finrank ℝ V,hpos, b,?_,?_,?_⟩
  · intro i j he
    have hx' := E.injective he
    have hv := congrArg (fun z : V => (z : Space D)) hx'
    change a i-a i₀=a j-a i₀ at hv
    exact ha (sub_left_injective hv)
  · intro i j
    change dist (E (x i)) (E (x j))=dist (a i) (a j)
    rw [dist_eq_norm,dist_eq_norm,← map_sub,LinearIsometryEquiv.norm_map]
    change ‖(a i-a i₀)-(a j-a i₀)‖=‖a i-a j‖
    rw [sub_sub_sub_cancel_right]
  · apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨b i₀,subset_affineSpan ℝ (Set.range b) (Set.mem_range_self i₀)⟩).mp
    rw [direction_affineSpan,vectorSpan_range_eq_span_range_vsub_right ℝ b i₀]
    simpa only [vsub_eq_sub,hb0,sub_zero] using hbspan

-- @@ L124-124 verbatim
end EuclideanRamsey


-- @@ L126-126 verbatim
namespace EuclideanRamsey


-- @@ L128-148 verbatim
theorem classification_nonempty {s D : ℕ} (a : Fin s → Space D)
    (hs : 0 < s) (ha : Function.Injective a) :
    Ramsey a ↔ s = 1 ∨ ∃ d : ℕ, 1 ≤ d ∧ ∃ b : Fin s → Space d,
      Function.Injective b ∧ Congruent a b ∧ affineSpan ℝ (Set.range b) = ⊤ ∧
      FieldCriterion b := by
  constructor
  · intro hr
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨d, hd, b, hb, hc, hspan⟩ := full_affine_representative a hs2 ha
      exact Or.inr ⟨d, hd, b, hb, hc, hspan,
        (classification b hs2 hd hb hspan).mp ((ramsey_congruent_iff hc).mp hr)⟩
  · rintro (hs1 | ⟨d, hd, b, hb, hc, hspan, hcrit⟩)
    · subst s
      exact singleton_ramsey a
    · by_cases hs1 : s = 1
      · subst s
        exact singleton_ramsey a
      · exact (ramsey_congruent_iff hc).mpr
          ((classification b (by omega) hd hb hspan).mpr hcrit)

-- @@ L149-149 verbatim
end EuclideanRamsey


-- @@ L151-151 verbatim
end


-- @@ L153-153 verbatim
end OAI
