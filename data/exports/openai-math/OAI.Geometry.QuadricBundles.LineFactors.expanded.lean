import OAI.Geometry.QuadricBundles.Regularity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace QuadricCounterexample

-- @@ L6-6 verbatim
open Set MvPolynomial

-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
abbrev StandardChart := Fin 2 × Fin 2


-- @@ L11-12 verbatim
def overlapPolynomial (i j : StandardChart) : BasePolynomial :=
  (if i.1=j.1 then 1 else X 0)*(if i.2=j.2 then 1 else X 1)

-- @@ L13-14 verbatim
def coordinateOverlap (i j : StandardChart) : Set BaseCoordinates :=
  {z | baseEval (overlapPolynomial i j) z ≠ 0}

-- @@ L15-15 verbatim
def scalarCoordinateChange (i j : Fin 2) (z : ℂ) : ℂ := if i=j then z else z⁻¹

-- @@ L16-17 verbatim
def coordinateChange (i j : StandardChart) (z : BaseCoordinates) : BaseCoordinates :=
  (scalarCoordinateChange i.1 j.1 z.1, scalarCoordinateChange i.2 j.2 z.2)

-- @@ L18-18 verbatim
def scalarFactor (i j : Fin 2) (z : ℂ) : ℂ := if i=j then 1 else z


-- @@ L20-20 verbatim
def firstFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := scalarFactor i.1 j.1 z.1

-- @@ L21-21 verbatim
def secondFactor (i j : StandardChart) (z : BaseCoordinates) : ℂ := scalarFactor i.2 j.2 z.2


-- @@ L23-26 verbatim
lemma coordinateOverlap_iff (i j : StandardChart) (z : BaseCoordinates) :
    z ∈ coordinateOverlap i j ↔ (i.1=j.1 ∨ z.1 ≠ 0) ∧ (i.2=j.2 ∨ z.2 ≠ 0) := by
  simp only [coordinateOverlap,mem_ofPred_eq,overlapPolynomial,baseEval_mul]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [h1,h2,baseEval]


-- @@ L28-38 verbatim
lemma scalarCoordinateChange_coord (i j : Fin 2) (z : ℂ) :
    coordP1 j (affineP1 i z)=scalarCoordinateChange i j z := by
  by_cases hij : i=j
  · subst j; simp [scalarCoordinateChange]
  · fin_cases i <;> fin_cases j <;> simp_all only [not_true_eq_false]
    · by_cases hz : z=0
      · subst z; simp [coordP1,affineP1,scalarCoordinateChange]
      · simp [coordP1,affineP1,scalarCoordinateChange,reciprocalP1_coe hz]
    · by_cases hz : z=0
      · subst z; simp [coordP1,affineP1,scalarCoordinateChange]
      · simp [coordP1,affineP1,scalarCoordinateChange,reciprocalP1_coe hz]


-- @@ L40-42 verbatim
lemma coordinateChange_coord (i j : StandardChart) (z : BaseCoordinates) :
    coordQuadric j (affineQuadric i z)=coordinateChange i j z := by
  ext <;> simp only [coordQuadric,affineQuadric,coordinateChange,scalarCoordinateChange_coord]


-- @@ L44-45 verbatim
@[simp] lemma scalarCoordinateChange_self (i : Fin 2) (z : ℂ) :
    scalarCoordinateChange i i z=z := by simp [scalarCoordinateChange]

-- @@ L46-47 verbatim
@[simp] lemma coordinateChange_self (i : StandardChart) (z : BaseCoordinates) :
    coordinateChange i i z=z := by simp [coordinateChange]

-- @@ L48-50 verbatim
lemma scalarCoordinateChange_inv (i j : Fin 2) (z : ℂ) :
    scalarCoordinateChange j i (scalarCoordinateChange i j z)=z := by
  by_cases h : i=j <;> simp [scalarCoordinateChange,h,eq_comm]

-- @@ L51-53 verbatim
lemma coordinateChange_inv (i j : StandardChart) (z : BaseCoordinates) :
    coordinateChange j i (coordinateChange i j z)=z := by
  ext <;> simp [coordinateChange,scalarCoordinateChange_inv]


-- @@ L55-64 verbatim
lemma affineP1_mem_range (i j : Fin 2) (z : ℂ) :
    affineP1 i z ∈ range (affineP1 j) ↔ i=j ∨ z ≠ 0 := by
  by_cases hij : i=j
  · subst j; exact iff_of_true ⟨z,rfl⟩ (Or.inl rfl)
  · rw [mem_range_affineP1]
    fin_cases i <;> fin_cases j <;> simp_all only [not_true_eq_false]
    · by_cases hz : z=0
      · subst z; simp [affineP1]
      · simp [affineP1,reciprocalP1_coe hz,hz]
    · simp [affineP1]


-- @@ L66-69 verbatim
lemma affineQuadric_mem_range (i j : StandardChart) (z : BaseCoordinates) :
    affineQuadric i z ∈ range (affineQuadric j) ↔ z ∈ coordinateOverlap i j := by
  rw [mem_range_affineQuadric,coordinateOverlap_iff]
  exact and_congr (affineP1_mem_range _ _ _) (affineP1_mem_range _ _ _)


-- @@ L71-75 verbatim
lemma affine_coordinateChange (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) :
    affineQuadric j (coordinateChange i j z)=affineQuadric i z := by
  rw [← coordinateChange_coord]
  exact affineQuadric_coord ((affineQuadric_mem_range i j z).mpr hz)


-- @@ L77-80 verbatim
lemma coordinateOverlap_change (i j : StandardChart) {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) : coordinateChange i j z ∈ coordinateOverlap j i := by
  rw [← affineQuadric_mem_range,affine_coordinateChange i j hz]
  exact ⟨z,rfl⟩


-- @@ L82-85 verbatim
lemma coordinateChange_comp (i j k : StandardChart) {z : BaseCoordinates}
    (hij : z ∈ coordinateOverlap i j) :
    coordinateChange j k (coordinateChange i j z)=coordinateChange i k z := by
  rw [← coordinateChange_coord,affine_coordinateChange i j hij,coordinateChange_coord]


-- @@ L87-91 verbatim
lemma coordinateOverlap_third (i j k : StandardChart) {z : BaseCoordinates}
    (hij : z ∈ coordinateOverlap i j) (hik : z ∈ coordinateOverlap i k) :
    coordinateChange i j z ∈ coordinateOverlap j k := by
  rw [← affineQuadric_mem_range,affine_coordinateChange i j hij]
  exact (affineQuadric_mem_range i k z).mpr hik


-- @@ L93-94 verbatim
lemma coordinateOverlap_open (i j : StandardChart) : IsOpen (coordinateOverlap i j) :=
  isOpen_ne.preimage (analytic_baseEval (overlapPolynomial i j)).continuous


-- @@ L96-97 verbatim
lemma uniformlyRegular_fst (U : Set BaseCoordinates) : UniformlyRegularOn U Prod.fst := by
  exact ⟨X 0,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp [baseEval]⟩

-- @@ L98-99 verbatim
lemma uniformlyRegular_snd (U : Set BaseCoordinates) : UniformlyRegularOn U Prod.snd := by
  exact ⟨X 1,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp [baseEval]⟩


-- @@ L101-116 verbatim
lemma UniformlyRegularOn.comp {U V : Set BaseCoordinates}
    {f : BaseCoordinates → ℂ} {g : BaseCoordinates → BaseCoordinates}
    (hf : UniformlyRegularOn U f)
    (h0 : UniformlyRegularOn V (fun z ↦ (g z).1))
    (h1 : UniformlyRegularOn V (fun z ↦ (g z).2))
    (hg : MapsTo g V U) : UniformlyRegularOn V (fun z ↦ f (g z)) := by
  have hadd (p : BasePolynomial) : UniformlyRegularOn V (fun z ↦ baseEval p (g z)) := by
    have h : ∀ i : Fin 2, UniformlyRegularOn V (fun z ↦ (![ (g z).1,(g z).2 ] : Fin 2 → ℂ) i) := by
      intro i; fin_cases i
      · exact h0
      · exact h1
    exact UniformlyRegularOn.eval h p
  obtain ⟨p,q,hq,h⟩ := hf
  have hn : ∀ z ∈ V, baseEval q (g z) ≠ 0 := fun z hz ↦ hq (g z) (hg hz)
  exact ((hadd p).mul ((hadd q).inv hn)).congr (fun z hz ↦ by
    rw [h (g z) (hg hz),div_eq_mul_inv])


-- @@ L118-123 verbatim
lemma firstFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (firstFactor i j) := by
  unfold firstFactor scalarFactor
  by_cases h : i.1=j.1
  · simpa only [ite_eq_left h] using uniformlyRegular_const U 1
  · simpa only [ite_eq_right h] using uniformlyRegular_fst U

-- @@ L124-129 verbatim
lemma secondFactor_regular (i j : StandardChart) (U : Set BaseCoordinates) :
    UniformlyRegularOn U (secondFactor i j) := by
  unfold secondFactor scalarFactor
  by_cases h : i.2=j.2
  · simpa only [ite_eq_left h] using uniformlyRegular_const U 1
  · simpa only [ite_eq_right h] using uniformlyRegular_snd U


-- @@ L131-137 verbatim
lemma firstFactor_ne_zero {i j : StandardChart} {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) : firstFactor i j z ≠ 0 := by
  have h := ((coordinateOverlap_iff i j z).mp hz).1
  unfold firstFactor scalarFactor
  split_ifs with hi
  · exact one_ne_zero
  · exact h.resolve_left hi

-- @@ L138-144 verbatim
lemma secondFactor_ne_zero {i j : StandardChart} {z : BaseCoordinates}
    (hz : z ∈ coordinateOverlap i j) : secondFactor i j z ≠ 0 := by
  have h := ((coordinateOverlap_iff i j z).mp hz).2
  unfold secondFactor scalarFactor
  split_ifs with hi
  · exact one_ne_zero
  · exact h.resolve_left hi


-- @@ L146-154 verbatim
lemma coordinateChange_fst_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ (coordinateChange i j z).1) := by
  by_cases h : i.1=j.1
  · simpa only [coordinateChange,scalarCoordinateChange,ite_eq_left h] using
      uniformlyRegular_fst (coordinateOverlap i j)
  · have hn : ∀ z ∈ coordinateOverlap i j, z.1 ≠ 0 := fun z hz ↦
      (((coordinateOverlap_iff i j z).mp hz).1).resolve_left h
    simpa only [coordinateChange,scalarCoordinateChange,ite_eq_right h] using
      (uniformlyRegular_fst (coordinateOverlap i j)).inv hn

-- @@ L155-163 verbatim
lemma coordinateChange_snd_regular (i j : StandardChart) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ (coordinateChange i j z).2) := by
  by_cases h : i.2=j.2
  · simpa only [coordinateChange,scalarCoordinateChange,ite_eq_left h] using
      uniformlyRegular_snd (coordinateOverlap i j)
  · have hn : ∀ z ∈ coordinateOverlap i j, z.2 ≠ 0 := fun z hz ↦
      (((coordinateOverlap_iff i j z).mp hz).2).resolve_left h
    simpa only [coordinateChange,scalarCoordinateChange,ite_eq_right h] using
      (uniformlyRegular_snd (coordinateOverlap i j)).inv hn


-- @@ L165-167 verbatim
lemma firstFactor_transition (i j : StandardChart) (z : BaseCoordinates) :
    firstFactor i j z=hyperplaneTransition i.1 j.1 (affineQuadric i z).1 := by
  simp [firstFactor,scalarFactor,hyperplaneTransition,affineQuadric]

-- @@ L168-170 verbatim
lemma secondFactor_transition (i j : StandardChart) (z : BaseCoordinates) :
    secondFactor i j z=hyperplaneTransition i.2 j.2 (affineQuadric i z).2 := by
  simp [secondFactor,scalarFactor,hyperplaneTransition,affineQuadric]


-- @@ L172-179 verbatim
lemma firstFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    firstFactor i j z*firstFactor j k (coordinateChange i j z)=firstFactor i k z := by
  rw [firstFactor_transition,firstFactor_transition,firstFactor_transition,affine_coordinateChange i j hj]
  apply hyperplaneTransition_mul
  · exact ⟨z.1,rfl⟩
  · exact (mem_range_affineQuadric j _).mp ((affineQuadric_mem_range i j z).mpr hj) |>.1
  · exact (mem_range_affineQuadric k _).mp ((affineQuadric_mem_range i k z).mpr hk) |>.1

-- @@ L180-187 verbatim
lemma secondFactor_mul (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z ∈ coordinateOverlap i j) (hk : z ∈ coordinateOverlap i k) :
    secondFactor i j z*secondFactor j k (coordinateChange i j z)=secondFactor i k z := by
  rw [secondFactor_transition,secondFactor_transition,secondFactor_transition,affine_coordinateChange i j hj]
  apply hyperplaneTransition_mul
  · exact ⟨z.2,rfl⟩
  · exact (mem_range_affineQuadric j _).mp ((affineQuadric_mem_range i j z).mpr hj) |>.2
  · exact (mem_range_affineQuadric k _).mp ((affineQuadric_mem_range i k z).mpr hk) |>.2


-- @@ L189-189 verbatim
end

-- @@ L190-190 verbatim
end QuadricCounterexample


-- @@ L192-192 verbatim
end OAI
