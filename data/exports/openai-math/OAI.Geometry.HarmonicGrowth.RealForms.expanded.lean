import OAI.Geometry.HarmonicGrowth.LieSaturation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Matrix

-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open scoped Topology

-- @@ L9-9 verbatim
open Filter

-- @@ L10-10 verbatim
open Matrix

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Matrix MvPolynomial

-- @@ L13-13 verbatim
open Matrix

-- @@ L14-14 verbatim
open scoped BigOperators

-- @@ L15-15 verbatim
open scoped BigOperators

-- @@ L16-16 verbatim
open Matrix

-- @@ L17-17 verbatim
open scoped BigOperators ComplexStarModule

-- @@ L18-18 verbatim
open Module


-- @@ L20-20 verbatim
namespace HarmonicCounterexample.RealForm

-- @@ L21-22 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]


-- @@ L24-32 verbatim
/-- The fixed real form of a conjugation really complexifies to the entire
complex space; this is an actual linear equivalence, not a dimension assumption. -/
def realImagEquiv : V ≃ₗ[ℝ] selfAdjoint V × selfAdjoint V where
  toFun x := (realPart x,imaginaryPart x)
  invFun x := (x.1:V)+Complex.I • (x.2:V)
  left_inv := realPart_add_I_smul_imaginaryPart
  right_inv x := by ext <;> simp
  map_add' x y := by simp
  map_smul' c x := by simp


-- @@ L34-40 verbatim
lemma real_form_finrank [FiniteDimensional ℂ V] :
    Module.finrank ℝ (selfAdjoint V)=Module.finrank ℂ V := by
  let : FiniteDimensional ℝ (selfAdjoint V) :=
    FiniteDimensional.of_surjective realPart realPart_surjective
  have h := (realImagEquiv (V:=V)).finrank_eq
  rw [Module.finrank_prod,finrank_real_of_complex] at h
  omega


-- @@ L42-42 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L44-53 verbatim
def complexCoordinates (b : Basis ι ℝ (selfAdjoint V)) : V →ₗ[ℂ] (ι → ℂ) where
  toFun x i := (b.repr (realPart x) i:ℂ)+Complex.I*(b.repr (imaginaryPart x) i:ℂ)
  map_add' x y := by ext i; simp; ring
  map_smul' c x := by
    ext i
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,map_smul,
      Finsupp.sub_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Pi.smul_apply,
      RingHom.id_apply]
    apply Complex.ext <;> simp


-- @@ L55-67 verbatim
omit [Fintype ι] in
lemma complexCoordinates_injective (b : Basis ι ℝ (selfAdjoint V)) :
    Function.Injective (complexCoordinates b) := by
  intro x y h
  apply ComplexStarModule.ext
  · apply b.repr.injective
    ext i
    have hi := congrArg (fun f : ι → ℂ => (f i).re) h
    simpa [complexCoordinates] using hi
  · apply b.repr.injective
    ext i
    have hi := congrArg (fun f : ι → ℂ => (f i).im) h
    simpa [complexCoordinates] using hi


-- @@ L69-83 verbatim
lemma complexCoordinates_surjective (b : Basis ι ℝ (selfAdjoint V)) :
    Function.Surjective (complexCoordinates b) := by
  intro z
  let u : selfAdjoint V := b.equivFun.symm (fun i => (z i).re)
  let v : selfAdjoint V := b.equivFun.symm (fun i => (z i).im)
  refine ⟨(u:V)+Complex.I • (v:V),?_⟩
  ext i
  have hu : b.repr u i=(z i).re := congrFun (b.equivFun.apply_symm_apply _) i
  have hv : b.repr v i=(z i).im := congrFun (b.equivFun.apply_symm_apply _) i
  change (b.repr (realPart ((u:V)+Complex.I • (v:V))) i:ℂ)+
    Complex.I*(b.repr (imaginaryPart ((u:V)+Complex.I • (v:V))) i:ℂ)=z i
  simp only [map_add,selfAdjoint.realPart_coe,realPart_I_smul,
    selfAdjoint.imaginaryPart_coe,neg_zero,add_zero,imaginaryPart_I_smul,zero_add,hu,hv]
  rw [mul_comm]
  exact Complex.re_add_im _


-- @@ L85-87 verbatim
def complexCoordinateEquiv (b : Basis ι ℝ (selfAdjoint V)) : V ≃ₗ[ℂ] (ι → ℂ) :=
  LinearEquiv.ofBijective (complexCoordinates b)
    ⟨complexCoordinates_injective b,complexCoordinates_surjective b⟩


-- @@ L89-92 verbatim
/-- A given real basis of the conjugation-fixed space is also a complex basis
of the original complex space. -/
def complexBasis (b : Basis ι ℝ (selfAdjoint V)) : Basis ι ℂ V :=
  (Pi.basisFun ℂ ι).map (complexCoordinateEquiv b).symm


-- @@ L94-102 verbatim
lemma complexBasis_apply (b : Basis ι ℝ (selfAdjoint V)) (i : ι) :
    complexBasis b i=(b i:V) := by
  apply (complexCoordinateEquiv b).injective
  simp only [complexBasis,Basis.map_apply,LinearEquiv.apply_symm_apply]
  ext j
  classical
  by_cases h : i=j <;>
    simp [complexCoordinateEquiv,complexCoordinates,Basis.repr_self,
      h,eq_comm]


-- @@ L104-104 verbatim
end HarmonicCounterexample.RealForm


-- @@ L106-106 verbatim
end


-- @@ L108-108 verbatim
noncomputable section

-- @@ L109-109 verbatim
open Matrix

-- @@ L110-110 verbatim
open scoped BigOperators

-- @@ L111-111 verbatim
open scoped Topology

-- @@ L112-112 verbatim
open Filter

-- @@ L113-113 verbatim
open Matrix

-- @@ L114-114 verbatim
open scoped BigOperators

-- @@ L115-115 verbatim
open Matrix MvPolynomial

-- @@ L116-116 verbatim
open Matrix

-- @@ L117-117 verbatim
open scoped BigOperators

-- @@ L118-118 verbatim
open scoped BigOperators

-- @@ L119-119 verbatim
open Matrix

-- @@ L120-120 verbatim
open scoped BigOperators ComplexStarModule

-- @@ L121-121 verbatim
open Module


-- @@ L123-123 verbatim
namespace HarmonicCounterexample.RealForm

-- @@ L124-124 verbatim
open Module

-- @@ L125-126 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]


-- @@ L128-134 verbatim
/-- Extension of a real endomorphism on the actual fixed real form. -/
def complexify (T : Module.End ℝ (selfAdjoint V)) : Module.End ℂ V where
  toFun x := (T (realPart x):V)+Complex.I • (T (imaginaryPart x):V)
  map_add' x y := by simp only [map_add,AddSubgroup.coe_add,smul_add]; abel
  map_smul' c x := by
    apply ComplexStarModule.ext <;>
      simp [realPart_smul,imaginaryPart_smul,sub_eq_add_neg,add_comm]



-- @@ L137-138 verbatim
@[simp] lemma complexify_apply_fixed (T : Module.End ℝ (selfAdjoint V)) (x : selfAdjoint V) :
    complexify T (x:V)=(T x:V) := by simp [complexify]


-- @@ L140-141 verbatim
@[simp] lemma complexify_realPart (T : Module.End ℝ (selfAdjoint V)) (x : V) :
    realPart (complexify T x)=T (realPart x) := by simp [complexify]


-- @@ L143-144 verbatim
@[simp] lemma complexify_imaginaryPart (T : Module.End ℝ (selfAdjoint V)) (x : V) :
    imaginaryPart (complexify T x)=T (imaginaryPart x) := by simp [complexify]


-- @@ L146-150 verbatim
lemma complexify_injective : Function.Injective (complexify (V:=V)) := by
  intro S T h
  ext x
  have hh := congrArg (fun X : Module.End ℂ V => X (x:V)) h
  simpa using hh


-- @@ L152-155 verbatim
lemma complexify_mul (S T : Module.End ℝ (selfAdjoint V)) :
    complexify (S*T)=complexify S*complexify T := by
  ext x
  apply ComplexStarModule.ext <;> simp


-- @@ L157-165 verbatim
/-- Complexification respects the REAL vector-space operations. -/
def complexifyLinear : Module.End ℝ (selfAdjoint V) →ₗ[ℝ] Module.End ℂ V where
  toFun := complexify
  map_add' S T := by ext x; simp [complexify]; abel
  map_smul' c T := by
    ext x
    simp only [complexify,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,
      selfAdjoint.val_smul,smul_add,RingHom.id_apply]
    rw [smul_comm Complex.I c]


-- @@ L167-167 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L169-172 verbatim
omit [DecidableEq ι] in
lemma complexBasis_repr (b : Basis ι ℝ (selfAdjoint V)) (x : V) (i : ι) :
    (complexBasis b).repr x i=complexCoordinates b x i := by
  rfl


-- @@ L174-178 verbatim
lemma complexify_matrix (b : Basis ι ℝ (selfAdjoint V)) (T : Module.End ℝ (selfAdjoint V)) :
    LinearMap.toMatrix (complexBasis b) (complexBasis b) (complexify T)=
      (LinearMap.toMatrix b b T).map Complex.ofReal := by
  ext i j
  simp [LinearMap.toMatrix_apply,complexBasis_apply,complexBasis_repr,complexCoordinates]


-- @@ L180-184 verbatim
lemma complexify_trace (b : Basis ι ℝ (selfAdjoint V)) (T : Module.End ℝ (selfAdjoint V)) :
    LinearMap.trace ℂ V (complexify T)=(LinearMap.trace ℝ (selfAdjoint V) T:ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (complexBasis b),
    LinearMap.trace_eq_matrix_trace ℝ b,complexify_matrix]
  simp [Matrix.trace]


-- @@ L186-186 verbatim
end HarmonicCounterexample.RealForm


-- @@ L188-188 verbatim
end


-- @@ L190-190 verbatim
noncomputable section

-- @@ L191-191 verbatim
open Matrix

-- @@ L192-192 verbatim
open scoped BigOperators

-- @@ L193-193 verbatim
open scoped Topology

-- @@ L194-194 verbatim
open Filter

-- @@ L195-195 verbatim
open Matrix

-- @@ L196-196 verbatim
open scoped BigOperators

-- @@ L197-197 verbatim
open Matrix MvPolynomial

-- @@ L198-198 verbatim
open Matrix

-- @@ L199-199 verbatim
open scoped BigOperators

-- @@ L200-200 verbatim
open scoped BigOperators

-- @@ L201-201 verbatim
open Matrix

-- @@ L202-202 verbatim
open scoped BigOperators ComplexStarModule

-- @@ L203-203 verbatim
open Module


-- @@ L205-205 verbatim
namespace HarmonicCounterexample.RealForm

-- @@ L206-206 verbatim
open Module

-- @@ L207-207 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L208-209 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [StarAddMonoid V] [StarModule ℂ V]


-- @@ L211-221 verbatim
lemma complexify_star (T : Module.End ℝ (selfAdjoint V)) (x : V) :
    complexify T (star x)=star (complexify T x) := by
  have hr : realPart (star x)=realPart x := by
    apply Subtype.ext
    simp only [realPart_apply_coe,star_star]
    rw [add_comm]
  have hi : imaginaryPart (star x)= -imaginaryPart x := by
    apply Subtype.ext
    simp only [imaginaryPart_apply_coe,star_star,AddSubgroup.coe_neg]
    rw [← neg_sub,smul_neg,smul_neg]
  simp [complexify,hr,hi]


-- @@ L223-224 verbatim
def restrictReal (T : Module.End ℂ V) : Module.End ℝ (selfAdjoint V) :=
  realPart.comp ((T.restrictScalars ℝ).comp (selfAdjoint.submodule ℝ V).subtype)


-- @@ L226-235 verbatim
lemma complexify_restrictReal (T : Module.End ℂ V)
    (hT : ∀ x,T (star x)=star (T x)) : complexify (restrictReal T)=T := by
  have hfixed (x : selfAdjoint V) : IsSelfAdjoint (T (x:V)) := by
    dsimp [IsSelfAdjoint]
    rw [← hT,x.property]
  have hv (x : selfAdjoint V) : (restrictReal T x:V)=T (x:V) :=
    (hfixed x).coe_realPart
  ext x
  change (restrictReal T (realPart x):V)+Complex.I • (restrictReal T (imaginaryPart x):V)=T x
  rw [hv,hv,← T.map_smul,← T.map_add,realPart_add_I_smul_imaginaryPart]


-- @@ L237-242 verbatim
def complexifyLie : Module.End ℝ (selfAdjoint V) →ₗ⁅ℝ⁆ Module.End ℂ V :=
  { complexifyLinear with
    map_lie' := by
      intro S T
      change complexify (S*T-T*S)=complexify S*complexify T-complexify T*complexify S
      exact (complexifyLinear.map_sub (S*T) (T*S)).trans (by change complexify (S*T)-complexify (T*S)=_; rw [complexify_mul,complexify_mul]) }


-- @@ L244-246 verbatim
variable {κ : Type*} {W : κ → Type*}
  [∀ i,AddCommGroup (W i)] [∀ i,Module ℂ (W i)]
  [∀ i,StarAddMonoid (W i)] [∀ i,StarModule ℂ (W i)]


-- @@ L248-253 verbatim
def complexifyTuple : (∀ i,Module.End ℝ (selfAdjoint (W i))) →ₗ⁅ℝ⁆
    (∀ i,Module.End ℂ (W i)) where
  toFun T i := complexify (T i)
  map_add' S T := funext (fun i => complexifyLinear.map_add (S i) (T i))
  map_smul' c T := funext (fun i => complexifyLinear.map_smul c (T i))
  map_lie' {S T} := funext (fun i => complexifyLie.map_lie (S i) (T i))


-- @@ L255-258 verbatim
lemma complexifyTuple_injective : Function.Injective (complexifyTuple (W:=W)) := by
  intro S T h
  funext i
  exact complexify_injective (congrFun h i)


-- @@ L260-272 verbatim
/-- Real simultaneous control descends to genuine endomorphisms of the fixed
real spaces. This is an injective Lie-algebra descent, not a dimension assertion. -/
lemma tuple_lieSpan_of_complexification {α : Type*}
    (G : α → ∀ i,Module.End ℝ (selfAdjoint (W i)))
    (X : ∀ i,Module.End ℝ (selfAdjoint (W i)))
    (h : complexifyTuple X ∈ LieSubalgebra.lieSpan ℝ _
        (Set.range (fun a => complexifyTuple (G a)))) :
    X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range G) := by
  have he : Set.range (fun a => complexifyTuple (G a)) = complexifyTuple '' Set.range G := by
    exact Set.range_comp complexifyTuple G
  rw [he,← LieSubalgebra.map_lieSpan] at h
  rcases h with ⟨Y,hY,hYX⟩
  exact complexifyTuple_injective hYX ▸ hY


-- @@ L274-274 verbatim
end HarmonicCounterexample.RealForm


-- @@ L276-276 verbatim
end


-- @@ L278-278 verbatim
noncomputable section

-- @@ L279-279 verbatim
open Matrix

-- @@ L280-280 verbatim
open scoped BigOperators

-- @@ L281-281 verbatim
open scoped Topology

-- @@ L282-282 verbatim
open Filter

-- @@ L283-283 verbatim
open Matrix

-- @@ L284-284 verbatim
open scoped BigOperators

-- @@ L285-285 verbatim
open Matrix MvPolynomial

-- @@ L286-286 verbatim
open Matrix

-- @@ L287-287 verbatim
open scoped BigOperators

-- @@ L288-288 verbatim
open scoped BigOperators

-- @@ L289-289 verbatim
open Matrix

-- @@ L290-290 verbatim
open scoped BigOperators ComplexStarModule

-- @@ L291-291 verbatim
open Module


-- @@ L293-293 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L294-294 verbatim
open Module

-- @@ L295-295 verbatim
open HarmonicCounterexample.RealForm


-- @@ L297-302 verbatim
/-- The real structure is Cartesian conjugation, i.e. coefficient conjugation
combined with interchange of z and w in split complex coordinates. -/
noncomputable instance harmonicSpaceStar (l : ℕ) : StarAddMonoid (harmonicSpace (Fin 8) l) where
  star := spaceRealConjugation l
  star_involutive x := (spaceRealConjugation l).apply_symm_apply x
  star_add := (spaceRealConjugation l).map_add


-- @@ L304-305 verbatim
instance harmonicSpaceStarModule (l : ℕ) : StarModule ℂ (harmonicSpace (Fin 8) l) where
  star_smul := (spaceRealConjugation l).map_smulₛₗ


-- @@ L307-307 verbatim
abbrev realHarmonicSpace (l : ℕ) := selfAdjoint (harmonicSpace (Fin 8) l)


-- @@ L309-311 verbatim
lemma realHarmonicSpace_finrank (l : ℕ) :
    Module.finrank ℝ (realHarmonicSpace l)=Module.finrank ℂ (harmonicSpace (Fin 8) l) :=
  real_form_finrank


-- @@ L313-319 verbatim
lemma harmonicEnd_star_of_conj {l : ℕ} (T : Module.End ℂ (harmonicSpace (Fin 8) l))
    (hT : (spaceRealConjugation l).conj T=T) : ∀ x,T (star x)=star (T x) := by
  intro x
  have h := congrArg (fun A : Module.End ℂ (harmonicSpace (Fin 8) l) => A (star x)) hT
  change (spaceRealConjugation l) (T ((spaceRealConjugation l).symm ((spaceRealConjugation l) x)))=T (star x) at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm


-- @@ L321-326 verbatim
lemma complexify_harmonicEnd_conj {l : ℕ} (T : Module.End ℝ (realHarmonicSpace l)) :
    (spaceRealConjugation l).conj (complexify T)=complexify T := by
  apply LinearMap.ext
  intro x
  change star (complexify T (star x))=complexify T x
  rw [complexify_star,star_star]


-- @@ L328-328 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L330-330 verbatim
end


-- @@ L332-332 verbatim
noncomputable section

-- @@ L333-333 verbatim
open Matrix

-- @@ L334-334 verbatim
open scoped BigOperators

-- @@ L335-335 verbatim
open scoped Topology

-- @@ L336-336 verbatim
open Filter

-- @@ L337-337 verbatim
open Matrix

-- @@ L338-338 verbatim
open scoped BigOperators

-- @@ L339-339 verbatim
open Matrix MvPolynomial

-- @@ L340-340 verbatim
open Matrix

-- @@ L341-341 verbatim
open scoped BigOperators

-- @@ L342-342 verbatim
open scoped BigOperators

-- @@ L343-343 verbatim
open Matrix

-- @@ L344-344 verbatim
open scoped BigOperators ComplexStarModule

-- @@ L345-345 verbatim
open Module


-- @@ L347-347 verbatim
namespace HarmonicCounterexample.Control

-- @@ L348-348 verbatim
open Module HarmonicCounterexample.RealForm HarmonicCounterexample.ComplexAngular

-- @@ L349-349 verbatim
open HarmonicCounterexample.Berger

-- @@ L350-350 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L352-357 verbatim
/-- Real generators on the actual real harmonic spaces, not formal matrix
copies with an assumed complexification. -/
def realHarmonicTupleGenerator (L : ℕ) (c : Fin L → ℝ)
    (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    ∀ l : Fin L,Module.End ℝ (realHarmonicSpace (l.val+2)) :=
  fun l => restrictReal (harmonicTupleGenerator L (fun l => (c l:ℂ)) J l)


-- @@ L359-365 verbatim
lemma complexify_realHarmonicTupleGenerator (L : ℕ) (c : Fin L → ℝ)
    (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    complexifyTuple (realHarmonicTupleGenerator L c J)=
      harmonicTupleGenerator L (fun l => (c l:ℂ)) J := by
  funext l
  exact complexify_restrictReal _ (harmonicEnd_star_of_conj _
    (harmonic_weighted_generator_real (l.val+2) (c l) J))


-- @@ L367-382 verbatim
/-- Source simultaneous controllability, now on GENUINE real harmonic spaces
with their actual real dimensions and actual real endomorphism traces. -/
theorem harmonic_simultaneous_actual_real (L : ℕ) (c : Fin L → ℝ)
    (hc : ∀ l,c l ≠ 0)
    {X : ∀ l : Fin L,Module.End ℝ (realHarmonicSpace (l.val+2))}
    (hX : ∀ l,LinearMap.trace ℝ _ (X l)=0) :
    X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range (realHarmonicTupleGenerator L c)) := by
  apply tuple_lieSpan_of_complexification
  have htr (l : Fin L) : LinearMap.trace ℂ _ (complexify (X l))=0 := by
    let : FiniteDimensional ℝ (realHarmonicSpace (l.val+2)) :=
      FiniteDimensional.of_surjective realPart realPart_surjective
    rw [complexify_trace (Module.finBasis ℝ _),hX l,Complex.ofReal_zero]
  have h := harmonic_simultaneous_real_end L c hc htr
    (fun l => complexify_harmonicEnd_conj (X l))
  simp only [complexify_realHarmonicTupleGenerator]
  exact h


-- @@ L384-384 verbatim
end HarmonicCounterexample.Control


-- @@ L386-386 verbatim
end


-- @@ L388-388 verbatim
end OAI
