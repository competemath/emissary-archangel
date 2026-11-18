import OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
import OAI.NumberTheory.DirichletL.Descent.InitializationEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
namespace SevenEighths.InverseInitialArithmetic

-- @@ L9-9 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L10-10 verbatim
open MixedCrossSeparation (columnCoefficient)

-- @@ L11-11 verbatim
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers

-- @@ L12-12 verbatim
open CompletedGauss

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L14-14 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L15-18 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})


-- @@ L20-25 verbatim
def initialColumn (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i∈S,p i) *
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (j*C) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S d) *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S h * H S


-- @@ L27-32 verbatim
theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      secondPreColumn p hp hcop hg Ψ (j*C) 1 1 d h H S := by
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]


-- @@ L34-42 verbatim
theorem initial_common_extraction (hpr : ∀ i,λ₀^2∣p i-1)
    (Ψ : O →* ℂ) (j t d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    initialColumn p hp hcop hg Ψ j (d*t) d h H (V∪N) =
      initialColumn p hp hcop hg Ψ j (d*t) d h (fun _=>1) V *
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H (V∪U)) N := by
  simp only [initialColumn_eq_secondPre]
  simpa only [one_mul] using secondPreColumn_union p hp hcop hg hpr Ψ j t 1 1 d h H V N hVN


-- @@ L44-55 verbatim
theorem initial_marked_child (F V A : Finset ι) (Ψ : O →* ℂ) (j t d h : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ j t 1 1 d h slots lists a W X


-- @@ L57-66 verbatim
theorem initial_input_row (F : Finset ι) (Ψ : O →* ℂ) (j : O)
    (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p hg F Ψ j 1 1 H z =
      FirstCauchyArithmetic.supportConjugateSum (fun i=>Ideal.span {p i}) hg F
        (fun S=>Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S j*H S) z := by
  unfold inputConjugateRow
  congr 1
  funext S
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [secondInputCoefficient,hone,one_pow,mul_one]


-- @@ L68-68 verbatim
def sourceIdeal (S : Finset ι) : Ideal O := Ideal.span {∏ i∈S,p i}


-- @@ L70-73 verbatim
include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))


-- @@ L75-78 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]


-- @@ L80-91 verbatim
include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_gen (hpr : ∀ i,λ₀^2∣p i-1) (S : Finset ι) :
    primaryGenerator (sourceIdeal p S)=∏ i∈S,p i := by
  apply primaryGenerator_span _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have he : p i*(∏ j∈S,p j)-1=(p i-1)*(∏ j∈S,p j)+((∏ j∈S,p j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (hpr i) _) ih


-- @@ L93-97 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]


-- @@ L99-100 verbatim
def sourcePrime (i : ι) : SmoothMobiusCorrection.PrimeIdeal :=
  ⟨Ideal.span {p i},Ideal.prime_of_isPrime (NeZero.ne _) inferInstance⟩


-- @@ L102-103 verbatim
def sourceTuple {J : ℕ} (G E V : Finset ι) (h : O) (assigned : Fin J→ι) : InitialTuple J :=
  ⟨sourceIdeal p G,sourceIdeal p E,sourceIdeal p V,h,fun i=>sourcePrime p (assigned i)⟩


-- @@ L105-110 verbatim
omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi


-- @@ L112-127 verbatim
include hp in

theorem sourceTuple_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι)
    (hEG : E⊆G) (ha : ∀ i,assigned i∈G∪V) :
    InitialSourceValid (sourceTuple p G E V h assigned) := by
  refine ⟨sourceIdeal_ne_zero p hp G,sourceIdeal_ne_zero p hp V,?_,
    sourceIdeal_dvd p E G hEG,?_⟩
  · change primaryGenerator (sourceIdeal p E)≠0
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  · intro i
    change (sourcePrime p (assigned i)).val∣sourceIdeal p G*sourceIdeal p V
    rcases Finset.mem_union.mp (ha i) with hi|hi
    · exact dvd_mul_of_dvd_left (source_prime_dvd p G (assigned i) hi) _
    · exact dvd_mul_of_dvd_right (source_prime_dvd p V (assigned i) hi) _


-- @@ L129-138 verbatim
include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem source_quotient (G E : Finset ι) (hEG : E⊆G) :
    CanonicalQuadraticSieve.idealQuotient (sourceIdeal p E) (sourceIdeal p G)=
      sourceIdeal p (G\E) := by
  apply mul_left_cancel₀ (sourceIdeal_ne_zero p hp E)
  rw [CanonicalQuadraticSieve.idealQuotient_mul (sourceIdeal_dvd p E G hEG)]
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]


-- @@ L140-146 verbatim
include hp in

theorem source_child (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι) (hEG : E⊆G) :
    initialChild (sourceTuple p G E V h assigned)=
      (sourceIdeal p (G\E),sourceIdeal p E*sourceIdeal p V,(∏ i∈E,p i)*h) := by
  simp only [initialChild,sourceTuple,source_quotient p hp G E hEG,sourceIdeal_gen p hp hpr E]


-- @@ L148-165 verbatim
theorem initial_pair_children
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (j t d h₁ h₂ : O) (H₁ H₂ : Finset ι→ℂ) :
    (∑ S∈F.powerset,∑ T∈F.powerset,if Disjoint S T then
      star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ H₁ S)*
        initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ H₂ T else 0) =
    ∑ V∈F.powerset,
      (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) V *
        star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ (fun _=>1) V)*
          initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ (fun _=>1) V) *
        star (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₁
          (j*t) (d*∏ i∈V,p i) (d*h₁) (fun U=>H₁ (V∪U)) N) *
        (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₂
          (j*t) (d*∏ i∈V,p i) (d*h₂) (fun U=>H₂ (V∪U)) N) := by
  simp only [initialColumn_eq_secondPre]
  simpa only [secondSeparatedPair,secondCommonWeight,secondChildSum,one_mul] using
    secondSeparatedPair_eq_children p hp hcop hg hinj hpr F Ψ₁ Ψ₂ j t 1 1 d h₁ h₂ H₁ H₂


-- @@ L167-197 verbatim
theorem initial_scalar_self_pair
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (Ψ : O →* ℂ) (j C d h : O) (V : Finset ι)
    (hΨ : ‖Ψ (∏ i∈V,p i)‖=1) :
    star (initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V)*
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V =
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V d *
        rowCoprimeMask (fun i=>Ideal.span {p i}) V h := by
  have hcol := columnCoefficient_mul_star p hp hcop hg hc V
  have hphase : Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i))=1 := by
    rw [←starRingEnd_apply,Complex.mul_conj',hΨ]
    norm_num
  have hmask : star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C) := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V d
  have hh := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V h
  simp only [initialColumn,mul_one,star_mul,star_star]
  calc
    _ = (columnCoefficient p hp hcop hg V*star (columnCoefficient p hp hcop hg V))*
      (Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i)))*
      (star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h) := by ring
    _ = _ := by rw [hcol,hphase,hmask,hd,hh]; ring


-- @@ L199-203 verbatim
theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he


-- @@ L205-210 verbatim
@[ext] structure Source (J : ℕ) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  assigned : Fin J→ι


-- @@ L212-213 verbatim
def toTuple {J : ℕ} (x : Source (ι:=ι) J) : InitialTuple J :=
  sourceTuple p x.common x.divisor x.overlap x.frequency x.assigned


-- @@ L215-230 verbatim
theorem toTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) {J : ℕ} :
    Function.Injective (toTuple p (J:=J)) := by
  intro x y he
  have hC := congrArg InitialTuple.common he
  have hD := congrArg InitialTuple.divisor he
  have hV := congrArg InitialTuple.residual he
  have hf := congrArg InitialTuple.frequency he
  have ha := congrArg InitialTuple.assigned he
  apply Source.ext
  · exact sourceIdeal_injective p hinj hC
  · exact sourceIdeal_injective p hinj hD
  · exact sourceIdeal_injective p hinj hV
  · exact hf
  · funext i
    apply hinj
    exact congrArg Subtype.val (congrFun ha i)


-- @@ L232-234 verbatim
def assignedTerm {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) : ℂ :=
  ∏ i, if assigned i∈lists i ∧ assigned i∈outer then a i (assigned i) else 0


-- @@ L236-242 verbatim
theorem assignedTerm_source {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) (h : assignedTerm lists a outer assigned≠0) :
    ∀ i,assigned i∈lists i ∧ assigned i∈outer := by
  intro i
  have hn := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  by_contra hi
  simp only [hi,ite_false,ne_eq,not_true_eq_false] at hn


-- @@ L244-252 verbatim
include hp in

theorem actual_source_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (x : Source (ι:=ι) J) (hdiv : x.divisor⊆x.common)
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hterm : assignedTerm lists a (x.common∪x.overlap) x.assigned≠0) :
    InitialSourceValid (toTuple p x) :=
  sourceTuple_valid p hp hpr x.common x.divisor x.overlap x.frequency x.assigned hdiv
    (fun i=>(assignedTerm_source lists a _ _ hterm i).2)


-- @@ L254-279 verbatim
include hp in

theorem actual_source_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))
  let T := S.image (toTuple p)
  have hvalid : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have hv := initialChild_valid (toTuple p x)
      (actual_source_valid p hp hpr x (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using hv
  have hh := valid_tuple_card_le_separated T t f k ht hf hvalid
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (toTuple_injective p hinj)
  rw [hcard] at hh
  exact hh


-- @@ L281-296 verbatim
include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem poisson_generator_unit (hpr : ∀ i,λ₀^2∣p i-1) (E : Finset ι) :
    ∃ u : Oˣ, primeSubsetGenerator (fun i=>Ideal.span {p i}) E=
      (u : O)*primaryGenerator (sourceIdeal p E) := by
  have hg0 : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs : Ideal.span {primaryGenerator (sourceIdeal p E)}=
      Ideal.span {primeSubsetGenerator (fun i=>Ideal.span {p i}) E} := by
    rw [(primaryGenerator_spec _ hg0).1]
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,
      sourceIdeal,FiniteGaussPhase.span_finset_prod]
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩


-- @@ L298-299 verbatim
def sectorSource {J : ℕ} (u : Oˣ) (x : Source (ι:=ι) J) : Source (ι:=ι) J :=
  {x with frequency := (u : O)^5*x.frequency}


-- @@ L301-311 verbatim
omit [DecidableEq ι] in
theorem sectorSource_injective {J : ℕ} (u : Oˣ) :
    Function.Injective (sectorSource (J:=J) (ι:=ι) u) := by
  intro x y he
  apply Source.ext
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.common) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.divisor) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.overlap) he
  · have hh := congrArg Source.frequency he
    exact mul_left_cancel₀ (pow_ne_zero 5 (Units.ne_zero u)) hh
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.assigned) he


-- @@ L313-319 verbatim
include hp in

omit hp in
theorem sectorTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {J : ℕ} (u : Oˣ) :
    Function.Injective (fun x : Source (ι:=ι) J=>toTuple p (sectorSource u x)) :=
  (toTuple_injective p hinj).comp (sectorSource_injective u)


-- @@ L321-346 verbatim
include hp in

theorem actual_sector_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ} (u : Oˣ)
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))
  let T := S.image (fun x=>toTuple p (sectorSource u x))
  have hv : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have he := initialChild_valid (toTuple p (sectorSource u x))
      (actual_source_valid p hp hpr (sectorSource u x) (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using he
  have hh := valid_tuple_card_le_separated T t f k ht hf hv
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (sectorTuple_injective p hinj u)
  rw [hcard] at hh
  exact hh


-- @@ L348-375 verbatim
theorem initial_poisson_child_normalized
    (hpr : ∀ i,λ₀^2∣p i-1) (G E V : Finset ι) (Ψ : O →* ℂ)
    (j e t h : O) (he : Ideal.span {e}=sourceIdeal p E)
    (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Oˣ, e=(u:O)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (H : Finset ι→ℂ) (N : Finset ι),
        secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
          secondChildColumn p hp hcop hg Ψ
            (j*primaryGenerator (sourceIdeal p (G\E)))
            (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
            (primaryGenerator (sourceIdeal p E)*((u:O)^5*h)) H N := by
  have hgE : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) e he hgE
  refine ⟨u,hu,?_⟩
  intro H N
  have hts : Ideal.span {t}=Ideal.span {primaryGenerator (sourceIdeal p (G\E))} := by
    rw [ht,sourceIdeal_gen p hp hpr (G\E)]
    rfl
  have hmask := rowCoprimeMask_mul_eq_of_span_eq (fun i=>Ideal.span {p i}) N j hts
  have hchange : secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
      secondChildColumn p hp hcop hg Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (e*∏ i∈V,p i) (e*h) H N := by
    simp only [secondChildColumn,hmask]
  rw [hchange,hu,primaryGenerator_mul,sourceIdeal_gen p hp hpr V]
  rw [mul_assoc (u:O)]
  exact secondChildColumn_generator_unit p hp hcop hg Ψ u _ _ _ h H N


-- @@ L377-377 verbatim
end SevenEighths.InverseInitialArithmetic


-- @@ L379-379 verbatim
end


-- @@ L381-381 verbatim
end OAI
