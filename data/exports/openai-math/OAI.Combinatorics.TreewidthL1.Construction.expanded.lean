import OAI.Combinatorics.TreewidthL1.ExpandedTree


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe treewidthLevel1 treewidthLevel2 treewidthLevel3 treewidthLevel4


-- @@ L7-7 verbatim
namespace BoundedTreewidthL1.ExpandedConstruction

-- @@ L8-8 verbatim
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
attribute [local instance] Classical.decEq Classical.propDecidable

-- @@ L11-11 verbatim
variable {V ι I : Type*} [Fintype V] [Fintype ι] [Fintype I]


-- @@ L13-22 verbatim
lemma weight_total (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) :
    (∑ a : State ι V, weight M F a) = (Fintype.card ι : ℝ)*(2*M) := by
  have he (i : ι) : (∑ ω : V → Bool, (sweep M (F i)).real {ω}) = 2*M := by
    have h := OrderedReservation.total_weight M hM (F i)
    unfold OrderedSweepFlow.total at h
    rw [OrderedReservation.sum_carrier M (F i) (fun _ => 1)] at h
    simpa only [mul_one] using h
  simp only [Fintype.sum_prod_type, weight, ← Finset.sum_div, he]
  simp
  ; ring


-- @@ L24-40 verbatim
lemma edge_label (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j : ι) (C : Finset ι)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q)
    (a b : State ι V) (hab : edge M F H P Q i j C a b ≠ 0)
    (v : V) (hvP : v ∈ P) (hvQ : v ∈ Q) : label a v = label b v := by
  by_contra hne
  apply hab
  apply ExpandedParticleKernel.compose_trace (weight M F) (departure M F P i j)
    (incoming M F H Q C) (fun a => label a v) (fun a => label a v) (fun a => label a v)
  · intro a b hne
    apply (departure_coupling M F P i j).2.2.2.1 a b
    intro he
    exact hne (congrFun he ⟨v,hvP⟩)
  · intro a b hne
    apply (incoming_coupling M F H Q C hret htrace).2.2.2.1 a b
    intro he
    exact hne (congrFun he ⟨v,hvQ⟩)
  · exact hne


-- @@ L42-47 verbatim
noncomputable def joints (parent : I → Option I) (M : ℝ) (F : I → ι → V → ℝ)
    (B : I → Finset V) (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (i j : I) (a b : State ι V) : ℝ :=
  if parent j = some i then edge M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j) a b
  else if parent i = some j then edge M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i) b a
  else 0


-- @@ L49-60 verbatim
lemma joints_symmetric
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {I : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [Fintype I]
    (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι) :
    TreeMarkov.Symmetric (fun _ : I => State ι V) (joints parent M F B fresh₁ fresh₂ C) := by
  intro i j a b
  by_cases hij : parent j = some i
  · simp [joints,hij,hanti j i hij]
  · by_cases hji : parent i = some j <;> simp [joints,hij,hji]


-- @@ L62-71 verbatim
lemma joints_eq
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {I : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [Fintype I]
    (parent : I → Option I) (M : ℝ) (F : I → ι → V → ℝ)
    (B : I → Finset V) (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (i j : I) (hp : parent j = some i) :
    joints parent M F B fresh₁ fresh₂ C i j =
      edge M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j) := by
  funext a b
  simp [joints,hp]


-- @@ L73-92 verbatim
lemma joints_coupling (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i j : I) (hij : T.Adj i j) :
    IsCoupling (weight M (F i)) (weight M (F j)) (joints parent M F B fresh₁ fresh₂ C i j) := by
  rcases horient i j hij with hji | hij
  · have he : joints parent M F B fresh₁ fresh₂ C i j =
        fun a b => edge M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i) b a := by
      funext a b
      simp [joints,hji,hanti i j hji]
    rw [he]
    exact (edge_coupling M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i)
      (hret j i hji) (htrace j i hji)).symm
  · rw [joints_eq parent M F B fresh₁ fresh₂ C i j hij]
    exact edge_coupling M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j)
      (hret i j hij) (htrace i j hij)


-- @@ L94-111 verbatim
lemma joints_label (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i j : I) (hij : T.Adj i j) (a b : State ι V)
    (hab : joints parent M F B fresh₁ fresh₂ C i j a b ≠ 0)
    (v : V) (hvi : v ∈ B i) (hvj : v ∈ B j) : label a v = label b v := by
  rcases horient i j hij with hji | hij
  · have he := joints_symmetric parent hanti M F B fresh₁ fresh₂ C i j a b
    rw [he, joints_eq parent M F B fresh₁ fresh₂ C j i hji] at hab
    exact (edge_label M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i)
      (hret j i hji) (htrace j i hji) b a hab v hvj hvi).symm
  · rw [joints_eq parent M F B fresh₁ fresh₂ C i j hij] at hab
    exact edge_label M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j)
      (hret i j hij) (htrace i j hij) a b hab v hvi hvj

-- @@ L112-112 verbatim
end BoundedTreewidthL1.ExpandedConstruction


-- @@ L114-114 verbatim
namespace BoundedTreewidthL1.ExpandedConstruction

-- @@ L115-115 verbatim
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix

-- @@ L116-116 verbatim
open scoped BigOperators

-- @@ L117-117 verbatim
attribute [local instance] Classical.decEq Classical.propDecidable

-- @@ L118-118 verbatim
variable {V ι I : Type*} [Fintype V] [Fintype ι] [Fintype I]


-- @@ L120-139 verbatim
lemma weight_separation (M : ℝ) (F : ι → V → ℝ)
    (hF : ∀ i v, |F i v| ≤ M) (u v : V) :
    cutDistance (weight M F) label u v = ∑ i, |F i u-F i v| := by
  unfold cutDistance
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  have he (b : Bool) : (∑ ω : V → Bool,
      if label (i,b,ω) u = label (i,b,ω) v then 0 else weight M F (i,b,ω)) =
      |F i u-F i v|/2 := by
    have hs := OrderedReservation.sum_event M (F i) (fun ω => ω u ≠ ω v)
    rw [← cutSeparation, sweep_separation M (F i) (hF i)] at hs
    rw [← hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    cases b <;> cases hu : ω u <;> cases hv : ω v <;> simp [label,weight,hu,hv]
  simp_rw [he]
  simp
  ; ring


-- @@ L141-147 verbatim
noncomputable def ensemble (T : SimpleGraph I) (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι) : (I → State ι V) → ℝ :=
  ExpandedTree.law T ((Fintype.card ι : ℝ)*(2*M)) (fun i => weight M (F i))
    (joints parent M F B fresh₁ fresh₂ C)
    (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)


-- @@ L149-172 verbatim
lemma ensemble_data (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j)) :
    (∀ x, 0 ≤ ensemble T parent hanti M F B fresh₁ fresh₂ C x) ∧
    (∑ x, ensemble T parent hanti M F B fresh₁ fresh₂ C x) = (Fintype.card ι : ℝ)*(2*M) ∧
    ∀ i a, (∑ x, if x i = a then ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) =
      weight M (F i) a := by
  have hmass : 0 < (Fintype.card ι : ℝ)*(2*M) := by positivity
  obtain ⟨hn,ht,hm⟩ := ExpandedTree.law_marginals T hT _ hmass _ _
    (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)
    (fun i => weight_nonneg M (F i)) (fun i => weight_total M hM.le (F i))
    (fun i j hij => (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace i j hij).nonneg)
    (fun i j hij => (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace i j hij).row)
  refine ⟨hn,ht,?_⟩
  intro i a
  convert hm i a using 1
  congr 1
  funext x
  split_ifs <;> rfl


-- @@ L174-186 verbatim
lemma ensemble_labels (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (x : I → State ι V) (hx : ensemble T parent hanti M F B fresh₁ fresh₂ C x ≠ 0)
    (i : I) (v : V) (hv : v ∈ B i) :
    ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x v = label (x i) v := by
  exact ExpandedTree.law_labels T (fun i => (B i : Set V)) hcover hrun _ _ _ _ label
    (joints_label T parent horient hanti M F B fresh₁ fresh₂ C hret htrace) x hx i v hv


-- @@ L188-237 verbatim
/-- Every bag has the exact particle metric, while the inter-bag coupling is
chosen to retain the sweep order of each currently reserved particle. -/
lemma ensemble_cobag (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i : I) (hF : ∀ r v, |F i r v| ≤ M) (u v : V) (hu : u ∈ B i) (hv : v ∈ B i) :
    cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) u v =
      ∑ r, |F i r u-F i r v| := by
  rw [← weight_separation M (F i) hF u v]
  have hm := (ensemble_data T hT parent horient hanti M hM hι F B fresh₁ fresh₂ C hret htrace).2.2 i
  unfold cutDistance
  have he : (∑ x : I → State ι V,
      if ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x u =
          ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x v then 0
      else ensemble T parent hanti M F B fresh₁ fresh₂ C x) =
      ∑ x : I → State ι V, ensemble T parent hanti M F B fresh₁ fresh₂ C x *
        (if label (x i) u = label (x i) v then 0 else 1) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hz : ensemble T parent hanti M F B fresh₁ fresh₂ C x = 0
    · simp [hz]
    · rw [ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hz i u hu,
        ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hz i v hv]
      split_ifs <;> simp
  rw [he, ExpandedChain.sum_fiber_mul (fun x : I → State ι V => x i)
    (ensemble T parent hanti M F B fresh₁ fresh₂ C)
    (fun a => if label a u = label a v then 0 else 1)]
  apply Finset.sum_congr rfl
  intro a _
  have hh : (∑ x : I → State ι V, if x i = a then
      ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) = weight M (F i) a := by
    convert hm a using 1
  have hh' : (∑ x : I → State ι V, if x i = a then
      ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) *
      (if label a u = label a v then (0:ℝ) else 1) =
      (if label a u = label a v then 0 else weight M (F i) a) := by
    rw [hh]
    split_ifs <;> simp
  convert hh' using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

-- @@ L238-238 verbatim
end BoundedTreewidthL1.ExpandedConstruction


-- @@ L240-240 verbatim
namespace BoundedTreewidthL1.ExpandedMeasurable

-- @@ L241-241 verbatim
open MeasureTheory ExpandedParticleLaw ExpandedParticleKernel ExpandedConstruction ReservedSuffix

-- @@ L242-242 verbatim
open scoped BigOperators

-- @@ L243-243 verbatim
attribute [local instance] Classical.decEq Classical.propDecidable

-- @@ L244-244 verbatim
variable {Ω V ι I : Type*} [MeasurableSpace Ω] [Fintype V] [Fintype ι] [Fintype I]


-- @@ L246-254 verbatim
lemma selected {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Ω → A → ℝ) (a : Ω → A)
    (hf : ∀ b, Measurable (fun ω => f ω b)) (ha : Measurable a) :
    Measurable (fun ω => f ω (a ω)) := by
  have he : (fun ω => f ω (a ω)) = (fun ω => ∑ b, if a ω = b then f ω b else 0) := by
    funext ω
    simp
  rw [he]
  exact Finset.measurable_sum _ (fun b _ => (hf b).ite (measurableSet_eq_fun ha measurable_const) measurable_const)


-- @@ L256-264 verbatim
lemma measurable_marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : Ω → A → ℝ) (hμ : ∀ a, Measurable (fun ω => μ ω a)) (c : C) :
    Measurable (fun ω => marginal f (μ ω) c) := by
  unfold marginal
  apply Finset.measurable_sum
  intro a _
  by_cases h : f a = c <;> simp only [h, ↓reduceIte]
  · exact hμ a
  · exact measurable_const


-- @@ L266-273 verbatim
lemma measurable_glue {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : Ω → A → ℝ) (ν : Ω → B → ℝ)
    (hμ : ∀ a, Measurable (fun ω => μ ω a)) (hν : ∀ b, Measurable (fun ω => ν ω b)) (a : A) (b : B) :
    Measurable (fun ω => glueWeights f g (μ ω) (ν ω) a b) := by
  unfold glueWeights
  by_cases h : f a = g b <;> simp only [h, ↓reduceIte]
  · exact ((hμ a).mul (hν b)).div (measurable_marginal f μ hμ (g b))
  · exact measurable_const


-- @@ L275-284 verbatim
lemma measurable_edge_fixed (M : ℝ) (F H : Ω → ι → V → ℝ)
    (hF : ∀ a, Measurable (fun ω => weight M (F ω) a))
    (hH : ∀ a, Measurable (fun ω => weight M (H ω) a))
    (P Q : Finset V) (i j : ι) (C : Finset ι) (a b : State ι V) :
    Measurable (fun ω => edge M (F ω) (H ω) P Q i j C a b) := by
  unfold edge compose
  apply Finset.measurable_sum
  intro c _
  exact ((measurable_glue _ _ _ _ hF hF a c).mul
    (measurable_glue _ _ _ _ hF hH c b)).div (hF c)


-- @@ L286-295 verbatim
lemma measurable_edge [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (M : ℝ) (F H : Ω → ι → V → ℝ)
    (hF : ∀ a, Measurable (fun ω => weight M (F ω) a))
    (hH : ∀ a, Measurable (fun ω => weight M (H ω) a))
    (P Q : Finset V) (i j : Ω → ι) (C : Ω → Finset ι)
    (hi : Measurable i) (hj : Measurable j) (hC : Measurable C) (a b : State ι V) :
    Measurable (fun ω => edge M (F ω) (H ω) P Q (i ω) (j ω) (C ω) a b) := by
  exact selected (fun ω (c : ι × ι × Finset ι) => edge M (F ω) (H ω) P Q c.1 c.2.1 c.2.2 a b)
    (fun ω => (i ω,j ω,C ω)) (fun c => measurable_edge_fixed M F H hF hH P Q c.1 c.2.1 c.2.2 a b)
    (hi.prodMk (hj.prodMk hC))


-- @@ L297-311 verbatim
lemma measurable_joints
    {Ω : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {I : Type treewidthLevel4} [MeasurableSpace Ω] [Fintype V] [Fintype ι] [Fintype I]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (parent : I → Option I) (M : ℝ) (F : Ω → I → ι → V → ℝ) (B : I → Finset V)
    (hF : ∀ i a, Measurable (fun ω => weight M (F ω i) a))
    (fresh₁ fresh₂ : Ω → I → ι) (C : Ω → I → Finset ι)
    (h₁ : ∀ i, Measurable (fun ω => fresh₁ ω i)) (h₂ : ∀ i, Measurable (fun ω => fresh₂ ω i))
    (hC : ∀ i, Measurable (fun ω => C ω i)) (i j : I) (a b : State ι V) :
    Measurable (fun ω => joints parent M (F ω) B (fresh₁ ω) (fresh₂ ω) (C ω) i j a b) := by
  unfold joints
  split_ifs
  · exact measurable_edge M _ _ (hF i) (hF j) _ _ _ _ _ (h₁ i) (h₂ i) (hC j) a b
  · exact measurable_edge M _ _ (hF j) (hF i) _ _ _ _ _ (h₁ j) (h₂ j) (hC i) b a
  · exact measurable_const


-- @@ L313-329 verbatim
lemma measurable_law {A : Type*} [Fintype A] (T : SimpleGraph I) (M : ℝ)
    (μ : Ω → I → A → ℝ) (J : Ω → I → I → A → A → ℝ)
    (hs : ∀ ω, TreeMarkov.Symmetric (fun _ : I => A) (J ω))
    (hμ : ∀ i a, Measurable (fun ω => μ ω i a))
    (hJ : ∀ i j a b, Measurable (fun ω => J ω i j a b)) (x : I → A) :
    Measurable (fun ω => ExpandedTree.law T M (μ ω) (J ω) (hs ω) x) := by
  unfold ExpandedTree.law TreeMarkov.density
  apply Measurable.const_mul
  apply Measurable.mul
  · exact Finset.measurable_prod _ (fun i _ => (hμ i (x i)).div_const M)
  · apply Finset.measurable_prod
    intro e _
    induction e using Sym2.ind with
    | _ i j =>
      simp only [TreeMarkov.edgeFactor_mk, TreeMarkov.interaction, ExpandedTree.jointLaw, ExpandedTree.marginalLaw]
      exact ((hJ i j (x i) (x j)).div_const M).div
        (((hμ i (x i)).div_const M).mul ((hμ j (x j)).div_const M))


-- @@ L331-342 verbatim
/-- Measurability of the actual expanded tree law, allowing the reservation
indices and free pools to depend on all the previously sampled noise. -/
lemma measurable_ensemble [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (T : SimpleGraph I) (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : Ω → I → ι → V → ℝ) (B : I → Finset V)
    (hF : ∀ i a, Measurable (fun ω => weight M (F ω i) a))
    (fresh₁ fresh₂ : Ω → I → ι) (C : Ω → I → Finset ι)
    (h₁ : ∀ i, Measurable (fun ω => fresh₁ ω i)) (h₂ : ∀ i, Measurable (fun ω => fresh₂ ω i))
    (hC : ∀ i, Measurable (fun ω => C ω i)) (x : I → State ι V) :
    Measurable (fun ω => ensemble T parent hanti M (F ω) B (fresh₁ ω) (fresh₂ ω) (C ω) x) := by
  exact measurable_law T _ _ _ _ hF (measurable_joints parent M F B hF fresh₁ fresh₂ C h₁ h₂ hC) x

-- @@ L343-343 verbatim
end BoundedTreewidthL1.ExpandedMeasurable


-- @@ L345-345 verbatim
end OAI
