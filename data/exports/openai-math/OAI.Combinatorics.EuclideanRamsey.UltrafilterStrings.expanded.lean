import OAI.Combinatorics.EuclideanRamsey.PathWords


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uModule uIndex uAlpha


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Real Filter Topology MeasureTheory Polynomial

-- @@ L12-12 verbatim
open Matrix MeasureTheory

-- @@ L13-13 verbatim
open MeasureTheory

-- @@ L14-14 verbatim
open Matrix

-- @@ L15-15 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator

-- @@ L16-16 verbatim
open MeasureTheory Matrix

-- @@ L17-17 verbatim
open scoped TensorProduct

-- @@ L18-18 verbatim
open scoped BigOperators Pointwise Topology

-- @@ L19-19 verbatim
open MeasureTheory Filter

-- @@ L20-20 verbatim
open scoped BigOperators Pointwise

-- @@ L21-21 verbatim
open scoped BigOperators Topology

-- @@ L22-22 verbatim
open scoped TensorProduct BigOperators

-- @@ L23-23 verbatim
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

-- @@ L24-24 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L26-26 verbatim
open Filter

-- @@ L27-27 verbatim
namespace EuclideanRamsey

-- @@ L28-28 verbatim
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup


-- @@ L30-30 verbatim
section Ultrafilters

-- @@ L31-31 verbatim
variable {M : Type uModule} [Monoid M]

-- @@ L32-37 verbatim
@[simp] lemma pure_mul_ultra (x : M) (V : Ultrafilter M) :
    (pure x : Ultrafilter M)*V = V.map (x*·) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]

-- @@ L38-43 verbatim
@[simp] lemma mul_pure_ultra (U : Ultrafilter M) (y : M) :
    U*(pure y : Ultrafilter M) = U.map (·*y) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]


-- @@ L45-55 verbatim
@[instance_reducible] def ultrafilterMonoid : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := by
    change (pure (1:M) : Ultrafilter M)*U=U
    rw [pure_mul_ultra]
    simp
  mul_one U := by
    change U*(pure (1:M) : Ultrafilter M)=U
    rw [mul_pure_ultra]
    simp


-- @@ L57-57 verbatim
end Ultrafilters


-- @@ L59-61 verbatim
inductive UltraColumn (ι : Type uIndex) (M : Type uModule)
  | common (U : Ultrafilter M)
  | principal (x : ι → M)


-- @@ L63-63 verbatim
namespace UltraColumn

-- @@ L64-64 verbatim
variable {ι : Type uIndex} {M : Type uModule}

-- @@ L65-67 verbatim
def value : UltraColumn ι M → ι → Ultrafilter M
  | .common U,_ => U
  | .principal x,i => pure (x i)

-- @@ L68-70 verbatim
def Realizes : UltraColumn ι M → (ι → M) → Prop
  | .common _,x => ∃ y,∀ i,x i=y
  | .principal y,x => x=y


-- @@ L72-83 verbatim
lemma choose [Finite ι] (q : UltraColumn ι M) (p : ι → M → Prop)
    (h : ∀ i,∀ᶠ x in (q.value i : Filter M),p i x) :
    ∃ x : ι → M,q.Realizes x ∧ ∀ i,p i (x i) := by
  cases q with
  | common U =>
    have hh : ∀ᶠ x in (U : Filter M),∀ i,p i x := Filter.eventually_all.mpr h
    obtain ⟨x,hx⟩ := hh.exists
    exact ⟨fun _ => x,⟨x,fun _ => rfl⟩,hx⟩
  | principal x =>
    refine ⟨x,rfl,?_⟩
    intro i
    simpa [value] using h i


-- @@ L85-109 verbatim
theorem simultaneously_realize [Finite ι] [Monoid M] (qs : List (UltraColumn ι M))
    (B : ι → Set M)
    (h : letI := ultrafilterMonoid (M:=M)
      ∀ i,B i ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M)) :
    ∃ xs : List (ι → M), List.Forall₂ Realizes qs xs ∧
      ∀ i, (xs.map (fun x => x i)).prod ∈ B i := by
  let := ultrafilterMonoid (M:=M)
  induction qs generalizing B with
  | nil =>
    refine ⟨[],.nil,?_⟩
    intro i
    have hi := h i
    change B i ∈ (pure (1:M) : Ultrafilter M) at hi
    simpa using hi
  | cons q qs ih =>
    have hh (i : ι) : ∀ᶠ x in (q.value i : Filter M),
        {y | x*y∈B i} ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M) := by
      have hi := h i
      change ∀ᶠ z in ((q.value i)*(qs.map (fun q => q.value i)).prod : Ultrafilter M), z∈B i at hi
      exact (Ultrafilter.eventually_mul _ _ _).mp hi
    obtain ⟨x,hx,hxB⟩ := q.choose _ hh
    obtain ⟨xs,hxs,hB⟩ := ih (fun i => {y | x i*y∈B i}) hxB
    refine ⟨x::xs,.cons hx hxs,?_⟩
    intro i
    simpa using hB i

-- @@ L110-110 verbatim
end UltraColumn

-- @@ L111-111 verbatim
end EuclideanRamsey

-- @@ L112-112 verbatim
namespace EuclideanRamsey

-- @@ L113-113 verbatim
open Filter

-- @@ L114-114 verbatim
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

-- @@ L115-115 verbatim
variable {ι : Type uIndex}


-- @@ L117-122 verbatim
inductive ColumnPath (a : ι → FiniteEuclidean) : List (UltraColumn ι Strings) → ℝ → Prop
  | nil : ColumnPath a [] 0
  | common (U : Ultrafilter Strings) : ColumnPath a [.common U] 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      ColumnPath a [.principal (fun i => FreeMonoid.of (b i))] u
  | append {p q u v} : ColumnPath a p u → ColumnPath a q v → ColumnPath a (p++q) (u+v)


-- @@ L124-157 verbatim
lemma ColumnPath.realizes {a : ι → FiniteEuclidean} {qs u} (h : ColumnPath a qs u)
    (xs : List (ι → Strings)) (hx : List.Forall₂ UltraColumn.Realizes qs xs) :
    StringFamily a u (fun i => (xs.map (fun x => x i)).prod) := by
  induction h generalizing xs with
  | nil =>
    cases hx
    simpa using StringFamily.common a 1
  | common U =>
    cases hx with
    | cons hx hn =>
      cases hn
      obtain ⟨x,hx⟩ := hx
      simpa [hx] using StringFamily.common a x
  | copy b hb =>
    cases hx with
    | cons hx hn =>
      cases hn
      change _ = _ at hx
      subst hx
      simpa using StringFamily.single hb
  | @append p q u v _ _ ihp ihq =>
    have hp : List.Forall₂ UltraColumn.Realizes p (xs.take p.length) := by
      have hh := List.forall₂_take p.length hx
      simpa only [List.take_left] using hh
    have hq : List.Forall₂ UltraColumn.Realizes q (xs.drop p.length) := by
      have hh := List.forall₂_drop p.length hx
      simpa only [List.drop_left] using hh
    have hmul := (ihp (xs.take p.length) hp).mul (ihq (xs.drop p.length) hq)
    have he : (fun i => ((xs.take p.length).map (fun x => x i)).prod) *
        (fun i => ((xs.drop p.length).map (fun x => x i)).prod) =
        (fun i => (xs.map (fun x => x i)).prod) := by
      funext i
      simp only [Pi.mul_apply,← List.prod_append,← List.map_append,List.take_append_drop]
    rwa [he] at hmul


-- @@ L159-178 verbatim
lemma Path.expand {a : ι → FiniteEuclidean} {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p) :
    ∃ qs : List (UltraColumn ι Strings),ColumnPath a qs u ∧
      (letI := ultrafilterMonoid (M:=Strings); ∀ i,(qs.map (fun q => q.value i)).prod=Ψ (w i)) := by
  let := ultrafilterMonoid (M:=Strings)
  induction h with
  | diag g => exact ⟨[.common (Ψ g)],.common _,by intro i; simp [UltraColumn.value]⟩
  | @copy u b hb =>
    refine ⟨[.common p,.principal (fun i => FreeMonoid.of (b i)),.common p],?_,?_⟩
    · simpa using (ColumnPath.common p).append ((ColumnPath.copy b hb).append (.common p))
    · intro i
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,UltraColumn.value,mul_one,hgen,mul_assoc]
  | @mul w v u t hu hv ihu ihv =>
    obtain ⟨qs,hqs,hqe⟩ := ihu
    obtain ⟨rs,hrs,hre⟩ := ihv
    refine ⟨qs++rs,hqs.append hrs,?_⟩
    intro i
    simp only [List.map_append,List.prod_append,hqe,hre,Pi.mul_apply]
    exact (Ψ.map_mul _ _).symm


-- @@ L180-188 verbatim
lemma ColumnPath.flatten {α : Type uAlpha} {a : ι → FiniteEuclidean} (l : List α)
    (qs : α → List (UltraColumn ι Strings)) (u : α → ℝ)
    (h : ∀ j∈l,ColumnPath a (qs j) (u j)) :
    ColumnPath a ((l.map qs).flatten) ((l.map u).sum) := by
  induction l with
  | nil => simpa using (ColumnPath.nil (a:=a))
  | cons j l ih =>
    simpa only [List.map_cons,List.flatten_cons,List.sum_cons] using
      (h j (by simp)).append (ih (fun k hk => h k (by simp [hk])))


-- @@ L190-201 verbatim
lemma flattened_ultra_product {α : Type uAlpha} (l : List α) (qs : α → List (UltraColumn ι Strings))
    (U : α → ι → Ultrafilter Strings)
    (h : letI := ultrafilterMonoid (M:=Strings); ∀ j∈l,∀ i,((qs j).map (fun q => q.value i)).prod=U j i) :
    letI := ultrafilterMonoid (M:=Strings)
    ∀ i,(((l.map qs).flatten).map (fun q => q.value i)).prod=(l.map (fun j => U j i)).prod := by
  let := ultrafilterMonoid (M:=Strings)
  intro i
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,List.prod_append,List.prod_cons]
    rw [h j (by simp) i,ih (fun k hk => h k (by simp [hk]))]

-- @@ L202-202 verbatim
end EuclideanRamsey


-- @@ L204-204 verbatim
end


-- @@ L206-206 verbatim
end OAI
