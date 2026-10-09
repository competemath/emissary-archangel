import OAI.Combinatorics.EuclideanRamsey.CornerGroup


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uModule uColor


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

-- @@ L25-25 verbatim
open Filter

-- @@ L26-26 verbatim
open Set


-- @@ L28-28 verbatim
namespace EuclideanRamsey

-- @@ L29-29 verbatim
open Filter

-- @@ L30-30 verbatim
open scoped BigOperators

-- @@ L31-31 verbatim
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup


-- @@ L33-36 verbatim
lemma exists_ultra_color {M : Type uModule} {κ : Type uColor} [Finite κ] (U : Ultrafilter M) (c : M → κ) :
    ∃ k,{x | c x=k}∈U := by
  apply Ultrafilter.eventually_exists_iff.mp
  exact Filter.Eventually.of_forall (fun x => ⟨c x,rfl⟩)

-- @@ L37-38 verbatim
noncomputable def ultraColor {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) : κ :=
  (exists_ultra_color U c).choose

-- @@ L39-40 verbatim
lemma ultraColor_spec {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {x | c x=ultraColor c U}∈U := (exists_ultra_color U c).choose_spec


-- @@ L42-57 verbatim
lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p := by
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨p,hp,hi⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  let := Corner.group hp hi
  let letter (z : FiniteEuclidean) : Corner p :=
    ⟨p*(pure (FreeMonoid.of z))*p,by
      constructor
      · simp only [← mul_assoc,hp]
      · simp only [mul_assoc,hp]⟩
  let ψ : LetterGroup →* Corner p := FreeGroup.lift letter
  let v : Corner p →ₙ* Ultrafilter Strings := { toFun := Subtype.val, map_mul' _ _ := rfl }
  refine ⟨p,v.comp ψ.toMulHom,?_⟩
  intro z
  change (ψ (FreeGroup.of z)).val=_
  exact congrArg (fun x : Corner p => x.val) (FreeGroup.lift_apply_of (f:=letter) (x:=z))


-- @@ L59-121 verbatim
theorem paths_monochromatic {s : ℕ} (a : Fin s → FiniteEuclidean)
    (hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ))
    {κ : Type uColor} [Finite κ] (c : FiniteEuclidean → κ) :
    ∃ b : Fin s → FiniteEuclidean,(∀ i j,‖b i-b j‖=‖a i-a j‖) ∧
      ∃ k : κ,∀ i,c (b i)=k := by
  classical
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) κ
  let := hβ
  obtain ⟨w,lmb,μ,hp,hm,hlmb,hratio⟩ := hpaths (Fintype.card β+1) (by omega)
  obtain ⟨W,hW⟩ := synchronize_paths (Fintype.card β+1) (by omega) hp hm hlmb hratio
  obtain ⟨p,Ψ,hgen⟩ := exists_corner_map
  let coloring : Strings → κ := fun x => c (FiniteEuclidean.flatten x.toList)
  let L : List β := Finset.univ.toList
  let C : (β → Fin s) → κ := fun x => ultraColor coloring ((L.map (fun j => Ψ (W (x j)))).prod)
  obtain ⟨line,k,hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter (fun j => line.idxFun j=none)
  let t := S.card
  have ht : 1 ≤ t := by
    apply Finset.card_pos.mpr
    obtain ⟨j,hj⟩ := line.proper
    exact ⟨j,by simp [S,hj]⟩
  have htn : t ≤ Fintype.card β+1 := le_trans (Finset.card_le_univ S) (Nat.le_succ _)
  obtain ⟨qs,hqs,hqe⟩ := (hW t ht htn).expand Ψ p hgen
  let q (j : β) : List (UltraColumn (Fin s) Strings) :=
    (line.idxFun j).elim qs (fun i => [.common (Ψ (W i))])
  let u (j : β) : ℝ := if line.idxFun j=none then 1/(t:ℝ) else 0
  have hcol : ∀ j∈L,ColumnPath a (q j) (u j) := by
    intro j _
    cases he : line.idxFun j with
    | none => simpa [q,u,he] using hqs
    | some i => simpa [q,u,he] using (ColumnPath.common (a:=a) (Ψ (W i)))
  have hprod : ∀ j∈L,∀ i,((q j).map (fun q => q.value i)).prod=Ψ (W (line i j)) := by
    intro j _ i
    cases he : line.idxFun j with
    | none => simpa [q,he,Combinatorics.Line.coe_apply] using hqe i
    | some x => simp [q,he,Combinatorics.Line.coe_apply,UltraColumn.value]
  have hweight : (L.map u).sum=1 := by
    have he : (L.map u).sum=∑ j,u j := by
      simp [L]
    rw [he]
    change (∑ j,if line.idxFun j=none then 1/(t:ℝ) else 0)=1
    rw [← Finset.sum_filter]
    change (∑ j∈S,1/(t:ℝ))=1
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (t:ℝ)*(1/(t:ℝ))=1
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))
  have hfull : ColumnPath a ((L.map q).flatten) 1 := by
    convert ColumnPath.flatten L q u hcol using 1
    exact hweight.symm
  have hmem : ∀ i,{x : Strings | coloring x=k}∈
      ((((L.map q).flatten).map (fun q => q.value i)).prod : Ultrafilter Strings) := by
    intro i
    rw [flattened_ultra_product L q (fun j i => Ψ (W (line i j))) hprod i]
    have hk := ultraColor_spec coloring ((L.map (fun j => Ψ (W (line i j)))).prod)
    change {x | coloring x=C (line i)}∈_ at hk
    rwa [hline i] at hk
  obtain ⟨xs,hxs,hxB⟩ := UltraColumn.simultaneously_realize ((L.map q).flatten)
    (fun _ => {x : Strings | coloring x=k}) hmem
  let b (i : Fin s) := FiniteEuclidean.flatten ((xs.map (fun x => x i)).prod : Strings).toList
  refine ⟨b,(hfull.realizes xs hxs).congruent,k,?_⟩
  exact hxB

-- @@ L122-122 verbatim
end EuclideanRamsey

-- @@ L123-123 verbatim
namespace EuclideanRamsey

-- @@ L124-124 verbatim
namespace FiniteEuclidean

-- @@ L125-125 verbatim
open Filter

-- @@ L126-126 verbatim
open scoped BigOperators

-- @@ L127-128 verbatim
noncomputable def truncate (d : ℕ) (x : FiniteEuclidean) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => coords x i)


-- @@ L130-138 verbatim
lemma embed_truncate (x : FiniteEuclidean) (d : ℕ)
    (h : ∀ n∈(coords x).support,n<d) : embed d (truncate d x)=x := by
  apply Finsupp.ext
  intro n
  change coords (embed d (truncate d x)) n=coords x n
  by_cases hn : n<d
  · exact embed_apply d (truncate d x) ⟨n,hn⟩
  · rw [embed_outside d _ n (by omega)]
    exact (Finsupp.notMem_support_iff.mp (fun hm => hn (h n hm))).symm


-- @@ L140-147 verbatim
lemma eventually_embed_truncate (x : FiniteEuclidean) :
    ∀ᶠ d : ℕ in atTop,embed (d+1) (truncate (d+1) x)=x := by
  filter_upwards [eventually_ge_atTop ((coords x).support.sup id)] with d hd
  apply embed_truncate
  intro n hn
  have h := Finset.le_sup (f:=id) hn
  dsimp only [id_eq] at h
  omega

-- @@ L148-148 verbatim
end FiniteEuclidean


-- @@ L150-185 verbatim
theorem finite_coloring_compactness {s : ℕ} (a : Fin s → FiniteEuclidean) (r : ℕ)
    (h : ∀ c : FiniteEuclidean → Fin r,∃ b : Fin s → FiniteEuclidean,
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k) :
    ∃ D : ℕ,1≤D ∧ ∀ c : EuclideanSpace ℝ (Fin D) → Fin r,
      ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
  classical
  by_contra hbad
  have hc : ∀ n : ℕ,∃ c : EuclideanSpace ℝ (Fin (n+1)) → Fin r,
      ¬ ∃ b : Fin s → EuclideanSpace ℝ (Fin (n+1)),
        (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
    intro n
    by_contra hh
    push Not at hh
    exact hbad ⟨n+1,by omega,hh⟩
  choose c hc using hc
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let C : FiniteEuclidean → Fin r := fun z => ultraColor
    (fun n => c n (FiniteEuclidean.truncate (n+1) z)) U
  obtain ⟨b,hb,k,hbk⟩ := h C
  have hcolor : ∀ᶠ n in (U : Filter ℕ),∀ i,c n (FiniteEuclidean.truncate (n+1) (b i))=k := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := ultraColor_spec (fun n => c n (FiniteEuclidean.truncate (n+1) (b i))) U
    change ∀ᶠ n in (U : Filter ℕ),c n (FiniteEuclidean.truncate (n+1) (b i))=C (b i) at hh
    rwa [hbk i] at hh
  have he : ∀ᶠ n in (U : Filter ℕ),∀ i,FiniteEuclidean.embed (n+1)
      (FiniteEuclidean.truncate (n+1) (b i))=b i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Ultrafilter.of_le Filter.atTop) (FiniteEuclidean.eventually_embed_truncate (b i))
  obtain ⟨n,hn,hcol⟩ := (he.and hcolor).exists
  apply hc n
  refine ⟨fun i => FiniteEuclidean.truncate (n+1) (b i),?_,k,hcol⟩
  intro i j
  rw [← (FiniteEuclidean.embed (n+1)).norm_map, map_sub,hn i,hn j,hb]

-- @@ L186-186 verbatim
end EuclideanRamsey


-- @@ L188-188 verbatim
end


-- @@ L190-190 verbatim
end OAI
