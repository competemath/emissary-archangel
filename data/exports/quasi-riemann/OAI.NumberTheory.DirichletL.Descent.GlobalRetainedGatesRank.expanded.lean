import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesChildren


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentGlobalRetainedGates

-- @@ L8-8 verbatim
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents

-- @@ L9-9 verbatim
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic

-- @@ L10-10 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks

-- @@ L11-11 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L13-13 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

-- @@ L14-14 verbatim
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L16-42 verbatim
theorem supported_row_rank_decrease (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z M ell A t V j eta shortCutoff : ℝ)
    (hZ : 1<Z) (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : shortCutoff≤ell+V) (hsmall : eta≤shortCutoff/16)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : ∀y∈original,Z^(j-eta)≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    ∀d∈keys p source,actualCellRowExponent Z M ell A t V j eta d+3*shortCutoff/2≤M := by
  intro source d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hxs := cell_subset p source d hx
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b X
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b X
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>Z^(j-eta)≤‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2) hJ
  exact actual_cell_row_decrease p hp source hs hk d x hx Z M ell A t V j eta shortCutoff
    hZ hA ht heta hbin hterminal hsmall (hb₁ x hxs) (hb₂ x hxs) (hj x hxs)


-- @@ L44-44 verbatim
end SevenEighths.InverseMomentGlobalRetainedGates

-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
