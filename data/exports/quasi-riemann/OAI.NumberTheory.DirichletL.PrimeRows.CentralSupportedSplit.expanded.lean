import OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L8-8 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical

-- @@ L9-9 verbatim
local notation "O" => HeckeFamily.O


-- @@ L11-13 verbatim
def supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0)


-- @@ L15-17 verbatim
def supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0)


-- @@ L19-22 verbatim
@[simp] lemma mem_supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedFloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0 :=
  Finset.mem_filter


-- @@ L24-27 verbatim
@[simp] lemma mem_supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedNonfloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0 :=
  Finset.mem_filter


-- @@ L29-34 verbatim
lemma nonfloor_grid_positive (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow)
    (hu : u∈supportedNonfloorRows S hmax R grid) (e : ℝ) (he : 0<e) :
    51/100<(51/100:ℝ)+e*grid u := by
  have hg : 0<(grid u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ((mem_supportedNonfloorRows S hmax R grid u).mp hu).2.2
  linarith [mul_pos he hg]


-- @@ L36-64 verbatim
theorem finiteCentralCubeRows_supported_split {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (grid : FreeRow→ℕ) (H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun _=>51/100) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
  have hfilter := finiteCentralCubeRows_filter_calibration S hS hmax η R T hT W Yp W0 W1 X Y Z e
    (fun u=>51/100+e*grid u) H
  refine hfilter.symm.trans ?_
  let Rs := R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0)
  have hfloor : Rs.filter (fun u=>grid u=0)=supportedFloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedFloorRows]
  have hn : Rs.filter (fun u=>¬grid u=0)=supportedNonfloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedNonfloorRows]
  have hsplit : finiteCentralCubeRows S hS hmax η Rs T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
    unfold finiteCentralCubeRows
    rw [←hfloor,←hn]
    exact (Finset.sum_filter_add_sum_filter_not Rs (fun u=>grid u=0) _).symm
  refine hsplit.trans ?_
  refine congrArg₂ (fun x y : ℂ => x + y) ?_ rfl
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  have hg := ((mem_supportedFloorRows S hmax R grid u).mp hu).2.2
  simp only [hg,Nat.cast_zero,mul_zero,add_zero]


-- @@ L66-72 verbatim
lemma normalized_nonfloor_error (A F Cfloor Cnon N : ℂ) (E B : ℝ)
    (hE : ‖A/N-F-(Cfloor+Cnon)/N‖≤E) (hB : ‖Cfloor/N‖≤B) :
    ‖A/N-F-Cnon/N‖≤E+B := by
  calc
    _ = ‖(A/N-F-(Cfloor+Cnon)/N)+Cfloor/N‖ := by congr 1;ring
    _ ≤ ‖A/N-F-(Cfloor+Cnon)/N‖+‖Cfloor/N‖ := norm_add_le _ _
    _ ≤ E+B := add_le_add hE hB


-- @@ L74-74 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L76-76 verbatim
end


-- @@ L78-78 verbatim
end OAI
