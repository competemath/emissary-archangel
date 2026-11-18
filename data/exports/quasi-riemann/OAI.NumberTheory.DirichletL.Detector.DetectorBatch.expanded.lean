import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
import OAI.NumberTheory.DirichletL.Hecke.DetectorBatch


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-13 verbatim
def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0


-- @@ L15-16 verbatim
@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]


-- @@ L18-23 verbatim
theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0


-- @@ L25-25 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L26-26 verbatim
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L27-27 verbatim
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L29-63 verbatim
def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤mesh) (hb : 0<binWidth)
    (hwpos : ∀s∈slots,0<widths s) (hwmesh : ∀s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=>sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=>hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply


-- @@ L65-83 verbatim
lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith


-- @@ L85-89 verbatim
lemma physical_slot_scale {N : ℕ} (ell : Fin N→ℝ) (Z d : ℝ) (hZ : 0<Z) (hd : d≠0) (j : Fin N) :
    (Z^d)^(ell j/d)=Z^(ell j) := by
  rw [←Real.rpow_mul hZ.le]
  congr 1
  field_simp

-- @@ L90-90 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L92-92 verbatim
end


-- @@ L94-94 verbatim
end OAI
