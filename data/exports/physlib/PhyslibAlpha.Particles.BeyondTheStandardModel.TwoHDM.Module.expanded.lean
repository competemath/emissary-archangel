/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.Basic

-- @@ L9-13 verbatim
/-!

# The Module structure on the two Higgs doublet model

-/

-- @@ L14-14 verbatim
@[expose] public section

-- @@ L15-19 verbatim
/-!

## The structure of a module

-/


-- @@ L21-21 verbatim
namespace TwoHiggsDoublet


-- @@ L23-24 verbatim
instance : Add TwoHiggsDoublet where
  add H1 H2 := { Φ1 := H1.Φ1 + H2.Φ1, Φ2 := H1.Φ2 + H2.Φ2 }


-- @@ L26-27 verbatim
@[simp]
lemma add_fst (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ1 = H1.Φ1 + H2.Φ1 := rfl


-- @@ L29-30 verbatim
@[simp]
lemma add_snd (H1 H2 : TwoHiggsDoublet) : (H1 + H2).Φ2 = H1.Φ2 + H2.Φ2 := rfl


-- @@ L32-33 verbatim
instance : Zero TwoHiggsDoublet where
  zero := { Φ1 := 0, Φ2 := 0 }


-- @@ L35-36 verbatim
@[simp]
lemma zero_fst : (0 : TwoHiggsDoublet).Φ1 = 0 := rfl


-- @@ L38-39 verbatim
@[simp]
lemma zero_snd : (0 : TwoHiggsDoublet).Φ2 = 0 := rfl


-- @@ L41-42 verbatim
instance : SMul ℂ TwoHiggsDoublet where
  smul c H := { Φ1 := c • H.Φ1, Φ2 := c • H.Φ2 }


-- @@ L44-45 verbatim
@[simp]
lemma smul_fst (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ1 = c • H.Φ1 := rfl


-- @@ L47-48 verbatim
@[simp]
lemma smul_snd (c : ℂ) (H : TwoHiggsDoublet) : (c • H).Φ2 = c • H.Φ2 := rfl


-- @@ L50-51 verbatim
instance : Neg TwoHiggsDoublet where
  neg H := { Φ1 := -H.Φ1, Φ2 := -H.Φ2 }


-- @@ L53-54 verbatim
@[simp]
lemma neg_fst (H : TwoHiggsDoublet) : (-H).Φ1 = -H.Φ1 := rfl


-- @@ L56-57 verbatim
@[simp]
lemma neg_snd (H : TwoHiggsDoublet) : (-H).Φ2 = -H.Φ2 := rfl


-- @@ L59-71 verbatim
instance : AddCommGroup TwoHiggsDoublet where
  add_assoc H1 H2 H3 := by
    ext <;> simp [add_assoc]
  zero_add H := by
    ext <;> simp
  add_zero H := by
    ext <;> simp
  nsmul := nsmulRec
  add_comm H1 H2 := by
    ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel H := by
    ext <;> simp [neg_add_cancel]


-- @@ L73-85 verbatim
instance : Module ℂ TwoHiggsDoublet where
  smul_add c H1 H2 := by
    ext <;> simp [smul_add]
  add_smul c1 c2 H := by
    ext <;> simp [add_smul]
  one_smul H := by
    ext <;> simp [one_smul]
  mul_smul c1 c2 H := by
    ext <;> simp [mul_smul]
  smul_zero c := by
    ext <;> simp [smul_zero]
  zero_smul H := by
    ext <;> simp [zero_smul]


-- @@ L87-87 verbatim
end TwoHiggsDoublet
