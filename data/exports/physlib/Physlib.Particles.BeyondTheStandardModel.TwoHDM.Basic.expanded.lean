/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic

-- @@ L9-24 verbatim
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

## i. Overview

The two Higgs doublet model (2HDM) is an extension of the Standard Model which adds a second Higgs
doublet.

## References

* https://arxiv.org/abs/hep-ph/0605184. [ref: arxiv_hep_ph_0605184]
* https://arxiv.org/abs/1605.03237. [ref: arxiv_1605_03237]
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open StandardModel


-- @@ L30-34 verbatim
/-!

## A. The configuration space

-/


-- @@ L36-42 verbatim
/-- The configuration space of the two Higgs doublet model.
  In otherwords, the underlying vector space associated with the model. -/
structure TwoHiggsDoublet where
  /-- The first Higgs doublet. -/
  Φ1 : HiggsVec
  /-- The second Higgs doublet. -/
  Φ2 : HiggsVec


-- @@ L44-44 verbatim
namespace TwoHiggsDoublet


-- @@ L46-46 verbatim
open InnerProductSpace


-- @@ L48-52 verbatim
@[ext]
lemma ext_of_fst_snd {H1 H2 : TwoHiggsDoublet}
    (h1 : H1.Φ1 = H2.Φ1) (h2 : H1.Φ2 = H2.Φ2) : H1 = H2 := by
  cases H1
  congr

-- @@ L53-57 verbatim
/-!

## B. Gauge group actions

-/


-- @@ L59-62 verbatim
noncomputable instance : SMul StandardModel.GaugeGroupI TwoHiggsDoublet where
  smul g H :=
    { Φ1 := StandardModel.HiggsVec.repGaugeGroupI g H.Φ1
      Φ2 := StandardModel.HiggsVec.repGaugeGroupI g H.Φ2 }


-- @@ L64-66 verbatim
@[simp]
lemma gaugeGroupI_smul_fst (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ1 = StandardModel.HiggsVec.repGaugeGroupI g H.Φ1 := rfl


-- @@ L68-70 verbatim
@[simp]
lemma gaugeGroupI_smul_snd (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).Φ2 = StandardModel.HiggsVec.repGaugeGroupI g H.Φ2 := rfl


-- @@ L72-76 verbatim
noncomputable instance : MulAction StandardModel.GaugeGroupI TwoHiggsDoublet where
  one_smul H := by
    ext <;> simp
  mul_smul g1 g2 H := by
    ext <;> simp [Module.End.mul_apply]


-- @@ L78-78 verbatim
end TwoHiggsDoublet
