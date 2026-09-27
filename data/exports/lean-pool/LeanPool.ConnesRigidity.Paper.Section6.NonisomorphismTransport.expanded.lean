/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import LeanPool.ConnesRigidity.Paper.Section6.Nonisomorphism
import LeanPool.ConnesRigidity.Paper.Section6.NonisomorphismEmbedding
import LeanPool.ConnesRigidity.Paper.Section6.QuotientModuleTransport


-- @@ L12-16 verbatim
/-!
This file exposes the concrete Section 6 module-equivalence conclusion for
the actual Zhou carriers. The proof uses the public characteristic-kernel
and quotient transport files in this project.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Connes

-- @@ L21-21 verbatim
namespace PaperNonisomorphism


-- @@ L23-23 verbatim
open Construction

-- @@ L24-24 verbatim
open Construction.PaperKernel

-- @@ L25-25 verbatim
open PaperCharacteristicTransport


-- @@ L27-29 verbatim
noncomputable section

/- A group isomorphism induces the module equivalence required in Section 6 (Zhou §6). -/

-- @@ L30-43 verbatim
theorem paperCharacteristicModuleEquiv
    (f : PaperKernel.paperGammaOne ≃* PaperKernel.paperGammaTwo) :
    ∃ σ : PaperKernel.Q ≃* PaperKernel.Q, Nonempty
      ((qRepresentationOne).asModule ≃ₗ[Ring]
        (qRepresentationTwoAlong σ).asModule) := by
  have hchar : Subgroup.map f.toMonoidHom
      (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom :=
    kernelSubgroup_characteristic PaperKernel.paperThetaOneHom
      PaperKernel.paperThetaTwoHom f
  let σ := quotientAutomorphism PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar
  refine ⟨σ, ⟨LinearEquiv.ofBijective (paperModuleLinearMap f hchar)
    (paperModuleLinearMap_bijective f hchar)⟩⟩


-- @@ L45-53 verbatim
/-- The concrete Zhou groups are nonisomorphic from the first-module input (Zhou §6). -/
theorem paperNotIsomorphic
    (hOne : moduleOneSemisimple) :
    ¬ Nonempty
      (PaperKernel.paperGammaOne ≃* PaperKernel.paperGammaTwo) := by
  rintro ⟨f⟩
  obtain ⟨σ, ⟨e⟩⟩ := paperCharacteristicModuleEquiv f
  apply paper_moduleTwoAlong_not_semisimple σ
  exact e.isSemisimpleModule_iff.mp hOne


-- @@ L55-55 verbatim
end

-- @@ L56-56 verbatim
end PaperNonisomorphism

-- @@ L57-57 verbatim
end Connes
