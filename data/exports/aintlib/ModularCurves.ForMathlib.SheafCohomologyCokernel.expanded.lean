import ModularCurves.ForMathlib.SheafCohomologyExact


-- @@ L3-9 verbatim
/-!
# Degree-one sheaf cohomology as a cokernel

This file extracts the first nontrivial consequence of the long exact sequence in
sheaf cohomology. When the middle sheaf has vanishing first cohomology, the connecting
homomorphism presents the first cohomology of the kernel as a cokernel in abelian groups.
-/


-- @@ L11-11 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L13-13 verbatim
universe w' w v u


-- @@ L15-15 verbatim
namespace CategoryTheory.Sheaf.H


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- @@ L20-20 verbatim
variable [HasSheafify J AddCommGrpCat.{w}]

-- @@ L21-21 verbatim
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

-- @@ L22-22 verbatim
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)


-- @@ L24-28 verbatim
private noncomputable def zeroOneShortComplex : ShortComplex AddCommGrpCat.{w'} :=
  ShortComplex.mk ((functorH J 0).map S.g)
    (AddCommGrpCat.ofHom (δ hS 0 1 rfl)) (by
      ext x
      exact longSequence_comp_zero₃ hS 0 1 rfl x)


-- @@ L30-33 verbatim
private theorem zeroOneShortComplex_exact : (zeroOneShortComplex hS).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact longSequence_exact₃ hS 0 1 rfl x hx


-- @@ L35-39 verbatim
private theorem zeroOneShortComplex_epi
    [Subsingleton (H S.X₂ 1)] : Epi (zeroOneShortComplex hS).g := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  exact longSequence_exact₁ hS 0 1 rfl x (Subsingleton.elim _ _)


-- @@ L41-49 verbatim
/-- If the middle sheaf in a short exact sequence has vanishing `H¹`, then the
connecting homomorphism identifies `H¹` of the kernel with the cokernel of the
degree-zero map. -/
noncomputable def cokernelMapZeroIsoOne [Subsingleton (H S.X₂ 1)] :
    cokernel ((functorH J 0).map S.g) ≅ (functorH J 1).obj S.X₁ := by
  let T := zeroOneShortComplex hS
  letI : Epi T.g := zeroOneShortComplex_epi hS
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel T.f) (zeroOneShortComplex_exact hS).gIsCokernel


-- @@ L51-61 verbatim
/-- The cokernel comparison carries the cokernel projection to the connecting
homomorphism. -/
@[reassoc]
theorem cokernelMapZeroIsoOne_hom_fac [Subsingleton (H S.X₂ 1)] :
    cokernel.π ((functorH J 0).map S.g) ≫ (cokernelMapZeroIsoOne hS).hom =
      AddCommGrpCat.ofHom (δ hS 0 1 rfl) := by
  let T := zeroOneShortComplex hS
  letI : Epi T.g := zeroOneShortComplex_epi hS
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel T.f) (zeroOneShortComplex_exact hS).gIsCokernel
      WalkingParallelPair.one


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end CategoryTheory.Sheaf.H
