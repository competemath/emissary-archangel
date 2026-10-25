import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleIsoOfModulesIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DetDualIso
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleHom
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.TangentBundle


-- @@ L8-16 verbatim
/-! # The determinant of the tangent bundle is the anticanonical bundle

`det T_X ≅ ω_X^{-1} = O_X(-K_X)`: the step of the degree identity `-K_X · f_*[C] = deg f^*T_X` of the
paper that replaces `-K_X` by the determinant of the tangent bundle.

The canonical form is `det_tangentBundle_iso_dual_canonicalBundle`: `det T_X ≅ ω_X^∨` with
`ω_X = canonicalBundle X = det Ω_X` (no divisor is chosen). The divisor form `det_tangentBundle_iso`
gives `det T_X ≅ O(-K)` for **every** Cartier divisor `K` with `O(K) ≅ ω_X`.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option maxHeartbeats 400000


-- @@ L21-21 verbatim
universe u v w u' v'


-- @@ L23-23 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L24-24 verbatim
open scoped AlgebraicGeometry


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-42 verbatim
/-- `det T_X ≅ ω_X^∨`: `T_X ≅ Ω_X^∨` (`tangentBundle_toModules`), `det` commutes with duals
(`VectorBundle.det_dual`), and `ω_X = det Ω_X` by definition. -/
theorem det_tangentBundle_iso_dual_canonicalBundle {k : Type*} [Field k] (X : SmoothProjectiveVariety k) :
    Nonempty ((tangentBundle X).det.toModules ≅
      AlgebraicGeometry.Scheme.Modules.dual (canonicalBundle X).toModules) := by
  obtain ⟨eT0⟩ := tangentBundle_toModules X
  have eT : (tangentBundle X).toModules ≅
      AlgebraicGeometry.Scheme.Modules.dual (cotangentBundle X).toModules := by
    let eΩ := Classical.choice (cotangentBundle_sheaf X)
    exact eT0 ≪≫ AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso eΩ
  have eExt : (tangentBundle X).det.toModules ≅
      (AlgebraicGeometry.VectorBundle.dual (cotangentBundle X)).det.toModules := by
    exact AlgebraicGeometry.Scheme.Modules.moduleExteriorIso X.toScheme (tangentBundle X).rank eT
  obtain ⟨eDetDual⟩ := VectorBundle.det_dual (cotangentBundle X)
  exact ⟨eExt ≪≫ eDetDual⟩


-- @@ L44-54 verbatim
/-- Divisor form: `det T_X ≅ O_X(-K)` for any canonical divisor `K` (`O(K) ≅ ω_X`). -/
theorem det_tangentBundle_iso {k : Type*} [Field k] (X : SmoothProjectiveVariety k)
    (K : CartierDivisor X.toVariety) (hK : Nonempty (K.lineBundle ≅ canonicalBundle X)) :
    Nonempty ((tangentBundle X).det ≅ (-K).lineBundle) := by
  obtain ⟨eTDual⟩ := det_tangentBundle_iso_dual_canonicalBundle X
  obtain ⟨eD⟩ := hK
  obtain ⟨eNeg⟩ := CartierDivisor.lineBundle_neg K
  have eNegK : (-K).lineBundle.toModules ≅
      AlgebraicGeometry.Scheme.Modules.dual (canonicalBundle X).toModules :=
    eNeg ≪≫ (AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (modulesIsoOfLineBundleIso eD)).symm
  exact ⟨lineBundleIsoOfModulesIso (eTDual ≪≫ eNegK.symm)⟩


-- @@ L56-56 verbatim
end
