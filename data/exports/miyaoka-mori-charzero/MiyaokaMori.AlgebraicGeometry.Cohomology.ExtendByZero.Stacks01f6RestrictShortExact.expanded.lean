import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackOpenImmersionShortExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sx
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sy
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyShift


-- @@ L7-33 verbatim
/-! # Restriction along an open immersion is exact and preserves flasqueness

**Restriction of `O_Y`-modules along an open immersion `j : X → Y` is exact, and preserves
flasqueness** (Stacks 01E1, cohomology-lemma-cohomology-of-open, first sentence of the proof:
"restriction to an open is exact, and the restriction of an injective sheaf is flasque";
Hartshorne III.2.5 and III Ex. 2.3(c)). Auxiliary module for Stacks 01F6.

Contents:
* `shortExact_map_restrictFunctor`: `j^*` (Mathlib `Scheme.Modules.restrictFunctor j`, whose
  sections over `W ⊆ X` are *definitionally* the sections of `M` over `j(W)`) preserves short exact
  sequences. Monomorphisms are preserved by `mono_restrictFunctor_map`
  (`PullbackOpenImmersionShortExact.lean`, which also proves the statement for the isomorphic functor `pullback j`; we need the
  `restrictFunctor` form because of its definitional sections); epimorphisms because `j^*` is a
  left adjoint (Mathlib `restrictAdjunction : restrictFunctor j ⊣ pushforward j`); exactness because
  a left adjoint preserves cokernels and in a short exact sequence `g` is the cokernel of `f`
  (Mathlib `Exact.map_of_epi_of_preservesCokernel`).
* `isFlasque_restrict`: `j^*` of a flasque module is flasque (its restriction maps are restriction
  maps of the original sheaf, along `j(W') ⊆ j(W)`).
* `subsingleton_sheafCohomology_of_isFlasque`, `subsingleton_sheafCohomology_restrict_of_injective`:
  `H^{k+1}(X, j^*I) = 0` for `I` injective (Stacks 09SX: injective ⇒ flasque, `isFlasque_of_injective`;
  Stacks 09SY: flasque ⇒ acyclic, `TopCat.Sheaf.H_subsingleton_of_isFlasque`, transported from `Ext`
  universe `u` to the universe `u+1` of `sheafCohomology` by `Ext.chgUniv`).
* Transport of sections, of surjectivity of `φ.app`, and of the cokernel group
  `Γ(R, U) ⧸ im Γ(I, U)` along an equality of opens `U₁ = U₂` (`subst`); and the identification of
  the `Γ(X, O_X)`-module quotient of `sheafCohomology.one_equiv_quotient` with the plain
  abelian-group quotient (`quotient_range_addEquiv_appTop`).
-/


-- @@ L35-35 verbatim
set_option autoImplicit false

-- @@ L36-36 verbatim
set_option maxHeartbeats 400000


-- @@ L38-38 verbatim
universe u


-- @@ L40-40 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L41-41 verbatim
open scoped AlgebraicGeometry


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L47-47 verbatim
section Restrict


-- @@ L49-49 verbatim
variable {X Y : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]


-- @@ L51-62 verbatim
/-- `j^*` preserves short exact sequences: it is a left adjoint (epimorphisms, cokernels) and it
preserves monomorphisms (`mono_restrictFunctor_map`, from `PullbackOpenImmersionShortExact`). -/
theorem shortExact_map_restrictFunctor {S : ShortComplex Y.Modules} (hS : S.ShortExact) :
    (S.map (restrictFunctor j)).ShortExact := by
  have hepi := hS.epi_g
  have hmono := hS.mono_f
  have : PreservesColimitsOfSize.{0, 0} (restrictFunctor j) :=
    (restrictAdjunction j).leftAdjoint_preservesColimits
  exact
    { exact := hS.exact.map_of_epi_of_preservesCokernel (restrictFunctor j) hepi inferInstance
      mono_f := mono_restrictFunctor_map j S.f
      epi_g := (restrictFunctor j).map_epi S.g }


-- @@ L64-67 verbatim
/-- `j^*` of a flasque module sheaf is flasque. -/
theorem isFlasque_restrict (M : Y.Modules) [hM : TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf] :
    TopCat.Sheaf.IsFlasque (M.restrict j).toAddCommGrpSheaf where
  epi {_U _V} i := hM.epi (j.opensFunctor.map i.unop).op


-- @@ L69-69 verbatim
end Restrict


-- @@ L71-77 verbatim
/-- Stacks 09SY at the universe of `sheafCohomology`: a flasque module sheaf has vanishing higher
cohomology. -/
theorem subsingleton_sheafCohomology_of_isFlasque {Z : AlgebraicGeometry.Scheme.{u}} (M : Z.Modules)
    [TopCat.Sheaf.IsFlasque M.toAddCommGrpSheaf] (k : ℕ) :
    Subsingleton (AlgebraicGeometry.sheafCohomology Z M (k + 1)) :=
  have _h := TopCat.Sheaf.H_subsingleton_of_isFlasque M.toAddCommGrpSheaf (k + 1) (Nat.succ_pos k)
  (Abelian.Ext.chgUniv.{u}).subsingleton


-- @@ L79-85 verbatim
/-- `H^{k+1}(X, j^*I) = 0` for `I` an injective `O_Y`-module (Stacks 01E1 / 09SX / 09SY). -/
theorem subsingleton_sheafCohomology_restrict_of_injective {X Y : AlgebraicGeometry.Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (I : Y.Modules) [Injective I] (k : ℕ) :
    Subsingleton (AlgebraicGeometry.sheafCohomology X (I.restrict j) (k + 1)) :=
  have _h1 : TopCat.Sheaf.IsFlasque I.toAddCommGrpSheaf := isFlasque_of_injective I
  have _h2 := isFlasque_restrict j I
  subsingleton_sheafCohomology_of_isFlasque (I.restrict j) k


-- @@ L87-87 verbatim
section Transport


-- @@ L89-89 verbatim
variable {X : AlgebraicGeometry.Scheme.{u}}


-- @@ L91-95 verbatim
/-- Sections over equal opens are the same abelian group. -/
theorem sections_addEquiv_of_eq (M : X.Modules) {U₁ U₂ : X.Opens} (h : U₁ = U₂) :
    Nonempty (Γ(M, U₁) ≃+ Γ(M, U₂)) := by
  subst h
  exact ⟨AddEquiv.refl _⟩


-- @@ L97-101 verbatim
/-- Surjectivity of `φ.app` is transported along an equality of opens. -/
theorem surjective_app_of_eq {M N : X.Modules} (φ : M ⟶ N) {U₁ U₂ : X.Opens} (h : U₁ = U₂)
    (hs : Function.Surjective (φ.app U₁)) : Function.Surjective (φ.app U₂) := by
  subst h
  exact hs


-- @@ L103-110 verbatim
/-- The cokernel group `Γ(R, U) ⧸ im (Γ(I, U) → Γ(R, U))` is transported along an equality of
opens. -/
theorem sectionsQuotient_addEquiv_of_eq {I R : X.Modules} (g : I ⟶ R) {U₁ U₂ : X.Opens}
    (h : U₁ = U₂) :
    Nonempty ((Γ(R, U₁) ⧸ AddMonoidHom.range (g.app U₁).hom) ≃+
      (Γ(R, U₂) ⧸ AddMonoidHom.range (g.app U₂).hom)) := by
  subst h
  exact ⟨AddEquiv.refl _⟩


-- @@ L112-130 verbatim
/-- The `Γ(X, O_X)`-module quotient `Γ(S.X₃, ⊤) ⧸ range (appTopLinear S.g)` (as in
`sheafCohomology.one_equiv_quotient`) is, as an abelian group, the quotient by the range of
`S.g.app ⊤`. -/
theorem quotient_range_addEquiv_appTop (S : ShortComplex X.Modules) :
    Nonempty ((Γ(S.X₃, ⊤) ⧸ LinearMap.range (Hom.appTopLinear S.g)) ≃+
      (Γ(S.X₃, ⊤) ⧸ AddMonoidHom.range (S.g.app ⊤).hom)) := by
  let p := LinearMap.range (Hom.appTopLinear S.g)
  let q : Γ(S.X₃, ⊤) →+ Γ(S.X₃, ⊤) ⧸ p := p.mkQ.toAddMonoidHom
  have hker : q.ker = AddMonoidHom.range (S.g.app ⊤).hom := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero p).1 hx)
      exact AddMonoidHom.mem_range.2 ⟨y, hy⟩
    · intro hx
      obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 hx
      exact (Submodule.Quotient.mk_eq_zero p).2 (LinearMap.mem_range.2 ⟨y, hy⟩)
  exact ⟨((QuotientAddGroup.quotientKerEquivOfSurjective q (Submodule.mkQ_surjective p)).symm).trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)⟩


-- @@ L132-132 verbatim
end Transport


-- @@ L134-134 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L136-136 verbatim
end
