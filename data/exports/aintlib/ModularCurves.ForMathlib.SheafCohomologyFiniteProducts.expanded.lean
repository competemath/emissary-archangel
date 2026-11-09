import ModularCurves.ForMathlib.SheafCechSheafResolution


-- @@ L3-9 verbatim
/-!
# Sheaf cohomology of finite products

This file identifies genuine sheaf cohomology of a finite product with the product of
the cohomology groups, then applies the result to the finite products occurring in the
sheaf-level Cech resolution.
-/


-- @@ L11-11 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace


-- @@ L13-13 verbatim
universe u


-- @@ L15-15 verbatim
namespace CategoryTheory.Sheaf.H


-- @@ L17-17 verbatim
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

-- @@ L18-18 verbatim
variable [HasSheafify J AddCommGrpCat.{u}]

-- @@ L19-19 verbatim
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]


-- @@ L21-32 verbatim
/-- Genuine sheaf cohomology commutes with finite products. -/
noncomputable def addEquivPi {ι : Type u} [Finite ι]
    (F : ι → Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    H (∏ᶜ F) n ≃+ ∀ i, H (F i) n := by
  letI := Fintype.ofFinite ι
  let e : Discrete.functor F ⋙ functorH J n ≅
      Discrete.functor (fun i => (functorH J n).obj (F i)) :=
    Discrete.natIso fun _ => Iso.refl _
  exact ((preservesLimitIso (functorH J n) (Discrete.functor F)) ≪≫
    HasLimit.isoOfNatIso e ≪≫
      AddCommGrpCat.productIsoPi
        (fun i => (functorH J n).obj (F i))).addCommGroupIsoToAddEquiv


-- @@ L34-40 verbatim
/-- A finite product of sheaves has subsingleton cohomology when each factor does. -/
theorem subsingleton_product_of_factors {ι : Type u} [Finite ι]
    (F : ι → Sheaf J AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ i, Subsingleton (H (F i) n)) : Subsingleton (H (∏ᶜ F) n) := by
  letI (i : ι) : Subsingleton (H (F i) n) := h i
  let e := addEquivPi F n
  exact ⟨fun x y => e.injective (funext fun i => Subsingleton.elim (e x i) (e y i))⟩


-- @@ L42-42 verbatim
end CategoryTheory.Sheaf.H


-- @@ L44-44 verbatim
namespace TopCat.Sheaf


-- @@ L46-46 verbatim
variable {X : TopCat.{u}}

-- @@ L47-47 verbatim
variable (F : Sheaf AddCommGrpCat.{u} X)

-- @@ L48-48 verbatim
variable {ι : Type u} (U : ι → Opens X)


-- @@ L50-57 verbatim
/-- A finite Cech term has vanishing cohomology in a degree whenever all of its
restriction-pushforward factors do. -/
theorem cechTerm_subsingleton_H_of_factors [Finite ι] (n q : ℕ)
    (h : ∀ i : Fin (n + 1) → ι,
      Subsingleton (H (cechTermFactor F U n i) q)) :
    Subsingleton (H (cechTerm F U n) q) := by
  exact CategoryTheory.Sheaf.H.subsingleton_product_of_factors
    (cechTermFactor F U n) q h


-- @@ L59-59 verbatim
end TopCat.Sheaf
