import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusOn
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.PullbackTrivialOnFiber


-- @@ L6-20 verbatim
/-! # Line bundles on a discrete scheme are trivial

If the underlying space of `Z` is discrete (e.g. an Artinian / finite scheme) and `L` is a line bundle on `Z`,
then `L ≅ O_Z`.

Proof: every point `z` has an open neighbourhood with a frame (`exists_frame`), which restricts to the open
point `{z}` (`pt z`); the open points form a pairwise disjoint open cover and `Γ(L, ∅)` is a singleton, so
these sections glue to a global section `s` (`exists_glue`, `TopCat.Sheaf.existsUnique_gluing'`); `s` is a
frame on every `pt z`, so by gluing of frames (`IsFrame.of_sSup`) `s` is a frame on `⊤`, and
`IsFrame.trivialization` + `iso_unit_of_trivialization_top` give `L ≅ O_Z`.

References: Stacks 00NX (finite projective modules over a local ring are free) + the sentence "`i^*E` is
trivial on a finite discrete scheme" in the proof of Stacks 0AYT. `pt` / `exists_glue` coincide with the
lemmas of the same name in `Stacks0ayt_FreeOfArtinian` (arbitrary rank), re-proved here to avoid importing
that module. -/


-- @@ L22-22 verbatim
set_option autoImplicit false

-- @@ L23-23 verbatim
set_option maxHeartbeats 400000


-- @@ L25-25 verbatim
universe u


-- @@ L27-27 verbatim
open CategoryTheory Opposite TopologicalSpace

-- @@ L28-28 verbatim
open scoped AlgebraicGeometry


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace MiyaokaMori.LineBundleTrivialOfDiscrete


-- @@ L34-34 verbatim
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules


-- @@ L36-36 verbatim
variable {Z : AlgebraicGeometry.Scheme.{u}}


-- @@ L38-47 verbatim
/-- Sections of a module over the empty open form a singleton (`TopCat.Sheaf.isTerminalOfEmpty`). -/
theorem subsingleton_sections_bot (N : Z.Modules) : Subsingleton Γ(N, ⊥) := by
  have t : Limits.IsTerminal (N.val.presheaf.obj (op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Z)
  have h : (𝟙 (N.val.presheaf.obj (op (⊥ : Z.Opens)))) = 0 := t.hom_ext _ _
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Γ(N, ⊥), z = 0 := fun z => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) z) h
    exact this
  rw [hx x, hx y]


-- @@ L49-52 verbatim
theorem subsingleton_sections_of_eq_bot (N : Z.Modules) (V : Z.Opens) (hV : V = ⊥) :
    Subsingleton Γ(N, V) := by
  subst hV
  exact subsingleton_sections_bot N


-- @@ L54-55 verbatim
/-- The open point `{z}` of a discrete scheme. -/
def pt [DiscreteTopology Z] (z : Z) : Z.Opens := ⟨{z}, isOpen_discrete _⟩


-- @@ L57-57 verbatim
theorem mem_pt [DiscreteTopology Z] (z : Z) : z ∈ pt z := Set.mem_singleton z


-- @@ L59-63 verbatim
theorem pt_le [DiscreteTopology Z] {z : Z} {V : Z.Opens} (hz : z ∈ V) : pt z ≤ V := by
  intro w hw
  have hw' : w = z := hw
  rw [hw']
  exact hz


-- @@ L65-70 verbatim
theorem pt_inf_eq_bot [DiscreteTopology Z] {z w : Z} (h : z ≠ w) : pt z ⊓ pt w = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have h1 : v = z := hv.1
  have h2 : v = w := hv.2
  exact absurd (h1.symm.trans h2) h


-- @@ L72-73 verbatim
theorem le_iSup_pt [DiscreteTopology Z] : (⊤ : Z.Opens) ≤ ⨆ z, pt z :=
  fun z _ => Opens.mem_iSup.mpr ⟨z, mem_pt z⟩


-- @@ L75-88 verbatim
/-- **Gluing along the open points of a discrete scheme**: given sections `u z ∈ Γ(E, {z})` on the open
points, there is a global section restricting to them (the open points are pairwise disjoint, so
compatibility is automatic). -/
theorem exists_glue [DiscreteTopology Z] (E : Z.Modules) (u : ∀ z : Z, Γ(E, pt z)) :
    ∃ s : Γ(E, ⊤), ∀ z, E.presheaf.map (homOfLE le_top).op s = u z := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} Z := ⟨E.val.presheaf, E.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 pt u := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Subsingleton.elim (Opens.infLELeft (pt i) (pt i)) (Opens.infLERight (pt i) (pt i))]
    · exact @Subsingleton.elim _ (subsingleton_sections_of_eq_bot E (pt i ⊓ pt j) (pt_inf_eq_bot hij)) _ _
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' pt ⊤ (fun z => homOfLE le_top) le_iSup_pt u hcompat
  exact ⟨s, hs⟩


-- @@ L90-106 verbatim
/-- A line bundle on a discrete scheme has a global frame. -/
theorem exists_isFrame_top_of_discreteTopology [DiscreteTopology Z] (L : Z.Modules) [L.IsLineBundle] :
    ∃ s : Γ(L, ⊤), IsFrame L ⊤ s := by
  have hloc : ∀ z : Z, ∃ u : Γ(L, pt z), IsFrame L (pt z) u := by
    intro z
    obtain ⟨W, hzW, e, he⟩ := exists_frame L z
    exact ⟨L.presheaf.map (homOfLE (pt_le hzW)).op e, he.restrict (pt_le hzW)⟩
  choose u hu using hloc
  obtain ⟨s, hs⟩ := exists_glue L u
  refine ⟨s, IsFrame.of_sSup (Set.range pt) (fun _ _ => le_top) ?_ ?_⟩
  · intro z _
    rw [Opens.mem_sSup]
    exact ⟨pt z, ⟨z, rfl⟩, mem_pt z⟩
  · rintro V ⟨z, rfl⟩
    have h : L.res (le_top : pt z ≤ ⊤) s = u z := hs z
    rw [h]
    exact hu z


-- @@ L108-112 verbatim
/-- **Line bundles on a discrete scheme are trivial**: `L ≅ O_Z`. -/
theorem nonempty_iso_unit_of_discreteTopology [DiscreteTopology Z] (L : Z.Modules) [L.IsLineBundle] :
    Nonempty (L ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  obtain ⟨s, hs⟩ := exists_isFrame_top_of_discreteTopology L
  exact iso_unit_of_trivialization_top L hs.trivialization rfl


-- @@ L114-114 verbatim
end MiyaokaMori.LineBundleTrivialOfDiscrete


-- @@ L116-116 verbatim
end
