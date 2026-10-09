import OAI.ModelTheory.Categoricity.Colors


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace CHObstruction


-- @@ L11-11 verbatim
open Cardinal Ordinal Order


-- @@ L13-13 verbatim
namespace EndpointDiagrams


-- @@ L15-15 verbatim
open Diagrams CountableClosures Tuples


-- @@ L17-17 verbatim
abbrev V := ZFSet.vonNeumann (ω_ (2 : Ordinal.{u}))

-- @@ L18-18 verbatim
abbrev D := Shrink.{u} V.{u}


-- @@ L20-20 verbatim
def element : D.{u} ≃ V.{u} := (equivShrink V).symm


-- @@ L22-22 verbatim
def membership (a b : D.{u}) : Prop := (element a).val ∈ (element b).val


-- @@ L24-29 verbatim
theorem separates : ∀ a b : D.{u}, a ≠ b → ∃ w, ¬ (membership w a ↔ membership w b) := by
  intro a b hab
  obtain ⟨w, hw⟩ := membership_separates V (ZFSet.isTransitive_vonNeumann _)
    (element a) (element b) (fun he => hab (element.injective he))
  refine ⟨element.symm w, ?_⟩
  simpa only [membership, Equiv.apply_symm_apply] using hw


-- @@ L31-32 verbatim
def rank (a : D.{u}) : Domination.Alpha.{u} :=
  ⟨(element a).val.rank, ZFSet.mem_vonNeumann.1 (element a).property⟩


-- @@ L34-35 verbatim
def seed {k : ℕ} (t : Fin k ↪ D.{u}) (J : {J : Finset (Fin k) // J.Nonempty}) :
    FiniteSeed D.{u} := ⟨J.val.map t, J.property.map⟩


-- @@ L37-37 verbatim
def fullSeed (t : Tuple D.{u}) : FiniteSeed D.{u} := seed t.2 ⟨Finset.univ, Finset.univ_nonempty⟩


-- @@ L39-40 verbatim
def entry {k : ℕ} (t : Fin k ↪ D.{u}) (l : Label (Fin k)) : D.{u} :=
  (enumeration membership separates (seed t l.1) l.2).val


-- @@ L42-46 verbatim
theorem entry_mem (t : Tuple D.{u}) (l : Label (Fin (t.1 + 1))) :
    entry t.2 l ∈ entries membership separates (fullSeed t) := by
  exact entries_mono membership separates (seed t.2 l.1) (fullSeed t)
    (Finset.map_subset_map.mpr (Finset.subset_univ _))
    (enumeration membership separates (seed t.2 l.1) l.2).property


-- @@ L48-51 verbatim
theorem entry_surjective (t : Tuple D.{u}) (x : entries membership separates (fullSeed t)) :
    ∃ l, entry t.2 l = x.val := by
  obtain ⟨n, hn⟩ := enumeration_surjective membership separates (fullSeed t) x
  exact ⟨(⟨Finset.univ, Finset.univ_nonempty⟩, n), congrArg Subtype.val hn⟩


-- @@ L53-60 verbatim
theorem entry_root {k : ℕ} (t : Fin k ↪ D.{u}) (i : Fin k) :
    entry t (Label.root i) = t i := by
  have hs : seed t (Label.root i).1 = ⟨{t i}, Finset.singleton_nonempty _⟩ := by
    apply Subtype.ext
    exact Finset.map_singleton _ _
  unfold entry
  rw [hs]
  exact enumeration_singleton membership separates (t i)


-- @@ L62-69 verbatim
theorem entry_comp {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (l : Label (Fin m)) :
    entry (e.trans t) l = entry t (Label.map e l) := by
  have hs : seed (e.trans t) l.1 = seed t (Label.map e l).1 := by
    apply Subtype.ext
    exact (Finset.map_map e t l.1.val).symm
  unfold entry
  rw [hs]
  rfl


-- @@ L71-71 verbatim
def beta (b : Tag.{u}) : Domination.Beta.{u} := b.toOrd


-- @@ L73-74 verbatim
def localTag (b : Tag.{u}) (a : D.{u}) : Tag.{u} :=
  Ordinal.ToType.mk (Domination.values (rank a) (beta b))


-- @@ L76-78 verbatim
@[simp] theorem localTag_value (b : Tag.{u}) (a : D.{u}) :
    tagOrdinal (localTag b a) = (Domination.values (rank a) (beta b)).val := by
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)


-- @@ L80-83 verbatim
def diagram {k : ℕ} (t : Fin k ↪ D.{u}) (b : Tag.{u}) : Diagram.{u} (Fin k) where
  eqv l l' := entry t l = entry t l'
  rel l l' := membership (entry t l) (entry t l')
  tag l := localTag b (entry t l)


-- @@ L85-91 verbatim
theorem diagram_restrict {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (b : Tag.{u}) :
    diagram (e.trans t) b = (diagram t b).restrict e := by
  unfold diagram Diagram.restrict
  congr 1 <;> funext l
  · funext l'; rw [entry_comp, entry_comp]
  · funext l'; rw [entry_comp, entry_comp]
  · rw [entry_comp]


-- @@ L93-95 verbatim
def Good (X : FiniteSeed D.{u}) (b : Tag.{u}) : Prop :=
  ∀ a c : entries membership separates X, membership a.val c.val →
    tagOrdinal (localTag b a.val) < tagOrdinal (localTag b c.val)


-- @@ L97-118 verbatim
theorem countable_bad (X : FiniteSeed D.{u}) : {b | ¬ Good X b}.Countable := by
  classical
  have : Countable (entries membership separates X) :=
    Set.countable_coe_iff.2 (entries_countable membership separates X)
  let bad (a c : entries membership separates X) : Set Tag.{u} :=
    if h : membership a.val c.val then
      {b | (Domination.values (rank c.val) (beta b)).val ≤
        (Domination.values (rank a.val) (beta b)).val} else ∅
  have hb : ∀ a c, (bad a c).Countable := by
    intro a c
    dsimp only [bad]
    split_ifs with h
    · have hr : (rank a.val).val < (rank c.val).val := ZFSet.rank_lt_of_mem h
      exact (Domination.countable_exceptions (rank c.val) ⟨(rank a.val).val, hr⟩).preimage
        Ordinal.ToType.mk.symm.injective
    · exact Set.countable_empty
  apply (Set.countable_iUnion (fun a => Set.countable_iUnion (hb a))).mono
  intro b h
  simp only [Good, not_forall] at h
  obtain ⟨a, c, hm, hlt⟩ := h
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨c, by
    simpa only [bad, dite_eq_left hm, Set.mem_ofPred_eq, localTag_value, not_lt] using hlt⟩⟩


-- @@ L120-124 verbatim
theorem good_mono {X Y : FiniteSeed D.{u}} (hXY : X.val ⊆ Y.val) {b : Tag.{u}}
    (h : Good Y b) : Good X b := by
  intro a c hac
  exact h ⟨a.val, entries_mono membership separates X Y hXY a.property⟩
    ⟨c.val, entries_mono membership separates X Y hXY c.property⟩ hac


-- @@ L126-146 verbatim
theorem diagram_valid (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    (diagram t.2 b).Valid := by
  constructor
  · exact ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  · intro a a' c c' haa hcc
    change membership _ _ ↔ membership _ _
    rw [show entry t.2 a = entry t.2 a' from haa,
      show entry t.2 c = entry t.2 c' from hcc]
  · intro a a' haa
    exact congrArg (localTag b) haa
  · intro a c hac
    exact hb ⟨entry t.2 a, entry_mem t a⟩ ⟨entry t.2 c, entry_mem t c⟩ hac
  · intro a c h
    apply CountableClosures.extensional membership separates
      (entry_mem t a) (entry_mem t c)
    intro z hz
    obtain ⟨l, hl⟩ := entry_surjective t ⟨z, hz⟩
    simpa only [diagram, hl] using h l
  · intro i j hij
    apply t.2.injective
    simpa only [diagram, entry_root] using hij


-- @@ L148-152 verbatim
theorem sub_seed (t : Tuple D.{u}) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    (fullSeed (sub t e)).val ⊆ (fullSeed t).val := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)


-- @@ L154-155 verbatim
def colors (hCH : CH.{u}) (t : Tuple D.{u}) (b : Tag.{u}) : Colors.Palette.{u} :=
  Colors.code hCH ⟨t.1, diagram t.2 b⟩


-- @@ L157-162 verbatim
theorem passes (hCH : CH.{u}) (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    Tests.Test hCH (fun t => colors hCH t b) t := by
  refine ⟨diagram t.2 b, ?_⟩
  intro m e
  rw [← diagram_restrict]
  exact ⟨diagram_valid (sub t e) b (good_mono (sub_seed t e) hb), rfl⟩


-- @@ L164-166 verbatim
theorem countable_failures (hCH : CH.{u}) (t : Tuple D.{u}) :
    {b | ¬ Tests.Test hCH (fun t => colors hCH t b) t}.Countable :=
  (countable_bad (fullSeed t)).mono (fun b h hb => h (passes hCH t b hb))


-- @@ L168-175 verbatim
theorem cardinal : #D.{u} = endpoint.{u} := by
  change V.card = _
  rw [ZFSet.card_vonNeumann]
  apply Cardinal.preBeth_of_omega0_sq_le
  apply le_of_lt
  rw [← Cardinal.ord_aleph, Cardinal.lt_ord, pow_two, Ordinal.card_mul,
    Ordinal.card_omega0, Cardinal.aleph0_mul_aleph0]
  exact Cardinal.aleph0_lt_aleph.2 (by norm_num)


-- @@ L177-177 verbatim
end EndpointDiagrams


-- @@ L179-179 verbatim
end CHObstruction


-- @@ L181-181 verbatim
end


-- @@ L183-183 verbatim
end OAI
