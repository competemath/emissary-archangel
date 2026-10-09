import OAI.Combinatorics.InfiniteMatroid.OrdinalRank
import OAI.Combinatorics.InfiniteMatroid.Columns
import OAI.Combinatorics.InfiniteMatroid.LocalBases


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open Set Filter Finset

-- @@ L9-9 verbatim
open scoped Topology symmDiff

-- @@ L10-10 verbatim
namespace InfiniteMatroidCounterexample


-- @@ L12-27 verbatim
lemma signed_columns_positive (P N : Finset ColumnTag) (hPN : Disjoint P N) :
    ¬ DSmall (columnPattern column P N) := by
  classical
  let F := P ∪ N
  let v (t : F) : Bool := decide (t.val ∈ P)
  apply mt (fun h ↦ dSmall_mono h ?_) (pattern_positive F v)
  intro x hx
  constructor
  · intro t ht
    have he := hx ⟨t, Finset.mem_union_left _ ht⟩
    simpa [v, ht, column] using he
  · intro t ht hc
    have hn : t ∉ P := fun hp ↦ Finset.disjoint_left.mp hPN hp ht
    have he := hx ⟨t, Finset.mem_union_right _ ht⟩
    have hf : x.2 (prefixString (columnString t) x.1) = false := by simpa [v, hn] using he
    exact Bool.false_ne_true (hf.symm.trans hc)


-- @@ L29-29 verbatim
def tagA (t : CIndex) : ColumnTag := (t,0)

-- @@ L30-30 verbatim
def tagB (t : CIndex) : ColumnTag := (t,1)

-- @@ L31-31 verbatim
def tagG (t : CIndex) : ColumnTag := (t,2)

-- @@ L32-32 verbatim
def AColumn (t : CIndex) : Set D := column (tagA t)

-- @@ L33-33 verbatim
def BColumn (t : CIndex) : Set D := column (tagB t)

-- @@ L34-34 verbatim
def GColumn (t : CIndex) : Set D := column (tagG t)


-- @@ L36-36 verbatim
def Ameet (F : Finset CIndex) : Set D := {x | ∀ t ∈ F, x ∈ AColumn t}

-- @@ L37-37 verbatim
def KSmall (X : Set D) : Prop := ∃ F : Finset CIndex, DSmall (X ∩ Ameet F)


-- @@ L39-46 verbatim
lemma Ameet_union (F H : Finset CIndex) : Ameet (F ∪ H) = Ameet F ∩ Ameet H := by
  ext x
  simp only [Ameet, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · exact fun h ↦ ⟨fun t ht ↦ h t (Or.inl ht), fun t ht ↦ h t (Or.inr ht)⟩
  · rintro ⟨hF,hH⟩ t (ht|ht)
    · exact hF t ht
    · exact hH t ht


-- @@ L48-50 verbatim
lemma dSmall_kSmall {X : Set D} (h : DSmall X) : KSmall X := by
  refine ⟨∅, ?_⟩
  simpa [Ameet] using h


-- @@ L52-54 verbatim
lemma kSmall_mono {X Y : Set D} (hY : KSmall Y) (hXY : X ⊆ Y) : KSmall X := by
  obtain ⟨F,hF⟩ := hY
  exact ⟨F,dSmall_mono hF (inter_subset_inter_left _ hXY)⟩


-- @@ L56-65 verbatim
lemma kSmall_union {X Y : Set D} (hX : KSmall X) (hY : KSmall Y) : KSmall (X ∪ Y) := by
  classical
  obtain ⟨F,hF⟩ := hX
  obtain ⟨H,hH⟩ := hY
  refine ⟨F ∪ H, dSmall_mono (dSmall_union hF hH) ?_⟩
  rw [Ameet_union]
  intro x hx
  rcases hx.1 with hxX|hxY
  · exact Or.inl ⟨hxX,hx.2.1⟩
  · exact Or.inr ⟨hxY,hx.2.2⟩


-- @@ L67-71 verbatim
lemma Ameet_positive (F : Finset CIndex) : ¬ DSmall (Ameet F) := by
  classical
  apply mt (fun h ↦ dSmall_mono h ?_) (signed_columns_positive (F.image tagA) ∅ (by simp))
  intro x hx t ht
  exact hx.1 _ (mem_image.mpr ⟨t,ht,rfl⟩)


-- @@ L73-75 verbatim
lemma kSmall_proper : ¬ KSmall univ := by
  rintro ⟨F,hF⟩
  exact Ameet_positive F (by simpa using hF)


-- @@ L77-79 verbatim
noncomputable def KIdeal : SubsetIdeal D :=
  ⟨KSmall,dSmall_kSmall dSmall_empty, fun _ _ h hs ↦ kSmall_mono h hs,
    fun _ _ hX hY ↦ kSmall_union hX hY, kSmall_proper⟩


-- @@ L81-86 verbatim
lemma AColumn_compl_kSmall (t : CIndex) : KSmall (AColumn t)ᶜ := by
  classical
  refine ⟨{t}, ?_⟩
  have he : (AColumn t)ᶜ ∩ Ameet {t} = ∅ := by ext x; simp [Ameet]
  rw [he]
  exact dSmall_empty


-- @@ L88-115 verbatim
lemma Gpattern_kPositive (P N : Finset CIndex) (hPN : Disjoint P N) :
    ¬ KIdeal.small (columnPattern GColumn P N) := by
  classical
  rintro ⟨F,hF⟩
  let P' := F.image tagA ∪ P.image tagG
  let N' := N.image tagG
  have hd : Disjoint P' N' := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨v,hvN,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hu with hu|hu
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hu
      have : (0 : Fin 3) = 2 := congrArg Prod.snd he
      have hv : (0 : ℕ) = 2 := congrArg Fin.val this
      omega
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hu
      have htv : t = v := congrArg Prod.fst he
      exact Finset.disjoint_left.mp hPN (htv ▸ ht) hvN
  apply signed_columns_positive P' N' hd
  apply dSmall_mono hF
  intro x hx
  refine ⟨⟨?_,?_⟩, ?_⟩
  · intro t ht
    exact hx.1 _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))
  · intro t ht
    exact hx.2 _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
  · intro t ht
    exact hx.1 _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))


-- @@ L117-120 verbatim
lemma exists_concrete_rank : ∃ R : RankModel D, R.ideal = KIdeal := by
  obtain ⟨U,hUK,hG,hfinite⟩ := exists_rank_ultrafilter KIdeal GColumn Gpattern_kPositive
  obtain ⟨R,hK,_⟩ := exists_rankModel KIdeal GColumn U hUK hG hfinite
  exact ⟨R,hK⟩


-- @@ L122-122 verbatim
end InfiniteMatroidCounterexample

-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
