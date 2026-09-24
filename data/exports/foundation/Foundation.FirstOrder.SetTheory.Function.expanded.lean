module

public import Foundation.FirstOrder.SetTheory.Z


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Basic definitions and lemmata for relations and functions
-/


-- @@ L10-10 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L12-12 expanded
variable {V : Type*} [SetStructure V] [Nonempty V] [ModelsSet (Language.str V set) Zermelo]


-- @@ L14-14 verbatim
/-! ### Relations -/


-- @@ L16-16 expanded
noncomputable def domain (R : V) : V :=
  {x ∈ sUnion (sUnion R) ; ∃ y, kpair x y ∈ R}


-- @@ L18-18 expanded
noncomputable def range (R : V) : V :=
  {y ∈ sUnion (sUnion R) ; ∃ x, kpair x y ∈ R}


-- @@ L20-20 verbatim
section domain


-- @@ L22-24 expanded
lemma mem_sUnion_sUnion_of_kpair_mem_left {x y R : V} (h : kpair x y ∈ R) : x ∈ sUnion (sUnion R) :=
  by
  simp only [mem_sUnion_iff]
  refine ⟨{ x, y }, ⟨kpair x y, h, by simp [kpair]⟩, by simp⟩


-- @@ L26-27 expanded
lemma mem_domain_iff {R x : V} : x ∈ domain R ↔ ∃ y, kpair x y ∈ R := by
  simpa [domain] using fun _ ↦ mem_sUnion_sUnion_of_kpair_mem_left


-- @@ L29-29 expanded
def domain.dfn : SetTheorySemisentence 2 :=
  UnivQuantifier.all
    (LogicalConnective.iff
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
          (UnivQuantifier.all
            (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
      (ExsQuantifier.exs
        (UnivQuantifier.all
          (binop% HArrow.hArrow
            ((kpair.dfn).nestFormulaeFunc
              (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
            (UnivQuantifier.all
              (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))))


-- @@ L31-31 expanded
instance domain.defined : DefinedFunction₁ (L := set) (M := V) domain domain.dfn :=
  ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := domain _), mem_domain_iff]⟩


-- @@ L33-33 expanded
instance domain.definable : DefinableFunction₁ (M := V) set domain :=
  domain.defined.to_definable


-- @@ L35-35 expanded
lemma mem_domain_of_kpair_mem {R x y : V} (h : kpair x y ∈ R) : x ∈ domain R :=
  mem_domain_iff.mpr ⟨y, h⟩


-- @@ L37-37 verbatim
@[simp] lemma domain_empty : domain (∅ : V) = ∅ := by ext; simp [mem_domain_iff]


-- @@ L39-43 expanded
@[simp]
lemma domain_prod (x y : V) [IsNonempty y] : domain (x ×ˢ y) = x :=
  by
  ext z
  suffices z ∈ x → ∃ x, x ∈ y by simpa [mem_domain_iff]
  intro _
  exact IsNonempty.nonempty


-- @@ L45-50 expanded
lemma domain_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : domain R ⊆ X :=
  by
  intro x hx
  have : ∃ y, kpair x y ∈ R := by simpa [mem_domain_iff] using hx
  rcases this with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hy
  exact this.1


-- @@ L52-55 verbatim
@[simp]
lemma domain_union {R₁ R₂ : V} : domain (R₁ ∪ R₂) = domain R₁ ∪ domain R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_domain_iff]; grind)


-- @@ L57-58 verbatim
lemma domain_inter_subset {R₁ R₂ : V} : domain (R₁ ∩ R₂) ⊆ domain R₁ ∩ domain R₂ := by
  intro p; simp only [mem_domain_iff, mem_inter_iff]; grind


-- @@ L60-61 expanded
@[simp, grind .]
lemma domain_insert {x y R : V} : domain (insert (kpair x y) R) = insert x (domain R) := by ext z;
  simp only [mem_domain_iff, mem_insert, kpair_iff]; grind


-- @@ L63-63 verbatim
end domain


-- @@ L65-65 verbatim
section range


-- @@ L67-69 expanded
lemma mem_sUnion_sUnion_of_kpair_mem_right {x y R : V} (h : kpair x y ∈ R) :
    y ∈ sUnion (sUnion R) := by
  simp only [mem_sUnion_iff]
  refine ⟨{ x, y }, ⟨kpair x y, h, by simp [kpair]⟩, by simp⟩


-- @@ L71-72 expanded
lemma mem_range_iff {R y : V} : y ∈ range R ↔ ∃ x, kpair x y ∈ R := by
  simpa [range] using fun _ ↦ mem_sUnion_sUnion_of_kpair_mem_right


-- @@ L74-74 expanded
def range.dfn : SetTheorySemisentence 2 :=
  UnivQuantifier.all
    (LogicalConnective.iff
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
          (UnivQuantifier.all
            (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
      (ExsQuantifier.exs
        (UnivQuantifier.all
          (binop% HArrow.hArrow
            ((kpair.dfn).nestFormulaeFunc
              (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2]) ![])))
            (UnivQuantifier.all
              (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))))


-- @@ L76-76 expanded
instance range.defined : DefinedFunction₁ (L := set) (M := V) range range.dfn :=
  ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := range _), mem_range_iff]⟩


-- @@ L78-78 expanded
instance range.definable : DefinableFunction₁ (M := V) set range :=
  range.defined.to_definable


-- @@ L80-80 expanded
lemma mem_range_of_kpair_mem {R x y : V} (h : kpair x y ∈ R) : y ∈ range R :=
  mem_range_iff.mpr ⟨x, h⟩


-- @@ L82-82 verbatim
@[simp] lemma range_empty : range (∅ : V) = ∅ := by ext; simp [mem_range_iff]


-- @@ L84-88 expanded
@[simp]
lemma range_prod (x y : V) [IsNonempty x] : range (x ×ˢ y) = y :=
  by
  ext z
  suffices z ∈ y → ∃ v, v ∈ x by simpa [mem_range_iff]
  intro _
  exact IsNonempty.nonempty


-- @@ L90-95 expanded
lemma range_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : range R ⊆ Y :=
  by
  intro y hy
  have : ∃ x, kpair x y ∈ R := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hx⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hx
  exact this.2


-- @@ L97-100 verbatim
@[simp]
lemma range_union {R₁ R₂ : V} : range (R₁ ∪ R₂) = range R₁ ∪ range R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_range_iff]; grind)


-- @@ L102-103 verbatim
lemma range_inter_subset {R₁ R₂ : V} : range (R₁ ∩ R₂) ⊆ range R₁ ∩ range R₂ := by
  intro p; simp only [mem_range_iff, mem_inter_iff]; grind


-- @@ L105-106 expanded
@[simp, grind =]
lemma range_insert {x y R : V} : range (insert (kpair x y) R) = insert y (range R) := by ext z;
  simp only [mem_range_iff, mem_insert, kpair_iff]; grind


-- @@ L108-108 verbatim
end range


-- @@ L110-110 verbatim
/-! ### Functions -/


-- @@ L112-112 expanded
noncomputable def function (Y X : V) : V :=
  {f ∈ power (X ×ˢ Y) ; ∀ x ∈ X, ∃! y, kpair x y ∈ f}


-- @@ L114-114 verbatim
noncomputable instance : Pow V V := ⟨fun Y X ↦ function Y X⟩


-- @@ L116-116 verbatim
lemma function_def {Y X : V} : Y ^ X = function Y X := rfl


-- @@ L118-118 expanded
lemma mem_function_iff {f Y X : V} : f ∈ Y ^ X ↔ f ⊆ X ×ˢ Y ∧ ∀ x ∈ X, ∃! y, kpair x y ∈ f := by
  simp [function, function_def]


-- @@ L120-120 expanded
def function.dfn : SetTheorySemisentence 3 :=
  UnivQuantifier.all
    (LogicalConnective.iff
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
          (UnivQuantifier.all
            (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
      (@HWedge.hWedge _ _ _ Wedge.instHWedge
        ((isSubsetOf).nestFormulae
          (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
            (vecCons
              ((prod.dfn).nestFormulaeFunc
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #4])
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3]) ![])))
              ![])))
        (UnivQuantifier.all
          (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #4])
            (Semiformula.ballMem (#0)
              (existsUnique
                (UnivQuantifier.all
                  (binop% HArrow.hArrow
                    ((kpair.dfn).nestFormulaeFunc
                      (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                        (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
                    (UnivQuantifier.all
                      (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                        (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))))))))


-- @@ L122-123 expanded
instance function.defined : DefinedFunction₂ (L := set) (M := V) (· ^ ·) function.dfn :=
  ⟨fun v ↦ by simp [function.dfn, mem_ext_iff (y := (v 1) ^ (v 2)), mem_function_iff]⟩


-- @@ L125-125 expanded
instance function.definable : DefinableFunction₂ (M := V) set (· ^ ·) :=
  function.defined.to_definable


-- @@ L127-128 expanded
lemma mem_function.intro {f X Y : V} (prod : f ⊆ X ×ˢ Y) (total : ∀ x ∈ X, ∃! y, kpair x y ∈ f) :
    f ∈ Y ^ X :=
  mem_function_iff.mpr ⟨prod, total⟩


-- @@ L130-130 expanded
lemma subset_prod_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ⊆ X ×ˢ Y :=
  mem_function_iff.mp h |>.1


-- @@ L132-133 expanded
lemma mem_of_mem_functions {f X Y : V} (h : f ∈ Y ^ X) (hx : kpair x y ∈ f) : x ∈ X ∧ y ∈ Y := by
  simpa using subset_prod_of_mem_function h _ hx


-- @@ L135-135 expanded
lemma function_subset_power_prod (X Y : V) : Y ^ X ⊆ power (X ×ˢ Y) := fun f hf ↦ by
  simpa using subset_prod_of_mem_function hf


-- @@ L137-137 expanded
lemma exists_unique_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃! y, kpair x y ∈ f :=
  mem_function_iff.mp h |>.2


-- @@ L139-143 expanded
lemma exists_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃ y ∈ Y, kpair x y ∈ f :=
  by
  intro x hx
  rcases (exists_unique_of_mem_function h x hx).exists with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hy
  exact ⟨y, this.2, hy⟩


-- @@ L145-154 expanded
lemma domain_eq_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : domain f = X :=
  by
  ext x
  suffices (∃ y, kpair x y ∈ f) ↔ x ∈ X by simpa [mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
    exact this.1
  · intro hx
    rcases exists_of_mem_function h x hx with ⟨y, hy⟩
    exact ⟨y, hy.2⟩


-- @@ L156-161 expanded
lemma range_subset_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : range f ⊆ Y :=
  by
  intro y hy
  have : ∃ x, kpair x y ∈ f := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hxy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
  exact this.2


-- @@ L163-176 expanded
lemma mem_function_range_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ∈ range f ^ X :=
  by
  have : f ⊆ X ×ˢ range f := by
    intro p hp
    have : ∃ x ∈ X, ∃ y ∈ Y, p = kpair x y := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function h _ hp
    rcases this with ⟨x, hx, y, hy, rfl⟩
    simpa [hx, mem_range_iff] using ⟨x, hp⟩
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption


-- @@ L178-188 expanded
lemma mem_function_of_mem_function_of_subset {f X Y₁ Y₂ : V} (h : f ∈ Y₁ ^ X) (hY : Y₁ ⊆ Y₂) :
    f ∈ Y₂ ^ X :=
  by
  have : f ⊆ X ×ˢ Y₂ :=
    calc
      f ⊆ X ×ˢ Y₁ := subset_prod_of_mem_function h
      _ ⊆ X ×ˢ Y₂ := prod_subset_prod_of_subset (by rfl) hY
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption


-- @@ L190-191 verbatim
lemma function_subset_function_of_subset {Y₁ Y₂ : V} (hY : Y₁ ⊆ Y₂) (X : V) : Y₁ ^ X ⊆ Y₂ ^ X :=
  fun _ hf ↦ mem_function_of_mem_function_of_subset hf hY


-- @@ L193-193 verbatim
@[simp] lemma empty_function_empty : (∅ : V) ^ (∅ : V) = {∅} := by ext z; simp [mem_function_iff]


-- @@ L195-197 verbatim
/-- Functions over arbitrary domain and range -/
class IsFunction (f : V) : Prop where
  mem_func : ∃ X Y : V, f ∈ Y ^ X


-- @@ L199-199 verbatim
lemma isFunction_def {f : V} : IsFunction f ↔ ∃ X Y : V, f ∈ Y ^ X := ⟨fun h ↦ h.mem_func, fun h ↦ ⟨h⟩⟩


-- @@ L201-201 expanded
def IsFunction.dfn : SetTheorySemisentence 1 :=
  ExsQuantifier.exs
    (ExsQuantifier.exs
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
          (UnivQuantifier.all
            (binop% HArrow.hArrow
              ((function.dfn).nestFormulaeFunc
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3]) ![])))
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0]))))))


-- @@ L203-203 expanded
instance IsFunction.defined : DefinedPred (L := set) (M := V) IsFunction dfn :=
  ⟨fun v ↦ by simp [isFunction_def, dfn]⟩


-- @@ L205-205 expanded
instance IsFunction.definable : DefinablePred (M := V) set IsFunction :=
  defined.to_definable


-- @@ L207-212 verbatim
lemma isFunction_iff {f : V} : IsFunction f ↔ f ∈ range f ^ domain f := by
  constructor
  · rintro ⟨X, Y, hf⟩
    simpa [domain_eq_of_mem_function hf] using mem_function_range_of_mem_function hf
  · intro h
    exact ⟨_, _, h⟩


-- @@ L214-214 verbatim
namespace IsFunction


-- @@ L216-216 verbatim
lemma of_mem {f X Y : V} (h : f ∈ Y ^ X) : IsFunction f := ⟨X, Y, h⟩


-- @@ L218-218 verbatim
lemma mem_function (f : V) [hf : IsFunction f] : f ∈ range f ^ domain f := isFunction_iff.mp hf


-- @@ L220-226 expanded
lemma mem_eq_kpair {f : V} [hf : IsFunction f] {p : V} (hpf : p ∈ f) : ∃ x y, p = kpair x y :=
  by
  rcases hf with ⟨X, Y, hfXY⟩
  have hsubset := (mem_function_iff.mp hfXY).1
  apply hsubset at hpf
  simp only [mem_prod_iff] at hpf
  rcases hpf with ⟨x, hxX, y, hyY, hpxy⟩
  exact ⟨x, y, hpxy⟩


-- @@ L228-247 expanded
@[grind ->]
lemma ofSubset (f g : V) [hf : IsFunction f] : g ⊆ f → IsFunction g :=
  by
  intro hgf
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro p hp
    have hpf : p ∈ f := hgf _ hp
    rcases
      show ∃ x ∈ domain f, ∃ y ∈ range f, p = kpair x y from by
        simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function _ hpf with
      ⟨x, -, y, -, rfl⟩
    have hxg : x ∈ domain g := mem_domain_of_kpair_mem hp
    have hyg : y ∈ range g := mem_range_of_kpair_mem hp
    simpa [mem_prod_iff] using And.intro hxg hyg
  · intro x hx
    rcases mem_domain_iff.mp hx with ⟨y, hxy⟩
    refine ExistsUnique.intro y hxy ?_
    intro y' hxy'
    have hyf : kpair x y ∈ f := hgf _ hxy
    have hy'f : kpair x y' ∈ f := hgf _ hxy'
    have hux : ∃! z, kpair x z ∈ f :=
      exists_unique_of_mem_function hf.mem_function x (mem_domain_of_kpair_mem hyf)
    exact hux.unique hy'f hyf


-- @@ L249-251 expanded
lemma unique {f : V} [hf : IsFunction f] {x y₁ y₂} (h₁ : kpair x y₁ ∈ f) (h₂ : kpair x y₂ ∈ f) :
    y₁ = y₂ :=
  by
  have : ∃! y, kpair x y ∈ f :=
    exists_unique_of_mem_function (isFunction_iff.mp hf) x (mem_domain_of_kpair_mem h₁)
  exact this.unique h₁ h₂


-- @@ L253-253 verbatim
@[simp] instance empty : IsFunction (∅ : V) := ⟨∅, ∅, by simp⟩


-- @@ L255-275 expanded
protected theorem insert (f x y : V) (hx : x ∉ domain f) [hf : IsFunction f] :
    IsFunction (insert (kpair x y) f) :=
  by
  refine ⟨insert x (domain f), insert y (range f), ?_⟩
  apply mem_function.intro
  · have : f ⊆ domain f ×ˢ range f := subset_prod_of_mem_function hf.mem_function
    exact insert_kpair_subset_insert_prod_insert_of_subset_prod this x y
  · intro z hz
    rcases show z = x ∨ z ∈ domain f by simpa using hz with (rfl | hz)
    · apply ExistsUnique.intro y (by simp)
      rintro y' H'
      rcases show y' = y ∨ kpair z y' ∈ f by simpa using H' with (rfl | H')
      · rfl
      have : z ∈ domain f := mem_domain_of_kpair_mem H'
      contradiction
    · rcases mem_domain_iff.mp hz with ⟨v, hzv⟩
      have : v ∈ range f := mem_range_of_kpair_mem hzv
      apply ExistsUnique.intro v (by simp [hzv])
      rintro w Hw
      rcases show z = x ∧ w = y ∨ kpair z w ∈ f by simpa using Hw with (⟨rfl, rfl⟩ | Hw)
      · have : z ∈ domain f := mem_domain_of_kpair_mem hzv
        contradiction
      exact hf.unique Hw hzv


-- @@ L277-277 expanded
@[simp]
instance (x y : V) : IsFunction ({kpair x y} : V) := by
  simpa using IsFunction.insert ∅ x y (by simp)


-- @@ L279-279 verbatim
end IsFunction


-- @@ L281-291 expanded
lemma function_eq_of_subset {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X) (h : f ⊆ g) : f = g :=
  by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply subset_antisymm h
  intro p hp
  rcases
    show ∃ x ∈ X, ∃ y ∈ Y, p = kpair x y from by
      simpa [mem_prod_iff] using subset_prod_of_mem_function hg _ hp with
    ⟨x, hx, y, hy, rfl⟩
  rcases show ∃ y' ∈ Y, kpair x y' ∈ f from exists_of_mem_function hf x hx with ⟨y', hy', Hf⟩
  have : kpair x y' ∈ g := h _ Hf
  rcases show y = y' from IsFunction.unique hp (h _ Hf)
  assumption


-- @@ L293-299 expanded
lemma function_ext {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X)
    (h : ∀ x ∈ X, ∀ y ∈ Y, kpair x y ∈ f → kpair x y ∈ g) : f = g :=
  by
  apply function_eq_of_subset hf hg
  intro p hp
  rcases
    show ∃ x ∈ X, ∃ y ∈ Y, p = kpair x y from by
      simpa [mem_prod_iff] using subset_prod_of_mem_function hf _ hp with
    ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy hp


-- @@ L301-311 expanded
@[grind <=]
lemma two_val_function_mem_iff_not {X f x : V} (hf : f ∈ (2 ^ X : V)) (hx : x ∈ X) :
    kpair x 0 ∈ f ↔ kpair x 1 ∉ f :=
  by
  have : IsFunction f := IsFunction.of_mem hf
  constructor
  · intro h0 h1
    have : (0 : V) = 1 := IsFunction.unique h0 h1
    simp_all
  · intro h1
    rcases exists_of_mem_function hf x hx with ⟨i, hi, hf⟩
    rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
    · assumption
    · contradiction


-- @@ L313-313 expanded
def Injective (R : V) : Prop :=
  ∀ x₁ x₂ y, kpair x₁ y ∈ R → kpair x₂ y ∈ R → x₁ = x₂


-- @@ L315-315 expanded
def Injective.dfn : SetTheorySemisentence 1 :=
  UnivQuantifier.all
    (UnivQuantifier.all
      (UnivQuantifier.all
        (@HArrow.hArrow _ _ _ Arrow.instHArrow
          (UnivQuantifier.all
            (binop% HArrow.hArrow
              ((kpair.dfn).nestFormulaeFunc
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
              (UnivQuantifier.all
                (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                  (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
          (@HArrow.hArrow _ _ _ Arrow.instHArrow
            (UnivQuantifier.all
              (binop% HArrow.hArrow
                ((kpair.dfn).nestFormulaeFunc
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                    (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
                (UnivQuantifier.all
                  (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                    (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
            (UnivQuantifier.all
              (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
                (UnivQuantifier.all
                  (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
                    (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0])))))))))


-- @@ L317-317 expanded
instance Injective.defined : DefinedPred (L := set) (M := V) Injective dfn :=
  ⟨fun v ↦ by simp [Injective, dfn]⟩


-- @@ L319-319 expanded
instance Injective.definable : DefinablePred (M := V) set Injective :=
  defined.to_definable


-- @@ L321-321 verbatim
lemma Injective.empty : Injective (∅ : V) := fun x₁ x₂ y ↦ by simp


-- @@ L323-324 expanded
/-- Identity -/
noncomputable def identity (X : V) : V :=
  {p ∈ X ×ˢ X ; ∃ x ∈ X, p = kpair x x}


-- @@ L326-329 expanded
lemma mem_identity_iff {X p : V} : p ∈ identity X ↔ ∃ x ∈ X, p = kpair x x :=
  by
  suffices ∀ x ∈ X, p = kpair x x → p ∈ X ×ˢ X by simpa [identity]
  rintro x hx rfl
  simp [hx]


-- @@ L331-331 expanded
def identity.dfn : SetTheorySemisentence 2 :=
  UnivQuantifier.all
    (LogicalConnective.iff
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
          (UnivQuantifier.all
            (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
          (Semiformula.bexsMem (#0)
            (UnivQuantifier.all
              (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
                (UnivQuantifier.all
                  (binop% HArrow.hArrow
                    ((kpair.dfn).nestFormulaeFunc
                      (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                        (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2]) ![])))
                    (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0])))))))))


-- @@ L333-333 expanded
instance identity.defined : DefinedFunction₁ (L := set) (M := V) identity dfn :=
  ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := identity (v 1)), mem_identity_iff]⟩


-- @@ L335-335 expanded
instance identity.definable : DefinableFunction₁ (M := V) set identity :=
  defined.to_definable


-- @@ L337-339 expanded
@[simp]
lemma kpair_mem_identity_iff {X x : V} : kpair x y ∈ identity X ↔ x ∈ X ∧ x = y :=
  by
  simp only [mem_identity_iff, kpair_iff, exists_eq_right_right', and_congr_left_iff]
  grind


-- @@ L341-350 expanded
@[simp]
lemma identity_mem_function (X : V) : identity X ∈ X ^ X :=
  by
  refine mem_function.intro ?_ ?_
  · intro p hp
    have : ∃ x ∈ X, p = kpair x x := by simpa [mem_identity_iff] using hp
    rcases this with ⟨x, hx, rfl⟩
    simp_all
  · intro x hx
    apply ExistsUnique.intro x (by simp [hx])
    simp only [kpair_mem_identity_iff, and_imp]
    grind


-- @@ L352-352 verbatim
instance IsFunction.identity (X : V) : IsFunction (identity X) := IsFunction.of_mem (identity_mem_function X)


-- @@ L354-358 verbatim
@[simp] lemma identity_injective (X : V) : Injective (identity X) := by
  intro x₁ x₂ y h₁ h₂
  rcases show x₁ ∈ X ∧ x₁ = y by simpa using h₁ with ⟨hx₁, rfl⟩
  rcases show x₂ ∈ X ∧ x₂ = x₁ by simpa using h₂ with ⟨hx₂, rfl⟩
  rfl


-- @@ L360-361 expanded
/-- Composition -/
noncomputable def compose (R S : V) : V :=
  {p ∈ domain R ×ˢ range S ; ∃ x y z, kpair x y ∈ R ∧ kpair y z ∈ S ∧ p = kpair x z}


-- @@ L363-366 expanded
lemma mem_compose_iff {R S p : V} :
    p ∈ compose R S ↔ ∃ x y z, kpair x y ∈ R ∧ kpair y z ∈ S ∧ p = kpair x z :=
  by
  simp only [compose, exists_and_left, mem_sep_iff, and_iff_right_iff_imp, forall_exists_index,
    and_imp]
  rintro x y hxy z hyz rfl
  simp [mem_domain_of_kpair_mem hxy, mem_range_of_kpair_mem hyz]


-- @@ L368-371 expanded
@[simp]
lemma kpair_mem_compose_iff {R S x z : V} :
    kpair x z ∈ compose R S ↔ ∃ y, kpair x y ∈ R ∧ kpair y z ∈ S :=
  by
  simp only [mem_compose_iff, kpair_iff, exists_and_left, exists_eq_right_right']
  grind


-- @@ L373-378 expanded
lemma compose_subset_prod {X Y Z R S : V} (hR : R ⊆ X ×ˢ Y) (hS : S ⊆ Y ×ˢ Z) :
    compose R S ⊆ X ×ˢ Z := by
  intro p hp
  rcases mem_compose_iff.mp hp with ⟨x, y, z, hxy, hyz, rfl⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using hR _ hxy
  have : y ∈ Y ∧ z ∈ Z := by simpa using hS _ hyz
  simp_all


-- @@ L380-396 expanded
lemma compose_function {X Y Z f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ Y) : compose f g ∈ Z ^ X :=
  by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply mem_function.intro ?_ ?_
  · exact compose_subset_prod (subset_prod_of_mem_function hf) (subset_prod_of_mem_function hg)
  · intro x hx
    have : ∃ y ∈ Y, kpair x y ∈ f := exists_of_mem_function hf x hx
    rcases this with ⟨y, hy, hxy⟩
    have : ∃ z ∈ Z, kpair y z ∈ g := exists_of_mem_function hg y hy
    rcases this with ⟨z, hz, hyz⟩
    apply ExistsUnique.intro z (by simpa using ⟨y, hxy, hyz⟩)
    intro z' hz'
    have : ∃ y', kpair x y' ∈ f ∧ kpair y' z' ∈ g := by simpa using hz'
    rcases this with ⟨y', hxy', hy'z'⟩
    rcases IsFunction.unique hxy hxy'
    rcases IsFunction.unique hyz hy'z'
    rfl


-- @@ L398-408 expanded
lemma compose_injective {R S : V} (hR : Injective R) (hS : Injective S) : Injective (compose R S) :=
  by
  intro x₁ x₂ z h₁ h₂
  have : ∃ y₁, kpair x₁ y₁ ∈ R ∧ kpair y₁ z ∈ S := by simpa using h₁
  rcases this with ⟨y₁, hx₁y₁, hy₁z⟩
  have : ∃ y₂, kpair x₂ y₂ ∈ R ∧ kpair y₂ z ∈ S := by simpa using h₂
  rcases this with ⟨y₂, hx₂y₂, hy₂z⟩
  have : y₁ = y₂ := hS y₁ y₂ z hy₁z hy₂z
  rcases this
  exact hR x₁ x₂ y₁ hx₁y₁ hx₂y₂


-- @@ L409-409 expanded
noncomputable def value (f x : V) :=
  {z ∈ sUnion (range f) ; ∃ y, z ∈ y ∧ kpair x y ∈ f}


-- @@ L411-412 verbatim
/-- If `x` is in `domain f`, then `f ‘ x` is the value of `f` at `x`, else it is `∅`. -/
scoped notation f:arg " ‘ " x:arg => value f x


-- @@ L414-414 expanded
def value.dfn : SetTheorySemisentence 3 :=
  UnivQuantifier.all
    (LogicalConnective.iff
      (UnivQuantifier.all
        (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
          (UnivQuantifier.all
            (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
      (@HWedge.hWedge _ _ _ Wedge.instHWedge
        (UnivQuantifier.all
          (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
            (UnivQuantifier.all
              (binop% HArrow.hArrow
                ((sUnion.dfn).nestFormulaeFunc
                  (vecCons
                    ((range.dfn).nestFormulaeFunc
                      (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #4]) ![]))
                    ![]))
                (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
        (ExsQuantifier.exs
          (@HWedge.hWedge _ _ _ Wedge.instHWedge
            (UnivQuantifier.all
              (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                (UnivQuantifier.all
                  (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
                    (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))
            (UnivQuantifier.all
              (binop% HArrow.hArrow
                ((kpair.dfn).nestFormulaeFunc
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                    (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
                (UnivQuantifier.all
                  (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #5])
                    (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))))))))


-- @@ L416-417 expanded
instance value.defined : DefinedFunction₂ (L := set) (M := V) value value.dfn :=
  ⟨fun v ↦ by simp [dfn, value]; simp only [mem_ext_iff, mem_sep_iff]⟩


-- @@ L419-419 expanded
instance value.definable : DefinableFunction₂ (M := V) set value :=
  value.defined.to_definable


-- @@ L421-432 expanded
lemma value_mem_range {f x : V} {X Y : V} (hf : f ∈ Y ^ X) (hx : x ∈ X) : f ‘ x ∈ range f :=
  by
  simp_all only [mem_function_iff, value, mem_range_iff]
  obtain ⟨hfleft, hfright⟩ := hf
  specialize hfright x hx
  obtain ⟨y, hy⟩ := ExistsUnique.exists hfright
  have h1 {w : V} : kpair x w ∈ f → w = y := by intro h; exact hfright.unique h hy
  have h2 : y = {z ∈ sUnion (range f) ; ∃ y, z ∈ y ∧ kpair x y ∈ f} :=
    by
    ext z
    simp only [mem_sep_iff, mem_sUnion_iff, mem_range_iff]
    constructor <;> intro h <;> grind
  grind


-- @@ L434-435 expanded
/-- Restricting the domain of a relation -/
noncomputable def restrict (R A : V) : V :=
  R ∩ (A ×ˢ range R)


-- @@ L437-438 verbatim
/-- Restricting the domain of a relation -/
scoped notation R:arg " ↾ " A:arg => restrict R A


-- @@ L440-440 expanded
def restrict.dfn : SetTheorySemisentence 3 :=
  UnivQuantifier.all
    (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
      (UnivQuantifier.all
        (binop% HArrow.hArrow
          ((inter.dfn).nestFormulaeFunc
            (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
              (vecCons
                ((prod.dfn).nestFormulaeFunc
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #4])
                    (vecCons
                      ((range.dfn).nestFormulaeFunc
                        (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3]) ![]))
                      ![])))
                ![])))
          (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0]))))


-- @@ L442-443 expanded
instance restrict.defined : DefinedFunction₂ (L := set) (M := V) restrict restrict.dfn :=
  ⟨fun v ↦ by simp [dfn, restrict]⟩


-- @@ L445-445 expanded
instance restrict.definable : DefinableFunction₂ (M := V) set restrict :=
  restrict.defined.to_definable


-- @@ L447-456 verbatim
@[simp] lemma domain_restrict_eq (R A : V) : domain (R ↾ A) = domain R ∩ A := by
  ext z
  apply Iff.intro <;> intro h
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    aesop
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    obtain ⟨⟨y, hy⟩, hzA⟩ := h
    use y
    simp_all only [kpair_mem_iff, true_and, mem_range_iff]
    use z


-- @@ L458-469 expanded
lemma mem_restrict_iff {R A p : V} : p ∈ (R ↾ A) ↔ p ∈ R ∧ ∃ x ∈ A, ∃ y, p = kpair x y :=
  by
  constructor
  · intro hp
    rcases show p ∈ R ∧ p ∈ A ×ˢ range R by simpa [restrict] using hp with ⟨hpR, hpP⟩
    rcases show ∃ x ∈ A, ∃ y ∈ range R, p = kpair x y by simpa [mem_prod_iff] using hpP with
      ⟨x, hxA, y, -, rfl⟩
    exact ⟨hpR, x, hxA, y, rfl⟩
  · rintro ⟨hpR, x, hxA, y, rfl⟩
    have hyR : y ∈ range R := mem_range_of_kpair_mem hpR
    have hpP : kpair x y ∈ A ×ˢ range R := by simpa [mem_prod_iff] using ⟨hxA, hyR⟩
    simpa [restrict] using And.intro hpR hpP


-- @@ L471-473 verbatim
@[simp] lemma restrict_subset (f A : V) : f ↾ A ⊆ f := by
  intro p hp
  exact (mem_restrict_iff.mp hp).1


-- @@ L475-476 verbatim
instance IsFunction.restrict (f A : V) [hf : IsFunction f] : IsFunction (f ↾ A) := by
  exact IsFunction.ofSubset f (f ↾ A) (restrict_subset f A)


-- @@ L478-486 expanded
lemma IsFunction.restrict_eq_self (f A : V) [hf : IsFunction f] (hA : domain f ⊆ A) : f ↾ A = f :=
  by
  apply subset_antisymm
  · intro p hp
    exact (mem_restrict_iff.mp hp).1
  · intro p hp
    rcases
      show ∃ x ∈ domain f, ∃ y ∈ range f, p = kpair x y from by
        simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function p hp with
      ⟨x, hxd, y, -, rfl⟩
    exact mem_restrict_iff.mpr ⟨hp, x, hA x hxd, y, rfl⟩


-- @@ L488-490 expanded
@[simp]
lemma kpair_mem_restrict_iff {R A x y : V} : kpair x y ∈ (R ↾ A) ↔ kpair x y ∈ R ∧ x ∈ A := by
  simp [mem_restrict_iff]


-- @@ L492-500 verbatim
lemma restrict_restrict_eq_restrict_inter (R A B : V) : (R ↾ A) ↾ B = R ↾ (A ∩ B) := by
  ext p
  simp only [mem_restrict_iff, mem_inter_iff]
  constructor
  · rintro ⟨⟨hpR, x, hxA, y, rfl⟩, x', hx'B, y', hxy⟩
    rcases kpair_inj hxy with ⟨rfl, rfl⟩
    exact ⟨hpR, x, ⟨hxA, hx'B⟩, y, rfl⟩
  · rintro ⟨hpR, x, hxAB, y, rfl⟩
    exact ⟨⟨hpR, x, hxAB.1, y, rfl⟩, x, hxAB.2, y, rfl⟩


-- @@ L502-503 verbatim
@[simp] lemma restrict_restrict_of_subset {R A B : V} (h : B ⊆ A) : (R ↾ A) ↾ B = R ↾ B := by
  simpa [inter_eq_right_of_subset h] using restrict_restrict_eq_restrict_inter R A B


-- @@ L505-522 expanded
/-- Restricting an inserted relation to a set that does not contain the inserted first coordinate
recovers the original restriction.
-/
lemma restrict_insert_kpair_eq_restrict_of_not_mem {f x y A : V} (hxA : x ∉ A) :
    (insert (kpair x y) f) ↾ A = f ↾ A := by
  ext p
  constructor
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hp', a, haA, b, rfl⟩
    rcases show kpair a b = kpair x y ∨ kpair a b ∈ f by simpa using hp' with (hxy | hf)
    · rcases kpair_inj hxy with ⟨rfl, rfl⟩
      exact (hxA haA).elim
    · exact mem_restrict_iff.mpr ⟨hf, a, haA, b, rfl⟩
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hf, a, haA, b, rfl⟩
    exact mem_restrict_iff.mpr ⟨by simp [hf], a, haA, b, rfl⟩


-- @@ L524-525 verbatim
/-- Image of a set under a relation -/
noncomputable def image (R A : V) : V := range (restrict R A)


-- @@ L527-528 verbatim
/-- Image of a set under a relation -/
scoped notation R:arg " “ " A:arg => image R A


-- @@ L530-530 expanded
def image.dfn : SetTheorySemisentence 3 :=
  UnivQuantifier.all
    (binop% HArrow.hArrow (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1])
      (UnivQuantifier.all
        (binop% HArrow.hArrow
          ((range.dfn).nestFormulaeFunc
            (vecCons
              ((restrict.dfn).nestFormulaeFunc
                (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #3])
                  (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #4]) ![])))
              ![]))
          (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0]))))


-- @@ L532-533 expanded
instance image.defined : DefinedFunction₂ (L := set) (M := V) image image.dfn :=
  ⟨fun v ↦ by simp [dfn, image]⟩


-- @@ L535-535 expanded
instance image.definable : DefinableFunction₂ (M := V) set image :=
  image.defined.to_definable


-- @@ L537-537 verbatim
/-! ### Cardinality comparison -/


-- @@ L539-539 verbatim
def CardLE (X Y : V) : Prop := ∃ f ∈ Y ^ X, Injective f


-- @@ L541-541 verbatim
infix:50 " ≤# " => CardLE


-- @@ L543-544 expanded
lemma cardLE_of_subset {X Y : V} (h : X ⊆ Y) : CardLE X Y :=
  ⟨identity X, mem_function_of_mem_function_of_subset (identity_mem_function X) h, by simp⟩


-- @@ L546-546 expanded
@[simp]
lemma cardLE_empty (X : V) : CardLE ∅ X :=
  cardLE_of_subset (by simp)


-- @@ L548-548 expanded
@[simp, refl]
lemma CardLE.refl (X : V) : CardLE X X :=
  cardLE_of_subset (by simp)


-- @@ L550-553 expanded
@[trans]
lemma CardLE.trans {X Y Z : V} : CardLE X Y → CardLE Y Z → CardLE X Z :=
  by
  rintro ⟨f, hf, f_inj⟩
  rintro ⟨g, hg, g_inj⟩
  refine ⟨compose f g, compose_function hf hg, compose_injective f_inj g_inj⟩


-- @@ L555-555 expanded
def CardLT (X Y : V) : Prop :=
  CardLE X Y ∧ ¬CardLE Y X


-- @@ L557-557 verbatim
infix:50 " <# " => CardLT


-- @@ L559-559 expanded
def CardLE.dfn : SetTheorySemisentence 2 :=
  UnivQuantifier.all
    (binop% HArrow.hArrow
      ((function.dfn).nestFormulaeFunc
        (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #2])
          (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![])))
      (Semiformula.bexsMem (#0)
        ((Injective.dfn).nestFormulae
          (vecCons (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]) ![]))))


-- @@ L561-561 expanded
instance CardLE.defined : DefinedRel (L := set) (M := V) CardLE dfn :=
  ⟨fun v ↦ by simp [CardLE, dfn]⟩


-- @@ L563-563 expanded
instance CardLE.definable : DefinableRel (M := V) set CardLE :=
  defined.to_definable


-- @@ L565-565 expanded
def CardLT.dfn : SetTheorySemisentence 2 :=
  @HWedge.hWedge _ _ _ Wedge.instHWedge
    (FFL.FirstOrder.Rewriting.subst CardLE.dfn (vecCons (#0) (vecCons #1 ![])))
    (@HTilde.hTilde _ _ Tilde.instHTilde
      (FFL.FirstOrder.Rewriting.subst CardLE.dfn (vecCons (#1) (vecCons #0 ![]))))


-- @@ L567-567 expanded
instance CardLT.defined : DefinedRel (L := set) (M := V) CardLT dfn :=
  ⟨fun v ↦ by simp [CardLT, dfn]⟩


-- @@ L569-569 expanded
instance CardLT.definable : DefinableRel (M := V) set CardLT :=
  defined.to_definable


-- @@ L571-571 expanded
def CardEQ (X Y : V) : Prop :=
  CardLE X Y ∧ CardLE Y X


-- @@ L573-573 verbatim
infix:60 " ≋ " => CardEQ


-- @@ L575-575 expanded
def CardEQ.dfn : SetTheorySemisentence 2 :=
  @HWedge.hWedge _ _ _ Wedge.instHWedge
    (FFL.FirstOrder.Rewriting.subst CardLE.dfn (vecCons (#0) (vecCons #1 ![])))
    (FFL.FirstOrder.Rewriting.subst CardLE.dfn (vecCons (#1) (vecCons #0 ![])))


-- @@ L577-577 expanded
instance CardEQ.defined : DefinedRel (L := set) (M := V) CardEQ dfn :=
  ⟨fun v ↦ by simp [CardEQ, dfn]⟩


-- @@ L579-579 expanded
instance CardEQ.definable : DefinableRel (M := V) set CardEQ :=
  defined.to_definable


-- @@ L581-581 expanded
lemma CardEQ.le {X Y : V} (h : CardEQ X Y) : CardLE X Y :=
  h.1


-- @@ L583-583 expanded
lemma CardEQ.ge {X Y : V} (h : CardEQ X Y) : CardLE Y X :=
  h.2


-- @@ L585-585 expanded
@[simp, refl]
lemma CardEQ.refl (X : V) : CardEQ X X :=
  ⟨by rfl, by rfl⟩


-- @@ L587-587 expanded
@[symm]
lemma CardEQ.symm {X Y : V} : CardEQ X Y → CardEQ Y X := fun e ↦ ⟨e.2, e.1⟩


-- @@ L589-590 expanded
@[trans]
lemma CardEQ.trans {X Y Z : V} : CardEQ X Y → CardEQ Y Z → CardEQ X Z := fun eXY eYZ ↦
  ⟨eXY.le.trans eYZ.le, eYZ.ge.trans eXY.ge⟩


-- @@ L592-625 expanded
lemma cardLT_power (X : V) : CardLT X (power X) :=
  by
  have : CardLE X (power X) :=
    by
    let F : V := {p ∈ X ×ˢ power X ; ∃ x ∈ X, p = kpair x { x }}
    have : F ∈ power X ^ X := by
      apply mem_function.intro
      · simp [F]
      · intro x hx
        apply ExistsUnique.intro { x } (by simp [F, hx])
        intro y hy
        have : y ⊆ X ∧ y = { x } := by simpa [hx, F] using hy
        simp [this]
    have : Injective F := by
      intro x₁ x₂ s h₁ h₂
      rcases show (x₁ ∈ X ∧ s ⊆ X) ∧ x₁ ∈ X ∧ s = { x₁ } by simpa [F] using h₁ with ⟨_, _, rfl⟩
      have : (x₂ ∈ X ∧ x₁ ∈ X) ∧ x₁ ∈ X ∧ x₂ = x₁ := by simpa [F] using h₂
      simp [this.2.2]
    refine ⟨F, by assumption, by assumption⟩
  have : ¬CardLE (power X) X := by
    rintro ⟨F, hF, injF⟩
    have : IsFunction F := IsFunction.of_mem hF
    let D : V := {x ∈ X ; ∃ s ∈ power X, kpair s x ∈ F ∧ x ∉ s}
    have : ∃ d ∈ X, kpair D d ∈ F := exists_of_mem_function hF D (by simp [D])
    rcases this with ⟨d, hd, Hd⟩
    have : d ∈ D ↔ d ∉ D :=
      calc
        d ∈ D ↔ ∃ s ⊆ X, kpair s d ∈ F ∧ d ∉ s := by simp [hd, D]
        _ ↔ d ∉ D := ?_
    · grind
    constructor
    · rintro ⟨S, hS, hSF, hdS⟩
      rcases show D = S from injF _ _ _ Hd hSF
      assumption
    · intro h
      refine ⟨D, by simpa [hd] using mem_of_mem_functions hF Hd, Hd, h⟩
  refine ⟨by assumption, by assumption⟩


-- @@ L627-700 expanded
lemma two_pow_cardEQ_power (X : V) : CardEQ (2 ^ X) (power X) :=
  by
  constructor
  · let F : V := {p ∈ (2 ^ X) ×ˢ power X ; ∃ f s, p = kpair f s ∧ ∀ x, x ∈ s ↔ kpair x 1 ∈ f}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro f hf
        let s : V := {x ∈ X ; kpair x 1 ∈ f}
        have ss_s : s ⊆ X := by simp [s]
        have mem_s : ∀ x, x ∈ s ↔ kpair x 1 ∈ f :=
          by
          simp only [mem_sep_iff, and_iff_right_iff_imp, s]
          intro x hx
          exact mem_of_mem_functions hf hx |>.1
        apply ExistsUnique.intro s ?_ ?_
        · simp [F, hf, ss_s, mem_s]
        · intro t ht
          ext x
          have ht : (f ∈ ((2 : V) ^ X) ∧ t ⊆ X) ∧ ∀ x, x ∈ t ↔ kpair x 1 ∈ f := by
            simpa [F] using ht
          simp [ht, mem_s]
    · intro f₁ f₂ s h₁ h₂
      have : (f₁ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ kpair x 1 ∈ f₁ := by simpa [F] using h₁
      rcases this with ⟨⟨f₁func, hs⟩, H₁⟩
      have : (f₂ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ kpair x 1 ∈ f₂ := by simpa [F] using h₂
      rcases this with ⟨⟨f₂func, _⟩, H₂⟩
      apply function_ext f₁func f₂func
      intro x hx i hi
      rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
      · contrapose
        suffices kpair x 1 ∈ f₂ → kpair x 1 ∈ f₁ by grind
        grind
      · grind
  · let F : V := {p ∈ power X ×ˢ (2 ^ X) ; ∃ f s, p = kpair s f ∧ ∀ x, kpair x 1 ∈ f ↔ x ∈ s}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro s hs
        have hs : s ⊆ X := by simpa using hs
        let f : V := {p ∈ X ×ˢ 2 ; ∃ x, (x ∈ s → p = kpair x 1) ∧ (x ∉ s → p = kpair x 0)}
        have kp1_mem_f : ∀ x, kpair x 1 ∈ f ↔ x ∈ s :=
          by
          intro x
          have : x ∈ s → x ∈ X := fun hx ↦ hs _ hx
          simp only [mem_sep_iff, kpair_mem_iff, mem_two_iff, one_ne_zero, or_true, and_true,
            kpair_iff, and_false, imp_false, not_not, f];
          grind
        have f_func : f ∈ (2 ^ X : V) :=
          by
          apply mem_function.intro (by simp [f])
          intro x hx
          by_cases hxS : x ∈ s
          · apply ExistsUnique.intro 1
            ·
              simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, one_ne_zero, or_true,
                and_self, kpair_iff, and_true, and_false, imp_false, not_not, true_and, f];
              grind
            · intro i hi
              simp [f, hx] at hi
              grind only
          · apply ExistsUnique.intro 0
            ·
              simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, zero_ne_one, or_false,
                and_self, kpair_iff, and_false, imp_false, and_true, true_and, f];
              grind
            · intro i hi
              simp [f, hx] at hi
              grind only
        apply ExistsUnique.intro f ?_ ?_
        · simp [F, hs, kp1_mem_f, f_func]
        · intro g hg
          have : (s ⊆ X ∧ g ∈ (2 ^ X : V)) ∧ ∀ x, kpair x 1 ∈ g ↔ x ∈ s := by simpa [F] using hg
          rcases this with ⟨⟨_, g_func⟩, Hg⟩
          apply function_ext g_func f_func
          intro x hx i hi
          rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
          · suffices kpair x 1 ∈ f → kpair x 1 ∈ g by grind
            grind
          · grind
    · intro s₁ s₂ f h₁ h₂
      have : (s₁ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, kpair x 1 ∈ f ↔ x ∈ s₁ := by simpa [F] using h₁
      have : (s₂ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, kpair x 1 ∈ f ↔ x ∈ s₂ := by simpa [F] using h₂
      ext z; grind


-- @@ L702-702 verbatim
end FFL.FirstOrder.SetTheory
