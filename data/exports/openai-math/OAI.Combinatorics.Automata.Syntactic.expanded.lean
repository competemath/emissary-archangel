import OAI.Combinatorics.Automata.RankLoss


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace OneWayLiveness

-- @@ L6-6 verbatim
open scoped Classical


-- @@ L8-8 verbatim
namespace BRel

-- @@ L9-9 verbatim
variable {H : Type*}

-- @@ L10-13 verbatim
lemma singleton_context (a : BRel H) (i j : H) :
    (∃ x y, (restrictedId {i} * a * restrictedId {j}).holds x y) ↔ a.holds i j := by
  simp only [mul_restrictedId, restrictedId_mul, Set.mem_singleton_iff]
  aesop


-- @@ L15-19 verbatim
lemma context_separates (u v : List (BRel H))
    (h : ∀ x y : List (BRel H), live (x ++ u ++ y) ↔ live (x ++ v ++ y)) : u.prod = v.prod := by
  ext i j
  have hh := h [restrictedId {i}] [restrictedId {j}]
  simpa only [live, List.prod_append, List.prod_cons, List.prod_nil, mul_one, singleton_context] using hh

-- @@ L20-20 verbatim
end BRel


-- @@ L22-55 verbatim
/-- Any matching recognition of liveness induces the full relation divisor.
The recognizer predicate may in particular sandwich the fixed endmarkers
and inspect the designated test ports. -/
theorem matching_recognition_degree {H A : Type} [Fintype H] [Fintype A]
    (η : BRel H → Pairing (A ⊕ A)) (test : Pairing (A ⊕ A) → Prop)
    (hη : ∀ w : List (BRel H), test (w.map η).prod ↔ BRel.live w)
    (x y : H) (hxy : x ≠ y) : rankLoss (Fintype.card H) ≤ Fintype.card A := by
  classical
  let S : Submonoid (Pairing (A ⊕ A) × BRel H) := {
    carrier := {p | ∃ w : List (BRel H), p = ((w.map η).prod, w.prod)}
    one_mem' := ⟨[], by simp only [List.map_nil, List.prod_nil]; rfl⟩
    mul_mem' := by
      rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u ++ v, by simp⟩ }
  let ρ : S →* Pairing (A ⊕ A) := (MonoidHom.fst _ _).comp S.subtype
  let φ : S →* BRel H := (MonoidHom.snd _ _).comp S.subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    have hd : (u.map η).prod = (v.map η).prod := by
      change a.val.1 = b.val.1 at hab
      simpa only [hu, hv] using hab
    have hr : u.prod = v.prod := by
      apply BRel.context_separates
      intro l r
      rw [← hη, ← hη]
      simp only [List.map_append, List.prod_append, hd]
    apply Subtype.ext
    rw [hu, hv, hd, hr]
  have hφ : Function.Surjective φ := by
    intro R
    exact ⟨⟨(η R, R), [R], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]⟩, rfl⟩
  exact relation_divisor_degree ρ hρ φ hφ x y hxy


-- @@ L57-57 verbatim
end OneWayLiveness


-- @@ L59-59 verbatim
end OAI
