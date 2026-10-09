import OAI.CategoryTheory.Globular.Colimits


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck


-- @@ L9-9 verbatim
open CategoryTheory CategoryTheory.Limits Opposite


-- @@ L11-11 verbatim
namespace Globe


-- @@ L13-14 verbatim
def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : Globe.mk m ⟶ Globe.mk n :=
  if e : m = n then e ▸ Face.id m else Face.face (lt_of_le_of_ne h e) side


-- @@ L16-18 verbatim
@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (Globe.mk n) := by
  simp only [faceLE, dite_true]
  rfl


-- @@ L20-22 verbatim
@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE h.le side = face h side := by
  simp [faceLE, h.ne, face]


-- @@ L24-24 verbatim
end Globe


-- @@ L26-26 verbatim
namespace GlobularPresheaf


-- @@ L28-29 verbatim
noncomputable def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : disk.{u} m ⟶ disk.{u} n :=
  uliftYoneda.{u}.map (Globe.faceLE h side)


-- @@ L31-33 verbatim
@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (disk.{u} n) := by
  change uliftYoneda.map (Globe.faceLE (le_refl n) side) = 𝟙 _
  rw [Globe.faceLE_refl, uliftYoneda.map_id]


-- @@ L35-38 verbatim
@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE.{u} h.le side = face h side := by
  unfold faceLE face
  rw [Globe.faceLE_of_lt]


-- @@ L40-61 verbatim
theorem face_low_bijective {m n k : ℕ} (h : m < n) (hk : k < m) (side : Bool) :
    Function.Bijective ((face.{u} h side).app (op (Globe.mk k))) := by
  constructor
  · rintro ⟨a⟩ ⟨b⟩ he
    cases a with
    | id => omega
    | face ha ba =>
      cases b with
      | id => omega
      | face hb bb =>
        have : ba = bb := by
          change ULift.up (Globe.Face.face (ha.trans h) ba) =
            ULift.up (Globe.Face.face (hb.trans h) bb) at he
          cases he
          rfl
        subst bb
        rfl
  · rintro ⟨a⟩
    cases a with
    | id => omega
    | face ha ba =>
      exact ⟨⟨Globe.Face.face hk ba⟩, rfl⟩


-- @@ L63-69 verbatim
theorem face_low_equal {m n k : ℕ} (h : m < n) (hk : k < m) (b c : Bool) :
    (face.{u} h b).app (op (Globe.mk k)) = (face h c).app (op (Globe.mk k)) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba => rfl


-- @@ L71-77 verbatim
theorem faceLE_low_bijective {m n k : ℕ} (h : m ≤ n) (hk : k < m) (side : Bool) :
    Function.Bijective ((faceLE.{u} h side).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with h | rfl
  · rw [faceLE_of_lt h]
    exact face_low_bijective h hk side
  · rw [faceLE_refl]
    exact Function.bijective_id



-- @@ L80-87 verbatim
theorem face_comp_faceLE {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) (s t : Bool) :
    face.{u} hab s ≫ faceLE hbc t = face (hab.trans_le hbc) s := by
  rcases lt_or_eq_of_le hbc with hbc | rfl
  · rw [faceLE_of_lt hbc]
    change uliftYoneda.map (Globe.face hab s) ≫ uliftYoneda.map (Globe.face hbc t) = _
    rw [← uliftYoneda.map_comp]
    rfl
  · rw [faceLE_refl, Category.comp_id]


-- @@ L89-106 verbatim
theorem globeMap_low_equal {m n k : ℕ} (f g : Globe.mk m ⟶ Globe.mk n) (hk : k < m) :
    (uliftYoneda.{u}.map f).app (op (Globe.mk k)) =
      (uliftYoneda.{u}.map g).app (op (Globe.mk k)) := by
  change Globe.Face m n at f g
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba =>
    cases f with
    | id =>
      cases g with
      | id => rfl
      | face hg bg => omega
    | face hf bf =>
      cases g with
      | id => omega
      | face hg bg => rfl


-- @@ L108-111 verbatim
theorem disk_hom_ext {n : ℕ} {X : GlobularPresheaf.{u}} {f g : disk n ⟶ X}
    (h : f.app (op (Globe.mk n)) = g.app (op (Globe.mk n))) : f = g := by
  apply uliftYonedaEquiv.injective
  exact ConcreteCategory.congr_hom h _


-- @@ L113-137 verbatim
theorem pushout_comparison_isIso {D : Type u} [Category.{v} D]
    {A B E P A' B' E' P' : D}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    {f' : A' ⟶ B'} {g' : A' ⟶ E'} {i' : B' ⟶ P'} {j' : E' ⟶ P'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E') (p : P ⟶ P')
    [IsIso a] [IsIso b] [IsIso e]
    (hf : f ≫ b = a ≫ f') (hg : g ≫ e = a ≫ g')
    (hi : i ≫ p = b ≫ i') (hj : j ≫ p = e ≫ j') : IsIso p := by
  let r : P' ⟶ P := h'.desc (inv b ≫ i) (inv e ≫ j) (by
    apply (cancel_epi a).1
    simp only [← Category.assoc, ← hf, ← hg]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact h.w)
  refine ⟨r, ?_, ?_⟩
  · apply h.hom_ext
    · rw [← Category.assoc, hi, Category.assoc]
      simp only [r, IsPushout.inl_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
    · rw [← Category.assoc, hj, Category.assoc]
      simp only [r, IsPushout.inr_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
  · apply h'.hom_ext
    · simp only [r, IsPushout.inl_desc_assoc, hi, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]
    · simp only [r, IsPushout.inr_desc_assoc, hj, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]



-- @@ L140-148 verbatim
theorem faceLE_cap_bijective {q d n k : ℕ} (hd : d = min n (q+1))
    (h : d ≤ n) (hk : k ≤ q) :
    Function.Bijective ((faceLE.{u} h false).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · apply faceLE_low_bijective
    have : d = q+1 := by omega
    omega
  · rw [faceLE_refl]
    exact Function.bijective_id


-- @@ L150-155 verbatim
theorem face_comp_eq_of_app_eq {m n : ℕ} {X : GlobularPresheaf.{u}}
    (h : m < n) (s : Bool) (a b : disk n ⟶ X)
    (hab : a.app (op (Globe.mk m)) = b.app (op (Globe.mk m))) :
    face h s ≫ a = face h s ≫ b := by
  apply disk_hom_ext
  exact congrArg (fun t => (face h s).app (op (Globe.mk m)) ≫ t) hab


-- @@ L157-157 verbatim
end GlobularPresheaf


-- @@ L159-159 verbatim
namespace Shape


-- @@ L161-162 verbatim
noncomputable def last (S : Shape) : GlobularPresheaf.disk S.1 ⟶ S.realize :=
  S.2.lastInclusion


-- @@ L164-164 verbatim
end Shape


-- @@ L166-166 verbatim
end Grothendieck


-- @@ L168-168 verbatim
end OAI
