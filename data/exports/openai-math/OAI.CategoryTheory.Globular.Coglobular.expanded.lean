import OAI.CategoryTheory.Globular.Whisker


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits Opposite


-- @@ L10-15 verbatim
structure CoGlobularObject (K : Type u) [Category.{v} K] where
  obj : ℕ → K
  source : ∀ n, obj n ⟶ obj (n+1)
  target : ∀ n, obj n ⟶ obj (n+1)
  source_source : ∀ n, source n ≫ source (n+1) = source n ≫ target (n+1)
  target_source : ∀ n, target n ≫ source (n+1) = target n ≫ target (n+1)


-- @@ L17-17 verbatim
namespace CoGlobularObject

-- @@ L18-18 verbatim
variable {K : Type u} [Category.{v} K]


-- @@ L20-21 verbatim
def adjacent (B : CoGlobularObject K) (n : ℕ) (ε : Bool) : B.obj n ⟶ B.obj (n+1) :=
  if ε then B.target n else B.source n


-- @@ L23-27 verbatim
theorem adjacent_pair (B : CoGlobularObject K) (n : ℕ) (ε δ : Bool) :
    B.adjacent n ε ≫ B.adjacent (n+1) δ = B.adjacent n ε ≫ B.source (n+1) := by
  cases ε <;> cases δ <;> simp only [adjacent, Bool.false_eq_true, ↓reduceIte]
  · exact (B.source_source n).symm
  · exact (B.target_source n).symm


-- @@ L29-33 verbatim
def face (B : CoGlobularObject K) {m k : ℕ} (h : m < k) (ε : Bool) : B.obj m ⟶ B.obj k :=
  match k with
  | 0 => False.elim (by omega)
  | k+1 => if e : m = k then eqToHom (congrArg B.obj e) ≫ B.adjacent k ε
    else B.face (by omega : m < k) ε ≫ B.source k


-- @@ L35-38 verbatim
@[simp] theorem face_succ (B : CoGlobularObject K) (n : ℕ) (ε : Bool) :
    B.face (Nat.lt_succ_self n) ε = B.adjacent n ε := by
  rw [face, dite_eq_left rfl]
  simp


-- @@ L40-55 verbatim
theorem face_adjacent (B : CoGlobularObject K) {m k : ℕ} (h : m < k) (ε δ : Bool) :
    B.face h ε ≫ B.adjacent k δ = B.face (by omega : m < k+1) ε := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases e : m = k
    · subst m
      rw [face_succ, B.adjacent_pair]
      rw [face, dite_eq_right (by omega)]
      rw [face_succ]
    · have hm : m < k := by omega
      rw [face, dite_eq_right e, Category.assoc]
      change (B.face hm ε ≫ B.adjacent k false ≫ B.adjacent (k+1) δ) = _
      rw [B.adjacent_pair, ← Category.assoc]
      rw [face, dite_eq_right (by omega), face, dite_eq_right e]
      rfl


-- @@ L57-68 verbatim
theorem face_comp (B : CoGlobularObject K) {m k l : ℕ} (h : m < k) (h' : k < l)
    (ε δ : Bool) : B.face h ε ≫ B.face h' δ = B.face (h.trans h') ε := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases e : k = l
    · subst k
      rw [face_succ]
      exact B.face_adjacent h ε δ
    · have hkl : k < l := by omega
      rw [face, dite_eq_right e, ← Category.assoc, ih hkl]
      exact B.face_adjacent (h.trans hkl) ε false


-- @@ L70-73 verbatim
def eval (B : CoGlobularObject K) {m n : ℕ} (f : Globe.Face m n) : B.obj m ⟶ B.obj n :=
  match f with
  | .id _ => 𝟙 _
  | .face h ε => B.face h ε


-- @@ L75-90 verbatim
def functor (B : CoGlobularObject K) : Globe ⥤ K where
  obj k := B.obj k.dim
  map f := B.eval f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    rcases X with ⟨x⟩
    rcases Y with ⟨y⟩
    rcases Z with ⟨z⟩
    change Globe.Face x y at f
    change Globe.Face y z at g
    cases f with
    | id => exact (Category.id_comp _).symm
    | face h ε =>
      cases g with
      | id => exact (Category.comp_id _).symm
      | face h' δ => exact (B.face_comp h h' ε δ).symm


-- @@ L92-95 verbatim
noncomputable def realization (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K] :
    GlobularPresheaf.{max v w} ⥤ K := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact uliftYoneda.{max v w}.leftKanExtension B.functor


-- @@ L97-100 verbatim
noncomputable def globeIso (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (k : ℕ) : B.realization.obj (GlobularPresheaf.disk.{max v w} k) ≅ B.obj k := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.isExtensionAlongULiftYoneda B.functor).app (Globe.mk k)


-- @@ L102-106 verbatim
instance preservesColimits_realization (B : CoGlobularObject K)
    [HasColimitsOfSize.{0,max v w} K] : PreservesColimits B.realization := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  unfold realization
  infer_instance


-- @@ L108-113 verbatim
@[reassoc] theorem globeIso_naturality (B : CoGlobularObject K)
    [HasColimitsOfSize.{0,max v w} K] {j k : ℕ} (f : Globe.Face j k) :
    B.realization.map (uliftYoneda.map f) ≫ (B.globeIso k).hom =
      (B.globeIso j).hom ≫ B.eval f := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.isExtensionAlongULiftYoneda B.functor).hom.naturality f


-- @@ L115-119 verbatim
noncomputable def homEquiv (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (Y : K) :
    (B.realization.obj S ⟶ Y) ≃ (S ⟶ (Presheaf.restrictedULiftYoneda.{w} B.functor).obj Y) := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit B.functor)).homEquiv S Y


-- @@ L121-124 verbatim
noncomputable def cell (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (k : ℕ) (x : S.obj (op (Globe.mk k))) :
    B.obj k ⟶ B.realization.obj S :=
  (B.globeIso k).inv ≫ B.realization.map (uliftYonedaEquiv.symm x)


-- @@ L126-135 verbatim
@[simp] theorem homEquiv_app (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (Y : K) (f : B.realization.obj S ⟶ Y)
    (k : ℕ) (x : S.obj (op (Globe.mk k))) :
    ((B.homEquiv S Y) f).app (op (Globe.mk k)) x = ULift.up (B.cell S k x ≫ f) := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  change ((uliftYoneda.{max v w}).leftKanExtension B.functor).obj S ⟶ Y at f
  change ((Presheaf.uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit B.functor)).homEquiv S Y f).app _ x = _
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  congr 1
  exact (Category.assoc _ _ _).symm


-- @@ L137-147 verbatim
theorem hom_ext (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    {S : GlobularPresheaf.{max v w}} {Y : K} {f g : B.realization.obj S ⟶ Y}
    (h : ∀ k x, B.cell S k x ≫ f = B.cell S k x ≫ g) : f = g := by
  apply (B.homEquiv S Y).injective
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  rcases k with ⟨⟨k⟩⟩
  simp only [homEquiv_app]
  exact congrArg ULift.up (h k x)


-- @@ L149-149 verbatim
end CoGlobularObject


-- @@ L151-158 verbatim
structure FiniteCoGlobularObject (K : Type u) [Category.{v} K] (q : ℕ) where
  obj : ∀ k, k ≤ q → K
  source : ∀ k (hk : k+1 ≤ q), obj k (by omega) ⟶ obj (k+1) hk
  target : ∀ k (hk : k+1 ≤ q), obj k (by omega) ⟶ obj (k+1) hk
  source_source : ∀ k (hk : k+2 ≤ q),
    source k (by omega) ≫ source (k+1) hk = source k (by omega) ≫ target (k+1) hk
  target_source : ∀ k (hk : k+2 ≤ q),
    target k (by omega) ≫ source (k+1) hk = target k (by omega) ≫ target (k+1) hk


-- @@ L160-160 verbatim
namespace FiniteCoGlobularObject

-- @@ L161-161 verbatim
variable {K : Type u} [Category.{v} K] [HasTerminal K] {q : ℕ}


-- @@ L163-164 verbatim
noncomputable def completedObj (B : FiniteCoGlobularObject K q) (k : ℕ) : K :=
  if h : k ≤ q then B.obj k h else ⊤_ K


-- @@ L166-167 verbatim
theorem completedObj_eq (B : FiniteCoGlobularObject K q) (k : ℕ) (h : k ≤ q) :
    B.completedObj k = B.obj k h := dite_eq_left h


-- @@ L169-170 verbatim
theorem completedObj_terminal (B : FiniteCoGlobularObject K q) (k : ℕ) (h : ¬ k ≤ q) :
    B.completedObj k = ⊤_ K := dite_eq_right h


-- @@ L172-178 verbatim
noncomputable def completedArrow (B : FiniteCoGlobularObject K q) (k : ℕ) (ε : Bool) :
    B.completedObj k ⟶ B.completedObj (k+1) :=
  if h : k+1 ≤ q then
    eqToHom (B.completedObj_eq k (by omega)) ≫
      (if ε then B.target k h else B.source k h) ≫
      eqToHom (B.completedObj_eq (k+1) h).symm
  else terminal.from _ ≫ eqToHom (B.completedObj_terminal (k+1) h).symm


-- @@ L180-191 verbatim
theorem completed_identity (B : FiniteCoGlobularObject K q) (k : ℕ) (ε : Bool) :
    B.completedArrow k ε ≫ B.completedArrow (k+1) false =
      B.completedArrow k ε ≫ B.completedArrow (k+1) true := by
  by_cases h : k+2 ≤ q
  · simp only [completedArrow, h, show k+1 ≤ q by omega, ↓reduceDIte]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [← Category.assoc (B.source k _), B.source_source k h, Category.assoc]
    · rw [← Category.assoc (B.target k _), B.target_source k h, Category.assoc]
  · have ht : IsTerminal (B.completedObj (k+2)) := by
      simpa only [completedObj, dite_eq_right h] using (terminalIsTerminal (C := K))
    exact ht.hom_ext _ _


-- @@ L193-198 verbatim
noncomputable abbrev complete (B : FiniteCoGlobularObject K q) : CoGlobularObject K where
  obj := B.completedObj
  source k := B.completedArrow k false
  target k := B.completedArrow k true
  source_source k := B.completed_identity k false
  target_source k := B.completed_identity k true


-- @@ L200-206 verbatim
noncomputable def map {L : Type w} [Category.{v} L]
    (B : FiniteCoGlobularObject K q) (F : K ⥤ L) : FiniteCoGlobularObject L q where
  obj k hk := F.obj (B.obj k hk)
  source k hk := F.map (B.source k hk)
  target k hk := F.map (B.target k hk)
  source_source k hk := by rw [← F.map_comp, ← F.map_comp, B.source_source k hk]
  target_source k hk := by rw [← F.map_comp, ← F.map_comp, B.target_source k hk]


-- @@ L208-209 verbatim
noncomputable def lowIso (B : FiniteCoGlobularObject K q) (k : ℕ) (hk : k ≤ q) :
    B.complete.obj k ≅ B.obj k hk := eqToIso (B.completedObj_eq k hk)


-- @@ L211-213 verbatim
noncomputable def face (B : FiniteCoGlobularObject K q) {j k : ℕ}
    (h : j < k) (hk : k ≤ q) (ε : Bool) : B.obj j (by omega) ⟶ B.obj k hk :=
  (B.lowIso j (by omega)).inv ≫ B.complete.face h ε ≫ (B.lowIso k hk).hom


-- @@ L215-225 verbatim
@[simp] theorem face_succ (B : FiniteCoGlobularObject K q) (k : ℕ)
    (hk : k+1 ≤ q) (ε : Bool) :
    B.face (Nat.lt_succ_self k) hk ε = if ε then B.target k hk else B.source k hk := by
  rw [face, CoGlobularObject.face_succ]
  have e : B.complete.adjacent k ε = B.completedArrow k ε := by cases ε <;> rfl
  rw [e]
  change eqToHom (B.completedObj_eq k (by omega)).symm ≫ B.completedArrow k ε ≫
    eqToHom (B.completedObj_eq (k+1) hk) = _
  rw [completedArrow, dite_eq_left hk]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]


-- @@ L227-231 verbatim
theorem face_comp (B : FiniteCoGlobularObject K q) {i j k : ℕ}
    (h : i < j) (h' : j < k) (hk : k ≤ q) (ε δ : Bool) :
    B.face h (by omega) ε ≫ B.face h' hk δ = B.face (h.trans h') hk ε := by
  simp only [face, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (B.complete.face h ε), B.complete.face_comp]


-- @@ L233-238 verbatim
theorem face_adjacent (B : FiniteCoGlobularObject K q) {j k : ℕ}
    (h : j < k) (hk : k+1 ≤ q) (ε δ : Bool) :
    B.face h (by omega) ε ≫ (if δ then B.target k hk else B.source k hk) =
      B.face (by omega : j < k+1) hk ε := by
  rw [← B.face_succ k hk δ]
  exact B.face_comp h (Nat.lt_succ_self k) hk ε δ


-- @@ L240-241 verbatim
noncomputable def realization (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] : GlobularPresheaf.{max v w} ⥤ K := B.complete.realization


-- @@ L243-246 verbatim
noncomputable def globeIso (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (k : ℕ) (hk : k ≤ q) :
    B.realization.obj (GlobularPresheaf.disk.{max v w} k) ≅ B.obj k hk :=
  (B.complete.globeIso k) ≪≫ B.lowIso k hk


-- @@ L248-260 verbatim
@[reassoc] theorem globeIso_face (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) :
    B.realization.map (GlobularPresheaf.face h ε) ≫ (B.globeIso k hk).hom =
      (B.globeIso j (by omega)).hom ≫ B.face h hk ε := by
  change B.complete.realization.map (GlobularPresheaf.face h ε) ≫
    ((B.complete.globeIso k).hom ≫ (B.lowIso k hk).hom) =
      ((B.complete.globeIso j).hom ≫ (B.lowIso j (by omega)).hom) ≫
        (B.lowIso j (by omega)).inv ≫ B.complete.face h ε ≫ (B.lowIso k hk).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have e := B.complete.globeIso_naturality (Globe.face h ε)
  change B.complete.realization.map (GlobularPresheaf.face h ε) ≫
    (B.complete.globeIso k).hom = (B.complete.globeIso j).hom ≫ B.complete.face h ε at e
  rw [← Category.assoc, e, Category.assoc]


-- @@ L262-262 verbatim
end FiniteCoGlobularObject


-- @@ L264-264 verbatim
namespace Shape

-- @@ L265-265 verbatim
open GlobularTheory


-- @@ L267-268 verbatim
def linearBlock (n k : ℕ) : Shape :=
  if k < n then globe k else if k = n then globe (n+1) else tripleShape n


-- @@ L270-271 verbatim
theorem linearBlock_low (n k : ℕ) (h : k < n) : linearBlock n k = globe k := by
  simp only [linearBlock, ite_eq_left h]


-- @@ L273-275 verbatim
theorem linearBlock_center (n k : ℕ) (h : k = n) : linearBlock n k = globe (n+1) := by
  subst k
  simp only [linearBlock, lt_self_iff_false, ↓reduceIte]


-- @@ L277-278 verbatim
theorem linearBlock_high (n k : ℕ) (h : n < k) : linearBlock n k = tripleShape n := by
  simp only [linearBlock, ite_eq_right (by omega : ¬ k < n), ite_eq_right (by omega : ¬ k = n)]


-- @@ L280-292 verbatim
noncomputable def linearAdjacent (n k : ℕ) (hk : k ≤ n) (ε : Bool) :
    linearBlock n k ⟶ linearBlock n (k+1) :=
  if h : k < n then
    if h' : k+1 < n then
      eqToHom (linearBlock_low n k h) ≫ face (Nat.lt_succ_self k) ε ≫
        eqToHom (linearBlock_low n (k+1) h').symm
    else
      eqToHom (linearBlock_low n k h) ≫ face (by omega : k < n+1) ε ≫
        eqToHom (linearBlock_center n (k+1) (by omega)).symm
  else
    eqToHom (linearBlock_center n k (by omega)) ≫
      (if ε then tripleLast n else tripleFirst n) ≫
      eqToHom (linearBlock_high n (k+1) (by omega)).symm


-- @@ L294-298 verbatim
theorem face_comp {a b c : ℕ} (h : a < b) (h' : b < c) (ε δ : Bool) :
    face h ε ≫ face h' δ = face (h.trans h') ε := by
  change uliftYoneda.map (Globe.face h ε) ≫ uliftYoneda.map (Globe.face h' δ) = _
  rw [← uliftYoneda.map_comp]
  rfl


-- @@ L300-311 verbatim
theorem face_triple_first_last (n k : ℕ) (hk : k < n) (ε : Bool) :
    face (by omega : k < n+1) ε ≫ tripleFirst n =
      face (by omega : k < n+1) ε ≫ tripleLast n := by
  have h₀ := congrArg (fun f => face hk ε ≫ f) (triple_first_middle n)
  have h₁ := congrArg (fun f => face hk ε ≫ f) (triple_middle_last n)
  rw [← Category.assoc, ← Category.assoc] at h₀ h₁
  change (face hk ε ≫ face (Nat.lt_succ_self n) true) ≫ tripleFirst n =
    (face hk ε ≫ face (Nat.lt_succ_self n) false) ≫ tripleMiddle n at h₀
  change (face hk ε ≫ face (Nat.lt_succ_self n) true) ≫ tripleMiddle n =
    (face hk ε ≫ face (Nat.lt_succ_self n) false) ≫ tripleLast n at h₁
  rw [face_comp, face_comp] at h₀ h₁
  exact h₀.trans h₁


-- @@ L313-327 verbatim
theorem linearAdjacent_identity (n k : ℕ) (hk : k+2 ≤ n+1) (ε : Bool) :
    linearAdjacent n k (by omega) ε ≫ linearAdjacent n (k+1) (by omega) false =
      linearAdjacent n k (by omega) ε ≫ linearAdjacent n (k+1) (by omega) true := by
  have h : k < n := by omega
  by_cases h' : k+1 < n
  · by_cases h'' : k+2 < n
    · simp only [linearAdjacent, dite_eq_left h, dite_eq_left h', dite_eq_left h'']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp, ← Category.assoc (face _ ε), face_comp]
    · simp only [linearAdjacent, dite_eq_left h, dite_eq_left h', dite_eq_right h'']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp, ← Category.assoc (face _ ε), face_comp]
  · simp only [linearAdjacent, dite_eq_left h, dite_eq_right h', Bool.false_eq_true, ↓reduceIte]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (face _ ε), face_triple_first_last n k h ε, Category.assoc]


-- @@ L329-334 verbatim
noncomputable def linearDiagram (n : ℕ) : FiniteCoGlobularObject Shape (n+1) where
  obj k _ := linearBlock n k
  source k hk := linearAdjacent n k (by omega) false
  target k hk := linearAdjacent n k (by omega) true
  source_source k hk := linearAdjacent_identity n k hk false
  target_source k hk := linearAdjacent_identity n k hk true


-- @@ L336-337 verbatim
noncomputable def linearGlobularDiagram (n : ℕ) : FiniteCoGlobularObject GlobularPresheaf.{0} (n+1) :=
  (linearDiagram n).map realization


-- @@ L339-340 verbatim
noncomputable def linearization (n : ℕ) : GlobularPresheaf.{0} ⥤ GlobularPresheaf.{0} :=
  (linearGlobularDiagram n).realization


-- @@ L342-344 verbatim
noncomputable def linearGlobeIso (n k : ℕ) (hk : k ≤ n+1) :
    (linearization n).obj (GlobularPresheaf.disk k) ≅ (linearBlock n k).realize :=
  (linearGlobularDiagram n).globeIso k hk


-- @@ L346-346 verbatim
end Shape

-- @@ L347-347 verbatim
end Grothendieck


-- @@ L349-349 verbatim
end OAI
