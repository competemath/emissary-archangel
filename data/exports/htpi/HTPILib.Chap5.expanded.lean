/- Copyright 2023-2025 Daniel J. Velleman -/

import HTPILib.Chap4

-- @@ L4-6 verbatim
namespace HTPI

/- Definitions -/

-- @@ L7-8 verbatim
def graph {A B : Type} (f : A → B) : Set (A × B) :=
    {(a, b) : A × B | f a = b}


-- @@ L10-11 verbatim
def is_func_graph {A B : Type} (G : Set (A × B)) : Prop :=
    ∀ (x : A), ∃! (y : B), (x, y) ∈ G


-- @@ L13-14 verbatim
def onto {A B : Type} (f : A → B) : Prop :=
  ∀ (y : B), ∃ (x : A), f x = y


-- @@ L16-17 verbatim
def one_to_one {A B : Type} (f : A → B) : Prop :=
  ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2


-- @@ L19-19 verbatim
def closed {A : Type} (f : A → A) (C : Set A) : Prop := ∀ x ∈ C, f x ∈ C


-- @@ L21-22 verbatim
def closure {A : Type} (f : A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed f D}


-- @@ L24-25 verbatim
def closed2 {A : Type} (f : A → A → A) (C : Set A) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, f x y ∈ C


-- @@ L27-28 verbatim
def closure2 {A : Type} (f : A → A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed2 f D}


-- @@ L30-31 verbatim
def closed_family {A : Type} (F : Set (A → A)) (C : Set A) : Prop :=
  ∀ f ∈ F, closed f C


-- @@ L33-34 verbatim
def closure_family {A : Type} (F : Set (A → A)) (B C : Set A) : Prop :=
  smallestElt (sub A) C {D : Set A | B ⊆ D ∧ closed_family F D}


-- @@ L36-37 verbatim
def image {A B : Type} (f : A → B) (X : Set A) : Set B :=
  {f x | x ∈ X}


-- @@ L39-42 verbatim
def inverse_image {A B : Type} (f : A → B) (Y : Set B) : Set A :=
  {a : A | f a ∈ Y}

/- Section 5.1 -/

-- @@ L43-44 verbatim
theorem graph_def {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ graph f ↔ f a = b := by rfl


-- @@ L46-49 verbatim
theorem func_from_graph_ltr {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) → is_func_graph F := sorry

--This proof is explained in Section 8.2

-- @@ L50-79 verbatim
theorem func_from_graph_rtl {A B : Type} (F : Set (A × B)) :
    is_func_graph F → (∃ (f : A → B), graph f = F) := by
  assume h1 : is_func_graph F
  define at h1    --h1 : ∀ (x : A), ∃! (y : B), (x, y) ∈ F
  have h2 : ∀ (x : A), ∃ (y : B), (x, y) ∈ F := by
    fix x : A
    obtain (y : B) (h3 : (x, y) ∈ F)
      (h4 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show ∃ (y : B), (x, y) ∈ F from Exists.intro y h3
    done
  set f : A → B := fun (x : A) => Classical.choose (h2 x)
  apply Exists.intro f
  apply Set.ext
  fix (x, y) : A × B
  have h3 : (x, f x) ∈ F := Classical.choose_spec (h2 x)
  apply Iff.intro
  · -- (→)
    assume h4 : (x, y) ∈ graph f
    define at h4        --h4 : f x = y
    rewrite [h4] at h3
    show (x, y) ∈ F from h3
    done
  · -- (←)
    assume h4 : (x, y) ∈ F
    define              --Goal : f x = y
    obtain (z : B) (h5 : (x, z) ∈ F)
      (h6 : ∀ (y1 y2 : B), (x, y1) ∈ F → (x, y2) ∈ F → y1 = y2) from h1 x
    show f x = y from h6 (f x) y h3 h4
    done
  done


-- @@ L81-83 verbatim
theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F :=
  Iff.intro (func_from_graph_ltr F) (func_from_graph_rtl F)


-- @@ L85-86 verbatim
theorem Theorem_5_1_4 {A B : Type} (f g : A → B) :
    (∀ (a : A), f a = g a) → f = g := funext


-- @@ L88-100 verbatim
example {A B : Type} (f g : A → B) :
    graph f = graph g → f = g := by
  assume h1 : graph f = graph g  --Goal : f = g
  apply funext                   --Goal : ∀ (x : A), f x = g x
  fix x : A
  have h2 : (x, f x) ∈ graph f := by
    define                       --Goal : f x = f x
    rfl
    done
  rewrite [h1] at h2             --h2 : (x, f x) ∈ graph g
  define at h2                   --h2 : g x = f x
  show f x = g x from h2.symm
  done


-- @@ L102-102 verbatim
def square1 (n : Nat) : Nat := n ^ 2


-- @@ L104-104 verbatim
def square2 : Nat → Nat := fun (n : Nat) => n ^ 2


-- @@ L106-106 verbatim
example : square1 = square2 := by rfl


-- @@ L108-108 verbatim
#eval square1 7     --Answer: 49


-- @@ L110-144 verbatim
theorem Theorem_5_1_5 {A B C : Type} (f : A → B) (g : B → C) :
    ∃ (h : A → C), graph h = comp (graph g) (graph f) := by
  set h : A → C := fun (x : A) => g (f x)
  apply Exists.intro h
  apply Set.ext
  fix (a, c) : A × C
  apply Iff.intro
  · -- Proof that (a, c) ∈ graph h → (a, c) ∈ comp (graph g) (graph f)
    assume h1 : (a, c) ∈ graph h
    define at h1  --h1 : h a = c
    define        --Goal : ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    apply Exists.intro (f a)
    apply And.intro
    · -- Proof that (a, f a) ∈ graph f
      define
      rfl
      done
    · -- Proof that (f a, c) ∈ graph g
      define
      show g (f a) = c from h1
      done
    done
  · -- Proof that (a, c) ∈ comp (graph g) (graph f) → (a, c) ∈ graph h
    assume h1 : (a, c) ∈ comp (graph g) (graph f)
    define        --Goal : h a = c
    define at h1  --h1 : ∃ (x : B), (a, x) ∈ graph f ∧ (x, c) ∈ graph g
    obtain (b : B) (h2 : (a, b) ∈ graph f ∧ (b, c) ∈ graph g) from h1
    have h3 : (a, b) ∈ graph f := h2.left
    have h4 : (b, c) ∈ graph g := h2.right
    define at h3          --h3 : f a = b
    define at h4          --h4 : g b = c
    rewrite [←h3] at h4   --h4 : g (f a) = c
    show h a = c from h4
    done
  done


-- @@ L146-147 verbatim
example {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by rfl


-- @@ L149-149 verbatim
example {A B : Type} (f : A → B) : f ∘ id = f := by rfl


-- @@ L151-153 verbatim
example {A B : Type} (f : A → B) : id ∘ f = f := by rfl

/- Section 5.2 -/

-- @@ L154-171 verbatim
theorem Theorem_5_2_5_1 {A B C : Type} (f : A → B) (g : B → C) :
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  assume h1 : one_to_one f
  assume h2 : one_to_one g
  define at h1  --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  define at h2  --h2 : ∀ (x1 x2 : B), g x1 = g x2 → x1 = x2
  define        --Goal : ∀ (x1 x2 : A), (g ∘ f) x1 = (g ∘ f) x2 → x1 = x2
  fix a1 : A
  fix a2 : A    --Goal : (g ∘ f) a1 = (g ∘ f) a2 → a1 = a2
  define : (g ∘ f) a1; define : (g ∘ f) a2
                --Goal : g (f a1) = g (f a2) → a1 = a2
  assume h3 : g (f a1) = g (f a2)
  have h4 : f a1 = f a2 := h2 (f a1) (f a2) h3
  show a1 = a2 from h1 a1 a2 h4
  done

lemma comp_def {A B C : Type} (g : B → C) (f : A → B) (x : A) :
    (g ∘ f) x = g (f x) := by rfl


-- @@ L173-189 verbatim
theorem Theorem_5_2_5_2 {A B C : Type} (f : A → B) (g : B → C) :
    onto f → onto g → onto (g ∘ f) := by
  assume h1 : onto f
  assume h2 : onto g
  define at h1           --h1 : ∀ (y : B), ∃ (x : A), f x = y
  define at h2           --h2 : ∀ (y : C), ∃ (x : B), g x = y
  define                 --Goal : ∀ (y : C), ∃ (x : A), (g ∘ f) x = y
  fix c : C
  obtain (b : B) (h3 : g b = c) from h2 c
  obtain (a : A) (h4 : f a = b) from h1 b
  apply Exists.intro a   --Goal : (g ∘ f) a = c
  rewrite [comp_def]     --Goal : g (f a) = c
  rewrite [←h4] at h3
  show g (f a) = c from h3
  done

/- Section 5.3 -/

-- @@ L190-214 verbatim
theorem Theorem_5_3_1 {A B : Type}
    (f : A → B) (h1 : one_to_one f) (h2 : onto f) :
    ∃ (g : B → A), graph g = inv (graph f) := by
  rewrite [func_from_graph]   --Goal : is_func_graph (inv (graph f))
  define        --Goal : ∀ (x : B), ∃! (y : A), (x, y) ∈ inv (graph f)
  fix b : B
  exists_unique
  · -- Existence
    define at h2          --h2 : ∀ (y : B), ∃ (x : A), f x = y
    obtain (a : A) (h4 : f a = b) from h2 b
    apply Exists.intro a  --Goal : (b, a) ∈ inv (graph f)
    define                --Goal : f a = b
    show f a = b from h4
    done
  · -- Uniqueness
    fix a1 : A; fix a2 : A
    assume h3 : (b, a1) ∈ inv (graph f)
    assume h4 : (b, a2) ∈ inv (graph f) --Goal : a1 = a2
    define at h3          --h3 : f a1 = b
    define at h4          --h4 : f a2 = b
    rewrite [←h4] at h3   --h3 : f a1 = f a2
    define at h1          --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    show a1 = a2 from h1 a1 a2 h3
    done
  done


-- @@ L216-227 verbatim
theorem Theorem_5_3_2_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : g ∘ f = id := by
  apply funext           --Goal : ∀ (x : A), (g ∘ f) x = id x
  fix a : A              --Goal : (g ∘ f) a = id a
  have h2 : (f a, a) ∈ graph g := by
    rewrite [h1]         --Goal : (f a, a) ∈ inv (graph f)
    define               --Goal : f a = f a
    rfl
    done
  define at h2           --h2 : g (f a) = a
  show (g ∘ f) a = id a from h2
  done


-- @@ L229-230 verbatim
theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := sorry


-- @@ L232-246 verbatim
theorem Theorem_5_3_3_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) : one_to_one f := by
  define              --Goal : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
  fix a1 : A; fix a2 : A
  assume h2 : f a1 = f a2
  show a1 = a2 from
    calc a1
      _ = id a1 := by rfl
      _ = (g ∘ f) a1 := by rw [h1]
      _ = g (f a1) := by rfl
      _ = g (f a2) := by rw [h2]
      _ = (g ∘ f) a2 := by rfl
      _ = id a2 := by rw [h1]
      _ = a2 := by rfl
  done


-- @@ L248-249 verbatim
theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := sorry


-- @@ L251-269 verbatim
theorem Theorem_5_3_5 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) (h2 : f ∘ g = id) : graph g = inv (graph f) := by
  have h3 : one_to_one f := Theorem_5_3_3_1 f g h1
  have h4 : onto f := Theorem_5_3_3_2 f g h2
  obtain (g' : B → A) (h5 : graph g' = inv (graph f))
    from Theorem_5_3_1 f h3 h4
  have h6 : g' ∘ f = id := Theorem_5_3_2_1 f g' h5
  have h7 : g = g' :=
    calc g
      _ = id ∘ g := by rfl
      _ = (g' ∘ f) ∘ g := by rw [h6]
      _ = g' ∘ (f ∘ g) := by rfl
      _ = g' ∘ id := by rw [h2]
      _ = g' := by rfl
  rewrite [←h7] at h5
  show graph g = inv (graph f) from h5
  done

/- Section 5.4 -/

-- @@ L270-313 verbatim
theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  set F : Set (Set A) := {D : Set A | B ⊆ D ∧ closed f D}
  set C : Set A := ⋂₀ F
  apply Exists.intro C    --Goal : closure f B C
  define                  --Goal : C ∈ F ∧ ∀ x ∈ F, C ⊆ x
  apply And.intro
  · -- Proof that C ∈ F
    define                  --Goal : B ⊆ C ∧ closed f C
    apply And.intro
    · -- Proof that B ⊆ C
      fix a : A
      assume h1 : a ∈ B       --Goal : a ∈ C
      define                  --Goal : ∀ t ∈ F, a ∈ t
      fix D : Set A
      assume h2 : D ∈ F
      define at h2            --h2 : B ⊆ D ∧ closed f D
      show a ∈ D from h2.left h1
      done
    · -- Proof that C is closed under f
      define                  --Goal : ∀ x ∈ C, f x ∈ C
      fix a : A
      assume h1 : a ∈ C       --Goal : f a ∈ C
      define                  --Goal : ∀ t ∈ F, f a ∈ t
      fix D : Set A
      assume h2 : D ∈ F       --Goal : f a ∈ D
      define at h1            --h1 : ∀ t ∈ F, a ∈ t
      have h3 : a ∈ D := h1 D h2
      define at h2            --h2 : B ⊆ D ∧ closed f D
      have h4 : closed f D := h2.right
      define at h4            --h4 : ∀ x ∈ D, f x ∈ D
      show f a ∈ D from h4 a h3
      done
    done
  · -- Proof that C is smallest
    fix D : Set A
    assume h1 : D ∈ F      --Goal : sub A C D
    define
    fix a : A
    assume h2 : a ∈ C       --Goal : a ∈ D
    define at h2            --h2 : ∀ t ∈ F, a ∈ t
    show a ∈ D from h2 D h1
    done
  done


-- @@ L315-315 verbatim
def plus (m n : Int) : Int := m + n


-- @@ L317-317 verbatim
def plus' : Int → Int → Int := fun (m n : Int) => m + n


-- @@ L319-319 verbatim
def plus'' : Int → Int → Int := fun (m : Int) => (fun (n : Int) => m + n)


-- @@ L321-321 verbatim
example : plus = plus'' := by rfl


-- @@ L323-323 verbatim
example : plus' = plus'' := by rfl


-- @@ L325-325 verbatim
#eval plus 3 2     --Answer: 5


-- @@ L327-330 verbatim
theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := sorry

/- Section 5.5 -/

-- @@ L331-332 verbatim
theorem image_def {A B : Type} (f : A → B) (X : Set A) (b : B) :
    b ∈ image f X ↔ ∃ x ∈ X, f x = b := by rfl


-- @@ L334-335 verbatim
theorem inverse_image_def {A B : Type} (f : A → B) (Y : Set B) (a : A) :
    a ∈ inverse_image f Y ↔ f a ∈ Y := by rfl


-- @@ L337-354 verbatim
theorem Theorem_5_5_2_1 {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∩ X) ⊆ image f W ∩ image f X := by
  fix y : B
  assume h1 : y ∈ image f (W ∩ X)  --Goal : y ∈ image f W ∩ image f X
  define at h1                     --h1 : ∃ x ∈ W ∩ X, f x = y
  obtain (x : A) (h2 : x ∈ W ∩ X ∧ f x = y) from h1
  define : x ∈ W ∩ X at h2         --h2 : (x ∈ W ∧ x ∈ X) ∧ f x = y
  apply And.intro
  · -- Proof that y ∈ image f W
    define                         --Goal : ∃ x ∈ W, f x = y
    show ∃ (x : A), x ∈ W ∧ f x = y from
      Exists.intro x (And.intro h2.left.left h2.right)
    done
  · -- Proof that y ∈ image f X
    show y ∈ image f X from
      Exists.intro x (And.intro h2.left.right h2.right)
    done
  done


-- @@ L356-380 verbatim
theorem Theorem_5_5_2_2 {A B : Type} (f : A → B) (W X : Set A)
    (h1 : one_to_one f) : image f (W ∩ X) = image f W ∩ image f X := by
  apply Set.ext
  fix y : B      --Goal : y ∈ image f (W ∩ X) ↔ y ∈ image f W ∩ image f X
  apply Iff.intro
  · -- (→)
    assume h2 : y ∈ image f (W ∩ X)
    show y ∈ image f W ∩ image f X from Theorem_5_5_2_1 f W X h2
    done
  · -- (←)
    assume h2 : y ∈ image f W ∩ image f X  --Goal : y ∈ image f (W ∩ X)
    define at h2                  --h2 : y ∈ image f W ∧ y ∈ image f X
    rewrite [image_def, image_def] at h2
          --h2 : (∃ x ∈ W, f x = y) ∧ ∃ x ∈ X, f x = y
    obtain (x1 : A) (h3 : x1 ∈ W ∧ f x1 = y) from h2.left
    obtain (x2 : A) (h4 : x2 ∈ X ∧ f x2 = y) from h2.right
    have h5 : f x2 = y := h4.right
    rewrite [←h3.right] at h5  --h5 : f x2 = f x1
    define at h1               --h1 : ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2
    have h6 : x2 = x1 := h1 x2 x1 h5
    rewrite [h6] at h4           --h4 : x1 ∈ X ∧ f x1 = y
    show y ∈ image f (W ∩ X) from
      Exists.intro x1 (And.intro (And.intro h3.left h4.left) h3.right)
    done
  done
