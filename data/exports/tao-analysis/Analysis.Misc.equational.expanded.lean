import Mathlib.Tactic

/-
A informal proof of the theorem `singleton_law` is provided below, courtesy of Bruno Le Floch https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Alternative.20proofs.20of.20E1689.E2.8A.A2E2/near/517189582.  Claude Code was used to formalize this proof using the following steps:

Step 0: Formalize the `S` and `f` notation.

Step 1: First make Lean formalizations of the *statements* of Lemma 1, Lemma 2 and Lemma 3, but leave the proofs as sorries.  Restructure the existing informal proof so that the statement and proof of each lemma is moved to be near the formal statement of that lemma, expressed as a comment.  Use the `S` and `f` notation as needed to align the formal statements with the informal statements.

Step 2a: Create a high-level skeleton for the proof of Lemma 1 by expressing each step of the informal proof as an appropriate Lean statement with justifications given as a sorry (e.g., a step might become a `have` statement that is given by a sorry).  At this stage of the process, do *not* try to justify the entire proof, and accept each step of the informal proof is valid (other than fixing any minor typos or inaccuracies).  If there is a step which is confusing, replace it with an appropriate sorry and let me know what the issue is, rather than spend a lot of time trying to understand it.  Again, take advantage of the `S` and `f` notation as needed to make the formalization match the informal proof as closely as possible.

Step 2b: Assuming no major issues were encountered in Step 2a, fill in all the sorries in the proof of Lemma 1.

Step 3a: Repeat Step 2a for the proof of Lemma 2.

Step 3b: Repeat Step 2b for the proof of Lemma 2.

Step 4a: Repeat Step 2a for the proof of Lemma 3.

Step 4b: Repeat Step 2b for the proof of Lemma 3.

Step 5a: Repeat Step 2a for the final part of the proof of `singleton_law` after Lemma 3.

Step 5b: Repeat Step 2b for the final part of the proof of `singleton_law` after Lemma 3.

Some manual golfing was performed afterwards.
-/



-- @@ L30-31 verbatim
class Magma (α : Type _) where
  op : α → α → α


-- @@ L33-33 verbatim
infix:65 " ◇ " => Magma.op


-- @@ L35-35 expanded
abbrev Equation1689 (M : Type _) [Magma M] :=
  ∀ x y z : M, x = Magma.op (Magma.op y x) (Magma.op (Magma.op x z) z)


-- @@ L37-37 verbatim
abbrev Equation2 (M: Type _) [Magma M] := ∀ x y : M, x = y


-- @@ L39-42 verbatim
variable {M : Type _} [Magma M]

-- Step 0: S and f notation
-- S z x = (x ◇ z) ◇ z  (written S_z(x) in the informal proof)

-- @@ L43-45 expanded
abbrev S (z x : M) : M :=
  Magma.op (Magma.op x z) z


-- @@ L46-54 expanded
abbrev f (x y : M) : M :=
  Magma.op x (S y x)


-- @@ L55-68 expanded
lemma S_left_ideal (h : Equation1689 M) (a b z : M) : S b a = Magma.op a (S z (S b a)) :=
  by
  have step := h (Magma.op (Magma.op a b) b) (Magma.op a a) z
  grind
    /-
    **Lemma 1:** For any a, b, c, one has S_b(a) = a ◇ f(b,c),  i.e., S b a = a ◇ f b c.
    
    *Proof:* For x = S b a and y ∈ Ma we have y ◇ x = a.  Then apply the main equation to these
    values of x, y to get
      S b a = a ◇ S z (S b a).
    Then set z = S c b and note that (S b a) ◇ z = ((a ◇ b) ◇ b) ◇ ((b ◇ c) ◇ c) = b to simplify
    the right-hand side above and get, as announced,
      S b a = a ◇ ((S b a ◇ z) ◇ z) = a ◇ (b ◇ z) = a ◇ f b c.
    -/


-- @@ L69-86 expanded
lemma lemma1 (h : Equation1689 M) (a b c : M) : S b a = Magma.op a (f b c) :=
  by
  have h1 : ∀ z : M, S b a = Magma.op a (S z (S b a)) := S_left_ideal h a b
  have h2 : Magma.op (S b a) (S c b) = b := (h b (Magma.op a b) c).symm
  have h3 : S (S c b) (S b a) = f b c := by
    grind
      -- Combine: S b a = a ◇ S (S c b) (S b a) = a ◇ f b c.
      
  calc
    S b a = Magma.op a (S (S c b) (S b a)) := h1 (S c b)
    _ = Magma.op a (f b c) := by
      rw [h3]
        /-
        **Lemma 2:** For all a there exist b, c, d such that f(b,c) = S_d(a),  i.e., f b c = S d a.
        
        *Proof:* By definition of f one has f b c = b ◇ S c b.  Taking b = S x a for some x, and
        rewriting b = a ◇ S c b using the first equation in the proof of Lemma 1, we find
          f b c = (a ◇ S c b) ◇ S c b,
        which has the desired form for d = S c b.  (Thus, the statement actually holds for all a, c.)
        -/


-- @@ L87-110 expanded
lemma lemma2 (h : Equation1689 M) (a : M) : ∃ b c d : M, f b c = S d a := by
  -- Take b := S a a (= S_a(a)), c := a, d := S a (S a a) (= S c b).
    -- The proof works for all a, c; any x works for b = S x a.
  
  use S a a, a,
    S a
      (S a a)
        -- From the same argument as the first equation in the proof of Lemma 1 (with b := a, z := a):
          --   b = S a a = a ◇ S a (S a a) = a ◇ S c b.
        
  have hb : S a a = Magma.op a (S a (S a a)) := S_left_ideal h a a a
  calc
    f (S a a) a = Magma.op (S a a) (S a (S a a)) := rfl
    _ = Magma.op (Magma.op a (S a (S a a))) (S a (S a a)) := by congr
    _ = S (S a (S a a)) a := rfl


-- @@ L111-140 expanded
lemma lemma3 (h : Equation1689 M) (a : M) : ∃ e : M, S e a = a := by
  -- Get b, c, d from Lemma 2, so that f b c = S d a.
  
  obtain ⟨b, c, d, hd⟩ := lemma2 h a
  use f a d
  have h_main : a = Magma.op (Magma.op (Magma.op a a) a) (S b a) := by
    grind
      -- Lemma 1 gives S b a = a ◇ f b c, so a = ((a ◇ a) ◇ a) ◇ (a ◇ f b c).
      
  have h_step2 : a = Magma.op (Magma.op (Magma.op a a) a) (Magma.op a (f b c)) :=
    h_main.trans
      (by rw [lemma1 h a b c])
        -- Since f b c = S d a by hd, a ◇ f b c = a ◇ S d a = f a d.
        
  have h_step3 : Magma.op a (f b c) = f a d := by
    grind
      -- Lemma 1 with b←a, c←d gives S a a = a ◇ f a d, i.e., (a ◇ a) ◇ a = a ◇ f a d.
      
  have h_step4 : Magma.op (Magma.op a a) a = Magma.op a (f a d) := by simpa using lemma1 h a a d
  calc
    S (f a d) a = Magma.op (Magma.op a (f a d)) (f a d) := rfl
    _ = Magma.op (Magma.op (Magma.op a a) a) (f a d) := by rw [← h_step4]
    _ = Magma.op (Magma.op (Magma.op a a) a) (Magma.op a (f b c)) := by rw [← h_step3]
    _ = Magma.op (Magma.op (Magma.op a a) a) (S b a) := by rw [← lemma1 h a b c]
    _ = a := h_main.symm


-- @@ L141-163 expanded
theorem singleton_law (h : Equation1689 M) : Equation2 M := by
  -- Step 1: S a b = a for all a, b.
    -- Lemma 3 gives e with S e a = a; main eq (x=a, z=e) gives a = (y ◇ a) ◇ S e a = (y ◇ a) ◇ a = S a y.
  
  have hS : ∀ a b : M, S a b = a := by
    intro a b
    obtain ⟨e, he⟩ := lemma3 h a
    grind
      -- Step 2: (a ◇ b) ◇ c = b for all a, b, c.
        -- Main eq (x=b, y=a, z=c) gives b = (a ◇ b) ◇ S c b = (a ◇ b) ◇ c by hS.
      
  have hrel : ∀ a b c : M, Magma.op (Magma.op a b) c = b :=
    by
    intro a b c
    have step := h b a c
    grind
      -- Step 3: a ◇ b = c for all a, b, c.
        -- From hrel: (d ◇ a) ◇ c = a, so a ◇ b = ((d ◇ a) ◇ c) ◇ b = c by hrel.
      
  have hconst : ∀ a b c : M, Magma.op a b = c :=
    by
    intro a b c
    have h1 : Magma.op (Magma.op a a) c = a := hrel a a c
    have h2 : Magma.op (Magma.op (Magma.op a a) c) b = c := hrel (Magma.op a a) c b
    grind
      -- Conclude: x = x ◇ x = y.
      
  intro x y
  exact (hconst x x x).symm.trans (hconst x x y)

