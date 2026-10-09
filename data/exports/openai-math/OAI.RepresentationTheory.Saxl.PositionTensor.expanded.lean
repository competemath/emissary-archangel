import OAI.RepresentationTheory.Saxl.SupportSeparation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped TensorProduct


-- @@ L9-11 verbatim
namespace Saxl

/- Concatenation of words on independent position blocks. -/

-- @@ L12-14 verbatim
def joinPositions {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : Fin n → Fin d :=
  fun i => Sum.elim x y (e i)


-- @@ L16-19 verbatim
@[simp] lemma leftWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : leftWord e (joinPositions e x y) = x := by
  funext i
  simp [leftWord, joinPositions]


-- @@ L21-24 verbatim
@[simp] lemma rightWord_join {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : Fin a → Fin d) (y : Fin b → Fin d) : rightWord e (joinPositions e x y) = y := by
  funext i
  simp [rightWord, joinPositions]


-- @@ L26-30 verbatim
@[simp] lemma joinPositions_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) : joinPositions e (leftWord e w) (rightWord e w) = w := by
  funext i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp [joinPositions,leftWord,rightWord]


-- @@ L32-39 verbatim
def positionUncurry {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    ((Fin b → Fin d) → WordSpace a d) ≃ₗ[ℂ] WordSpace n d where
  toFun f w := f (rightWord e w) (leftWord e w)
  invFun z y x := z (joinPositions e x y)
  left_inv f := by ext y x; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L41-43 verbatim
def positionTensor {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    WordSpace a d ⊗[ℂ] WordSpace b d ≃ₗ[ℂ] WordSpace n d :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace a d) (Fin b → Fin d) ≪≫ₗ positionUncurry e


-- @@ L45-50 verbatim
@[simp] lemma positionTensor_tmul {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionTensor e (x ⊗ₜ[ℂ] y) = positionProduct e x y := by
  funext w
  change y (rightWord e w) * x (leftWord e w) = _
  exact mul_comm _ _


-- @@ L52-66 verbatim
lemma positionProduct_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (x : WordSpace a d) (y : WordSpace b d) :
    wordRep n d (sumPerm e g h) (positionProduct e x y) =
      positionProduct e (wordRep a d g x) (wordRep b d h y) := by
  funext w
  change x (leftWord e (w ∘ sumPerm e g h)) * y (rightWord e (w ∘ sumPerm e g h)) = _
  have hl : leftWord e (w ∘ sumPerm e g h) = leftWord e w ∘ g := by
    funext i
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e g h) = rightWord e w ∘ h := by
    funext i
    simp [rightWord]
  rw [hl,hr]
  rfl


-- @@ L68-75 verbatim
lemma positionTensor_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (z : WordSpace a d ⊗[ℂ] WordSpace b d) :
    positionTensor e (TensorProduct.map (wordRep a d g) (wordRep b d h) z) =
      wordRep n d (sumPerm e g h) (positionTensor e z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rw [TensorProduct.map_tmul, positionTensor_tmul, positionTensor_tmul, positionProduct_equivariant]


-- @@ L77-121 verbatim
lemma product_mem_cyclic {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ cyclic (wordRep a d) v) (hy : y ∈ cyclic (wordRep b d) u) :
    positionProduct e x y ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  let S := cyclic (wordRep n d) (positionProduct e v u)
  change x ∈ Submodule.span ℂ _ at hx
  change y ∈ Submodule.span ℂ _ at hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [← positionProduct_equivariant]
      exact S.apply_mem_toSubmodule (sumPerm e g h) (mem_cyclic _ _)
    | zero =>
      have hz : positionProduct e (wordRep a d g v) 0 = 0 := by ext; simp [positionProduct]
      rw [hz]
      exact S.toSubmodule.zero_mem
    | add y z hy hz ihy ihz =>
      have he : positionProduct e (wordRep a d g v) (y+z) =
          positionProduct e (wordRep a d g v) y + positionProduct e (wordRep a d g v) z := by
        ext; simp [positionProduct,mul_add]
      rw [he]
      exact S.toSubmodule.add_mem ihy ihz
    | smul c y hy ih =>
      have he : positionProduct e (wordRep a d g v) (c • y) =
          c • positionProduct e (wordRep a d g v) y := by ext; simp [positionProduct,mul_left_comm]
      rw [he]
      exact S.toSubmodule.smul_mem c ih
  | zero =>
    have hz : positionProduct e 0 y = 0 := by ext; simp [positionProduct]
    rw [hz]
    exact S.toSubmodule.zero_mem
  | add x z hx hz ihx ihz =>
    have he : positionProduct e (x+z) y = positionProduct e x y + positionProduct e z y := by
      ext; simp [positionProduct,add_mul]
    rw [he]
    exact S.toSubmodule.add_mem ihx ihz
  | smul c x hx ih =>
    have he : positionProduct e (c • x) y = c • positionProduct e x y := by
      ext; simp [positionProduct,mul_assoc]
    rw [he]
    exact S.toSubmodule.smul_mem c ih


-- @@ L123-123 verbatim
end Saxl


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
end OAI
