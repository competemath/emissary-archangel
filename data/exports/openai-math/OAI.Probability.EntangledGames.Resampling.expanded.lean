import OAI.Probability.EntangledGames.RelativeEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_X u_Y u_I u_E u_F u_R


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
namespace ThresholdParallelRepetition.FiniteProbability

-- @@ L10-10 verbatim
namespace Law

-- @@ L11-12 verbatim
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]


-- @@ L14-14 verbatim
abbrev Profile (I : Type u_I) (X : Type u_X) (Y : Type u_Y) := I → X × Y


-- @@ L16-17 verbatim
def updateLeft (z : Profile I X Y) (i : I) (x : X) : Profile I X Y :=
  Function.update z i (x,(z i).2)

-- @@ L18-19 verbatim
def updateRight (z : Profile I X Y) (i : I) (y : Y) : Profile I X Y :=
  Function.update z i ((z i).1,y)


-- @@ L21-23 verbatim
def left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenSecond x₀ (z i).2).avg (fun x => f (updateLeft z i x))

-- @@ L24-26 verbatim
def right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (z : Profile I X Y) : E :=
  (μ.givenFirst y₀ (z i).1).avg (fun y => f (updateRight z i y))


-- @@ L28-29 verbatim
def IgnoresLeft (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z x, f (updateLeft z i x) = f z

-- @@ L30-31 verbatim
def IgnoresRight (f : Profile I X Y → E) (i : I) : Prop :=
  ∀ z y, f (updateRight z i y) = f z


-- @@ L33-35 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_self (z : Profile I X Y) (i : I) : updateLeft z i (z i).1 = z := by
  simp [updateLeft]

-- @@ L36-38 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_self (z : Profile I X Y) (i : I) : updateRight z i (z i).2 = z := by
  simp [updateRight]

-- @@ L39-42 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_same (z : Profile I X Y) (i : I) (x x' : X) :
    updateLeft (updateLeft z i x) i x' = updateLeft z i x' := by
  simp [updateLeft]

-- @@ L43-46 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_same (z : Profile I X Y) (i : I) (y y' : Y) :
    updateRight (updateRight z i y) i y' = updateRight z i y' := by
  simp [updateRight]

-- @@ L47-51 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_comm (z : Profile I X Y) {i j : I} (hij : i ≠ j) (x x' : X) :
    updateLeft (updateLeft z i x) j x' = updateLeft (updateLeft z j x') i x := by
  simp only [updateLeft, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z

-- @@ L52-56 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_comm (z : Profile I X Y) {i j : I} (hij : i ≠ j) (y y' : Y) :
    updateRight (updateRight z i y) j y' = updateRight (updateRight z j y') i y := by
  simp only [updateRight, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z

-- @@ L57-64 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_right_comm (z : Profile I X Y) (i j : I) (x : X) (y : Y) :
    updateLeft (updateRight z j y) i x = updateRight (updateLeft z i x) j y := by
  by_cases hij : i = j
  · subst j; simp [updateLeft, updateRight]
  · simp only [updateLeft, updateRight, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ z


-- @@ L66-73 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresLeft (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    IgnoresLeft (μ.left x₀ i f) i := by
  intro z x
  simp only [left, updateLeft, Function.update_self]
  congr 1
  funext x'
  simp [Function.update_idem]

-- @@ L74-81 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    IgnoresRight (μ.right y₀ i f) i := by
  intro z y
  simp only [right, updateRight, Function.update_self]
  congr 1
  funext y'
  simp [Function.update_idem]


-- @@ L83-91 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresLeft_other (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.left x₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [left, hi]
  congr 1
  funext u
  rw [updateLeft_comm z (Ne.symm hij), hf _ _]

-- @@ L92-100 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresRight_other (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresRight f j) : IgnoresRight (μ.left x₀ i f) j := by
  intro z y
  have hi : updateRight z j y i = z i := Function.update_of_ne hij _ _
  simp only [left, hi]
  congr 1
  funext u
  rw [updateLeft_right_comm, hf _ _]

-- @@ L101-109 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresRight f j) : IgnoresRight (μ.right y₀ i f) j := by
  intro z y
  have hi : updateRight z j y i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [updateRight_comm z (Ne.symm hij), hf _ _]

-- @@ L110-118 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresLeft_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.right y₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [← updateLeft_right_comm, hf _ _]


-- @@ L120-125 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_of_ignores (μ : Law (X×Y)) (x₀ : X) (i : I)
    {f : Profile I X Y → E} (hf : IgnoresLeft f i) : μ.left x₀ i f = f := by
  funext z
  change (μ.givenSecond x₀ (z i).2).avg (fun x => f (updateLeft z i x)) = f z
  simp only [hf z, avg_const]

-- @@ L126-131 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_of_ignores (μ : Law (X×Y)) (y₀ : Y) (i : I)
    {f : Profile I X Y → E} (hf : IgnoresRight f i) : μ.right y₀ i f = f := by
  funext z
  change (μ.givenFirst y₀ (z i).1).avg (fun y => f (updateRight z i y)) = f z
  simp only [hf z, avg_const]


-- @@ L133-137 verbatim
omit [DecidableEq Y] in
lemma pair_avg_left (μ : Law (X×Y)) (x₀ : X) (f : X×Y → E) :
    μ.avg (fun z => (μ.givenSecond x₀ z.2).avg (fun x => f (x,z.2))) = μ.avg f := by
  rw [disintegrate_second μ x₀, disintegrate_second μ x₀ f]
  simp only [avg_const]

-- @@ L138-142 verbatim
omit [DecidableEq X] in
lemma pair_avg_right (μ : Law (X×Y)) (y₀ : Y) (f : X×Y → E) :
    μ.avg (fun z => (μ.givenFirst y₀ z.1).avg (fun y => f (z.1,y))) = μ.avg f := by
  rw [disintegrate_first μ y₀, disintegrate_first μ y₀ f]
  simp only [avg_const]


-- @@ L144-159 verbatim
omit [DecidableEq Y] in
lemma pi_avg_left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.left x₀ i f) = (pi (fun _ : I => μ)).avg f := by
  rw [pi_avg_split _ i, pi_avg_split _ i f]
  rw [avg_comm, avg_comm μ]
  congr 1
  funext r
  change μ.avg (fun z => (μ.givenSecond x₀ _).avg _) = _
  have he (z : X×Y) (x : X) :
      updateLeft ((Equiv.funSplitAt i (X×Y)).symm (z,r)) i x =
        (Equiv.funSplitAt i (X×Y)).symm ((x,z.2),r) := by
    simpa only [updateLeft, Equiv.funSplitAt_symm_apply, dite_eq_left] using
      update_split i r z (x,z.2)
  simp_rw [he]
  simpa only [Equiv.funSplitAt_symm_apply, dite_eq_left] using
    (pair_avg_left μ x₀ (fun z => f ((Equiv.funSplitAt i (X×Y)).symm (z,r))))

-- @@ L160-175 verbatim
omit [DecidableEq X] in
lemma pi_avg_right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.right y₀ i f) = (pi (fun _ : I => μ)).avg f := by
  rw [pi_avg_split _ i, pi_avg_split _ i f]
  rw [avg_comm, avg_comm μ]
  congr 1
  funext r
  change μ.avg (fun z => (μ.givenFirst y₀ _).avg _) = _
  have he (z : X×Y) (y : Y) :
      updateRight ((Equiv.funSplitAt i (X×Y)).symm (z,r)) i y =
        (Equiv.funSplitAt i (X×Y)).symm ((z.1,y),r) := by
    simpa only [updateRight, Equiv.funSplitAt_symm_apply, dite_eq_left] using
      update_split i r z (z.1,y)
  simp_rw [he]
  simpa only [Equiv.funSplitAt_symm_apply, dite_eq_left] using
    (pair_avg_right μ y₀ (fun z => f ((Equiv.funSplitAt i (X×Y)).symm (z,r))))


-- @@ L177-177 verbatim
section Linear

-- @@ L178-178 verbatim
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]

-- @@ L179-182 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_linear (μ : Law (X×Y)) (x₀ : X) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.left x₀ i f z) = μ.left x₀ i (fun q => L (f q)) z := avg_linear _ _ _

-- @@ L183-186 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_linear (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.right y₀ i f z) = μ.right y₀ i (fun q => L (f q)) z := avg_linear _ _ _


-- @@ L188-201 verbatim
omit [DecidableEq Y] in
lemma pi_left_pairing (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.left x₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.left x₀ i f z)) =
      μ.left x₀ i (fun z => L z (f z)) := by
    funext z
    rw [left_linear]
    unfold left
    congr 1
    funext x
    simp only [hL z x]
  rw [he, pi_avg_left]


-- @@ L203-216 verbatim
omit [DecidableEq X] in
lemma pi_right_pairing (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.right y₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.right y₀ i f z)) =
      μ.right y₀ i (fun z => L z (f z)) := by
    funext z
    rw [right_linear]
    unfold right
    congr 1
    funext y
    simp only [hL z y]
  rw [he, pi_avg_right]

-- @@ L217-217 verbatim
end Linear


-- @@ L219-219 verbatim
section Folds


-- @@ L221-222 verbatim
def lefts (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.left x₀) f


-- @@ L224-225 verbatim
def rights (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E) :
    Profile I X Y → E := l.foldr (μ.right y₀) f


-- @@ L227-235 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma lefts_ignoresLeft_mem (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → E) {i : I} (hi : i ∈ l) : IgnoresLeft (μ.lefts x₀ l f) i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    by_cases hj : j=i
    · subst j; exact left_ignoresLeft μ x₀ i _
    · exact left_ignoresLeft_other μ x₀ hj (ih ((List.mem_cons.mp hi).resolve_left (Ne.symm hj)))


-- @@ L237-245 verbatim
omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresRight_mem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → E) {i : I} (hi : i ∈ l) : IgnoresRight (μ.rights y₀ l f) i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    by_cases hj : j=i
    · subst j; exact right_ignoresRight μ y₀ i _
    · exact right_ignoresRight_other μ y₀ hj (ih ((List.mem_cons.mp hi).resolve_left (Ne.symm hj)))


-- @@ L247-255 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma lefts_ignoresRight_notMem (μ : Law (X×Y)) (x₀ : X) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresRight f i) :
    IgnoresRight (μ.lefts x₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact left_ignoresRight_other μ x₀ (Ne.symm h.1) (ih h.2)


-- @@ L257-265 verbatim
omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresLeft_notMem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresLeft f i) :
    IgnoresLeft (μ.rights y₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact right_ignoresLeft_other μ y₀ (Ne.symm h.1) (ih h.2)


-- @@ L267-267 verbatim
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]

-- @@ L268-278 verbatim
omit [DecidableEq Y] in
lemma pi_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.lefts x₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.left x₀ i (μ.lefts x₀ l f) z)) = _
    rw [pi_left_pairing μ x₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))


-- @@ L280-290 verbatim
omit [DecidableEq X] in
lemma pi_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.rights y₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.right y₀ i (μ.rights y₀ l f) z)) = _
    rw [pi_right_pairing μ y₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))

-- @@ L291-291 verbatim
end Folds


-- @@ L293-293 verbatim
section FixedCoordinate

-- @@ L294-299 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (x : X) :
    updateLeft (Function.update z i q) j x = Function.update (updateLeft z j x) i q := by
  simp only [updateLeft, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z

-- @@ L300-305 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (y : Y) :
    updateRight (Function.update z i q) j y = Function.update (updateRight z j y) i q := by
  simp only [updateRight, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z


-- @@ L307-312 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma left_update (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ j f (Function.update z i q) =
      μ.left x₀ j (fun r => f (Function.update r i q)) z := by
  simp only [left, Function.update_of_ne (Ne.symm hij), updateLeft_update _ hij]

-- @@ L313-318 verbatim
omit [Fintype I] [DecidableEq X] in
lemma right_update (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ j f (Function.update z i q) =
      μ.right y₀ j (fun r => f (Function.update r i q)) z := by
  simp only [right, Function.update_of_ne (Ne.symm hij), updateRight_update _ hij]


-- @@ L320-320 verbatim
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]

-- @@ L321-332 verbatim
omit [DecidableEq Y] in
lemma pi_fixed_left_pairing (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [left_update μ x₀ hij]
  apply pi_left_pairing
  intro z x
  dsimp only
  rw [← updateLeft_update _ hij, hL]

-- @@ L333-344 verbatim
omit [DecidableEq X] in
lemma pi_fixed_right_pairing (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [right_update μ y₀ hij]
  apply pi_right_pairing
  intro z y
  dsimp only
  rw [← updateRight_update _ hij, hL]


-- @@ L346-360 verbatim
omit [DecidableEq Y] in
lemma pi_fixed_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.lefts x₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j (μ.lefts x₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_left_pairing μ x₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))

-- @@ L361-375 verbatim
omit [DecidableEq X] in
lemma pi_fixed_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.rights y₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j (μ.rights y₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_right_pairing μ y₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))

-- @@ L376-376 verbatim
end FixedCoordinate


-- @@ L378-378 verbatim
section FoldLinear

-- @@ L379-379 verbatim
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]

-- @@ L380-391 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma lefts_linear (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E)
    (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.lefts x₀ l f z) = μ.lefts x₀ l (fun q => L (f q)) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change L ((μ.givenSecond x₀ (z i).2).avg _) = _
    rw [avg_linear]
    change (μ.givenSecond x₀ (z i).2).avg (fun x => L (μ.lefts x₀ l f (updateLeft z i x))) =
      (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (fun q => L (f q)) (updateLeft z i x))
    simp only [ih]

-- @@ L392-403 verbatim
omit [Fintype I] [DecidableEq X] in
lemma rights_linear (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E)
    (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.rights y₀ l f z) = μ.rights y₀ l (fun q => L (f q)) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change L ((μ.givenFirst y₀ (z i).1).avg _) = _
    rw [avg_linear]
    change (μ.givenFirst y₀ (z i).1).avg (fun y => L (μ.rights y₀ l f (updateRight z i y))) =
      (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (fun q => L (f q)) (updateRight z i y))
    simp only [ih]

-- @@ L404-414 verbatim
omit [Fintype I] [DecidableEq Y] in
lemma lefts_sum (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.lefts x₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.lefts x₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (fun q => ∑ r, f r q) (updateLeft z i x)) =
      ∑ r, (μ.givenSecond x₀ (z i).2).avg (fun x => μ.lefts x₀ l (f r) (updateLeft z i x))
    simp only [ih]
    exact avg_sum _ _

-- @@ L415-425 verbatim
omit [Fintype I] [DecidableEq X] in
lemma rights_sum (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : R → Profile I X Y → E)
    (z : Profile I X Y) :
    μ.rights y₀ l (fun q => ∑ r, f r q) z = ∑ r, μ.rights y₀ l (f r) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    change (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (fun q => ∑ r, f r q) (updateRight z i y)) =
      ∑ r, (μ.givenFirst y₀ (z i).1).avg (fun y => μ.rights y₀ l (f r) (updateRight z i y))
    simp only [ih]
    exact avg_sum _ _

-- @@ L426-426 verbatim
end FoldLinear


-- @@ L428-428 verbatim
end Law

-- @@ L429-429 verbatim
end ThresholdParallelRepetition.FiniteProbability


-- @@ L431-431 verbatim
end


-- @@ L433-433 verbatim
end OAI
