import OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace Problem346


-- @@ L9-9 verbatim
universe u


-- @@ L11-11 verbatim
variable {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]


-- @@ L13-18 verbatim
/-- A form on symmetric powers, evaluated on products, is multilinear in all
of the underlying vector factors. -/
def flattenedSymmetricForm (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  (T.compMultilinearMap (fun _ => symMonomialMultilinear b V)).domDomCongr
    (Equiv.sigmaEquivProd (Fin a) (Fin b))


-- @@ L20-24 verbatim
@[simp]
theorem flattenedSymmetricForm_apply (T : SymmetricMultilinearForm a b V)
    (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T v =
      T (fun i => symMonomial b V (fun j => v (i, j))) := rfl


-- @@ L26-34 verbatim
/-- Independent permutations within the rows preserve the flattened form. -/
theorem flattenedSymmetricForm_inner_permute
    (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (p.1, σ p.1 p.2)) =
      flattenedSymmetricForm T v := by
  apply congrArg T
  funext i
  exact symMonomial_permute b V (σ i) (fun j => v (i, j))


-- @@ L36-43 verbatim
/-- Symmetry of the original form permits permutation of the rows. -/
theorem flattenedSymmetricForm_outer_permute
    (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (σ p.1, p.2)) =
      flattenedSymmetricForm T v := by
  exact hT σ (fun i => symMonomial b V (fun j => v (i, j)))


-- @@ L45-49 verbatim
/-- Compatibility API for the same flattened form, with inferred degrees. -/
abbrev flattenedForm {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  flattenedSymmetricForm T


-- @@ L51-54 verbatim
@[simp]
theorem flattenedForm_apply {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) (x : Fin a × Fin b → V) :
    flattenedForm T x = T (fun i => symMonomial b V (fun j => x (i, j))) := rfl


-- @@ L56-61 verbatim
theorem flattenedForm_permute_factors (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (p.1, σ p.1 p.2)) =
      flattenedForm T x :=
  flattenedSymmetricForm_inner_permute T σ x


-- @@ L63-69 verbatim
theorem flattenedForm_permute_slots (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (σ p.1, p.2)) =
      flattenedForm T x :=
  flattenedSymmetricForm_outer_permute T hT σ x


-- @@ L71-80 verbatim
/-- Simultaneous row and independent within-row permutation invariance. -/
theorem flattenedForm_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (τ : Fin a → Equiv.Perm (Fin b))
    (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (σ p.1, τ p.1 p.2)) =
      flattenedForm T x :=
  (flattenedForm_permute_factors a b V T τ (fun p => x (σ p.1, p.2))).trans
    (flattenedForm_permute_slots a b V T hT σ x)


-- @@ L82-86 verbatim
/-- Implicit-parameter factor symmetry used by the transfer sequences. -/
theorem flattenedForm_factor_perm (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedForm T (fun p => v (p.1, σ p.1 p.2)) = flattenedForm T v :=
  flattenedSymmetricForm_inner_permute T σ v


-- @@ L88-93 verbatim
/-- Implicit-parameter row symmetry used by the transfer sequences. -/
theorem flattenedForm_row_perm (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T) (σ : Equiv.Perm (Fin a))
    (v : Fin a × Fin b → V) :
    flattenedForm T (fun p => v (σ p.1, p.2)) = flattenedForm T v :=
  flattenedSymmetricForm_outer_permute T hT σ v


-- @@ L95-98 verbatim
@[simp] theorem flattenedForm_constant_rows (T : SymmetricMultilinearForm a b V)
    (v : Fin a → V) :
    flattenedForm T (fun p => v p.1) =
      T (fun i => symMonomial b V (fun _ => v i)) := rfl


-- @@ L100-103 verbatim
@[simp] theorem flattenedForm_constant_columns (T : SymmetricMultilinearForm a b V)
    (v : Fin b → V) :
    flattenedForm T (fun p => v p.2) =
      T (fun _ => symMonomial b V v) := rfl


-- @@ L105-105 verbatim
end Problem346


-- @@ L107-107 verbatim
end


-- @@ L109-109 verbatim
end OAI
