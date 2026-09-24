module

public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.Meta.ClProver


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-9 verbatim
/-!
# Abstract incompleteness theorems and related results
-/


-- @@ L11-11 verbatim
namespace FFL


-- @@ L13-13 verbatim
open FFL.Entailment


-- @@ L15-15 verbatim
namespace FirstOrder


-- @@ L17-17 verbatim
variable {L₀ L : Language}


-- @@ L19-19 verbatim
abbrev Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)


-- @@ L21-21 verbatim
namespace ProvabilityAbstraction


-- @@ L23-26 verbatim
structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]


-- @@ L28-28 verbatim
namespace Provability


-- @@ L30-30 verbatim
variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}


-- @@ L32-32 verbatim
@[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]

-- @@ L33-33 verbatim
instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩


-- @@ L35-35 verbatim
def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥


-- @@ L37-37 verbatim
abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)


-- @@ L39-39 verbatim
end Provability



-- @@ L42-42 verbatim
section


-- @@ L44-44 verbatim
namespace Provability


-- @@ L46-46 verbatim
section


-- @@ L48-52 verbatim
variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma D1 {𝔅 : Provability T₀ T} {σ : Sentence L} : T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.bew_def h


-- @@ L54-55 verbatim
class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ

-- @@ L56-56 verbatim
export HBL2 (D2)


-- @@ L58-58 verbatim
variable [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)


-- @@ L60-61 verbatim
class HBL3 where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)

-- @@ L62-62 verbatim
export HBL3 (D3)


-- @@ L64-64 verbatim
class HBL extends 𝔅.HBL2, 𝔅.HBL3


-- @@ L66-67 verbatim
class Mono [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  mono {σ τ : Sentence L} : T ⊢ σ 🡒 τ → T₀ ⊢ 𝔅 σ 🡒 𝔅 τ

-- @@ L68-68 verbatim
export Mono (mono)


-- @@ L70-71 verbatim
class Ext [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  ext {σ τ : Sentence L} : T ⊢ σ 🡘 τ → T₀ ⊢ 𝔅 σ 🡘 𝔅 τ

-- @@ L72-72 verbatim
export Ext (ext)


-- @@ L74-75 verbatim
class Rosser [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ

-- @@ L76-76 verbatim
export Rosser (Ros)



-- @@ L79-85 verbatim
/--
  Abstract version of formalized `Γ`-completeness for provability `𝔅`.

  example: `[∀ σ ∈ 𝚺₁, 𝔅.FormalizedCompleteOn σ]` for formalized `𝚺₁`-completeness.
-/
class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
  formalized_complete_on : T₀ ⊢ σ 🡒 𝔅 σ

-- @@ L86-86 verbatim
export FormalizedCompleteOn (formalized_complete_on)

-- @@ L87-87 verbatim
attribute [simp, grind .] formalized_complete_on


-- @@ L89-89 verbatim
instance [∀ σ, 𝔅.FormalizedCompleteOn (𝔅 σ)] : 𝔅.HBL3 := ⟨by simp⟩


-- @@ L91-95 verbatim
/--
  NOTE: Named after [Vis21].
-/
class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ

-- @@ L96-96 verbatim
export Kreisel (KR)

-- @@ L97-97 verbatim
attribute [simp, grind .] KR



-- @@ L100-104 verbatim
class SoundOn
  [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}
  (𝔅 : Provability T₀ T) (M : outParam Type*) [Nonempty M] [Structure L₀ M]
  where
  sound_on {σ : Sentence L} : M↓[L₀] ⊧ (𝔅 σ : Sentence L₀) → T ⊢ σ

-- @@ L105-105 verbatim
export SoundOn (sound_on)

-- @@ L106-106 verbatim
attribute [simp, grind .] sound_on


-- @@ L108-116 verbatim
omit [L.ReferenceableBy L₀] in
lemma syntactical_sound {T₀ T : Theory L} {𝔅 : Provability T₀ T}
    (M : Type*) [Nonempty M] [Structure L M] [SoundOn 𝔅 M] [M↓[L] ⊧* T₀] :
    ∀ {σ : Sentence L}, T₀ ⊢ 𝔅 σ → T ⊢ σ := by
  intro σ h;
  apply 𝔅.sound_on;
  apply models_of_provable (L := L) (T := T₀);
  . infer_instance;
  . exact h;


-- @@ L118-118 verbatim
end



-- @@ L121-121 verbatim
section


-- @@ L123-129 verbatim
variable
  [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}
  {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma bew_distribute_imply [𝔅.HBL2] (h : T₀ ⊢ 𝔅 (σ 🡒 τ)) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := D2 ⨀ h


-- @@ L131-131 verbatim
instance [𝔅.HBL2] : 𝔅.Mono := ⟨λ h => bew_distribute_imply $ D1 h⟩

-- @@ L132-150 verbatim
instance [𝔅.HBL2] : 𝔅.Ext := ⟨λ h => E_intro (mono (K_left h)) (mono (K_right h))⟩

lemma bew_distribute_and [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 σ := bew_distribute_imply $ D1 and₁;
  have h₂ : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 τ := bew_distribute_imply $ D1 and₂;
  cl_prover [h₁, h₂];

lemma bew_distribute_and' [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ := λ h => bew_distribute_and ⨀ h

lemma bew_collect_and [𝔅.HBL2] [L₀.DecidableEq] [L.DecidableEq] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ 🡒 𝔅 (σ ⋏ τ) := by
  have h₁ : T₀ ⊢ 𝔅 σ 🡒 𝔅 (τ 🡒 σ ⋏ τ) := 𝔅.mono $ by cl_prover
  have h₂ : T₀ ⊢ 𝔅 (τ 🡒 σ ⋏ τ) 🡒 𝔅 τ 🡒 𝔅 (σ ⋏ τ) := D2;
  cl_prover [h₁, h₂];


lemma dia_mono [L₀.DecidableEq] [L.DecidableEq] [𝔅.Mono]
  (h : T ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅.dia σ 🡒 𝔅.dia τ := by
  have : T₀ ⊢ 𝔅 (∼τ) 🡒 𝔅 (∼σ) := 𝔅.mono $ by cl_prover [h];
  cl_prover [this]


-- @@ L152-152 verbatim
end


-- @@ L154-154 verbatim
section


-- @@ L156-162 verbatim
variable
  [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
  {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma mono' [𝔅.Mono] (h : T₀ ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := 𝔅.mono $ WeakerThan.pbl h
lemma ext' [𝔅.Ext] (h : T₀ ⊢ σ 🡘 τ) : T₀ ⊢ 𝔅 σ 🡘 𝔅 τ := 𝔅.ext $ WeakerThan.pbl h


-- @@ L164-164 verbatim
end


-- @@ L166-166 verbatim
end Provability



-- @@ L169-169 verbatim
end





-- @@ L174-176 verbatim
class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]


-- @@ L178-178 verbatim
open FFL.Entailment Diagonalization Provability


-- @@ L180-182 verbatim
variable
  [L.ReferenceableBy L]
  {T₀ T : Theory L} [Diagonalization T₀] {𝔅 : Provability T₀ T}


-- @@ L184-187 verbatim
def gödel (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ “x. ¬!𝔅.prov x”

lemma gödel_spec : T₀ ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅) := by simpa [gödel, Provability.pr] using diag “x. ¬!𝔅.prov x”;


-- @@ L189-189 verbatim
section First


-- @@ L191-191 verbatim
variable [L.DecidableEq]

-- @@ L192-192 verbatim
variable [T₀ ⪯ T] [Consistent T]


-- @@ L194-200 verbatim
theorem unprovable_gödel : T ⊬ (gödel 𝔅) := by
  intro h;
  have h₁ : T ⊢ 𝔅 (gödel 𝔅) := WeakerThan.pbl $ D1 h;
  have h₂ : T ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅) := WeakerThan.pbl $ gödel_spec;
  have : T ⊢ ⊥ := by cl_prover [h₁, h₂, h];
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this;
  contradiction


-- @@ L202-207 verbatim
theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼(gödel 𝔅) := by
  intro h₂;
  have h₁ : T ⊢ (gödel 𝔅) := WeakerThan.pbl $ 𝔅.KR $ by cl_prover [gödel_spec (T₀ := T₀), h₂];
  have : T ⊢ ⊥ := (N_iff_CO.mp $ WeakerThan.pbl $ h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this
  contradiction;


-- @@ L209-212 verbatim
theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅) := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_gödel


-- @@ L214-215 verbatim
theorem first_incompleteness [𝔅.Kreisel] : Incomplete T :=
  incomplete_def.mpr ⟨(gödel 𝔅), gödel_independent⟩


-- @@ L217-217 verbatim
end First



-- @@ L220-220 verbatim
section Second


-- @@ L222-222 verbatim
variable [𝔅.HBL]


-- @@ L224-225 verbatim
omit [Diagonalization T₀] in
lemma formalized_consistent_of_existance_unprovable [L.DecidableEq] : T₀ ⊢ ∼𝔅 σ 🡒 𝔅.con := contra $ mdp D2 $ D1 efq


-- @@ L227-227 verbatim
local notation "𝐆" => gödel 𝔅


-- @@ L229-229 verbatim
variable [L.DecidableEq] [T₀ ⪯ T]


-- @@ L231-237 verbatim
/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_gödel  : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆 := by
  suffices T₀ ⊢ ∼𝔅 ⊥ 🡒 ∼𝔅 𝐆 from this
  have h₁ : T₀ ⊢ 𝔅 𝐆 🡒 𝔅 (𝔅 𝐆) := D3
  have h₂ : T₀ ⊢ 𝔅 𝐆 🡒 𝔅 (𝔅 𝐆 🡒 ⊥) := 𝔅.mono' $ by cl_prover [gödel_spec (T₀ := T₀)]
  have h₃ : T₀ ⊢ 𝔅 (𝔅 𝐆 🡒 ⊥) 🡒 𝔅 (𝔅 𝐆) 🡒 𝔅 ⊥ := D2
  cl_prover [h₁, h₂, h₃]


-- @@ L239-243 verbatim
theorem gödel_iff_con : T₀ ⊢ 𝐆 🡘 𝔅.con := by
  have h₁ : T₀ ⊢ ∼𝔅 𝐆 🡒 𝔅.con := formalized_consistent_of_existance_unprovable
  have h₂ : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆 := formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝐆 🡘 ∼𝔅 𝐆 := gödel_spec
  cl_prover [h₁, h₂, h₃];


-- @@ L245-249 verbatim
theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con := by
  intro h
  have : T₀ ⊢ 𝐆 🡘 𝔅.con := gödel_iff_con
  have : T ⊢ 𝐆 := by cl_prover [h, this]
  exact unprovable_gödel this


-- @@ L251-255 verbatim
theorem con_unrefutable [Consistent T] [𝔅.Kreisel] : T ⊬ ∼𝔅.con := by
  intro h
  have : T ⊢ 𝐆 🡘 𝔅.con := WeakerThan.pbl $ gödel_iff_con;
  have : T ⊢ ∼𝐆 := by cl_prover [h, this]
  exact unrefutable_gödel this


-- @@ L257-260 verbatim
theorem con_independent [Consistent T] [𝔅.Kreisel] : Independent T 𝔅.con := by
  constructor
  . apply con_unprovable
  . apply con_unrefutable


-- @@ L262-262 verbatim
end Second



-- @@ L265-265 verbatim
section Löb


-- @@ L267-267 verbatim
def kreisel (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”


-- @@ L269-269 verbatim
variable {σ : Sentence L}


-- @@ L271-275 verbatim
local notation "𝐊" => kreisel 𝔅

lemma kreisel_spec : T₀ ⊢ (𝐊 σ) 🡘 (𝔅 (𝐊 σ) 🡒 σ) := by
  have := diag (T := T₀) “x. !𝔅.prov x → !σ”
  simpa [kreisel, Provability.pr, Rew.subst_comp_subst, ←TransitiveRewriting.comp_app] using this;


-- @@ L277-277 verbatim
private lemma kreisel_specAux₂ : T₀ ⊢ (𝔅 (𝐊 σ) 🡒 σ) 🡒 (𝐊 σ) := K_right kreisel_spec


-- @@ L279-279 verbatim
variable [𝔅.HBL]


-- @@ L281-282 verbatim
private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ :=
  Entailment.mdp₁ (C_trans (mdp D2 (D1 (WeakerThan.pbl <| K_left (kreisel_spec)))) D2) D3


-- @@ L284-284 verbatim
variable [L.DecidableEq] [T₀ ⪯ T]


-- @@ L286-289 verbatim
theorem löb_theorem (H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ := by
  have d₁ : T ⊢ 𝔅 (𝐊 σ) 🡒 σ := C_trans (WeakerThan.pbl kreisel_specAux₁) H;
  have d₂ : T ⊢ 𝔅 (𝐊 σ)     := WeakerThan.pbl $ D1 $ WeakerThan.pbl kreisel_specAux₂ ⨀ d₁;
  exact d₁ ⨀ d₂;


-- @@ L291-312 verbatim
theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ := by
  have h₁ : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ := kreisel_specAux₁;
  have h₂ : T₀ ⊢ (𝔅 σ 🡒 σ) 🡒 (𝔅 (𝐊 σ) 🡒 σ) := CCC_of_C_left h₁;
  have h₃ : T ⊢ (𝔅 σ 🡒 σ) 🡒 𝐊 σ := WeakerThan.pbl $ C_trans (CCC_of_C_left h₁) kreisel_specAux₂;
  exact C_trans (D2 ⨀ (D1 h₃)) h₁;

lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢ ∼𝔅.con := löb_theorem $ CN_of_CN_right hC;
  have : T ⊬ ∼𝔅.con := con_unrefutable;
  contradiction;

lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼(gödel 𝔅)) := by
  by_contra hC;
  have : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := formalized_unprovable_not_con;
  have : T ⊢ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := C_trans hC
    $ WeakerThan.pbl
    $ K_left $ ENN_of_E
    $ 𝔅.ext
    $ ENN_of_E
    $ WeakerThan.pbl gödel_iff_con
  contradiction;


-- @@ L314-314 verbatim
end Löb



-- @@ L317-317 verbatim
section Rosser


-- @@ L319-319 verbatim
variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T] {𝔅 : Provability T₀ T}


-- @@ L321-321 verbatim
local notation "𝐑" => gödel 𝔅


-- @@ L323-328 verbatim
theorem unrefutable_rosser [𝔅.Rosser] : T ⊬ ∼𝐑 := by
  intro hnρ;
  have hρ : T ⊢ 𝐑 := WeakerThan.pbl $ (K_right gödel_spec) ⨀ (Ros hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    (N_iff_CO.mp hnρ) ⨀ hρ;
  contradiction


-- @@ L330-333 verbatim
theorem rosser_independent [L.DecidableEq] [𝔅.Rosser] : Independent T 𝐑 := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_rosser


-- @@ L335-336 verbatim
theorem rosser_first_incompleteness [L.DecidableEq] (𝔅 : Provability T₀ T) [𝔅.Rosser] : Incomplete T :=
  incomplete_def.mpr ⟨gödel 𝔅, rosser_independent⟩


-- @@ L338-342 verbatim
omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable from `T`. -/
theorem kreisel_remark [𝔅.Rosser] : T ⊢ 𝔅.con := by
  have : T₀ ⊢ ∼𝔅 ⊥ := Ros (N_iff_CO.mpr (by simp));
  exact WeakerThan.pbl $ this;


-- @@ L344-344 verbatim
end Rosser


-- @@ L346-346 verbatim
end ProvabilityAbstraction


-- @@ L348-348 verbatim
end FirstOrder
