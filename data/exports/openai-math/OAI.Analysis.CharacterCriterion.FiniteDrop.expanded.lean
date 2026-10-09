import OAI.Analysis.CharacterCriterion.FullComparison


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [instSize : KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]



-- @@ L24-24 verbatim
namespace KirchbergRordam.GenericRW.ConeDrop

-- @@ L25-25 verbatim
open scoped CStarAlgebra ComplexOrder BigOperators

-- @@ L26-26 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor ConeModel

-- @@ L27-27 verbatim
local instance : PartialOrder Cone := CStarAlgebra.spectralOrder _

-- @@ L28-28 verbatim
local instance : LE Cone := (CStarAlgebra.spectralOrder Cone).toLE

-- @@ L29-29 verbatim
local instance : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _

-- @@ L30-30 verbatim
variable {P : Type*} [CStarAlgebra P]

-- @@ L31-31 verbatim
local instance (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _

-- @@ L32-32 verbatim
local instance (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _


-- @@ L34-39 verbatim
lemma map_y (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) (hδ : 0≤δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.y k δ hδ j)=cornerWord k (η (ConeCut.q δ hδ)) (η (ConeCut.g δ)) j := by
  rw [ConeCube.y,powerHom_word,cornerWord]
  congr 1
  funext i
  split_ifs <;> rfl

-- @@ L40-43 verbatim
lemma map_defect (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) (δ : ℝ) :
    1-powerHom η k (ConeCube.h k δ)=defectWord k (η (ConeCut.g δ)) := by
  rw [← map_one (powerHom η k),← map_sub,ConeCube.defect_word,powerHom_word]
  rfl

-- @@ L44-47 verbatim
lemma map_fix (η : Cone →⋆ₐ[ℂ] P) (k : ℕ) {δ : ℝ} (hδ : 0<δ) (j : Fin (k+1)) :
    powerHom η k (ConeCube.x k δ 0 0)*cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j=
      cornerWord k (η (ConeCut.q δ hδ.le)) (η (ConeCut.g δ)) j := by
  rw [← map_y,← map_mul,ConeCube.x_fixes_y k hδ j]


-- @@ L49-55 verbatim
omit instSize instPauliData in
lemma map_nonneg_generic
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    [pE : PartialOrder E] [StarOrderedRing E] [PartialOrder F] [StarOrderedRing F]
    (φ : E →⋆ₐ[ℂ] F) {a : E} (ha : 0≤a) : 0≤φ a := map_nonneg φ ha

-- @@ L56-56 verbatim
variable [Nontrivial P] [PartialOrder P] [StarOrderedRing P]



-- @@ L59-118 verbatim
theorem exists_drop_from_full_cone (η : Cone →⋆ₐ[ℂ] P)
    (hfull : Fullness.IsFull (η (ConeCut.q 0 (le_refl 0)))) :
    ∃ m : ℕ, Nonempty (DimensionDrop23 →⋆ₐ[ℂ] powerPack P m) := by
  classical
  obtain ⟨δ,hδ,hδ1,hfullδ⟩ := ConeCut.exists_full_cut η hfull
  let c := η (ConeCut.q δ hδ.le)
  let G := η (ConeCut.g δ)
  let z : Fin 2→P := fun i=>η (ConeCut.z δ hδ.le (Fin.castLE PauliData.two_le i))
  have hz (i j : Fin 2) : star (z i)*z j=if i=j then c else 0 := by
    dsimp only [z,c]
    rw [← map_star,← map_mul,ConeCut.z_gram]
    have he : (Fin.castLE PauliData.two_le i = Fin.castLE PauliData.two_le j) ↔ i=j :=
      (Fin.castLE_injective PauliData.two_le).eq_iff
    simp only [he, apply_ite, map_zero]
    split_ifs <;> rfl
  have hc : 0≤c := by rw [← show star (z 0)*z 0=c by simpa using hz 0 0]; exact star_mul_self_nonneg _
  have hG : 0≤G := map_nonneg_generic (pE:=CStarAlgebra.spectralOrder Cone) η (ConeCut.g_nonneg δ)
  have hcG : c*G=0 := by dsimp only [c,G]; rw [← map_mul,ConeCut.qg_zero hδ,map_zero]
  obtain ⟨N,v,hv⟩ := FullComparison.full_comparison hc hfullδ
  have hN : N≠0 := by intro he; subst N; simp at hv
  let : NeZero N := ⟨hN⟩
  obtain ⟨L,e,a,b,ha,hb⟩ := auxiliary c v hv z hz
  let J := Fin (L+1)→Fin N
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α:=J))
  let σ : Fin (k+1)≃J := (Fintype.equivFinOfCardEq hk).symm
  let Y : Fin (k+1)→powerPack P k := cornerWord k c G
  let U : Fin (k+1)→Fin N→powerPack P k := fun j i=>columnWord k G j (v i)
  let V : Fin (k+1)→powerPack P L := fun j=>b (σ j)
  have hV : ∑ j,star (V j)*e*V j=1 := by
    have he := σ.sum_comp (fun j=>star (b j)*e*b j)
    exact he.trans hb
  let B := MaxTensor.Algebra (powerPack P k) (powerPack P L)
  let : PartialOrder B := CStarAlgebra.spectralOrder _
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  let φ : powerPack P k →⋆ₐ[ℂ] B := includeLeft
  let ψ : powerPack P L →⋆ₐ[ℂ] B := includeRight
  let W := ((ConeCube.weighted k hδ).map (powerHom η k)).map φ
  have hY (j) : 0≤Y j := cornerWord_nonneg k hc hG j
  have hYY (j l) (hjl : j≠l) : Y j*Y l=0 := cornerWord_orthogonal k hcG j l hjl
  have hU (j) : ∑ i,star (U j i)*Y j*U j i=defectWord k G := columnWord_comparison k hG v hv j
  have hcomp := AmplifiedComparison.compare φ ψ (fun x y=>legs_commute x y)
    Y hY hYY U a V e ha (defectWord k G) hU hV
  have hsum : 0≤φ (∑ j,Y j) := map_nonneg φ (Finset.sum_nonneg (fun j _=>hY j))
  have hfix : W.x 0 0*φ (∑ j,Y j)=φ (∑ j,Y j) := by
    change φ (powerHom η k (ConeCube.x k δ 0 0))*φ (∑ j,Y j)=_
    rw [← map_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_fix η k hδ j
  have hcut := support_cut_comparison (W.star_x 0 0) hsum hfix
  have hdef : 1-W.h=φ (defectWord k G) := by
    change 1-φ (powerHom η k (ConeCube.h k δ))=_
    rw [← map_one φ,← map_sub,map_defect]
  have hw : CuntzBelow (1-W.h) (ExactCut.cut (W.x 0 0) (1/2)) := by
    rw [hdef]
    exact hcomp.trans hcut
  obtain ⟨flatten⟩ := exists_joinPower P k L
  exact ⟨k+L+1,⟨flatten.comp (W.cutoffHom hw)⟩⟩

-- @@ L119-119 verbatim
end KirchbergRordam.GenericRW.ConeDrop


-- @@ L121-121 verbatim
namespace KirchbergRordam.GenericRW.MaxTensor

-- @@ L122-122 verbatim
open scoped BigOperators

-- @@ L123-123 verbatim
universe u

-- @@ L124-124 verbatim
variable {P Q : Type u} [CStarAlgebra P] [CStarAlgebra Q]


-- @@ L126-136 verbatim
omit instSize instPauliData in
lemma norm_pure_le
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {P : Type u}
    {Q : Type u}
    [CStarAlgebra P]
    [CStarAlgebra Q]
    (a : P) (b : Q) : ‖pure a b‖≤‖a‖*‖b‖ :=
  (norm_mul_le _ _).trans (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le includeLeft a)
    (NonUnitalStarAlgHom.norm_apply_le includeRight b) (norm_nonneg _) (norm_nonneg _))


-- @@ L138-138 verbatim
variable [PartialOrder P] [StarOrderedRing P] [PartialOrder Q] [StarOrderedRing Q]

-- @@ L139-139 verbatim
local instance : PartialOrder (Algebra P Q) := CStarAlgebra.spectralOrder _

-- @@ L140-140 verbatim
local instance : StarOrderedRing (Algebra P Q) := CStarAlgebra.spectralOrderedRing _

-- @@ L141-147 verbatim
lemma pure_nonneg {a : P} {b : Q} (ha : 0≤a) (hb : 0≤b) : 0≤pure a b := by
  have he : star (pure (CFC.sqrt a) (CFC.sqrt b))*pure (CFC.sqrt a) (CFC.sqrt b)=pure a b := by
    rw [pure_star,pure_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
      CFC.sqrt_mul_sqrt_self _ ha,CFC.sqrt_mul_sqrt_self _ hb]
  rw [← he]
  exact star_mul_self_nonneg _

-- @@ L148-148 verbatim
end KirchbergRordam.GenericRW.MaxTensor


-- @@ L150-150 verbatim
namespace KirchbergRordam.GenericRW.FullRankWeighted

-- @@ L151-151 verbatim
open scoped BigOperators

-- @@ L152-152 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness

-- @@ L153-153 verbatim
universe u

-- @@ L154-154 verbatim
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L155-155 verbatim
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

-- @@ L156-156 verbatim
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

-- @@ L157-157 verbatim
local instance : PartialOrder (Algebra A B) := CStarAlgebra.spectralOrder _

-- @@ L158-158 verbatim
local instance : StarOrderedRing (Algebra A B) := CStarAlgebra.spectralOrderedRing _


-- @@ L160-171 verbatim
def tensor (W : WeightedUnits I A) (V : WeightedUnits J B) : WeightedUnits (I×J) (Algebra A B) where
  h := pure W.h V.h
  x i j := pure (W.x i.1 j.1) (V.x i.2 j.2)
  nonneg := pure_nonneg W.nonneg V.nonneg
  norm_le := (norm_pure_le _ _).trans (by nlinarith [W.norm_le,V.norm_le,norm_nonneg W.h,norm_nonneg V.h])
  star_x i j := by rw [pure_star,W.star_x,V.star_x]
  mul_x i j k l := by
    rw [pure_mul,W.mul_x,V.mul_x]
    by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
      simp [h1,h2,Prod.ext_iff,pure_mul]
  diagonal := by
    simp only [Fintype.sum_prod_type,← pure_sum_right,← pure_sum_left,W.diagonal,V.diagonal]


-- @@ L173-180 verbatim
def reindex (W : WeightedUnits I A) (e : I ≃ J) : WeightedUnits J A where
  h := W.h
  x i j := W.x (e.symm i) (e.symm j)
  nonneg := W.nonneg
  norm_le := W.norm_le
  star_x i j := W.star_x _ _
  mul_x i j k l := by simp only [W.mul_x,EmbeddingLike.apply_eq_iff_eq]
  diagonal := (Equiv.sum_comp e.symm (fun i=>W.x i i)).trans W.diagonal


-- @@ L182-182 verbatim
variable [instNontrivialA : Nontrivial A]

-- @@ L183-211 verbatim
omit instSize instPauliData instNontrivialA in
lemma pure_full
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type u}
    {B : Type u}
    [CStarAlgebra A]
    [CStarAlgebra B]
    [PartialOrder A]
    [StarOrderedRing A]
    [PartialOrder B]
    [StarOrderedRing B]
    [Nontrivial A]
    {a : A} {b : B} (ha : IsFull a) (hb : IsFull b) : IsFull (pure a b) := by
  classical
  obtain ⟨n,h,l,h1⟩ := FullComparison.finite_presentation ha
  obtain ⟨m,s,t,h2⟩ := FullComparison.finite_presentation hb
  let K := TwoSidedIdeal.span ({pure a b} : Set (Algebra A B))
  apply TwoSidedIdeal.eq_top
  have he : (∑ i : Fin n, ∑ j : Fin m, pure (h i) (s j)*pure a b*pure (l i) (t j))=1 := by
    simp only [pure_mul]
    simp_rw [← pure_sum_right]
    rw [← pure_sum_left,h1,h2,pure_one]
  rw [← he]
  apply K.asIdeal.sum_mem
  intro i hi
  apply K.asIdeal.sum_mem
  intro j hj
  exact K.mul_mem_right _ _ (K.mul_mem_left _ _ (TwoSidedIdeal.subset_span (by simp)))

-- @@ L212-212 verbatim
end KirchbergRordam.GenericRW.FullRankWeighted


-- @@ L214-214 verbatim
namespace KirchbergRordam.GenericRW.FullRankWeighted

-- @@ L215-215 verbatim
open scoped BigOperators

-- @@ L216-216 verbatim
open OrderZero

-- @@ L217-217 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L219-219 verbatim
variable {w : A} (hw : w * w = 0)

-- @@ L220-233 verbatim
omit hw in
omit instSize instPauliData in
lemma abs_mul_self_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : CFC.sqrt (star w * w) * w = 0 := by
  apply Intertwining.sqrt_mul_eq_zero (star_mul_self_nonneg w)
  rw [mul_assoc, hw, mul_zero]


-- @@ L235-248 verbatim
omit hw in
omit instSize instPauliData in
lemma self_mul_coabs_zero.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    (hw : w * w = 0)
    : w * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, hw, zero_mul]


-- @@ L250-253 verbatim
include hw in
lemma abs_coabs_zero : CFC.sqrt (star w * w) * CFC.sqrt (w * star w) = 0 := by
  apply Intertwining.mul_sqrt_eq_zero (mul_star_self_nonneg w)
  rw [← mul_assoc, abs_mul_self_zero hw, zero_mul]


-- @@ L255-265 verbatim
omit instSize instPauliData in
lemma self_abs.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {w : A}
    : w * CFC.sqrt (star w * w) = CFC.sqrt (w * star w) * w :=
  Intertwining.sqrt (star_mul_self_nonneg w) (mul_star_self_nonneg w) (mul_assoc _ _ _).symm



-- @@ L268-296 verbatim
def ofSquareZero (hw : w * w = 0) (hn : ‖w‖ ≤ 1) : WeightedUnits (Fin 2) A := by
  let a := CFC.sqrt (star w * w)
  let b := CFC.sqrt (w * star w)
  let x : Fin 2 → Fin 2 → A := ![![a, star w], ![w, b]]
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hb : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have haa : a * a = star w * w := CFC.sqrt_mul_sqrt_self _
  have hbb : b * b = w * star w := CFC.sqrt_mul_sqrt_self _
  have hab : a * b = 0 := abs_coabs_zero hw
  have hba : b * a = 0 := by simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have haw : a * w = 0 := abs_mul_self_zero hw
  have hwb : w * b = 0 := self_mul_coabs_zero hw
  have hwa : w * a = b * w := self_abs
  have hwsa : star w * a = 0 := by simpa only [star_mul, ha.star_eq, star_zero] using congrArg star haw
  have hbws : b * star w = 0 := by simpa only [star_mul, hb.star_eq, star_zero] using congrArg star hwb
  have hbw : a * star w = star w * b := by
    simpa only [star_mul, ha.star_eq, hb.star_eq] using congrArg star hwa
  have hws : star w * star w = 0 := by simpa only [star_mul, star_zero] using congrArg star hw
  refine ⟨a + b, x, add_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _), ?_, ?_, ?_, by simp [Fin.sum_univ_two, x]⟩
  · rw [ha.norm_add_eq_max hb hab]
    dsimp only [a, b]
    rw [CFC.norm_sqrt (star w * w), CFC.norm_sqrt (w * star w), CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star,
      Real.sqrt_mul_self (norm_nonneg _), max_self]
    exact hn
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [x, ha.star_eq, hb.star_eq]
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [x, add_mul, haa, hbb, hab, hba, haw, hwb, hwsa, hbws, hws, hw, hwa, hbw]



-- @@ L299-299 verbatim
end KirchbergRordam.GenericRW.FullRankWeighted


-- @@ L301-301 verbatim
namespace KirchbergRordam.GenericRW.FullRankWeighted

-- @@ L302-302 verbatim
open scoped BigOperators

-- @@ L303-303 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor OrderZero Fullness

-- @@ L304-304 verbatim
universe u

-- @@ L305-305 verbatim
variable {P : Type u} [CStarAlgebra P]

-- @@ L306-306 verbatim
local instance (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _

-- @@ L307-307 verbatim
local instance (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _

-- @@ L308-308 verbatim
local instance : PartialOrder P := CStarAlgebra.spectralOrder _

-- @@ L309-309 verbatim
local instance : StarOrderedRing P := CStarAlgebra.spectralOrderedRing _


-- @@ L311-311 verbatim
abbrev Row := KirchbergRordam.PauliPower.Row


-- @@ L313-315 verbatim
def power (W : WeightedUnits (Fin 2) P) : (k : ℕ) → WeightedUnits (Row k) (powerPack P k)
  | 0 => W
  | k+1 => tensor W (power W k)


-- @@ L317-317 verbatim
variable [Nontrivial P]

-- @@ L318-322 verbatim
lemma power_full (W : WeightedUnits (Fin 2) P) (hW : ∀ i, IsFull (W.x i i))
    (k : ℕ) (i : Row k) : IsFull ((power W k).x i i) := by
  induction k with
  | zero => exact hW i
  | succ k ih => exact pure_full (hW i.1) (ih i.2)


-- @@ L324-335 verbatim
omit instSize instPauliData in
lemma exists_flatten
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (D : Type u) [CStarAlgebra D] (n k : ℕ) :
    ∃ m : ℕ, Nonempty (powerPack (powerPack D n) k →⋆ₐ[ℂ] powerPack D m) := by
  induction k with
  | zero => exact ⟨n,⟨StarAlgHom.id ℂ _⟩⟩
  | succ k ih =>
    obtain ⟨m,⟨φ⟩⟩ := ih
    obtain ⟨ψ⟩ := exists_joinPower D n m
    exact ⟨n+m+1,⟨ψ.comp (MaxTensor.map (StarAlgHom.id ℂ (powerPack D n)) φ)⟩⟩

-- @@ L336-336 verbatim
end KirchbergRordam.GenericRW.FullRankWeighted


-- @@ L338-338 verbatim
namespace KirchbergRordam.GenericRW.FullRankWeighted

-- @@ L339-339 verbatim
section

-- @@ L340-340 verbatim
open OrderZero Fullness _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

-- @@ L341-341 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [instNontrivialA : Nontrivial A]

-- @@ L342-356 verbatim
omit instSize instPauliData in
lemma sqrt_star_mul_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (star w*w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (star w*w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.star_mul_self_eq_zero_iff _).mp hh.symm)

-- @@ L357-371 verbatim
omit instSize instPauliData in
lemma sqrt_mul_star_self_full.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    [instNontrivialA : Nontrivial A]
    {w : A} (hw : IsFull w) : IsFull (CFC.sqrt (w*star w)) := by
  apply full_of_survives
  intro π he
  have hh := congrArg π.representation (CFC.sqrt_mul_sqrt_self (w*star w))
  rw [map_mul,he,zero_mul,map_mul,map_star] at hh
  exact full_survives hw π.representation ((CStarRing.mul_star_self_eq_zero_iff _).mp hh.symm)


-- @@ L373-377 verbatim
lemma ofSquareZero_full {w : A} (hw : w*w=0) (hn : ‖w‖≤1) (hf : IsFull w) (i : Fin 2) :
    IsFull ((ofSquareZero hw hn).x i i) := by
  fin_cases i
  · exact sqrt_star_mul_self_full hf
  · exact sqrt_mul_star_self_full hf

-- @@ L378-378 verbatim
end


-- @@ L380-380 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness

-- @@ L381-381 verbatim
universe u

-- @@ L382-382 verbatim
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

-- @@ L383-404 verbatim
omit [Size] [PauliData] in
theorem exists_full_cone (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, ∃ η : @ConeModel.Cone (powerSize k) →⋆ₐ[ℂ] powerPack D m,
      IsFull (η (@ConeModel.corner (powerSize k) 0 0)) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,y,hyz,hyfull⟩ := FullSquareZero.exists_full_square_zero hD
  obtain ⟨w,hwz,hwfull,hwn⟩ := FullSquareZero.normalize hyz hyfull
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  let W := ofSquareZero hwz hwn.le
  let := CStarAlgebra.spectralOrder (powerPack (powerPack D n) k)
  let := CStarAlgebra.spectralOrderedRing (powerPack (powerPack D n) k)
  let V := reindex (power W k) (rowEquiv k)
  obtain ⟨m,⟨φ⟩⟩ := exists_flatten D n k
  let := CStarAlgebra.spectralOrder (powerPack D m)
  let := CStarAlgebra.spectralOrderedRing (powerPack D m)
  let R := V.map φ
  refine ⟨m,R.coneHom,?_⟩
  rw [R.coneHom_corner]
  apply Fullness.full_map
  exact power_full W (ofSquareZero_full hwz hwn.le hwfull) k ((rowEquiv k).symm 0)

-- @@ L405-405 verbatim
end KirchbergRordam.GenericRW.FullRankWeighted


-- @@ L407-407 verbatim
namespace KirchbergRordam.GenericRW.ConeCut

-- @@ L408-415 verbatim
lemma q_zero_eq_corner : q 0 (le_refl 0)=ConeModel.corner 0 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [ConeModel.corner_apply]
  change coeff 0 t • unit 0 0=(↑(t:ℝ):ℂ) • CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  rw [show coeff 0 t=(t:ℝ) by simp [coeff,max_eq_left t.property.1]]
  exact (Complex.coe_smul _ _).symm

-- @@ L416-416 verbatim
end KirchbergRordam.GenericRW.ConeCut


-- @@ L418-418 verbatim
namespace KirchbergRordam.GenericRW

-- @@ L419-419 verbatim
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

-- @@ L420-433 verbatim
omit [Size] [PauliData] in


theorem finite_prime_power_drop (D : Type*) [CStarAlgebra D] [Nontrivial D]
    (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) (k : ℕ) :
    ∃ m : ℕ, Nonempty (@DimensionDrop23 (powerSize k) →⋆ₐ[ℂ] powerPack D m) := by
  let : Size := powerSize k
  let : PauliData := powerPauliData k
  obtain ⟨n,η,hη⟩ := FullRankWeighted.exists_full_cone hD k
  let := CStarAlgebra.spectralOrder (powerPack D n)
  let := CStarAlgebra.spectralOrderedRing (powerPack D n)
  obtain ⟨l,⟨φ⟩⟩ := ConeDrop.exists_drop_from_full_cone η (by rwa [ConeCut.q_zero_eq_corner])
  obtain ⟨m,⟨ψ⟩⟩ := FullRankWeighted.exists_flatten D n l
  exact ⟨m,⟨ψ.comp φ⟩⟩

-- @@ L434-434 verbatim
end KirchbergRordam.GenericRW


-- @@ L436-436 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L437-437 verbatim
end


-- @@ L439-439 verbatim
end OAI
