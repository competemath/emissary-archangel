module

public import Architect
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Cotensors
public import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal
public import InfinityCosmos.ForMathlib.CategoryTheory.Enriched.Limits.IsConicalTerminal
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.MorphismProperty
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalPullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts
public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
namespace CategoryTheory


-- @@ L23-23 verbatim
open Category Limits MonoidalCategory SimplicialCategory EnrichedOrdinaryCategory Enriched SSet


-- @@ L25-25 verbatim
universe w v u


-- @@ L27-27 verbatim
variable (K : Type u) [Category.{v} K] [SimplicialCategory K]


-- @@ L29-33 verbatim
/-- A `PreInfinityCosmos` is a simplicially enriched category whose hom-spaces are quasi-categories
and whose morphisms come equipped with a special class of isofibrations. -/
class PreInfinityCosmos extends SimplicialCategory K where
  [has_qcat_homs : ∀ {X Y : K}, SSet.Quasicategory (EnrichedCategory.Hom X Y)]
  IsIsofibration : MorphismProperty K


-- @@ L35-35 verbatim
namespace InfinityCosmos


-- @@ L37-37 verbatim
variable {K : Type u} [Category.{v} K] [PreInfinityCosmos.{v} K]


-- @@ L39-39 verbatim
open PreInfinityCosmos


-- @@ L41-44 verbatim
/-- Common notation for the hom-spaces in a pre-∞-cosmos. -/
def Fun (A B : K) : QCat where
  obj := EnrichedCategory.Hom A B
  property := has_qcat_homs


-- @@ L46-48 verbatim
noncomputable def representableMap' {X A B : K} (f : 𝟙_ SSet ⟶ EnrichedCategory.Hom A B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ EnrichedCategory.Hom X B :=
  (ρ_ _).inv ≫ _ ◁ f ≫ EnrichedCategory.comp (V := SSet) X A B


-- @@ L50-52 verbatim
noncomputable def representableMap (X : K) {A B : K} (f : A ⟶ B) :
    (EnrichedCategory.Hom X A : SSet) ⟶ EnrichedCategory.Hom X B :=
  representableMap' (eHomEquiv SSet f)


-- @@ L54-55 verbatim
noncomputable def toFunMap (X : K) {A B : K} (f : A ⟶ B) : Fun X A ⟶ Fun X B :=
  ObjectProperty.homMk <| representableMap X f


-- @@ L57-58 verbatim
/-- The subtype of isofibrations. Arguments of this type have the form `⟨ f hf ⟩`. -/
def Isofibration (X Y : K) : Type v := {f : X ⟶ Y // IsIsofibration f}


-- @@ L60-61 verbatim
/-- Type with "\rr". -/
infixr:25 " ↠ " => Isofibration


-- @@ L63-63 expanded
instance (A B : K) : Coe (Isofibration A B) (A ⟶ B) :=
  ⟨fun f ↦ f.1⟩


-- @@ L65-65 verbatim
end InfinityCosmos


-- @@ L67-67 verbatim
open PreInfinityCosmos InfinityCosmos Enriched


-- @@ L69-69 verbatim
variable (K : Type u) [Category.{v} K]


-- @@ L71-122 expanded
/-- An `InfinityCosmos` extends a `PreInfinityCosmos` with limit and isofibration axioms. -/
@[blueprint "defn:cosmos" (title := "$\\infty$-cosmos") (statement := /--
    An $\infty$-\textbf{cosmos} $\cK$ is a category that is enriched over
      quasi-categories,\footnote{This is to say $\cK$ is a simplicially enriched category (see
      Definition \ref{defn:simplicial-category}) whose hom spaces are all quasi-categories.} meaning in
      particular that\begin{itemize}
      \item its morphisms $f \colon A \to B$ define the vertices of a quasi-category denoted $\Fun(A,B)$
      and referred to as a \textbf{functor space},
      \end{itemize}
      that is also equipped with a specified collection of maps that we call \textbf{isofibrations} and
      denote by ``$\fib$'' satisfying the following two axioms:
      \begin{enumerate}
      \item\label{itm:cosmos-limits} (completeness) The quasi-categorically enriched category $\cK$
      pos\-sess\-es a terminal object, small products, pullbacks of isofibrations, limits of countable
      towers of isofibrations, and cotensors with simplicial sets, each of these limit notions
      satisfying a universal property that is enriched over simplicial sets.\footnote{This is to say,
      these are simplicially enriched limit notions, in the sense described in Definitions
      \ref{defn:simplicial-cotensor} and \ref{defn:simplicial-conical-limit}.}
      \item\label{itm:cosmos-isofib} (isofibrations) The isofibrations contain all isomorphisms and any
      map whose codomain is the terminal object; are closed under composition, product, pullback,
      forming inverse limits of towers, and Leibniz cotensors with monomorphisms of simplicial sets; and
      have the property that if $f \colon A \fib B$ is an isofibration and $X$ is any object then
      $\Fun(X,A) \fib \Fun(X,B)$ is an isofibration of quasi-categories.
      \end{enumerate}
      -/
    )]
class InfinityCosmos extends PreInfinityCosmos K where
  comp_isIsofibration {A B C : K} (f : Isofibration A B) (g : Isofibration B C) :
    IsIsofibration (f.1 ≫ g.1)
  iso_isIsofibration {X Y : K} (e : X ⟶ Y) [IsIso e] : IsIsofibration e
  all_objects_fibrant {X Y : K} (hY : IsConicalTerminal SSet Y) (f : X ⟶ Y) : IsIsofibration f
  [has_products : HasConicalProducts SSet K]
  prod_map_fibrant {γ : Type w} {A B : γ → K} (f : ∀ i, Isofibration (A i) (B i)) :
    IsIsofibration (Limits.Pi.map (fun i ↦ (f i).1))
  [has_isofibration_pullbacks {E B A : K} (p : Isofibration E B) (f : A ⟶ B) :
    HasConicalPullback SSet p.1 f]
  pullback_isIsofibration {E B A P : K} (p : Isofibration E B) (f : A ⟶ B) (fst : P ⟶ E)
    (snd : P ⟶ A) (h : IsPullback fst snd p.1 f) : IsIsofibration snd
  has_limits_of_towers (F : ℕᵒᵖ ⥤ K) :
    (∀ n : ℕ, IsIsofibration (F.map (homOfLE (Nat.le_succ n)).op)) → HasConicalLimit SSet F
  has_limits_of_towers_isIsofibration (F : ℕᵒᵖ ⥤ K) (hf) :
    haveI := has_limits_of_towers F hf
    IsIsofibration (limit.π F (.op 0))
  [has_cotensors : HasCotensors K]
  leibniz_cotensor_isIsofibration {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K} (f : Isofibration A B)
    {P : K} (fst : P ⟶ cotensor.obj U A) (snd : P ⟶ cotensor.obj V B)
    (h : IsPullback fst snd (cotensorCovMap U f.1) (cotensorContraMap i B)) :
    IsIsofibration
      (h.isLimit.lift <|
        PullbackCone.mk (cotensorContraMap i A) (cotensorCovMap V f.1)
          (cotensor_bifunctoriality i f.1))
  local_isoFibration {X A B : K} (f : Isofibration A B) : Isofibration (toFunMap X f.1)


-- @@ L124-124 verbatim
attribute [instance] has_products has_isofibration_pullbacks has_cotensors


-- @@ L126-126 verbatim
namespace InfinityCosmos


-- @@ L128-128 verbatim
variable {K : Type u} [Category.{v} K] [InfinityCosmos K]


-- @@ L130-131 verbatim
/-- An ∞-cosmos has a conical terminal object as `SSet`-enriched limit. -/
example : HasConicalTerminal SSet K := inferInstance


-- @@ L133-134 verbatim
/-- An ∞-cosmos has a terminal object. -/
example : HasTerminal K := inferInstance


-- @@ L136-137 verbatim
/-- An ∞-cosmos has cotensors. -/
example : HasCotensors K := inferInstance


-- @@ L139-140 verbatim
/-- An ∞-cosmos has products. -/
example : HasProducts K := inferInstance


-- @@ L142-143 expanded
/-- An ∞-cosmos has pullbacks. -/
example {E B A : K} (p : Isofibration E B) (f : A ⟶ B) : HasPullback p.1 f :=
  inferInstance


-- @@ L145-145 verbatim
end InfinityCosmos


-- @@ L147-147 verbatim
end CategoryTheory
